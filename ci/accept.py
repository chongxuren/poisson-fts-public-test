"""Atomically add the verified snapshot and its score to the public test branch."""
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from judge.score import standings


def git(*args, data=None):
    return subprocess.check_output(["git", *args], input=data, text=True).strip()


def main():
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    pr = event["pull_request"]
    receipt = json.loads(os.environ["RECEIPT"])
    base, head = receipt["base"], receipt["head"]
    number = int(pr["number"])
    run = int(os.environ["GITHUB_RUN_ID"])
    if base != pr["base"]["sha"] or head != pr["head"]["sha"] or pr["base"]["ref"] != "main":
        raise ValueError("receipt does not match this event")
    path = f"submissions/{receipt['track']}/{receipt['id']}"
    git("config", "user.name", "Poisson challenge judge")
    git("config", "user.email", "41898282+github-actions[bot]@users.noreply.github.com")
    for attempt in range(5):
        git("fetch", "--quiet", "--no-tags", "origin", "+refs/heads/main:refs/remotes/origin/main",
            f"+refs/pull/{number}/head:refs/rehearsal/input")
        latest = git("rev-parse", "refs/remotes/origin/main")
        board = json.loads(git("show", f"{latest}:docs/scores.json"))
        if any(row["head"] == head and row["pr"] == number for row in board["history"]):
            print("This snapshot already has a receipt.")
            return
        active = json.loads(subprocess.check_output(
            ["gh", "api", f"repos/{os.environ['GITHUB_REPOSITORY']}/pulls/{number}"]))
        if active["state"] != "open" or active["head"]["sha"] != head or git("rev-parse", "refs/rehearsal/input") != head:
            raise ValueError("pull request is closed or has a newer snapshot")
        git("merge-base", "--is-ancestor", base, latest)
        git("diff", "--quiet", base, latest, "--", ".", ":(exclude)submissions/**",
            ":(exclude)docs/scores.json")
        if git("ls-tree", latest, "--", path):
            raise ValueError("submission identifier already taken")
        # Read only Git objects. Neither contestant files nor the candidate tree are checked out.
        git("read-tree", latest)
        git("read-tree", "--prefix=" + path + "/", f"{head}:{path}")
        entries = [{key: value for key, value in row.items()
                    if key not in ("record", "delta", "previous")} for row in board["history"]]
        entries.append({**receipt, "pr": number, "run": run})
        payload = json.dumps(standings(entries), indent=2) + "\n"
        blob = git("hash-object", "-w", "--stdin", data=payload)
        git("update-index", "--add", "--cacheinfo", f"100644,{blob},docs/scores.json")
        tree = git("write-tree")
        commit = git("commit-tree", tree, "-p", latest, "-p", head,
                     "-m", f"Accept verified rehearsal submission #{number}")
        pushed = subprocess.run(["git", "push", "origin", f"{commit}:refs/heads/main"])
        if pushed.returncode == 0:
            print(f"Accepted PR #{number} at {head}.")
            return
    raise RuntimeError("concurrent updates prevented promotion; rerun this workflow")


if __name__ == "__main__":
    main()
