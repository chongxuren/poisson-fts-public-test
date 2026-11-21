#!/usr/bin/env python3
"""Compile in one disposable container and replay only neutral proof data in another."""
import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from judge.entry import from_git

ROOT=Path(__file__).resolve().parents[1]
LIMIT=32*1024**2

def mount(src, target):
    return ["--mount",f"type=bind,source={src},target={target},readonly"]

def verify(directory, *, fixture_debug=False):
    prefix=Path(subprocess.check_output(["lean","--print-prefix"],text=True).strip())
    libs=subprocess.check_output(["lake","env","printenv","LEAN_PATH"],text=True).strip().split(os.pathsep)
    sources=[Path(p).resolve() for p in libs if p and Path(p).is_dir() and not Path(p).resolve().is_relative_to(prefix)]
    paths=[f"/libsrc/{i}" for i in range(len(sources))]
    envpath=":".join(["/judgelib",*paths])
    image=os.environ["JUDGE_IMAGE"]
    args=["docker","run","--rm","--pull=never","--network=none","--read-only","--cap-drop=ALL",
          "--security-opt=no-new-privileges","--pids-limit=128","--memory=4g","--cpus=2",
          "--user=65534:65534","--tmpfs","/tmp:rw,nosuid,nodev,size=512m,mode=1777",
          "--ulimit","fsize=134217728:134217728","--log-driver=none","-e","HOME=/tmp",
          "-e","LEAN_ABORT_ON_PANIC=1","-e","LEAN_NUM_THREADS=2","-e","PATH=/lean/bin:/usr/bin:/bin"]
    for src,target in [(prefix,"/lean"),(ROOT/"build/lib","/judgelib"),*zip(sources,paths)]:
        args.extend(mount(src,target))
    cert=directory/"certificate.ndjson"
    guest=args+mount(directory/"proof","/proof")+mount(ROOT/"ci/guest.sh","/guest.sh")+mount(
        ROOT/"judge/ExportEntry.lean","/tools/ExportEntry.lean")+["-e","LEAN_PATH="+envpath,image,"bash","/guest.sh"]
    # Only a bounded text stream crosses into the trusted stage; no guest filesystem is retained.
    with cert.open("wb") as out, subprocess.Popen(guest,stdout=subprocess.PIPE,stderr=None if fixture_debug else subprocess.DEVNULL) as p:
        size=0
        while block:=p.stdout.read(65536):
            size+=len(block)
            if size>LIMIT:
                p.kill()
                raise ValueError("proof export exceeds 32 MiB")
            out.write(block)
        if p.wait()!=0 or size==0: raise ValueError("contestant compilation or proof export failed")
    # All source here is organizer-generated. The replay process cannot read entrant Lean or .olean files.
    trusted=args+mount(directory/"Expected.lean","/expected/Expected.lean")+mount(cert,"/data/proof")+mount(
        ROOT/"judge/Replay.lean","/tools/Replay.lean")+["-e","LEAN_PATH=/tmp:"+envpath,image,"bash","-ec",
        "lean -R /expected -o /tmp/Expected.olean /expected/Expected.lean && lean --run /tools/Replay.lean /data/proof"]
    # Malformed proof data may cause large diagnostics. Keep it out of workflow commands.
    with (tempfile.TemporaryFile() if fixture_debug else open(os.devnull, "wb")) as log:
        result=subprocess.run(trusted,stdout=log,stderr=subprocess.STDOUT)
        if result.returncode:
            if fixture_debug:
                log.seek(0)
                print(log.read(1800).decode(errors="replace"), flush=True)
            raise ValueError("kernel rejected the proof, its axioms, or its claimed target")

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("base"); ap.add_argument("head"); args=ap.parse_args()
    with tempfile.TemporaryDirectory(dir=ROOT/"build") as tmp:
        d=Path(tmp)
        cert=from_git(args.base,args.head,d)
        verify(d)
    receipt={**cert,"base":args.base,"head":args.head}
    with open(os.environ["GITHUB_OUTPUT"],"a") as out:
        print("receipt="+json.dumps(receipt,separators=(",",":")),file=out)
    print(f"Kernel verified {cert['track']} at {cert['bound_bytes']} bytes.")

if __name__=="__main__":
    main()
