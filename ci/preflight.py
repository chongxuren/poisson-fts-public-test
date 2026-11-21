"""Select optional organizer-built dependencies from the validated entry."""
import os
import tempfile
from pathlib import Path

from judge.entry import from_git

if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as directory:
        claim = from_git(os.environ["BASE"], os.environ["HEAD"], Path(directory))
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        print("grscc=" + str(claim.get("reference") == "grs-cc-v1").lower(), file=output)
        print("fors=" + str(claim.get("reference", "").startswith("fors-")).lower(), file=output)
