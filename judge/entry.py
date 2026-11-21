"""Read a single additive entry from Git as inert bytes and generate the organizer's goal."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ID = re.compile(r"[a-z0-9][a-z0-9-]{0,47}\Z")
TRACKS = ("lower-bound", "construction")
MAX_FILE = 4 * 1024 * 1024

def require(test, message):
    if not test:
        raise ValueError(message)

def json_data(raw):
    def pairs(items):
        data = dict(items)
        require(len(data) == len(items), "duplicate JSON key")
        return data
    return json.loads(raw, object_pairs_hook=pairs)

def natural(value, label):
    require(type(value) is int and 0 <= value < 2**31, f"invalid {label}")
    return value

def array(value, label):
    require(type(value) is list, f"invalid {label}")
    return value

def scheme_literal(data):
    require(type(data) is dict and set(data) == {"representation","graph","encoder","counter_bits"}
            and data["representation"] == "explicit-dag-circuit-v1", "expected explicit DAG circuit")
    graph, encoder = array(data["graph"], "graph"), data["encoder"]
    require(bool(graph) and type(encoder) is dict and set(encoder) == {"inputs","gates","outputs"}, "invalid scheme")
    inputs = natural(encoder["inputs"], "inputs")
    require(inputs > 0, "empty raw input")
    def terms(rows, arities, gates=False):
        result = []
        for index, row in enumerate(array(rows, "rows")):
            require(type(row) is list and row and type(row[0]) is str and
                    row[0] in arities and len(row)-1 == arities[row[0]], "bad node or gate")
            tag, *args = row
            if gates and tag == "constant":
                require(type(args[0]) is bool, "expected a boolean constant")
                args = [str(args[0]).lower()]
            else:
                limit = inputs if gates and tag == "input" else index
                require(all(natural(x, "index") < limit for x in args), "invalid reference")
            result.append("."+tag+"".join(" "+str(x) for x in args))
        return "["+",".join(result)+"]"
    nodes = terms(graph, {"source":0,"unary":1,"binary":2})
    gates = terms(encoder["gates"], {"input":1,"constant":1,"neg":1,"conj":2,"xor":2}, True)
    outputs = array(encoder["outputs"], "outputs")
    require(len(outputs) == 1+2*len(graph) and all(natural(x, "output")<len(encoder["gates"]) for x in outputs),
            "invalid output mask layout")
    counter = natural(data["counter_bits"], "counter bits")
    return f"⟨{nodes}, ⟨{inputs}, {gates}, [{','.join(map(str, outputs))}]⟩, {counter}⟩"

def prepare(files, entry, dest):
    parts = entry.split("/")
    require(len(parts)==3 and parts[0]=="submissions" and parts[1] in TRACKS and ID.fullmatch(parts[2]), "bad entry path")
    track, ident = parts[1:]
    require(0<len(files)<=64 and sum(map(len,files.values()))<=16*1024**2, "entry size limit")
    required = {"claim.json","proof/Main.lean","ARGUMENT.md","PROVENANCE.md"}
    if track=="construction":
        required.add("program.json")
    require(required<=files.keys() and all(files[x].strip() for x in required), "missing required file")
    claim = json_data(files["claim.json"])
    require(type(claim) is dict and set(claim)=={"track","id","bound_bytes","team","contract"}
            and claim["track"]==track and claim["id"]==ident and claim["contract"]=="poisson-dag-v2-rehearsal-1",
            "invalid claim or contract")
    require(type(claim["team"]) is str and ID.fullmatch(claim["team"]), "invalid team")
    bound = natural(claim["bound_bytes"], "byte bound")
    require(bound>0, "expected positive bound")
    proof = dest/"proof"
    proof.mkdir(parents=True)
    for name, raw in files.items():
        require(len(raw)<=MAX_FILE, "file limit")
        if name.startswith("proof/"):
            require(re.fullmatch(r"proof/(?:[A-Za-z][A-Za-z0-9_]*/)*[A-Za-z][A-Za-z0-9_]*\.lean", name), "bad module name")
            path = dest/name
            path.parent.mkdir(exist_ok=True, parents=True)
            path.write_bytes(raw)
        else:
            require(name in required, "unexpected entry file")
    code = "import PoissonDAG.V2.Model\n"
    if track == "construction":
        program = json_data(files["program.json"])
        if program == {"representation": "organizer-reference-v1", "scheme": "grs-cc-v1"}:
            code += "import PoissonDAG.Constructions.GRSCC.Circuit\n"
            literal = "PoissonDAG.GRSCC.scheme"
            claim["reference"] = "grs-cc-v1"
        else:
            literal = scheme_literal(program)
        code += "def Judge.literal : PoissonDAG.Scheme := " + literal + "\n"
        goal = f"PoissonDAG.V2.ConstructionCertificate Judge.literal {bound}"
    else:
        goal = f"PoissonDAG.V2.UniversalLowerBound {bound}"
    (dest/"Expected.lean").write_text(code+"def Judge.goal : Prop := "+goal+"\n")
    hashes={p:hashlib.sha256(v).hexdigest() for p,v in sorted(files.items())}
    return dict(claim, snapshot=hashlib.sha256(json.dumps(hashes,sort_keys=True).encode()).hexdigest())

def git(*args):
    return subprocess.check_output(["git", *args])

def from_git(base, head, dest):
    require(all(re.fullmatch("[0-9a-f]{40}", s) for s in (base,head)), "bad commit")
    require(git("merge-base",base,head).decode().strip()==base, "rebase onto the checked base")
    changes=git("diff","--no-renames","--name-status","-z",base,head).split(b"\0")[:-1]
    require(0<len(changes)<=128 and all(x==b"A" for x in changes[::2]), "one new entry only")
    paths=[s.decode("ascii") for s in changes[1::2]]
    entries={"/".join(p.split("/")[:3]) for p in paths}
    require(len(entries)==1,"one entry per PR")
    entry=entries.pop()
    require(re.fullmatch(r"submissions/(construction|lower-bound)/[a-z0-9-]+",entry), "organizer paths are protected")
    require(not git("ls-tree",base,"--",entry), "entry already exists")
    files={}
    total=0
    for p in paths:
        meta=git("ls-tree","-l",head,"--",p).split(b"\t",1)[0].split()
        require(len(meta)==4 and meta[:2]==[b"100644",b"blob"] and int(meta[3])<=MAX_FILE,"invalid file mode or size")
        total += int(meta[3])
        require(total<=16*1024**2, "entry size limit")
        files[p[len(entry)+1:]]=git("cat-file","blob",meta[2].decode())
    return prepare(files,entry,dest)
