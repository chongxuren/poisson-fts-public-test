"""Runnable public reference for the 40-tree construction in the challenge model."""
import argparse
import hashlib
import hmac
import json
import sys
from fractions import Fraction
from math import factorial

TREES = 40
HEIGHT = 8
LABEL_BYTES = 16


def build_program():
    """Compile the fixed forest and public bit-slicing encoder to the judge format."""
    graph = []
    gates = [["constant", False], ["constant", True]]
    frontier = []
    plan = []

    def gate(*instruction):
        gates.append(list(instruction))
        return len(gates) - 1

    def node(instruction, supplied, evaluated):
        graph.append(instruction)
        frontier.append(supplied)
        plan.append(evaluated)
        return len(graph) - 1

    roots = []
    for tree in range(TREES):
        # selected[h][j] tests whether leaf index >> h equals j.
        selected = [None] * (HEIGHT + 1)
        selected[HEIGHT] = [1]
        for h in reversed(range(HEIGHT)):
            bit = gate("input", tree * HEIGHT + h)
            complement = gate("neg", bit)
            selected[h] = [gate("conj", parent, branch)
                           for parent in selected[h + 1] for branch in (complement, bit)]

        # The selected leaf and its bottom sibling are both sent.
        level = [node(["source"], selected[1][j // 2], 0) for j in range(2**HEIGHT)]
        for h in range(1, HEIGHT + 1):
            parents = []
            for j in range(len(level) // 2):
                sibling_selected = selected[h][j ^ 1] if h < HEIGHT else 0
                parents.append(node(["binary", level[2*j], level[2*j+1]],
                                    sibling_selected, selected[h][j]))
            level = parents
        roots.append(level[0])

    while len(roots) > 1:
        joined = [node(["binary", roots[i], roots[i+1]], 0, 1)
                  for i in range(0, len(roots)-1, 2)]
        if len(roots) % 2:
            joined.append(roots[-1])
        roots = joined
    return {"representation": "explicit-dag-circuit-v1", "graph": graph,
            "encoder": {"inputs": TREES * HEIGHT, "gates": gates, "outputs": [1, *frontier, *plan]},
            "counter_bits": 0}


class CountedHash:
    """Addressed 128-bit outputs for reproducible model examples."""
    def __init__(self):
        self.calls = 0

    def __call__(self, domain, index, value):
        self.calls += 1
        return hashlib.sha256(b"PoissonForest/v1/" + domain + index.to_bytes(4, "big") +
                              value).digest()[:LABEL_BYTES]


def masks(program, raw):
    """Evaluate the gate types used by this reference program."""
    values = []
    for tag, *args in program["encoder"]["gates"]:
        if tag == "constant":
            value = args[0]
        elif tag == "input":
            value = bool(raw >> args[0] & 1)
        elif tag == "neg":
            value = not values[args[0]]
        elif tag == "conj":
            value = values[args[0]] and values[args[1]]
        else:
            raise ValueError(f"unexpected reference gate: {tag}")
        values.append(value)
    outputs = [values[g] for g in program["encoder"]["outputs"]]
    if not outputs[0]:
        raise ValueError("reference encoder must always accept")
    end = 1 + len(program["graph"])
    return outputs[1:end], outputs[end:]


def encode(program, message, oracle):
    blocks = b"".join(oracle(b"M", i, message) for i in range(3))
    return masks(program, int.from_bytes(blocks[:TREES], "little"))


def labels(program, seed, oracle):
    if len(seed) != 32:
        raise ValueError("expected a 32-byte seed")
    result = []
    for address, (tag, *parents) in enumerate(program["graph"]):
        if tag == "source":
            value = oracle(b"S", address, seed)
        else:
            left, right = parents
            value = oracle(b"B", address, result[left] + result[right])
        result.append(value)
    return result


def public_key(program, seed):
    return labels(program, seed, CountedHash())[-1]


def sign(program, seed, message, oracle):
    values = labels(program, seed, oracle)
    supplied, _ = encode(program, message, oracle)
    return b"".join(v for v, take in zip(values, supplied) if take)


def verify(program, root, message, signature, oracle):
    supplied, plan = encode(program, message, oracle)
    if len(signature) != LABEL_BYTES * sum(supplied):
        return False
    known = []
    offset = 0
    for address, (tag, *parents) in enumerate(program["graph"]):
        value = None
        if supplied[address]:
            value = signature[offset:offset + LABEL_BYTES]
            offset += LABEL_BYTES
        elif plan[address] and tag == "binary":
            left, right = parents
            if known[left] is not None and known[right] is not None:
                value = oracle(b"B", address, known[left] + known[right])
        known.append(value)
    return known[-1] is not None and hmac.compare_digest(known[-1], root)


def covering_envelope():
    head = sum(Fraction(q**40, factorial(q) * 2**280) for q in range(65))
    return head + Fraction(66, 65 * factorial(65))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-program", action="store_true", help="print the official JSON encoding")
    args = parser.parse_args()
    program = build_program()
    if args.emit_program:
        json.dump(program, sys.stdout, separators=(",", ":"))
        print()
        return
    seed = bytes(range(32))  # Public reproducible test vector.
    message = b"Poisson DAG rehearsal"
    root = public_key(program, seed)
    signing, checking = CountedHash(), CountedHash()
    signature = sign(program, seed, message, signing)
    if not verify(program, root, message, signature, checking):
        raise RuntimeError("reference verification failed")
    envelope = covering_envelope()
    print(f"{len(signature):,} signature bytes; {signing.calls:,} signing hashes; "
          f"{checking.calls:,} verification hashes.")
    print("Exact scalar covering envelope <= 2^-128:", envelope <= Fraction(1, 2**128))


if __name__ == "__main__":
    main()
