"""Reject missing declarations or nonstandard axioms in an overlay replay."""

import pathlib
import re
import sys


def verify(source: str, log: str) -> int:
    names = re.findall(r"^#print axioms (\S+)$", source, re.M)
    if not names or len(names) != len(set(names)):
        raise ValueError("expected a nonempty set of distinct axiom probes")
    if re.search(r"sorryAx|\berror(?:\([^)]*\))?:|\bwarning:", log):
        raise ValueError("replay contains an error, warning, or placeholder axiom")
    flat = re.sub(r"\s+", " ", log)
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for name in names:
        pattern = "'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]"
        match = re.search(pattern, flat)
        if match:
            axioms = {a.strip() for a in match.group(1).split(",") if a.strip()}
            if not axioms <= allowed:
                raise ValueError(f"nonstandard axioms for {name}: {sorted(axioms)}")
        elif f"'{name}' does not depend on any axioms" not in flat:
            raise ValueError(f"missing axiom output: {name}")
    return len(names)


if __name__ == "__main__":
    source, log = (pathlib.Path(p).read_text() for p in sys.argv[1:])
    print("AUDITED_THEOREMS", verify(source, log))
    print("ALL_STANDARD_AXIOMS_ONLY")
