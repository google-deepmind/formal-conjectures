"""KREIN_CERTIFICATE_RECEIPT_V2 — execution-bound receipts for verify_krein_arb_v1.py.

run   : python3 krein_arb_receipt_v2.py run LP.json M X Z0 OUT.json
        Executes the (unchanged) verifier on LP.json, parses its stdout, and writes a canonical
        receipt: source head, verifier/LP Git blob + SHA-256, parameters, the verifier-emitted
        cells_verified / zero-cell bound / tail bound / verdict, runtime identities, stdout SHA-256,
        and receipt_sha256 = SHA-256 of the canonical body. status = EXECUTION_BOUND only if the
        verifier exited 0 and printed CERTIFIED.
check : python3 krein_arb_receipt_v2.py check OUT.json
        Recomputes the canonical hash and the verifier/LP hashes at the current head.
        Any byte drift -> INVALID; a different source head -> HISTORICAL; else CURRENT.
prose : python3 krein_arb_receipt_v2.py prose STATUS.md OUT.json [OUT.json ...]
        Fails if STATUS.md states a cell count for a receipt's L that differs from cells_verified.
"""
import hashlib, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
VERIFIER = os.path.join(HERE, "verify_krein_arb_v1.py")


def git(*a):
    return subprocess.check_output(["git", *a], cwd=HERE).decode().strip()


def file_id(path):
    data = open(path, "rb").read()
    return {"path": os.path.relpath(os.path.abspath(path), git("rev-parse", "--show-toplevel")),
            "git_blob": git("hash-object", path), "sha256": hashlib.sha256(data).hexdigest()}


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def receipt_hash(body):
    return hashlib.sha256(canonical(body).encode()).hexdigest()


def runtime():
    import flint, numpy, scipy
    return {"python": sys.version.split()[0], "python_flint": flint.__version__,
            "numpy": numpy.__version__, "scipy": scipy.__version__}


def parse(stdout):
    cells = re.search(r"cells verified on .*\]: (\d+)\s*$", stdout, re.M)
    zero = re.search(r"^zero cell .*lower bound of F = \[([0-9.eE+-]+)", stdout, re.M)
    tail = re.search(r"^tail lower bound .*: \[([0-9.eE+-]+)", stdout, re.M)
    cert = re.search(r"^CERTIFIED: ", stdout, re.M)
    return {"cells_verified": int(cells.group(1)) if cells else None,
            "zero_cell_lower_bound": zero.group(1) if zero else None,
            "tail_lower_bound_F_over_W": tail.group(1) if tail else None,
            "certified_line_present": bool(cert)}


def support(P):
    """The verifier trusts uk; Lean needs every hat support [u-w, u+w] outside (-L, L). Exact check."""
    from fractions import Fraction
    gap = min(Fraction(u) for u in P["uk"]) - Fraction(P["w"]) - Fraction(P["L"])
    return {"min_uk_minus_w_minus_L": str(gap), "ok": gap >= 0 and len(P["coef"]) == len(P["uk"]) + 5}


def run(lp, m, x, z0, out):
    head = git("rev-parse", "HEAD")
    lp = os.path.abspath(lp)
    try:
        dirty = git("status", "--porcelain", "--", VERIFIER, lp)
        tracked = subprocess.run(["git", "ls-files", "--error-unmatch", lp], cwd=HERE,
                                 capture_output=True).returncode == 0
    except subprocess.CalledProcessError:
        dirty, tracked = "outside-repo", False
    p = subprocess.run([sys.executable, VERIFIER, lp, m, x, z0], capture_output=True, text=True)
    stdout = p.stdout + p.stderr
    P = json.load(open(lp)); L = P["L"]
    body = {"schema": "aegis.rh.krein-arb-receipt.v2", "source_head_sha": head,
            "inputs_committed_at_head": dirty == "" and tracked,
            "verifier": file_id(VERIFIER), "lp_payload": file_id(lp),
            "parameters": {"L": L, "m": m, "X": x, "zero_cell": z0}, "hat_support": support(P),
            "result": parse(stdout), "exit_code": p.returncode,
            "stdout_sha256": hashlib.sha256(stdout.encode()).hexdigest(),
            "runtime": runtime(), "rh_proven": False, "authority_effect": "NONE"}
    ok = (p.returncode == 0 and body["result"]["certified_line_present"] and body["result"]["cells_verified"]
          and body["hat_support"]["ok"])
    body["status"] = "EXECUTION_BOUND" if ok else "NOT_CERTIFIED"
    rec = dict(body, receipt_sha256=receipt_hash(body))
    open(out, "w").write(canonical(rec) + "\n")
    open(out + ".stdout", "w").write(stdout)
    print(rec["status"], rec["result"]["cells_verified"], rec["receipt_sha256"])
    return 0 if rec["status"] == "EXECUTION_BOUND" else 1


def check(path):
    rec = json.load(open(path))
    body = {k: v for k, v in rec.items() if k != "receipt_sha256"}
    if receipt_hash(body) != rec.get("receipt_sha256"):
        print("INVALID receipt_sha256"); return 1
    if rec.get("status") != "EXECUTION_BOUND" or not rec.get("hat_support", {}).get("ok"):
        print("INVALID status", rec.get("status"), rec.get("hat_support")); return 1
    top = git("rev-parse", "--show-toplevel")
    for key in ("verifier", "lp_payload"):
        f = rec[key]; p = os.path.join(top, f["path"])
        if not os.path.exists(p) or file_id(p)["sha256"] != f["sha256"] or file_id(p)["git_blob"] != f["git_blob"]:
            print("INVALID", key, "drift"); return 1
    if not rec.get("inputs_committed_at_head"):
        print("UNCOMMITTED (execution-bound, inputs not committed at source head)"); return 0
    if rec["source_head_sha"] != git("rev-parse", "HEAD"):
        print("HISTORICAL", rec["source_head_sha"]); return 0
    print("CURRENT"); return 0


def prose(status_md, receipts):
    text = open(status_md, encoding="utf-8").read(); bad = 0
    for path in receipts:
        rec = json.load(open(path)); L = rec["parameters"]["L"]; n = rec["result"]["cells_verified"]
        tag = "1.0" if L == 1.0 else repr(L)
        for mt in re.finditer(r"L = %s(?![\d/])[^\n]*?(\d{4,6}) cells" % re.escape(tag), text):
            if int(mt.group(1)) != n:
                print(f"FAIL L={tag}: prose {mt.group(1)} != receipt {n}"); bad = 1
    print("PROSE_OK" if not bad else "PROSE_MISMATCH"); return bad


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "run": sys.exit(run(*sys.argv[2:7]))
    if cmd == "check": sys.exit(check(sys.argv[2]))
    if cmd == "prose": sys.exit(prose(sys.argv[2], sys.argv[3:]))
    sys.exit(__doc__)
