# Split a heavy wide cell into k sub-cells at existing breakpoints; verify each in the exact mirror.
import json, sys
from fractions import Fraction as Q
from m105 import *
d = json.load(open('design105F.json'))
def cc(lo, hi): return (Q(0), hi) if lo == 0 else ((lo + hi) / 2, (hi - lo) / 2)
def check(cell, lo, hi, br):
    pa = (36,30,12,120,36,40) if cell['deg'] == 36 else (16,30,12,120,16,40)
    c, r = cc(lo, hi); M = wideTM2(pa, cell['K0'], cell['hats'], r, c); Wp = weightPoly(c); a = lo
    for b in br:
        if not checkPiece(pa, cell['K0'], cell['N'], c, r, M, Wp, a, b): return False
        a = b
    return a == hi
def split(i, k):
    cell = d[i]; lo, hi = Q(cell['lo']), Q(cell['hi']); br = [Q(b) for b in cell['breaks']]
    n = len(br); cuts = [br[(j * n) // k - 1] for j in range(1, k)]
    parts, start, prev = [], 0, lo
    for cut in cuts + [hi]:
        j = br.index(cut); parts.append((prev, cut, br[start:j + 1])); start, prev = j + 1, cut
    return [(p, check(cell, *p)) for p in parts]
if __name__ == '__main__':
    i, k = int(sys.argv[1]), int(sys.argv[2])
    for (lo, hi, br), ok in split(i, k): print(i, lo, hi, len(br), ok, flush=True)
