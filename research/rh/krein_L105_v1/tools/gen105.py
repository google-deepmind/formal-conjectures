import json, sys, os
from fractions import Fraction as Q
R='/home/user/mathlib4-433/tree105'
D=json.load(open('design105F.json'))
HDR=open('/home/user/mathlib4-433/tree_cell2/RHKreinHatAtV1.lean').read().split('-/')[0]+'-/\n'
def qs(s):
    q=Q(s); return f"{q.numerator}" if q.denominator==1 else f"{q.numerator}/{q.denominator}"
def rq(s): return f"((({qs(s)} : ℚ)) : ℝ)"
def cell_thm(i,c):
    pa=f"(paH {c['N']})" if c['deg']==36 else f"(paL {c['N']})"
    br=", ".join(f"({qs(b)} : ℚ)" for b in c['breaks'])
    return (f"theorem w{i:04d} : ∀ t : ℝ, {rq(c['lo'])} ≤ t → t ≤ {rq(c['hi'])} → 0 ≤ Fcert t :=\n"
            f"  checkWide_sound {pa} {c['K0']} {'true' if c['hats'] else 'false'} ({qs(c['lo'])} : ℚ) ({qs(c['hi'])} : ℚ) [{br}]\n"
            f"    (by decide +kernel)\n")
def glue_chain(names):
    e=names[0]
    for n in names[1:]: e=f"(glue {e} {n})"
    return e
def batches(cost_budget):
    out=[]; cur=[]; cost=0
    for i,c in enumerate(D):
        cc=(40 if c['deg']==36 else 4)+len(c['breaks'])*(2 if c['deg']==36 else 1)
        if cur and cost+cc>cost_budget: out.append(cur); cur=[]; cost=0
        cur.append(i); cost+=cc
    if cur: out.append(cur)
    return out
def write(budget):
    B=batches(budget); names=[]
    base=HDR+"""
import RHKreinL105TailV1

/-! Parameters of the `L = 21/20` wide cells.  AUTHORITY_EFFECT = NONE. -/

namespace AEGIS.RHKreinL105BatchV1
open AEGIS.RHKreinL105CheckerV1
def paH (N : ℕ) : Params := ⟨⟨36, 30, 12, 120⟩, 36, 40, N⟩
def paL (N : ℕ) : Params := ⟨⟨16, 30, 12, 120⟩, 16, 40, N⟩
end AEGIS.RHKreinL105BatchV1
"""
    open(f'{R}/RHKreinL105BatchV1.lean','w').write(base)
    for k,idx in enumerate(B):
        nm=f"RHKreinL105Batch{k:03d}"; names.append((nm,idx))
        s=HDR+f"""
import RHKreinL105BatchV1

/-! Wide cells {idx[0]}–{idx[-1]} of the `L = 21/20` certificate, one kernel check per cell.
AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinL105BatchV1
open AEGIS.RHKreinL105CheckerV1 AEGIS.RHKreinL105TailV1

"""
        for i in idx: s+=cell_thm(i,D[i])+"\n"
        s+=(f"theorem b{k:03d} : ∀ t : ℝ, {rq(D[idx[0]]['lo'])} ≤ t → t ≤ {rq(D[idx[-1]]['hi'])} → 0 ≤ Fcert t :=\n"
            f"  {glue_chain([f'w{i:04d}' for i in idx])}\n\nend AEGIS.RHKreinL105BatchV1\n")
        open(f'{R}/{nm}.lean','w').write(s)
    json.dump(names,open('batches105.json','w'))
    print(len(B),'batch files')
write(int(sys.argv[1]) if len(sys.argv)>1 else 200)
