# Re-split heavy L105 batches (kernel OOM) into sub-files of <= UNIT pieces; each sub-cell re-checked in the mirror.
import json, sys
from pathlib import Path
from fractions import Fraction as Q
from gen105 import HDR, qs, rq, glue_chain, R, D
from split import check
S=str(Path(__file__).resolve().parent)
B=json.loads((Path(S) / 'batches105.json').read_text(encoding='utf-8'))
ok=set(l.split()[0] for l in open(f'{S}/batch105.log') if ' OK' in l)
UNIT=25
def w(i): return len(D[i]['breaks'])*D[i]['N']/256
def units(i):
    c=D[i]; lo,hi=Q(c['lo']),Q(c['hi']); br=[Q(b) for b in c['breaks']]
    if len(br)<=UNIT: return [(lo,hi,br)]
    k=-(-len(br)//UNIT); n=len(br); out=[]; start=0; prev=lo
    for j in range(1,k+1):
        e=(j*n)//k; out.append((prev,br[e-1],br[start:e])); start=e; prev=br[e-1]
    return out
def thm(name,c,lo,hi,br):
    pa=f"(paH {c['N']})" if c['deg']==36 else f"(paL {c['N']})"
    b=", ".join(f"({qs(x)} : ℚ)" for x in br)
    return (f"theorem {name} : ∀ t : ℝ, {rq(lo)} ≤ t → t ≤ {rq(hi)} → 0 ≤ Fcert t :=\n"
            f"  checkWide_sound {pa} {c['K0']} {'true' if c['hats'] else 'false'} ({qs(lo)} : ℚ) ({qs(hi)} : ℚ) [{b}]\n"
            f"    (by decide +kernel)\n")
hdr=lambda imports,desc: HDR+f"\n{imports}\n\n/-! {desc}\nAUTHORITY_EFFECT = NONE. -/\n\nset_option autoImplicit false\n\nnamespace AEGIS.RHKreinL105BatchV1\nopen AEGIS.RHKreinL105CheckerV1 AEGIS.RHKreinL105TailV1\n\n"
newlist=[]
for nm,idx in B:
    k=int(nm[-3:])
    if nm in ok or sum(w(i) for i in idx)<=60: newlist.append(nm); continue
    U=[]
    for i in idx:
        for u,(lo,hi,br) in enumerate(units(i)):
            assert check(D[i],lo,hi,br), (i,lo,hi)
            U.append((f"w{i:04d}_{u}",i,lo,hi,br))
    groups=[]; cur=[]; cw=0
    for x in U:
        xw=len(x[4])*D[x[1]]['N']/256
        if cur and cw+xw>UNIT: groups.append(cur); cur=[]; cw=0
        cur.append(x); cw+=xw
    groups.append(cur)
    subs=[]
    for j,g in enumerate(groups):
        sn=f"{nm}p{j}"; subs.append(sn)
        s=hdr("import RHKreinL105BatchV1",f"Sub-cells {g[0][0]}–{g[-1][0]} of the `L = 21/20` certificate (split for kernel memory).")
        for (name,i,lo,hi,br) in g: s+=thm(name,D[i],lo,hi,br)+"\n"
        s+="end AEGIS.RHKreinL105BatchV1\n"; open(f'{R}/{sn}.lean','w').write(s)
    s=hdr("\n".join(f"import {x}" for x in subs),f"Wide cells {idx[0]}–{idx[-1]} of the `L = 21/20` certificate, glued from sub-cells.")
    s+=(f"theorem b{k:03d} : ∀ t : ℝ, {rq(D[idx[0]]['lo'])} ≤ t → t ≤ {rq(D[idx[-1]]['hi'])} → 0 ≤ Fcert t :=\n"
        f"  {glue_chain([x[0] for x in U])}\n\nend AEGIS.RHKreinL105BatchV1\n")
    open(f'{R}/{nm}.lean','w').write(s)
    newlist+=subs+[nm]; print(nm,len(U),'units',len(subs),'sub-files',flush=True)
open(f'{S}/batchlist105.txt','w').write("\n".join(newlist)+"\n")
print(len(newlist),'entries')
