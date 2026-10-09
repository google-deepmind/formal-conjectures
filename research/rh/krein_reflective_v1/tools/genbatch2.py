import json, sys
from fractions import Fraction as F
br={**json.load(open(sys.argv[1])),**json.load(open(sys.argv[2]))}
start,end,size,outdir=int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5]),sys.argv[6]
HDR=open('genbatch.py').read().split('HDR="""')[1].split('"""')[0]
def q(x):
    x=F(x); return f"{x.numerator}" if x.denominator==1 else f"{x.numerator}/{x.denominator}"
names=[]
for s in range(start,end,size):
    m=min(size,end-s); nm=f"RHKreinCellBatch{s:04d}"
    idx=list(range(s,s+m))
    defs="\n".join(f"def b{i:04d} : List ℚ := [{', '.join(q(x) for x in br[str(i)])}]" for i in idx)
    cells="\n\n".join(f"theorem c{i:04d} : checkCell pa19 (cellAt {i}) b{i:04d} = true := by decide +kernel" for i in idx)
    lst=", ".join(f"cellAt {i}" for i in idx)
    txt=HDR+f"""
/-! Serialized cells {s} to {s+m-1}: kernel-checked analytic soundness, one kernel check per
cell. AUTHORITY_EFFECT = NONE. -/

set_option autoImplicit false

namespace AEGIS.RHKreinCellBatchV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1

{defs}

def breaks{s:04d} : List (List ℚ) := [{', '.join(f'b{i:04d}' for i in idx)}]

{cells}

theorem slice{s:04d} : slice {s} {m} = [{lst}] := by decide +kernel

theorem batch{s:04d}_ok : checkAll pa19 (slice {s} {m}) breaks{s:04d} = true := by
  rw [slice{s:04d}]
  simp only [breaks{s:04d}, checkAll, {', '.join(f'c{i:04d}' for i in idx)}, Bool.and_self]

theorem batch{s:04d} : ∀ c ∈ slice {s} {m}, CellAnalyticSoundV1 c :=
  checkAll_sound pa19 _ _ batch{s:04d}_ok

end AEGIS.RHKreinCellBatchV1

#print axioms AEGIS.RHKreinCellBatchV1.batch{s:04d}
"""
    open(f"{outdir}/{nm}.lean","w").write(txt); names.append((nm,s,m))
json.dump(names,open(f"{outdir}/batches.json","w"))
print(len(names),'files')
