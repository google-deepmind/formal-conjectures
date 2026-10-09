"""Exact finite checks for A2 / 19 motifs. Standard-library integer arithmetic.
This is an executable certificate of the displayed finite identities, not a
Lean kernel proof or a theorem about the repository Weil quadratic.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json


def proper_automorphisms(c):
    # Q=x^2+xy+c*y^2=(x+y/2)^2+(c-1/4)*y^2.
    # For c=1 or 5, vectors of Q-norm 1 or c have |x|,|y|<=4.
    # Thus this enumeration contains every possible matrix column.
    q=lambda x,y:x*x+x*y+c*y*y
    unit=[(x,y) for x,y in product(range(-4,5),repeat=2) if q(x,y)==1]
    second=[(x,y) for x,y in product(range(-4,5),repeat=2) if q(x,y)==c]
    ans=[]
    for (a,b),(d,e) in product(unit,second):
        if a*e-b*d==1 and 2*a*d+a*e+b*d+2*c*b*e==1:
            ans.append([[a,d],[b,e]])
    return ans


def run():
    # Axial A2 coordinates; graph distance max(|x|,|y|,|x+y|).
    pts=[(x,y) for x,y in product(range(-2,3),repeat=2)
         if max(abs(x),abs(y),abs(x+y))<=2]
    shells=Counter(max(abs(x),abs(y),abs(x+y)) for x,y in pts)
    assert [shells[k] for k in range(3)]==[1,6,12]
    assert len(pts)==19
    # Coefficients of the polynomial identity C_n=Q_A2(n+1,n).
    # Both expand to 3*n^2+3*n+1, exact coefficient arithmetic.
    centered_hex_coefficients=[1,3,3]
    norm_diagonal_coefficients=[1,2+1,1+1+1]
    assert centered_hex_coefficients==norm_diagonal_coefficients
    assert 3*3+3*2+2*2==19
    # Autocorrelation of the 19 point stencil: sum of squared characters.
    diff=Counter((a-c,b-d) for a,b in pts for c,d in pts)
    assert diff[(0,0)]==19
    # At character exp(i*pi*x), every value is exactly +/-1.
    st=sum((-1)**x if x>=0 else (-1)**(-x) for x,y in pts)
    spectral=sum(v*((-1)**abs(x)) for (x,y),v in diff.items())
    assert st==3 and spectral==9
    assert spectral-diff[(0,0)]==-10
    projected=Counter(x for x,y in pts)
    pc=Counter(a-b for a in projected for b in projected
               for _ in range(projected[a]*projected[b]))
    assert [projected[x] for x in range(-2,3)]==[3,4,5,4,3]
    assert pc[0]==75 and sum(v*((-1)**abs(x)) for x,v in pc.items())==9
    assert 9-pc[0]==-66
    # Fixed-support normalized projected steps, full width 19/1000.
    width=Fraction(19,1000)
    delta=width/12
    axis=[delta,delta/2,delta/2]*6
    angled=[width/12]*12
    assert sum(axis)==sum(angled)==width
    aut3=proper_automorphisms(1)
    aut19=proper_automorphisms(5)
    assert len(aut3)==6 and len(aut19)==2
    out={
      "status":"EXACT_FINITE_IDENTITIES_VERIFIED",
      "authority_effect":"NONE",
      "A2_shell_counts":[1,6,12],
      "A2_cluster_points":pts,
      "A2_cluster_size":19,
      "centered_hex_norm_identity_coefficients":[1,3,3],
      "A2_norm_3_2":19,
      "norm_form_discriminants":{"x2+xy+y2":-3,"x2+xy+5y2":-19},
      "proper_norm_automorphisms":{"minus3":aut3,"minus19":aut19},
      "stencil_character_pi_0_sum":st,
      "stencil_autocorrelation_spectrum_pi_0":spectral,
      "remove_2D_origin_spectrum_pi_0":-10,
      "axis_projection_stencil_coefficients":[3,4,5,4,3],
      "axis_projection_autocorrelation_zero_coefficient":75,
      "remove_1D_origin_spectrum_pi":-66,
      "A2_axis_projection_steps":[str(x) for x in axis],
      "A2_30_degree_projection_nonzero_steps":[str(x) for x in angled],
      "total_support_width":str(width),
    }
    path=Path(__file__).with_name("structure_receipt.json")
    path.write_text(json.dumps(out,indent=2)+"\n")
    print("PASS: shell count, discriminants, complete proper automorphism enumeration, projection widths, and negative spectra after zero deletion")

if __name__=="__main__":run()
