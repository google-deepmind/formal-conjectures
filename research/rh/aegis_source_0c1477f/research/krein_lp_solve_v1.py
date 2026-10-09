import sys, math, json, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__file__))
import krein_dual_beyond_log2 as K
L=float(sys.argv[1]); w=0.02; span=4.0; xi_max=300.0; dxi=0.01
xi=np.arange(0,xi_max,dxi); wt=(xi**2+0.25)**2; uk=np.arange(L+w,L+span,w)
h=K.columns(xi,L,w,uk); a_ub=np.hstack([-h,wt[:,None]]); c=np.zeros(h.shape[1]+1); c[-1]=-1
for bound in [float(b) for b in sys.argv[2:]]:
    r=K.linprog(c,A_ub=a_ub,b_ub=wt*K.symbol(xi,L),bounds=[(-bound,bound)]*(h.shape[1]-5)+[(-1e6,1e6)]*5+[(None,None)],method="highs")
    m,coef=r.x[-1],r.x[:-1]
    print(f'bound={bound:g} m={m:.5f} sum|hat c|={np.abs(coef[:-5]).sum():.1f} delta={np.array2string(coef[-5:],precision=3)}',flush=True)
    json.dump({"L":L,"w":w,"span":span,"uk":uk.tolist(),"coef":coef.tolist(),"m":m,"bound":bound},open(f'lp_{L}_{bound:g}.json','w'))
