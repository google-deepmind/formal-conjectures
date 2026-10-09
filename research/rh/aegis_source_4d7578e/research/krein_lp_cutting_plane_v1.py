import sys, math, json, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__file__))
import krein_dual_beyond_log2 as K
L=float(sys.argv[1]); span=float(sys.argv[2]); hb=float(sys.argv[3]); db=float(sys.argv[4]); tag=sys.argv[5]
w=0.02; xi_max=300.0
uk=np.arange(L+w,L+span,w)
xi=np.arange(0,xi_max,0.01)
fine=np.arange(0,xi_max,0.001)
bounds=[(-hb,hb)]*len(uk)+[(-db,db)]*5+[(None,None)]
for it in range(12):
    wt=(xi**2+0.25)**2; h=K.columns(xi,L,w,uk)
    A=np.hstack([-h,wt[:,None]]); c=np.zeros(h.shape[1]+1); c[-1]=-1
    r=K.linprog(c,A_ub=A,b_ub=wt*K.symbol(xi,L),bounds=bounds,method="highs")
    if r.status!=0: print('LP fail',r.message,flush=True); sys.exit(1)
    m,coef=r.x[-1],r.x[:-1]
    # evaluate F with margin m*0.9 on fine grid in chunks
    bad=[]; worst=0
    for s in range(0,len(fine),200000):
        f=fine[s:s+200000]; wf=(f**2+0.25)**2
        F=wf*(K.symbol(f,L)-0.9*m)+K.columns(f,L,w,uk)@coef
        idx=np.where(F<0)[0]; worst=min(worst,F.min() if len(F) else 0)
        bad+=list(f[idx])
    print(f'it={it} m={m:.6f} npts={len(xi)} violations={len(bad)} worst={worst:.3g}',flush=True)
    json.dump({"L":L,"w":w,"span":span,"uk":uk.tolist(),"coef":coef.tolist(),"m":m,"bound":hb},open(f'krein_lp_{tag}.json','w'))
    if not bad: break
    bad=np.array(bad)
    # add violating points plus neighbours
    xi=np.unique(np.concatenate([xi,bad,bad+0.0005,bad-0.0005]))
    xi=xi[xi>=0]
