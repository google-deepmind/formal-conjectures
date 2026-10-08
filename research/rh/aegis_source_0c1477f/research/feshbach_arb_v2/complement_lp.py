import numpy as np, math, json
from scipy.special import digamma
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack
import sys
L=float(sys.argv[1]); c_t=float(sys.argv[2]); Xi0=float(sys.argv[3]); STEP=float(sys.argv[4]); Z0S=sys.argv[5] if len(sys.argv)>5 else '0.05'
def _lam(q):
    for p in range(2,q+1):
        if q%p==0:
            m=q
            while m%p==0: m//=p
            return p if m==1 else 0
    return 0
PP=[(math.log(q),2*math.log(_lam(q))/math.sqrt(q)) for q in range(2,int(math.exp(L))+2) if _lam(q) and math.log(q)<L]
def S(xi): return np.real(digamma(0.25+0.5j*xi))-math.log(math.pi)-sum(a*np.cos(xi*lq) for lq,a in PP)
def col(xs,cc,h,kk): return 2*np.cos(xs*cc)*np.sinc(xs*h/(2*np.pi))**kk*h
specs=[(cc,0.02,2) for cc in np.arange(L+0.02,L+4.0,0.02)]
xg=np.arange(0,max(300,2.2*Xi0),0.02); wg=(xg**2+0.25)**2; hb=np.array([col(xg,*s) for s in specs]).T; ns=int((xg<=Xi0).sum())
lp=linprog(np.concatenate([np.zeros(len(specs)),np.full(ns,0.02)]),A_ub=hstack([csr_matrix(-hb),csr_matrix((-wg[:ns],(np.arange(ns),np.arange(ns))),shape=(len(xg),ns))]).tocsr(),
  b_ub=wg*(S(xg)-c_t),bounds=[(-1e6,1e6)]*len(specs)+[(0,None)]*ns,method='highs')
s=lp.x[len(specs):]; coef=lp.x[:len(specs)]
print("max|coef|",np.abs(coef).max(),"sum|coef|",np.abs(coef).sum())
json.dump({"L":L,"w":0.02,"uk":[float(c) for c,_,_ in specs],"coef":coef.tolist()+[0.0]*5,"slack":s.tolist(),"xg_step":0.02,"c_t":c_t},open("complement_lp.json","w"))
z0, step = float(Z0S), STEP; K = int(np.ceil((Xi0 - z0) / step)) + 1; sbar = []
for k in range(K):
    a = z0 + k * step; b = a + step; m = (xg[:ns] >= a - 0.02) & (xg[:ns] <= b + 0.02)
    sbar.append(float(s[m].max() * 1.02 + 1e-4) if m.any() and s[m].max() > 0 else 0.0)
json.dump({"z0": Z0S, "step": repr(STEP), "sbar": [repr(v) for v in sbar]}, open("sbar.json", "w"))
