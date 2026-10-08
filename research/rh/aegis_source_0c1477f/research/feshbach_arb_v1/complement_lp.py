import numpy as np, math, json
from scipy.special import digamma
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack
L=1.05; c_t=1.0; Xi0=40
def S(xi): return np.real(digamma(0.25+0.5j*xi))-math.log(math.pi)-2*math.log(2)/math.sqrt(2)*np.cos(xi*math.log(2))
def col(xs,cc,h,kk): return 2*np.cos(xs*cc)*np.sinc(xs*h/(2*np.pi))**kk*h
specs=[(cc,0.02,2) for cc in np.arange(L+0.02,L+4.0,0.02)]
xg=np.arange(0,300,0.01); wg=(xg**2+0.25)**2; hb=np.array([col(xg,*s) for s in specs]).T; ns=int((xg<=Xi0).sum())
lp=linprog(np.concatenate([np.zeros(len(specs)),np.full(ns,0.01)]),A_ub=hstack([csr_matrix(-hb),csr_matrix((-wg[:ns],(np.arange(ns),np.arange(ns))),shape=(len(xg),ns))]).tocsr(),
  b_ub=wg*(S(xg)-c_t),bounds=[(-1e6,1e6)]*len(specs)+[(0,None)]*ns,method='highs')
s=lp.x[len(specs):]; coef=lp.x[:len(specs)]
print("max|coef|",np.abs(coef).max(),"sum|coef|",np.abs(coef).sum())
json.dump({"L":L,"w":0.02,"uk":[float(c) for c,_,_ in specs],"coef":coef.tolist()+[0.0]*5,"slack":s.tolist(),"xg_step":0.01,"c_t":c_t},open("complement_lp.json","w"))
z0, step = 0.05, 0.25; K = int(np.ceil((40 - z0) / step)) + 1; sbar = []
for k in range(K):
    a = z0 + k * step; b = a + step; m = (xg[:ns] >= a - 0.01) & (xg[:ns] <= b + 0.01)
    sbar.append(float(s[m].max() * 1.02 + 1e-4) if m.any() and s[m].max() > 0 else 0.0)
json.dump({"z0": "0.05", "step": "0.25", "sbar": [repr(v) for v in sbar]}, open("sbar.json", "w"))
