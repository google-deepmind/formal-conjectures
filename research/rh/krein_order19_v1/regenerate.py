"""Regenerate a genuine-function Krein candidate. Numerical discovery only."""
import json, math, os
import numpy as np
from scipy.optimize import linprog
from scipy.special import digamma

L=.8; w=.02; order=19; h=.001
uk=L+w*np.arange(1,200)
center=L+order*h/2
def symbol(t):
    return digamma(.25+.5j*t).real-math.log(math.pi)-math.sqrt(2)*math.log(2)*np.cos(t*math.log(2))
def columns(t):
    t=np.asarray(t)
    hats=2*w*np.sinc(t*w/(2*math.pi))[:,None]**2*np.cos(t[:,None]*uk)
    smooth=np.sinc(t*h/(2*math.pi))**order
    edge=np.array([smooth*t**j*(np.cos(t*center) if j%2==0 else np.sin(t*center)) for j in range(5)]).T
    return np.hstack([hats,edge])
def weight(t): return (t*t+.25)**2

if __name__=='__main__':
    t=np.arange(0,300,.02)
    cols=columns(t)/weight(t)[:,None]
    a=np.hstack([-cols,np.ones((len(t),1))])
    c=np.zeros(a.shape[1]); c[-1]=-1
    r=linprog(c,A_ub=a,b_ub=symbol(t),bounds=[(-1e5,1e5)]*(a.shape[1]-1)+[(None,None)],method='highs',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    print(r.message,flush=True)
    if not r.success: raise SystemExit(1)
    coef=r.x[:-1]; m=r.x[-1]
    print('margin',m,'maxcoef',abs(coef).max(),'edge',coef[-5:],flush=True)
    out={'status':'NUMERICAL_CANDIDATE_ONLY','L':'4/5','order':order,'h':'1/1000','hat_width':'1/50','hat_centers':[str(v) for v in uk],'coefficients':[str(v) for v in coef],'margin':str(m),'source_sha':'2c3d041b633147ec97c7ef753aa9d157a47bb9f5','candidate_basis':'199 even hats plus derivatives 0..4 of an order19 normalized cardinal B-spline supported on [L,L+19h], reflected evenly'}
    with open('candidate.json','w') as f: json.dump(out,f,indent=2)
    worst=(math.inf,None)
    for lo in range(0,3000,25):
      tt=np.arange(lo,lo+25,.002)
      vals=symbol(tt)+columns(tt)@coef/weight(tt)
      j=int(vals.argmin())
      if vals[j]<worst[0]: worst=(float(vals[j]),float(tt[j]))
    print('fine grid',worst,flush=True)
