#!/usr/bin/env python3
"""Fast convergence diagnostic for the committed Krein primal basis.

Reproduces the finite-dimensional basis used by krein_dual_beyond_log2.py
without the 1200-point x quadrature. Numerical diagnostic only: a positive
finite-section minimum is only an upper bound on the unrestricted infimum.
RH_PROVEN=false; authority_effect=NONE.
"""
from __future__ import annotations
import argparse, json, math, time
import numpy as np
from scipy.linalg import eigh
from scipy.special import digamma

LOG2=math.log(2.0); LOG3=math.log(3.0)

def symbol(xi,L):
    if not L < LOG3:
        raise ValueError("valid only for L < log(3); prime 3 enters at/above log(3)")
    out=np.real(digamma(0.25+0.5j*xi))-math.log(math.pi)
    if L>LOG2:
        out-=math.sqrt(2.0)*LOG2*np.cos(xi*LOG2)
    return out

def expansions(L,n):
    a=math.pi/L; exps=[]
    for k in range(1,n+1):
        exps.append({k-1:0.5*(0.25+((k-1)*a)**2),
                     k+1:-0.5*(0.25+((k+1)*a)**2)})
    return a,exps

def gram(L,n):
    _,exps=expansions(L,n); G=np.zeros((n,n))
    for i in range(n):
        for j in range(i,n):
            v=0.0
            for mode,ci in exps[i].items():
                cj=exps[j].get(mode)
                if cj is not None:
                    v+=ci*cj*(L if mode==0 else L/2.0)
            G[i,j]=G[j,i]=v
    return G

def _I(q,L):
    return L*np.exp(-0.5j*q*L)*np.sinc(q*L/(2.0*math.pi))

def cosine_transform(xi,L,mode,a):
    return 0.5*(_I(xi-mode*a,L)+_I(xi+mode*a,L))

def quadratic_matrix(L,n,T,dt,chunk):
    a,_=expansions(L,n); Q=np.zeros((n,n))
    xi_all=np.arange(dt/2.0,T,dt)
    for start in range(0,len(xi_all),chunk):
        xi=xi_all[start:start+chunk]
        C=np.empty((n+2,len(xi)),complex)
        for mode in range(n+2):
            C[mode]=cosine_transform(xi,L,mode,a)
        F=np.empty((n,len(xi)),complex)
        for k in range(1,n+1):
            A=0.5*(0.25+((k-1)*a)**2)
            B=-0.5*(0.25+((k+1)*a)**2)
            F[k-1]=A*C[k-1]+B*C[k+1]
        s=symbol(xi,L)
        Q+=((F*s)@F.conj().T).real*dt/math.pi
    return Q

def run(L,nmax,T,dt,chunk,checkpoints):
    t0=time.time(); G=gram(L,nmax); Q=quadratic_matrix(L,nmax,T,dt,chunk)
    vals={}
    for n in checkpoints:
        vals[str(n)]=float(eigh(Q[:n,:n],G[:n,:n],eigvals_only=True,
                                subset_by_index=[0,0])[0])
    return {
      "schema":"aegis.rh.krein-primal-convergence.v2",
      "status":"NUMERICAL_DIAGNOSTIC_ONLY",
      "authority_effect":"NONE","rh_proven":False,"L":L,
      "L_lt_log3":bool(L<LOG3),
      "basis":"(1/4-D^2)(sin(pi*x/L)*sin(k*pi*x/L)), k=1..n",
      "quadrature":{"xi_midpoint_T":T,"dt":dt,"chunk":chunk},
      "lambda_min_by_dimension":vals,
      "interpretation":"Finite-subspace minima are upper bounds on the unrestricted infimum; positive values do not prove positivity.",
      "elapsed_seconds":time.time()-t0}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--L",type=float,default=1.05)
    ap.add_argument("--nmax",type=int,default=256)
    ap.add_argument("--T",type=float,default=3000.0)
    ap.add_argument("--dt",type=float,default=0.02)
    ap.add_argument("--chunk",type=int,default=4000)
    ap.add_argument("--checkpoints",default="32,64,96,128,160,192,224,256")
    ap.add_argument("--out")
    a=ap.parse_args(); cps=[int(x) for x in a.checkpoints.split(",") if x]
    out=run(a.L,a.nmax,a.T,a.dt,a.chunk,cps); s=json.dumps(out,indent=2,sort_keys=True)
    print(s)
    if a.out:
        open(a.out,"w",encoding="utf-8").write(s+"\n")
if __name__=="__main__": main()
