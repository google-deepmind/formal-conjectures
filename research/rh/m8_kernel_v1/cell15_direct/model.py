# Exact-rational model of the direct cell-15 correction lower bound.
import re
from fractions import Fraction as F
from math import factorial
import os
src=open(os.environ.get('EXPLICIT_CORRECTION', 'AEGISOverlay/RHKreinExplicitCorrectionV1.lean')).read()
blk=src[src.index('def hatCoefficient'):src.index('def splineCoefficient')]
HC=[F(x) for x in re.findall(r'(-?\d+(?:/\d+)?)', blk.split('![')[1])]
SP=[F(234102120892757,5000000000),F(-12240399939171,2500000000),F(-2918648959121,10000000000),F(123578990441,10000000000),F(9711997751,10000000000)]
H=[F(j+41,50) for j in range(199)]
W=F(1619,2000)
def cp15(x): return sum((-1)**n*x**(2*n)/factorial(2*n) for n in range(8))
def sp15(x): return sum((-1)**n*x**(2*n+1)/factorial(2*n+1) for n in range(8))
DEN=10**24
def rnd(x): return F(round(x*DEN),DEN)
def model(c,r,lo,hi):
    Q=[rnd(cp15(c*h)) for h in H]; R=[rnd(sp15(c*h)) for h in H]
    # hat poly coefficients: c_j(Q cP(sh) - R sP(sh)) = sum_k a_k s^k
    def gam(k,q,rr): # coefficient of y^k in q cP(y) - rr sP(y)
        sgn=(-1)**(k//2)
        return (sgn*q if k%2==0 else -sgn*rr)/factorial(k)
    B=[sum(HC[j]*H[j]**k*gam(k,Q[j],R[j]) for j in range(199)) for k in range(8)]
    Qw=rnd(cp15(c*W)); Rw=rnd(sp15(c*W))
    # polynomial arithmetic in s
    def mul(p,q):
        out=[F(0)]*(len(p)+len(q)-1)
        for i,a in enumerate(p):
            for j,b in enumerate(q): out[i+j]+=a*b
        return out
    def add(p,q):
        n=max(len(p),len(q)); return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(n)]
    def sc(a,p): return [a*x for x in p]
    cPw=[ (F((-1)**(k//2))*W**k/factorial(k) if k%2==0 else F(0)) for k in range(8)]
    sPw=[ (F((-1)**(k//2))*W**k/factorial(k) if k%2==1 else F(0)) for k in range(8)]
    Pc=add(sc(Qw,cPw),sc(-Rw,sPw)); Ps=add(sc(Rw,cPw),sc(Qw,sPw))
    t=[c,F(1)]
    tp=[[F(1)]]
    for i in range(4): tp.append(mul(tp[-1],t))
    D=[F(0)]
    for i in range(5): D=add(D, sc(SP[i], mul(tp[i], Pc if i%2==0 else Ps)))
    A1=add([F(1)], sc(F(-1,30000), mul(t,t)))
    A2=add([F(1)], sc(F(-19,24000000), mul(t,t)))
    G=add(sc(F(2,50),mul(A1,B)), mul(A2,D))
    floor=G[0]-sum(abs(G[k])*r**k for k in range(1,len(G)))
    # errors
    HB=sum(abs(x) for x in HC); EB=sum(abs(x) for x in SP)
    epsH=sum(abs(HC[j])*(F(6,10**20)+2*abs(cp15(c*H[j])-Q[j])+2*abs(sp15(c*H[j])-R[j])) for j in range(199))
    epsW=F(6,10**20)+2*abs(cp15(c*W)-Qw)+2*abs(sp15(c*W)-Rw)
    epsE=EB*epsW
    th1=F(8,10**14); th2=F(4,10**17)
    err=F(2,50)*(th1*HB+epsH)+th2*EB+epsE
    return dict(Q=Q,R=R,B=B,Qw=Qw,Rw=Rw,D=D,G=G,floor=floor,err=err,epsH=epsH,epsE=epsE,HB=HB,EB=EB)
if __name__=='__main__':
    c=F(5025,65536); r=F(75,65536)
    m=model(c,r,c-r,c+r)
    Wt=F(4724429978091121,72057594037927936); lv=F(292616690003685633,2**64); sL=F(-313119,50000)
    need=Wt*(lv-(sL-F(1,16)))
    print('G deg',len(m['G'])-1,'floor',float(m['floor']),'err',float(m['err']),'need',float(need),'margin',float(m['floor']-m['err']-need))
    print('epsH',float(m['epsH']),'HB',float(m['HB']))
    print([float(x) for x in m['G']])
