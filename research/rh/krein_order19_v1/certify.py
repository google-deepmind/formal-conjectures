"""Rigorous ball-arithmetic check of a regenerated, exact-rational Krein symbol candidate.

This certifies only the explicit analytic symbol inequality. No Lean theorem,
Mellin/Weil symbol bridge, or RH claim follows from this executable alone.
"""
from fractions import Fraction as Q
from math import factorial
import json, hashlib, time
from flint import arb, acb, arb_series, fmpq, ctx
ctx.prec=512
ctx.cap=8

def A(q):
    q=Q(q)
    return arb(fmpq(q.numerator,q.denominator))

raw=json.load(open('candidate.json'))
# Nearest decimal rational with fixed denominator. Exact integer consumption.
den=10**10
coeff=[Q(round(Q(x)*den),den) for x in raw['coefficients']]
m=Q(1,16); L=Q(4,5); w=Q(1,50); h=Q(1,1000); order=19
centers=[L+j*w for j in range(1,200)]
right=L+order*h; cen=L+order*h/2
ca=[A(q) for q in coeff]
log2=arb(2).log(); pi=arb.pi(); logpi=pi.log(); prime=arb(2).sqrt()*log2
M8=sum(2*w*abs(c)*(u+w)**8 for c,u in zip(coeff[:-5],centers))
M8+=sum(abs(c)*2**j/h**j*right**8 for j,c in enumerate(coeff[-5:]))
remcoeff=A(M8/Q(factorial(8)))

def Hseries(mid):
    t=arb_series([A(mid),arb(1)],prec=8)
    angle=t*A(w)
    cx=angle.cos()
    # u_j=(40+j)/50, 1 <= j <=199: exact Chebyshev recurrence.
    cprev=arb_series([1],prec=8); ccur=cx
    tr=arb_series([0],prec=8)
    for k in range(2,240):
      cn=2*cx*ccur-cprev
      cprev,ccur=ccur,cn
      if k>=41: tr+=ca[k-41]*cn
    z=t*A(w/2)
    hat=(z.sin()/z)**2*A(2*w)*tr
    z=t*A(h/2)
    smooth=(z.sin()/z)**order
    cs=(t*A(cen)).cos(); sn=(t*A(cen)).sin()
    bd=arb_series([0],prec=8)
    for j,c in enumerate(ca[-5:]): bd+=c*t**j*(cs if j%2==0 else sn)
    return hat+smooth*bd

def Hinterval(lo,hi):
    mid=(lo+hi)/2; rad=(hi-lo)/2
    jet=Hseries(mid)
    dx=arb(0,A(rad))
    v=arb(0)
    for k in range(7,-1,-1): v=v*dx+jet[k]
    return v+arb(0,remcoeff*A(rad)**8)

def digamma_lower(t,N=128):
    # psi(1/4+it/2).re = -gamma + sum_{n>=0}(1/(n+1)
    #   -(n+1/4)/((n+1/4)^2+t^2/4)).  Use source-proved gamma<.5792.
    # Tail >= -(3/4) sum_{n>=N}(n+1/4)^(-2)
    #      >= -(3/4)((N+1/4)^(-1)+(N+1/4)^(-2)).
    tt=A(t)**2/4
    v=-A(Q(5792,10000))
    for n in range(N):
      a=A(Q(n)+Q(1,4))
      v+=A(Q(1,n+1))-a/(a*a+tt)
    q=Q(N)+Q(1,4)
    return v-A(Q(3,4)*(1/q+1/q**2))

def lower(lo,hi):
    mid=(lo+hi)/2; rad=(hi-lo)/2
    x=arb(A(mid),A(rad))
    # The real digamma series is termwise nondecreasing for nonnegative t;
    # evaluate its rigorous lower endpoint at the left endpoint exactly.
    s=digamma_lower(lo)-logpi-prime*(x*log2).cos()
    H=Hinterval(lo,hi)
    return s+H/(x*x+arb(1)/4)**2-A(m)

def tail(T):
    # Re digamma(1/4+it/2) is nondecreasing in |t| by its absolutely
    # convergent real series; drop cos and sinc factors in magnitude.
    base=digamma_lower(T)-logpi-prime-A(m)
    bound=sum(A(2*w*abs(c)) for c in coeff[:-5])/A(T)**4
    bound+=sum(A(abs(c))/A(T)**(4-j) for j,c in enumerate(coeff[-5:]))
    return base-bound

def lower_dyadic64(v):
    mantissa,exponent=v.lower().man_exp()
    mantissa=int(mantissa);exponent=int(exponent)+64
    result=(mantissa<<exponent) if exponent>=0 else mantissa//(1<<(-exponent))
    # Conversion rounds DOWN in exact integer arithmetic.
    if not A(Q(result,2**64))<=v.lower():
      raise ArithmeticError('Lower-endpoint serialization did not round down')
    return result

if __name__=='__main__':
    t0=time.time(); T=Q(300)
    print('tail lower',tail(T),flush=True)
    if not tail(T)>0: raise SystemExit('TAIL FAILED')
    # Intervals have exact rational dyadic endpoints. Breadth-first is not needed.
    stack=[(Q(0),T)]; accepted=[]; visited=0; failures=[]
    while stack:
      lo,hi=stack.pop(); visited+=1
      if hi-lo>Q(1,2):
        mid=(lo+hi)/2; stack.extend([(mid,hi),(lo,mid)]); continue
      v=lower(lo,hi)
      if v>A(Q(1,100000)):
        accepted.append((lo,hi,v))
      elif hi-lo<Q(1,2**22):
        failures.append((lo,hi,str(v))); break
      else:
        mid=(lo+hi)/2; stack.extend([(mid,hi),(lo,mid)])
      if visited%2000==0: print('progress',visited,'accepted',len(accepted),'at',float(lo),'secs',time.time()-t0,flush=True)
    certificate={'schema':'AEGIS_KREIN_REGENERATED_RATIONAL_SYMBOL_V1','status':'CERTIFIED_EXPLICIT_SYMBOL_ONLY' if not failures else 'FAILED','authority_effect':'NONE','RH_PROVEN':False,'source_sha':'2c3d041b633147ec97c7ef753aa9d157a47bb9f5','source_blob':'cb5aaa842b90b49172bbc129f0e3a8ee93923a84','original_order19_reproduced':False,'regenerated_basis':True,'L':str(L),'h':str(h),'order':order,'margin':str(m),'hat_width':str(w),'hat_centers':[str(v) for v in centers],'coefficients':[str(v) for v in coeff],'spline_support':[str(L),str(right)],'spline_center':str(cen),'M8':str(M8),'tail_start':str(T),'tail_enclosure':str(tail(T)),'accepted_intervals':[[str(a),str(b),lower_dyadic64(v)] for a,b,v in accepted],'interval_lower_bound_denominator':str(2**64),'finite_interval_slack_lower':'1/100000','psi_partial_sum_terms':128,'gamma_upper':'362/625','failures':[[str(a),str(b),v] for a,b,v in failures],'precision_bits':ctx.prec,'python_flint_version':'0.9.0','elapsed_seconds':time.time()-t0,'notes':'Ball arithmetic is a rigorous numerical certificate for the explicit symbol, not a kernel theorem or repository Weil-form bridge. The monotonicity and Taylor remainder bounds have external mathematical justifications documented separately.'}
    with open('certificate.json','w') as f: json.dump(certificate,f,indent=2)
    print(certificate['status'],'intervals',len(accepted),'secs',time.time()-t0,flush=True)
