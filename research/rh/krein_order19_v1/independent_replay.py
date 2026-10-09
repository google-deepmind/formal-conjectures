"""Independent replay: exact certificate input, direct trigonometric jets, 256-term psi bound.
Does not import regeneration or primary certification code.
"""
import json, sys, math, time, hashlib
from fractions import Fraction as Q
from flint import arb, arb_series, fmpq, ctx
ctx.prec=256
ctx.cap=8

def a(q):
 q=Q(q);return arb(fmpq(q.numerator,q.denominator))
data=json.load(open('certificate.json'))
if data['status']!='CERTIFIED_EXPLICIT_SYMBOL_ONLY':raise ValueError('Not a completed certificate')
if data['RH_PROVEN'] is not False:raise ValueError('Numerical certificate cannot confer RH authority')
cs=[Q(v) for v in data['coefficients']]
us=[Q(v) for v in data['hat_centers']]
L=Q(data['L']);h=Q(data['h']);w=Q(data['hat_width']);m=Q(data['margin']);T=Q(data['tail_start'])
if (L,h,w,m,T,len(cs),len(us),data['order'])!=(Q(4,5),Q(1,1000),Q(1,50),Q(1,16),Q(300),204,199,19):raise ValueError('Unexpected certificate parameters')
if us!=[L+j*w for j in range(1,200)]:raise ValueError('Wrong hat centers')
right=L+19*h;center=L+19*h/2
if data['spline_support']!=[str(L),str(right)]:raise ValueError('Wrong support')
mom8=sum(2*w*abs(c)*(u+w)**8 for c,u in zip(cs[:-5],us))
mom8+=sum(abs(c)*(2/h)**j*right**8 for j,c in enumerate(cs[-5:]))
if mom8!=Q(data['M8']):raise ValueError('Wrong derivative remainder bound')
intervals=[(Q(i[0]),Q(i[1])) for i in data['accepted_intervals']]
if data['interval_lower_bound_denominator']!=str(2**64):raise ValueError('Wrong dyadic denominator')
for item in data['accepted_intervals']:
 if not isinstance(item[2],int) or Q(item[2],2**64)<Q(data['finite_interval_slack_lower']):
  raise ValueError('Stored lower endpoint is below the claimed reserve')
if intervals[0][0]!=0 or intervals[-1][1]!=T:raise ValueError('Wrong interval endpoints')
for i,(l,r) in enumerate(intervals):
 if not l<r:raise ValueError('Empty/reversed interval')
 if i and l!=intervals[i-1][1]:raise ValueError('Gap or overlap in cover')

# Exact binomial cancellation is the polynomial identity showing support
# vanishes beyond the nineteenth knot, including all derivative columns.
for degree in range(19):
 if sum((-1)**k*math.comb(19,k)*k**degree for k in range(20))!=0:
  raise ValueError('Spline support identity failed')

log2=arb(2).log();logpi=arb.pi().log();pp=arb(2).sqrt()*log2
def psi_bound(t):
 v=-a(Q(5792,10000));sq=a(t*t/4)
 for n in range(256):
  u=Q(n)+Q(1,4)
  v+=a(Q(1,n+1)-u/(u*u+t*t/4))
 u=Q(256)+Q(1,4)
 return v-a(Q(3,4)*(1/u+1/u**2))

def h_bound(left,right_end):
 mid=(left+right_end)/2;rad=(right_end-left)/2
 t=arb_series([a(mid),1],prec=8)
 z=t*a(w/2);hat_factor=2*a(w)*(z.sin()/z)**2
 jet=arb_series([0],prec=8)
 for c,u in zip(cs[:-5],us):jet+=a(c)*(t*a(u)).cos()
 jet*=hat_factor
 z=t*a(h/2);bf=(z.sin()/z)**19
 for j,c in enumerate(cs[-5:]):
  phase=(t*a(center)).sin() if j%2 else (t*a(center)).cos()
  jet+=a(c)*t**j*phase*bf
 # Direct sum of bounded Taylor monomials, independent of Horner evaluation.
 dx=arb(0,a(rad));value=arb(0);power=arb(1)
 for k in range(8):
  value+=jet[k]*power
  power*=dx
 return value+arb(0,a(mom8*rad**8/Q(math.factorial(8))))

def check(left,right_end):
 mid=(left+right_end)/2;rad=(right_end-left)/2
 x=arb(a(mid),a(rad))
 v=psi_bound(left)-logpi-pp*(x*log2).cos()-a(m)
 return v+h_bound(left,right_end)/(x*x+arb(1)/4)**2

start=time.time();accepted=0;subdivisions=0;queue=list(reversed(intervals));min_width=T
while queue:
 left,right_end=queue.pop()
 if check(left,right_end)>0:
  accepted+=1;min_width=min(min_width,right_end-left)
 elif right_end-left<Q(1,2**24):raise ValueError('Unable to verify interval')
 else:
  mid=(left+right_end)/2;queue.extend([(mid,right_end),(left,mid)]);subdivisions+=1
tail=psi_bound(T)-logpi-pp-a(m)
tail-=a(sum(2*w*abs(c)/T**4 for c in cs[:-5])+sum(abs(c)*T**(j-4) for j,c in enumerate(cs[-5:])))
if not tail>0:raise ValueError('Tail did not verify')
receipt={'status':'INDEPENDENT_EXPLICIT_SYMBOL_REPLAY_PASS','RH_PROVEN':False,'authority_effect':'NONE','certificate_sha256':hashlib.sha256(open('certificate.json','rb').read()).hexdigest(),'input_cover_intervals':len(intervals),'accepted_intervals':accepted,'additional_subdivisions':subdivisions,'tail_enclosure':str(tail),'spline_support_integer_identities':19,'precision_bits':ctx.prec,'psi_partial_sum_terms':256,'duration_seconds':time.time()-start}
json.dump(receipt,open('independent_receipt.json','w'),indent=2)
print(json.dumps(receipt,indent=2))
