import json
from m105 import *
D=json.load(open('design105N.json'))
pa=(16,30,12,120,16,40); bad=[]
for i,cell in enumerate(D):
    if cell['hats']: cell['deg']=36; continue
    lo=Q(cell['lo']); hi=Q(cell['hi']); K0=cell['K0']; N=cell['N']
    c=(lo+hi)/2; r=(hi-lo)/2
    M=wideTM2(pa,K0,False,r,c); Wp=weightPoly(c); a=lo; ok=True
    for b in map(Q,cell['breaks']):
        if not checkPiece(pa,K0,N,c,r,M,Wp,a,b): ok=False; break
        a=b
    cell['deg']=16 if ok else 36
    if not ok: bad.append(cell['lo'])
json.dump(D,open('design105F.json','w'))
print('nohat cells failing at deg16:',len(bad),bad[:10])
