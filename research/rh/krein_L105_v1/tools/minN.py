import json, collections
from m105 import *
pa=(36,30,12,120,36,40)
D=json.load(open('design105.json'))
out=[]; cnt=collections.Counter()
for i,cell in enumerate(D):
    lo=Q(cell['lo']); hi=Q(cell['hi']); K0=cell['K0']; hats=cell['hats']
    c=Q(0) if lo==0 else (lo+hi)/2; r=hi if lo==0 else (hi-lo)/2
    M=wideTM2(pa,K0,hats,r,c); Wp=weightPoly(c); br=[Q(b) for b in cell['breaks']]
    best=None
    for N in [16,32,64,128,256]:
        if N<K0: continue
        a=lo; ok=True
        for b in br:
            if not checkPiece(pa,K0,N,c,r,M,Wp,a,b): ok=False; break
            a=b
        if ok: best=N; break
    assert best is not None, (i, cell['lo'])
    cell['N']=best; cnt[best]+=1; out.append(cell)
    if i%200==0: print(i, cnt, flush=True)
json.dump(out,open('design105N.json','w')); print('DONE',cnt)
