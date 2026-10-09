import sys, json, time
from m105 import *
from pathlib import Path
TOOLS = Path(__file__).resolve().parent
pa=(36,30,12,120,36,40); N=256
def pieces_for(lo,hi,K0,hats,maxdepth=16):
    c=(lo+hi)/2; r=(hi-lo)/2
    if lo==0: c=Q(0); r=hi
    M=wideTM2(pa,K0,hats,r,c); Wp=weightPoly(c)
    out=[]; stack=[(lo,hi,0)]
    while stack:
        a,b,d=stack.pop()
        if checkPiece(pa,K0,N,c,r,M,Wp,a,b): out.append(b)
        elif d>=maxdepth: return None
        else:
            m=(a+b)/2; stack+=[(m,b,d+1),(a,m,d+1)]
    return out
cells=[]; t=Q(0); T1=Q(3000); t0=time.time(); nh=0
while t<T1:
    if t==0: lo,hi,K0=Q(0),Q(3,10),16
    elif t<Q(21,2): lo=t; hi=min(t+1, Q(21,2)) if t>=Q(1,2) else Q(1,2); K0=16
    else: lo=t; K0=0; hi=None
    if hi is None:
        # try cheap (no hats) wide cell r=9/10 first, else hat cell r=1/2
        hi=min(lo+Q(9,5),T1); br=pieces_for(lo,hi,K0,False) if lo>=50 else None
        hats=False
        if br is None:
            hi=min(lo+1,T1); br=pieces_for(lo,hi,K0,True); hats=True
    else:
        hats=True; br=pieces_for(lo,hi,K0,True)
    if lo==0: c=Q(0); r=Q(3,10); 
    if br is None: print('FAIL',float(lo),float(hi)); sys.exit(1)
    nh+=hats
    cells.append({'lo':str(lo),'hi':str(hi),'K0':K0,'hats':hats,'breaks':[str(b) for b in sorted(br)]})
    t=hi
    if len(cells)%100==0: print(len(cells),float(t),'hatcells',nh,'pieces',sum(len(c['breaks']) for c in cells),f'{time.time()-t0:.0f}s',flush=True)
(TOOLS / 'design105.json').write_text(json.dumps(cells), encoding='utf-8')
print('DONE cells',len(cells),'hatcells',nh,'pieces',sum(len(c['breaks']) for c in cells))
