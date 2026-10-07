"""Controlled numerical discovery; no interval or theorem authority.
Same total spline support 19/1000, center, LP constraints and coefficient cap.
"""
import hashlib, json, math, os, platform, time
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
import scipy
from scipy.optimize import linprog
from scipy.special import digamma
from pathlib import Path
ROOT=Path(__file__).resolve().parent
WIDTH=.019
L=.8
W=.02
CENTERS=L+W*np.arange(1,200)
C=L+WIDTH/2

def symbol(t):
    return digamma(.25+.5j*t).real-math.log(math.pi)-math.sqrt(2)*math.log(2)*np.cos(t*math.log(2))

def envelope(t, steps):
    return np.prod(np.sinc(np.outer(t,steps)/(2*math.pi)),axis=1)

def columns(t, steps):
    hats=2*W*np.sinc(t*W/(2*math.pi))[:,None]**2*np.cos(t[:,None]*CENTERS)
    smooth=envelope(t,steps)
    edge=np.array([smooth*t**j*(np.cos(t*C) if j%2==0 else np.sin(t*C)) for j in range(5)]).T
    return np.hstack([hats,edge])

def weight(t): return (t*t+.25)**2

def run(name,steps):
    start=time.monotonic()
    t=np.arange(0,300,.02)
    cols=columns(t,steps)/weight(t)[:,None]
    aa=np.hstack([-cols,np.ones((len(t),1))])
    objective=np.zeros(aa.shape[1]); objective[-1]=-1
    result=linprog(objective,A_ub=aa,b_ub=symbol(t),bounds=[(-1e5,1e5)]*(aa.shape[1]-1)+[(None,None)],method="highs",options={"dual_feasibility_tolerance":1e-9,"primal_feasibility_tolerance":1e-9})
    receipt={"name":name,"status":"NUMERICAL_DISCOVERY_ONLY","solver_status":result.message,"success":bool(result.success),"step_lengths":list(steps),"step_sum":sum(steps)}
    if result.success:
        coef=result.x[:-1]
        worst=(math.inf,None)
        for lo in range(0,3000,25):
            tt=np.arange(lo,lo+25,.002)
            values=symbol(tt)+columns(tt,steps)@coef/weight(tt)
            j=int(values.argmin())
            if values[j]<worst[0]: worst=(float(values[j]),float(tt[j]))
        edge=cols[:,-5:]
        edge=edge/np.linalg.norm(edge,axis=0)
        receipt.update(lp_margin=float(result.x[-1]),fine_grid_minimum=worst,maximum_absolute_coefficient=float(abs(coef).max()),column_normalized_edge_condition=float(np.linalg.cond(edge)),coefficients=coef.tolist())
    receipt["elapsed_seconds"]=time.monotonic()-start
    print(name,receipt.get("lp_margin"),receipt.get("fine_grid_minimum"),flush=True)
    return receipt

if __name__=="__main__":
    cases=[(f"cardinal_order_{n}",[WIDTH/n]*n) for n in range(17,22)]
    # A2 directions at 0,60,120 degrees, each repeated six times.
    # Horizontal projection has lengths delta,delta/2,delta/2.
    delta=WIDTH/12
    cases.append(("a2_axis_projection_18_directions",[delta,delta/2,delta/2]*6))
    # At 30 degrees, six directions are orthogonal and disappear;
    # the twelve remaining projected lengths coincide after width normalization.
    cases.append(("a2_30_degree_projection_18_directions",[WIDTH/12]*12))
    output={"authority_effect":"NONE","source_sha":"ab791e06dd9368fdcc8684b8bc8dec2feb0ee3ac","source_script_sha256":hashlib.sha256((ROOT.parent/"krein_order19_v1/regenerate.py").read_bytes()).hexdigest(),"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__,"total_spline_support":"19/1000","spline_center":"1619/2000","L":"4/5","coefficient_cap":100000,"training_grid":"[0,300), step 1/50","evaluation_grid":"[0,3000), step 1/500","cases":[]}
    for name,steps in cases:
        output["cases"].append(run(name,steps))
        (ROOT/"order_comparison.json").write_text(json.dumps(output,indent=2)+"\n")
