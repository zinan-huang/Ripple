import numpy as np
from scipy.integrate import solve_ivp

def rhs(t, z, k):
    u, v = z
    return [1 + 3*u*u*v + v**3 - k*u*v,
            u**3 + 3*u*v*v - k*u*v]

def blew(k, U0, T=10, thr=1e4):
    def e(t,z,k):
        return thr - (z[0]+z[1])
    e.terminal=True; e.direction=-1
    try:
        sol = solve_ivp(rhs,[0,T],[U0,0],args=(k,),events=e,rtol=1e-8,atol=1e-10,max_step=0.01)
        return len(sol.t_events[0]) > 0
    except Exception:
        return True  # treat failure as blowup

# Binary search critical k for each U0
print("U0       critical k*    k*/U0")
for U0 in [2, 5, 10, 50, 100, 500]:
    lo, hi = 0.5*U0, 10*U0
    for _ in range(20):
        mid = 0.5*(lo+hi)
        if blew(mid, U0): lo = mid
        else: hi = mid
    print(f"{U0:5d}  {(lo+hi)/2:10.4f}   {(lo+hi)/(2*U0):.4f}")
