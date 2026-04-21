"""
Precise computation of K* by shooting on the rescaled ODE directly.

  σ̃' = σ̃³ − (K/2)(σ̃² − ỹ²)
  ỹ' = −ỹ³
  (σ̃, ỹ)(0) = (1, 1)

K* is the critical K above which σ̃ remains bounded (→ K/2).
"""
import numpy as np
from scipy.integrate import solve_ivp
from mpmath import mp, mpf, findroot

mp.dps = 40  # 40-digit precision for mpmath

# --- scipy float64 for bracketing ---
def rhs(tau, z, K):
    s, y = z
    return [s**3 - 0.5*K*(s*s - y*y), -y**3]

def blew(K, T=1e6, thr=1e6):
    def e(t,z,K): return thr - z[0]
    e.terminal=True; e.direction=-1
    sol = solve_ivp(rhs,[0,T],[1.0,1.0],args=(K,),events=e,method='DOP853',
                    rtol=1e-13,atol=1e-15)
    return len(sol.t_events[0])>0

# Binary search
lo, hi = 3.0, 3.3
for _ in range(50):
    mid = 0.5*(lo+hi)
    if blew(mid): lo = mid
    else: hi = mid
    if hi-lo < 1e-15: break
print(f"K* ≈ {(lo+hi)/2:.12f}  (float64 brackets: [{lo:.12f}, {hi:.12f}])")
print(f"K* - √10 = {(lo+hi)/2 - np.sqrt(10):.6e}")
print(f"K* - π   = {(lo+hi)/2 - np.pi:.6e}")
print(f"K*/2    = {(lo+hi)/4:.12f}")
print(f"K*² / 10 = {((lo+hi)/2)**2 / 10:.12f}")
print(f"(K*/2)² = {((lo+hi)/4)**2:.12f}")
