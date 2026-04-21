"""
Question: for p = 1 - y^3, is there a U0 such that NO k prevents blow-up?

Scan high k for fixed U0.
"""
import numpy as np
from scipy.integrate import solve_ivp

def rhs(t, z, k):
    u, v = z
    return [1 + 3*u*u*v + v**3 - k*u*v,
            u**3 + 3*u*v*v - k*u*v]

def blowup_event(thr):
    def e(t, z, k):
        return thr - (z[0] + z[1])
    e.terminal = True; e.direction = -1
    return e

def run(k, U0, V0=0, T=50, thr=1e4):
    sol = solve_ivp(rhs, [0, T], [U0, V0], args=(k,), method='RK45',
                    events=blowup_event(thr), rtol=1e-9, atol=1e-11, max_step=0.001)
    blew = len(sol.t_events[0]) > 0
    sigma_max = float(np.max(sol.y[0] + sol.y[1]))
    t_blow = float(sol.t_events[0][0]) if blew else None
    return blew, sigma_max, t_blow

print(f"{'U0':>5} {'k':>8} {'blow?':>6} {'σ_max':>10} {'t_blow':>10}")
print("-"*50)
# For U0 fixed, does LARGE k suppress blow-up?
for U0 in [20, 50, 100, 1000]:
    for k in [3*U0, 4*U0, 10*U0, 100*U0, 10000*U0]:
        b, sm, tb = run(k, U0)
        m = "YES" if b else "no"
        tb_s = f"{tb:10.5f}" if tb else "     --   "
        print(f"{U0:5d} {k:8.1f} {m:>6} {sm:10.2e} {tb_s}")
    print()

# Conjecture: critical k*(U0) ~ 3 U0 (from σ=k/3 barrier analysis).
# If k > 3 U0, no blow-up. Confirmed?
print("\n=== Refined critical k near 3*U0 ===")
for U0 in [10, 50, 100, 500]:
    # Binary search for critical k
    lo, hi = U0, 100*U0
    for _ in range(30):
        mid = (lo+hi)/2
        b, _, _ = run(mid, U0, T=10)
        if b: lo = mid
        else: hi = mid
    print(f"U0={U0:5d}  critical k in [{lo:.4f}, {hi:.4f}]   ratio k*/U0 ≈ {(lo+hi)/(2*U0):.4f}")
