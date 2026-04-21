"""
Numerical exploration of scalar-cubic dual-rail blow-up with nonzero IC.

System:
  u' = 1 + 3 u^2 v + v^3 - k u v
  v' = u^3 + 3 u v^2 - k u v

Equivalently σ = u + v, y = u - v satisfy
  y' = 1 - y^3
  σ' = 1 + σ^3 - (k/2)(σ^2 - y^2)

We scan (k, U0) for U0 = u(0) with v(0) = 0, and detect whether σ
blows up (reaches a large threshold) before y decays to 1.
"""
import numpy as np
from scipy.integrate import solve_ivp

def rhs(t, z, k):
    u, v = z
    du = 1 + 3*u*u*v + v**3 - k*u*v
    dv = u**3 + 3*u*v*v - k*u*v
    return [du, dv]

def blowup_event(threshold):
    def event(t, z, k):
        u, v = z
        return threshold - (u + v)  # zero when σ hits threshold
    event.terminal = True
    event.direction = -1
    return event

def run(k, U0, V0=0.0, T=20.0, blow_threshold=1e3):
    z0 = [U0, V0]
    sol = solve_ivp(rhs, [0, T], z0, args=(k,), method='RK45',
                    events=blowup_event(blow_threshold), rtol=1e-8, atol=1e-10,
                    max_step=0.01)
    blew = len(sol.t_events[0]) > 0
    t_end = sol.t_events[0][0] if blew else sol.t[-1]
    sigma_end = sol.y[0][-1] + sol.y[1][-1]
    y_end = sol.y[0][-1] - sol.y[1][-1]
    sigma_max = np.max(sol.y[0] + sol.y[1])
    return {
        'k': k, 'U0': U0, 'V0': V0,
        'blew': blew, 't_end': t_end,
        'sigma_end': sigma_end, 'y_end': y_end, 'sigma_max': sigma_max,
    }

print("k    U0    blew?   t_end      σ_max      σ_end      y_end")
print("-" * 72)
for k in [6.1, 7.0, 10.0, 20.0, 50.0, 100.0]:
    for U0 in [0.0, 1.0, 2.0, 5.0, 10.0, 20.0, 50.0]:
        r = run(k, U0)
        mark = "YES" if r['blew'] else "no"
        print(f"{k:4.1f} {U0:5.1f} {mark:>5}  "
              f"{r['t_end']:8.4f}  {r['sigma_max']:9.2e}  "
              f"{r['sigma_end']:9.2e}  {r['y_end']:8.3e}")
