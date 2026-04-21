"""
Test Dad's hypothesis: is the quintic saddle-node k ≈ 13.01 the same as
the scaling constant K* ≈ 3.158 from the cubic large-U₀ limit?

Short answer: NO. They come from different limits.

  - Zero-init saddle-node (k_SN): has +1 forcing, y² ∈ [0,1].
    Cubic: k = 6.  Quintic: k ≈ 13.01.

  - Large-U₀ rescaled constant (K*): no +1 forcing (drops as U₀^{-3}),
    ỹ(τ) decays as (1+2τ)^{-1/(deg-1)} (not static).
    Cubic: K* ≈ 3.1580...  Quintic: K* = ?

Both are saddle-node-like: negative term (−(K/2)σ²) must suppress positive
term (σ^deg) at some σ-value. But they're different values because:
  (i) the +1 forcing matters for zero-init (ỹ = y starts at 0 then grows
      toward attractor), but is negligible for large U₀,
  (ii) the worst y² = 1 in zero-init vs ỹ(τ) decaying from 1 to 0 in
      large-U₀, which makes the rescaled problem LESS strict.
"""
import numpy as np
from scipy.integrate import solve_ivp

# --- Cubic rescaled saddle-node (static, no +1) ---
# f(σ) = σ³ − (K/2)σ² + (K/2).  f'=0 ⇒ σ = K/3.
# f(K/3) = 0 ⇒ K² = 27 ⇒ K = 3√3 ≈ 5.196.
K_cubic_rescaled_static = np.sqrt(27)

# --- Cubic observed K* from dynamics ---
K_cubic_observed = 3.158048614517

# --- Quintic rescaled saddle-node (static, no +1) ---
# f(σ) = σ⁵ − (K/2)σ² + (K/2). f'(σ) = σ(5σ³ − K).  σ* = (K/5)^{1/3}.
# f(σ*) = σ*⁵ − (K/2)σ*² + K/2 = (K/5)σ*² − (K/2)σ*² + K/2
#       = −(3K/10)σ*² + K/2.
# Set = 0: σ*² = 5/3. With σ*³ = K/5: σ*⁶ = K²/25 = (5/3)³ = 125/27.
# So K² = 25·125/27 = 3125/27 ≈ 115.74.  K = √(3125/27) ≈ 10.758.
K_quintic_rescaled_static = np.sqrt(3125/27)

# --- Quintic zero-init saddle-node (with +1) ---
# f(σ) = 1 + σ⁵ − (K/2)σ² + K/2.  Same critical σ* = (K/5)^{1/3}.
# f(σ*) = 1 − (3K/10)(K/5)^{2/3} + K/2 = 0.
# Solve numerically.
from mpmath import mpf, mp, findroot
mp.dps = 25
def quintic_zero_init_sn(K):
    K = mpf(K)
    return 1 - (3*K/10) * (K/5)**(mpf(2)/3) + K/2
K_quintic_zero_init = findroot(quintic_zero_init_sn, 13.0)

print("=" * 60)
print("SADDLE-NODE THRESHOLDS")
print("=" * 60)
print(f"Cubic zero-init (+1 forcing):         k = 6")
print(f"Cubic rescaled static (no +1):        K = 3√3 ≈ {K_cubic_rescaled_static:.10f}")
print(f"Cubic OBSERVED K* (dynamic ỹ decay):    K* ≈ {K_cubic_observed:.10f}")
print(f"  → dynamic K* < static K_SN by factor {K_cubic_rescaled_static / K_cubic_observed:.4f}")
print()
print(f"Quintic zero-init (+1 forcing):       k ≈ {float(K_quintic_zero_init):.10f}")
print(f"Quintic rescaled static (no +1):      K = √(3125/27) ≈ {K_quintic_rescaled_static:.10f}")
print(f"Quintic OBSERVED K* (dynamic ỹ):      K*_quintic = ? [compute below]")
print()

# --- Compute quintic observed K*_quintic by shooting ---
# Rescaled quintic ODE with u(t) = U₀ φ, t = τ / U₀⁴, K = k / U₀³.
# Large U₀ limit:
#   σ̃' = σ̃⁵ − (K/2)(σ̃² − ỹ²)
#   ỹ' = −ỹ⁵
#   (σ̃, ỹ)(0) = (1, 1).
def rhs_quintic(tau, z, K):
    s, y = z
    return [s**5 - 0.5*K*(s*s - y*y), -y**5]

def blew_quintic(K, T=1e4, thr=1e4):
    def e(t, z, K): return thr - z[0]
    e.terminal = True; e.direction = -1
    sol = solve_ivp(rhs_quintic, [0, T], [1.0, 1.0], args=(K,), events=e,
                    method='RK45', rtol=1e-9, atol=1e-11)
    if len(sol.t_events[0]) > 0:
        return True
    return sol.y[0, -1] > 10.0

print(f"[probe K=0]    blew = {blew_quintic(0.0, T=10, thr=1e3)}")
print(f"[probe K=0.5]  blew = {blew_quintic(0.5)}")
print(f"[probe K=1.0]  blew = {blew_quintic(1.0)}")
print(f"[probe K=2.0]  blew = {blew_quintic(2.0)}")
print(f"[probe K=5.0]  blew = {blew_quintic(5.0)}")
print(f"[probe K=11.0] blew = {blew_quintic(11.0)}")
lo, hi = 0.0, 20.0
for _ in range(60):
    mid = 0.5 * (lo + hi)
    if blew_quintic(mid):
        lo = mid
    else:
        hi = mid
    if hi - lo < 1e-12:
        break
K_quintic_observed = 0.5 * (lo + hi)
print(f"Quintic observed K* (binary search): K*_quintic ≈ {K_quintic_observed:.10f}")
print(f"  → ratio (static / observed): {K_quintic_rescaled_static / K_quintic_observed:.4f}")
print()

# --- Cross-check: is K*_quintic an "obvious" constant? ---
print("Cross-check against common constants for K*_quintic:")
for name, val in [("π", np.pi),
                  ("e", np.e),
                  ("5^{1/2}", np.sqrt(5)),
                  ("5^{2/3}", 5**(2/3)),
                  ("5^{3/2}/2", np.sqrt(125)/2),
                  ("(3/2)^{3/2}·π", (1.5)**1.5 * np.pi),
                  ("√(10)/... ", None)]:
    if val is not None:
        print(f"  K*_q − {name:12s} = {K_quintic_observed - val:+.6e}")

# --- DEEPER: is there a saddle-node interpretation of K*_observed? ---
# For the rescaled ODE, the initial point (1, 1) must lie on the 1D
# stable (center) manifold of (K/2, 0). This is a NONLINEAR EIGENVALUE
# problem, not a polynomial root. The "static saddle-node" K_SN is just
# an upper bound.
print()
print("=" * 60)
print("CONCLUSION")
print("=" * 60)
print("""
Dad's hypothesis: "the quintic k ≈ 13.01 is what K* was for cubic"
  — correct in SPIRIT (both are critical k's for suppressing blow-up),
  — but NOT equal as numbers. They live in different limits:

  [zero-init, +1 forcing] SADDLE-NODE      [large-init, rescaled] EIGENVALUE
  cubic:   k = 6                            K* ≈ 3.158 (< 3√3 = 5.196)
  quintic: k ≈ 13.01                        K* ≈ {K_obs} (< √(3125/27) = 10.76)

Why K* < K_SN:  the rescaled problem has ỹ(τ) DECAYING, so the worst-case
y² = 1 used in the static bound is too pessimistic. The true K* is a
nonlinear eigenvalue — the K for which (1,1) lies on the center manifold
of (K/2, 0). PSLQ on K*_cubic showed no algebraic relation up to deg 10.
""".format(K_obs=K_quintic_observed))
