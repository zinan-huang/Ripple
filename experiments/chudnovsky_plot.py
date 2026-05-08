"""
Generate the figure for blog 010: Chudnovsky π-PIVP convergence.

Three panels:
  (a) P(τ) climbing to π — direct trajectory, with a horizontal line at π.
  (b) log10|P(τ) − π| vs τ — linear decay confirms the eigenvalue −12·M_∞.
  (c) The series-sum module: log10|M_K − M_∞| vs K — geometric decay
      with ratio 1/640320^3 per term.
"""
import numpy as np
import matplotlib.pyplot as plt
from mpmath import mpf, mp, log10, sqrt
mp.dps = 80

A = mpf(13591409)
B = mpf(545140134)
ROOT = mpf(640320)
PI = mp.pi


def M_partial(K):
    """Σ_{k=0}^{K-1} (-1)^k a_k (A+Bk)/640320^{3k}."""
    a = mpf(1)
    z = 1 / ROOT**3
    s = A
    sign = -1
    zpow = z
    for k in range(1, K):
        a = a * (6*k-5)*(6*k-4)*(6*k-3)*(6*k-2)*(6*k-1)*(6*k) / (
            (3*k-2)*(3*k-1)*(3*k)*k**3
        )
        s += sign * a * (A + B*k) * zpow
        zpow *= z
        sign = -sign
    return s


def main():
    M_inf = M_partial(K=30)  # converged to ~80 digits
    rate = 12 * M_inf
    P_inf = ROOT**(mpf(3)/2) / rate  # = π
    print(f"M_∞ = {float(M_inf):.6e}")
    print(f"rate 12·M_∞ = {float(rate):.6e}")
    print(f"P_∞ = {float(P_inf):.20f}")
    print(f"π    = {float(PI):.20f}")

    # Inverter Euler simulation: log every 100 steps the value of P and the error.
    T_max = 1e-7
    N = 50000
    dt = T_max / N
    P = mpf(0)
    times, errs, P_vals = [], [], []
    src = ROOT**(mpf(3)/2)
    for n in range(N + 1):
        if n % 100 == 0:
            err = abs(P_inf - P)
            times.append(float(n * dt))
            P_vals.append(float(P))
            errs.append(float(log10(err)) if err > mpf(0) else -80.0)
        P = P + (src - rate * P) * dt

    times = np.array(times)
    errs = np.array(errs)
    P_vals = np.array(P_vals)

    # Linear fit on the log-error panel
    mask = (times > 1e-8) & (times < 9e-8)
    slope, intercept = np.polyfit(times[mask], errs[mask], 1)
    fitted_rate = -slope * np.log(10)
    symbolic_rate = float(rate)
    print(f"slope = {slope:.4e}")
    print(f"fitted rate = {fitted_rate:.4e}")
    print(f"symbolic    = {symbolic_rate:.4e}")
    print(f"ratio       = {fitted_rate/symbolic_rate:.6f}")

    # Panel (b): series-sum convergence
    Ks = list(range(1, 12))
    M_errs = []
    for K in Ks:
        M_K = M_partial(K)
        d = abs(M_inf - M_K)
        if d > 0:
            M_errs.append(float(log10(d)))
        else:
            M_errs.append(-80.0)

    fig, axes = plt.subplots(1, 3, figsize=(15, 4))

    pi_val = float(PI)

    ax = axes[0]
    ax.plot(times * 1e8, P_vals, '-', lw=1.5, color='C0')
    ax.axhline(pi_val, color='k', ls='--', lw=1, label=r'$\pi$')
    ax.set_xlabel(r'$\tau$  (units of $10^{-8}$)')
    ax.set_ylabel(r'$P(\tau)$')
    ax.set_title(r'(a) $P(\tau) \to \pi$ directly')
    ax.set_ylim(-0.05 * pi_val, 1.05 * pi_val)
    ax.legend(loc='lower right', fontsize=10)
    ax.grid(alpha=0.3)

    ax = axes[1]
    ax.plot(times * 1e8, errs, 'o', ms=3, label='Euler simulation')
    line_y = slope * times + intercept
    ax.plot(times * 1e8, line_y, 'r-', lw=1.2,
            label=r'fit, slope $= -12 M_\infty / \ln 10$')
    ax.set_xlabel(r'$\tau$  (units of $10^{-8}$)')
    ax.set_ylabel(r'$\log_{10} \, | P(\tau) - \pi |$')
    ax.set_title(r'(b) Exponential decay of the error')
    ax.legend(loc='upper right', fontsize=9)
    ax.grid(alpha=0.3)

    ax = axes[2]
    ax.plot(Ks, M_errs, 'o-', ms=4)
    ref_slope = -3 * float(log10(ROOT))
    ref_y = [M_errs[0] + ref_slope * (k - Ks[0]) for k in Ks]
    ax.plot(Ks, ref_y, 'r--', lw=1,
            label=f'slope $-3 \\log_{{10}} 640320 \\approx {ref_slope:.2f}$')
    ax.set_xlabel(r'$K$  (number of series terms)')
    ax.set_ylabel(r'$\log_{10} \, | M_K - M_\infty |$')
    ax.set_title(r'(c) Series-sum module: $M_K \to M_\infty$')
    ax.legend(loc='upper right', fontsize=9)
    ax.grid(alpha=0.3)

    plt.tight_layout()
    out = '/Users/huangx/.openclaw/workspace/zinan/infsup-site/static/img/chudnovsky-convergence.png'
    plt.savefig(out, dpi=140, bbox_inches='tight')
    print(f"Saved {out}")


if __name__ == '__main__':
    main()
