"""Experiment 10: Intermediate-degree sweep.

For each n in {5, 10, 20, 40}, study the dual-rail dynamics for
    y' = -q_n(y),   q_n(y) = y^n - y - 1
starting from y(0) = 0. Each q_n has a unique positive real root
lambda_n in (1, 2) (the n-bonacci constant), and lambda_n is stable
under y' = -q_n(y) since q_n'(lambda) = n*lambda^(n-1) - 1 > 0.

Extracts k* (minimum k for which the dual-rail k-sweep succeeds),
reports k*/M_0 vs n, and fits the scaling C(deg).

Same numerics as exp 09: LSODA, rtol=1e-6, atol=1e-8, max_step=0.01,
T=5.0, 1000 eval points.
"""
from __future__ import annotations

import os
import numpy as np
from math import comb
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))

DEGREES = [5, 10, 20, 40]

# LSODA settings (matching exp 09)
RTOL = 1e-6
ATOL = 1e-8
MAX_STEP = 0.01
T_END = 5.0
N_EVAL = 1000

# k-sweep range (same shape as exp 09)
K_LO_REL = 0.1     # k_lo = 0.1 * M_0
K_HI_REL = 1000.0  # k_hi = 1000 * M_0
N_K = 10


def build_polynomial(n):
    """Return the coefficient list c[0..n] for q_n(y) = y^n - y - 1.

    c[0] = -1, c[1] = -1, c[n] = 1, rest 0.
    """
    c = [0] * (n + 1)
    c[0] = -1
    c[1] = -1
    c[n] = 1
    return c


def q_eval(coeffs, y):
    r = 0.0
    for ck in reversed(coeffs):
        r = r * y + ck
    return r


def q_prime_eval(coeffs, y):
    r = 0.0
    deg = len(coeffs) - 1
    for k in reversed(range(1, deg + 1)):
        r = r * y + k * coeffs[k]
    return r


def find_lambda(coeffs):
    """Unique positive real root in (1, 2) for q_n(y) = y^n - y - 1."""
    return brentq(lambda y: q_eval(coeffs, y), 1.0 + 1e-6, 2.0)


def split_monomials(coeffs, sign):
    """Expand sign * q(u - v) into (plus_terms, minus_terms).

    Each term is (exp_u, exp_v, coef) with coef > 0.
    """
    deg = len(coeffs) - 1
    plus_terms = []
    minus_terms = []
    for k in range(deg + 1):
        rk = sign * coeffs[k]
        if rk == 0:
            continue
        sign_rk = 1 if rk > 0 else -1
        abs_rk = abs(rk)
        for j in range(k + 1):
            mono_sign = sign_rk * ((-1) ** j)
            coef = float(abs_rk) * float(comb(k, j))
            term = (k - j, j, coef)
            if mono_sign > 0:
                plus_terms.append(term)
            else:
                minus_terms.append(term)
    return plus_terms, minus_terms


def make_rail_evaluator(plus_terms, minus_terms, deg):
    PLUS_EU = np.array([t[0] for t in plus_terms], dtype=np.int64)
    PLUS_EV = np.array([t[1] for t in plus_terms], dtype=np.int64)
    PLUS_C = np.array([t[2] for t in plus_terms], dtype=np.float64)
    MINUS_EU = np.array([t[0] for t in minus_terms], dtype=np.int64)
    MINUS_EV = np.array([t[1] for t in minus_terms], dtype=np.int64)
    MINUS_C = np.array([t[2] for t in minus_terms], dtype=np.float64)

    def eval_rails(u, v):
        up = np.ones(deg + 1)
        vp = np.ones(deg + 1)
        for i in range(1, deg + 1):
            up[i] = up[i - 1] * u
            vp[i] = vp[i - 1] * v
        pp = float(np.sum(PLUS_C * up[PLUS_EU] * vp[PLUS_EV])) if PLUS_C.size else 0.0
        pm = float(np.sum(MINUS_C * up[MINUS_EU] * vp[MINUS_EV])) if MINUS_C.size else 0.0
        return pp, pm

    return eval_rails


def run_for_degree(n):
    print(f"\n{'='*60}", flush=True)
    print(f"[n={n}] starting", flush=True)
    print(f"{'='*60}", flush=True)

    coeffs = build_polynomial(n)
    lam = find_lambda(coeffs)
    qp_lam = q_prime_eval(coeffs, lam)
    sign = -1 if qp_lam > 0 else +1
    print(f"[n={n}] λ = {lam:.10f}, q'(λ) = {qp_lam:.4e}, SIGN = {sign}", flush=True)

    plus_terms, minus_terms = split_monomials(coeffs, sign)
    print(f"[n={n}] #plus = {len(plus_terms)}, #minus = {len(minus_terms)}", flush=True)

    eval_rails = make_rail_evaluator(plus_terms, minus_terms, n)

    pp_lam, pm_lam = eval_rails(lam, 0.0)
    M0 = max(pp_lam, pm_lam)
    print(f"[n={n}] p̂⁺(λ,0) = {pp_lam:.6e}, p̂⁻(λ,0) = {pm_lam:.6e}, M₀ = {M0:.6e}", flush=True)

    # --- Original trajectory
    def original_rhs(_t, state):
        (y,) = state
        return [sign * q_eval(coeffs, y)]

    t_eval = np.linspace(0.0, T_END, N_EVAL)
    print(f"[n={n}] solving original trajectory...", flush=True)
    sol_orig = solve_ivp(
        original_rhs, (0.0, T_END), [0.0], t_eval=t_eval,
        rtol=1e-8, atol=1e-10, method="LSODA", max_step=0.01,
    )
    print(f"[n={n}]   orig success={sol_orig.success}, final y = {sol_orig.y[0][-1]:.6f}",
          flush=True)

    # --- k sweep
    def dualrail_rhs(k):
        def rhs(_t, state):
            u, v = state
            if not (np.isfinite(u) and np.isfinite(v)):
                return [0.0, 0.0]
            pp, pm = eval_rails(u, v)
            ann = k * u * v
            return [pp - ann, pm - ann]
        return rhs

    k_lo = M0 * K_LO_REL
    k_hi = M0 * K_HI_REL
    ks = np.logspace(np.log10(k_lo), np.log10(k_hi), N_K)

    results = []
    for idx, k in enumerate(ks):
        print(f"[n={n}] [{idx+1}/{N_K}] k = {k:.4e} (k/M₀ = {k/M0:.3e})...",
              flush=True)
        try:
            sol = solve_ivp(
                dualrail_rhs(k), (0.0, T_END), [0.0, 0.0], t_eval=t_eval,
                rtol=RTOL, atol=ATOL, method="LSODA", max_step=MAX_STEP,
            )
            u, v = sol.y
            row = dict(
                k=float(k),
                k_over_M0=float(k / M0),
                success=bool(sol.success),
                status=int(sol.status),
                message=str(sol.message),
                max_u=float(np.nanmax(u)) if u.size else float("nan"),
                max_v=float(np.nanmax(v)) if v.size else float("nan"),
                final_u=float(u[-1]) if u.size and np.isfinite(u[-1]) else float("nan"),
                final_v=float(v[-1]) if v.size and np.isfinite(v[-1]) else float("nan"),
                final_t=float(sol.t[-1]) if sol.t.size else 0.0,
                all_finite=bool(np.all(np.isfinite(sol.y))),
            )
        except Exception as e:
            row = dict(k=float(k), k_over_M0=float(k / M0),
                       error=str(e), all_finite=False, success=False,
                       final_t=0.0)
        passed = (row.get("success", False) and row.get("all_finite", False)
                  and row.get("final_t", 0.0) >= T_END - 1e-6)
        row["passed"] = bool(passed)
        results.append(row)
        print(f"[n={n}]   success={row.get('success')}, final_t={row.get('final_t'):.3f},"
              f" final_v={row.get('final_v', float('nan')):.3e},"
              f" passed={row['passed']}",
              flush=True)

    # Determine k*: smallest passing k in the sweep
    passes = [r for r in results if r["passed"]]
    if passes:
        kstar = min(r["k"] for r in passes)
        kstar_rel = kstar / M0
    else:
        kstar = float("inf")
        kstar_rel = float("inf")
    print(f"[n={n}] k* ≈ {kstar:.4e}, k*/M₀ ≈ {kstar_rel:.4e}", flush=True)

    # Representative plot at smallest successful k
    if passes and sol_orig.success:
        kp = min(r["k"] for r in passes)
        print(f"[n={n}] representative plot at k*≈{kp:.3e}...", flush=True)
        try:
            sol = solve_ivp(
                dualrail_rhs(kp), (0.0, T_END), [0.0, 0.0], t_eval=t_eval,
                rtol=1e-8, atol=1e-10, method="LSODA", max_step=0.01,
            )
            if sol.success:
                fig, ax = plt.subplots(figsize=(8, 4))
                ax.plot(sol.t, sol.y[0], label="u")
                ax.plot(sol.t, sol.y[1], label="v")
                ax.plot(sol.t, sol.y[0] - sol.y[1], "--", label="u - v")
                ax.plot(sol_orig.t, sol_orig.y[0], ":", alpha=0.6, label="y (orig)")
                ax.axhline(lam, color="gray", linestyle=":", alpha=0.5,
                           label=f"λ = {lam:.4f}")
                ax.set_xlabel("t")
                ax.set_title(
                    f"n={n}: y' = -(y^{n} - y - 1), k*≈{kp:.2e}, M₀={M0:.2e}"
                )
                ax.legend()
                fig.tight_layout()
                fig.savefig(os.path.join(HERE, f"dualrail_n{n}.png"), dpi=120)
                plt.close(fig)
        except Exception as e:
            print(f"[n={n}] plot failed: {e}", flush=True)

    return {
        "n": n,
        "lambda": lam,
        "qprime_lam": qp_lam,
        "sign": sign,
        "num_plus": len(plus_terms),
        "num_minus": len(minus_terms),
        "pp_lam": pp_lam,
        "pm_lam": pm_lam,
        "M0": M0,
        "kstar": kstar,
        "kstar_over_M0": kstar_rel,
        "sweep": results,
    }


def summarize_and_plot(all_results):
    # Include exp 09 anchor
    conway_anchor = dict(n=71, M0=3.629e8, kstar_rel=359.38, source="exp 09")

    ns = [r["n"] for r in all_results]
    kstar_rels = [r["kstar_over_M0"] for r in all_results]
    M0s = [r["M0"] for r in all_results]

    print("\n\n" + "="*60, flush=True)
    print("SUMMARY", flush=True)
    print("="*60, flush=True)
    header = f"{'n':>4} {'λ':>10} {'M₀':>14} {'k*':>14} {'k*/M₀':>12}"
    print(header, flush=True)
    for r in all_results:
        print(f"{r['n']:>4} {r['lambda']:>10.6f} {r['M0']:>14.6e}"
              f" {r['kstar']:>14.6e} {r['kstar_over_M0']:>12.4e}",
              flush=True)
    print(f"{conway_anchor['n']:>4} {'1.303577':>10} {conway_anchor['M0']:>14.3e}"
          f" {conway_anchor['M0']*conway_anchor['kstar_rel']:>14.3e}"
          f" {conway_anchor['kstar_rel']:>12.2f}  (exp 09)", flush=True)

    # Combine finite data for fitting
    fit_ns = []
    fit_krel = []
    for r in all_results:
        if np.isfinite(r["kstar_over_M0"]):
            fit_ns.append(r["n"])
            fit_krel.append(r["kstar_over_M0"])
    # Add Conway anchor
    fit_ns_with_conway = fit_ns + [conway_anchor["n"]]
    fit_krel_with_conway = fit_krel + [conway_anchor["kstar_rel"]]

    # Power-law fit: log(k*/M₀) = α log n + log A
    fit_result = None
    if len(fit_ns) >= 2:
        ln = np.log(fit_ns)
        lk = np.log(fit_krel)
        A = np.vstack([ln, np.ones_like(ln)]).T
        alpha, logA = np.linalg.lstsq(A, lk, rcond=None)[0]
        fit_result = dict(alpha=alpha, A=np.exp(logA), using_conway=False)
        print(f"\nPower-law fit on our 4 points: k*/M₀ ≈ {np.exp(logA):.3f} · n^{alpha:.3f}",
              flush=True)

        # With Conway
        ln_c = np.log(fit_ns_with_conway)
        lk_c = np.log(fit_krel_with_conway)
        A_c = np.vstack([ln_c, np.ones_like(ln_c)]).T
        alpha_c, logA_c = np.linalg.lstsq(A_c, lk_c, rcond=None)[0]
        fit_result["alpha_with_conway"] = alpha_c
        fit_result["A_with_conway"] = np.exp(logA_c)
        print(f"Power-law fit including Conway (n=71): "
              f"k*/M₀ ≈ {np.exp(logA_c):.3f} · n^{alpha_c:.3f}",
              flush=True)

    # Exponential fit: log(k*/M₀) = β n + const
    if len(fit_ns) >= 2:
        ln_arr = np.array(fit_ns, dtype=float)
        lk_arr = np.log(fit_krel)
        A = np.vstack([ln_arr, np.ones_like(ln_arr)]).T
        beta, logB = np.linalg.lstsq(A, lk_arr, rcond=None)[0]
        print(f"Exponential fit on our 4 points: k*/M₀ ≈ {np.exp(logB):.3f} · exp({beta:.3f}·n)",
              flush=True)
        if fit_result is not None:
            fit_result["beta_exp"] = beta
            fit_result["B_exp"] = np.exp(logB)

    # Main plot: k*/M₀ vs n (log-y)
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.semilogy(ns, kstar_rels, "o-", label="n-bonacci (exp 10)")
    ax.semilogy([conway_anchor["n"]], [conway_anchor["kstar_rel"]], "rs",
                markersize=10, label=f"Conway n=71 (exp 09)")

    if fit_result is not None:
        ng = np.linspace(min(ns) * 0.8, 80, 100)
        ax.semilogy(ng, fit_result["A"] * ng**fit_result["alpha"], "k--", alpha=0.6,
                    label=f"fit (10 only): {fit_result['A']:.2f}·n^{fit_result['alpha']:.2f}")
        ax.semilogy(ng, fit_result["A_with_conway"] * ng**fit_result["alpha_with_conway"],
                    "g--", alpha=0.6,
                    label=f"fit (10+09): {fit_result['A_with_conway']:.2f}·n^{fit_result['alpha_with_conway']:.2f}")

    ax.set_xlabel("polynomial degree n")
    ax.set_ylabel("k* / M₀")
    ax.set_title("Prefactor C(deg) = k*/M₀ vs polynomial degree")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "kstar_vs_degree.png"), dpi=120)
    plt.close(fig)
    print(f"Saved {os.path.join(HERE, 'kstar_vs_degree.png')}", flush=True)

    # Also plot M₀ vs n to confirm it stays ~O(1)
    fig, ax = plt.subplots(figsize=(8, 4))
    ax.plot(ns, M0s, "o-")
    ax.set_xlabel("n")
    ax.set_ylabel("M₀")
    ax.set_title("On-trajectory production M₀ vs degree (should stay O(1) here)")
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "M0_vs_degree.png"), dpi=120)
    plt.close(fig)

    return fit_result, conway_anchor


def main():
    all_results = []
    for n in DEGREES:
        r = run_for_degree(n)
        all_results.append(r)

    fit_result, conway_anchor = summarize_and_plot(all_results)

    # Write summary.txt
    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        f.write("Experiment 10 — Intermediate-degree sweep\n")
        f.write("=" * 60 + "\n")
        f.write(f"Polynomial family: q_n(y) = y^n - y - 1\n")
        f.write(f"Degrees tested: {DEGREES}\n")
        f.write(f"LSODA: rtol={RTOL}, atol={ATOL}, max_step={MAX_STEP}, T={T_END}\n")
        f.write(f"k sweep: {N_K} points, k/M₀ ∈ [{K_LO_REL}, {K_HI_REL}]\n\n")

        f.write("Per-degree results:\n")
        f.write(f"{'n':>4} {'λ':>12} {'M₀':>14} {'k*':>14} {'k*/M₀':>12}\n")
        for r in all_results:
            f.write(f"{r['n']:>4} {r['lambda']:>12.8f} {r['M0']:>14.6e}"
                    f" {r['kstar']:>14.6e} {r['kstar_over_M0']:>12.4e}\n")
        f.write(f"{conway_anchor['n']:>4} {'1.30357727':>12}"
                f" {conway_anchor['M0']:>14.6e}"
                f" {conway_anchor['M0']*conway_anchor['kstar_rel']:>14.6e}"
                f" {conway_anchor['kstar_rel']:>12.4f}  (exp 09)\n\n")

        if fit_result is not None:
            f.write(f"Power-law fit (exp 10 only): "
                    f"k*/M₀ ≈ {fit_result['A']:.4f} · n^{fit_result['alpha']:.4f}\n")
            f.write(f"Power-law fit (exp 10 + Conway anchor): "
                    f"k*/M₀ ≈ {fit_result['A_with_conway']:.4f}"
                    f" · n^{fit_result['alpha_with_conway']:.4f}\n")
            f.write(f"Exponential fit (exp 10 only): "
                    f"k*/M₀ ≈ {fit_result['B_exp']:.4f}"
                    f" · exp({fit_result['beta_exp']:.4f}·n)\n")

        f.write("\n\nFull per-k sweep data:\n")
        for r in all_results:
            f.write(f"\n--- n = {r['n']} ---\n")
            for row in r["sweep"]:
                f.write(str(row) + "\n")

    print("Summary written.", flush=True)


if __name__ == "__main__":
    main()
