"""Experiment 11: Batch survey of 10 polynomial systems.

For each system (see `system.md`), run the same dual-rail k-sweep as
exp 10 and extract k*, k*/M₀. Fit joint scaling
    log(k*/M₀) = logC + α·log(deg) + β·log(max|c|)
across the 10 new systems plus 5 anchors from exps 09, 10.

Numerics identical to exp 10: LSODA, rtol=1e-6, atol=1e-8, max_step=0.01,
T=5.0, 10-point log sweep over k/M₀ ∈ [0.1, 1000].
"""
from __future__ import annotations

import os
import numpy as np
from math import comb
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))

# LSODA settings (matching exp 09/10)
RTOL = 1e-6
ATOL = 1e-8
MAX_STEP = 0.01
T_END = 5.0
N_EVAL = 1000

K_LO_REL = 0.1
K_HI_REL = 1000.0
N_K = 10

# ----------------------------------------------------------------------
# System definitions. Each entry:
#   name -> (coeffs [c0..cd], bracket_lo, bracket_hi for brentq)
# ----------------------------------------------------------------------
SYSTEMS = [
    ("golden",            [-1, -1, 1],                                       1.0, 2.0),
    ("plastic",           [-1, -1, 0, 1],                                    1.0, 2.0),
    ("silver",            [-1, -2, 1],                                       2.0, 3.0),
    ("tribonacci",        [-1, -1, -1, 1],                                   1.0, 2.0),
    ("dense_deg10",       [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1],       1.0, 2.0),
    ("small_lambda",      [-0.1, 0, 0, 0, 0, 1],                             0.1, 1.5),
    ("large_coef_deg5",   [-50, -50, 0, 0, 0, 1],                            1.0, 3.0),
    ("near_cancel_deg5",  [-1, -1, 0, 0, -100, 100],                         1.0, 2.0),
    ("sparse_deg15",      [-1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1],
                                                                             1.0, 2.0),
    ("cheb_like_deg5",    [-3, 5, 0, -20, 0, 16],                            1.0, 2.0),
]

# Anchors from exps 09/10 for joint fit
ANCHORS = [
    dict(name="nbon_n5",  deg=5,  maxc=1,  kstar_rel=16.68),
    dict(name="nbon_n10", deg=10, maxc=1,  kstar_rel=46.42),
    dict(name="nbon_n20", deg=20, maxc=1,  kstar_rel=129.15),
    dict(name="nbon_n40", deg=40, maxc=1,  kstar_rel=359.38),
    dict(name="conway_n71", deg=71, maxc=14, kstar_rel=359.38),
]


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


def find_lambda(coeffs, lo, hi):
    return brentq(lambda y: q_eval(coeffs, y), lo + 1e-9, hi)


def split_monomials(coeffs, sign):
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


def run_for_system(name, coeffs, lo, hi):
    print(f"\n{'='*60}", flush=True)
    print(f"[{name}] starting", flush=True)
    print(f"{'='*60}", flush=True)

    deg = len(coeffs) - 1
    maxc = max(abs(c) for c in coeffs)

    lam = find_lambda(coeffs, lo, hi)
    qp_lam = q_prime_eval(coeffs, lam)
    sign = -1 if qp_lam > 0 else +1
    print(f"[{name}] deg={deg}, max|c|={maxc}, λ={lam:.10f}, q'(λ)={qp_lam:.4e}, SIGN={sign}",
          flush=True)

    plus_terms, minus_terms = split_monomials(coeffs, sign)
    print(f"[{name}] #plus={len(plus_terms)}, #minus={len(minus_terms)}", flush=True)

    eval_rails = make_rail_evaluator(plus_terms, minus_terms, deg)

    pp_lam, pm_lam = eval_rails(lam, 0.0)
    M0 = max(pp_lam, pm_lam)
    print(f"[{name}] p̂⁺(λ,0)={pp_lam:.6e}, p̂⁻(λ,0)={pm_lam:.6e}, M₀={M0:.6e}",
          flush=True)

    # Original trajectory
    def original_rhs(_t, state):
        (y,) = state
        return [sign * q_eval(coeffs, y)]

    t_eval = np.linspace(0.0, T_END, N_EVAL)
    sol_orig = solve_ivp(
        original_rhs, (0.0, T_END), [0.0], t_eval=t_eval,
        rtol=1e-8, atol=1e-10, method="LSODA", max_step=0.01,
    )
    print(f"[{name}]   orig success={sol_orig.success}, final y={sol_orig.y[0][-1]:.6f}",
          flush=True)

    # k sweep
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
        print(f"[{name}] [{idx+1:2d}/{N_K}] k/M₀={row['k_over_M0']:.3e}"
              f"  success={row.get('success')}"
              f"  final_t={row.get('final_t'):.3f}"
              f"  final_v={row.get('final_v', float('nan')):.3e}"
              f"  passed={row['passed']}",
              flush=True)

    passes = [r for r in results if r["passed"]]
    if passes:
        kstar = min(r["k"] for r in passes)
        kstar_rel = kstar / M0
    else:
        kstar = float("inf")
        kstar_rel = float("inf")
    print(f"[{name}] k* ≈ {kstar:.4e}, k*/M₀ ≈ {kstar_rel:.4e}", flush=True)

    # Representative plot at smallest successful k
    if passes and sol_orig.success:
        kp = min(r["k"] for r in passes)
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
                ax.set_title(f"{name}: deg={deg} max|c|={maxc} k*≈{kp:.2e} M₀={M0:.2e}")
                ax.legend()
                fig.tight_layout()
                fig.savefig(os.path.join(HERE, f"dualrail_{name}.png"), dpi=120)
                plt.close(fig)
        except Exception as e:
            print(f"[{name}] plot failed: {e}", flush=True)

    return {
        "name": name,
        "deg": deg,
        "maxc": maxc,
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


def joint_fit(points):
    """Fit log(k*/M₀) = logC + α log(deg) + β log(max|c|).

    points: list of dict with 'deg', 'maxc', 'kstar_over_M0'.
    """
    rows = [p for p in points if np.isfinite(p["kstar_over_M0"]) and p["kstar_over_M0"] > 0]
    ld = np.log(np.array([p["deg"] for p in rows], dtype=float))
    lc = np.log(np.array([max(float(p["maxc"]), 1e-12) for p in rows]))
    lk = np.log(np.array([p["kstar_over_M0"] for p in rows]))

    A = np.vstack([ld, lc, np.ones_like(ld)]).T
    sol, *_ = np.linalg.lstsq(A, lk, rcond=None)
    alpha, beta, logC = sol
    C = np.exp(logC)

    preds = C * (np.exp(ld) ** alpha) * (np.exp(lc) ** beta)
    return dict(alpha=float(alpha), beta=float(beta), C=float(C),
                pred=preds.tolist(), obs=[p["kstar_over_M0"] for p in rows],
                names=[p["name"] for p in rows])


def deg_only_fit(points):
    """Fit log(k*/M₀) = logC + α log(deg). Compare to joint fit."""
    rows = [p for p in points if np.isfinite(p["kstar_over_M0"]) and p["kstar_over_M0"] > 0]
    ld = np.log(np.array([p["deg"] for p in rows], dtype=float))
    lk = np.log(np.array([p["kstar_over_M0"] for p in rows]))
    A = np.vstack([ld, np.ones_like(ld)]).T
    sol, *_ = np.linalg.lstsq(A, lk, rcond=None)
    alpha, logC = sol
    return dict(alpha=float(alpha), C=float(np.exp(logC)))


def summarize_and_plot(all_results):
    print("\n\n" + "="*70, flush=True)
    print("SUMMARY", flush=True)
    print("="*70, flush=True)
    header = f"{'name':20s} {'deg':>4} {'max|c|':>8} {'λ':>10} {'M₀':>14} {'k*':>14} {'k*/M₀':>12}"
    print(header, flush=True)
    for r in all_results:
        print(f"{r['name']:20s} {r['deg']:>4} {r['maxc']:>8.1f} {r['lambda']:>10.6f}"
              f" {r['M0']:>14.6e} {r['kstar']:>14.6e} {r['kstar_over_M0']:>12.4e}",
              flush=True)
    print("\n[Anchors from exps 09/10]", flush=True)
    for a in ANCHORS:
        print(f"{a['name']:20s} {a['deg']:>4} {a['maxc']:>8.1f} {'--':>10} {'--':>14} {'--':>14}"
              f" {a['kstar_rel']:>12.4e}", flush=True)

    # Combined point list for fitting
    points = [
        dict(name=r["name"], deg=r["deg"], maxc=float(r["maxc"]),
             kstar_over_M0=r["kstar_over_M0"])
        for r in all_results
    ] + [
        dict(name=a["name"], deg=a["deg"], maxc=float(a["maxc"]),
             kstar_over_M0=a["kstar_rel"])
        for a in ANCHORS
    ]

    jf = joint_fit(points)
    df = deg_only_fit(points)
    print(f"\nJoint fit (all {len([p for p in points if np.isfinite(p['kstar_over_M0'])])} points):",
          flush=True)
    print(f"  k*/M₀ ≈ {jf['C']:.3f} · deg^{jf['alpha']:.3f} · max|c|^{jf['beta']:.3f}",
          flush=True)
    print(f"Deg-only fit:", flush=True)
    print(f"  k*/M₀ ≈ {df['C']:.3f} · deg^{df['alpha']:.3f}", flush=True)

    # Residuals
    print("\nObs vs joint fit pred:", flush=True)
    for name, obs, pred in zip(jf["names"], jf["obs"], jf["pred"]):
        ratio = obs / pred if pred > 0 else float("nan")
        print(f"  {name:20s} obs={obs:10.3e}  pred={pred:10.3e}  ratio={ratio:5.2f}",
              flush=True)

    # Plot: k*/M₀ vs deg, colored by max|c|
    fig, ax = plt.subplots(figsize=(9, 6))
    degs = [p["deg"] for p in points if np.isfinite(p["kstar_over_M0"])]
    ks = [p["kstar_over_M0"] for p in points if np.isfinite(p["kstar_over_M0"])]
    cs = [p["maxc"] for p in points if np.isfinite(p["kstar_over_M0"])]
    ns = [p["name"] for p in points if np.isfinite(p["kstar_over_M0"])]
    sc = ax.scatter(degs, ks, c=np.log10(np.maximum(cs, 1)), s=80, cmap="viridis",
                    edgecolor="k")
    for d, k, n in zip(degs, ks, ns):
        ax.annotate(n, (d, k), fontsize=7, alpha=0.8)
    d_grid = np.linspace(2, 72, 200)
    ax.plot(d_grid, df["C"] * d_grid**df["alpha"], "k--",
            label=f"deg-only fit: {df['C']:.2f}·deg^{df['alpha']:.2f}")
    plt.colorbar(sc, ax=ax, label="log10(max|c|)")
    ax.set_xlabel("degree")
    ax.set_ylabel("k* / M₀")
    ax.set_yscale("log")
    ax.set_xscale("log")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()
    ax.set_title("Exp 11 batch survey: k*/M₀ vs degree")
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "kstar_vs_deg_batch.png"), dpi=120)
    plt.close(fig)

    # Plot: residuals of joint fit vs observation
    fig, ax = plt.subplots(figsize=(9, 6))
    obs = np.array(jf["obs"])
    pred = np.array(jf["pred"])
    ax.loglog(pred, obs, "o", markersize=8)
    lims = [min(obs.min(), pred.min()), max(obs.max(), pred.max())]
    ax.plot(lims, lims, "k--", alpha=0.5)
    for o, p, n in zip(obs, pred, jf["names"]):
        ax.annotate(n, (p, o), fontsize=7, alpha=0.8)
    ax.set_xlabel("predicted k*/M₀ (joint fit)")
    ax.set_ylabel("observed k*/M₀")
    ax.set_title(f"Joint fit  k*/M₀ ≈ {jf['C']:.2f}·deg^{jf['alpha']:.2f}·max|c|^{jf['beta']:.2f}")
    ax.grid(True, which="both", alpha=0.3)
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "joint_fit_residuals.png"), dpi=120)
    plt.close(fig)

    return jf, df, points


def main():
    all_results = []
    for (name, coeffs, lo, hi) in SYSTEMS:
        r = run_for_system(name, coeffs, lo, hi)
        all_results.append(r)

    jf, df, points = summarize_and_plot(all_results)

    # Write summary.txt
    with open(os.path.join(HERE, "summary.txt"), "w") as f:
        f.write("Experiment 11 — Batch survey of 10 polynomial systems\n")
        f.write("=" * 70 + "\n")
        f.write(f"LSODA: rtol={RTOL}, atol={ATOL}, max_step={MAX_STEP}, T={T_END}\n")
        f.write(f"k sweep: {N_K} log points over k/M₀ ∈ [{K_LO_REL}, {K_HI_REL}]\n\n")

        f.write("Per-system results:\n")
        f.write(f"{'name':20s} {'deg':>4} {'max|c|':>8} {'λ':>12} "
                f"{'M₀':>14} {'k*':>14} {'k*/M₀':>12}\n")
        for r in all_results:
            f.write(f"{r['name']:20s} {r['deg']:>4} {r['maxc']:>8.1f}"
                    f" {r['lambda']:>12.8f} {r['M0']:>14.6e}"
                    f" {r['kstar']:>14.6e} {r['kstar_over_M0']:>12.4e}\n")
        f.write("\nAnchor points from exps 09/10:\n")
        for a in ANCHORS:
            f.write(f"  {a['name']:20s} deg={a['deg']:3d}"
                    f" max|c|={a['maxc']:5.1f}"
                    f" k*/M₀={a['kstar_rel']:10.4f}\n")

        f.write(f"\nJoint fit:  k*/M₀ ≈ {jf['C']:.4f}"
                f" · deg^{jf['alpha']:.4f}"
                f" · max|c|^{jf['beta']:.4f}\n")
        f.write(f"Deg-only fit: k*/M₀ ≈ {df['C']:.4f}"
                f" · deg^{df['alpha']:.4f}\n\n")

        f.write("Obs vs joint fit (including anchors):\n")
        for name, obs, pred in zip(jf["names"], jf["obs"], jf["pred"]):
            ratio = obs / pred if pred > 0 else float("nan")
            f.write(f"  {name:20s} obs={obs:10.3e}"
                    f"  pred={pred:10.3e}  ratio={ratio:5.2f}\n")

        f.write("\n\nFull per-k sweep data:\n")
        for r in all_results:
            f.write(f"\n--- {r['name']} (deg={r['deg']}, max|c|={r['maxc']}) ---\n")
            for row in r["sweep"]:
                f.write(str(row) + "\n")

    print("summary.txt written.", flush=True)


if __name__ == "__main__":
    main()
