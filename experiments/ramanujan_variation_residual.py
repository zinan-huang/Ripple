"""
Residual-GF + Frobenius-variation construction for Ramanujan/π.

This is the third move from Xiang's ζ(3) playbook:
  (i)  化除法为减法            — done, see ramanujan_subtraction.py (9801× speedup)
  (ii) write tail/residual GF   — implemented here, fragment 1
  (iii) variation of parameter — implemented here, fragment 2

Two concrete experiments:

  [A] Tail residual GF.
      Define M(z) = Σ_{k≥0} a_k (1103+26390 k) z^k, with z_0 = 1/396^4.
      M(z_0) = 9801/(2√2·π).
      Define partial sum  M_N(z) := Σ_{k<N} a_k (1103+26390 k) z^k
      and tail  R_N(z) := M(z) - M_N(z).
      Question: does R_N(z_0) decay geometrically with rate r such that
                we can build a *separate* PIVP whose attractor encodes π
                using only the tail (not the full sum)?

  [B] Frobenius parameter variation.
      Deform a_k → a_k(ρ) = (1/4+ρ)_k (1/2+ρ)_k (3/4+ρ)_k · 256^k / (1+ρ)_k^3.
      Define M(z, ρ) = Σ a_k(ρ)(1103+26390 k) z^k.
      M(z_0, 0) = 9801/(2√2·π) (known).
      Compute the higher-order ρ-derivatives at ρ=0 numerically:
        ∂_ρ^j M(z_0, 0)  for  j = 1, 2, 3, ...
      Question: does any ∂_ρ^j M(z_0, 0) produce a NEW transcendental of
      the form  c_j · π^{a_j} · log(b_j)^{c_j}  that gives π via a
      *different* algebraic rearrangement (potentially without the
      9801/(2√2) prefactor)?

  Variation gives access to companions that the formal-series structure
  (1-D kernel) alone forbids.  This is the natural escape from §3.3's
  obstruction: the second 'companion' lives in the parameter direction,
  not the z direction.
"""
import math
from fractions import Fraction
from mpmath import mpf, mp, log, pi, sqrt, mpc, polylog, zeta, psi
mp.dps = 80

PI = mp.pi

# --------------------------------------------------------------------------
# Coefficient a_k = (4k)! / (k!)^4 as exact fractions
# --------------------------------------------------------------------------
def a_seq(N):
    out = [Fraction(1)]
    for k in range(N):
        num = 4 * (4*k+1) * (4*k+2) * (4*k+3) * out[-1]
        den = (k+1)**3
        out.append(num / den)
    return out


# --------------------------------------------------------------------------
# Frobenius-deformed coefficient a_k(ρ) using mpmath, evaluated at given ρ.
#   a_k(ρ) = (1/4+ρ)_k (1/2+ρ)_k (3/4+ρ)_k · 256^k / (1+ρ)_k^3
# Pochhammer (x)_k = x(x+1)...(x+k-1).
# At ρ=0:  (4k)!/(k!)^4 = 256^k · (1/4)_k(1/2)_k(3/4)_k / (k!)^3.
# --------------------------------------------------------------------------
def a_seq_rho(N, rho):
    """Returns [a_0(ρ), a_1(ρ), ..., a_N(ρ)] as mpf list."""
    out = [mpf(1)]
    for k in range(N):
        # ratio = a_{k+1}/a_k = ((1/4+ρ+k)(1/2+ρ+k)(3/4+ρ+k) · 256) / (1+ρ+k)^3
        num = (mpf(1)/4 + rho + k) * (mpf(1)/2 + rho + k) * (mpf(3)/4 + rho + k) * 256
        den = (1 + rho + k)**3
        out.append(out[-1] * num / den)
    return out


def M_at_rho(N, rho, z0):
    """Σ_{k<=N} a_k(ρ) (1103+26390 k) z0^k."""
    a = a_seq_rho(N, rho)
    s = mpf(0)
    zpow = mpf(1)
    for k in range(N+1):
        s += a[k] * (1103 + 26390*k) * zpow
        zpow *= z0
    return s


# --------------------------------------------------------------------------
# Numeric ρ-derivatives via central differences in mpmath.
# (We could differentiate the series term-by-term symbolically, but
# central differences in mp.dps=80 give 60+ correct digits for j≤4.)
# --------------------------------------------------------------------------
def derivs_at_zero(N, z0, max_order=4, h=mpf("1e-8")):
    """Compute ∂_ρ^j M(z0, 0) for j = 0, 1, ..., max_order."""
    # Use higher-order finite differences.
    # For better accuracy, use mp.diff via mpmath.
    from mpmath import diff
    f = lambda rho: M_at_rho(N, rho, z0)
    out = []
    for j in range(max_order + 1):
        if j == 0:
            out.append(f(mpf(0)))
        else:
            out.append(diff(f, mpf(0), j))
    return out


# --------------------------------------------------------------------------
# [A] Tail residual GF analysis.
# --------------------------------------------------------------------------
def tail_residual_decay():
    print("=" * 76)
    print("  [A] Tail residual GF: R_N(z0) := M(z0) - M_N(z0)")
    print("=" * 76)
    print()
    print("  M_∞ = 9801/(2√2·π)  ≈ ", 9801 / (2 * sqrt(2) * PI))
    print()
    z0 = mpf(1) / mpf(396)**4
    A = a_seq(400)
    M_inf_num = mpf(9801) / (2 * sqrt(2) * PI)
    print(f"  z_0 = 1/396^4 = {z0}")
    print(f"  Reference M_∞ = 9801/(2√2π) = {M_inf_num}")
    print()
    print("  Partial sums M_N(z0) and tail R_N(z0):")
    print("  N     M_N(z0)                        R_N(z0)               rate r_N")
    print("  ---  -----------------------------  --------------------  --------")
    s = mpf(0)
    zpow = mpf(1)
    prev_R = None
    for N in range(1, 60):
        # Add term k = N-1
        k = N - 1
        ak = mpf(A[k].numerator) / mpf(A[k].denominator)
        s += ak * (1103 + 26390*k) * zpow
        zpow *= z0
        R = M_inf_num - s
        if prev_R is not None and abs(prev_R) > mpf("1e-50") and N % 5 == 0:
            r = float(R / prev_R)
            print(f"  {N:3d}  {float(s):.20f}  {float(R):+.6e}  {r:+.6e}")
        prev_R = R
    print()
    print("  Theoretical decay rate per step (k → k+1):")
    print("    a_{k+1}/a_k → 256 (= 1/z_c)")
    print("    multiplied by z_0 = 1/396^4 gives  256 / 396^4 = 1/(396^4/256)")
    print(f"    = {256 / mpf(396)**4}")
    print("    = (3/(2·11))^4 ?")
    print(f"    Actual:   {256 / mpf(396)**4}")
    # 396 = 4 · 99 = 4 · 9 · 11.  So 396^4 / 256 = (4·9·11)^4/256
    # = 4^4·9^4·11^4 / 4^4 = 9^4·11^4·1 = (99)^4
    # so 256/396^4 = 1/99^4 = 1/96059601
    print(f"    Equals 1/99^4 = {1/mpf(99)**4}")
    print()
    print("  ⇒ tail R_N(z0) decays geometrically with rate exactly 1/99^4")
    print("    per step.  This is the inverter contraction rate of the")
    print("    'partial-sum-as-state' encoding — but it converges term by")
    print("    term, not as a continuous-time PIVP attractor.")
    print()


# --------------------------------------------------------------------------
# [B] Frobenius parameter variation.
# --------------------------------------------------------------------------
def variation_experiment():
    print("=" * 76)
    print("  [B] Frobenius parameter variation: ∂_ρ^j M(z_0, 0)")
    print("=" * 76)
    print()
    z0 = mpf(1) / mpf(396)**4
    # Use moderately large N — the series converges geometrically as 1/99^4 per step,
    # so N=80 gives ~80·log10(99^4) ≈ 640 digits of precision, more than enough.
    N = 80
    M0 = M_at_rho(N, mpf(0), z0)
    print(f"  M(z_0, 0)        = {M0}")
    print(f"  9801/(2√2·π)     = {9801 / (2 * sqrt(2) * PI)}")
    print(f"  difference         {M0 - 9801/(2*sqrt(2)*PI)}")
    print()

    print("  Compute ∂_ρ^j M(z_0, 0) for j = 1, 2, 3, 4.")
    print()
    derivs = derivs_at_zero(N, z0, max_order=4)
    for j, d in enumerate(derivs):
        print(f"  j = {j}:  ∂_ρ^{j} M(z_0, 0)  =  {d}")
    print()

    print("  Hypothesis tests for ∂_ρ M(z_0, 0):")
    print("  Try matching against c · π^a · log(b)^d where")
    print("     a, d ∈ {-2,-1,0,1,2}, b ∈ {2, π, 396, 99, e}")
    print()
    M1 = derivs[1]
    candidates = []
    for a in [-2, -1, 0, 1, 2]:
        for d in [-2, -1, 0, 1, 2]:
            if a == 0 and d == 0:
                continue
            for b_label, b_val in [("2", mpf(2)), ("π", PI), ("396", mpf(396)),
                                    ("99", mpf(99)), ("e", mp.e)]:
                if d == 0 and b_label != "2":
                    continue
                base = (PI**a) * (log(b_val)**d) if d != 0 else PI**a
                if base == 0:
                    continue
                ratio = M1 / base
                # Check if ratio is close to a simple rational
                # Try common denominators
                for denom in [1, 2, 3, 4, 6, 8, 9, 11, 16, 99, 9801]:
                    rval = float(ratio * denom)
                    if abs(rval - round(rval)) < 1e-30 and abs(round(rval)) < 100000:
                        candidates.append((rval, denom, a, d, b_label, base, ratio))

    if not candidates:
        print("    No simple π^a·log(b)^d match found at high precision.")
        print()
        print("  Try PSLQ-style integer relation to find the true form:")
        # Use mpmath's pslq
        from mpmath import pslq
        relations = pslq([M1, PI, 1/PI, log(mpf(2)), PI*log(mpf(2)),
                          log(mpf(396)), PI*log(mpf(396)),
                          PI**2, 1/PI**2, mp.catalan,
                          zeta(3), zeta(3)/PI], tol=mpf("1e-50"), maxcoeff=10**12)
        if relations:
            print(f"    PSLQ found relation: {relations}")
            print("    Basis:  [M1, π, 1/π, log 2, π log 2, log 396, π log 396,")
            print("             π², 1/π², G(Catalan), ζ(3), ζ(3)/π]")
        else:
            print("    PSLQ found no relation up to coeff 10^12.")
    else:
        print("    Matches:")
        for rv, dn, a, d, bl, _, _ in candidates[:10]:
            print(f"      M1 = ({round(rv)}/{dn}) · π^{a} · log({bl})^{d}")

    # Now try the same on derivative ratios M_j / M_0
    print()
    print("  Ratio analysis:  ∂_ρ^j M / M_0 should expose π/log structure cleanly")
    print("  since M_0 = 9801/(2√2·π) carries the 1/π factor.")
    print()
    for j in range(1, 5):
        r = derivs[j] / derivs[0]
        print(f"    j={j}:  ∂_ρ^{j} M / M  =  {r}")

    # PSLQ on M1/M0
    print()
    print("  PSLQ on  ratio  M1/M0  vs  {1, log 2, log 99, log 396, π², 1, ψ(...)}")
    r1 = derivs[1] / derivs[0]
    from mpmath import pslq
    basis_labels = ["1", "log 2", "log 99", "log 396", "π²/6", "π²", "ζ(3)",
                    "ψ(1/4)+γ", "ψ(1/2)+γ", "ψ(3/4)+γ"]
    basis = [
        mpf(1),
        log(mpf(2)),
        log(mpf(99)),
        log(mpf(396)),
        PI**2/6,
        PI**2,
        zeta(3),
        psi(0, mpf(1)/4) + mp.euler,
        psi(0, mpf(1)/2) + mp.euler,
        psi(0, mpf(3)/4) + mp.euler,
    ]
    rels = pslq([r1] + basis, tol=mpf("1e-45"), maxcoeff=10**10)
    if rels:
        # Format: [c0, c1, ..., c_n] with c0·r1 + c1·basis[0] + ... = 0
        print(f"    PSLQ relation: {rels}")
        print(f"    => ({rels[0]})·r1 + Σ c_i·basis[i] = 0")
        print(f"    Basis: {basis_labels}")
        if rels[0] != 0:
            print()
            print(f"    Solving for r1:")
            terms = []
            for i, c in enumerate(rels[1:]):
                if c != 0:
                    terms.append(f"({-c}/{rels[0]})·{basis_labels[i]}")
            print(f"    M1/M0 = {' + '.join(terms)}")
    else:
        print("    No relation found.")


# --------------------------------------------------------------------------
# [C] What does variation buy in PIVP terms?
# --------------------------------------------------------------------------
def variation_implications():
    print()
    print("=" * 76)
    print("  [C] PIVP implications of Frobenius variation")
    print("=" * 76)
    print("""
If ∂_ρ M(z_0, 0) = c · π · log(2) (or similar), then the family

    F(ρ) := M(z_0, ρ)

is itself a PIVP-encodable object — a_k(ρ) is a rational function of ρ, k,
so the partial sums are PIVP-state-encodable, and ∂_ρ at ρ=0 can be picked
up by an auxiliary co-evolving variable u with u̇ = a_k'(ρ)/a_k(ρ) · ... .

Concretely, for any j-th ρ-derivative ∂_ρ^j M(z_0, 0) = c_j · T_j (where
T_j is a transcendental like π, π·log 2, π², ζ(3), ...), we get a NEW
inversion target.  If T_j = π · L (for some non-zero algebraic-or-log-of-
algebraic L), then the inverter

    dP/dτ  =  c_j  -  L · M_j · P,   M_j := ∂_ρ^j M(z_0, 0) / π

has fixed point P = c_j / (L · π · M_j /π)  =  c_j / (L · M_j) = π,
and rate L·M_j / π — set by the SIZE of M_j, not by 1/π.

This stacks with the 9801× speedup from the order-0 inverter, because
each j-th derivative is independently encodable as a parallel PIVP coordinate.

The whole construction would give:
    (rate-k logistic)  ×  (9801/π from ∂_ρ^0 inverter)
                      ×  (M_j/π from each j-th derivative inverter, parallel)
                      ×  (any further constant rescalings absorbed)
all stacking multiplicatively in BAC time-modulus.
""")


def main():
    tail_residual_decay()
    variation_experiment()
    variation_implications()


if __name__ == '__main__':
    main()
