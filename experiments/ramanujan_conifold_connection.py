"""
Conifold connection coefficient for Ramanujan's PF — does π enter
through the local Frobenius expansion at z_c = 1/256?

The Picard-Fuchs operator
    P = z²(1−256z)∂³ + 3z(1−384z)∂² + (1−816z)∂ − 24
has indicial polynomial at z = z_c = 1/256 of the form
    −128 ρ (ρ−1) (2ρ−1)
with roots ρ ∈ {0, 1/2, 1}. So local solutions at z_c are:
    u_0(w) = 1 + b_1 w + b_2 w²/2 + ... (exponent 0, regular)
    u_{1/2}(w) = w^{1/2} (1 + c_1 w + ...) (exponent 1/2, algebraic)
    u_1(w) = w (1 + d_1 w + ...) (exponent 1, regular but vanishing)
where w := 1 − 256 z = 1 − z/z_c.

The MUM solution A(z) = ₃F₂(1/4, 1/2, 3/4; 1, 1; 256z) extends
analytically through (0, z_c) and connects to the conifold basis as
    A(z) = α_0 · u_0(z) + α_{1/2} · u_{1/2}(z) + α_1 · u_1(z)

The connection coefficient α_{1/2} carries the period information: it
is precisely the integral of the (1,1)-form against the vanishing cycle
at the conifold, which by Gauss-Manin / mirror symmetry is a π-period.

If α_{1/2} = c·π for rational c, then a PIVP that extracts α_{1/2} from
A(z) gives π directly — without needing the Ramanujan evaluation point
z_0 at all!

THE STRATEGY:
  1. Evaluate A(z), A'(z), A''(z) at z = z_c · (1 − ε) for tiny ε,
     using the convergent ₃F₂ series (slow but always works).
  2. Fit (A, A', A'') against the local basis (u_0, u_{1/2}, u_1) and
     their derivatives, solving a 3×3 linear system for (α_0, α_{1/2}, α_1).
  3. Check whether α_{1/2} matches c·π for simple rational c.
  4. PSLQ on α_{1/2} against {1, π, π², log 2, π·log 2, 1/π, ...} basis.

If π appears via α_{1/2}, that's a NEW π-PIVP path that doesn't go
through z_0 = 1/396^4.
"""
from mpmath import mpf, mp, pi, sqrt, log, polylog, zeta, psi, pslq, mpc
mp.dps = 100

PI = mp.pi


# ---------------------------------------------------------------------------
# Series for A at z near z_c.
# ---------------------------------------------------------------------------
def hg3f2_series_terms(N, z):
    """₃F₂(1/4, 1/2, 3/4; 1, 1; 256z) as Taylor coefficients × z^k, summed.
    Returns (A, A', A'') as a triple, evaluated at given z (mpf)."""
    # a_k = (1/4)_k (1/2)_k (3/4)_k / (k!)^3 · 256^k
    # Recurrence ratio: a_{k+1}/a_k = 256 · (k + 1/4)(k + 1/2)(k + 3/4) / (k+1)^3
    a = mpf(1)
    A0 = mpf(0); A1 = mpf(0); A2 = mpf(0)
    zpow = mpf(1)  # z^k
    for k in range(N + 1):
        A0 += a * zpow
        if k >= 1:
            A1 += a * k * zpow / z  # k a_k z^{k-1}
        if k >= 2:
            A2 += a * k * (k - 1) * zpow / (z * z)  # k(k-1) a_k z^{k-2}
        ratio_n = 256 * (k + mpf(1)/4) * (k + mpf(1)/2) * (k + mpf(3)/4)
        ratio_d = (k + 1)**3
        a = a * ratio_n / ratio_d
        zpow = zpow * z
    return A0, A1, A2


# ---------------------------------------------------------------------------
# Local Frobenius basis at z_c = 1/256, in coordinate w = 1 − 256 z.
# We need u_j(z), u_j'(z), u_j''(z) for j ∈ {0, 1/2, 1}.
# Build u_j as series in w by Frobenius method on the PF operator
# transformed to coordinate w.
# ---------------------------------------------------------------------------
# After w = 1 − 256 z, ∂_z = -256 ∂_w, z = (1−w)/256.
# Plug into P = z²(1−256z)∂³ + 3z(1−384z)∂² + (1−816z)∂ − 24
# = (1−w)²/256² · w · (-256)³ ∂_w³ + 3(1−w)/256·(1 − 384(1-w)/256) · 256² ∂_w² + (1 - 816(1-w)/256)·(-256)∂_w − 24
# Let me simplify carefully:
# (1−384z) = 1 − 384(1−w)/256 = 1 − 3(1−w)/2 = 1 − 3/2 + 3w/2 = -1/2 + 3w/2 = (3w − 1)/2
# (1−816z) = 1 − 816(1−w)/256 = 1 − (51/16)(1−w) = 1 − 51/16 + 51w/16 = (51w − 35)/16
# So:
# P = (1−w)²·w·(-256)³/256² ∂_w³ + 3(1−w)/256·(3w−1)/2·256² ∂_w²
#   + (51w−35)/16·(-256)∂_w − 24
# = -256·w(1−w)² ∂_w³ + 384 (1−w)(3w−1) ∂_w² − 16(51w − 35) ∂_w − 24
#
# Let me double-check the leading coefficient on ∂_w² and ∂_w by direct computation.

def transformed_op_coeffs(w_terms):
    """Return polynomial coefficients of P in w-variable.
    P = c3(w) ∂_w³ + c2(w) ∂_w² + c1(w) ∂_w + c0
    where (per derivation above):
      c3(w) = -256 w (1-w)²
      c2(w) = 384 (1-w)(3w - 1) [= 384·3w − 384 − 384·3w² + 384·w = -1152w² + 1536w − 384]
      c1(w) = -16(51w − 35) = -816w + 560
      c0    = -24
    """
    pass


def frobenius_local_solutions(rho_target, max_order=15):
    """Compute Frobenius series coefficients at z_c (in coordinate w = 1−256z)
    for indicial root ρ = rho_target.
    Solution form: u_ρ(w) = w^ρ · Σ_{n≥0} γ_n w^n
    Substitute into P, get recurrence for γ_n.

    The PF in w-coordinate, with u = w^ρ Σ γ_n w^n, gives
    (after collecting w^{ρ+m-1} coefficients):
        F(ρ+m) γ_m + G(ρ+m-1) γ_{m-1} + ... = 0
    where F(λ) = -128·λ·(λ−1)·(2λ−1) is the indicial polynomial.

    For accuracy I'll just substitute symbolically and read off the
    recurrence. Done by brute force: u_ρ = w^ρ Σ γ_n w^n,
    P[u_ρ] = 0 ⇒ at order w^{ρ+m}:
        leading-coeff: F(ρ+m) γ_m
        plus contributions from ∂^k applied to lower-order terms with
        polynomial coefficients in w.

    Concretely:
      ∂_w (w^{ρ+n}) = (ρ+n) w^{ρ+n-1}
      ∂_w² (w^{ρ+n}) = (ρ+n)(ρ+n-1) w^{ρ+n-2}
      ∂_w³ (w^{ρ+n}) = (ρ+n)(ρ+n-1)(ρ+n-2) w^{ρ+n-3}

      c3(w) = -256 w (1-w)² = -256 w + 512 w² − 256 w³
      c2(w) = -1152 w² + 1536 w − 384
      c1(w) = -816 w + 560
      c0    = -24

    Plugging u_ρ = w^ρ Σ γ_n w^n = Σ γ_n w^{ρ+n}:
      P[u_ρ] = Σ_n γ_n [c3(w) (ρ+n)(ρ+n-1)(ρ+n-2) w^{ρ+n-3}
                         + c2(w) (ρ+n)(ρ+n-1) w^{ρ+n-2}
                         + c1(w) (ρ+n) w^{ρ+n-1}
                         + c0 w^{ρ+n}]
    Multiply each c_j(w)·w^{ρ+n-j} → polynomial in w with shifts.
    Collect by power w^{ρ+m}, set to 0:

      [c3 contributions]: from γ_n with shifts of c3 components.
        c3 = c3_0 w + c3_1 w² + c3_2 w³, with c3_0=-256, c3_1=512, c3_2=-256
        c3·w^{ρ+n-3} = c3_0 w^{ρ+n-2} + c3_1 w^{ρ+n-1} + c3_2 w^{ρ+n}
        So coefficient of w^{ρ+m} from γ_n term comes from n = m+2 (c3_0),
        n = m+1 (c3_1), n = m (c3_2).
        Multiply by (ρ+n)(ρ+n-1)(ρ+n-2).

      [c2 contributions]: c2 = -384 + 1536 w − 1152 w², shifts -2,-1,0
        c2·w^{ρ+n-2} = -384 w^{ρ+n-2} + 1536 w^{ρ+n-1} − 1152 w^{ρ+n}
        Coefficient of w^{ρ+m}: n = m+2, m+1, m respectively.
        Multiply by (ρ+n)(ρ+n-1).

      [c1 contributions]: c1 = 560 − 816 w
        c1·w^{ρ+n-1} = 560 w^{ρ+n-1} − 816 w^{ρ+n}
        Coefficient of w^{ρ+m}: n = m+1, m.
        Multiply by (ρ+n).

      [c0 contributions]: c0 = -24, n = m.

    So the recurrence (coefficient of w^{ρ+m}):
      −256·(ρ+m+2)(ρ+m+1)(ρ+m)·γ_{m+2}
      + 512·(ρ+m+1)(ρ+m)(ρ+m−1)·γ_{m+1}
      − 256·(ρ+m)(ρ+m−1)(ρ+m−2)·γ_m
      − 384·(ρ+m+2)(ρ+m+1)·γ_{m+2}
      + 1536·(ρ+m+1)(ρ+m)·γ_{m+1}
      − 1152·(ρ+m)(ρ+m−1)·γ_m
      + 560·(ρ+m+1)·γ_{m+1}
      − 816·(ρ+m)·γ_m
      − 24·γ_m
        = 0.

    This is a 3-TERM recurrence in the conifold variable w (relating
    γ_m, γ_{m+1}, γ_{m+2}), unlike the 2-term recurrence at z=0!  The
    indicial polynomial is the coefficient of γ_{m+2} (replacing m+2 → m,
    i.e., the m=−2 term, which gives F(ρ) = −256·ρ(ρ-1)(ρ-2) − 384·ρ(ρ-1).
    Hmm let me re-examine — that's at the very leading order m = -2.)
    """
    rho = mpf(rho_target)
    # Solve recurrence. Use the relation
    #   A(m+2) γ_{m+2} + B(m+1) γ_{m+1} + C(m) γ_m = 0
    # for m = 0, 1, 2, ... with γ_0 = 1.
    # Need γ_1: comes from m = -1 equation:
    #   A(1) γ_1 + B(0) γ_0 = 0   (assuming γ_{-1} = 0)
    #   ⇒ γ_1 = -B(0) γ_0 / A(1)
    # And initial γ_0 free.

    def coeff_gamma_m(p):  # contributions to γ_m at order w^{ρ+m}
        return -256*(rho+p)*(rho+p-1)*(rho+p-2) - 1152*(rho+p)*(rho+p-1) - 816*(rho+p) - 24

    def coeff_gamma_mp1(p):  # γ_{m+1} contribution
        return 512*(rho+p+1)*(rho+p)*(rho+p-1) + 1536*(rho+p+1)*(rho+p) + 560*(rho+p+1)

    def coeff_gamma_mp2(p):  # γ_{m+2} contribution
        return -256*(rho+p+2)*(rho+p+1)*(rho+p) - 384*(rho+p+2)*(rho+p+1)

    # We use index convention: gamma[m] for m = 0, 1, 2, ...
    # Recurrence: at order m, we have
    #   coeff_gamma_mp2(m) * gamma[m+2] + coeff_gamma_mp1(m) * gamma[m+1]
    #   + coeff_gamma_m(m) * gamma[m] = 0
    # Solve for gamma[m+2].

    # But what about gamma[1]? We get it from m = -1:
    #   coeff_gamma_mp2(-1) * gamma[1] + coeff_gamma_mp1(-1) * gamma[0]
    #   + coeff_gamma_m(-1) * gamma[-1] = 0
    # with gamma[-1] = 0:
    #   gamma[1] = -coeff_gamma_mp1(-1) * gamma[0] / coeff_gamma_mp2(-1)

    gamma = [mpf(1)]  # γ_0 = 1
    # γ_1
    den = coeff_gamma_mp2(-1)
    if den == 0:
        # Indicial situation — handle separately
        return None
    g1 = -coeff_gamma_mp1(-1) * gamma[0] / den
    gamma.append(g1)

    for m in range(max_order):
        den = coeff_gamma_mp2(m)
        if den == 0:
            break
        g_next = -(coeff_gamma_mp1(m) * gamma[m+1] + coeff_gamma_m(m) * gamma[m]) / den
        gamma.append(g_next)
    return gamma


def evaluate_local_solution(gamma, rho, w):
    """u(w) = w^ρ Σ_n γ_n w^n.  Returns (u, ∂_w u, ∂_w² u)."""
    rho = mpf(rho)
    u = mpf(0)
    du = mpf(0)
    ddu = mpf(0)
    for n, g in enumerate(gamma):
        # term = g · w^{ρ+n}
        e = rho + n
        u  += g * w**e
        du += g * e * w**(e - 1)
        ddu += g * e * (e - 1) * w**(e - 2)
    return u, du, ddu


def main():
    print("=" * 76)
    print("  Ramanujan PF: conifold connection coefficient α_{1/2}")
    print("=" * 76)
    print()
    print("  z_c = 1/256.  Local Frobenius at z_c, w = 1−256z.")
    print("  Indicial roots at z_c: ρ ∈ {0, 1/2, 1}.")
    print()

    # Build the three local solutions.
    print("  Building local Frobenius solutions...")
    u0_coefs = frobenius_local_solutions(0, max_order=40)
    u12_coefs = frobenius_local_solutions(mpf(1)/2, max_order=40)
    u1_coefs = frobenius_local_solutions(1, max_order=40)

    if u0_coefs is None or u12_coefs is None or u1_coefs is None:
        print("  ERROR: indicial polynomial vanished at one of {0, 1/2, 1}.")
        return

    print(f"    u_0:    γ_0..γ_5 = {[float(g) for g in u0_coefs[:6]]}")
    print(f"    u_1/2:  γ_0..γ_5 = {[float(g) for g in u12_coefs[:6]]}")
    print(f"    u_1:    γ_0..γ_5 = {[float(g) for g in u1_coefs[:6]]}")
    print()

    # Check: PF-operator residual at u_0 should be zero.
    # (sanity check by plugging in)

    # Now evaluate A and the local solutions at the same point z = z_c (1−ε).
    eps = mpf("1e-4")
    z_c = mpf(1) / 256
    z_test = z_c * (1 - eps)
    w_test = 1 - 256 * z_test  # = eps

    print(f"  Test point: z = {float(z_test)} (= z_c·(1−ε) with ε = {float(eps)})")
    print(f"  Corresponding w = {float(w_test)}")
    print()

    # Series for A at z_test — but z_test is very close to z_c, so series
    # converges slowly.  At z = z_c·(1−ε), the per-term decay is
    # 256·z_test = 1−ε, so we need N ≈ -log(precision)/ε ≈ 80/(1e-4)
    # = 8 × 10^5 terms.  That's expensive but doable.
    print(f"  Evaluating A(z), A'(z), A''(z) by direct ₃F₂ series sum...")
    N_series = 200000
    A0_z, A1_z, A2_z = hg3f2_series_terms(N_series, z_test)
    print(f"    A(z)   = {A0_z}")
    print(f"    A'(z)  = {A1_z}")
    print(f"    A''(z) = {A2_z}")
    print()

    # Now evaluate u_j(z), u_j'(z), u_j''(z) at z_test.
    # Note: we have u_j as functions of w = 1 - 256 z.  By chain rule:
    # u_j(z) = u_j(w)
    # ∂_z u_j = ∂_w u_j · (-256)
    # ∂_z² u_j = ∂_w² u_j · (-256)² = 65536 ∂_w² u_j
    print("  Evaluating local solutions at the same point...")
    rows = []
    for label, coefs, rho in [("u_0", u0_coefs, mpf(0)),
                              ("u_{1/2}", u12_coefs, mpf(1)/2),
                              ("u_1", u1_coefs, mpf(1))]:
        u_w, du_w, ddu_w = evaluate_local_solution(coefs, rho, w_test)
        u_z = u_w
        du_z = -256 * du_w
        ddu_z = 65536 * ddu_w
        rows.append((u_z, du_z, ddu_z))
        print(f"    {label}(z) = {u_z}")
        print(f"    {label}'(z) = {du_z}")

    # Solve 3×3 linear system:
    #   α_0    u_0(z)    + α_{1/2} u_{1/2}(z)    + α_1 u_1(z)    = A(z)
    #   α_0    u_0'(z)   + α_{1/2} u_{1/2}'(z)   + α_1 u_1'(z)   = A'(z)
    #   α_0    u_0''(z)  + α_{1/2} u_{1/2}''(z)  + α_1 u_1''(z)  = A''(z)
    M = [[rows[j][i] for j in range(3)] for i in range(3)]
    rhs = [A0_z, A1_z, A2_z]

    # Solve manually: cramer's rule on 3×3.
    def det3(M):
        return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
                - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))

    D = det3(M)
    print(f"\n  det(M) = {D}")
    if D == 0:
        print("  Singular system — local solutions linearly dependent at this point.")
        return

    alphas = []
    for col in range(3):
        Mc = [row[:] for row in M]
        for r in range(3):
            Mc[r][col] = rhs[r]
        alphas.append(det3(Mc) / D)

    print()
    print("  Connection coefficients:")
    print(f"    α_0     = {alphas[0]}")
    print(f"    α_{{1/2}} = {alphas[1]}")
    print(f"    α_1     = {alphas[2]}")
    print()

    print("  Looking for π content in α_{1/2}:")
    print(f"    α_{{1/2}} / π     = {alphas[1] / PI}")
    print(f"    α_{{1/2}} / π²    = {alphas[1] / PI**2}")
    print(f"    α_{{1/2}} · π     = {alphas[1] * PI}")
    print(f"    α_{{1/2}} · π²    = {alphas[1] * PI**2}")
    print(f"    α_{{1/2}} / √π    = {alphas[1] / sqrt(PI)}")

    # PSLQ on α_{1/2} against {1, π, 1/π, π², √π, log 2, ...}
    print()
    print("  PSLQ on α_{1/2} against arithmetic basis:")
    basis = [
        mpf(1),
        PI,
        1 / PI,
        PI**2,
        sqrt(PI),
        log(mpf(2)),
        PI * log(mpf(2)),
        zeta(3),
        sqrt(mpf(2)),
        sqrt(mpf(2)) / PI,
        PI / sqrt(mpf(2)),
        1 / sqrt(PI),
        PI**2 / 6,
    ]
    basis_labels = [
        "1", "π", "1/π", "π²", "√π", "log 2", "π·log 2", "ζ(3)",
        "√2", "√2/π", "π/√2", "1/√π", "π²/6",
    ]
    rels = pslq([alphas[1]] + basis, tol=mpf("1e-50"), maxcoeff=10**12)
    if rels:
        print(f"    PSLQ relation: {rels}")
        print(f"    Basis: ['α_{{1/2}}'] + {basis_labels}")
        if rels[0] != 0:
            terms = []
            for i, c in enumerate(rels[1:]):
                if c != 0:
                    terms.append(f"({-c}/{rels[0]})·{basis_labels[i]}")
            print(f"    α_{{1/2}} = {' + '.join(terms)}")
    else:
        print("    No relation found.  α_{1/2} is a new transcendental,")
        print("    or relation requires basis beyond what was tested.")


if __name__ == '__main__':
    main()
