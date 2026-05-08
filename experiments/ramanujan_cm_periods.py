"""
Ramanujan PF at the CM point z_0 = 1/396^4: search for π-period
combinations beyond the canonical 1103·A + 26390·z₀·A'.

The Picard-Fuchs ODE is order 3, so the local 3-D solution space at z_0
has a basis (A, y_1, y_2) where y_1, y_2 involve log z.  Three linearly
independent periods at z_0:
    P_0 := A(z_0),
    P_1 := z_0 · A'(z_0),
    P_2 := z_0² · A''(z_0).

Ramanujan's identity uses the combination 1103·P_0 + 26390·P_1 = 9801/(2√2·π).

Question: are there OTHER rational combinations of (P_0, P_1, P_2) that
yield simple π-expressions? If so, each gives a distinct π-PIVP construction.

We compute P_0, P_1, P_2 to high precision and PSLQ them against
{1, π, 1/π, π², 1/π², √2, √2/π, π/√2, ...}.
"""
from mpmath import mpf, mp, pi, sqrt, log, pslq, zeta, mpc
mp.dps = 80

PI = mp.pi


def hg3f2_at_z0(N=80):
    """Compute P_0 = A(z_0), P_1 = z_0 A'(z_0), P_2 = z_0² A''(z_0) using
    the recurrence for a_k = (4k)!/(k!)^4 and z_0 = 1/396^4."""
    z0 = mpf(1) / mpf(396)**4
    a = mpf(1)
    P0 = mpf(0); P1 = mpf(0); P2 = mpf(0)
    zpow = mpf(1)  # z_0^k
    for k in range(N + 1):
        P0 += a * zpow
        if k >= 1:
            P1 += a * k * zpow  # k a_k z_0^k = z_0 · k a_k z_0^{k-1}
        if k >= 2:
            P2 += a * k * (k - 1) * zpow  # k(k-1) a_k z_0^k = z_0² · k(k-1) a_k z_0^{k-2}
        # a_{k+1}/a_k = 4(4k+1)(4k+2)(4k+3)/(k+1)^3
        a = a * 4 * (4*k+1) * (4*k+2) * (4*k+3) / (k+1)**3
        zpow = zpow * z0
    return P0, P1, P2


def main():
    print("=" * 76)
    print("  Ramanujan PF at CM point z_0 = 1/396^4: period basis search")
    print("=" * 76)
    print()

    P0, P1, P2 = hg3f2_at_z0(80)
    print(f"  P_0 := A(z_0)             = {P0}")
    print(f"  P_1 := z_0 · A'(z_0)      = {P1}")
    print(f"  P_2 := z_0² · A''(z_0)    = {P2}")
    print()
    print(f"  Ramanujan check: 1103 P_0 + 26390 P_1 = {1103*P0 + 26390*P1}")
    print(f"                   9801/(2√2·π)         = {9801/(2*sqrt(2)*PI)}")
    print()

    # Now look at each period individually.
    print("  Test each P_j against the standard π basis:")
    basis_labels = ["1", "π", "1/π", "π²", "1/π²", "√2/π", "π/√2", "√2·π", "π·√2/396",
                    "log 2", "π log 2", "ζ(3)", "ζ(3)/π"]
    basis = [mpf(1), PI, 1/PI, PI**2, 1/PI**2, sqrt(2)/PI, PI/sqrt(2),
             sqrt(2)*PI, PI*sqrt(2)/396, log(mpf(2)), PI*log(mpf(2)),
             zeta(3), zeta(3)/PI]

    for j, P in enumerate([P0, P1, P2]):
        print(f"\n  P_{j} = {P}")
        rels = pslq([P] + basis, tol=mpf("1e-50"), maxcoeff=10**12)
        if rels and rels[0] != 0:
            print(f"    PSLQ found: {rels}")
            terms = []
            for i, c in enumerate(rels[1:]):
                if c != 0:
                    terms.append(f"({-c}/{rels[0]})·{basis_labels[i]}")
            print(f"    P_{j} = {' + '.join(terms)}")
        else:
            print(f"    No simple relation found.")

    # Now try: linear combinations a·P_0 + b·P_1 + c·P_2 against {1, π, 1/π, ...}
    print()
    print("  Joint PSLQ on (P_0, P_1, P_2) against π-basis:")
    print("  Looking for integer combinations (n_0, n_1, n_2, m_1, m_2, ...) such that")
    print("    n_0 P_0 + n_1 P_1 + n_2 P_2 = m_1·1 + m_2·π + m_3·1/π + m_4·1/(√2·π) ...")
    rels = pslq([P0, P1, P2, mpf(1), PI, 1/PI, 1/(sqrt(2)*PI),
                 sqrt(2)/PI, PI/sqrt(2), mpf(1)/(sqrt(mpf(2))*PI*9801)],
                tol=mpf("1e-50"), maxcoeff=10**8)
    if rels:
        labels = ["P_0", "P_1", "P_2", "1", "π", "1/π", "1/(√2 π)",
                  "√2/π", "π/√2", "1/(9801·√2·π)"]
        print(f"    PSLQ relation: {rels}")
        for lab, c in zip(labels, rels):
            if c != 0:
                print(f"      {c}·{lab}")
    else:
        print("    No relation.  Increase basis or coeff bound.")

    # Try: scan all (n_0, n_1, n_2) with small bounds for c_0 P_0 + c_1 P_1 + c_2 P_2
    # being a simple π-multiple.
    print()
    print("  Scan small integer combinations (|n_i| ≤ 5) for hits on π-multiples:")
    pi_targets = {
        "1/π": 1/PI,
        "π": PI,
        "1/(π√2)": 1/(PI*sqrt(2)),
        "π/√2": PI/sqrt(2),
        "√2/π": sqrt(2)/PI,
        "1/π²": 1/PI**2,
        "1/(9801·√2·π)": mpf(1)/(9801*sqrt(2)*PI),
    }
    found = []
    for n0 in range(-10, 11):
        for n1 in range(-10, 11):
            for n2 in range(-10, 11):
                if n0 == 0 and n1 == 0 and n2 == 0:
                    continue
                comb = n0*P0 + n1*P1 + n2*P2
                if abs(comb) < mpf("1e-40"):
                    continue
                for label, target in pi_targets.items():
                    ratio = comb / target
                    # Check if ratio is rational with small denom
                    for denom in range(1, 100):
                        rval = float(ratio * denom)
                        if abs(rval - round(rval)) < 1e-25 and abs(round(rval)) < 100000:
                            found.append((n0, n1, n2, label, denom, round(rval)))
                            break
    found = list(set(found))
    if found:
        print("  Found combinations:")
        for n0, n1, n2, lab, dn, num in found[:30]:
            print(f"    {n0:+d}·P_0 {n1:+d}·P_1 {n2:+d}·P_2 = ({num}/{dn}) · {lab}")
    else:
        print("  No (small) integer combinations match simple π multiples.")

    # Use the PF ODE to express P_2 in terms of P_0 and P_1.
    # PF: z²(1−256z) f''' + 3z(1−384z) f'' + (1−816z) f' − 24 f = 0.
    # Multiply by z to get an Euler-type equation:
    #   z³(1−256z) f''' + 3z²(1−384z) f'' + z(1−816z) f' − 24 z f = 0
    # In Euler form θ f = z f' (so P_1 = θ_z A at z_0):
    # Actually simpler: at z = z_0, use the PF directly to get a linear
    # relation on A''', A'', A', A.  Then the period algebra has at most
    # 3 independent values (P_0, P_1, P_2); P_3 is dependent.
    print()
    print("  Sanity check: PF relation at z_0")
    z0 = mpf(1) / mpf(396)**4
    P3 = (24 * P0 - (1 - 816*z0) * P1/z0 - 3*z0*(1 - 384*z0) * P2/z0**2) / (z0**2*(1 - 256*z0))
    P3 *= z0**3   # z_0³ A'''(z_0)
    print(f"    P_3 := z_0³ A'''(z_0) (computed via PF) = {P3}")


if __name__ == '__main__':
    main()
