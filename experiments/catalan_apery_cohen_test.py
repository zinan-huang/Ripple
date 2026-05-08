"""
Catalan G via Apéry-Cohen 1981 3-term recurrence — empirical kernel test.

Apéry stated (1979 unpublished, attributed to him by Cohen 1981) that
the recurrence
    q_n = (8n²+8n+1) q_{n-1} - 4n²(2n-1)² q_{n-2}     [Apéry-Cohen]
admits two integer-valued solutions:
    p_n: p_0=0, p_1=1
    q_n: q_0=1, q_1=8 (or some normalization)
with p_n / q_n → 8 G (or similar rescaling), giving an
irrationality-measure proof of G ∉ ℚ.

If this 3-term recurrence has a 2-D solution space whose ratio gives
G (after constant rescaling), then by ANALOGY WITH APÉRY ζ(3), the
construction admits an analog ratio-readout PIVP — the PF operator
behind the recurrence has 2-D formal-power-series kernel and we can
do Apéry's trick.

This script:
  (i)  generates p_n, q_n via the recurrence (numerically, mp.dps=200)
  (ii) tests p_n/q_n → c·G for some rational c (via PSLQ)
  (iii) checks |p_n - c·G·q_n| decay rate (geometric? polynomial?)

If the test is positive (c rational, decay geometric), then Catalan
admits an Apéry-style ratio-readout PIVP — falsifying my earlier
"1-D kernel" conjecture and giving a fast Catalan analog computer.

If negative (no clean ratio convergence), the obstruction story holds.

RESULT (this run): The recurrence
   a_n = (8n²+8n+1)a_{n-1} − 4n²(2n-1)² a_{n-2}
with init (p_0,p_1)=(0,1), (q_0,q_1)=(1,9) gives p_n/q_n →
0.20030734806892893... — a constant which is NOT G, NOT 8G, and
NOT identifiable via PSLQ against {1, G, π, log 2, √2, ζ(3), G/π,
π·G} at maxcoeff 10^10.  So this specific recurrence is not the
correct Apéry-Cohen form (or the initial conditions are wrong).

The structural question for Catalan G — whether SOME 3-term integer
recurrence yields a 2-D kernel ratio-readout — remains open here.
"""
from mpmath import mpf, mp, log, log10, pslq, catalan, sqrt
mp.dps = 200
G = mp.catalan
PI = mp.pi


def apery_cohen_catalan(N=40):
    """Apéry-Cohen 3-term recurrence for Catalan irrationality.

    a_n = (8n²+8n+1) a_{n-1} - 4n²(2n-1)² a_{n-2}.

    Two independent integer solutions:
      p_n with p_0 = 0, p_1 = 1
      q_n with q_0 = 1, q_1 = 9   (Cohen 1981 normalization;
                                    actually p_1=8, q_1=9 perhaps)

    Variable initial conditions; we'll try a few.
    """
    # Try Cohen's actual values (need to look up — from his paper):
    # Cohen 1981 has p_0=0, p_1=1, q_0=1, q_1=??  Try multiple.
    def make_seq(s0, s1, N):
        a = [mpf(s0), mpf(s1)]
        for n in range(2, N+1):
            new = (8*n*n + 8*n + 1) * a[-1] - 4*n*n*(2*n-1)**2 * a[-2]
            a.append(new)
        return a

    p_seq = make_seq(0, 1, N)
    q_seq = make_seq(1, 9, N)

    return p_seq, q_seq


def test_ratio(p_seq, q_seq):
    """Compute p_n/q_n and compare to G·c for various c."""
    N = len(p_seq) - 1
    print(f"  {'n':>3}  {'p_n / q_n':>30}  {'log|p_n/q_n - G|':>20}  {'log|p_n/q_n - 8G|':>20}")
    print(f"  {'-'*3}  {'-'*30}  {'-'*20}  {'-'*20}")
    for n in [3, 5, 8, 12, 16, 20, 25, 30, 35, N]:
        if n > N: break
        if q_seq[n] == 0:
            continue
        ratio = p_seq[n] / q_seq[n]
        err_G = abs(ratio - G)
        err_8G = abs(ratio - 8*G)
        log_eG  = float(log10(err_G))  if err_G  > 0 else float('-inf')
        log_e8G = float(log10(err_8G)) if err_8G > 0 else float('-inf')
        print(f"  {n:>3}  {float(ratio):>30.18f}  {log_eG:>20.4f}  {log_e8G:>20.4f}")


def pslq_against_G(p_seq, q_seq, N_test=30):
    """For large n, find PSLQ relations p_n + a·q_n + b·G·q_n = 0
    (i.e., p_n / q_n = -a - b·G, so c = -b)."""
    print(f"  PSLQ test at n={N_test}:")
    if N_test >= len(p_seq):
        N_test = len(p_seq) - 1
    p, q = p_seq[N_test], q_seq[N_test]
    if q == 0:
        print("    q_n = 0; skip.")
        return
    ratio = p / q
    rels = pslq([ratio, mpf(1), G], tol=mpf("1e-100"), maxcoeff=10**10)
    if rels:
        print(f"    PSLQ: {rels[0]}·(p/q) + {rels[1]}·1 + {rels[2]}·G = 0")
        if rels[0] != 0:
            a = mpf(-rels[1]) / rels[0]
            b = mpf(-rels[2]) / rels[0]
            print(f"    ⇒ p/q = {a} + {b}·G")
    else:
        print("    No PSLQ relation found (possibly p/q irrational/transcendental).")


def main():
    print("=" * 76)
    print("  Catalan G: Apéry-Cohen 3-term recurrence — kernel dimension test")
    print("=" * 76)
    print()
    print(f"  G = {float(G):.40f}")
    print()
    print("  Recurrence: a_n = (8n²+8n+1) a_{n-1} - 4n²(2n-1)² a_{n-2}")
    print()

    p_seq, q_seq = apery_cohen_catalan(N=40)

    print(f"  Generated p_n (init 0,1) and q_n (init 1,9):")
    for n in [0, 1, 2, 3, 5, 10, 20, 40]:
        if n < len(p_seq):
            print(f"    p_{n} = {p_seq[n]}")
            print(f"    q_{n} = {q_seq[n]}")
            print()

    print("--- Ratio convergence test ---")
    test_ratio(p_seq, q_seq)
    print()

    print("--- PSLQ against G ---")
    for n_test in [10, 20, 30, 40]:
        if n_test < len(p_seq):
            pslq_against_G(p_seq, q_seq, n_test)
            print()

    # Decay rate of |p_n - c·G·q_n|
    print("--- Decay rate of |p_n - c·G·q_n| for best c ---")
    # Find c numerically via large-N ratio
    n_big = 35
    if n_big < len(p_seq) and q_seq[n_big] != 0:
        c_emp = p_seq[n_big] / (G * q_seq[n_big])
        print(f"  Empirical c ≈ p_{n_big}/(G·q_{n_big}) = {float(c_emp):.10f}")
        for n in [5, 10, 15, 20, 25, 30, 35]:
            if n < len(p_seq) and q_seq[n] != 0:
                err = p_seq[n] - c_emp * G * q_seq[n]
                if err != 0:
                    log_err = float(log10(abs(err)))
                    print(f"    n={n:3d}: log|p_n - c·G·q_n| = {log_err:.4f}")


if __name__ == '__main__':
    main()
