import Ripple.LPP.CasselsElementary
import Ripple.LPP.EhrenfestUrn

/-!
# Albenque–Gerin: Ehrenfest-computable algebraic numbers of every degree

M. Albenque and L. Gerin, "On the algebraic numbers computable by some generalized Ehrenfest
urns", DMTCS 14(2) (2012), Theorem 5: the set of Ehrenfest-computable numbers contains
algebraic numbers of every degree `d ≥ 1`.

`EhrenfestUrn.lean` proves this from the lower-prime Cassels divisibility statement
`CatalanCasselsUpperDivisorNatLT`
(`ehrenfest_all_algebraic_degrees_of_cassels_upper_divisor_lt_via_normalized_q_gap`).
`CasselsElementary.lean` proves Cassels' divisibility `q ∣ x` for `x^p = y^q + 1`
(`cassels_upper_divisor_nat_elementary`, primes `p, q ≥ 5`, `x, y > 1`, no order premise).
The two files sit in separate import branches; this module composes them.
-/

namespace Ripple

/-- Cassels' divisibility theorem in the form `CatalanCasselsUpperDivisorNat`:
for primes `p, q ≥ 5` and `x, y > 1`, `x^p = y^q + 1` implies `q ∣ x`. -/
theorem catalanCasselsUpperDivisorNat_holds : CatalanCasselsUpperDivisorNat :=
  fun x y p q hx hy hp hq hp5 hq5 hpow =>
    cassels_upper_divisor_nat_elementary x y p q hx hy hp hq hp5 hq5 hpow

/-- The lower-prime range `p < q` of Cassels' divisibility theorem, the premise of the
Ehrenfest every-degree construction. This range needs only the leading-coefficient descent of
`CasselsElementary`, not Cassels' Lemma 2. -/
theorem catalanCasselsUpperDivisorNatLT_holds : CatalanCasselsUpperDivisorNatLT :=
  fun x y p q hx hy hp hq hp5 hq5 hpq hpow =>
    cassels_upper_divisor_nat_elementary_of_p_lt_q x y p q hx hy hp hq hp5 hq5 hpq hpow

/-- **Albenque–Gerin, Theorem 5 (every degree).** For every `d ≥ 1` there is an
Ehrenfest-computable `ν` that is a root of an irreducible integer polynomial of degree `d`. -/
theorem isEhrenfestComputable_algebraic_of_degree (d : ℕ) (hd : 0 < d) :
    ∃ ν : ℝ, IsEhrenfestComputable ν ∧
      ∃ P : Polynomial ℤ, P.natDegree = d ∧
      Polynomial.eval₂ (Int.castRingHom ℝ) ν P = 0 ∧ Irreducible P :=
  ehrenfest_all_algebraic_degrees_of_cassels_upper_divisor_lt_via_normalized_q_gap d hd
    catalanCasselsUpperDivisorNatLT_holds

end Ripple
