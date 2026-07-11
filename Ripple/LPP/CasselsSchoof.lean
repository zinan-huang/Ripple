import Ripple.LPP.EhrenfestUrn

/-!
  Schoof/Cassels bridge for the Ehrenfest LPP obstruction.

  The local q-adic package now reduces the remaining external number-theory
  input to the lower-prime Cassels frontier
  `CatalanCasselsUpperDivisorNatLT`.  Schoof's Chapter 6 proves this through
  an integer Cassels theorem.  This file records the exact symmetry bridge:
  the Nat lower-prime statement follows from the integer "large prime divides
  the second base" half.

  No theorem is axiomatized here.  The hard Runge/Pade proof is isolated in
  the proposition `IntCatalanCasselsLargePrimeDivisorGT`.
-/

namespace Ripple

/-- Integer Cassels large-prime divisor half, oriented as in Schoof Chapter 6.

For odd prime exponents `Q < P`, any nonzero integer solution
`X^P - Y^Q = 1` has the larger exponent prime `P` dividing the second base
`Y`.  This is the hard Runge/Pade half needed by the LPP branch after the
symmetry `(x,y,p,q) ↦ (-y,-x,q,p)`. -/
def IntCatalanCasselsLargePrimeDivisorGT : Prop :=
  ∀ X Y : ℤ, ∀ P Q : ℕ,
    X ≠ 0 → Y ≠ 0 → P.Prime → Q.Prime →
      5 ≤ P → 5 ≤ Q → Q < P →
        X ^ P - Y ^ Q = 1 → (P : ℤ) ∣ Y

private lemma nat_dvd_of_int_dvd_neg_natCast {q x : ℕ}
    (h : (q : ℤ) ∣ (-(x : ℤ))) :
    q ∣ x := by
  have hAbs : Int.natAbs ((q : ℤ)) ∣ Int.natAbs (-(x : ℤ)) :=
    Int.natAbs_dvd_natAbs.mpr h
  simpa using hAbs

/-- The integer large-prime Cassels half implies the exact Nat lower-prime
upper-base divisibility frontier used by the Ehrenfest proof.

The proof is purely algebraic: from `x^p = y^q + 1` with `p < q`, form the
integer solution `(-y)^q - (-x)^p = 1`.  Since the exponents are odd primes,
the integer theorem with `(P,Q) = (q,p)` gives `q ∣ -x`, hence `q ∣ x`. -/
theorem catalanCasselsUpperDivisorNatLT_of_int_large_prime_divisor_gt
    (hI : IntCatalanCasselsLargePrimeDivisorGT) :
    CatalanCasselsUpperDivisorNatLT := by
  intro x y p q hx hy hp hq hp5 hq5 hpq hpow
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hX_ne : (-(y : ℤ)) ≠ 0 := by
    exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (by omega))
  have hY_ne : (-(x : ℤ)) ≠ 0 := by
    exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (by omega))
  have hpowZ : ((x : ℤ) ^ p) = ((y : ℤ) ^ q) + 1 := by
    exact_mod_cast hpow
  have hIntEq : (-(y : ℤ)) ^ q - (-(x : ℤ)) ^ p = 1 := by
    rw [hq_odd.neg_pow, hp_odd.neg_pow]
    omega
  have hdvdInt : (q : ℤ) ∣ (-(x : ℤ)) :=
    hI (-(y : ℤ)) (-(x : ℤ)) q p hX_ne hY_ne hq hp hq5 hp5 hpq hIntEq
  exact nat_dvd_of_int_dvd_neg_natCast hdvdInt

/-- The same integer Cassels half closes the narrow no-lower-prime-divisor
Catalan interface used by the final LPP obstruction. -/
theorem noLowerPrimeDivisorCatalanNat_of_int_large_prime_divisor_gt
    (hI : IntCatalanCasselsLargePrimeDivisorGT) :
    NoLowerPrimeDivisorCatalanNat :=
  noLowerPrimeDivisorCatalanNat_of_cassels_upper_divisor_lt
    (catalanCasselsUpperDivisorNatLT_of_int_large_prime_divisor_gt hI)

/-- Final Ehrenfest obstruction route through the correctly oriented integer
Schoof/Cassels large-prime half. -/
theorem noEhrenfestModFivePowerObstruction_of_int_large_prime_divisor_gt
    (hI : IntCatalanCasselsLargePrimeDivisorGT) :
    NoEhrenfestModFivePowerObstruction :=
  noEhrenfestModFivePowerObstruction_of_cassels_upper_divisor_lt
    (catalanCasselsUpperDivisorNatLT_of_int_large_prime_divisor_gt hI)

/-- Public all-degree wrapper through the integer Schoof/Cassels frontier. -/
theorem ehrenfest_all_algebraic_degrees_of_int_large_prime_divisor_gt
    (d : ℕ) (hd : 0 < d) (hI : IntCatalanCasselsLargePrimeDivisorGT) :
    ∃ ν : ℝ, IsEhrenfestComputable ν ∧
      ∃ P : Polynomial ℤ, P.natDegree = d ∧
      Polynomial.eval₂ (Int.castRingHom ℝ) ν P = 0 ∧ Irreducible P := by
  exact ehrenfest_all_algebraic_degrees_of_cassels_upper_divisor_lt_via_normalized_q_gap
    d hd (catalanCasselsUpperDivisorNatLT_of_int_large_prime_divisor_gt hI)

end Ripple
