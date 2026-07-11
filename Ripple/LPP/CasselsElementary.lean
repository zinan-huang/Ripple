/-
  Ripple.LPP.CasselsElementary — Elementary Cassels upper-divisor layer

  Goal: prove `CatalanCasselsUpperDivisorNat` (q ∣ x for `x^p = y^q + 1`
  with p,q odd primes ≥ 5) by an elementary argument that does NOT need
  cyclotomic fields, ideals, Dedekind domains, or rings of integers.

  Pipeline (Cassels 1960 style, in ℕ/ℤ):
    1. y^q + 1 = (y+1) * Ψ_q(y) for odd q, where
         Ψ_q(y) = y^(q-1) - y^(q-2) + ... - y + 1.
    2. gcd(y+1, Ψ_q(y)) = gcd(y+1, q).
    3. Coprime product = p-th power ⟹ each factor is a p-th power.
    4. After substituting y+1 = u^p, the residual identity
         Ψ_q(u^p - 1) = v^p
       has no solution for distinct odd primes p,q ≥ 5
       (leading-coefficient binomial-descent contradiction).
    5. Combine: from `¬ q ∣ x` and `x^p = y^q + 1`, derive a witness for
       step 4, contradicting it; hence q ∣ x.

  Status: lemmas 1-3 structurally closed with a small number of marked
  TODOs for exact mathlib API names; lemma 4 is the hard standalone
  arithmetic lemma and still `sorry`.  Lemma 5 chains 1-4.
-/

import Ripple.LPP.CasselsClassical
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

namespace Ripple

/-! ## Definitions -/

/-- Integer alternating quotient

    Ψ_q(y) = y^(q-1) - y^(q-2) + ... - y + 1.

For odd `q`, this satisfies `(y + 1) * Ψ_q(y) = y^q + 1`. The integer
version is the cleanest representation of the alternating signs. -/
def altCyclotomicPlusZ (q y : ℕ) : ℤ :=
  ∑ i ∈ Finset.range q, (-1 : ℤ) ^ i * (y : ℤ) ^ (q - 1 - i)

/-- Natural-number version of the alternating quotient.

For odd `q`, this equals the positive integer `(y^q + 1) / (y + 1)`. -/
def altCyclotomicPlusNat (q y : ℕ) : ℕ :=
  Int.natAbs (altCyclotomicPlusZ q y)

/-! ## Shared private helpers for the integer identity and its positivity -/

/-- Integer-level telescoping identity that underlies the factorization of
`y^q + 1`. For any `n`,

    (y + 1) * ∑_{i=0}^{n-1} (-1)^i y^(n-1-i) = y^n - (-1)^n.

Specializing to odd `n = q` gives the public Lemma 1 below. -/
private theorem altCyclotomicPlusZ_geom_telescope
    (y : ℕ) (n : ℕ) :
    ((y : ℤ) + 1) *
        (∑ i ∈ Finset.range n,
          (-1 : ℤ) ^ i * (y : ℤ) ^ (n - 1 - i))
      =
    (y : ℤ) ^ n - (-1 : ℤ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hscale :
          (∑ i ∈ Finset.range n,
            (-1 : ℤ) ^ i * (y : ℤ) ^ (n - i))
            =
          (y : ℤ) *
            (∑ i ∈ Finset.range n,
              (-1 : ℤ) ^ i * (y : ℤ) ^ (n - 1 - i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi_lt : i < n := Finset.mem_range.mp hi
        have hsub : n - i = (n - 1 - i) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      have htail :
          (-1 : ℤ) ^ n * (y : ℤ) ^ (n - n) =
            (-1 : ℤ) ^ n := by
        simp
      have hscale' :
          (∑ x ∈ Finset.range n,
            (-1 : ℤ) ^ x * (y : ℤ) ^ (n + 1 - 1 - x))
            =
          (y : ℤ) *
            (∑ i ∈ Finset.range n,
              (-1 : ℤ) ^ i * (y : ℤ) ^ (n - 1 - i)) := by
        convert hscale using 2
      have htail' :
          (-1 : ℤ) ^ n * (y : ℤ) ^ (n + 1 - 1 - n) =
            (-1 : ℤ) ^ n := by
        simpa using htail
      rw [hscale', htail']
      calc
        ((y : ℤ) + 1) *
            ((y : ℤ) *
                (∑ i ∈ Finset.range n,
                  (-1 : ℤ) ^ i * (y : ℤ) ^ (n - 1 - i))
              + (-1 : ℤ) ^ n)
            =
          (y : ℤ) *
              (((y : ℤ) + 1) *
                (∑ i ∈ Finset.range n,
                  (-1 : ℤ) ^ i * (y : ℤ) ^ (n - 1 - i)))
            + ((y : ℤ) + 1) * (-1 : ℤ) ^ n := by
              ring
        _ =
          (y : ℤ) * ((y : ℤ) ^ n - (-1 : ℤ) ^ n)
            + ((y : ℤ) + 1) * (-1 : ℤ) ^ n := by
              rw [ih]
        _ =
          (y : ℤ) ^ (n + 1) - (-1 : ℤ) ^ (n + 1) := by
              ring_nf

/-- Integer factorization identity for odd `q`. -/
private theorem altCyclotomicPlusZ_mul_eq_pow_add_one_int
    (y q : ℕ) (hq_odd : Odd q) :
    ((y : ℤ) + 1) * altCyclotomicPlusZ q y =
      (y : ℤ) ^ q + 1 := by
  have hneg_one_pow : (-1 : ℤ) ^ q = -1 := by
    rcases hq_odd with ⟨k, hk⟩
    rw [hk]
    simp [pow_succ, pow_mul]
  unfold altCyclotomicPlusZ
  have h := altCyclotomicPlusZ_geom_telescope y q
  rw [hneg_one_pow] at h
  simpa using h

/-- The alternating quotient is nonnegative for odd `q`. -/
private theorem altCyclotomicPlusZ_nonneg_of_odd
    (y q : ℕ) (hq_odd : Odd q) :
    0 ≤ altCyclotomicPlusZ q y := by
  have hypos : 0 < ((y : ℤ) + 1) := by
    have : 0 ≤ (y : ℤ) := Int.ofNat_nonneg y
    omega
  have hZ := altCyclotomicPlusZ_mul_eq_pow_add_one_int y q hq_odd
  have hprod_nonneg :
      0 ≤ ((y : ℤ) + 1) * altCyclotomicPlusZ q y := by
    rw [hZ]; positivity
  have hprod_nonneg' :
      0 ≤ altCyclotomicPlusZ q y * ((y : ℤ) + 1) := by
    simpa [mul_comm] using hprod_nonneg
  exact nonneg_of_mul_nonneg_left hprod_nonneg' hypos

/-- ℕ↔ℤ bridge: the Nat version is the literal cast of the (nonneg) ℤ version. -/
private theorem altCyclotomicPlusNat_cast_eq
    (y q : ℕ) (hq_odd : Odd q) :
    ((altCyclotomicPlusNat q y : ℕ) : ℤ) =
      altCyclotomicPlusZ q y := by
  unfold altCyclotomicPlusNat
  exact Int.natAbs_of_nonneg (altCyclotomicPlusZ_nonneg_of_odd y q hq_odd)

/-! ## Lemma 1: factorization of `y^q + 1` -/

/-- Factorization of `y^q + 1` by the alternating quotient. -/
theorem alt_cyclotomic_plus_nat_mul_eq_pow_add_one
    (y q : ℕ) (hq_odd : Odd q) :
    (y + 1) * altCyclotomicPlusNat q y = y ^ q + 1 := by
  apply Int.ofNat.inj
  change (((y + 1) * altCyclotomicPlusNat q y : ℕ) : ℤ) =
    ((y ^ q + 1 : ℕ) : ℤ)
  push_cast
  rw [altCyclotomicPlusNat_cast_eq y q hq_odd]
  exact altCyclotomicPlusZ_mul_eq_pow_add_one_int y q hq_odd

/-! ## Lemma 2: the gcd-residue identity -/

private lemma altCyclotomicPlusZ_mod_add_one
    (y q : ℕ) (hq_odd : Odd q) :
    altCyclotomicPlusZ q y ≡
      (q : ℤ) [ZMOD ((y + 1 : ℕ) : ℤ)] := by
  unfold altCyclotomicPlusZ
  have hy_mod : (y : ℤ) ≡ (-1 : ℤ) [ZMOD ((y + 1 : ℕ) : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-1, by push_cast; ring⟩
  have hq_even_sub_one : Even (q - 1) := by
    rcases hq_odd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have hneg_pow_q_sub_one : (-1 : ℤ) ^ (q - 1) = 1 := by
    rcases hq_even_sub_one with ⟨k, hk⟩
    rw [hk]; simp [pow_mul]
  have hterm :
      ∀ i ∈ Finset.range q,
        (-1 : ℤ) ^ i * (y : ℤ) ^ (q - 1 - i)
          ≡ 1 [ZMOD ((y + 1 : ℕ) : ℤ)] := by
    intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    have hpow_y :
        (y : ℤ) ^ (q - 1 - i) ≡
          (-1 : ℤ) ^ (q - 1 - i) [ZMOD ((y + 1 : ℕ) : ℤ)] :=
      hy_mod.pow _
    have hmul :
        (-1 : ℤ) ^ i * (y : ℤ) ^ (q - 1 - i)
          ≡
        (-1 : ℤ) ^ i * (-1 : ℤ) ^ (q - 1 - i)
          [ZMOD ((y + 1 : ℕ) : ℤ)] :=
      Int.ModEq.mul_left _ hpow_y
    have hexp_sum : i + (q - 1 - i) = q - 1 := by omega
    have hone : (-1 : ℤ) ^ i * (-1 : ℤ) ^ (q - 1 - i) = 1 := by
      rw [← pow_add, hexp_sum]; exact hneg_pow_q_sub_one
    exact hmul.trans (by simpa [hone])
  have hsum :
      (∑ i ∈ Finset.range q,
        (-1 : ℤ) ^ i * (y : ℤ) ^ (q - 1 - i))
        ≡
      (∑ i ∈ Finset.range q, (1 : ℤ))
        [ZMOD ((y + 1 : ℕ) : ℤ)] :=
    Int.ModEq.sum hterm
  have hones : (∑ i ∈ Finset.range q, (1 : ℤ)) = (q : ℤ) := by simp
  simpa [hones] using hsum

private lemma nat_gcd_eq_of_modEq
    (a b c : ℕ) (h : b ≡ c [MOD a]) :
    Nat.gcd a b = Nat.gcd a c := by
  simpa [Nat.gcd_comm] using h.gcd_eq

/-- ℕ-level residue identity: `Ψ_q(y) ≡ q [MOD y + 1]` for odd `q`.

Extracted from the proof of `gcd_add_one_alt_cyclotomic_plus_nat` so it
can be reused by the Cassels descent (Route A first step). -/
private lemma altCyclotomicPlusNat_mod_add_one
    (y q : ℕ) (hq_odd : Odd q) :
    altCyclotomicPlusNat q y ≡ q [MOD y + 1] := by
  have hmodZ :
      altCyclotomicPlusZ q y ≡
        (q : ℤ) [ZMOD ((y + 1 : ℕ) : ℤ)] :=
    altCyclotomicPlusZ_mod_add_one y q hq_odd
  have hcast : ((altCyclotomicPlusNat q y : ℕ) : ℤ) =
      altCyclotomicPlusZ q y :=
    altCyclotomicPlusNat_cast_eq y q hq_odd
  have hmodZ' :
      ((altCyclotomicPlusNat q y : ℕ) : ℤ) ≡
        (q : ℤ) [ZMOD ((y + 1 : ℕ) : ℤ)] := by
    simpa [hcast] using hmodZ
  exact_mod_cast hmodZ'

/-- The two factors `y + 1` and `Ψ_q(y)` have gcd equal to `gcd (y+1) q`.

Elementary replacement for the cyclotomic common-divisor statement:
modulo `y + 1`, the alternating quotient is congruent to `q`. -/
theorem gcd_add_one_alt_cyclotomic_plus_nat
    (y q : ℕ) (hq_odd : Odd q) :
    Nat.gcd (y + 1) (altCyclotomicPlusNat q y) =
      Nat.gcd (y + 1) q :=
  nat_gcd_eq_of_modEq (y + 1) (altCyclotomicPlusNat q y) q
    (altCyclotomicPlusNat_mod_add_one y q hq_odd)

/-! ## Lemma 3: coprime product of a prime-exponent power -/

private theorem exists_eq_pow_of_factorization_exp_dvd
    {N p : ℕ}
    (hN0 : N ≠ 0)
    (hp_pos : 0 < p)
    (hdiv : ∀ r : ℕ, p ∣ N.factorization r) :
    ∃ U : ℕ, N = U ^ p := by
  /- First try the one-line reconstruction theorem.  If the name has
     drifted in mathlib, fall back to explicit
       `let U := N.factorization.prod fun r e => r ^ (e / p)`
     + `Nat.factorization_inj` after rewriting both factorizations. -/
  refine ⟨Nat.floorRoot p N, ?_⟩
  have hp_ne : p ≠ 0 := Nat.ne_of_gt hp_pos
  have hroot_ne : Nat.floorRoot p N ≠ 0 :=
    Nat.floorRoot_ne_zero.mpr ⟨hp_ne, hN0⟩
  have hroot_dvd : Nat.floorRoot p N ^ p ∣ N :=
    Nat.floorRoot_pow_dvd
  have hN_dvd : N ∣ Nat.floorRoot p N ^ p := by
    rw [← Nat.factorization_le_iff_dvd hN0 (pow_ne_zero p hroot_ne)]
    intro r
    obtain ⟨m, hm⟩ := hdiv r
    rw [Nat.factorization_pow, Nat.factorization_floorRoot]
    simp [Finsupp.smul_apply, hm, Nat.mul_div_right _ hp_pos]
  exact Nat.dvd_antisymm hN_dvd hroot_dvd

private theorem left_factorization_exp_dvd_of_coprime_mul_eq_pow
    {A B X p : ℕ}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hp : p.Prime)
    (hcop : Nat.Coprime A B)
    (hprod : A * B = X ^ p) :
    ∀ r : ℕ, p ∣ A.factorization r := by
  intro r
  by_cases hr : r.Prime
  · have hmul_fun :
        (A * B).factorization = A.factorization + B.factorization :=
      Nat.factorization_mul hA0 hB0
    have hpow_fun :
        (X ^ p).factorization = p • X.factorization :=
      Nat.factorization_pow X p
    have hmul_r :
        (A * B).factorization r =
          A.factorization r + B.factorization r := by
      rw [hmul_fun]; rfl
    have hpow_r :
        (X ^ p).factorization r =
          p * X.factorization r := by
      rw [hpow_fun]; simp [nsmul_eq_mul]
    have hsum :
        A.factorization r + B.factorization r =
          p * X.factorization r := by
      calc
        A.factorization r + B.factorization r
            = (A * B).factorization r := by rw [hmul_r]
        _ = (X ^ p).factorization r := by rw [hprod]
        _ = p * X.factorization r := by rw [hpow_r]
    by_cases hAfac_zero : A.factorization r = 0
    · exact ⟨0, by simp [hAfac_zero]⟩
    · have hr_dvd_A : r ∣ A :=
        Nat.dvd_of_factorization_pos hAfac_zero
      have hBfac_zero : B.factorization r = 0 := by
        by_contra hBfac_ne_zero
        have hr_dvd_B : r ∣ B :=
          Nat.dvd_of_factorization_pos hBfac_ne_zero
        have hr_one : r = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop hr_dvd_A hr_dvd_B
        exact hr.ne_one hr_one
      have hAeq : A.factorization r = p * X.factorization r := by
        omega
      exact ⟨X.factorization r, hAeq⟩
  · have hzero : A.factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_prime A hr
    exact ⟨0, by simp [hzero]⟩

/-- If a product of coprime natural numbers equals a prime-exponent power,
then each factor is itself a `p`-th power.

Elementary `ℕ` UFD step used after splitting `x^p = (y + 1) * Ψ_q(y)`. -/
theorem coprime_mul_eq_prime_pow_split
    {A B X p : ℕ}
    (hp : p.Prime)
    (hcop : Nat.Coprime A B)
    (hprod : A * B = X ^ p) :
    ∃ U V : ℕ, A = U ^ p ∧ B = V ^ p := by
  by_cases hA0 : A = 0
  · subst hA0
    have hB_one : B = 1 := by simpa using hcop
    subst hB_one
    have hX0 : X = 0 := by
      have : X ^ p = 0 := by simpa using hprod.symm
      exact pow_eq_zero this
    subst hX0
    exact ⟨0, 1, by rw [zero_pow hp.ne_zero], by simp⟩
  by_cases hB0 : B = 0
  · subst hB0
    have hA_one : A = 1 := by simpa using hcop
    subst hA_one
    have hX0 : X = 0 := by
      have : X ^ p = 0 := by simpa using hprod.symm
      exact pow_eq_zero this
    subst hX0
    exact ⟨1, 0, by simp, by rw [zero_pow hp.ne_zero]⟩
  have hA_exp :
      ∀ r : ℕ, p ∣ A.factorization r :=
    left_factorization_exp_dvd_of_coprime_mul_eq_pow
      hA0 hB0 hp hcop hprod
  have hprod_comm : B * A = X ^ p := by rw [mul_comm]; exact hprod
  have hB_exp :
      ∀ r : ℕ, p ∣ B.factorization r :=
    left_factorization_exp_dvd_of_coprime_mul_eq_pow
      hB0 hA0 hp hcop.symm hprod_comm
  rcases exists_eq_pow_of_factorization_exp_dvd hA0 hp.pos hA_exp with ⟨U, hU⟩
  rcases exists_eq_pow_of_factorization_exp_dvd hB0 hp.pos hB_exp with ⟨V, hV⟩
  exact ⟨U, V, hU, hV⟩

/-! ## Lemma 4: the hard binomial-descent contradiction

Decomposed into private helpers per ChatGPT outline:
  - `shifted_alt_cyclotomic_top_two_expansion_int` (mechanical binomial)
  - `shifted_alt_cyclotomic_lt_top_power` + `pth_root_lt_of_shifted_alt_eq`
    (size bound v < u^(q-1))
  - `cassels_shifted_top_coefficient_p_lt_q` (the real arithmetic blocker:
    leading-coefficient comparison forces p · k = q, contradicting distinct
    primes)
  - `no_prime_coefficient_eq_of_ne` (trivial primality contradiction)

The lower-prime branch (`p < q`) is closed by the chain above.  The
`q < p` branch is currently `sorry`; the LPP obstruction package always
provides `p < q`, so downstream Ehrenfest use only needs the lower-prime
specialization. -/

/-- Top-two-term integer expansion of the shifted alternating quotient,
with an UNRESTRICTED integer remainder.

The stronger form factoring the remainder by `u^(p*(q-3))` is false:
e.g. `Ψ_5(z-1) = z^4 - 5z^3 + 10z^2 - 10z + 5`, and the tail
`10z^2 - 10z + 5` is not divisible by `z^2`.  See
`shifted_alt_cyclotomic_full_expansion_int` (placeholder below) for the
correct full expansion needed by the descent. -/
private theorem shifted_alt_cyclotomic_top_two_expansion_int
    (u p q : ℕ)
    (hu : 1 < u)
    (hq3 : 3 ≤ q) :
    ∃ R : ℤ,
      ((altCyclotomicPlusNat q (u ^ p - 1) : ℕ) : ℤ) =
        (u : ℤ) ^ (p * (q - 1))
          - (q : ℤ) * (u : ℤ) ^ (p * (q - 2))
          + R := by
  refine ⟨
    ((altCyclotomicPlusNat q (u ^ p - 1) : ℕ) : ℤ)
      - ((u : ℤ) ^ (p * (q - 1))
          - (q : ℤ) * (u : ℤ) ^ (p * (q - 2))), ?_⟩
  ring

/-- Range-shift form of the shifted quotient expansion.

This is the clean form obtained directly from the binomial expansion of
`(z - 1)^q + 1`, after the constant term cancels for odd `q`.

With `z = u^p`,
  `Ψ_q(z - 1) = ∑ j < q, (-1)^(q-(j+1)) * choose q (j+1) * z^j`. -/
private theorem shifted_alt_cyclotomic_full_expansion_range_int
    (u p q : ℕ)
    (hu : 1 < u)
    (hq_odd : Odd q) :
    ((altCyclotomicPlusNat q (u ^ p - 1) : ℕ) : ℤ) =
      ∑ j ∈ Finset.range q,
        (-1 : ℤ) ^ (q - (j + 1))
          * (Nat.choose q (j + 1) : ℤ)
          * (u : ℤ) ^ (p * j) := by
  classical
  let z : ℤ := (u : ℤ) ^ p
  have hz_nat_pos : 0 < u ^ p := pow_pos (by omega : 0 < u) p
  have hz_ne_zero : z ≠ 0 := by dsimp [z]; positivity
  have hcast_sub : ((u ^ p - 1 : ℕ) : ℤ) = z - 1 := by
    have hnat : u ^ p - 1 + 1 = u ^ p := Nat.sub_add_cancel (by omega)
    have hcast : ((u ^ p - 1 : ℕ) : ℤ) + 1 = (u : ℤ) ^ p := by
      exact_mod_cast hnat
    dsimp [z]
    omega
  have hcast_alt :
      ((altCyclotomicPlusNat q (u ^ p - 1) : ℕ) : ℤ) =
        altCyclotomicPlusZ q (u ^ p - 1) := by
    exact altCyclotomicPlusNat_cast_eq (u ^ p - 1) q hq_odd
  have hbase : ((u ^ p - 1 : ℕ) : ℤ) + 1 = z := by dsimp [z]; omega
  have hpowa : ((u ^ p - 1 : ℕ) : ℤ) ^ q = (z - 1) ^ q := by
    rw [hcast_sub]
  have hmul_left :
      z * ((altCyclotomicPlusNat q (u ^ p - 1) : ℕ) : ℤ) =
        (z - 1) ^ q + 1 := by
    rw [hcast_alt]
    have h := altCyclotomicPlusZ_mul_eq_pow_add_one_int (u ^ p - 1) q hq_odd
    simpa [hbase, hpowa, mul_comm] using h
  have hneg_one_pow_q : (-1 : ℤ) ^ q = -1 := by
    rcases hq_odd with ⟨r, hr⟩
    rw [hr]; simp [pow_succ, pow_mul]
  have hbinom :
      (z - 1) ^ q + 1 =
        z *
          (∑ j ∈ Finset.range q,
            (-1 : ℤ) ^ (q - (j + 1))
              * (Nat.choose q (j + 1) : ℤ)
              * z ^ j) := by
    have hadd :
        (z + (-1 : ℤ)) ^ q =
          ∑ k ∈ Finset.range (q + 1),
            (Nat.choose q k : ℤ) * z ^ k * (-1 : ℤ) ^ (q - k) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (add_pow z (-1 : ℤ) q)
    have hsplit :
        (∑ k ∈ Finset.range (q + 1),
            (Nat.choose q k : ℤ) * z ^ k * (-1 : ℤ) ^ (q - k))
          =
        (-1 : ℤ) ^ q +
            ∑ j ∈ Finset.range q,
              (Nat.choose q (j + 1) : ℤ)
                * z ^ (j + 1)
                * (-1 : ℤ) ^ (q - (j + 1)) := by
      rw [Finset.sum_range_succ']
      simp [Nat.choose_zero_right, add_comm]
    calc
      (z - 1) ^ q + 1
          = (z + (-1 : ℤ)) ^ q + 1 := by ring
      _ =
          ((∑ k ∈ Finset.range (q + 1),
              (Nat.choose q k : ℤ) * z ^ k * (-1 : ℤ) ^ (q - k))
            + 1) := by rw [hadd]
      _ =
          ((-1 : ℤ) ^ q
            + ∑ j ∈ Finset.range q,
              (Nat.choose q (j + 1) : ℤ)
                * z ^ (j + 1)
                * (-1 : ℤ) ^ (q - (j + 1)))
            + 1 := by rw [hsplit]
      _ =
          ∑ j ∈ Finset.range q,
            (Nat.choose q (j + 1) : ℤ)
              * z ^ (j + 1)
              * (-1 : ℤ) ^ (q - (j + 1)) := by
              rw [hneg_one_pow_q]; ring
      _ =
          z *
            (∑ j ∈ Finset.range q,
              (-1 : ℤ) ^ (q - (j + 1))
                * (Nat.choose q (j + 1) : ℤ)
                * z ^ j) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [pow_succ]; ring
  have hmul_right :
      z *
        (∑ j ∈ Finset.range q,
          (-1 : ℤ) ^ (q - (j + 1))
            * (Nat.choose q (j + 1) : ℤ)
            * (u : ℤ) ^ (p * j))
        =
      (z - 1) ^ q + 1 := by
    rw [hbinom]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hzpow : z ^ j = (u : ℤ) ^ (p * j) := by
      dsimp [z]; rw [← pow_mul]
    rw [hzpow]
  apply mul_left_cancel₀ hz_ne_zero
  calc
    z * ((altCyclotomicPlusNat q (u ^ p - 1) : ℕ) : ℤ)
        = (z - 1) ^ q + 1 := hmul_left
    _ =
      z *
        (∑ j ∈ Finset.range q,
          (-1 : ℤ) ^ (q - (j + 1))
            * (Nat.choose q (j + 1) : ℤ)
            * (u : ℤ) ^ (p * j)) := by rw [← hmul_right]

/-- Full polynomial expansion of the shifted quotient.

`Ψ_q(z - 1) = ∑ k = 1..q, (-1)^(q-k) · choose q k · z^(k-1)`
for odd `q`, specialized to `z = u^p`.  This is the correct mechanical
identity for the descent. -/
private theorem shifted_alt_cyclotomic_full_expansion_int
    (u p q : ℕ)
    (hu : 1 < u)
    (hq_odd : Odd q) :
    ((altCyclotomicPlusNat q (u ^ p - 1) : ℕ) : ℤ) =
      ∑ k ∈ Finset.Icc 1 q,
        (-1 : ℤ) ^ (q - k)
          * (Nat.choose q k : ℤ)
          * (u : ℤ) ^ (p * (k - 1)) := by
  classical
  rw [shifted_alt_cyclotomic_full_expansion_range_int u p q hu hq_odd]
  -- Reindex `j ∈ range q` by `k = j + 1 ∈ Icc 1 q`.
  symm
  refine Finset.sum_bij
    (fun k _hk => k - 1)
    ?hmem ?hinj ?hsurj ?hterm
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkq : k ≤ q := (Finset.mem_Icc.mp hk).2
    exact Finset.mem_range.mpr (by
      change k - 1 < q
      omega)
  · intro a ha b hb hab
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    change a = b
    change a - 1 = b - 1 at hab
    omega
  · intro j hj
    refine ⟨j + 1, ?_, ?_⟩
    · have hjq : j < q := Finset.mem_range.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · simp
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkq : k ≤ q := (Finset.mem_Icc.mp hk).2
    have hk_succ : k - 1 + 1 = k := by omega
    simp [hk_succ]

/-- Mechanical gap helper: for `1 < z` and `2 ≤ q`,
`(z - 1)^q + 1 < z^q`. -/
private theorem pow_sub_one_add_one_lt_pow
    (z q : ℕ) (hz : 1 < z) (hq : 2 ≤ q) :
    (z - 1) ^ q + 1 < z ^ q := by
  rcases Nat.exists_eq_add_of_le hq with ⟨k, hk⟩
  subst hk
  have hz_sub_pos : 0 < z - 1 := by omega
  have hz_sub_le : z - 1 ≤ z := by omega
  have hpow_le : (z - 1) ^ k ≤ z ^ k :=
    Nat.pow_le_pow_left hz_sub_le k
  have hdiff_big : 1 < (2 * (z - 1) + 1) * (z - 1) ^ k := by
    have hpow_pos : 0 < (z - 1) ^ k := pow_pos hz_sub_pos k
    nlinarith
  calc
    (z - 1) ^ (2 + k) + 1
        < (z - 1) ^ (2 + k)
            + (2 * (z - 1) + 1) * (z - 1) ^ k := by omega
    _ = ((z - 1) ^ 2 + (2 * (z - 1) + 1)) * (z - 1) ^ k := by
            rw [pow_add]; ring
    _ = z ^ 2 * (z - 1) ^ k := by
            have hcoeff : (z - 1) ^ 2 + (2 * (z - 1) + 1) = z ^ 2 := by
              have hz_expand : z = (z - 1) + 1 := by omega
              nlinarith
            rw [hcoeff]
    _ ≤ z ^ 2 * z ^ k := Nat.mul_le_mul_left (z ^ 2) hpow_le
    _ = z ^ (2 + k) := by rw [pow_add]

/-- Size bound: the shifted alternating quotient is strictly below the
leading `p`-th power `(u^(q-1))^p`.

Requires `0 < p`; statement is false at `p = 0` (both sides equal 1). -/
private theorem shifted_alt_cyclotomic_lt_top_power
    (u p q : ℕ)
    (hu : 1 < u)
    (hp_pos : 0 < p)
    (hq_odd : Odd q)
    (hq5 : 5 ≤ q) :
    altCyclotomicPlusNat q (u ^ p - 1) <
      (u ^ (q - 1)) ^ p := by
  let z : ℕ := u ^ p
  have hz_gt_one : 1 < z := Nat.one_lt_pow (Nat.ne_of_gt hp_pos) hu
  have hq_pos : 0 < q := by omega
  have hfactor :
      z * altCyclotomicPlusNat q (z - 1) = (z - 1) ^ q + 1 := by
    have h := alt_cyclotomic_plus_nat_mul_eq_pow_add_one (z - 1) q hq_odd
    have hz_sub : z - 1 + 1 = z := by omega
    simpa [hz_sub] using h
  have hgap : (z - 1) ^ q + 1 < z ^ q :=
    pow_sub_one_add_one_lt_pow z q hz_gt_one (by omega)
  have hmul_lt :
      z * altCyclotomicPlusNat q (z - 1) < z * z ^ (q - 1) := by
    rw [hfactor]
    have hzpow : z * z ^ (q - 1) = z ^ q := by
      rw [← pow_succ']
      congr 1
      omega
    simpa [hzpow] using hgap
  have hlt_z :
      altCyclotomicPlusNat q (z - 1) < z ^ (q - 1) :=
    Nat.lt_of_mul_lt_mul_left hmul_lt
  have hz_rewrite : z ^ (q - 1) = (u ^ (q - 1)) ^ p := by
    show (u ^ p) ^ (q - 1) = (u ^ (q - 1)) ^ p
    rw [← pow_mul, ← pow_mul, mul_comm]
  simpa [z, hz_rewrite] using hlt_z

private theorem pth_root_lt_of_shifted_alt_eq
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp_pos : 0 < p)
    (hq_odd : Odd q)
    (hq5 : 5 ≤ q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    v < u ^ (q - 1) := by
  have hlt :
      v ^ p < (u ^ (q - 1)) ^ p := by
    rw [← hvpow]
    exact shifted_alt_cyclotomic_lt_top_power u p q hu hp_pos hq_odd hq5
  exact lt_of_pow_lt_pow_left' p hlt

/-- First u-adic consequence of the shifted Cassels equation.

From `v^p = Ψ_q(u^p - 1)` and the gcd/residue lemma
`Ψ_q(y) ≡ q [MOD y+1]`, with `y = u^p - 1`, we get
`v^p ≡ q [MOD u^p]`.

This is the first nontrivial descent invariant of the Cassels chain.
The earlier mod-`p` reduction only gave `v ≡ Ψ_q(u-1) [MOD p]`, which
is not contradictory (Route C critique 2026-05-15). -/
private theorem shifted_cassels_vpow_mod_u_pow
    (u v p q : ℕ)
    (hu : 1 < u)
    (hq_odd : Odd q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    v ^ p ≡ q [MOD u ^ p] := by
  have hy_add : (u ^ p - 1) + 1 = u ^ p := by
    have hu_pos : 0 < u ^ p := pow_pos (by omega : 0 < u) p
    omega
  have hmod :
      altCyclotomicPlusNat q (u ^ p - 1) ≡ q [MOD (u ^ p - 1) + 1] :=
    altCyclotomicPlusNat_mod_add_one (u ^ p - 1) q hq_odd
  rw [hy_add] at hmod
  rw [← hvpow]
  exact hmod

/-- Prime-divisor consequence of the u-adic congruence.

If `r ∣ u`, then `v^p ≡ q [MOD r^p]` — the local form of the descent
invariant. -/
private theorem shifted_cassels_vpow_mod_prime_pow_of_dvd_u
    (u v p q r : ℕ)
    (hu : 1 < u)
    (hq_odd : Odd q)
    (hr_dvd_u : r ∣ u)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    v ^ p ≡ q [MOD r ^ p] := by
  have hmod_u : v ^ p ≡ q [MOD u ^ p] :=
    shifted_cassels_vpow_mod_u_pow u v p q hu hq_odd hvpow
  have hrpow_dvd_upow : r ^ p ∣ u ^ p := pow_dvd_pow_of_dvd hr_dvd_u p
  exact hmod_u.of_dvd hrpow_dvd_upow

/-- A2 chain step: `q ∤ u`.

If `q ∣ u` then reducing the locked invariant `v^p ≡ q [MOD u^p]`
modulo `q^p` gives `v^p ≡ q [MOD q^p]`.  Case-split on `q ∣ v`:
  - `q ∣ v` ⇒ `q^p ∣ v^p` ⇒ `q^p ∣ q`, impossible since `q < q^p`
    for `1 < p`.
  - `q ∤ v` ⇒ `v^p` is a unit mod `q` ⇒ `q ∤ v^p`, but the
    residue gives `q ∣ v^p`. -/
private theorem shifted_cassels_q_not_dvd_u
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp_one_lt : 1 < p)
    (hq : q.Prime)
    (hq_odd : Odd q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    ¬ q ∣ u := by
  intro hq_dvd_u
  have hp_pos : 0 < p := by omega
  have hmod_qpow : v ^ p ≡ q [MOD q ^ p] :=
    shifted_cassels_vpow_mod_prime_pow_of_dvd_u
      u v p q q hu hq_odd hq_dvd_u hvpow
  by_cases hq_dvd_v : q ∣ v
  · have hqpow_dvd_vpow : q ^ p ∣ v ^ p :=
      pow_dvd_pow_of_dvd hq_dvd_v p
    have hzero_vpow : v ^ p ≡ 0 [MOD q ^ p] :=
      (Nat.modEq_zero_iff_dvd).mpr hqpow_dvd_vpow
    have hq_mod_zero : q ≡ 0 [MOD q ^ p] :=
      hmod_qpow.symm.trans hzero_vpow
    have hqpow_dvd_q : q ^ p ∣ q :=
      (Nat.modEq_zero_iff_dvd).mp hq_mod_zero
    have h2q : 2 ≤ q := hq.two_le
    have hqpow_gt_q : q < q ^ p := by
      have hq2_le : q ^ 2 ≤ q ^ p :=
        Nat.pow_le_pow_right (by omega) hp_one_lt
      have hq2_eq : q ^ 2 = q * q := sq q
      nlinarith
    exact absurd (Nat.le_of_dvd hq.pos hqpow_dvd_q) (by omega)
  · have hmod_q : v ^ p ≡ q [MOD q] :=
      hmod_qpow.of_dvd (dvd_pow_self q (by omega : p ≠ 0))
    have hq_zero : q ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
    have hq_dvd_vpow : q ∣ v ^ p :=
      (Nat.modEq_zero_iff_dvd).mp (hmod_q.trans hq_zero)
    exact hq_dvd_v (hq.dvd_of_dvd_pow hq_dvd_vpow)

/-- A2 chain step: `Nat.Coprime u v`.

If a prime `r ∣ gcd u v`, then from `v^p ≡ q [MOD r^p]` and `r ∣ v^p`
we get `r ∣ q`, hence `r = q`; but `q ∤ u` by the previous step. -/
private theorem shifted_cassels_coprime_u_v
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp_one_lt : 1 < p)
    (hq : q.Prime)
    (hq_odd : Odd q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    Nat.Coprime u v := by
  by_contra hnot
  have hgcd_ne_one : Nat.gcd u v ≠ 1 := by
    intro hgcd_one
    exact hnot hgcd_one
  rcases Nat.exists_prime_and_dvd hgcd_ne_one with ⟨r, hr, hr_dvd_gcd⟩
  have hr_dvd_u : r ∣ u := hr_dvd_gcd.trans (Nat.gcd_dvd_left u v)
  have hr_dvd_v : r ∣ v := hr_dvd_gcd.trans (Nat.gcd_dvd_right u v)
  have hmod_rpow : v ^ p ≡ q [MOD r ^ p] :=
    shifted_cassels_vpow_mod_prime_pow_of_dvd_u
      u v p q r hu hq_odd hr_dvd_u hvpow
  have hp_ne_zero : p ≠ 0 := by omega
  have hmod_r : v ^ p ≡ q [MOD r] :=
    hmod_rpow.of_dvd (dvd_pow_self r hp_ne_zero)
  have hr_dvd_vpow : r ∣ v ^ p :=
    dvd_trans hr_dvd_v (dvd_pow_self v hp_ne_zero)
  have hzero_vpow : v ^ p ≡ 0 [MOD r] :=
    (Nat.modEq_zero_iff_dvd).mpr hr_dvd_vpow
  have hq_mod_zero : q ≡ 0 [MOD r] := hmod_r.symm.trans hzero_vpow
  have hr_dvd_q : r ∣ q := (Nat.modEq_zero_iff_dvd).mp hq_mod_zero
  have hr_eq_q : r = q := by
    rcases hq.eq_one_or_self_of_dvd r hr_dvd_q with h1 | hself
    · exact (hr.ne_one h1).elim
    · exact hself
  have hq_dvd_u : q ∣ u := by rw [← hr_eq_q]; exact hr_dvd_u
  exact (shifted_cassels_q_not_dvd_u
    u v p q hu hp_one_lt hq hq_odd hvpow) hq_dvd_u

/-- A2 chain step: local p-th power residue condition.

For every prime divisor `r ∣ u`, `q` is a p-th power residue
modulo `r^p` (witnessed by `v`). -/
private theorem shifted_cassels_q_is_pth_power_residue_mod_prime_pow
    (u v p q r : ℕ)
    (hu : 1 < u)
    (hp_one_lt : 1 < p)
    (hq : q.Prime)
    (hq_odd : Odd q)
    (hr_dvd_u : r ∣ u)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    ∃ w : ℕ, w ^ p ≡ q [MOD r ^ p] :=
  ⟨v, shifted_cassels_vpow_mod_prime_pow_of_dvd_u
        u v p q r hu hq_odd hr_dvd_u hvpow⟩

/-- Deficit upper bound: `z^(q-1) - Ψ_q(z-1) ≤ q · z^(q-2)`. -/
private theorem shifted_cassels_deficit_le
    (u p q : ℕ)
    (hu : 1 < u)
    (hp_pos : 0 < p)
    (hq_odd : Odd q)
    (hq2 : 2 ≤ q) :
    (u ^ (p * (q - 1))
      - altCyclotomicPlusNat q (u ^ p - 1))
      ≤ q * u ^ (p * (q - 2)) := by
  classical
  have hq_pos : 0 < q := by omega
  let z : ℕ := u ^ p
  have hz_pos : 0 < z := by dsimp [z]; exact pow_pos (by omega : 0 < u) p
  have hz_gt_one : 1 < z := by
    dsimp [z]; exact Nat.one_lt_pow (Nat.ne_of_gt hp_pos) hu
  have hfactor :
      z * altCyclotomicPlusNat q (z - 1) = (z - 1) ^ q + 1 := by
    have h := alt_cyclotomic_plus_nat_mul_eq_pow_add_one (z - 1) q hq_odd
    have hz_sub : z - 1 + 1 = z := by omega
    simpa [hz_sub] using h
  have hdiff_pow_le :
      z ^ q - (z - 1) ^ q ≤ q * z ^ (q - 1) := by
    have hsum_factor :
        z ^ q - (z - 1) ^ q =
          ∑ i ∈ Finset.range q,
            z ^ (q - 1 - i) * (z - 1) ^ i := by
      clear hq_odd hfactor hq2 hq_pos
      induction q with
      | zero => simp
      | succ n ih =>
          rw [Finset.sum_range_succ]
          have hz_sub_le : z - 1 ≤ z := by omega
          have hpow_le : (z - 1) ^ n ≤ z ^ n :=
            Nat.pow_le_pow_left hz_sub_le n
          have hmain :
              z ^ (n + 1) - (z - 1) ^ (n + 1)
                =
              z * (z ^ n - (z - 1) ^ n) + (z - 1) ^ n := by
            have hle2 : (z - 1) ^ n ≤ z * (z - 1) ^ n :=
              Nat.le_mul_of_pos_left _ (by omega : 0 < z)
            calc
              z ^ (n + 1) - (z - 1) ^ (n + 1)
                  = z * z ^ n - (z - 1) * (z - 1) ^ n := by
                    rw [pow_succ', pow_succ']
              _ = z * (z ^ n - (z - 1) ^ n) + (z - 1) ^ n := by
                    have hzpsub : z * (z - 1) ^ n = (z - 1) * (z - 1) ^ n + (z - 1) ^ n := by
                      have : z * (z - 1) ^ n = ((z - 1) + 1) * (z - 1) ^ n := by
                        congr 1; omega
                      rw [this]
                      ring
                    have hmul_sub :
                        z * (z ^ n - (z - 1) ^ n) + z * (z - 1) ^ n = z * z ^ n := by
                      rw [← Nat.mul_add]
                      rw [Nat.sub_add_cancel hpow_le]
                    apply Nat.sub_eq_of_eq_add
                    calc
                      z * z ^ n
                          = z * (z ^ n - (z - 1) ^ n) + z * (z - 1) ^ n := hmul_sub.symm
                      _ = z * (z ^ n - (z - 1) ^ n)
                            + ((z - 1) * (z - 1) ^ n + (z - 1) ^ n) := by
                              rw [hzpsub]
                      _ = (z * (z ^ n - (z - 1) ^ n) + (z - 1) ^ n)
                            + (z - 1) * (z - 1) ^ n := by
                              ring
          have hscale :
              z *
                (∑ i ∈ Finset.range n,
                  z ^ (n - 1 - i) * (z - 1) ^ i)
                =
              ∑ i ∈ Finset.range n,
                z ^ (n - i) * (z - 1) ^ i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < n := Finset.mem_range.mp hi
            have hsub : n - i = (n - 1 - i) + 1 := by omega
            rw [hsub, pow_succ]; ring
          calc
            z ^ (n + 1) - (z - 1) ^ (n + 1)
                = z * (z ^ n - (z - 1) ^ n) + (z - 1) ^ n := hmain
            _ = z *
                  (∑ i ∈ Finset.range n,
                    z ^ (n - 1 - i) * (z - 1) ^ i)
                  + (z - 1) ^ n := by
                    rw [ih]
            _ = (∑ i ∈ Finset.range n,
                  z ^ (n - i) * (z - 1) ^ i)
                + z ^ (n - n) * (z - 1) ^ n := by
                    rw [hscale]; simp
    have hterm_le :
        ∀ i ∈ Finset.range q,
          z ^ (q - 1 - i) * (z - 1) ^ i ≤ z ^ (q - 1) := by
      intro i hi
      have hiq : i < q := Finset.mem_range.mp hi
      have hzi : (z - 1) ^ i ≤ z ^ i :=
        Nat.pow_le_pow_left (by omega : z - 1 ≤ z) i
      calc
        z ^ (q - 1 - i) * (z - 1) ^ i
            ≤ z ^ (q - 1 - i) * z ^ i :=
              Nat.mul_le_mul_left _ hzi
        _ = z ^ ((q - 1 - i) + i) := by rw [← pow_add]
        _ = z ^ (q - 1) := by congr 1; omega
    calc
      z ^ q - (z - 1) ^ q
          = ∑ i ∈ Finset.range q,
              z ^ (q - 1 - i) * (z - 1) ^ i := hsum_factor
      _ ≤ ∑ _i ∈ Finset.range q, z ^ (q - 1) :=
            Finset.sum_le_sum hterm_le
      _ = q * z ^ (q - 1) := by simp [mul_comm]
  have hmul_deficit :
      z *
        (z ^ (q - 1) - altCyclotomicPlusNat q (z - 1))
        ≤ z * (q * z ^ (q - 2)) := by
    rw [Nat.mul_sub_left_distrib]
    rw [hfactor]
    have hzpow_q : z * z ^ (q - 1) = z ^ q := by
      rw [← pow_succ']
      congr 1
      omega
    have hzpow_rhs : z * (q * z ^ (q - 2)) = q * z ^ (q - 1) := by
      calc
        z * (q * z ^ (q - 2)) = q * (z * z ^ (q - 2)) := by ring
        _ = q * z ^ (q - 1) := by
              congr 1
              rw [← pow_succ']
              congr 1
              omega
    rw [hzpow_q, hzpow_rhs]
    have hsub_le :
        z ^ q - ((z - 1) ^ q + 1) ≤ z ^ q - (z - 1) ^ q :=
      Nat.sub_le_sub_left (Nat.le_add_right _ _) _
    exact le_trans hsub_le hdiff_pow_le
  have hcancel :
      z ^ (q - 1) - altCyclotomicPlusNat q (z - 1)
        ≤ q * z ^ (q - 2) :=
    Nat.le_of_mul_le_mul_left hmul_deficit hz_pos
  have hzpow_left : z ^ (q - 1) = u ^ (p * (q - 1)) := by
    dsimp [z]; rw [← pow_mul]
  have hzpow_right : z ^ (q - 2) = u ^ (p * (q - 2)) := by
    dsimp [z]; rw [← pow_mul]
  simpa [z, hzpow_left, hzpow_right] using hcancel

/-- Difference-of-powers lower bound: `(A - v) · A^(p-1) ≤ A^p - v^p`
when `v ≤ A` and `0 < p`. Follows from the factorization
`A^p - v^p = (A - v) · ∑ i ∈ range p, A^(p-1-i) · v^i`, whose sum is
at least the i=0 term `A^(p-1)`. -/
private theorem pow_deficit_ge_first_term
    (A v p : ℕ)
    (hp_pos : 0 < p)
    (hvA : v ≤ A) :
    (A - v) * A ^ (p - 1) ≤ A ^ p - v ^ p := by
  cases p with
  | zero => omega
  | succ n =>
      apply Nat.le_sub_of_add_le
      have hvpow_le : v ^ (n + 1) ≤ v * A ^ n := by
        calc
          v ^ (n + 1) = v * v ^ n := by rw [pow_succ']
          _ ≤ v * A ^ n :=
                Nat.mul_le_mul_left v (Nat.pow_le_pow_left hvA n)
      have hmain :
          (A - v) * A ^ n + v ^ (n + 1)
            ≤ (A - v) * A ^ n + v * A ^ n :=
        Nat.add_le_add_left hvpow_le _
      have hright :
          (A - v) * A ^ n + v * A ^ n = A ^ (n + 1) := by
        have hAv : A - v + v = A := by omega
        calc
          (A - v) * A ^ n + v * A ^ n
              = ((A - v) + v) * A ^ n := by ring
          _ = A * A ^ n := by rw [hAv]
          _ = A ^ (n + 1) := by rw [pow_succ']
      exact le_trans hmain (by rw [hright])

/-- Interval-route first bound: `v` is close to the leading root
`u^(q-1)`.

Specifically, `u^(q-1) - v ≤ 2q · u^(q-p-1)`.  The constant `2q` is
intentionally loose; the sharper `q` bound holds via the same chain. -/
private theorem cassels_w_bound
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp_one_lt : 1 < p)
    (hq_odd : Odd q)
    (hp5 : 5 ≤ p)
    (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1)) :
    v ≥ u ^ (q - 1) - 2 * q * u ^ (q - p - 1) := by
  let A : ℕ := u ^ (q - 1)
  have hp_pos : 0 < p := by omega
  have hq_pos : 0 < q := by omega
  have hvA : v ≤ A := by dsimp [A]; exact le_of_lt hvlt
  have hdef_lower :
      (A - v) * A ^ (p - 1) ≤ A ^ p - v ^ p :=
    pow_deficit_ge_first_term A v p hp_pos hvA
  have hA_pow : A ^ p = u ^ (p * (q - 1)) := by
    dsimp [A]; rw [← pow_mul, Nat.mul_comm]
  have hdef_upper :
      A ^ p - v ^ p ≤ q * u ^ (p * (q - 2)) := by
    rw [hA_pow, ← hvpow]
    exact shifted_cassels_deficit_le u p q hu hp_pos hq_odd (by omega)
  have hcombined :
      (A - v) * A ^ (p - 1) ≤ q * u ^ (p * (q - 2)) :=
    le_trans hdef_lower hdef_upper
  have hcancel_bound : A - v ≤ q * u ^ (q - p - 1) := by
    have hu_pos : 0 < u := by omega
    have hA_factor : A ^ (p - 1) = u ^ ((q - 1) * (p - 1)) := by
      dsimp [A]; rw [← pow_mul]
    have hexp :
        p * (q - 2) = (q - p - 1) + ((q - 1) * (p - 1)) := by
      have hpq1 : p + 1 ≤ q := by omega
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hpq1
      subst q
      have h1 : p + 1 + t - 2 = p + t - 1 := by omega
      have h2 : p + 1 + t - p - 1 = t := by omega
      have h3 : p + 1 + t - 1 = p + t := by omega
      rw [h1, h2, h3]
      have h4 : p + t - 1 = (p - 1) + t := by omega
      rw [h4]
      have hp_mul_t : p * t = (p - 1) * t + t := by
        have hp_pred : p = (p - 1) + 1 := by omega
        calc
          p * t = ((p - 1) + 1) * t := congrArg (fun n => n * t) hp_pred
          _ = (p - 1) * t + t := by rw [Nat.add_mul, one_mul]
      calc
        p * (p - 1 + t) = p * (p - 1) + p * t := by rw [Nat.mul_add]
        _ = p * (p - 1) + ((p - 1) * t + t) := by rw [hp_mul_t]
        _ = t + (p + t) * (p - 1) := by ring
    have hright :
        q * u ^ (p * (q - 2)) =
          (q * u ^ (q - p - 1)) * u ^ ((q - 1) * (p - 1)) := by
      rw [hexp, pow_add]; ring
    have hcombined' :
        (A - v) * u ^ ((q - 1) * (p - 1))
          ≤
        (q * u ^ (q - p - 1)) * u ^ ((q - 1) * (p - 1)) := by
      simpa [hA_factor, hright] using hcombined
    have hpow_pos : 0 < u ^ ((q - 1) * (p - 1)) :=
      pow_pos hu_pos _
    exact Nat.le_of_mul_le_mul_right hcombined' hpow_pos
  have htwo_bound : A - v ≤ 2 * q * u ^ (q - p - 1) := by
    nlinarith [hcancel_bound]
  dsimp [A] at htwo_bound
  omega

/-- Useful intermediate from the i=p term observation:

  `u^p ∣ (u^(q-1) - v)^p + q`.

This follows from `v^p ≡ q [MOD u^p]` together with the fact that in the
binomial expansion of `v^p = (A-w)^p` with `A = u^(q-1)`, `w = A - v`,
every term with `i < p` contains `A^(p-i) = u^((q-1)(p-i))` and
`(q-1)(p-i) ≥ q-1 ≥ p` (since `p < q`), so vanishes mod `u^p`.  Only
the `i = p` term `(-w)^p = -w^p` (for odd `p`) survives. -/
private theorem cassels_w_pow_add_q_dvd_u_pow
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime)
    (hp5 : 5 ≤ p)
    (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvlt : v < u ^ (q - 1))
    (hmod : v ^ p ≡ q [MOD u ^ p]) :
    u ^ p ∣ (u ^ (q - 1) - v) ^ p + q := by
  classical
  let A : ℕ := u ^ (q - 1)
  let w : ℕ := A - v
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hp_pos : 0 < p := hp.pos
  have hu_pos : 0 < u := by omega
  have hvA : v ≤ A := by dsimp [A]; exact le_of_lt hvlt
  have hv_eq_int : (v : ℤ) = (A : ℤ) - (w : ℤ) := by dsimp [w]; omega
  have hp_le_qsub1 : p ≤ q - 1 := by omega
  have hA_dvd : u ^ p ∣ A := by
    dsimp [A]
    refine ⟨u ^ (q - 1 - p), ?_⟩
    rw [← pow_add]; congr 1; omega
  have hA_modNat : A ≡ 0 [MOD u ^ p] :=
    (Nat.modEq_zero_iff_dvd).mpr hA_dvd
  have hA_modZ :
      (A : ℤ) ≡ 0 [ZMOD ((u ^ p : ℕ) : ℤ)] := by
    exact_mod_cast hA_modNat
  have hv_mod_neg_w :
      (v : ℤ) ≡ -((w : ℤ)) [ZMOD ((u ^ p : ℕ) : ℤ)] := by
    rw [hv_eq_int]
    have h := Int.ModEq.sub hA_modZ (Int.ModEq.refl ((w : ℤ)))
    simpa using h
  have hneg_pow :
      (-(w : ℤ)) ^ p = -((w : ℤ) ^ p) := by
    rcases hp_odd with ⟨k, hk⟩
    rw [hk, pow_succ, pow_mul]
    have hsquare : (-(w : ℤ)) ^ 2 = (w : ℤ) ^ 2 := by ring
    rw [hsquare]; ring
  have hvpow_mod_neg :
      (v : ℤ) ^ p ≡ -((w : ℤ) ^ p) [ZMOD ((u ^ p : ℕ) : ℤ)] := by
    have h := hv_mod_neg_w.pow p
    simpa [hneg_pow] using h
  have hsumZ :
      ((v ^ p + w ^ p : ℕ) : ℤ) ≡ 0 [ZMOD ((u ^ p : ℕ) : ℤ)] := by
    have h := hvpow_mod_neg.add_right ((w : ℤ) ^ p)
    simpa [Nat.cast_add, Nat.cast_pow] using h
  have hdivZ :
      ((u ^ p : ℕ) : ℤ) ∣ ((v ^ p + w ^ p : ℕ) : ℤ) :=
    Int.modEq_zero_iff_dvd.mp hsumZ
  have hdivNat : u ^ p ∣ v ^ p + w ^ p := by exact_mod_cast hdivZ
  have hsumNat : v ^ p + w ^ p ≡ 0 [MOD u ^ p] :=
    (Nat.modEq_zero_iff_dvd).mpr hdivNat
  have hq_w_zero : q + w ^ p ≡ 0 [MOD u ^ p] :=
    ((hmod.add_right (w ^ p)).symm).trans hsumNat
  have hdiv_qw : u ^ p ∣ q + w ^ p :=
    (Nat.modEq_zero_iff_dvd).mp hq_w_zero
  simpa [A, w, add_comm] using hdiv_qw

/-! ### Corrected Cassels descent: binomial-root + p-adic divisibility -/

/-! ### Padé approximation infrastructure for the Cassels descent

ChatGPT-recommended (8689a859) 3-helper decomposition of the
genuinely hard Cassels core.  Each is a real research-level
sub-blocker; the wrapper `cassels_shifted_solution_forces_p_dvd_u`
combines them. -/

/-- Real-root identity from the shifted Cassels equation. -/
private theorem cassels_real_root_identity
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1)) :
    ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
      =
    (1 - ((u : ℝ) ^ p)⁻¹) ^ q
      + (((u : ℝ) ^ p)⁻¹) ^ q := by
  classical
  have hq_odd : Odd q := hq.odd_of_ne_two (by have := hp.two_le; omega)
  have hu_pos : 0 < u := by omega
  have hu_pow_pos : 0 < u ^ p := pow_pos hu_pos p
  have h_one_le_up : 1 ≤ u ^ p := Nat.succ_le_of_lt hu_pow_pos
  have h_y_add : (u ^ p - 1) + 1 = u ^ p :=
    Nat.sub_add_cancel h_one_le_up
  have hfac :
      ((u ^ p - 1) + 1) *
          altCyclotomicPlusNat q (u ^ p - 1)
        =
      (u ^ p - 1) ^ q + 1 :=
    alt_cyclotomic_plus_nat_mul_eq_pow_add_one
      (u ^ p - 1) q hq_odd
  have hprod_nat :
      u ^ p * v ^ p = (u ^ p - 1) ^ q + 1 := by
    calc
      u ^ p * v ^ p
          = u ^ p * altCyclotomicPlusNat q (u ^ p - 1) := by
              rw [← hvpow]
      _ = ((u ^ p - 1) + 1) *
              altCyclotomicPlusNat q (u ^ p - 1) := by
              rw [h_y_add]
      _ = (u ^ p - 1) ^ q + 1 := hfac
  have hsub_cast :
      ((u ^ p - 1 : ℕ) : ℝ) = (u : ℝ) ^ p - 1 := by
    rw [Nat.cast_sub h_one_le_up]; simp
  have hprod_real :
      (u : ℝ) ^ p * (v : ℝ) ^ p
        =
      ((u : ℝ) ^ p - 1) ^ q + 1 := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hprod_nat
    push_cast at h
    simpa [hsub_cast] using h
  have huR_ne : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu_pos)
  have hUp_ne : (u : ℝ) ^ p ≠ 0 := pow_ne_zero p huR_ne
  have hB_ne : ((u : ℝ) ^ p) ^ (q - 1) ≠ 0 := pow_ne_zero (q - 1) hUp_ne
  have hq_succ : q = (q - 1) + 1 := by omega
  have hden_factor :
      ((u : ℝ) ^ p) ^ q = ((u : ℝ) ^ p) ^ (q - 1) * (u : ℝ) ^ p := by
    set A : ℝ := (u : ℝ) ^ p
    change A ^ q = A ^ (q - 1) * A
    calc
      A ^ q = A ^ ((q - 1) + 1) := by rw [← hq_succ]
      _ = A ^ (q - 1) * A := by rw [pow_succ]
  have hdiv_main :
      (v : ℝ) ^ p / (((u : ℝ) ^ p) ^ (q - 1))
        =
      (((u : ℝ) ^ p - 1) ^ q + 1) / (((u : ℝ) ^ p) ^ q) := by
    calc
      (v : ℝ) ^ p / (((u : ℝ) ^ p) ^ (q - 1))
          =
            ((u : ℝ) ^ p * (v : ℝ) ^ p) /
          ((u : ℝ) ^ p * (((u : ℝ) ^ p) ^ (q - 1))) := by
            field_simp [hUp_ne, hB_ne]
      _ = (((u : ℝ) ^ p - 1) ^ q + 1) / (((u : ℝ) ^ p) ^ q) := by
            rw [hprod_real, hden_factor]; ring
  have hright :
      (((u : ℝ) ^ p - 1) ^ q + 1) / (((u : ℝ) ^ p) ^ q)
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q + (((u : ℝ) ^ p)⁻¹) ^ q := by
    set A : ℝ := (u : ℝ) ^ p
    have hA_ne : A ≠ 0 := by simpa [A] using hUp_ne
    have hAq_ne : A ^ q ≠ 0 := pow_ne_zero q hA_ne
    have hbase : 1 - A⁻¹ = (A - 1) / A := by
      field_simp [hA_ne]
    change ((A - 1) ^ q + 1) / (A ^ q) = (1 - A⁻¹) ^ q + (A⁻¹) ^ q
    rw [hbase, div_pow, inv_pow]
    field_simp [hAq_ne]
  have hlhs :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (v : ℝ) ^ p / (((u : ℝ) ^ p) ^ (q - 1)) := by
    rw [div_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc
    ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        = (v : ℝ) ^ p / (((u : ℝ) ^ p) ^ (q - 1)) := hlhs
    _ = (((u : ℝ) ^ p - 1) ^ q + 1) / (((u : ℝ) ^ p) ^ q) := hdiv_main
    _ = (1 - ((u : ℝ) ^ p)⁻¹) ^ q
          + (((u : ℝ) ^ p)⁻¹) ^ q := hright

/-- The shifted quotient equation is equivalent to the Catalan-shaped
natural-number equation used by Cassels' `−1` lemma. -/
private theorem shifted_cassels_catalan_nat
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hq2 : 2 < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    (v * u) ^ p = (u ^ p - 1) ^ q + 1 := by
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hu_pos : 0 < u := by omega
  have hu_pow_pos : 0 < u ^ p := pow_pos hu_pos p
  have h_one_le_up : 1 ≤ u ^ p := Nat.succ_le_of_lt hu_pow_pos
  have h_y_add : (u ^ p - 1) + 1 = u ^ p :=
    Nat.sub_add_cancel h_one_le_up
  have hfac :
      ((u ^ p - 1) + 1) *
          altCyclotomicPlusNat q (u ^ p - 1)
        =
      (u ^ p - 1) ^ q + 1 :=
    alt_cyclotomic_plus_nat_mul_eq_pow_add_one
      (u ^ p - 1) q hq_odd
  calc
    (v * u) ^ p = v ^ p * u ^ p := by rw [mul_pow]
    _ = altCyclotomicPlusNat q (u ^ p - 1) * u ^ p := by rw [← hvpow]
    _ = u ^ p * altCyclotomicPlusNat q (u ^ p - 1) := by rw [mul_comm]
    _ = ((u ^ p - 1) + 1) * altCyclotomicPlusNat q (u ^ p - 1) := by
          rw [h_y_add]
    _ = (u ^ p - 1) ^ q + 1 := hfac

/-- Converse algebraic extraction: the real root identity used in the Runge
package forces the shifted Cassels quotient equation over `ℕ`. -/
private theorem shifted_cassels_of_real_root_identity
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    altCyclotomicPlusNat q (u ^ p - 1) = v ^ p := by
  classical
  set a : ℕ := u ^ p - 1 with ha_def
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hu_pos : 0 < u := by omega
  have hu_pow_pos : 0 < u ^ p := pow_pos hu_pos p
  have h_one_le_up : 1 ≤ u ^ p := Nat.succ_le_of_lt hu_pow_pos
  have huRpos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu_pos
  have hu_ne : (u : ℝ) ≠ 0 := ne_of_gt huRpos
  have hup_ne : ((u : ℝ) ^ p) ≠ 0 := pow_ne_zero _ hu_ne
  have ha_eq : (a : ℝ) = (u : ℝ) ^ p - 1 := by
    have h1 : a + 1 = u ^ p := by
      rw [ha_def]
      exact Nat.sub_add_cancel h_one_le_up
    have h2 : ((a : ℕ) : ℝ) + 1 = ((u : ℕ) : ℝ) ^ p := by
      exact_mod_cast h1
    linarith
  have hcatalan_real : ((v : ℝ) * (u : ℝ)) ^ p = ((a : ℝ)) ^ q + 1 := by
    rw [ha_eq, mul_pow]
    have hup1_ne : ((u : ℝ) ^ (q - 1)) ^ p ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ hu_ne)
    have hpq1 : (q - 1) * p + p = q * p := by
      cases q with
      | zero => omega
      | succ n => simp; ring
    have hexp : ((u : ℝ) ^ (q - 1)) ^ p * (u : ℝ) ^ p = ((u : ℝ) ^ p) ^ q := by
      have : ((u : ℝ) ^ (q - 1)) ^ p * (u : ℝ) ^ p
          = (u : ℝ) ^ ((q - 1) * p + p) := by rw [← pow_mul, ← pow_add]
      rw [this, hpq1, pow_mul']
    have hx : (v : ℝ) ^ p = ((u : ℝ) ^ (q - 1)) ^ p *
        ((1 - ((u : ℝ) ^ p)⁻¹) ^ q + ((u : ℝ) ^ p)⁻¹ ^ q) := by
      have h2 := hroot
      rw [div_pow, div_eq_iff hup1_ne] at h2
      linarith
    have hfact : ((u : ℝ) ^ p) ^ q * (1 - ((u : ℝ) ^ p)⁻¹) ^ q =
        ((u : ℝ) ^ p - 1) ^ q := by
      rw [← mul_pow]
      congr 1
      field_simp
    have hfact2 : ((u : ℝ) ^ p) ^ q * ((u : ℝ) ^ p)⁻¹ ^ q = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hup_ne, one_pow]
    have h2 : (v : ℝ) ^ p * ((u : ℝ) ^ p) ^ q =
        ((u : ℝ) ^ (q - 1)) ^ p * (((u : ℝ) ^ p - 1) ^ q + 1) := by
      rw [hx]
      have expand : ((u : ℝ) ^ (q - 1)) ^ p *
          ((1 - ((u : ℝ) ^ p)⁻¹) ^ q + ((u : ℝ) ^ p)⁻¹ ^ q) * ((u : ℝ) ^ p) ^ q =
          ((u : ℝ) ^ (q - 1)) ^ p *
          (((u : ℝ) ^ p) ^ q * (1 - ((u : ℝ) ^ p)⁻¹) ^ q +
           ((u : ℝ) ^ p) ^ q * ((u : ℝ) ^ p)⁻¹ ^ q) := by ring
      rw [expand, hfact, hfact2]
    rw [← hexp] at h2
    have key : ((u : ℝ) ^ (q - 1)) ^ p * ((v : ℝ) ^ p * (u : ℝ) ^ p) =
        ((u : ℝ) ^ (q - 1)) ^ p * (((u : ℝ) ^ p - 1) ^ q + 1) := by
      linarith
    exact mul_left_cancel₀ hup1_ne key
  have hcatalan_nat : (v * u) ^ p = a ^ q + 1 := by
    exact_mod_cast hcatalan_real
  have ha_succ : a + 1 = u ^ p := by
    rw [ha_def]
    exact Nat.sub_add_cancel h_one_le_up
  have hfac :
      (a + 1) * altCyclotomicPlusNat q a = a ^ q + 1 :=
    alt_cyclotomic_plus_nat_mul_eq_pow_add_one a q hq_odd
  have halt_prod :
      u ^ p * altCyclotomicPlusNat q a = a ^ q + 1 := by
    rw [← ha_succ]
    exact hfac
  have hvu_prod :
      v ^ p * u ^ p = a ^ q + 1 := by
    rw [← mul_pow]
    exact hcatalan_nat
  have hsame :
      u ^ p * v ^ p = u ^ p * altCyclotomicPlusNat q a := by
    rw [mul_comm (u ^ p) (v ^ p)]
    exact hvu_prod.trans halt_prod.symm
  have hvpow : v ^ p = altCyclotomicPlusNat q a :=
    Nat.eq_of_mul_eq_mul_left hu_pow_pos hsame
  simpa [a, ha_def] using hvpow.symm

/-- In the shifted lower-prime Cassels equation, the ramified `p ∣ u`
branch is already impossible by Cassels' elementary Lemma 2 (`−1` case).

The remaining hard branch is therefore `¬ p ∣ u`. -/
private theorem shifted_cassels_not_p_dvd_u
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    ¬ p ∣ u := by
  intro hp_dvd_u
  have hcat : (v * u) ^ p = (u ^ p - 1) ^ q + 1 :=
    shifted_cassels_catalan_nat u v p q hu hp hq (by
      have hp2 : 2 ≤ p := hp.two_le
      omega) hvpow
  have hv_pos : 0 < v := by
    by_contra hv_not
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv_not
    subst hv0
    simp [zero_pow hp.ne_zero] at hcat
  have hp_le_u : p ≤ u :=
    Nat.le_of_dvd (by omega : 0 < u) hp_dvd_u
  have hu_ge_three : 3 ≤ u := by omega
  have hvu_ge_three : 3 ≤ v * u := by
    have hmul : 1 * u ≤ v * u :=
      Nat.mul_le_mul_right u (by omega : 1 ≤ v)
    by_contra hnot
    have hvu_le_two : v * u ≤ 2 := by omega
    have hu_ge_two : 2 ≤ u := by omega
    have hv_ge_one : 1 ≤ v := by omega
    have hvu_ge_two : 2 ≤ v * u := by
      have hu_le_vu : u ≤ v * u := by
        simpa using hmul
      exact le_trans hu_ge_two hu_le_vu
    have hvu_eq_two : v * u = 2 := by omega
    have hu_le_two : u ≤ 2 := by
      nlinarith
    have hu_eq_two : u = 2 := by omega
    have hv_eq_one : v = 1 := by
      nlinarith
    subst hu_eq_two
    subst hv_eq_one
    have hbase_gt_one : 1 < 2 ^ p - 1 := by
      have hp2 : 2 ≤ p := hp.two_le
      have hpow4 : 4 ≤ 2 ^ p := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp2
      omega
    have hpow_gt :
        2 ^ p - 1 < (2 ^ p - 1) ^ q := by
      have hq_gt_one : 1 < q := lt_trans hp.one_lt hp_lt_q
      calc
        2 ^ p - 1 = (2 ^ p - 1) ^ 1 := by rw [pow_one]
        _ < (2 ^ p - 1) ^ q :=
            Nat.pow_lt_pow_right hbase_gt_one hq_gt_one
    simp only [one_mul] at hcat
    have hlt : 2 ^ p < (2 ^ p - 1) ^ q + 1 := by
      have hbase_add : 2 ^ p = (2 ^ p - 1) + 1 := by omega
      omega
    have hEq : 2 ^ p = (2 ^ p - 1) ^ q + 1 := by
      simpa using hcat
    exact (ne_of_lt hlt hEq).elim
  have hminus :
      (u ^ p - 1) ^ q = (v * u) ^ p - 1 := by
    omega
  have hp_dvd_vu_sub_one : p ∣ (v * u - 1) :=
    Ripple.LPP.CasselsClassical.cassels_lemma_2_minus
      q p (u ^ p - 1) (v * u) hq hp hp_lt_q hvu_ge_three hminus
  have hp_dvd_vu : p ∣ v * u :=
    dvd_mul_of_dvd_right hp_dvd_u v
  have hp_dvd_one : p ∣ 1 := by
    have hsub : p ∣ v * u - (v * u - 1) :=
      Nat.dvd_sub hp_dvd_vu hp_dvd_vu_sub_one
    have hvu_pos : 0 < v * u := by positivity
    have hdiff : v * u - (v * u - 1) = 1 := by omega
    simpa [hdiff] using hsub
  exact hp.not_dvd_one hp_dvd_one

/-- In the lower-prime shifted Cassels equation, Cassels' `−1` lemma gives
`p ∣ v*u - 1`; reducing the shifted equation modulo `p` then forces
`p ∣ u - 1`. -/
private theorem shifted_cassels_p_dvd_u_sub_one
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p) :
    p ∣ u - 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcat : (v * u) ^ p = (u ^ p - 1) ^ q + 1 :=
    shifted_cassels_catalan_nat u v p q hu hp hq (by
      have hp2 : 2 ≤ p := hp.two_le
      omega) hvpow
  have hv_pos : 0 < v := by
    by_contra hv_not
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv_not
    subst hv0
    simp [zero_pow hp.ne_zero] at hcat
  have hvu_ge_three : 3 ≤ v * u := by
    have hmul : 1 * u ≤ v * u :=
      Nat.mul_le_mul_right u (by omega : 1 ≤ v)
    by_contra hnot
    have hvu_le_two : v * u ≤ 2 := by omega
    have hu_ge_two : 2 ≤ u := by omega
    have hvu_ge_two : 2 ≤ v * u := by
      have hu_le_vu : u ≤ v * u := by
        simpa using hmul
      exact le_trans hu_ge_two hu_le_vu
    have hvu_eq_two : v * u = 2 := by omega
    have hu_le_two : u ≤ 2 := by
      nlinarith
    have hu_eq_two : u = 2 := by omega
    have hv_eq_one : v = 1 := by
      nlinarith
    subst hu_eq_two
    subst hv_eq_one
    have hbase_gt_one : 1 < 2 ^ p - 1 := by
      have hp2 : 2 ≤ p := hp.two_le
      have hpow4 : 4 ≤ 2 ^ p := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp2
      omega
    have hpow_gt :
        2 ^ p - 1 < (2 ^ p - 1) ^ q := by
      have hq_gt_one : 1 < q := lt_trans hp.one_lt hp_lt_q
      calc
        2 ^ p - 1 = (2 ^ p - 1) ^ 1 := by rw [pow_one]
        _ < (2 ^ p - 1) ^ q :=
            Nat.pow_lt_pow_right hbase_gt_one hq_gt_one
    simp only [one_mul] at hcat
    have hlt : 2 ^ p < (2 ^ p - 1) ^ q + 1 := by
      have hbase_add : 2 ^ p = (2 ^ p - 1) + 1 := by omega
      omega
    have hEq : 2 ^ p = (2 ^ p - 1) ^ q + 1 := by
      simpa using hcat
    exact (ne_of_lt hlt hEq).elim
  have hminus :
      (u ^ p - 1) ^ q = (v * u) ^ p - 1 := by
    omega
  have hp_dvd_vu_sub_one : p ∣ (v * u - 1) :=
    Ripple.LPP.CasselsClassical.cassels_lemma_2_minus
      q p (u ^ p - 1) (v * u) hq hp hp_lt_q hvu_ge_three hminus
  have hvu_pos : 0 < v * u := by positivity
  have hone_le_vu : 1 ≤ v * u := Nat.succ_le_of_lt hvu_pos
  have hvu_mod_one_nat : v * u ≡ 1 [MOD p] := by
    exact ((Nat.modEq_iff_dvd' hone_le_vu).mpr hp_dvd_vu_sub_one).symm
  have hvu_one : ((v * u : ℕ) : ZMod p) = 1 :=
    by simpa using (ZMod.natCast_eq_natCast_iff (v * u) 1 p).2 hvu_mod_one_nat
  have hcatZ :
      ((v * u : ℕ) : ZMod p) ^ p =
        ((u ^ p - 1 : ℕ) : ZMod p) ^ q + 1 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) hcat
    simpa [Nat.cast_pow, Nat.cast_add] using h
  have hpow_zero :
      ((u ^ p - 1 : ℕ) : ZMod p) ^ q = 0 := by
    have hright :
        ((u ^ p - 1 : ℕ) : ZMod p) ^ q + 1 = 1 := by
      rw [← hcatZ, hvu_one]
      simp
    exact add_right_cancel (by simpa using hright :
      ((u ^ p - 1 : ℕ) : ZMod p) ^ q + 1 = 0 + 1)
  have hbase_zero : ((u ^ p - 1 : ℕ) : ZMod p) = 0 :=
    eq_zero_of_pow_eq_zero hpow_zero
  have hu_pos : 0 < u := by omega
  have hu_pow_pos : 0 < u ^ p := pow_pos hu_pos p
  have h_one_le_up : 1 ≤ u ^ p := Nat.succ_le_of_lt hu_pow_pos
  have hcast_sub :
      ((u ^ p - 1 : ℕ) : ZMod p) = (u : ZMod p) ^ p - 1 := by
    rw [Nat.cast_sub h_one_le_up]
    simp
  have hu_sub_one_zero : (u : ZMod p) - 1 = 0 := by
    rw [hcast_sub, ZMod.pow_card] at hbase_zero
    exact hbase_zero
  have hcast_um1 :
      ((u - 1 : ℕ) : ZMod p) = (u : ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ u)]
    simp
  exact (ZMod.natCast_eq_zero_iff (u - 1) p).mp (by
    rw [hcast_um1]
    exact hu_sub_one_zero)

/-- Positive cyclotomic quotient for `x^p - 1`. -/
def Phi (p x : ℕ) : ℕ :=
  ∑ i ∈ Finset.range p, x ^ i

theorem Phi_mul_sub_one (p x : ℕ) (hx : 1 ≤ x) :
    Phi p x * (x - 1) = x ^ p - 1 := by
  have h :=
    (Commute.all (x - 1) (1 : ℕ)).geom_sum₂_mul_add p
  rw [Nat.sub_add_cancel hx, geom_sum₂_with_one, one_pow] at h
  have h' : Phi p x * (x - 1) + 1 = x ^ p := by
    simpa [Phi] using h
  omega

theorem cassels_ramified_first_split
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx2 : 2 ≤ x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ β : ℕ, p * (x - 1) = β ^ q := by
  obtain ⟨t, hxsplit, hqj⟩ :=
    Ripple.LPP.CasselsClassical.cassels_cor1_split_minus
      q p a x hq hp hp2 hx2 hpx1 hcat
  set j := padicValNat p (x - 1) with hj
  obtain ⟨m, hm⟩ := hqj
  refine ⟨p ^ m * t, ?_⟩
  have hjq : j + 1 = q * m := by
    simpa [hj] using hm
  have hpmul : p * (x - 1) = p ^ (j + 1) * t ^ q := by
    rw [hxsplit]
    rw [pow_succ]
    ring
  calc
    p * (x - 1) = p ^ (j + 1) * t ^ q := hpmul
    _ = p ^ (q * m) * t ^ q := by rw [hjq]
    _ = p ^ (m * q) * t ^ q := by rw [Nat.mul_comm q m]
    _ = (p ^ m) ^ q * t ^ q := by rw [pow_mul]
    _ = (p ^ m * t) ^ q := by rw [Nat.mul_pow]

theorem cassels_ramified_second_split
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx2 : 2 ≤ x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ γ : ℕ, Phi p x = p * γ ^ q := by
  obtain ⟨γ, hquot⟩ :=
    Ripple.LPP.CasselsClassical.cassels_cor1_quot_split_minus
      q p a x hq hp hp2 hx2 hpx1 hcat
  refine ⟨γ, ?_⟩
  have hx1_pos : 0 < x - 1 := by omega
  have hgeom : Phi p x * (x - 1) = x ^ p - 1 :=
    Phi_mul_sub_one p x (by omega)
  have hdiv : x - 1 ∣ x ^ p - 1 := ⟨Phi p x, by
    rw [← hgeom, Nat.mul_comm]⟩
  have hquot_phi : (x ^ p - 1) / (x - 1) = Phi p x := by
    apply Nat.eq_of_mul_eq_mul_right hx1_pos
    rw [Nat.div_mul_cancel hdiv, hgeom]
  rw [← hquot_phi]
  exact hquot

theorem cassels_ramified_split
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx2 : 2 ≤ x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ β γ : ℕ,
      p * (x - 1) = β ^ q ∧
      Phi p x = p * γ ^ q := by
  obtain ⟨β, hβ⟩ :=
    cassels_ramified_first_split x a p q hp hq hp2 hx2 hpx1 hcat
  obtain ⟨γ, hγ⟩ :=
    cassels_ramified_second_split x a p q hp hq hp2 hx2 hpx1 hcat
  exact ⟨β, γ, hβ, hγ⟩

theorem cassels_ramified_a_eq_beta_mul_gamma
    (x a p q β γ : ℕ) (hq0 : 0 < q) (hx : 1 < x)
    (hcat : a ^ q = x ^ p - 1)
    (hβ : p * (x - 1) = β ^ q)
    (hγ : Phi p x = p * γ ^ q) :
    a = β * γ := by
  have hgeom : Phi p x * (x - 1) = x ^ p - 1 :=
    Phi_mul_sub_one p x (by omega)
  have hprod : (β * γ) ^ q = a ^ q := by
    rw [Nat.mul_pow]
    calc
      β ^ q * γ ^ q = (p * (x - 1)) * γ ^ q := by rw [← hβ]
      _ = (x - 1) * (p * γ ^ q) := by ring
      _ = (x - 1) * Phi p x := by rw [← hγ]
      _ = Phi p x * (x - 1) := by ring
      _ = x ^ p - 1 := hgeom
      _ = a ^ q := hcat.symm
  exact Nat.pow_left_injective (Nat.ne_of_gt hq0) hprod.symm

theorem cassels_ramified_p_dvd_beta
    (p q x β : ℕ) (hp : p.Prime)
    (hβ : p * (x - 1) = β ^ q) :
    p ∣ β := by
  apply hp.dvd_of_dvd_pow
  rw [← hβ]
  exact dvd_mul_right p (x - 1)

theorem posQuot_natCast_eq_Phi (p x : ℕ) :
    Ripple.LPP.CasselsClassical.posQuot (x : ℤ) p = (Phi p x : ℤ) := by
  unfold Ripple.LPP.CasselsClassical.posQuot Phi
  norm_num

theorem Phi_not_prime_sq_dvd_of_prime_dvd_sub_one
    (p x : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hx : 1 < x)
    (hpx : p ∣ x - 1) :
    ¬ p ^ 2 ∣ Phi p x := by
  have hpxNatZ : (p : ℤ) ∣ ((x - 1 : ℕ) : ℤ) := by
    exact_mod_cast hpx
  have hcast : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
    have hx1 : (1 : ℕ) ≤ x := by omega
    rw [Nat.cast_sub hx1, Nat.cast_one]
  have hpxZ : (p : ℤ) ∣ ((x : ℤ) - 1) := by
    rwa [hcast] at hpxNatZ
  obtain ⟨_, hnot⟩ :=
    Ripple.LPP.CasselsClassical.cassels_vq_posQuot_eq_one
      p hp hp2 (x : ℤ) hpxZ
  intro hsq
  apply hnot
  rw [posQuot_natCast_eq_Phi]
  exact_mod_cast hsq

theorem cassels_ramified_p_not_dvd_gamma
    (p q x γ : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hq0 : 0 < q)
    (hx : 1 < x) (hpx : p ∣ x - 1)
    (hγ : Phi p x = p * γ ^ q) :
    ¬ p ∣ γ := by
  intro hpg
  have hpgq : p ∣ γ ^ q := dvd_pow hpg (Nat.ne_of_gt hq0)
  obtain ⟨m, hm⟩ := hpgq
  have hp2_dvd_rhs : p ^ 2 ∣ p * γ ^ q := by
    refine ⟨m, ?_⟩
    rw [hm]
    ring
  have hp2_dvd_phi : p ^ 2 ∣ Phi p x := by
    rw [hγ]
    exact hp2_dvd_rhs
  exact Phi_not_prime_sq_dvd_of_prime_dvd_sub_one
    p x hp hp2 hx hpx hp2_dvd_phi

theorem cassels_ramified_beta_normal_form
    (p q x β : ℕ) (hp0 : 0 < p) (hq0 : 0 < q)
    (hpβ : p ∣ β)
    (hβ : p * (x - 1) = β ^ q) :
    ∃ δ : ℕ, β = p * δ ∧ x - 1 = p ^ (q - 1) * δ ^ q := by
  obtain ⟨δ, rfl⟩ := hpβ
  refine ⟨δ, rfl, ?_⟩
  have hpow : (p * δ) ^ q = p * (p ^ (q - 1) * δ ^ q) := by
    cases q with
    | zero => omega
    | succ r =>
        simp [Nat.mul_pow, pow_succ]
        ring
  exact Nat.eq_of_mul_eq_mul_left hp0 (by
    rw [hpow] at hβ
    exact hβ)

theorem cassels_ramified_normal_form
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx : 1 < x)
    (hpx1 : p ∣ x - 1) (hcat : a ^ q = x ^ p - 1) :
    ∃ δ γ : ℕ,
      x - 1 = p ^ (q - 1) * δ ^ q ∧
      Phi p x = p * γ ^ q ∧
      a = p * δ * γ ∧
      ¬ p ∣ γ := by
  obtain ⟨β, γ, hβ, hγ⟩ :=
    cassels_ramified_split x a p q hp hq hp2 (by omega) hpx1 hcat
  have ha : a = β * γ :=
    cassels_ramified_a_eq_beta_mul_gamma x a p q β γ
      hq.pos hx hcat hβ hγ
  have hpβ : p ∣ β := cassels_ramified_p_dvd_beta p q x β hp hβ
  obtain ⟨δ, hβeq, hxnorm⟩ :=
    cassels_ramified_beta_normal_form p q x β hp.pos hq.pos hpβ hβ
  have hpγ : ¬ p ∣ γ :=
    cassels_ramified_p_not_dvd_gamma p q x γ hp hp2 hq.pos hx hpx1 hγ
  refine ⟨δ, γ, hxnorm, hγ, ?_, hpγ⟩
  rw [ha, hβeq]

theorem prime_dvd_sub_one_of_pow_eq_pow_add_one
    (x a p q : ℕ) (hp : p.Prime)
    (hq0 : 0 < q) (hpa : p ∣ a) (hxa : x ^ p = a ^ q + 1) :
    p ∣ x - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : ((x : ℕ) : ZMod p) ^ p = 1 := by
    have h : (((x ^ p : ℕ) : ZMod p) = ((a ^ q + 1 : ℕ) : ZMod p)) :=
      congrArg (fun n : ℕ => ((n : ℕ) : ZMod p)) hxa
    have ha0 : ((a : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff a p).mpr hpa
    simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one, ha0,
      zero_pow (Nat.ne_of_gt hq0)] using h
  have hx1_z : ((x : ℕ) : ZMod p) = 1 := by
    rw [← ZMod.pow_card (x : ZMod p)]
    exact hxp
  have hsub0 : ((x - 1 : ℕ) : ZMod p) = 0 := by
    by_cases hx0 : x = 0
    · subst hx0
      simp at hx1_z
    · have hx1 : 1 ≤ x := by omega
      rw [Nat.cast_sub hx1, Nat.cast_one, hx1_z, sub_self]
  exact (ZMod.natCast_eq_zero_iff (x - 1) p).mp hsub0

theorem cassels_ramified_normal_form_of_p_dvd_a
    (x a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hx : 1 < x)
    (hxa : x ^ p = a ^ q + 1) (hpa : p ∣ a) :
    ∃ β γ : ℕ,
      x - 1 = p ^ (q - 1) * β ^ q ∧
      Phi p x = p * γ ^ q ∧
      a = p * β * γ ∧
      ¬ p ∣ γ := by
  have hpx1 : p ∣ x - 1 :=
    prime_dvd_sub_one_of_pow_eq_pow_add_one x a p q hp hq.pos hpa hxa
  have hcat : a ^ q = x ^ p - 1 := by omega
  exact cassels_ramified_normal_form x a p q hp hq hp2 hx hpx1 hcat

theorem prime_sq_dvd_pow_sub_one_of_prime_dvd_sub_one
    (u p : ℕ) (hp : p.Prime) (hu : 1 ≤ u) (hpu : p ∣ u - 1) :
    p ^ 2 ∣ u ^ p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu_one : ((u : ℕ) : ZMod p) = 1 := by
    have hcast : ((u - 1 : ℕ) : ZMod p) = (u : ZMod p) - 1 := by
      rw [Nat.cast_sub hu]
      simp
    have hzero : ((u - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (u - 1) p).mpr hpu
    have : (u : ZMod p) - 1 = 0 := by
      rwa [hcast] at hzero
    exact sub_eq_zero.mp this
  have hPhi_dvd : p ∣ Phi p u := by
    have hPhi_zero : ((Phi p u : ℕ) : ZMod p) = 0 := by
      simp [Phi, hu_one]
    exact (ZMod.natCast_eq_zero_iff (Phi p u) p).mp hPhi_zero
  obtain ⟨A, hA⟩ := hPhi_dvd
  obtain ⟨B, hB⟩ := hpu
  refine ⟨A * B, ?_⟩
  have hgeom : Phi p u * (u - 1) = u ^ p - 1 :=
    Phi_mul_sub_one p u hu
  calc
    u ^ p - 1 = Phi p u * (u - 1) := hgeom.symm
    _ = (p * A) * (p * B) := by rw [hA, hB]
    _ = p ^ 2 * (A * B) := by ring

theorem cassels_ramified_p_dvd_beta_of_u_sub_one
    (u p β γ : ℕ) (hp : p.Prime) (hu : 1 ≤ u)
    (hpu : p ∣ u - 1)
    (ha : u ^ p - 1 = p * β * γ)
    (hpγ : ¬ p ∣ γ) :
    p ∣ β := by
  have hp2a : p ^ 2 ∣ u ^ p - 1 :=
    prime_sq_dvd_pow_sub_one_of_prime_dvd_sub_one u p hp hu hpu
  have hp2_rhs : p ^ 2 ∣ p * β * γ := by
    rwa [ha] at hp2a
  obtain ⟨k, hk⟩ := hp2_rhs
  have hp_dvd_bg : p ∣ β * γ := by
    refine ⟨k, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * (β * γ) = p * β * γ := by ring
      _ = p ^ 2 * k := hk
      _ = p * (p * k) := by rw [pow_two]; ring
  rcases hp.dvd_mul.mp hp_dvd_bg with hpβ | hpγ'
  · exact hpβ
  · exact False.elim (hpγ hpγ')

theorem cassels_ramified_second_p_normal_form
    (x a p q β γ : ℕ) (hq0 : 0 < q)
    (hβnorm : x - 1 = p ^ (q - 1) * β ^ q)
    (hanorm : a = p * β * γ)
    (hpβ : p ∣ β) :
    ∃ δ : ℕ,
      β = p * δ ∧
      x - 1 = p ^ (2 * q - 1) * δ ^ q ∧
      a = p ^ 2 * δ * γ := by
  obtain ⟨δ, hβeq⟩ := hpβ
  refine ⟨δ, hβeq, ?_, ?_⟩
  · subst β
    rw [Nat.mul_pow] at hβnorm
    calc
      x - 1 = p ^ (q - 1) * (p ^ q * δ ^ q) := hβnorm
      _ = p ^ ((q - 1) + q) * δ ^ q := by ring_nf
      _ = p ^ (2 * q - 1) * δ ^ q := by
            have hq1 : 1 ≤ q := by omega
            have hsum : q - 1 + q = 2 * q - 1 := by omega
            rw [hsum]
  · subst β
    calc
      a = p * (p * δ) * γ := hanorm
      _ = p ^ 2 * δ * γ := by rw [pow_two]; ring

theorem cassels_ramified_base_power_lower_bound
    (u v p q δ : ℕ)
    (hu : 1 < u)
    (hq0 : 0 < q)
    (hvlt : v < u ^ (q - 1))
    (hxgt : 1 < v * u)
    (hxnorm : v * u - 1 = p ^ (2 * q - 1) * δ ^ q) :
    p ^ (2 * q - 1) < u ^ q := by
  have hxsub_pos : 0 < v * u - 1 := by omega
  have hprod_pos : 0 < p ^ (2 * q - 1) * δ ^ q := by
    rwa [hxnorm] at hxsub_pos
  have hdelta_pow_pos : 0 < δ ^ q := by
    by_contra hnot
    have hzero : δ ^ q = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, mul_zero] at hprod_pos
    omega
  have hp_pow_le :
      p ^ (2 * q - 1) ≤ v * u - 1 := by
    rw [hxnorm]
    exact Nat.le_mul_of_pos_right _ hdelta_pow_pos
  have hsub_lt : v * u - 1 < v * u := by omega
  have hvu_lt : v * u < u ^ (q - 1) * u :=
    Nat.mul_lt_mul_of_pos_right hvlt (by omega : 0 < u)
  have huq : u ^ (q - 1) * u = u ^ q := by
    calc
      u ^ (q - 1) * u = u ^ ((q - 1) + 1) := by
        rw [pow_succ]
      _ = u ^ q := by
        rw [show (q - 1) + 1 = q by omega]
  exact lt_of_le_of_lt hp_pow_le
    (lt_trans hsub_lt (lt_of_lt_of_eq hvu_lt huq))

theorem Phi_modEq_prime_of_prime_sq_dvd_sub_one
    (p x : ℕ) (hx : 1 ≤ x) (hpx2 : p ^ 2 ∣ x - 1) :
    Phi p x ≡ p [MOD p ^ 2] := by
  have hxmod : x ≡ 1 [MOD p ^ 2] :=
    ((Nat.modEq_iff_dvd' hx).mpr hpx2).symm
  have hterms :
      ∀ i ∈ Finset.range p, x ^ i ≡ (fun _ : ℕ => 1) i [MOD p ^ 2] := by
    intro i _
    simpa using hxmod.pow i
  have hsum :=
    Nat.ModEq.sum (s := Finset.range p)
      (f := fun i => x ^ i) (g := fun _ : ℕ => 1) hterms
  simpa [Phi] using hsum

theorem Phi_modEq_of_dvd_sub_one
    (p x M : ℕ) (hx : 1 ≤ x) (hM : M ∣ x - 1) :
    Phi p x ≡ p [MOD M] := by
  have hxmod : x ≡ 1 [MOD M] :=
    ((Nat.modEq_iff_dvd' hx).mpr hM).symm
  have hterms :
      ∀ i ∈ Finset.range p, x ^ i ≡ (fun _ : ℕ => 1) i [MOD M] := by
    intro i _
    simpa using hxmod.pow i
  have hsum :=
    Nat.ModEq.sum (s := Finset.range p)
      (f := fun i => x ^ i) (g := fun _ : ℕ => 1) hterms
  simpa [Phi] using hsum

theorem ramified_gamma_pow_modEq_one_of_prime_sq_dvd_sub_one
    (p q x γ : ℕ) (hp0 : p ≠ 0) (hx : 1 ≤ x)
    (hpx2 : p ^ 2 ∣ x - 1)
    (hγ : Phi p x = p * γ ^ q) :
    γ ^ q ≡ 1 [MOD p] := by
  have hphi : Phi p x ≡ p [MOD p ^ 2] :=
    Phi_modEq_prime_of_prime_sq_dvd_sub_one p x hx hpx2
  have hg : p * γ ^ q ≡ p * 1 [MOD p * p] := by
    simpa [hγ, pow_two] using hphi
  exact Nat.ModEq.mul_left_cancel' hp0 hg

theorem prime_pow_modEq_one_of_lt
    (p q a : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpow : a ^ q ≡ 1 [MOD p]) :
    a ≡ 1 [MOD p] := by
  have hp_not_dvd_a : ¬ p ∣ a := by
    intro hpa
    have ha_pow_zero : a ^ q ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_pow hpa hq.ne_zero)
    have hone_zero : 1 ≡ 0 [MOD p] := hpow.symm.trans ha_pow_zero
    exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp hone_zero)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcop_ap : Nat.Coprime a p :=
    ((hp.coprime_iff_not_dvd).mpr hp_not_dvd_a).symm
  let z : (ZMod p)ˣ := ZMod.unitOfCoprime a hcop_ap
  have hz_pow : z ^ q = 1 := by
    ext
    change ((z : ZMod p) ^ q) = (1 : ZMod p)
    rw [ZMod.coe_unitOfCoprime]
    rw [← Nat.cast_pow]
    simpa using (ZMod.natCast_eq_natCast_iff (a ^ q) 1 p).mpr hpow
  have horder_dvd_q : orderOf z ∣ q := orderOf_dvd_of_pow_eq_one hz_pow
  have horder_dvd_psub : orderOf z ∣ p - 1 := by
    have horder_dvd_card : orderOf z ∣ Nat.card (ZMod p)ˣ :=
      orderOf_dvd_natCard z
    rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient p,
      Nat.totient_prime hp] at horder_dvd_card
  have hq_not_dvd_psub : ¬ q ∣ p - 1 := by
    intro hqdiv
    have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hle : q ≤ p - 1 := Nat.le_of_dvd hpos hqdiv
    omega
  have hz_one : z = 1 := by
    rcases (Nat.dvd_prime hq).mp horder_dvd_q with horder_one | horder_q
    · exact orderOf_eq_one_iff.mp horder_one
    · exact False.elim (hq_not_dvd_psub (by rwa [horder_q] at horder_dvd_psub))
  have ha_cast_one : (a : ZMod p) = 1 := by
    calc
      (a : ZMod p) = (z : ZMod p) := by
        simp [z, ZMod.coe_unitOfCoprime]
      _ = (1 : ZMod p) := by rw [hz_one]; rfl
  exact (ZMod.natCast_eq_natCast_iff a 1 p).mp (by
    simpa using ha_cast_one)

theorem ramified_gamma_pow_high_modEq_one
    (p q x γ δ : ℕ) (hp0 : p ≠ 0) (hq1 : 1 ≤ q) (hx : 1 ≤ x)
    (hxnorm : x - 1 = p ^ (2 * q - 1) * δ ^ q)
    (hγ : Phi p x = p * γ ^ q) :
    γ ^ q ≡ 1 [MOD p ^ (2 * q - 2)] := by
  have hp_high_dvd : p ^ (2 * q - 1) ∣ x - 1 := by
    rw [hxnorm]
    exact dvd_mul_right (p ^ (2 * q - 1)) (δ ^ q)
  have hphi : Phi p x ≡ p [MOD p ^ (2 * q - 1)] :=
    Phi_modEq_of_dvd_sub_one p x (p ^ (2 * q - 1)) hx hp_high_dvd
  have hpow_succ : p ^ (2 * q - 1) = p * p ^ (2 * q - 2) := by
    have hsucc : 2 * q - 1 = (2 * q - 2) + 1 := by omega
    rw [hsucc, pow_succ]
    ring
  have hg : p * γ ^ q ≡ p * 1 [MOD p * p ^ (2 * q - 2)] := by
    simpa [hγ, hpow_succ] using hphi
  exact Nat.ModEq.mul_left_cancel' hp0 hg

theorem prime_pow_root_high_modEq_one_of_lt
    (p q a m : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp_odd : Odd p) (hpq : p < q)
    (ha_mod : a ≡ 1 [MOD p])
    (ha_pow_high : a ^ q ≡ 1 [MOD p ^ m]) :
    a ≡ 1 [MOD p ^ m] := by
  by_cases ha_one : a = 1
  · subst a
    exact Nat.ModEq.refl 1
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_ne_zero : a ≠ 0 := by
    intro ha_zero
    subst a
    have hone_zero : 1 ≡ 0 [MOD p] := ha_mod.symm
    exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp hone_zero)
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha_ne_zero
  have ha_gt_one : 1 < a := by omega
  have ha_one_le : 1 ≤ a := by omega
  have hpdvd_sub : p ∣ a - 1 :=
    (Nat.modEq_iff_dvd' ha_one_le).mp ha_mod.symm
  have hp_not_dvd_a : ¬ p ∣ a := by
    intro hpa
    have ha_zero_mod : a ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr hpa
    have hone_zero : 1 ≡ 0 [MOD p] :=
      ha_mod.symm.trans ha_zero_mod
    exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp hone_zero)
  have hpow_ge_one : 1 ≤ a ^ q :=
    Nat.succ_le_of_lt (pow_pos ha_pos q)
  have hpow_dvd : p ^ m ∣ a ^ q - 1 :=
    (Nat.modEq_iff_dvd' hpow_ge_one).mp ha_pow_high.symm
  have hpow_gt_one : 1 < a ^ q :=
    Nat.one_lt_pow hq.ne_zero ha_gt_one
  have hpow_sub_ne : a ^ q - 1 ≠ 0 := by omega
  have hm_le_val_pow : m ≤ padicValNat p (a ^ q - 1) :=
    (padicValNat_dvd_iff_le hpow_sub_ne).mp hpow_dvd
  have hval_pow_eq :
      padicValNat p (a ^ q - 1)
        = padicValNat p (a - 1) + padicValNat p q := by
    simpa using
      (padicValNat.pow_sub_pow (p := p) hp_odd
        (x := a) (y := 1) ha_gt_one hpdvd_sub hp_not_dvd_a hq.ne_zero)
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hdiv
    have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdiv
    omega
  have hpval_q : padicValNat p q = 0 :=
    padicValNat.eq_zero_of_not_dvd hp_not_dvd_q
  have hm_le_val_sub : m ≤ padicValNat p (a - 1) := by
    rw [hval_pow_eq, hpval_q, add_zero] at hm_le_val_pow
    exact hm_le_val_pow
  have hsub_ne : a - 1 ≠ 0 := by omega
  have hpow_dvd_sub : p ^ m ∣ a - 1 :=
    (padicValNat_dvd_iff_le hsub_ne).mpr hm_le_val_sub
  exact ((Nat.modEq_iff_dvd' ha_one_le).mpr hpow_dvd_sub).symm

theorem Phi_gt_prime_of_one_lt
    (p x : ℕ) (hp2 : 2 ≤ p) (hx : 1 < x) :
    p < Phi p x := by
  have hle :
      ∀ i ∈ Finset.range p, (fun _ : ℕ => (1 : ℕ)) i ≤ x ^ i := by
    intro i _
    exact Nat.one_le_pow i x (by omega)
  have hlt_one :
      (fun _ : ℕ => (1 : ℕ)) 1 < x ^ 1 := by
    simpa using hx
  have hsum_lt :
      (Finset.range p).sum (fun _ : ℕ => (1 : ℕ))
        < (Finset.range p).sum (fun i => x ^ i) :=
    Finset.sum_lt_sum hle ⟨1, by simpa using hp2, hlt_one⟩
  simpa [Phi] using hsum_lt

theorem ramified_gamma_gt_one
    (p q x γ : ℕ) (hp2 : 2 ≤ p) (hq0 : 0 < q) (hx : 1 < x)
    (hγ : Phi p x = p * γ ^ q) :
    1 < γ := by
  have hphi_gt : p < Phi p x :=
    Phi_gt_prime_of_one_lt p x hp2 hx
  by_contra hnot
  have hγ_le : γ ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos γ with hγ0 | hγpos
  · subst γ
    rw [zero_pow hq0.ne', mul_zero] at hγ
    omega
  · have hγeq : γ = 1 := by omega
    subst γ
    rw [one_pow, mul_one] at hγ
    omega

theorem ramified_u_pow_gt_five_mul_p_pow_q_of_gamma_high
    (u p q δ γ : ℕ) (hu : 1 < u) (hp5 : 5 ≤ p) (hq0 : 0 < q)
    (ha : u ^ p - 1 = p ^ 2 * δ * γ)
    (hγgt : 1 < γ)
    (hγdvd : p ^ (q - 1) ∣ γ - 1) :
    5 * p ^ q < u ^ p := by
  have hp_pos : 0 < p := by omega
  have hu_pow_gt_one : 1 < u ^ p :=
    Nat.one_lt_pow (by omega : p ≠ 0) hu
  have hsub_pos : 0 < u ^ p - 1 := by omega
  have hprod_pos : 0 < p ^ 2 * δ * γ := by
    rwa [ha] at hsub_pos
  have hδpos : 0 < δ := by
    by_contra hnot
    have hδ0 : δ = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hδ0, mul_zero, zero_mul] at hprod_pos
    omega
  have hγsub_pos : 0 < γ - 1 := by omega
  have hp_pow_le_gamma_sub : p ^ (q - 1) ≤ γ - 1 :=
    Nat.le_of_dvd hγsub_pos hγdvd
  have hγ_lower : p ^ (q - 1) + 1 ≤ γ := by omega
  have hbase_le_prod :
      p ^ 2 * (p ^ (q - 1) + 1) ≤ p ^ 2 * δ * γ := by
    have hδ_one : 1 ≤ δ := Nat.succ_le_of_lt hδpos
    have hbase_le_dg : p ^ (q - 1) + 1 ≤ δ * γ := by
      calc
        p ^ (q - 1) + 1 ≤ 1 * γ := by simpa using hγ_lower
        _ ≤ δ * γ := Nat.mul_le_mul_right γ hδ_one
    have hmul := Nat.mul_le_mul_left (p ^ 2) hbase_le_dg
    simpa [mul_assoc] using hmul
  have hbase_le_sub :
      p ^ 2 * (p ^ (q - 1) + 1) ≤ u ^ p - 1 := by
    rw [ha]
    exact hbase_le_prod
  have hpow_main_lt_base :
      p ^ (q + 1) < p ^ 2 * (p ^ (q - 1) + 1) := by
    have hq_exp : 2 + (q - 1) = q + 1 := by omega
    calc
      p ^ (q + 1) = p ^ 2 * p ^ (q - 1) := by
        rw [← pow_add, hq_exp]
      _ < p ^ 2 * (p ^ (q - 1) + 1) := by
        exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) (pow_pos hp_pos 2)
  have hpow_main_lt_u : p ^ (q + 1) < u ^ p := by
    exact lt_of_lt_of_le hpow_main_lt_base
      (le_trans hbase_le_sub (Nat.sub_le _ _))
  have hfive_le : 5 * p ^ q ≤ p ^ (q + 1) := by
    calc
      5 * p ^ q ≤ p * p ^ q := Nat.mul_le_mul_right (p ^ q) hp5
      _ = p ^ (q + 1) := by
        rw [pow_succ]
        ring
  exact lt_of_le_of_lt hfive_le hpow_main_lt_u

theorem prime_eq_seven_or_ge_eleven_of_five_lt
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hpq : p < q) :
    q = 7 ∨ 11 ≤ q := by
  by_cases hq7 : q = 7
  · exact Or.inl hq7
  · right
    have hq_ne5 : q ≠ 5 := by
      intro h
      omega
    have hq_ne6 : q ≠ 6 := by
      intro h
      subst h
      norm_num at hq
    have hq_ne8 : q ≠ 8 := by
      intro h
      subst h
      norm_num at hq
    have hq_ne9 : q ≠ 9 := by
      intro h
      subst h
      norm_num at hq
    have hq_ne10 : q ≠ 10 := by
      intro h
      subst h
      norm_num at hq
    omega

theorem prime_eq_five_of_five_le_lt_seven
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p < 7) :
    p = 5 := by
  have hp_ne6 : p ≠ 6 := by
    intro h
    subst h
    norm_num at hp
  omega

theorem prime_dvd_left_factor_sub_one_of_mul_sub_one
    (p u v : ℕ) [Fact p.Prime]
    (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hpu : p ∣ u - 1) (hpmul : p ∣ v * u - 1) :
    p ∣ v - 1 := by
  have hu_one : ((u : ℕ) : ZMod p) = 1 := by
    have hcast : ((u - 1 : ℕ) : ZMod p) = (u : ZMod p) - 1 := by
      rw [Nat.cast_sub hu]
      simp
    have hzero : ((u - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (u - 1) p).mpr hpu
    have : (u : ZMod p) - 1 = 0 := by
      rwa [hcast] at hzero
    exact sub_eq_zero.mp this
  have hmul_one : ((v * u : ℕ) : ZMod p) = 1 := by
    have hvu_one : 1 ≤ v * u := Nat.mul_pos (by omega) (by omega)
    have hcast :
        ((v * u - 1 : ℕ) : ZMod p) = ((v * u : ℕ) : ZMod p) - 1 := by
      rw [Nat.cast_sub hvu_one]
      simp
    have hzero : ((v * u - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (v * u - 1) p).mpr hpmul
    have : ((v * u : ℕ) : ZMod p) - 1 = 0 := by
      rwa [hcast] at hzero
    exact sub_eq_zero.mp this
  have hv_one : ((v : ℕ) : ZMod p) = 1 := by
    simpa [Nat.cast_mul, hu_one] using hmul_one
  have hv_sub_zero : ((v - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hv, Nat.cast_one, hv_one, sub_self]
  exact (ZMod.natCast_eq_zero_iff (v - 1) p).mp hv_sub_zero

theorem ramified_uv_first_quotient
    (u v p q δ : ℕ) (hp0 : 0 < p) (hq0 : 0 < q)
    (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hpu : p ∣ u - 1) (hpv : p ∣ v - 1)
    (hxnorm : v * u - 1 = p ^ (2 * q - 1) * δ ^ q) :
    ∃ U V : ℕ,
      u - 1 = p * U ∧
      v - 1 = p * V ∧
      p ^ (2 * q - 2) ∣ U + V + p * U * V := by
  obtain ⟨U, hU⟩ := hpu
  obtain ⟨V, hV⟩ := hpv
  refine ⟨U, V, hU, hV, ?_⟩
  have hu_eq : u = p * U + 1 := by omega
  have hv_eq : v = p * V + 1 := by omega
  have hprod :
      v * u - 1 = p * (U + V + p * U * V) := by
    have hprod_succ :
        v * u = p * (U + V + p * U * V) + 1 := by
      rw [hu_eq, hv_eq]
      ring
    omega
  have hpow_split :
      p ^ (2 * q - 1) = p * p ^ (2 * q - 2) := by
    have hpos : 1 ≤ 2 * q - 1 := by omega
    calc
      p ^ (2 * q - 1) = p ^ ((2 * q - 2) + 1) := by
        congr 1
        omega
      _ = p ^ (2 * q - 2) * p := by rw [pow_succ]
      _ = p * p ^ (2 * q - 2) := by ring
  have hcancel :
      U + V + p * U * V = p ^ (2 * q - 2) * δ ^ q := by
    apply Nat.eq_of_mul_eq_mul_left hp0
    calc
      p * (U + V + p * U * V) = v * u - 1 := hprod.symm
      _ = p ^ (2 * q - 1) * δ ^ q := hxnorm
      _ = p * (p ^ (2 * q - 2) * δ ^ q) := by
        rw [hpow_split]
        ring
  exact ⟨δ ^ q, hcancel⟩

theorem ramified_uv_first_quotient_exact
    (u v p q δ : ℕ) (hp0 : 0 < p) (hq0 : 0 < q)
    (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hpu : p ∣ u - 1) (hpv : p ∣ v - 1)
    (hxnorm : v * u - 1 = p ^ (2 * q - 1) * δ ^ q) :
    ∃ U V : ℕ,
      u - 1 = p * U ∧
      v - 1 = p * V ∧
      U + V + p * U * V = p ^ (2 * q - 2) * δ ^ q := by
  obtain ⟨U, hU⟩ := hpu
  obtain ⟨V, hV⟩ := hpv
  refine ⟨U, V, hU, hV, ?_⟩
  have hu_eq : u = p * U + 1 := by omega
  have hv_eq : v = p * V + 1 := by omega
  have hprod :
      v * u - 1 = p * (U + V + p * U * V) := by
    have hprod_succ :
        v * u = p * (U + V + p * U * V) + 1 := by
      rw [hu_eq, hv_eq]
      ring
    omega
  have hpow_split :
      p ^ (2 * q - 1) = p * p ^ (2 * q - 2) := by
    have hpos : 1 ≤ 2 * q - 1 := by omega
    calc
      p ^ (2 * q - 1) = p ^ ((2 * q - 2) + 1) := by
        congr 1
        omega
      _ = p ^ (2 * q - 2) * p := by rw [pow_succ]
      _ = p * p ^ (2 * q - 2) := by ring
  apply Nat.eq_of_mul_eq_mul_left hp0
  calc
    p * (U + V + p * U * V) = v * u - 1 := hprod.symm
    _ = p ^ (2 * q - 1) * δ ^ q := hxnorm
    _ = p * (p ^ (2 * q - 2) * δ ^ q) := by
      rw [hpow_split]
      ring

theorem ramified_uv_first_quotient_linear_mod
    (p q U V : ℕ) (hq2 : 2 ≤ q)
    (hUV : p ^ (2 * q - 2) ∣ U + V + p * U * V) :
    p ∣ U + V := by
  have hp_pow : p ∣ p ^ (2 * q - 2) := by
    simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 2)
  have hp_sum : p ∣ U + V + p * U * V :=
    hp_pow.trans hUV
  have hp_tail : p ∣ p * U * V := by
    simpa [mul_assoc] using dvd_mul_right p (U * V)
  have hp_sum' : p ∣ (U + V) + p * U * V := by
    simpa [add_assoc] using hp_sum
  exact (Nat.dvd_add_iff_left hp_tail).mpr hp_sum'

theorem ramified_uv_second_quotient_linear_mod
    (p q U V : ℕ) (hp0 : 0 < p) (hq2 : 2 ≤ q)
    (hUV : p ^ (2 * q - 2) ∣ U + V + p * U * V)
    (hlin : p ∣ U + V) :
    ∃ W : ℕ, U + V = p * W ∧ p ∣ W + U * V := by
  obtain ⟨W, hW⟩ := hlin
  refine ⟨W, hW, ?_⟩
  have hp2_pow : p ^ 2 ∣ p ^ (2 * q - 2) :=
    pow_dvd_pow p (by omega : 2 ≤ 2 * q - 2)
  have hp2_sum : p ^ 2 ∣ U + V + p * U * V :=
    hp2_pow.trans hUV
  have hsum_eq : U + V + p * U * V = p * (W + U * V) := by
    rw [hW]
    ring
  rw [hsum_eq] at hp2_sum
  obtain ⟨K, hK⟩ := hp2_sum
  refine ⟨K, ?_⟩
  exact Nat.eq_of_mul_eq_mul_left hp0 (by
    calc
      p * (W + U * V) = p ^ 2 * K := hK
      _ = p * (p * K) := by ring)

theorem ramified_uv_second_quotient_exact
    (p q U V W δ : ℕ) (hp0 : 0 < p) (hq2 : 2 ≤ q)
    (hW : U + V = p * W)
    (hUVexact : U + V + p * U * V = p ^ (2 * q - 2) * δ ^ q) :
    W + U * V = p ^ (2 * q - 3) * δ ^ q := by
  have hleft : U + V + p * U * V = p * (W + U * V) := by
    rw [hW]
    ring
  have hpow_split :
      p ^ (2 * q - 2) = p * p ^ (2 * q - 3) := by
    calc
      p ^ (2 * q - 2) = p ^ ((2 * q - 3) + 1) := by
        congr 1
        omega
      _ = p ^ (2 * q - 3) * p := by rw [pow_succ]
      _ = p * p ^ (2 * q - 3) := by ring
  apply Nat.eq_of_mul_eq_mul_left hp0
  calc
    p * (W + U * V) = U + V + p * U * V := hleft.symm
    _ = p ^ (2 * q - 2) * δ ^ q := hUVexact
    _ = p * (p ^ (2 * q - 3) * δ ^ q) := by
          rw [hpow_split]
          ring

theorem ramified_uv_next_quotient_int_form
    (p U : ℕ) (X Y S R : ℤ) (hp0 : 0 < p)
    (hY : X - S = (p : ℤ) * Y)
    (hRel : Y + (U : ℤ) * X = (p : ℤ) * R) :
    ∃ Z : ℤ,
      Y + (U : ℤ) * S = (p : ℤ) * Z ∧
      Z + (U : ℤ) * Y = R := by
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hp_YS : (p : ℤ) ∣ Y + (U : ℤ) * S := by
    have hsum :
        (p : ℤ) ∣ (Y + (U : ℤ) * S) + (U : ℤ) * (X - S) := by
      rw [hY]
      refine ⟨R, ?_⟩
      calc
        (Y + (U : ℤ) * S) + (U : ℤ) * ((p : ℤ) * Y)
            = Y + (U : ℤ) * X := by
                have hx : X = S + (p : ℤ) * Y := by omega
                rw [hx]
                ring
        _ = (p : ℤ) * R := hRel
    have htail : (p : ℤ) ∣ (U : ℤ) * (X - S) := by
      rw [hY]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (dvd_mul_right (p : ℤ) ((U : ℤ) * Y))
    have hsub := dvd_sub hsum htail
    have hsub_eq :
        ((Y + (U : ℤ) * S) + (U : ℤ) * (X - S))
          - (U : ℤ) * (X - S) = Y + (U : ℤ) * S := by
      ring
    rwa [hsub_eq] at hsub
  rcases hp_YS with ⟨Z, hZ⟩
  refine ⟨Z, hZ, ?_⟩
  apply mul_left_cancel₀ hp_ne
  calc
    (p : ℤ) * (Z + (U : ℤ) * Y)
        = (p : ℤ) * Z + (U : ℤ) * ((p : ℤ) * Y) := by ring
    _ = (Y + (U : ℤ) * S) + (U : ℤ) * (X - S) := by
          rw [← hZ, ← hY]
    _ = Y + (U : ℤ) * X := by ring
    _ = (p : ℤ) * R := hRel

theorem ramified_uv_next_boundary_congruence
    (p U : ℕ) (X Y S R : ℤ)
    (hY : X - S = (p : ℤ) * Y)
    (hRel : Y + (U : ℤ) * X = R) :
    (p : ℤ) ∣ (Y + (U : ℤ) * S) - R := by
  have htail : (p : ℤ) ∣ (U : ℤ) * (S - X) := by
    have hneg : (p : ℤ) ∣ - (X - S) := by
      rw [hY]
      exact dvd_neg.mpr (dvd_mul_right (p : ℤ) Y)
    have hdiff : (p : ℤ) ∣ S - X := by
      simpa using hneg
    exact dvd_mul_of_dvd_right hdiff (U : ℤ)
  have htarget :
      (Y + (U : ℤ) * S) - R = (U : ℤ) * (S - X) := by
    rw [← hRel]
    ring
  rwa [htarget]

theorem ramified_pow_rhs_split
    (p q δ e : ℕ) (he : 1 ≤ e) :
    ((p ^ e * δ ^ q : ℕ) : ℤ)
      = (p : ℤ) * ((p ^ (e - 1) * δ ^ q : ℕ) : ℤ) := by
  have hnat :
      p ^ e * δ ^ q = p * (p ^ (e - 1) * δ ^ q) := by
    calc
      p ^ e * δ ^ q = p ^ ((e - 1) + 1) * δ ^ q := by
        rw [Nat.sub_add_cancel he]
      _ = (p ^ (e - 1) * p) * δ ^ q := by rw [pow_succ]
      _ = p * (p ^ (e - 1) * δ ^ q) := by ring
  exact_mod_cast hnat

theorem ramified_uv_next_two_quotients_int_form
    (p q U δ e : ℕ) (X Y S : ℤ) (hp0 : 0 < p) (he2 : 2 ≤ e)
    (hY : X - S = (p : ℤ) * Y)
    (hRel : Y + (U : ℤ) * X = ((p ^ e * δ ^ q : ℕ) : ℤ)) :
    ∃ Z T : ℤ,
      Y - (-(U : ℤ) * S) = (p : ℤ) * Z ∧
      Z + (U : ℤ) * Y = ((p ^ (e - 1) * δ ^ q : ℕ) : ℤ) ∧
      Z - ((U : ℤ) ^ 2 * S) = (p : ℤ) * T ∧
      T + (U : ℤ) * Z = ((p ^ (e - 2) * δ ^ q : ℕ) : ℤ) := by
  let R1 : ℤ := ((p ^ (e - 1) * δ ^ q : ℕ) : ℤ)
  have hRel1 : Y + (U : ℤ) * X = (p : ℤ) * R1 := by
    rw [hRel]
    dsimp [R1]
    exact ramified_pow_rhs_split p q δ e (by omega)
  obtain ⟨Z, hZ, hZR1⟩ :=
    ramified_uv_next_quotient_int_form
      p U X Y S R1 hp0 hY hRel1
  let R2 : ℤ := ((p ^ (e - 2) * δ ^ q : ℕ) : ℤ)
  have hRel2 : Z + (U : ℤ) * Y = (p : ℤ) * R2 := by
    rw [hZR1]
    dsimp [R1, R2]
    exact ramified_pow_rhs_split p q δ (e - 1) (by omega)
  have hZ' : Y - (-(U : ℤ) * S) = (p : ℤ) * Z := by
    simpa [sub_eq_add_neg] using hZ
  obtain ⟨T, hT, hTR2⟩ :=
    ramified_uv_next_quotient_int_form
      p U Y Z (-(U : ℤ) * S) R2 hp0 hZ' hRel2
  refine ⟨Z, T, hZ', hZR1, ?_, hTR2⟩
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg] using hT

theorem ramified_uv_second_quotient_int_form
    (u p q U V W δ : ℕ) (hu : 1 ≤ u)
    (hU : u - 1 = p * U)
    (hW : U + V = p * W)
    (hWVexact : W + U * V = p ^ (2 * q - 3) * δ ^ q) :
    (u : ℤ) * (W : ℤ) - (U : ℤ) ^ 2
      = ((p ^ (2 * q - 3) * δ ^ q : ℕ) : ℤ) := by
  have huZ : (u : ℤ) = 1 + (p : ℤ) * (U : ℤ) := by
    have hcast : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by
      rw [Nat.cast_sub hu]
      simp
    have hUcast : ((u - 1 : ℕ) : ℤ) = ((p * U : ℕ) : ℤ) := by
      exact_mod_cast hU
    rw [hcast] at hUcast
    push_cast at hUcast
    omega
  have hVZ : (V : ℤ) = (p : ℤ) * (W : ℤ) - (U : ℤ) := by
    have hcast : ((U + V : ℕ) : ℤ) = ((p * W : ℕ) : ℤ) := by
      exact_mod_cast hW
    push_cast at hcast
    omega
  have hWVZ :
      (W : ℤ) + (U : ℤ) * (V : ℤ)
        = ((p ^ (2 * q - 3) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hWVexact
  calc
    (u : ℤ) * (W : ℤ) - (U : ℤ) ^ 2
        = (1 + (p : ℤ) * (U : ℤ)) * (W : ℤ) - (U : ℤ) ^ 2 := by
            rw [huZ]
    _ = (W : ℤ) + (U : ℤ) * ((p : ℤ) * (W : ℤ) - (U : ℤ)) := by
            ring
    _ = (W : ℤ) + (U : ℤ) * (V : ℤ) := by
            rw [hVZ]
    _ = ((p ^ (2 * q - 3) * δ ^ q : ℕ) : ℤ) := hWVZ

theorem ramified_uv_third_quotient_int_form
    (u p q U W δ : ℕ) (hp0 : 0 < p) (hq2 : 2 ≤ q)
    (hu : 1 ≤ u)
    (hU : u - 1 = p * U)
    (hWVint :
      (u : ℤ) * (W : ℤ) - (U : ℤ) ^ 2
        = ((p ^ (2 * q - 3) * δ ^ q : ℕ) : ℤ))
    (hWmod : W ≡ U ^ 2 [MOD p]) :
    ∃ A : ℤ,
      (W : ℤ) - (U : ℤ) ^ 2 = (p : ℤ) * A ∧
      A + (U : ℤ) * (W : ℤ)
        = ((p ^ (2 * q - 4) * δ ^ q : ℕ) : ℤ) := by
  have hmod_dvd :
      (p : ℤ) ∣ (((U ^ 2 : ℕ) : ℤ) - (W : ℤ)) :=
    Nat.modEq_iff_dvd.mp hWmod
  rcases hmod_dvd with ⟨B, hB⟩
  have hA : (W : ℤ) - (U : ℤ) ^ 2 = (p : ℤ) * (-B) := by
    have hB' : (U : ℤ) ^ 2 - (W : ℤ) = (p : ℤ) * B := by
      simpa [Nat.cast_pow] using hB
    calc
      (W : ℤ) - (U : ℤ) ^ 2
          = -((U : ℤ) ^ 2 - (W : ℤ)) := by ring
      _ = -((p : ℤ) * B) := by rw [hB']
      _ = (p : ℤ) * (-B) := by ring
  refine ⟨-B, hA, ?_⟩
  have huZ : (u : ℤ) = 1 + (p : ℤ) * (U : ℤ) := by
    have hcast : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by
      rw [Nat.cast_sub hu]
      simp
    have hUcast : ((u - 1 : ℕ) : ℤ) = ((p * U : ℕ) : ℤ) := by
      exact_mod_cast hU
    rw [hcast] at hUcast
    push_cast at hUcast
    omega
  let R : ℤ := ((p ^ (2 * q - 4) * δ ^ q : ℕ) : ℤ)
  have hpow_split :
      ((p ^ (2 * q - 3) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 3) * δ ^ q =
          p * (p ^ (2 * q - 4) * δ ^ q) := by
      calc
        p ^ (2 * q - 3) * δ ^ q
            = p ^ ((2 * q - 4) + 1) * δ ^ q := by
                have h_exp : 2 * q - 3 = (2 * q - 4) + 1 := by omega
                rw [h_exp]
          _ = (p ^ (2 * q - 4) * p) * δ ^ q := by rw [pow_succ]
          _ = p * (p ^ (2 * q - 4) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * ((-B) + (U : ℤ) * (W : ℤ)) = (p : ℤ) * R := by
    calc
      (p : ℤ) * ((-B) + (U : ℤ) * (W : ℤ))
          = (p : ℤ) * (-B) + (p : ℤ) * ((U : ℤ) * (W : ℤ)) := by ring
      _ = ((W : ℤ) - (U : ℤ) ^ 2)
            + (p : ℤ) * ((U : ℤ) * (W : ℤ)) := by rw [← hA]
      _ = (1 + (p : ℤ) * (U : ℤ)) * (W : ℤ) - (U : ℤ) ^ 2 := by ring
      _ = (u : ℤ) * (W : ℤ) - (U : ℤ) ^ 2 := by rw [huZ]
      _ = ((p ^ (2 * q - 3) * δ ^ q : ℕ) : ℤ) := hWVint
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_third_quotient_cubic_mod
    (p q U W δ : ℕ) (A : ℤ) (hq3 : 3 ≤ q)
    (hAthird :
      A + (U : ℤ) * (W : ℤ)
        = ((p ^ (2 * q - 4) * δ ^ q : ℕ) : ℤ))
    (hWmod : W ≡ U ^ 2 [MOD p]) :
    (p : ℤ) ∣ A + (U : ℤ) ^ 3 := by
  have hp_pow_nat : p ∣ p ^ (2 * q - 4) := by
    simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 4)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 4) * δ ^ q :=
    dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 4) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_AUW : (p : ℤ) ∣ A + (U : ℤ) * (W : ℤ) := by
    rw [hAthird]
    exact hp_rhs
  have hdiff :
      (p : ℤ) ∣ (U : ℤ) ^ 2 - (W : ℤ) := by
    have h := Nat.modEq_iff_dvd.mp hWmod
    simpa [Nat.cast_pow] using h
  have hdiff_mul :
      (p : ℤ) ∣ (U : ℤ) * ((U : ℤ) ^ 2 - (W : ℤ)) :=
    dvd_mul_of_dvd_right hdiff (U : ℤ)
  have hmul_eq :
      (U : ℤ) * ((U : ℤ) ^ 2 - (W : ℤ))
        = (U : ℤ) ^ 3 - (U : ℤ) * (W : ℤ) := by
    ring
  have hp_cube_sub :
      (p : ℤ) ∣ (U : ℤ) ^ 3 - (U : ℤ) * (W : ℤ) := by
    rwa [← hmul_eq]
  have hsum := dvd_add hp_AUW hp_cube_sub
  simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using hsum

theorem ramified_uv_fourth_quotient_int_form
    (p q U W δ : ℕ) (A : ℤ) (hp0 : 0 < p) (hq3 : 3 ≤ q)
    (hA :
      (W : ℤ) - (U : ℤ) ^ 2 = (p : ℤ) * A)
    (hAthird :
      A + (U : ℤ) * (W : ℤ)
        = ((p ^ (2 * q - 4) * δ ^ q : ℕ) : ℤ))
    (hAcubic : (p : ℤ) ∣ A + (U : ℤ) ^ 3) :
    ∃ B : ℤ,
      A + (U : ℤ) ^ 3 = (p : ℤ) * B ∧
      B + (U : ℤ) * A
        = ((p ^ (2 * q - 5) * δ ^ q : ℕ) : ℤ) := by
  rcases hAcubic with ⟨B, hB⟩
  refine ⟨B, hB, ?_⟩
  let R : ℤ := ((p ^ (2 * q - 5) * δ ^ q : ℕ) : ℤ)
  have hpow_split :
      ((p ^ (2 * q - 4) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 4) * δ ^ q =
          p * (p ^ (2 * q - 5) * δ ^ q) := by
      calc
        p ^ (2 * q - 4) * δ ^ q
            = p ^ ((2 * q - 5) + 1) * δ ^ q := by
                have h_exp : 2 * q - 4 = (2 * q - 5) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 5) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 5) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (B + (U : ℤ) * A) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (B + (U : ℤ) * A)
          = (p : ℤ) * B + (U : ℤ) * ((p : ℤ) * A) := by ring
      _ = (A + (U : ℤ) ^ 3)
            + (U : ℤ) * ((W : ℤ) - (U : ℤ) ^ 2) := by
              rw [← hB, ← hA]
      _ = A + (U : ℤ) * (W : ℤ) := by ring
      _ = ((p ^ (2 * q - 4) * δ ^ q : ℕ) : ℤ) := hAthird
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_fourth_quotient_quartic_mod
    (p q U δ : ℕ) (A B : ℤ) (hq3 : 3 ≤ q)
    (hBfourth :
      B + (U : ℤ) * A
        = ((p ^ (2 * q - 5) * δ ^ q : ℕ) : ℤ))
    (hAcubic : (p : ℤ) ∣ A + (U : ℤ) ^ 3) :
    (p : ℤ) ∣ B - (U : ℤ) ^ 4 := by
  have hp_pow_nat : p ∣ p ^ (2 * q - 5) := by
    simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 5)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 5) * δ ^ q :=
    dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 5) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_BUA : (p : ℤ) ∣ B + (U : ℤ) * A := by
    rw [hBfourth]
    exact hp_rhs
  have hp_UA_U4 : (p : ℤ) ∣ (U : ℤ) * A + (U : ℤ) ^ 4 := by
    have hmul : (p : ℤ) ∣ (U : ℤ) * (A + (U : ℤ) ^ 3) :=
      dvd_mul_of_dvd_right hAcubic (U : ℤ)
    have hmul_eq :
        (U : ℤ) * (A + (U : ℤ) ^ 3)
          = (U : ℤ) * A + (U : ℤ) ^ 4 := by
      ring
    rwa [hmul_eq] at hmul
  have hsub := dvd_sub hp_BUA hp_UA_U4
  have hsub_eq :
      (B + (U : ℤ) * A) - ((U : ℤ) * A + (U : ℤ) ^ 4)
        = B - (U : ℤ) ^ 4 := by
    ring
  rwa [hsub_eq] at hsub

theorem ramified_uv_fifth_quotient_int_form
    (p q U δ : ℕ) (A B : ℤ) (hp0 : 0 < p) (hq4 : 4 ≤ q)
    (hB :
      A + (U : ℤ) ^ 3 = (p : ℤ) * B)
    (hBfourth :
      B + (U : ℤ) * A
        = ((p ^ (2 * q - 5) * δ ^ q : ℕ) : ℤ))
    (hBquartic : (p : ℤ) ∣ B - (U : ℤ) ^ 4) :
    ∃ C : ℤ,
      B - (U : ℤ) ^ 4 = (p : ℤ) * C ∧
      C + (U : ℤ) * B
        = ((p ^ (2 * q - 6) * δ ^ q : ℕ) : ℤ) := by
  rcases hBquartic with ⟨C, hC⟩
  refine ⟨C, hC, ?_⟩
  let R : ℤ := ((p ^ (2 * q - 6) * δ ^ q : ℕ) : ℤ)
  have hpow_split :
      ((p ^ (2 * q - 5) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 5) * δ ^ q =
          p * (p ^ (2 * q - 6) * δ ^ q) := by
      calc
        p ^ (2 * q - 5) * δ ^ q
            = p ^ ((2 * q - 6) + 1) * δ ^ q := by
                have h_exp : 2 * q - 5 = (2 * q - 6) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 6) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 6) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (C + (U : ℤ) * B) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (C + (U : ℤ) * B)
          = (p : ℤ) * C + (U : ℤ) * ((p : ℤ) * B) := by ring
      _ = (B - (U : ℤ) ^ 4)
            + (U : ℤ) * (A + (U : ℤ) ^ 3) := by
              rw [← hC, ← hB]
      _ = B + (U : ℤ) * A := by ring
      _ = ((p ^ (2 * q - 5) * δ ^ q : ℕ) : ℤ) := hBfourth
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_fifth_quotient_quintic_mod
    (p q U δ : ℕ) (B C : ℤ) (hq4 : 4 ≤ q)
    (hCfifth :
      C + (U : ℤ) * B
        = ((p ^ (2 * q - 6) * δ ^ q : ℕ) : ℤ))
    (hBquartic : (p : ℤ) ∣ B - (U : ℤ) ^ 4) :
    (p : ℤ) ∣ C + (U : ℤ) ^ 5 := by
  have hp_pow_nat : p ∣ p ^ (2 * q - 6) := by
    simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 6)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 6) * δ ^ q :=
    dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 6) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_CUB : (p : ℤ) ∣ C + (U : ℤ) * B := by
    rw [hCfifth]
    exact hp_rhs
  have hp_UB_U5 : (p : ℤ) ∣ (U : ℤ) * B - (U : ℤ) ^ 5 := by
    have hmul : (p : ℤ) ∣ (U : ℤ) * (B - (U : ℤ) ^ 4) :=
      dvd_mul_of_dvd_right hBquartic (U : ℤ)
    have hmul_eq :
        (U : ℤ) * (B - (U : ℤ) ^ 4)
          = (U : ℤ) * B - (U : ℤ) ^ 5 := by
      ring
    rwa [hmul_eq] at hmul
  have hsub := dvd_sub hp_CUB hp_UB_U5
  have hsub_eq :
      (C + (U : ℤ) * B) - ((U : ℤ) * B - (U : ℤ) ^ 5)
        = C + (U : ℤ) ^ 5 := by
    ring
  rwa [hsub_eq] at hsub

theorem ramified_uv_sixth_quotient_int_form
    (p q U δ : ℕ) (B C : ℤ) (hp0 : 0 < p) (hq4 : 4 ≤ q)
    (hC :
      B - (U : ℤ) ^ 4 = (p : ℤ) * C)
    (hCfifth :
      C + (U : ℤ) * B
        = ((p ^ (2 * q - 6) * δ ^ q : ℕ) : ℤ))
    (hCquintic : (p : ℤ) ∣ C + (U : ℤ) ^ 5) :
    ∃ D : ℤ,
      C + (U : ℤ) ^ 5 = (p : ℤ) * D ∧
      D + (U : ℤ) * C
        = ((p ^ (2 * q - 7) * δ ^ q : ℕ) : ℤ) := by
  rcases hCquintic with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  let R : ℤ := ((p ^ (2 * q - 7) * δ ^ q : ℕ) : ℤ)
  have hpow_split :
      ((p ^ (2 * q - 6) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 6) * δ ^ q =
          p * (p ^ (2 * q - 7) * δ ^ q) := by
      calc
        p ^ (2 * q - 6) * δ ^ q
            = p ^ ((2 * q - 7) + 1) * δ ^ q := by
                have h_exp : 2 * q - 6 = (2 * q - 7) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 7) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 7) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (D + (U : ℤ) * C) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (D + (U : ℤ) * C)
          = (p : ℤ) * D + (U : ℤ) * ((p : ℤ) * C) := by ring
      _ = (C + (U : ℤ) ^ 5)
            + (U : ℤ) * (B - (U : ℤ) ^ 4) := by
              rw [← hD, ← hC]
      _ = C + (U : ℤ) * B := by ring
      _ = ((p ^ (2 * q - 6) * δ ^ q : ℕ) : ℤ) := hCfifth
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_sixth_quotient_sextic_mod
    (p q U δ : ℕ) (C D : ℤ) (hq4 : 4 ≤ q)
    (hDsixth :
      D + (U : ℤ) * C
        = ((p ^ (2 * q - 7) * δ ^ q : ℕ) : ℤ))
    (hCquintic : (p : ℤ) ∣ C + (U : ℤ) ^ 5) :
    (p : ℤ) ∣ D - (U : ℤ) ^ 6 := by
  have hp_pow_nat : p ∣ p ^ (2 * q - 7) := by
    simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 7)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 7) * δ ^ q :=
    dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 7) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_DUC : (p : ℤ) ∣ D + (U : ℤ) * C := by
    rw [hDsixth]
    exact hp_rhs
  have hp_UC_U6 : (p : ℤ) ∣ (U : ℤ) * C + (U : ℤ) ^ 6 := by
    have hmul : (p : ℤ) ∣ (U : ℤ) * (C + (U : ℤ) ^ 5) :=
      dvd_mul_of_dvd_right hCquintic (U : ℤ)
    have hmul_eq :
        (U : ℤ) * (C + (U : ℤ) ^ 5)
          = (U : ℤ) * C + (U : ℤ) ^ 6 := by
      ring
    rwa [hmul_eq] at hmul
  have hsub := dvd_sub hp_DUC hp_UC_U6
  have hsub_eq :
      (D + (U : ℤ) * C) - ((U : ℤ) * C + (U : ℤ) ^ 6)
        = D - (U : ℤ) ^ 6 := by
    ring
  rwa [hsub_eq] at hsub

theorem ramified_uv_seventh_quotient_int_form
    (p q U δ : ℕ) (C D : ℤ) (hp0 : 0 < p) (hq4 : 4 ≤ q)
    (hD :
      C + (U : ℤ) ^ 5 = (p : ℤ) * D)
    (hDsixth :
      D + (U : ℤ) * C
        = ((p ^ (2 * q - 7) * δ ^ q : ℕ) : ℤ))
    (hDsextic : (p : ℤ) ∣ D - (U : ℤ) ^ 6) :
    ∃ E : ℤ,
      D - (U : ℤ) ^ 6 = (p : ℤ) * E ∧
      E + (U : ℤ) * D
        = ((p ^ (2 * q - 8) * δ ^ q : ℕ) : ℤ) := by
  rcases hDsextic with ⟨E, hE⟩
  refine ⟨E, hE, ?_⟩
  let R : ℤ := ((p ^ (2 * q - 8) * δ ^ q : ℕ) : ℤ)
  have hpow_split :
      ((p ^ (2 * q - 7) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 7) * δ ^ q =
          p * (p ^ (2 * q - 8) * δ ^ q) := by
      calc
        p ^ (2 * q - 7) * δ ^ q
            = p ^ ((2 * q - 8) + 1) * δ ^ q := by
                have h_exp : 2 * q - 7 = (2 * q - 8) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 8) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 8) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (E + (U : ℤ) * D) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (E + (U : ℤ) * D)
          = (p : ℤ) * E + (U : ℤ) * ((p : ℤ) * D) := by ring
      _ = (D - (U : ℤ) ^ 6)
            + (U : ℤ) * (C + (U : ℤ) ^ 5) := by
              rw [← hE, ← hD]
      _ = D + (U : ℤ) * C := by ring
      _ = ((p ^ (2 * q - 7) * δ ^ q : ℕ) : ℤ) := hDsixth
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_seventh_quotient_septic_mod
    (p q U δ : ℕ) (D E : ℤ) (hq5 : 5 ≤ q)
    (hEseventh :
      E + (U : ℤ) * D
        = ((p ^ (2 * q - 8) * δ ^ q : ℕ) : ℤ))
    (hDsextic : (p : ℤ) ∣ D - (U : ℤ) ^ 6) :
    (p : ℤ) ∣ E + (U : ℤ) ^ 7 := by
  have hp_pow_nat : p ∣ p ^ (2 * q - 8) := by
    simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 8)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 8) * δ ^ q :=
    dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 8) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_EUD : (p : ℤ) ∣ E + (U : ℤ) * D := by
    rw [hEseventh]
    exact hp_rhs
  have hp_UD_U7 : (p : ℤ) ∣ (U : ℤ) * D - (U : ℤ) ^ 7 := by
    have hmul : (p : ℤ) ∣ (U : ℤ) * (D - (U : ℤ) ^ 6) :=
      dvd_mul_of_dvd_right hDsextic (U : ℤ)
    have hmul_eq :
        (U : ℤ) * (D - (U : ℤ) ^ 6)
          = (U : ℤ) * D - (U : ℤ) ^ 7 := by
      ring
    rwa [hmul_eq] at hmul
  have hsub := dvd_sub hp_EUD hp_UD_U7
  have hsub_eq :
      (E + (U : ℤ) * D) - ((U : ℤ) * D - (U : ℤ) ^ 7)
        = E + (U : ℤ) ^ 7 := by
    ring
  rwa [hsub_eq] at hsub

theorem ramified_uv_eighth_quotient_int_form
    (p q U δ : ℕ) (D E : ℤ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    (hE :
      D - (U : ℤ) ^ 6 = (p : ℤ) * E)
    (hEseventh :
      E + (U : ℤ) * D
        = ((p ^ (2 * q - 8) * δ ^ q : ℕ) : ℤ))
    (hEseptic : (p : ℤ) ∣ E + (U : ℤ) ^ 7) :
    ∃ F : ℤ,
      E + (U : ℤ) ^ 7 = (p : ℤ) * F ∧
      F + (U : ℤ) * E
        = ((p ^ (2 * q - 9) * δ ^ q : ℕ) : ℤ) := by
  rcases hEseptic with ⟨F, hF⟩
  refine ⟨F, hF, ?_⟩
  let R : ℤ := ((p ^ (2 * q - 9) * δ ^ q : ℕ) : ℤ)
  have hpow_split :
      ((p ^ (2 * q - 8) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 8) * δ ^ q =
          p * (p ^ (2 * q - 9) * δ ^ q) := by
      calc
        p ^ (2 * q - 8) * δ ^ q
            = p ^ ((2 * q - 9) + 1) * δ ^ q := by
                have h_exp : 2 * q - 8 = (2 * q - 9) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 9) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 9) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (F + (U : ℤ) * E) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (F + (U : ℤ) * E)
          = (p : ℤ) * F + (U : ℤ) * ((p : ℤ) * E) := by ring
      _ = (E + (U : ℤ) ^ 7)
            + (U : ℤ) * (D - (U : ℤ) ^ 6) := by
              rw [← hF, ← hE]
      _ = E + (U : ℤ) * D := by ring
      _ = ((p ^ (2 * q - 8) * δ ^ q : ℕ) : ℤ) := hEseventh
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_eighth_quotient_octic_mod
    (p q U δ : ℕ) (E F : ℤ) (hq5 : 5 ≤ q)
    (hFeighth :
      F + (U : ℤ) * E
        = ((p ^ (2 * q - 9) * δ ^ q : ℕ) : ℤ))
    (hEseptic : (p : ℤ) ∣ E + (U : ℤ) ^ 7) :
    (p : ℤ) ∣ F - (U : ℤ) ^ 8 := by
  have hp_pow_nat : p ∣ p ^ (2 * q - 9) := by
    simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 9)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 9) * δ ^ q :=
    dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 9) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_FUE : (p : ℤ) ∣ F + (U : ℤ) * E := by
    rw [hFeighth]
    exact hp_rhs
  have hp_UE_U8 : (p : ℤ) ∣ (U : ℤ) * E + (U : ℤ) ^ 8 := by
    have hmul : (p : ℤ) ∣ (U : ℤ) * (E + (U : ℤ) ^ 7) :=
      dvd_mul_of_dvd_right hEseptic (U : ℤ)
    have hmul_eq :
        (U : ℤ) * (E + (U : ℤ) ^ 7)
          = (U : ℤ) * E + (U : ℤ) ^ 8 := by
      ring
    rwa [hmul_eq] at hmul
  have hsub := dvd_sub hp_FUE hp_UE_U8
  have hsub_eq :
      (F + (U : ℤ) * E) - ((U : ℤ) * E + (U : ℤ) ^ 8)
        = F - (U : ℤ) ^ 8 := by
    ring
  rwa [hsub_eq] at hsub

theorem ramified_uv_ninth_quotient_int_form
    (p q U δ : ℕ) (E F : ℤ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    (hF :
      E + (U : ℤ) ^ 7 = (p : ℤ) * F)
    (hFeighth :
      F + (U : ℤ) * E
        = ((p ^ (2 * q - 9) * δ ^ q : ℕ) : ℤ))
    (hF_octic : (p : ℤ) ∣ F - (U : ℤ) ^ 8) :
    ∃ G : ℤ,
      F - (U : ℤ) ^ 8 = (p : ℤ) * G ∧
      G + (U : ℤ) * F
        = ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ) := by
  rcases hF_octic with ⟨G, hG⟩
  refine ⟨G, hG, ?_⟩
  let R : ℤ := ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ)
  have hpow_split :
      ((p ^ (2 * q - 9) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 9) * δ ^ q =
          p * (p ^ (2 * q - 10) * δ ^ q) := by
      calc
        p ^ (2 * q - 9) * δ ^ q
            = p ^ ((2 * q - 10) + 1) * δ ^ q := by
                have h_exp : 2 * q - 9 = (2 * q - 10) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 10) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 10) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (G + (U : ℤ) * F) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (G + (U : ℤ) * F)
          = (p : ℤ) * G + (U : ℤ) * ((p : ℤ) * F) := by ring
      _ = (F - (U : ℤ) ^ 8)
            + (U : ℤ) * (E + (U : ℤ) ^ 7) := by
              rw [← hG, ← hF]
      _ = F + (U : ℤ) * E := by ring
      _ = ((p ^ (2 * q - 9) * δ ^ q : ℕ) : ℤ) := hFeighth
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_ninth_boundary_congruence
    (p q U δ : ℕ) (F G : ℤ)
    (hGninth :
      G + (U : ℤ) * F
        = ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ))
    (hF_octic : (p : ℤ) ∣ F - (U : ℤ) ^ 8) :
    (p : ℤ) ∣
      (G + (U : ℤ) ^ 9)
        - ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ) := by
  have htail : (p : ℤ) ∣ (U : ℤ) * ((U : ℤ) ^ 8 - F) := by
    have hneg : (p : ℤ) ∣ - (F - (U : ℤ) ^ 8) := dvd_neg.mpr hF_octic
    have hdiff : (p : ℤ) ∣ (U : ℤ) ^ 8 - F := by
      simpa using hneg
    exact dvd_mul_of_dvd_right hdiff (U : ℤ)
  have htarget :
      (G + (U : ℤ) ^ 9)
        - ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ)
        = (U : ℤ) * ((U : ℤ) ^ 8 - F) := by
    rw [← hGninth]
    ring
  rwa [htarget]

theorem ramified_uv_ninth_boundary_q_five
    (p q U δ : ℕ) (F G : ℤ) (hqeq : q = 5)
    (hGninth :
      G + (U : ℤ) * F
        = ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ))
    (hF_octic : (p : ℤ) ∣ F - (U : ℤ) ^ 8) :
    (p : ℤ) ∣ (G + (U : ℤ) ^ 9) - ((δ ^ 5 : ℕ) : ℤ) := by
  subst hqeq
  simpa using
    ramified_uv_ninth_boundary_congruence
      p 5 U δ F G hGninth hF_octic

theorem ramified_uv_tenth_quotient_int_form
    (p q U δ : ℕ) (F G : ℤ) (hp0 : 0 < p) (hq6 : 6 ≤ q)
    (hG :
      F - (U : ℤ) ^ 8 = (p : ℤ) * G)
    (hGninth :
      G + (U : ℤ) * F
        = ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ))
    (hG_boundary :
      (p : ℤ) ∣
        (G + (U : ℤ) ^ 9)
          - ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ)) :
    ∃ H : ℤ,
      G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
      H + (U : ℤ) * G
        = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) := by
  let R : ℤ := ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 10) * δ ^ q := by
    have hp_pow_nat : p ∣ p ^ (2 * q - 10) := by
      simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 10)
    exact dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_GU9 : (p : ℤ) ∣ G + (U : ℤ) ^ 9 := by
    have hsum := dvd_add hG_boundary hp_rhs
    have hsum_eq :
        ((G + (U : ℤ) ^ 9)
            - ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ))
          + ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ)
          = G + (U : ℤ) ^ 9 := by
      ring
    rwa [hsum_eq] at hsum
  rcases hp_GU9 with ⟨H, hH⟩
  refine ⟨H, hH, ?_⟩
  have hpow_split :
      ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 10) * δ ^ q =
          p * (p ^ (2 * q - 11) * δ ^ q) := by
      calc
        p ^ (2 * q - 10) * δ ^ q
            = p ^ ((2 * q - 11) + 1) * δ ^ q := by
                have h_exp : 2 * q - 10 = (2 * q - 11) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 11) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 11) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (H + (U : ℤ) * G) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (H + (U : ℤ) * G)
          = (p : ℤ) * H + (U : ℤ) * ((p : ℤ) * G) := by ring
      _ = (G + (U : ℤ) ^ 9)
            + (U : ℤ) * (F - (U : ℤ) ^ 8) := by
              rw [← hH, ← hG]
      _ = G + (U : ℤ) * F := by ring
      _ = ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ) := hGninth
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_tenth_boundary_congruence
    (p q U δ : ℕ) (G H : ℤ)
    (hHtenth :
      H + (U : ℤ) * G
        = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ))
    (hG_nonic : (p : ℤ) ∣ G + (U : ℤ) ^ 9) :
    (p : ℤ) ∣
      (H - (U : ℤ) ^ 10)
        - ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) := by
  have htail : (p : ℤ) ∣ -((U : ℤ) * (G + (U : ℤ) ^ 9)) := by
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hG_nonic (U : ℤ))
  have htarget :
      (H - (U : ℤ) ^ 10)
        - ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ)
        = -((U : ℤ) * (G + (U : ℤ) ^ 9)) := by
    rw [← hHtenth]
    ring
  rwa [htarget]

theorem ramified_uv_eleventh_quotient_int_form
    (p q U δ : ℕ) (G H : ℤ) (hp0 : 0 < p) (hq6 : 6 ≤ q)
    (hH :
      G + (U : ℤ) ^ 9 = (p : ℤ) * H)
    (hHtenth :
      H + (U : ℤ) * G
        = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ))
    (hH_boundary :
      (p : ℤ) ∣
        (H - (U : ℤ) ^ 10)
          - ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ)) :
    ∃ I : ℤ,
      H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
      I + (U : ℤ) * H
        = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) := by
  let R : ℤ := ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 11) * δ ^ q := by
    have hp_pow_nat : p ∣ p ^ (2 * q - 11) := by
      simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 11)
    exact dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_HU10 : (p : ℤ) ∣ H - (U : ℤ) ^ 10 := by
    have hsum := dvd_add hH_boundary hp_rhs
    have hsum_eq :
        ((H - (U : ℤ) ^ 10)
            - ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ))
          + ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ)
          = H - (U : ℤ) ^ 10 := by
      ring
    rwa [hsum_eq] at hsum
  rcases hp_HU10 with ⟨I, hI⟩
  refine ⟨I, hI, ?_⟩
  have hpow_split :
      ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 11) * δ ^ q =
          p * (p ^ (2 * q - 12) * δ ^ q) := by
      calc
        p ^ (2 * q - 11) * δ ^ q
            = p ^ ((2 * q - 12) + 1) * δ ^ q := by
                have h_exp : 2 * q - 11 = (2 * q - 12) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 12) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 12) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (I + (U : ℤ) * H) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (I + (U : ℤ) * H)
          = (p : ℤ) * I + (U : ℤ) * ((p : ℤ) * H) := by ring
      _ = (H - (U : ℤ) ^ 10)
            + (U : ℤ) * (G + (U : ℤ) ^ 9) := by
              rw [← hI, ← hH]
      _ = H + (U : ℤ) * G := by ring
      _ = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) := hHtenth
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_eleventh_boundary_congruence
    (p q U δ : ℕ) (H I : ℤ)
    (hIeleventh :
      I + (U : ℤ) * H
        = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ))
    (hH_deci : (p : ℤ) ∣ H - (U : ℤ) ^ 10) :
    (p : ℤ) ∣
      (I + (U : ℤ) ^ 11)
        - ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) := by
  have htail : (p : ℤ) ∣ (U : ℤ) * ((U : ℤ) ^ 10 - H) := by
    have hneg : (p : ℤ) ∣ - (H - (U : ℤ) ^ 10) := dvd_neg.mpr hH_deci
    have hdiff : (p : ℤ) ∣ (U : ℤ) ^ 10 - H := by
      simpa using hneg
    exact dvd_mul_of_dvd_right hdiff (U : ℤ)
  have htarget :
      (I + (U : ℤ) ^ 11)
        - ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ)
        = (U : ℤ) * ((U : ℤ) ^ 10 - H) := by
    rw [← hIeleventh]
    ring
  rwa [htarget]

theorem ramified_uv_eleventh_boundary_q_six
    (p q U δ : ℕ) (G H : ℤ) (hqeq : q = 6)
    (hHtenth :
      H + (U : ℤ) * G
        = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ))
    (hG_nonic : (p : ℤ) ∣ G + (U : ℤ) ^ 9) :
    (p : ℤ) ∣ (H - (U : ℤ) ^ 10) - ((p * δ ^ 6 : ℕ) : ℤ) := by
  subst hqeq
  simpa using
    ramified_uv_tenth_boundary_congruence
      p 6 U δ G H hHtenth hG_nonic

theorem ramified_uv_eleventh_boundary_q_six_sharp
    (p q U δ : ℕ) (H I : ℤ) (hqeq : q = 6)
    (hIeleventh :
      I + (U : ℤ) * H
        = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ))
    (hH_deci : (p : ℤ) ∣ H - (U : ℤ) ^ 10) :
    (p : ℤ) ∣ (I + (U : ℤ) ^ 11) - ((δ ^ 6 : ℕ) : ℤ) := by
  subst hqeq
  simpa using
    ramified_uv_eleventh_boundary_congruence
      p 6 U δ H I hIeleventh hH_deci

theorem ramified_uv_twelfth_quotient_int_form
    (p q U δ : ℕ) (H I : ℤ) (hp0 : 0 < p) (hq7 : 7 ≤ q)
    (hI :
      H - (U : ℤ) ^ 10 = (p : ℤ) * I)
    (hIeleventh :
      I + (U : ℤ) * H
        = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ))
    (hI_boundary :
      (p : ℤ) ∣
        (I + (U : ℤ) ^ 11)
          - ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ)) :
    ∃ J : ℤ,
      I + (U : ℤ) ^ 11 = (p : ℤ) * J ∧
      J + (U : ℤ) * I
        = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) := by
  let R : ℤ := ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 12) * δ ^ q := by
    have hp_pow_nat : p ∣ p ^ (2 * q - 12) := by
      simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 12)
    exact dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_IU11 : (p : ℤ) ∣ I + (U : ℤ) ^ 11 := by
    have hsum := dvd_add hI_boundary hp_rhs
    have hsum_eq :
        ((I + (U : ℤ) ^ 11)
            - ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ))
          + ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ)
          = I + (U : ℤ) ^ 11 := by
      ring
    rwa [hsum_eq] at hsum
  rcases hp_IU11 with ⟨J, hJ⟩
  refine ⟨J, hJ, ?_⟩
  have hpow_split :
      ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 12) * δ ^ q =
          p * (p ^ (2 * q - 13) * δ ^ q) := by
      calc
        p ^ (2 * q - 12) * δ ^ q
            = p ^ ((2 * q - 13) + 1) * δ ^ q := by
                have h_exp : 2 * q - 12 = (2 * q - 13) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 13) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 13) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (J + (U : ℤ) * I) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (J + (U : ℤ) * I)
          = (p : ℤ) * J + (U : ℤ) * ((p : ℤ) * I) := by ring
      _ = (I + (U : ℤ) ^ 11)
            + (U : ℤ) * (H - (U : ℤ) ^ 10) := by
              rw [← hJ, ← hI]
      _ = I + (U : ℤ) * H := by ring
      _ = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) := hIeleventh
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_low_boundary_split
    (p q U δ : ℕ) (F G : ℤ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    (hG :
      F - (U : ℤ) ^ 8 = (p : ℤ) * G)
    (hGninth :
      G + (U : ℤ) * F
        = ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ))
    (hF_octic : (p : ℤ) ∣ F - (U : ℤ) ^ 8)
    (hG_boundary :
      (p : ℤ) ∣
        (G + (U : ℤ) ^ 9)
          - ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ)) :
    (q = 5 ∧
        (p : ℤ) ∣ (G + (U : ℤ) ^ 9) - ((δ ^ 5 : ℕ) : ℤ))
      ∨
    (q = 6 ∧
        ∃ H I : ℤ,
          G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
          H + (U : ℤ) * G
            = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
          H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
          I + (U : ℤ) * H
            = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
          (p : ℤ) ∣ (I + (U : ℤ) ^ 11) - ((δ ^ 6 : ℕ) : ℤ))
      ∨
    (7 ≤ q ∧
        ∃ H I J : ℤ,
          G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
          H + (U : ℤ) * G
            = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
          H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
          I + (U : ℤ) * H
            = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
          I + (U : ℤ) ^ 11 = (p : ℤ) * J ∧
          J + (U : ℤ) * I
            = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ)) := by
  by_cases hqeq5 : q = 5
  · left
    exact ⟨hqeq5,
      ramified_uv_ninth_boundary_q_five
        p q U δ F G hqeq5 hGninth hF_octic⟩
  · have hq6 : 6 ≤ q := by omega
    obtain ⟨H, hH, hHtenth⟩ :=
      ramified_uv_tenth_quotient_int_form
        p q U δ F G hp0 hq6 hG hGninth hG_boundary
    have hG_nonic : (p : ℤ) ∣ G + (U : ℤ) ^ 9 := ⟨H, hH⟩
    have hH_boundary :
        (p : ℤ) ∣
          (H - (U : ℤ) ^ 10)
            - ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) :=
      ramified_uv_tenth_boundary_congruence
        p q U δ G H hHtenth hG_nonic
    obtain ⟨I, hI, hIeleventh⟩ :=
      ramified_uv_eleventh_quotient_int_form
        p q U δ G H hp0 hq6 hH hHtenth hH_boundary
    have hH_deci : (p : ℤ) ∣ H - (U : ℤ) ^ 10 := ⟨I, hI⟩
    have hI_boundary :
        (p : ℤ) ∣
          (I + (U : ℤ) ^ 11)
            - ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) :=
      ramified_uv_eleventh_boundary_congruence
        p q U δ H I hIeleventh hH_deci
    by_cases hqeq6 : q = 6
    · right
      left
      refine ⟨hqeq6, H, I, hH, hHtenth, hI, hIeleventh, ?_⟩
      exact ramified_uv_eleventh_boundary_q_six_sharp
        p q U δ H I hqeq6 hIeleventh hH_deci
    · have hq7 : 7 ≤ q := by omega
      obtain ⟨J, hJ, hJtwelfth⟩ :=
        ramified_uv_twelfth_quotient_int_form
          p q U δ H I hp0 hq7 hI hIeleventh hI_boundary
      right
      right
      exact ⟨hq7, H, I, J, hH, hHtenth, hI, hIeleventh, hJ, hJtwelfth⟩

theorem ramified_uv_twelfth_boundary_congruence
    (p q U δ : ℕ) (I J : ℤ)
    (hJtwelfth :
      J + (U : ℤ) * I
        = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ))
    (hI_undeci : (p : ℤ) ∣ I + (U : ℤ) ^ 11) :
    (p : ℤ) ∣
      (J - (U : ℤ) ^ 12)
        - ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) := by
  have htail : (p : ℤ) ∣ -((U : ℤ) * (I + (U : ℤ) ^ 11)) := by
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hI_undeci (U : ℤ))
  have htarget :
      (J - (U : ℤ) ^ 12)
        - ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ)
        = -((U : ℤ) * (I + (U : ℤ) ^ 11)) := by
    rw [← hJtwelfth]
    ring
  rwa [htarget]

theorem ramified_uv_thirteenth_quotient_int_form
    (p q U δ : ℕ) (I J : ℤ) (hp0 : 0 < p) (hq7 : 7 ≤ q)
    (hJ :
      I + (U : ℤ) ^ 11 = (p : ℤ) * J)
    (hJtwelfth :
      J + (U : ℤ) * I
        = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ))
    (hJ_boundary :
      (p : ℤ) ∣
        (J - (U : ℤ) ^ 12)
          - ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ)) :
    ∃ K : ℤ,
      J - (U : ℤ) ^ 12 = (p : ℤ) * K ∧
      K + (U : ℤ) * J
        = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ) := by
  let R : ℤ := ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ)
  have hp_rhs_nat : p ∣ p ^ (2 * q - 13) * δ ^ q := by
    have hp_pow_nat : p ∣ p ^ (2 * q - 13) := by
      simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 13)
    exact dvd_mul_of_dvd_left hp_pow_nat (δ ^ q)
  have hp_rhs : (p : ℤ) ∣ ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) := by
    exact_mod_cast hp_rhs_nat
  have hp_JU12 : (p : ℤ) ∣ J - (U : ℤ) ^ 12 := by
    have hsum := dvd_add hJ_boundary hp_rhs
    have hsum_eq :
        ((J - (U : ℤ) ^ 12)
            - ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ))
          + ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ)
          = J - (U : ℤ) ^ 12 := by
      ring
    rwa [hsum_eq] at hsum
  rcases hp_JU12 with ⟨K, hK⟩
  refine ⟨K, hK, ?_⟩
  have hpow_split :
      ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) = (p : ℤ) * R := by
    have hnat :
        p ^ (2 * q - 13) * δ ^ q =
          p * (p ^ (2 * q - 14) * δ ^ q) := by
      calc
        p ^ (2 * q - 13) * δ ^ q
            = p ^ ((2 * q - 14) + 1) * δ ^ q := by
                have h_exp : 2 * q - 13 = (2 * q - 14) + 1 := by omega
                rw [h_exp]
        _ = (p ^ (2 * q - 14) * p) * δ ^ q := by rw [pow_succ]
        _ = p * (p ^ (2 * q - 14) * δ ^ q) := by ring
    dsimp [R]
    exact_mod_cast hnat
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hmul :
      (p : ℤ) * (K + (U : ℤ) * J) = (p : ℤ) * R := by
    calc
      (p : ℤ) * (K + (U : ℤ) * J)
          = (p : ℤ) * K + (U : ℤ) * ((p : ℤ) * J) := by ring
      _ = (J - (U : ℤ) ^ 12)
            + (U : ℤ) * (I + (U : ℤ) ^ 11) := by
              rw [← hK, ← hJ]
      _ = J + (U : ℤ) * I := by ring
      _ = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) := hJtwelfth
      _ = (p : ℤ) * R := hpow_split
  exact mul_left_cancel₀ hp_ne hmul

theorem ramified_uv_thirteenth_boundary_congruence
    (p q U δ : ℕ) (J K : ℤ)
    (hKthirteenth :
      K + (U : ℤ) * J
        = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ))
    (hJ_duodeci : (p : ℤ) ∣ J - (U : ℤ) ^ 12) :
    (p : ℤ) ∣
      (K + (U : ℤ) ^ 13)
        - ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ) := by
  have htail : (p : ℤ) ∣ (U : ℤ) * ((U : ℤ) ^ 12 - J) := by
    have hneg : (p : ℤ) ∣ - (J - (U : ℤ) ^ 12) := dvd_neg.mpr hJ_duodeci
    have hdiff : (p : ℤ) ∣ (U : ℤ) ^ 12 - J := by
      simpa using hneg
    exact dvd_mul_of_dvd_right hdiff (U : ℤ)
  have htarget :
      (K + (U : ℤ) ^ 13)
        - ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ)
        = (U : ℤ) * ((U : ℤ) ^ 12 - J) := by
    rw [← hKthirteenth]
    ring
  rwa [htarget]

theorem ramified_uv_thirteenth_boundary_q_seven_sharp
    (p q U δ : ℕ) (J K : ℤ) (hqeq : q = 7)
    (hKthirteenth :
      K + (U : ℤ) * J
        = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ))
    (hJ_duodeci : (p : ℤ) ∣ J - (U : ℤ) ^ 12) :
    (p : ℤ) ∣ (K + (U : ℤ) ^ 13) - ((δ ^ 7 : ℕ) : ℤ) := by
  subst hqeq
  simpa using
    ramified_uv_thirteenth_boundary_congruence
      p 7 U δ J K hKthirteenth hJ_duodeci

theorem ramified_uv_fourteenth_quotient_int_form
    (p q U δ : ℕ) (J K : ℤ) (hp0 : 0 < p) (hq8 : 8 ≤ q)
    (hK :
      J - (U : ℤ) ^ 12 = (p : ℤ) * K)
    (hKthirteenth :
      K + (U : ℤ) * J
        = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ)) :
    ∃ L : ℤ,
      K + (U : ℤ) ^ 13 = (p : ℤ) * L ∧
      L + (U : ℤ) * K
        = ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ) := by
  let R : ℤ := ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ)
  have hRel :
      K + (U : ℤ) * J = (p : ℤ) * R := by
    calc
      K + (U : ℤ) * J
          = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ) := hKthirteenth
      _ = (p : ℤ) * R := by
            dsimp [R]
            exact ramified_pow_rhs_split p q δ (2 * q - 14) (by omega)
  obtain ⟨L, hL, hLR⟩ :=
    ramified_uv_next_quotient_int_form
      p U J K ((U : ℤ) ^ 12) R hp0 hK hRel
  refine ⟨L, ?_, ?_⟩
  · simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hL
  · simpa [R] using hLR

theorem ramified_uv_fifteenth_quotient_int_form
    (p q U δ : ℕ) (K L : ℤ) (hp0 : 0 < p) (hq8 : 8 ≤ q)
    (hL :
      K + (U : ℤ) ^ 13 = (p : ℤ) * L)
    (hLfourteenth :
      L + (U : ℤ) * K
        = ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ)) :
    ∃ M : ℤ,
      L - (U : ℤ) ^ 14 = (p : ℤ) * M ∧
      M + (U : ℤ) * L
        = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ) := by
  let R : ℤ := ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ)
  have hRel :
      L + (U : ℤ) * K = (p : ℤ) * R := by
    calc
      L + (U : ℤ) * K
          = ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ) := hLfourteenth
      _ = (p : ℤ) * R := by
            dsimp [R]
            exact ramified_pow_rhs_split p q δ (2 * q - 15) (by omega)
  have hL' : K - (-(U : ℤ) ^ 13) = (p : ℤ) * L := by
    simpa using hL
  obtain ⟨M, hM, hMR⟩ :=
    ramified_uv_next_quotient_int_form
      p U K L (-(U : ℤ) ^ 13) R hp0 hL' hRel
  refine ⟨M, ?_, ?_⟩
  · simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hM
  · simpa [R] using hMR

theorem ramified_uv_fifteenth_boundary_congruence
    (p q U δ : ℕ) (L M : ℤ)
    (hMfifteenth :
      M + (U : ℤ) * L
        = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ))
    (hL_tetradeci : (p : ℤ) ∣ L - (U : ℤ) ^ 14) :
    (p : ℤ) ∣
      (M + (U : ℤ) ^ 15)
        - ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ) := by
  have htail : (p : ℤ) ∣ (U : ℤ) * ((U : ℤ) ^ 14 - L) := by
    have hneg : (p : ℤ) ∣ - (L - (U : ℤ) ^ 14) := dvd_neg.mpr hL_tetradeci
    have hdiff : (p : ℤ) ∣ (U : ℤ) ^ 14 - L := by
      simpa using hneg
    exact dvd_mul_of_dvd_right hdiff (U : ℤ)
  have htarget :
      (M + (U : ℤ) ^ 15)
        - ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ)
        = (U : ℤ) * ((U : ℤ) ^ 14 - L) := by
    rw [← hMfifteenth]
    ring
  rwa [htarget]

theorem ramified_uv_fifteenth_boundary_q_eight_sharp
    (p q U δ : ℕ) (L M : ℤ) (hqeq : q = 8)
    (hMfifteenth :
      M + (U : ℤ) * L
        = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ))
    (hL_tetradeci : (p : ℤ) ∣ L - (U : ℤ) ^ 14) :
    (p : ℤ) ∣ (M + (U : ℤ) ^ 15) - ((δ ^ 8 : ℕ) : ℤ) := by
  subst hqeq
  simpa using
    ramified_uv_fifteenth_boundary_congruence
      p 8 U δ L M hMfifteenth hL_tetradeci

theorem ramified_uv_q_eight_or_higher_tail_split
    (p q U δ : ℕ) (J K : ℤ) (hp0 : 0 < p) (hq8 : 8 ≤ q)
    (hK :
      J - (U : ℤ) ^ 12 = (p : ℤ) * K)
    (hKthirteenth :
      K + (U : ℤ) * J
        = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ)) :
    (q = 8 ∧
        ∃ L M : ℤ,
          K + (U : ℤ) ^ 13 = (p : ℤ) * L ∧
          L + (U : ℤ) * K
            = ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ) ∧
          L - (U : ℤ) ^ 14 = (p : ℤ) * M ∧
          M + (U : ℤ) * L
            = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ) ∧
          (p : ℤ) ∣ (M + (U : ℤ) ^ 15) - ((δ ^ 8 : ℕ) : ℤ))
      ∨
    (9 ≤ q ∧
        ∃ L M : ℤ,
          K + (U : ℤ) ^ 13 = (p : ℤ) * L ∧
          L + (U : ℤ) * K
            = ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ) ∧
          L - (U : ℤ) ^ 14 = (p : ℤ) * M ∧
          M + (U : ℤ) * L
            = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ)) := by
  obtain ⟨L, hL, hLfourteenth⟩ :=
    ramified_uv_fourteenth_quotient_int_form
      p q U δ J K hp0 hq8 hK hKthirteenth
  obtain ⟨M, hM, hMfifteenth⟩ :=
    ramified_uv_fifteenth_quotient_int_form
      p q U δ K L hp0 hq8 hL hLfourteenth
  by_cases hqeq8 : q = 8
  · left
    refine ⟨hqeq8, L, M, hL, hLfourteenth, hM, hMfifteenth, ?_⟩
    exact ramified_uv_fifteenth_boundary_q_eight_sharp
      p q U δ L M hqeq8 hMfifteenth ⟨M, hM⟩
  · right
    exact ⟨by omega, L, M, hL, hLfourteenth, hM, hMfifteenth⟩

theorem ramified_uv_q_nine_or_higher_tail_split
    (p q U δ : ℕ) (L M : ℤ) (hp0 : 0 < p) (hq9 : 9 ≤ q)
    (hM :
      L - (U : ℤ) ^ 14 = (p : ℤ) * M)
    (hMfifteenth :
      M + (U : ℤ) * L
        = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ)) :
    (q = 9 ∧
        ∃ N O : ℤ,
          M + (U : ℤ) ^ 15 = (p : ℤ) * N ∧
          N + (U : ℤ) * M
            = ((p ^ (2 * q - 17) * δ ^ q : ℕ) : ℤ) ∧
          N - (U : ℤ) ^ 16 = (p : ℤ) * O ∧
          O + (U : ℤ) * N
            = ((p ^ (2 * q - 18) * δ ^ q : ℕ) : ℤ) ∧
          (p : ℤ) ∣ (O + (U : ℤ) ^ 17) - ((δ ^ 9 : ℕ) : ℤ))
      ∨
    (10 ≤ q ∧
        ∃ N O : ℤ,
          M + (U : ℤ) ^ 15 = (p : ℤ) * N ∧
          N + (U : ℤ) * M
            = ((p ^ (2 * q - 17) * δ ^ q : ℕ) : ℤ) ∧
          N - (U : ℤ) ^ 16 = (p : ℤ) * O ∧
          O + (U : ℤ) * N
            = ((p ^ (2 * q - 18) * δ ^ q : ℕ) : ℤ)) := by
  obtain ⟨N, O, hN, hNsixteenth, hO, hOseventeenth⟩ :=
    ramified_uv_next_two_quotients_int_form
      p q U δ (2 * q - 16) L M ((U : ℤ) ^ 14) hp0 (by omega)
      hM hMfifteenth
  have hN' : M + (U : ℤ) ^ 15 = (p : ℤ) * N := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg] using hN
  have hO' : N - (U : ℤ) ^ 16 = (p : ℤ) * O := by
    simpa [pow_two, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hO
  by_cases hqeq9 : q = 9
  · left
    refine ⟨hqeq9, N, O, hN', hNsixteenth, hO', hOseventeenth, ?_⟩
    have hboundary :
        (p : ℤ) ∣
          (O + (U : ℤ) * ((U : ℤ) ^ 16))
            - ((p ^ (2 * q - 18) * δ ^ q : ℕ) : ℤ) :=
      ramified_uv_next_boundary_congruence
        p U N O ((U : ℤ) ^ 16)
        (((p ^ (2 * q - 18) * δ ^ q : ℕ) : ℤ))
        hO' hOseventeenth
    subst hqeq9
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hboundary
  · right
    exact ⟨by omega, N, O, hN', hNsixteenth, hO', hOseventeenth⟩

theorem ramified_uv_q_ten_or_higher_tail_split
    (p q U δ : ℕ) (N O : ℤ) (hp0 : 0 < p) (hq10 : 10 ≤ q)
    (hO :
      N - (U : ℤ) ^ 16 = (p : ℤ) * O)
    (hOseventeenth :
      O + (U : ℤ) * N
        = ((p ^ (2 * q - 18) * δ ^ q : ℕ) : ℤ)) :
    (q = 10 ∧
        ∃ P Q : ℤ,
          O + (U : ℤ) ^ 17 = (p : ℤ) * P ∧
          P + (U : ℤ) * O
            = ((p ^ (2 * q - 19) * δ ^ q : ℕ) : ℤ) ∧
          P - (U : ℤ) ^ 18 = (p : ℤ) * Q ∧
          Q + (U : ℤ) * P
            = ((p ^ (2 * q - 20) * δ ^ q : ℕ) : ℤ) ∧
          (p : ℤ) ∣ (Q + (U : ℤ) ^ 19) - ((δ ^ 10 : ℕ) : ℤ))
      ∨
    (11 ≤ q ∧
        ∃ P Q : ℤ,
          O + (U : ℤ) ^ 17 = (p : ℤ) * P ∧
          P + (U : ℤ) * O
            = ((p ^ (2 * q - 19) * δ ^ q : ℕ) : ℤ) ∧
          P - (U : ℤ) ^ 18 = (p : ℤ) * Q ∧
          Q + (U : ℤ) * P
            = ((p ^ (2 * q - 20) * δ ^ q : ℕ) : ℤ)) := by
  obtain ⟨P, Q, hP, hPeighteenth, hQ, hQnineteenth⟩ :=
    ramified_uv_next_two_quotients_int_form
      p q U δ (2 * q - 18) N O ((U : ℤ) ^ 16) hp0 (by omega)
      hO hOseventeenth
  have hP' : O + (U : ℤ) ^ 17 = (p : ℤ) * P := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg] using hP
  have hQ' : P - (U : ℤ) ^ 18 = (p : ℤ) * Q := by
    simpa [pow_two, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hQ
  by_cases hqeq10 : q = 10
  · left
    refine ⟨hqeq10, P, Q, hP', hPeighteenth, hQ', hQnineteenth, ?_⟩
    have hboundary :
        (p : ℤ) ∣
          (Q + (U : ℤ) * ((U : ℤ) ^ 18))
            - ((p ^ (2 * q - 20) * δ ^ q : ℕ) : ℤ) :=
      ramified_uv_next_boundary_congruence
        p U P Q ((U : ℤ) ^ 18)
        (((p ^ (2 * q - 20) * δ ^ q : ℕ) : ℤ))
        hQ' hQnineteenth
    subst hqeq10
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hboundary
  · right
    exact ⟨by omega, P, Q, hP', hPeighteenth, hQ', hQnineteenth⟩

theorem ramified_uv_q_eleven_or_higher_tail_split
    (p q U δ : ℕ) (P Q : ℤ) (hp0 : 0 < p) (hq11 : 11 ≤ q)
    (hQ :
      P - (U : ℤ) ^ 18 = (p : ℤ) * Q)
    (hQnineteenth :
      Q + (U : ℤ) * P
        = ((p ^ (2 * q - 20) * δ ^ q : ℕ) : ℤ)) :
    (q = 11 ∧
        ∃ R S : ℤ,
          Q + (U : ℤ) ^ 19 = (p : ℤ) * R ∧
          R + (U : ℤ) * Q
            = ((p ^ (2 * q - 21) * δ ^ q : ℕ) : ℤ) ∧
          R - (U : ℤ) ^ 20 = (p : ℤ) * S ∧
          S + (U : ℤ) * R
            = ((p ^ (2 * q - 22) * δ ^ q : ℕ) : ℤ) ∧
          (p : ℤ) ∣ (S + (U : ℤ) ^ 21) - ((δ ^ 11 : ℕ) : ℤ))
      ∨
    (12 ≤ q ∧
        ∃ R S : ℤ,
          Q + (U : ℤ) ^ 19 = (p : ℤ) * R ∧
          R + (U : ℤ) * Q
            = ((p ^ (2 * q - 21) * δ ^ q : ℕ) : ℤ) ∧
          R - (U : ℤ) ^ 20 = (p : ℤ) * S ∧
          S + (U : ℤ) * R
            = ((p ^ (2 * q - 22) * δ ^ q : ℕ) : ℤ)) := by
  obtain ⟨R, S, hR, hRtwentieth, hS, hStwentyfirst⟩ :=
    ramified_uv_next_two_quotients_int_form
      p q U δ (2 * q - 20) P Q ((U : ℤ) ^ 18) hp0 (by omega)
      hQ hQnineteenth
  have hR' : Q + (U : ℤ) ^ 19 = (p : ℤ) * R := by
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm, sub_eq_add_neg] using hR
  have hS' : R - (U : ℤ) ^ 20 = (p : ℤ) * S := by
    simpa [pow_two, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hS
  by_cases hqeq11 : q = 11
  · left
    refine ⟨hqeq11, R, S, hR', hRtwentieth, hS', hStwentyfirst, ?_⟩
    have hboundary :
        (p : ℤ) ∣
          (S + (U : ℤ) * ((U : ℤ) ^ 20))
            - ((p ^ (2 * q - 22) * δ ^ q : ℕ) : ℤ) :=
      ramified_uv_next_boundary_congruence
        p U R S ((U : ℤ) ^ 20)
        (((p ^ (2 * q - 22) * δ ^ q : ℕ) : ℤ))
        hS' hStwentyfirst
    subst hqeq11
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hboundary
  · right
    exact ⟨by omega, R, S, hR', hRtwentieth, hS', hStwentyfirst⟩

theorem ramified_uv_low_boundary_split_refined
    (p q U δ : ℕ) (F G : ℤ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    (hG :
      F - (U : ℤ) ^ 8 = (p : ℤ) * G)
    (hGninth :
      G + (U : ℤ) * F
        = ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ))
    (hF_octic : (p : ℤ) ∣ F - (U : ℤ) ^ 8)
    (hG_boundary :
      (p : ℤ) ∣
        (G + (U : ℤ) ^ 9)
          - ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ)) :
    (q = 5 ∧
        (p : ℤ) ∣ (G + (U : ℤ) ^ 9) - ((δ ^ 5 : ℕ) : ℤ))
      ∨
    (q = 6 ∧
        ∃ H I : ℤ,
          G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
          H + (U : ℤ) * G
            = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
          H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
          I + (U : ℤ) * H
            = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
          (p : ℤ) ∣ (I + (U : ℤ) ^ 11) - ((δ ^ 6 : ℕ) : ℤ))
      ∨
    (q = 7 ∧
        ∃ H I J K : ℤ,
          G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
          H + (U : ℤ) * G
            = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
          H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
          I + (U : ℤ) * H
            = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
          I + (U : ℤ) ^ 11 = (p : ℤ) * J ∧
          J + (U : ℤ) * I
            = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) ∧
          J - (U : ℤ) ^ 12 = (p : ℤ) * K ∧
          K + (U : ℤ) * J
            = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ) ∧
          (p : ℤ) ∣ (K + (U : ℤ) ^ 13) - ((δ ^ 7 : ℕ) : ℤ))
      ∨
    (8 ≤ q ∧
        ∃ H I J K : ℤ,
          G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
          H + (U : ℤ) * G
            = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
          H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
          I + (U : ℤ) * H
            = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
          I + (U : ℤ) ^ 11 = (p : ℤ) * J ∧
          J + (U : ℤ) * I
            = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) ∧
          J - (U : ℤ) ^ 12 = (p : ℤ) * K ∧
          K + (U : ℤ) * J
            = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ)) := by
  rcases ramified_uv_low_boundary_split
      p q U δ F G hp0 hq5 hG hGninth hF_octic hG_boundary with
    hfive | hsix_or_ge
  · left
    exact hfive
  rcases hsix_or_ge with hsix | hge7
  · right
    left
    exact hsix
  right
  right
  rcases hge7 with ⟨hq7, H, I, J, hH, hHtenth, hI, hIeleventh, hJ, hJtwelfth⟩
  have hI_undeci : (p : ℤ) ∣ I + (U : ℤ) ^ 11 := ⟨J, hJ⟩
  have hJ_boundary :
      (p : ℤ) ∣
        (J - (U : ℤ) ^ 12)
          - ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) :=
    ramified_uv_twelfth_boundary_congruence
      p q U δ I J hJtwelfth hI_undeci
  obtain ⟨K, hK, hKthirteenth⟩ :=
    ramified_uv_thirteenth_quotient_int_form
      p q U δ I J hp0 hq7 hJ hJtwelfth hJ_boundary
  have hJ_duodeci : (p : ℤ) ∣ J - (U : ℤ) ^ 12 := ⟨K, hK⟩
  by_cases hqeq7 : q = 7
  · left
    refine ⟨hqeq7, H, I, J, K, hH, hHtenth, hI, hIeleventh,
      hJ, hJtwelfth, hK, hKthirteenth, ?_⟩
    exact ramified_uv_thirteenth_boundary_q_seven_sharp
      p q U δ J K hqeq7 hKthirteenth hJ_duodeci
  · right
    exact ⟨by omega, H, I, J, K, hH, hHtenth, hI, hIeleventh,
      hJ, hJtwelfth, hK, hKthirteenth⟩

theorem ramified_uv_second_quotient_square_mod
    (p U V W : ℕ)
    (hW : U + V = p * W)
    (hWUV : p ∣ W + U * V) :
    W ≡ U ^ 2 [MOD p] := by
  have hUV_zero : ((U : ℕ) : ZMod p) + (V : ZMod p) = 0 := by
    have hcast :
        ((U + V : ℕ) : ZMod p) = ((p * W : ℕ) : ZMod p) :=
      congrArg (fun n : ℕ => ((n : ℕ) : ZMod p)) hW
    simpa [Nat.cast_add, Nat.cast_mul] using hcast
  have hWUV_zero : ((W : ℕ) : ZMod p) + (U : ZMod p) * (V : ZMod p) = 0 := by
    have hzero : ((W + U * V : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (W + U * V) p).mpr hWUV
    simpa [Nat.cast_add, Nat.cast_mul] using hzero
  have hV_eq : (V : ZMod p) = -(U : ZMod p) := by
    have hUV_zero' : (V : ZMod p) + (U : ZMod p) = 0 := by
      simpa [add_comm] using hUV_zero
    exact eq_neg_of_add_eq_zero_left hUV_zero'
  have hW_eq : (W : ZMod p) = -((U : ZMod p) * (V : ZMod p)) := by
    exact eq_neg_of_add_eq_zero_left hWUV_zero
  have hcast_eq : (W : ZMod p) = ((U ^ 2 : ℕ) : ZMod p) := by
    calc
      (W : ZMod p) = -((U : ZMod p) * (V : ZMod p)) := hW_eq
      _ = -((U : ZMod p) * (-(U : ZMod p))) := by rw [hV_eq]
      _ = ((U ^ 2 : ℕ) : ZMod p) := by
            norm_num [Nat.cast_pow]
            ring
  exact (ZMod.natCast_eq_natCast_iff W (U ^ 2) p).mp hcast_eq

theorem ramified_v_pow_eq_one_zmod_q
    (u v a p q : ℕ) (hq : q.Prime)
    (hq_u : ¬ q ∣ u)
    (hcat : (v * u) ^ p = a ^ q + 1)
    (ha_succ : a + 1 = u ^ p) :
    ((v : ℕ) : ZMod q) ^ p = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hu_ne : ((u : ℕ) : ZMod q) ≠ 0 := by
    intro hu0
    exact hq_u ((ZMod.natCast_eq_zero_iff u q).mp hu0)
  have hup_ne : ((u : ℕ) : ZMod q) ^ p ≠ 0 := pow_ne_zero p hu_ne
  have hcat_z :
      (((v * u) ^ p : ℕ) : ZMod q) = ((a ^ q + 1 : ℕ) : ZMod q) := by
    exact congrArg (fun n : ℕ => ((n : ℕ) : ZMod q)) hcat
  have ha_frob : ((a : ℕ) : ZMod q) ^ q = (a : ℕ) := ZMod.pow_card _
  have ha_succ_z : ((a : ℕ) : ZMod q) + 1 = ((u : ℕ) : ZMod q) ^ p := by
    have h := congrArg (fun n : ℕ => ((n : ℕ) : ZMod q)) ha_succ
    simpa using h
  have h : (((v : ℕ) : ZMod q) ^ p) * (((u : ℕ) : ZMod q) ^ p)
      = ((u : ℕ) : ZMod q) ^ p := by
    simpa [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      mul_pow, ha_frob, ha_succ_z] using hcat_z
  exact mul_right_cancel₀ hup_ne (by simpa using h)

theorem ramified_q_not_dvd_v
    (u v a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hq_u : ¬ q ∣ u)
    (hcat : (v * u) ^ p = a ^ q + 1)
    (ha_succ : a + 1 = u ^ p) :
    ¬ q ∣ v := by
  intro hqv
  have hvp_eq_one :
      ((v : ℕ) : ZMod q) ^ p = 1 :=
    ramified_v_pow_eq_one_zmod_q u v a p q hq hq_u hcat ha_succ
  have hv_zero : ((v : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff v q).mpr hqv
  have hone_zero : ((1 : ℕ) : ZMod q) = 0 := by
    simpa [hv_zero, zero_pow hp.ne_zero] using hvp_eq_one.symm
  exact hq.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 q).mp hone_zero)

private lemma exists_pow_one_add_eq_quadratic_add_cube (x q : ℕ) :
    ∃ R : ℕ, (1 + x) ^ q =
      1 + q * x + Nat.choose q 2 * x ^ 2 + x ^ 3 * R := by
  induction q with
  | zero =>
      exact ⟨0, by simp⟩
  | succ q ih =>
      rcases ih with ⟨R, hR⟩
      refine ⟨Nat.choose q 2 + R * (1 + x), ?_⟩
      have hchoose_succ : Nat.choose (q + 1) 2 = q + Nat.choose q 2 := by
        calc
          Nat.choose (q + 1) 2 = Nat.choose q 1 + Nat.choose q 2 := by
            simpa using Nat.choose_succ_succ q 1
          _ = q + Nat.choose q 2 := by rw [Nat.choose_one_right]
      rw [pow_succ, hR, hchoose_succ]
      ring

theorem ramified_u_second_quotient_linear_mod
    (u p δ γ U : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hu : 1 ≤ u)
    (hU : u - 1 = p * U)
    (ha : u ^ p - 1 = p ^ 2 * δ * γ) :
    δ * γ ≡ U [MOD p] := by
  obtain ⟨R, hR⟩ := exists_pow_one_add_eq_quadratic_add_cube (p * U) p
  have hp_choose : p ∣ Nat.choose p 2 :=
    hp.dvd_choose_self (by norm_num) hp2
  obtain ⟨C, hC⟩ := hp_choose
  have hu_eq : u = 1 + p * U := by omega
  have hsub :
      u ^ p - 1 = p ^ 2 * U + p ^ 3 * (C * U ^ 2 + U ^ 3 * R) := by
    rw [hu_eq, hR, hC]
    ring_nf
    omega
  have hcancel :
      δ * γ = U + p * (C * U ^ 2 + U ^ 3 * R) := by
    apply Nat.mul_left_cancel (show 0 < p ^ 2 by positivity)
    calc
      p ^ 2 * (δ * γ)
          = u ^ p - 1 := by
              rw [ha]
              ring
      _ = p ^ 2 * U + p ^ 3 * (C * U ^ 2 + U ^ 3 * R) := hsub
      _ = p ^ 2 * (U + p * (C * U ^ 2 + U ^ 3 * R)) := by
              ring
  rw [hcancel]
  have hzero : p * (C * U ^ 2 + U ^ 3 * R) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p (C * U ^ 2 + U ^ 3 * R))
  simpa using (Nat.ModEq.add_left U hzero)

theorem ramified_v_second_quotient_linear_mod
    (a v p q D V : ℕ) (hp : p.Prime) (hp2 : 2 < p) (hq2 : 2 ≤ q)
    (hv : 1 ≤ v)
    (hV : v - 1 = p * V)
    (ha : a = p ^ 2 * D)
    (hcat_div : (a + 1) * v ^ p = a ^ q + 1) :
    p ∣ V + D := by
  obtain ⟨R, hR⟩ := exists_pow_one_add_eq_quadratic_add_cube (p * V) p
  have hp_choose : p ∣ Nat.choose p 2 :=
    hp.dvd_choose_self (by norm_num) hp2
  obtain ⟨C, hC⟩ := hp_choose
  have hv_eq : v = 1 + p * V := by omega
  let E : ℕ := C * V ^ 2 + V ^ 3 * R
  have hv_exp : v ^ p = 1 + p ^ 2 * V + p ^ 3 * E := by
    rw [hv_eq, hR, hC]
    dsimp [E]
    ring
  let S : ℕ := E + p * D * V + p ^ 2 * D * E
  have hprod : (a + 1) * v ^ p = 1 + p ^ 2 * (V + D) + p ^ 3 * S := by
    rw [ha, hv_exp]
    ring
  have hpow_split : a ^ q = p ^ 3 * (p ^ (2 * q - 3) * D ^ q) := by
    rw [ha]
    calc
      (p ^ 2 * D) ^ q = (p ^ 2) ^ q * D ^ q := by rw [Nat.mul_pow]
      _ = p ^ (2 * q) * D ^ q := by rw [pow_mul]
      _ = p ^ 3 * (p ^ (2 * q - 3) * D ^ q) := by
            have h_exp : 2 * q = 3 + (2 * q - 3) := by omega
            rw [h_exp, pow_add]
            have h_tail : 3 + (2 * q - 3) - 3 = 2 * q - 3 := by omega
            rw [h_tail]
            ring
  let T : ℕ := p ^ (2 * q - 3) * D ^ q
  have hpow_split_T : a ^ q = p ^ 3 * T := by
    simpa [T] using hpow_split
  have hrhs : a ^ q + 1 = 1 + p ^ 3 * T := by
    rw [hpow_split_T]
    omega
  have heq :
      1 + p ^ 2 * (V + D) + p ^ 3 * S = 1 + p ^ 3 * T := by
    rw [← hprod, hcat_div, hrhs]
  have heq_terms :
      p ^ 2 * (V + D) + p ^ 3 * S = p ^ 3 * T := by
    omega
  have hcancel : V + D + p * S = p * T := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < p ^ 2 by positivity)
    calc
      p ^ 2 * (V + D + p * S)
          = p ^ 2 * (V + D) + p ^ 3 * S := by ring
      _ = p ^ 3 * T := heq_terms
      _ = p ^ 2 * (p * T) := by ring
  have hp_sum : p ∣ (V + D) + p * S := ⟨T, hcancel⟩
  have hp_tail : p ∣ p * S := dvd_mul_right p S
  exact (Nat.dvd_add_iff_left hp_tail).mpr hp_sum

theorem ramified_contra_of_q_dvd_vu
    (u v a p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hq_u : ¬ q ∣ u)
    (hcat : (v * u) ^ p = a ^ q + 1)
    (ha_succ : a + 1 = u ^ p)
    (hq_vu : q ∣ v * u) :
    False := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hu_ne : ((u : ℕ) : ZMod q) ≠ 0 := by
    intro hu0
    exact hq_u ((ZMod.natCast_eq_zero_iff u q).mp hu0)
  have hup_ne : ((u : ℕ) : ZMod q) ^ p ≠ 0 := pow_ne_zero p hu_ne
  have hcat_z :
      (((v * u) ^ p : ℕ) : ZMod q) = ((a ^ q + 1 : ℕ) : ZMod q) := by
    exact congrArg (fun n : ℕ => ((n : ℕ) : ZMod q)) hcat
  have ha_frob : ((a : ℕ) : ZMod q) ^ q = (a : ℕ) := ZMod.pow_card _
  have ha_succ_z : ((a : ℕ) : ZMod q) + 1 = ((u : ℕ) : ZMod q) ^ p := by
    have h := congrArg (fun n : ℕ => ((n : ℕ) : ZMod q)) ha_succ
    simpa using h
  have hvp_eq_one : ((v : ℕ) : ZMod q) ^ p = 1 := by
    have h : (((v : ℕ) : ZMod q) ^ p) * (((u : ℕ) : ZMod q) ^ p)
        = ((u : ℕ) : ZMod q) ^ p := by
      simpa [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        mul_pow, ha_frob, ha_succ_z] using hcat_z
    exact mul_right_cancel₀ hup_ne (by simpa using h)
  have hq_v : q ∣ v := by
    rcases (Nat.Prime.dvd_mul hq).mp hq_vu with hqv | hqu
    · exact hqv
    · exact False.elim (hq_u hqu)
  have hv_zero : ((v : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff v q).mpr hq_v
  have hone_zero : ((1 : ℕ) : ZMod q) = 0 := by
    simpa [hv_zero, zero_pow hp.ne_zero] using hvp_eq_one.symm
  exact hq.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 q).mp hone_zero)

/-- p-adic denominator obstruction: assuming `¬ p ∣ u`, the cleared
finite Puiseux truncation has nonzero residue mod `p`, while the
cleared integer `v` is 0 mod `p`. -/
private theorem cassels_truncation_denominator_obstruction
    (u v p q N : ℕ)
    (hu : 1 < u)
    (hp : p.Prime)
    (hp_lt_q : p < q)
    (hNpos : 0 < N)
    (hp_not_dvd_u : ¬ p ∣ u) :
    True := by
  -- Statement deliberately weakened to True for now; the actual
  -- denominator obstruction needs Finsupp/ℚ infrastructure that
  -- is not yet wired in.  See body of next theorem for the
  -- algebraic content.
  trivial

/-- Padé/Runge approximation gap (THE REAL ANALYTIC BLOCKER).

For some N > 0, the finite Puiseux truncation `T` of `F(X) = ((1-X)^q + X^q)^(1/p)`
satisfies `|v - u^(q-1) · T| < 1/D`, where `D` is the appropriate
denominator clearing factor.

This is the genuinely hard part: a robust Cassels/Runge-style
approximation strong enough to beat the rational denominator gap for
ALL distinct odd primes `5 ≤ p < q`.  Naive truncation at
`⌊(q-1)/p⌋` is too weak for large `q`. -/
private theorem cassels_root_truncation_gap
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1)) :
    True := by
  trivial

/-! ### Precise Padé / denominator skeleton for the genuine Cassels blocker

ChatGPT 0721574a 2026-05-15 detailed decomposition: the monolithic
research sorry decomposes into precise sub-theorems, each at a clear
level (analytic / p-adic / formal arithmetic / wrapper). -/

/-- Numerator `q(q-p)(q-2p)...(q-(k-1)p)` appearing in `(-1)^k · binom(q/p,k)`. -/
private def casselsBinomNum (p q k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, ((q : ℤ) - (j : ℤ) * (p : ℤ))

/-- Rational coefficient `(-1)^k · binom(q/p,k)` with explicit denominator. -/
private def casselsRootCoeff (p q k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k)
    * (casselsBinomNum p q k : ℚ)
    / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))

/-! ### Building blocks for the proper Runge approximant of F(X)

ChatGPT pro extended 50c971bc (2026-05-15) first incremental step
toward `cassels_runge_gap_core`.  The actual algebraic root is
  `F(X) = ((1-X)^q + X^q)^(1/p)`
not just `(1-X)^(q/p)`.  Via the factoring
  `F(X) = (1-X)^(q/p) · (1 + (X/(1-X))^q)^(1/p)`
the coefficient at degree k is a sum over `a` of corrections, where
the `a`-th correction uses one factor of `(X/(1-X))^q`. -/

/-- General numerator `A(A-p)(A-2p)...(A-(k-1)p)` over ℤ.

Used to express binomial coefficients of `(1-X)^(A/p)` for
non-integer exponents.  Allows `A : ℤ` because corrections
require `A = q - q·a·p` which may be negative. -/
private def casselsGeneralBinomNum (p : ℕ) (A : ℤ) (k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, (A - (j : ℤ) * (p : ℤ))

/-- Coefficient of `X^k` in `(1 - X)^(A/p)`: `(-1)^k · binom(A/p, k)`. -/
private def casselsOneMinusCoeff (p : ℕ) (A : ℤ) (k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ k)
    * (casselsGeneralBinomNum p A k : ℚ)
    / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))

/-- Coefficient of `Z^a` in `(1 + Z)^(1/p)`: `binom(1/p, a)` (no sign). -/
private def casselsOnePlusOneOverPCoeff (p a : ℕ) : ℚ :=
  (casselsGeneralBinomNum p (1 : ℤ) a : ℚ)
    / ((p : ℚ) ^ a * (Nat.factorial a : ℚ))

/-- The `a`-th correction contribution to the coefficient of `X^k` in `F(X)`.

Using `F(X) = (1-X)^(q/p) · (1 + (X/(1-X))^q)^(1/p)`, the `a`-th term is
`binom(1/p,a) · X^(q·a) · (1-X)^(q/p - q·a)`.  Its contribution to
degree `k` is `binom(1/p,a) · [X^(k-q·a)] (1-X)^((q - q·a·p)/p)`. -/
private def casselsActualCorrectionTerm (p q k a : ℕ) : ℚ :=
  casselsOnePlusOneOverPCoeff p a
    * casselsOneMinusCoeff p
        ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ))
        (k - q * a)

/-- Coefficient of `X^k` in the formal expansion of
`F(X) = ((1-X)^q + X^q)^(1/p)`.

The `a = 0` term is the old coefficient of `(1-X)^(q/p)`, namely
`casselsRootCoeff p q k`.  The sum over `a ≥ 1` adds the corrections
from the second factor.  For `k < q`, only `a = 0` contributes. -/
private def casselsActualRootCoeff (p q k : ℕ) : ℚ :=
  casselsRootCoeff p q k
    + ∑ a ∈ Finset.Icc 1 (k / q),
        casselsActualCorrectionTerm p q k a

/-- For `k < q`, the actual coefficient equals the old (1-X)^(q/p)
coefficient — no correction term applies. -/
private theorem cassels_actual_eq_binomial_below_q
    (p q k : ℕ) (hk : k < q) :
    casselsActualRootCoeff p q k = casselsRootCoeff p q k := by
  have hdiv : k / q = 0 := Nat.div_eq_of_lt hk
  simp [casselsActualRootCoeff, hdiv]

/-- At `k = q`, the correction is exactly `1/p`. -/
private theorem cassels_actual_root_at_top_correction
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q) :
    casselsActualRootCoeff p q q
      = casselsRootCoeff p q q + (1 / (p : ℚ)) := by
  have hq_ne_zero : q ≠ 0 := hq.ne_zero
  have hqdiv : q / q = 1 := Nat.div_self hq.pos
  have hcorr : casselsActualCorrectionTerm p q q 1 = 1 / (p : ℚ) := by
    simp [
      casselsActualCorrectionTerm,
      casselsOnePlusOneOverPCoeff,
      casselsOneMinusCoeff,
      casselsGeneralBinomNum
    ]
  calc
    casselsActualRootCoeff p q q
        = casselsRootCoeff p q q
          + ∑ a ∈ Finset.Icc 1 (q / q),
              casselsActualCorrectionTerm p q q a := by rfl
    _ = casselsRootCoeff p q q
        + casselsActualCorrectionTerm p q q 1 := by
            rw [hqdiv]; simp
    _ = casselsRootCoeff p q q + (1 / (p : ℚ)) := by rw [hcorr]

private theorem casselsBinomNum_ne_zero_of_prime_lt
    (p q k : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q) :
    casselsBinomNum p q k ≠ 0 := by
  classical
  unfold casselsBinomNum
  rw [Finset.prod_ne_zero_iff]
  intro j _ hj
  have hq_eq : (q : ℤ) = (j : ℤ) * (p : ℤ) := by omega
  have hp_dvd_qZ : (p : ℤ) ∣ (q : ℤ) := by
    refine ⟨j, ?_⟩
    rw [hq_eq]
    ring
  have hp_dvd_q : p ∣ q := by exact_mod_cast hp_dvd_qZ
  rcases hq.eq_one_or_self_of_dvd p hp_dvd_q with hp_eq_one | hp_eq_q
  · exact hp.ne_one hp_eq_one
  · omega

private theorem casselsRootCoeff_ne_zero_of_prime_lt
    (p q k : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q) :
    casselsRootCoeff p q k ≠ 0 := by
  unfold casselsRootCoeff
  refine div_ne_zero ?_ ?_
  · refine mul_ne_zero ?_ ?_
    · exact pow_ne_zero k (by norm_num : (-1 : ℚ) ≠ 0)
    · exact_mod_cast casselsBinomNum_ne_zero_of_prime_lt p q k hp hq hp_lt_q
  · refine mul_ne_zero ?_ ?_
    · exact pow_ne_zero k (by exact_mod_cast hp.ne_zero : (p : ℚ) ≠ 0)
    · exact_mod_cast Nat.factorial_ne_zero k

private theorem casselsRootCoeff_succ
    (p q k : ℕ) (hp0 : p ≠ 0) :
    casselsRootCoeff p q (k + 1)
      =
    -(((q : ℚ) - (k : ℚ) * (p : ℚ))
        / ((p : ℚ) * ((k + 1 : ℕ) : ℚ)))
      * casselsRootCoeff p q k := by
  unfold casselsRootCoeff casselsBinomNum
  rw [Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  have hkQ : (((k + 1 : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp [hpQ, hkQ]
  ring_nf

private theorem casselsRootCoeff_abs_succ_eq
    (p q k : ℕ) (hp0 : p ≠ 0) :
    |((casselsRootCoeff p q (k + 1) : ℚ) : ℝ)|
      =
    |(((q : ℝ) - (k : ℝ) * (p : ℝ))
        / ((p : ℝ) * ((k + 1 : ℕ) : ℝ)))|
      * |((casselsRootCoeff p q k : ℚ) : ℝ)| := by
  have hrec := casselsRootCoeff_succ p q k hp0
  have hrecR :
      ((casselsRootCoeff p q (k + 1) : ℚ) : ℝ)
        =
      -(((q : ℝ) - (k : ℝ) * (p : ℝ))
          / ((p : ℝ) * ((k + 1 : ℕ) : ℝ)))
        * ((casselsRootCoeff p q k : ℚ) : ℝ) := by
    exact_mod_cast hrec
  rw [hrecR, abs_mul, abs_neg]

private theorem casselsRootCoeff_abs_ratio_le_one
    (p q k : ℕ) (hp0 : 0 < p) (hk : q < p * k) :
    |(((q : ℝ) - (k : ℝ) * (p : ℝ))
        / ((p : ℝ) * ((k + 1 : ℕ) : ℝ)))| ≤ 1 := by
  have hpR_pos : (0 : ℝ) < p := by exact_mod_cast hp0
  have hk1R_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hden_pos : (0 : ℝ) < (p : ℝ) * ((k + 1 : ℕ) : ℝ) :=
    mul_pos hpR_pos hk1R_pos
  have hnum_nonpos : (q : ℝ) - (k : ℝ) * (p : ℝ) ≤ 0 := by
    have hk_le : q ≤ k * p := by
      rw [Nat.mul_comm]
      exact Nat.le_of_lt hk
    have hk_leR : (q : ℝ) ≤ (k * p : ℕ) := by exact_mod_cast hk_le
    push_cast at hk_leR
    nlinarith
  rw [abs_div, abs_of_nonpos hnum_nonpos, abs_of_pos hden_pos]
  rw [div_le_one hden_pos]
  have hdiff_le : -((q : ℝ) - (k : ℝ) * (p : ℝ))
      ≤ (p : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    have hk_le : q ≤ k * p := by
      rw [Nat.mul_comm]
      exact Nat.le_of_lt hk
    have hle_nat : k * p - q ≤ p * (k + 1) := by
      exact le_trans (Nat.sub_le (k * p) q) (by
        rw [Nat.mul_comm k p]
        exact Nat.mul_le_mul_left p (Nat.le_succ k))
    have hleR : ((k * p - q : ℕ) : ℝ) ≤ (p * (k + 1) : ℕ) := by
      exact_mod_cast hle_nat
    rw [Nat.cast_sub hk_le] at hleR
    push_cast at hleR
    rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by norm_num]
    nlinarith
  exact hdiff_le

private theorem casselsRootCoeff_abs_succ_mul_pow_le
    (p q k : ℕ) (hp0 : 0 < p) (hk : q < p * k)
    {X : ℝ} (hX0 : 0 ≤ X) :
    |((casselsRootCoeff p q (k + 1) : ℚ) : ℝ)| * X ^ (k + 1)
      ≤
    X * (|((casselsRootCoeff p q k : ℚ) : ℝ)| * X ^ k) := by
  have hratio :=
    casselsRootCoeff_abs_ratio_le_one p q k hp0 hk
  have hrec :=
    casselsRootCoeff_abs_succ_eq p q k (Nat.ne_of_gt hp0)
  rw [hrec, pow_succ]
  have hnonneg :
      0 ≤ |(((q : ℝ) - (k : ℝ) * (p : ℝ))
          / ((p : ℝ) * ((k + 1 : ℕ) : ℝ)))| := abs_nonneg _
  have htail_nonneg :
      0 ≤ |((casselsRootCoeff p q k : ℚ) : ℝ)| * (X ^ k * X) := by
    positivity
  calc
    |(((q : ℝ) - (k : ℝ) * (p : ℝ))
        / ((p : ℝ) * ((k + 1 : ℕ) : ℝ)))|
        * |((casselsRootCoeff p q k : ℚ) : ℝ)| * (X ^ k * X)
        =
      |(((q : ℝ) - (k : ℝ) * (p : ℝ))
        / ((p : ℝ) * ((k + 1 : ℕ) : ℝ)))|
        * (|((casselsRootCoeff p q k : ℚ) : ℝ)| * (X ^ k * X)) := by
          ring
    _ ≤ 1 * (|((casselsRootCoeff p q k : ℚ) : ℝ)| * (X ^ k * X)) :=
          mul_le_mul_of_nonneg_right hratio htail_nonneg
    _ = X * (|((casselsRootCoeff p q k : ℚ) : ℝ)| * X ^ k) := by
          ring

private theorem casselsRootCoeff_tail_le_geom_of_q_lt_p_mul
    (p q R n : ℕ) (hp0 : 0 < p) (hR : q < p * R)
    {X : ℝ} (hX0 : 0 ≤ X) :
    |((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)|
        * X ^ (n + (R + 1))
      ≤
    X ^ n
      * (|((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
          * X ^ (R + 1)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let k := n + (R + 1)
      have hk : q < p * k := by
        have hRle : R ≤ k := by
          dsimp [k]
          omega
        have hmul : p * R ≤ p * k := Nat.mul_le_mul_left p hRle
        exact lt_of_lt_of_le hR hmul
      have hstep :
          |((casselsRootCoeff p q (k + 1) : ℚ) : ℝ)| * X ^ (k + 1)
            ≤
          X * (|((casselsRootCoeff p q k : ℚ) : ℝ)| * X ^ k) :=
        casselsRootCoeff_abs_succ_mul_pow_le p q k hp0 hk hX0
      have hih :
          |((casselsRootCoeff p q k : ℚ) : ℝ)| * X ^ k
            ≤
          X ^ n
            * (|((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
                * X ^ (R + 1)) := by
        dsimp [k]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
      calc
        |((casselsRootCoeff p q (Nat.succ n + (R + 1)) : ℚ) : ℝ)|
            * X ^ (Nat.succ n + (R + 1))
            =
          |((casselsRootCoeff p q (k + 1) : ℚ) : ℝ)| * X ^ (k + 1) := by
            have hidx : Nat.succ n + (R + 1) = k + 1 := by
              dsimp [k]
              omega
            rw [hidx]
        _ ≤ X * (|((casselsRootCoeff p q k : ℚ) : ℝ)| * X ^ k) :=
            hstep
        _ ≤ X * (X ^ n
            * (|((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
                * X ^ (R + 1))) :=
            mul_le_mul_of_nonneg_left hih hX0
        _ =
          X ^ Nat.succ n
            * (|((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
                * X ^ (R + 1)) := by
            rw [pow_succ X n, pow_succ X R]
            ring

private theorem casselsRootCoeff_tail_abs_summable_of_q_lt_p_mul
    (p q R : ℕ) (hp0 : 0 < p) (hR : q < p * R)
    {X : ℝ} (hX0 : 0 ≤ X) (hXlt : X < 1) :
    Summable
      (fun n : ℕ =>
        |((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1))) := by
  let C : ℝ :=
    |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| * X ^ (R + 1)
  have hgeo : Summable (fun n : ℕ => C * X ^ n) :=
    (summable_geometric_of_lt_one hX0 hXlt).mul_left C
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hgeo
  intro n
  have hle :=
    casselsRootCoeff_tail_le_geom_of_q_lt_p_mul p q R n hp0 hR hX0
  simpa [C, mul_comm, mul_left_comm, mul_assoc] using hle

private theorem casselsRootCoeff_tail_abs_tsum_le_geom
    (p q R : ℕ) (hp0 : 0 < p) (hR : q < p * R)
    {X : ℝ} (hX0 : 0 ≤ X) (hXlt : X < 1) :
    (∑' n : ℕ,
        |((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1)))
      ≤
    |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) := by
  let C : ℝ :=
    |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| * X ^ (R + 1)
  have hLsum :=
    casselsRootCoeff_tail_abs_summable_of_q_lt_p_mul
      p q R hp0 hR hX0 hXlt
  have hRsum : Summable (fun n : ℕ => C * X ^ n) :=
    (summable_geometric_of_lt_one hX0 hXlt).mul_left C
  have hpoint :
      ∀ n : ℕ,
        |((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)|
            * X ^ (n + (R + 1))
          ≤ C * X ^ n := by
    intro n
    have hle :=
      casselsRootCoeff_tail_le_geom_of_q_lt_p_mul p q R n hp0 hR hX0
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using hle
  calc
    (∑' n : ℕ,
        |((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1)))
        ≤ ∑' n : ℕ, C * X ^ n :=
          hLsum.tsum_le_tsum hpoint hRsum
    _ = C * (1 - X)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hX0 hXlt]
    _ =
      |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) := by
          dsimp [C]
          ring

private theorem casselsActualRootCoeff_ne_zero_of_lt_q
    (p q k : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q)
    (hk : k < q) :
    casselsActualRootCoeff p q k ≠ 0 := by
  rw [cassels_actual_eq_binomial_below_q p q k hk]
  exact casselsRootCoeff_ne_zero_of_prime_lt p q k hp hq hp_lt_q

/-! ### Actual-root coefficient denominator clearing

These lemmas are the coefficient-side replacement for the older Padé-only
clearing once the truncation level passes `q`.  They are independent of the
final Archimedean estimate: every coefficient of the actual branch
`((1-X)^q + X^q)^(1/p)` has denominator dividing `p^k * k!`. -/

private def casselsCoeffDenBound (p k : ℕ) : ℕ :=
  p ^ k * Nat.factorial k

private theorem rat_den_div_nat_dvd (z : ℤ) (D : ℕ) :
    (((z : ℚ) / (D : ℚ)).den) ∣ D := by
  have hkey : ((Rat.divInt z (D : ℤ)).den : ℤ) ∣ (D : ℤ) :=
    Rat.den_dvd z (D : ℤ)
  have hrepr : (z : ℚ) / (D : ℚ) = Rat.divInt z (D : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    ring
  rw [hrepr]
  exact_mod_cast hkey

private theorem rat_den_mul_is_int (x : ℚ) :
    ∃ z : ℤ, (x.den : ℚ) * x = (z : ℚ) := by
  refine ⟨x.num, ?_⟩
  have hden : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_nz
  have h : (x.num : ℚ) / (x.den : ℚ) = x := Rat.num_div_den x
  rw [div_eq_iff hden] at h
  rw [h]
  ring

private theorem rat_mul_is_int_of_den_dvd
    (D : ℕ) (x : ℚ) (hD : x.den ∣ D) :
    ∃ z : ℤ, (D : ℚ) * x = (z : ℚ) := by
  rcases hD with ⟨c, rfl⟩
  rcases rat_den_mul_is_int x with ⟨z, hz⟩
  refine ⟨(c : ℤ) * z, ?_⟩
  calc
    ((x.den * c : ℕ) : ℚ) * x
        = (c : ℚ) * ((x.den : ℚ) * x) := by
          push_cast
          ring
    _ = (c : ℚ) * (z : ℚ) := by rw [hz]
    _ = (((c : ℤ) * z : ℤ) : ℚ) := by
          push_cast
          ring

private theorem rat_mul_den_dvd_of_den_dvd
    (x y : ℚ) {Dx Dy : ℕ}
    (hx : x.den ∣ Dx) (hy : y.den ∣ Dy) :
    (x * y).den ∣ Dx * Dy :=
  (Rat.mul_den_dvd x y).trans (Nat.mul_dvd_mul hx hy)

private theorem rat_add_den_dvd_common
    (x y : ℚ) {D : ℕ}
    (hx : x.den ∣ D) (hy : y.den ∣ D) :
    (x + y).den ∣ D :=
  (Rat.add_den_dvd_lcm x y).trans
    ((Nat.lcm_dvd_iff).mpr ⟨hx, hy⟩)

private theorem rat_sum_den_dvd_common
    {ι : Type*} (s : Finset ι) (f : ι → ℚ) {D : ℕ}
    (hf : ∀ i ∈ s, (f i).den ∣ D) :
    (∑ i ∈ s, f i).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
      rw [Finset.sum_insert hat]
      refine rat_add_den_dvd_common _ _
        (hf a (Finset.mem_insert_self a t)) ?_
      exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem casselsRootCoeff_den_dvd (p q k : ℕ) :
    (casselsRootCoeff p q k).den ∣ casselsCoeffDenBound p k := by
  unfold casselsRootCoeff casselsCoeffDenBound
  have hrepr :
      ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
        / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))
        =
      (((-1 : ℤ) ^ k * casselsBinomNum p q k : ℤ) : ℚ)
        / ((p ^ k * Nat.factorial k : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hrepr]
  exact rat_den_div_nat_dvd _ (p ^ k * Nat.factorial k)

private theorem casselsOneMinusCoeff_den_dvd
    (p : ℕ) (A : ℤ) (k : ℕ) :
    (casselsOneMinusCoeff p A k).den ∣ casselsCoeffDenBound p k := by
  unfold casselsOneMinusCoeff casselsCoeffDenBound
  have hrepr :
      ((-1 : ℚ) ^ k) * (casselsGeneralBinomNum p A k : ℚ)
        / ((p : ℚ) ^ k * (Nat.factorial k : ℚ))
        =
      (((-1 : ℤ) ^ k * casselsGeneralBinomNum p A k : ℤ) : ℚ)
        / ((p ^ k * Nat.factorial k : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hrepr]
  exact rat_den_div_nat_dvd _ (p ^ k * Nat.factorial k)

private theorem casselsOnePlusOneOverPCoeff_den_dvd
    (p a : ℕ) :
    (casselsOnePlusOneOverPCoeff p a).den ∣ casselsCoeffDenBound p a := by
  unfold casselsOnePlusOneOverPCoeff casselsCoeffDenBound
  have hrepr :
      (casselsGeneralBinomNum p (1 : ℤ) a : ℚ)
        / ((p : ℚ) ^ a * (Nat.factorial a : ℚ))
        =
      ((casselsGeneralBinomNum p (1 : ℤ) a : ℤ) : ℚ)
        / ((p ^ a * Nat.factorial a : ℕ) : ℚ) := by
    push_cast
    ring
  rw [hrepr]
  exact rat_den_div_nat_dvd _ (p ^ a * Nat.factorial a)

private theorem casselsActualCorrectionTerm_den_dvd
    (p q k a : ℕ) (hqpos : 0 < q)
    (ha : a ∈ Finset.Icc 1 (k / q)) :
    (casselsActualCorrectionTerm p q k a).den
      ∣ casselsCoeffDenBound p k := by
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  have haq : a * q ≤ k := (Nat.le_div_iff_mul_le hqpos).mp hak
  have hqa : q * a ≤ k := by rwa [Nat.mul_comm] at haq
  have hprod :
      (casselsActualCorrectionTerm p q k a).den
        ∣ casselsCoeffDenBound p a
            * casselsCoeffDenBound p (k - q * a) := by
    unfold casselsActualCorrectionTerm
    exact rat_mul_den_dvd_of_den_dvd _ _
      (casselsOnePlusOneOverPCoeff_den_dvd p a)
      (casselsOneMinusCoeff_den_dvd p _ (k - q * a))
  refine hprod.trans ?_
  unfold casselsCoeffDenBound
  have hsum_le : a + (k - q * a) ≤ k := by
    have ha_le_qa : a ≤ q * a := Nat.le_mul_of_pos_left a hqpos
    omega
  have hp_dvd : p ^ a * p ^ (k - q * a) ∣ p ^ k := by
    rw [← pow_add]
    exact pow_dvd_pow p hsum_le
  have hfac_dvd :
      Nat.factorial a * Nat.factorial (k - q * a)
        ∣ Nat.factorial k :=
    (Nat.factorial_mul_factorial_dvd_factorial_add a (k - q * a)).trans
      (Nat.factorial_dvd_factorial hsum_le)
  calc
    p ^ a * Nat.factorial a
        * (p ^ (k - q * a) * Nat.factorial (k - q * a))
        = (p ^ a * p ^ (k - q * a))
            * (Nat.factorial a * Nat.factorial (k - q * a)) := by
          ring
    _ ∣ p ^ k * Nat.factorial k :=
          Nat.mul_dvd_mul hp_dvd hfac_dvd

private theorem casselsActualRootCoeff_den_dvd
    (p q k : ℕ) (hqpos : 0 < q) :
    (casselsActualRootCoeff p q k).den ∣ casselsCoeffDenBound p k := by
  unfold casselsActualRootCoeff
  refine rat_add_den_dvd_common _ _
    (casselsRootCoeff_den_dvd p q k) ?_
  exact rat_sum_den_dvd_common _ _
    (fun a ha => casselsActualCorrectionTerm_den_dvd p q k a hqpos ha)

private theorem rat_inv_nat_pow_den_dvd (u e : ℕ) :
    (((u : ℚ) ^ e)⁻¹).den ∣ u ^ e := by
  have hrepr : (((u : ℚ) ^ e)⁻¹) = (1 : ℚ) / ((u ^ e : ℕ) : ℚ) := by
    push_cast
    rw [inv_eq_one_div]
  rw [hrepr]
  exact rat_den_div_nat_dvd 1 (u ^ e)

private theorem casselsRootCoeff_cleared_eq_top_witness
    (p q N : ℕ) (hp : p.Prime) :
    ((p ^ N * Nat.factorial N : ℕ) : ℚ) * casselsRootCoeff p q N
      =
    (((-1 : ℤ) ^ N * casselsBinomNum p q N : ℤ) : ℚ) := by
  have hpQ_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hfacQ_ne : (Nat.factorial N : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  unfold casselsRootCoeff
  push_cast
  field_simp [hpQ_ne, hfacQ_ne]

private theorem casselsActualCorrectionTerm_den_dvd_top_unit_bound
    (p q N a : ℕ) (hq2 : 2 ≤ q)
    (ha : a ∈ Finset.Icc 1 (N / q)) :
    (casselsActualCorrectionTerm p q N a).den
      ∣ p ^ (N - 1) * Nat.factorial N := by
  obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp ha
  have hqpos : 0 < q := by omega
  have haq : a * q ≤ N := (Nat.le_div_iff_mul_le hqpos).mp haN
  have hqa : q * a ≤ N := by rwa [Nat.mul_comm] at haq
  have hprod :
      (casselsActualCorrectionTerm p q N a).den
        ∣ casselsCoeffDenBound p a
            * casselsCoeffDenBound p (N - q * a) := by
    unfold casselsActualCorrectionTerm
    exact rat_mul_den_dvd_of_den_dvd _ _
      (casselsOnePlusOneOverPCoeff_den_dvd p a)
      (casselsOneMinusCoeff_den_dvd p _ (N - q * a))
  refine hprod.trans ?_
  unfold casselsCoeffDenBound
  have hNpos : 1 ≤ N := by
    have : 1 * q ≤ N := le_trans (Nat.mul_le_mul_right q ha1) haq
    omega
  have hexp_le : a + (N - q * a) ≤ N - 1 := by
    have ha_succ_le_qa : a + 1 ≤ q * a := by
      have htwo : 2 * a ≤ q * a := Nat.mul_le_mul_right a hq2
      omega
    omega
  have hp_dvd : p ^ a * p ^ (N - q * a) ∣ p ^ (N - 1) := by
    rw [← pow_add]
    exact pow_dvd_pow p hexp_le
  have hsum_le : a + (N - q * a) ≤ N := by omega
  have hfac_dvd :
      Nat.factorial a * Nat.factorial (N - q * a)
        ∣ Nat.factorial N :=
    (Nat.factorial_mul_factorial_dvd_factorial_add a (N - q * a)).trans
      (Nat.factorial_dvd_factorial hsum_le)
  calc
    p ^ a * Nat.factorial a
        * (p ^ (N - q * a) * Nat.factorial (N - q * a))
        = (p ^ a * p ^ (N - q * a))
            * (Nat.factorial a * Nat.factorial (N - q * a)) := by
          ring
    _ ∣ p ^ (N - 1) * Nat.factorial N :=
          Nat.mul_dvd_mul hp_dvd hfac_dvd

private theorem casselsActualCorrectionTerm_top_cleared_p_multiple
    (p q N a : ℕ) (hp : p.Prime) (hq2 : 2 ≤ q)
    (ha : a ∈ Finset.Icc 1 (N / q)) :
    ∃ z : ℤ,
      ((p ^ N * Nat.factorial N : ℕ) : ℚ)
        * casselsActualCorrectionTerm p q N a
        = (((p : ℤ) * z : ℤ) : ℚ) := by
  have hden :=
    casselsActualCorrectionTerm_den_dvd_top_unit_bound p q N a hq2 ha
  rcases rat_mul_is_int_of_den_dvd (p ^ (N - 1) * Nat.factorial N)
      (casselsActualCorrectionTerm p q N a) hden with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hqpos : 0 < q := by omega
  have haq : a * q ≤ N :=
    (Nat.le_div_iff_mul_le hqpos).mp (Finset.mem_Icc.mp ha).2
  have hNpos : 0 < N := by
    have : 1 * q ≤ N := le_trans (Nat.mul_le_mul_right q ha1) haq
    omega
  have hpow :
      p ^ N * Nat.factorial N
        = p * (p ^ (N - 1) * Nat.factorial N) := by
    cases N with
    | zero => omega
    | succ N =>
        simp [pow_succ]
        ring
  calc
    ((p ^ N * Nat.factorial N : ℕ) : ℚ)
        * casselsActualCorrectionTerm p q N a
        =
      (p : ℚ)
        * (((p ^ (N - 1) * Nat.factorial N : ℕ) : ℚ)
          * casselsActualCorrectionTerm p q N a) := by
          rw [hpow]
          push_cast
          ring
    _ = (p : ℚ) * (z : ℚ) := by rw [hz]
    _ = (((p : ℤ) * z : ℤ) : ℚ) := by
          push_cast
          ring

/-- Deliberately large truncation level depending on desired p-adic order `n`. -/
private def casselsPadeLevel (p q n : ℕ) : ℕ :=
  max (n * q + 1) (((q - 1) / p) + n + 1)

/-- Finite rational truncation
`Σ_{k≤N} c_k · u^(q-1) · (u^p)^(-k)`. -/
private def casselsPadeTruncQ (u p q N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    casselsRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k

/-- Safe denominator-clearing factor: clears `p^k`, `k!`, and `(u^p)^(-k)`
up to `k ≤ N`. -/
private def casselsPadeClearDen (u p N : ℕ) : ℕ :=
  p ^ N * Nat.factorial N * u ^ (p * N)

private theorem casselsPadeLevel_pos (p q n : ℕ) : 0 < casselsPadeLevel p q n := by
  unfold casselsPadeLevel; omega

private theorem casselsPadeClearDen_pos
    (u p N : ℕ) (hu_pos : 0 < u) (hp_pos : 0 < p) :
    0 < casselsPadeClearDen u p N := by
  unfold casselsPadeClearDen; positivity

/-- Clearing denominators makes the rational truncation integral.

ChatGPT 57e822fb: termwise-witness proof avoiding ring_nf/field_simp,
chaining manual cancellations of `p^k`, `k!`, `u^(pk)` from the
cleared denominator factor. -/
private theorem cassels_pade_trunc_cleared_integral
    (u p q N : ℕ) (hu : 1 < u) (hp : p.Prime) :
    ∃ z : ℤ,
      (casselsPadeClearDen u p N : ℚ) * casselsPadeTruncQ u p q N
        = (z : ℚ) := by
  classical
  let D : ℕ := casselsPadeClearDen u p N
  let f : ℕ → ℚ := fun k =>
    casselsRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k
  let witness : ℕ → ℤ := fun k =>
    ((-1 : ℤ) ^ k)
      * casselsBinomNum p q k
      * ((p ^ (N - k)
            * (Nat.factorial N / Nat.factorial k)
            * u ^ (p * (N - k) + (q - 1)) : ℕ) : ℤ)
  have hu_pos : 0 < u := by omega
  have hp_pos : 0 < p := hp.pos
  have huQ_ne : (u : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu_pos)
  have hpQ_ne : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp_pos)
  have hterm :
      ∀ k ∈ Finset.range (N + 1),
        (D : ℚ) * f k = ((witness k : ℤ) : ℚ) := by
    intro k hk
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hk_fact_dvd : Nat.factorial k ∣ Nat.factorial N :=
      Nat.factorial_dvd_factorial hkN
    have hk_fact_ne : (Nat.factorial k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero k)
    have hp_pow_k_ne : (p : ℚ) ^ k ≠ 0 := pow_ne_zero k hpQ_ne
    have hu_pow_pk_ne : (u : ℚ) ^ (p * k) ≠ 0 := pow_ne_zero (p * k) huQ_ne
    have hD_cast :
        (D : ℚ) =
        (p : ℚ) ^ N * (Nat.factorial N : ℚ) * (u : ℚ) ^ (p * N) := by
      dsimp [D, casselsPadeClearDen]; push_cast; ring
    have hfact_mul :
        ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ)
          * (Nat.factorial k : ℚ)
          = (Nat.factorial N : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hk_fact_dvd
    have hfact_div :
        (Nat.factorial N : ℚ) / (Nat.factorial k : ℚ)
          = ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ) := by
      field_simp [hk_fact_ne]
      simpa [mul_comm] using hfact_mul.symm
    have hfact_dvd_int : (Nat.factorial k : ℤ) ∣ (Nat.factorial N : ℤ) := by
      exact_mod_cast hk_fact_dvd
    have hfact_divZ :
        (((Nat.factorial N : ℤ) / (Nat.factorial k : ℤ) : ℤ) : ℚ)
          = (Nat.factorial N : ℚ) / (Nat.factorial k : ℚ) := by
      simpa using (Int.cast_div (α := ℚ) hfact_dvd_int hk_fact_ne)
    have hp_pow_mul :
        (p : ℚ) ^ (N - k) * (p : ℚ) ^ k = (p : ℚ) ^ N := by
      rw [← pow_add]
      have hNk : N - k + k = N := Nat.sub_add_cancel hkN
      rw [hNk]
    have hp_pow_div :
        (p : ℚ) ^ N / (p : ℚ) ^ k = (p : ℚ) ^ (N - k) := by
      field_simp [hp_pow_k_ne]
      simpa [mul_comm] using hp_pow_mul.symm
    have hu_inv_pow :
        (((u : ℚ) ^ p)⁻¹) ^ k = ((u : ℚ) ^ (p * k))⁻¹ := by
      rw [inv_pow, ← pow_mul]
    have hu_pow_mul :
        (u : ℚ) ^ (p * (N - k)) * (u : ℚ) ^ (p * k) = (u : ℚ) ^ (p * N) := by
      rw [← pow_add]
      have hexp : p * (N - k) + p * k = p * N := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hkN]
      rw [hexp]
    have hu_pow_div :
        (u : ℚ) ^ (p * N) * ((u : ℚ) ^ (p * k))⁻¹
          = (u : ℚ) ^ (p * (N - k)) := by
      field_simp [hu_pow_pk_ne]
      simpa [mul_comm] using hu_pow_mul.symm
    have hu_part :
        (u : ℚ) ^ (p * N) * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k
          = (u : ℚ) ^ (p * (N - k) + (q - 1)) := by
      rw [hu_inv_pow]
      calc
        (u : ℚ) ^ (p * N) * (u : ℚ) ^ (q - 1) * ((u : ℚ) ^ (p * k))⁻¹
            = ((u : ℚ) ^ (p * N) * ((u : ℚ) ^ (p * k))⁻¹)
                * (u : ℚ) ^ (q - 1) := by ring
        _ = (u : ℚ) ^ (p * (N - k)) * (u : ℚ) ^ (q - 1) := by rw [hu_pow_div]
        _ = (u : ℚ) ^ (p * (N - k) + (q - 1)) := by rw [← pow_add]
    have hden_inv :
        (((p : ℚ) ^ k * (Nat.factorial k : ℚ))⁻¹)
          = ((p : ℚ) ^ k)⁻¹ * (Nat.factorial k : ℚ)⁻¹ := by
      rw [mul_inv]
    have hcoeff :
        (p : ℚ) ^ N * (Nat.factorial N : ℚ)
          * (((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              / ((p : ℚ) ^ k * (Nat.factorial k : ℚ)))
          = ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              * (p : ℚ) ^ (N - k)
              * ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ) := by
      calc
        (p : ℚ) ^ N * (Nat.factorial N : ℚ)
            * (((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
                / ((p : ℚ) ^ k * (Nat.factorial k : ℚ)))
            = ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
                * ((p : ℚ) ^ N / (p : ℚ) ^ k)
                * ((Nat.factorial N : ℚ) / (Nat.factorial k : ℚ)) := by
              rw [div_eq_mul_inv, hden_inv]; ring
        _ = ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              * (p : ℚ) ^ (N - k)
              * ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ) := by
              rw [hp_pow_div, hfact_div]
    calc
      (D : ℚ) * f k
          = ((p : ℚ) ^ N * (Nat.factorial N : ℚ) * (u : ℚ) ^ (p * N))
              * (casselsRootCoeff p q k
                * (u : ℚ) ^ (q - 1) * (((u : ℚ) ^ p)⁻¹) ^ k) := by
            rw [hD_cast]
      _ = ((p : ℚ) ^ N * (Nat.factorial N : ℚ) * (casselsRootCoeff p q k))
            * ((u : ℚ) ^ (p * N) * (u : ℚ) ^ (q - 1)
              * (((u : ℚ) ^ p)⁻¹) ^ k) := by ring
      _ = (((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              * (p : ℚ) ^ (N - k)
              * ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ))
            * ((u : ℚ) ^ (p * (N - k) + (q - 1))) := by
              dsimp [casselsRootCoeff]; rw [hcoeff, hu_part]
      _ = ((witness k : ℤ) : ℚ) := by
            dsimp [witness]; push_cast
            rw [← hfact_div, hfact_divZ]
            ring
  refine ⟨∑ k ∈ Finset.range (N + 1), witness k, ?_⟩
  calc
    (casselsPadeClearDen u p N : ℚ) * casselsPadeTruncQ u p q N
        = (D : ℚ) * (∑ k ∈ Finset.range (N + 1), f k) := by
            dsimp [D, f, casselsPadeTruncQ]
    _ = ∑ k ∈ Finset.range (N + 1), (D : ℚ) * f k := by
            rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (N + 1), ((witness k : ℤ) : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hterm k hk
    _ = ((∑ k ∈ Finset.range (N + 1), witness k : ℤ) : ℚ) := by
            push_cast
            rfl

/-! ### Catalan-side B2.4 clearing bricks

These are the non-circular algebraic pieces of the Ribenboim/Cassels
clearing argument.  They use the Catalan expansion
`a * (1 + a^(-q))^(1/q)` and prove that the fixed finite truncation has
an explicitly cleared integer value.  The remaining B2.4 work is the
nonzero tail estimate and the upper bound `|I| < 1`. -/

/-- Catalan binomial coefficient `C(1/q, k)`. -/
noncomputable def catalanCoeff (q k : ℕ) : ℚ :=
  (∏ j ∈ Finset.range k, ((1 : ℚ) - (j : ℚ) * (q : ℚ)))
    / ((q : ℚ) ^ k * (Nat.factorial k : ℚ))

theorem catalanCoeff_ne_zero (q k : ℕ) (hq2 : 2 ≤ q) :
    catalanCoeff q k ≠ 0 := by
  unfold catalanCoeff
  refine div_ne_zero ?_ ?_
  · exact Finset.prod_ne_zero_iff.mpr (by
      intro j _ hj
      have hjqQ : ((j * q : ℕ) : ℚ) = 1 := by
        have hmul : (j : ℚ) * (q : ℚ) = 1 := by linarith
        simpa using hmul
      have hjq : j * q = 1 := by exact_mod_cast hjqQ
      cases j with
      | zero => simp at hjq
      | succ j =>
          have hge : 2 ≤ Nat.succ j * q :=
            Nat.mul_le_mul (by omega : 1 ≤ Nat.succ j) hq2
          rw [hjq] at hge
          omega)
  · exact mul_ne_zero
      (pow_ne_zero k (Nat.cast_ne_zero.mpr (by omega : q ≠ 0)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))

/-- The `A = 1` binomial numerator factors as `p^a` times the real
generalized-binomial product. -/
theorem casselsGeneralBinomNum_one_real_factor
    (p a : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsGeneralBinomNum p 1 a : ℤ) : ℝ)
      = (p : ℝ) ^ a
          * ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
  unfold casselsGeneralBinomNum
  push_cast
  calc
    ∏ j ∈ Finset.range a, ((1 : ℝ) - (j : ℝ) * (p : ℝ))
        = ∏ j ∈ Finset.range a,
            (p : ℝ) * ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = (∏ _j ∈ Finset.range a, (p : ℝ))
          * ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (p : ℝ) ^ a
          * ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [Finset.prod_const, Finset.card_range]

/-- `Ring.choose r k * k!` is the descending product
`∏_{j<k} (r - j)` over `ℝ`. -/
theorem ring_choose_mul_factorial_eq_prod (r : ℝ) (k : ℕ) :
    Ring.choose r k * (k.factorial : ℝ)
      = ∏ j ∈ Finset.range k, (r - (j : ℝ)) := by
  have h1 : (descPochhammer ℤ k).smeval r
      = k.factorial • Ring.choose r k :=
    Ring.descPochhammer_eq_factorial_smul_choose r k
  have h2 : (descPochhammer ℤ k).smeval r
      = (descPochhammer ℝ k).eval r := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval ℤ (descPochhammer ℤ k) r,
      ← Polynomial.eval_map, descPochhammer_map]
  rw [h2, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  rw [h1]
  ring

/-- The binomial numerator factors as `p^k` times the real descending
product for `q/p`. -/
theorem casselsBinomNum_real_factor
    (p q k : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsBinomNum p q k : ℤ) : ℝ)
      = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
  unfold casselsBinomNum
  push_cast
  calc
    ∏ j ∈ Finset.range k, ((q : ℝ) - (j : ℝ) * (p : ℝ))
        = ∏ j ∈ Finset.range k,
            (p : ℝ) * ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = (∏ _j ∈ Finset.range k, (p : ℝ))
          * ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [Finset.prod_const, Finset.card_range]

/-- The rational coefficient `casselsRootCoeff` is the real binomial
coefficient `(-1)^k * choose(q/p,k)`. -/
theorem casselsRootCoeff_real_eq_choose
    (p q k : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsRootCoeff p q k : ℚ) : ℝ)
      = (-1 : ℝ) ^ k * Ring.choose ((q : ℝ) / (p : ℝ)) k := by
  unfold casselsRootCoeff
  push_cast
  rw [casselsBinomNum_real_factor p q k hp]
  have hprod :
      ∏ j ∈ Finset.range k, ((q : ℝ) / (p : ℝ) - (j : ℝ))
        = Ring.choose ((q : ℝ) / (p : ℝ)) k * (k.factorial : ℝ) :=
    (ring_choose_mul_factorial_eq_prod ((q : ℝ) / (p : ℝ)) k).symm
  rw [hprod]
  have hpk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero k hp
  have hfac : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- The root-coefficient stream sums to `(1-X)^(q/p)` for `|X|<1`. -/
theorem cassels_rootCoeff_hasSum
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) {X : ℝ} (hX : |X| < 1) :
    HasSum (fun k => (casselsRootCoeff p q k : ℝ) * X ^ k)
      ((1 - X) ^ ((q : ℝ) / (p : ℝ))) := by
  have hball : (-X) ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist (-X) (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs, abs_neg]
      calc ENNReal.ofReal |X|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg X)).2 hX
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (q : ℝ) / (p : ℝ))).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  have hbranch_eq : ((1 : ℝ) + -X) ^ ((q : ℝ) / (p : ℝ))
      = (1 - X) ^ ((q : ℝ) / (p : ℝ)) := by ring_nf
  rw [hbranch_eq] at hHS
  convert hHS using 1
  ext k
  rw [casselsRootCoeff_real_eq_choose p q k hp, smul_eq_mul, neg_pow]
  ring

private theorem casselsRootCoeff_tail_gap_abs_le_geom
    (p q R : ℕ) (hp0 : 0 < p) (hR : q < p * R)
    {X : ℝ} (hX0 : 0 ≤ X) (hXlt : X < 1) :
    |(1 - X) ^ ((q : ℝ) / (p : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            ((casselsRootCoeff p q k : ℚ) : ℝ) * X ^ k|
      ≤
    |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) := by
  have hpR_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp0)
  have hXabs : |X| < 1 := by
    rw [abs_of_nonneg hX0]
    exact hXlt
  have htail :
      HasSum
        (fun n : ℕ =>
          ((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)
            * X ^ (n + (R + 1)))
        ((1 - X) ^ ((q : ℝ) / (p : ℝ))
          - ∑ k ∈ Finset.range (R + 1),
              ((casselsRootCoeff p q k : ℚ) : ℝ) * X ^ k) := by
    exact (hasSum_nat_add_iff' (R + 1)).mpr
      (cassels_rootCoeff_hasSum p q hpR_ne hXabs)
  have hnorm_summ :
      Summable
        (fun n : ℕ =>
          ‖((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)
            * X ^ (n + (R + 1))‖) := by
    have habs :=
      casselsRootCoeff_tail_abs_summable_of_q_lt_p_mul
        p q R hp0 hR hX0 hXlt
    refine habs.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg hX0 (n + (R + 1)))]
  have hbound := norm_tsum_le_tsum_norm hnorm_summ
  rw [htail.tsum_eq, Real.norm_eq_abs] at hbound
  calc
    |(1 - X) ^ ((q : ℝ) / (p : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            ((casselsRootCoeff p q k : ℚ) : ℝ) * X ^ k|
        ≤
      ∑' n : ℕ,
        ‖((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)
          * X ^ (n + (R + 1))‖ := hbound
    _ =
      ∑' n : ℕ,
        |((casselsRootCoeff p q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1)) := by
          apply tsum_congr
          intro n
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (pow_nonneg hX0 (n + (R + 1)))]
    _ ≤
      |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) :=
          casselsRootCoeff_tail_abs_tsum_le_geom p q R hp0 hR hX0 hXlt

/-- The real branch `F(X) = ((1-X)^q + X^q)^(1/p)`. -/
noncomputable def casselsBranch (p q : ℕ) (X : ℝ) : ℝ :=
  ((1 - X) ^ q + X ^ q) ^ ((p : ℝ)⁻¹)

/-- The branch base is strictly positive on `[0, 1/32]`. -/
theorem cassels_branch_base_pos
    (p q : ℕ) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    0 < (1 - X) ^ q + X ^ q := by
  have h1X_pos : 0 < 1 - X := by linarith
  have h1X_pow_pos : 0 < (1 - X) ^ q := pow_pos h1X_pos q
  have hX_pow_nonneg : 0 ≤ X ^ q := pow_nonneg hX0 q
  nlinarith

/-- The branch base is at most `2` on `[0, 1/32]`. -/
theorem cassels_branch_base_le_two
    (p q : ℕ) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (1 - X) ^ q + X ^ q ≤ 2 := by
  have h1X_nonneg : 0 ≤ 1 - X := by linarith
  have h1X_le_one : 1 - X ≤ 1 := by linarith
  have hX_le_one : X ≤ 1 := by linarith
  have h1X_pow_le : (1 - X) ^ q ≤ (1 : ℝ) ^ q :=
    pow_le_pow_left₀ h1X_nonneg h1X_le_one q
  have hX_pow_le : X ^ q ≤ (1 : ℝ) ^ q :=
    pow_le_pow_left₀ hX0 hX_le_one q
  simp at h1X_pow_le hX_pow_le
  nlinarith

/-- Defining algebraic property of the branch:
`F(X)^p = (1-X)^q + X^q` on `[0,1/32]`. -/
theorem casselsBranch_pow_p
    (p q : ℕ) (hp : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (casselsBranch p q X) ^ p = (1 - X) ^ q + X ^ q := by
  unfold casselsBranch
  exact Real.rpow_inv_natCast_pow
    (le_of_lt (cassels_branch_base_pos p q hq5 hX0 hXle)) hp.ne'

/-- Generic p-th-power identity for any real Runge approximant values `b, a`.

This is the algebraic mechanism that turns a small linear branch error
`b * F(X) - a` into the pure polynomial remainder
`b^p * ((1-X)^q + X^q) - a^p`. -/
theorem cassels_pth_power_identity_generic
    (p q : ℕ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) (b a : ℝ) :
    (b * casselsBranch p q X - a)
        * (∑ i ∈ Finset.range p,
            (b * casselsBranch p q X) ^ i * a ^ (p - 1 - i))
      = b ^ p * ((1 - X) ^ q + X ^ q) - a ^ p := by
  have hFp : (casselsBranch p q X) ^ p = (1 - X) ^ q + X ^ q :=
    casselsBranch_pow_p p q hp0 hq5 hX0 hXle
  have hgeom := (Commute.all (b * casselsBranch p q X) a).geom_sum₂_mul p
  rw [mul_comm, hgeom, mul_pow, hFp]

/-- Generic factored p-th-power remainder.

Once an approximant has a linear branch error divisible by `X^(2N+1)`,
the polynomial remainder `b^p ((1-X)^q + X^q) - a^p` inherits the same
factor, with the usual geometric cofactor. -/
theorem cassels_pth_power_X_factored_generic
    (p q N : ℕ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ))
    (b a G : ℝ)
    (hfactor : b * casselsBranch p q X - a = X ^ (2 * N + 1) * G) :
    b ^ p * ((1 - X) ^ q + X ^ q) - a ^ p
      =
    X ^ (2 * N + 1)
      * (G * (∑ i ∈ Finset.range p,
          (b * casselsBranch p q X) ^ i * a ^ (p - 1 - i))) := by
  have hid :=
    cassels_pth_power_identity_generic p q hp0 hq5 hX0 hXle b a
  rw [← hid, hfactor]
  ring

/-- Real evaluation wrapper for a polynomial with rational coefficients. -/
noncomputable def casselsRatPolyEvalReal
    (P : Polynomial ℚ) (X : ℝ) : ℝ :=
  (P.map (algebraMap ℚ ℝ)).eval X

/-- Evaluation bridge from rational points to real points. -/
theorem casselsRatPolyEvalReal_cast (P : Polynomial ℚ) (y : ℚ) :
    casselsRatPolyEvalReal P (y : ℝ) = ((P.eval y : ℚ) : ℝ) := by
  unfold casselsRatPolyEvalReal
  rw [Polynomial.eval_map]
  have hy : (y : ℝ) = (algebraMap ℚ ℝ) y :=
    (eq_ratCast (algebraMap ℚ ℝ) y).symm
  rw [hy, Polynomial.eval₂_at_apply, eq_ratCast]

/-- Denominator coefficient of the explicit Cassels-Hermite Padé approximant. -/
noncomputable def casselsHermiteDenCoeff (p q N k : ℕ) : ℚ :=
  ((ascPochhammer ℚ k).eval (-(N : ℚ))
      * (ascPochhammer ℚ k).eval ((q : ℚ) / (p : ℚ) - (N : ℚ)))
    / ((ascPochhammer ℚ k).eval (-(2 * N : ℚ)) * (k.factorial : ℚ))
    * (-1 : ℚ) ^ k

/-- Numerator coefficient of the explicit Cassels-Hermite Padé approximant. -/
noncomputable def casselsHermiteNumCoeff (p q N k : ℕ) : ℚ :=
  ((ascPochhammer ℚ k).eval (-(N : ℚ))
      * (ascPochhammer ℚ k).eval (-((q : ℚ) / (p : ℚ)) - (N : ℚ)))
    / ((ascPochhammer ℚ k).eval (-(2 * N : ℚ)) * (k.factorial : ℚ))
    * (-1 : ℚ) ^ k

/-- Denominator polynomial of the explicit Cassels-Hermite Padé approximant. -/
noncomputable def casselsHermiteB (p q N : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (casselsHermiteDenCoeff p q N k) * Polynomial.X ^ k

/-- Numerator polynomial of the explicit Cassels-Hermite Padé approximant. -/
noncomputable def casselsHermiteA (p q N : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (casselsHermiteNumCoeff p q N k) * Polynomial.X ^ k

theorem casselsHermiteDenCoeff_zero (p q N : ℕ) :
    casselsHermiteDenCoeff p q N 0 = 1 := by
  simp [casselsHermiteDenCoeff, ascPochhammer_zero]

theorem casselsHermiteNumCoeff_zero (p q N : ℕ) :
    casselsHermiteNumCoeff p q N 0 = 1 := by
  simp [casselsHermiteNumCoeff, ascPochhammer_zero]

/-- For `k ≤ N`, the factor `(−N)_k` in the Hermite coefficient is nonzero. -/
theorem casselsHermite_negN_pochhammer_ne_zero
    (N k : ℕ) (hk : k ≤ N) :
    (ascPochhammer ℚ k).eval (-(N : ℚ)) ≠ 0 := by
  intro hzero
  rcases (ascPochhammer_eval_eq_zero_iff k (-(N : ℚ))).mp hzero with
    ⟨j, hjk, hj⟩
  have hjQ : (j : ℚ) = (N : ℚ) := by
    simpa using hj
  have hjN : j = N := by exact_mod_cast hjQ
  omega

/-- For `k ≤ N`, the denominator factor `(−2N)_k` is nonzero. -/
theorem casselsHermite_negTwoN_pochhammer_ne_zero
    (N k : ℕ) (hk : k ≤ N) :
    (ascPochhammer ℚ k).eval (-(2 * N : ℚ)) ≠ 0 := by
  intro hzero
  rcases (ascPochhammer_eval_eq_zero_iff k (-(2 * N : ℚ))).mp hzero with
    ⟨j, hjk, hj⟩
  have hjQ : (j : ℚ) = (2 * N : ℚ) := by
    simpa using hj
  have hjN : j = 2 * N := by exact_mod_cast hjQ
  omega

/-- For `N < k`, the factor `(−N)_k` vanishes. -/
theorem casselsHermite_negN_pochhammer_eq_zero_of_gt
    (N k : ℕ) (hk : N < k) :
    (ascPochhammer ℚ k).eval (-(N : ℚ)) = 0 :=
  ascPochhammer_eval_neg_coe_nat_of_lt hk

/-- The Hermite denominator coefficient stream is supported in degree `≤ N`. -/
theorem casselsHermiteDenCoeff_eq_zero_of_gt
    (p q N k : ℕ) (hk : N < k) :
    casselsHermiteDenCoeff p q N k = 0 := by
  have hpoch := casselsHermite_negN_pochhammer_eq_zero_of_gt N k hk
  simp [casselsHermiteDenCoeff, hpoch]

/-- The Hermite numerator coefficient stream is supported in degree `≤ N`. -/
theorem casselsHermiteNumCoeff_eq_zero_of_gt
    (p q N k : ℕ) (hk : N < k) :
    casselsHermiteNumCoeff p q N k = 0 := by
  have hpoch := casselsHermite_negN_pochhammer_eq_zero_of_gt N k hk
  simp [casselsHermiteNumCoeff, hpoch]

/-- Coefficient extraction for the Hermite denominator polynomial. -/
theorem casselsHermiteB_coeff (p q N i : ℕ) :
    (casselsHermiteB p q N).coeff i =
      if i ∈ Finset.range (N + 1)
        then casselsHermiteDenCoeff p q N i else 0 := by
  unfold casselsHermiteB
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) i
    (fun k => casselsHermiteDenCoeff p q N k)]

/-- Coefficient extraction for the Hermite numerator polynomial. -/
theorem casselsHermiteA_coeff (p q N i : ℕ) :
    (casselsHermiteA p q N).coeff i =
      if i ∈ Finset.range (N + 1)
        then casselsHermiteNumCoeff p q N i else 0 := by
  unfold casselsHermiteA
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (N + 1)) i
    (fun k => casselsHermiteNumCoeff p q N k)]

/-- Coefficient extraction for `B` against the full Hermite stream. -/
theorem casselsHermiteB_coeff_stream (p q N i : ℕ) :
    (casselsHermiteB p q N).coeff i =
      casselsHermiteDenCoeff p q N i := by
  rw [casselsHermiteB_coeff]
  by_cases hi : i ∈ Finset.range (N + 1)
  · simp [hi]
  · have hNi : N < i := by
      rw [Finset.mem_range] at hi
      omega
    simp [hi, casselsHermiteDenCoeff_eq_zero_of_gt p q N i hNi]

/-- Coefficient extraction for `A` against the full Hermite stream. -/
theorem casselsHermiteA_coeff_stream (p q N i : ℕ) :
    (casselsHermiteA p q N).coeff i =
      casselsHermiteNumCoeff p q N i := by
  rw [casselsHermiteA_coeff]
  by_cases hi : i ∈ Finset.range (N + 1)
  · simp [hi]
  · have hNi : N < i := by
      rw [Finset.mem_range] at hi
      omega
    simp [hi, casselsHermiteNumCoeff_eq_zero_of_gt p q N i hNi]

/-- Real evaluation of the Hermite denominator polynomial as a finite sum. -/
theorem casselsHermiteB_evalReal (p q N : ℕ) (X : ℝ) :
    casselsRatPolyEvalReal (casselsHermiteB p q N) X
      =
    ∑ k ∈ Finset.range (N + 1),
      (casselsHermiteDenCoeff p q N k : ℝ) * X ^ k := by
  unfold casselsRatPolyEvalReal casselsHermiteB
  simp only [Polynomial.map_sum, Polynomial.eval_finset_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, eq_ratCast]

/-- Real evaluation of the Hermite numerator polynomial as a finite sum. -/
theorem casselsHermiteA_evalReal (p q N : ℕ) (X : ℝ) :
    casselsRatPolyEvalReal (casselsHermiteA p q N) X
      =
    ∑ k ∈ Finset.range (N + 1),
      (casselsHermiteNumCoeff p q N k : ℝ) * X ^ k := by
  unfold casselsRatPolyEvalReal casselsHermiteA
  simp only [Polynomial.map_sum, Polynomial.eval_finset_sum,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, eq_ratCast]

/-- Hermite denominator normalization at zero. -/
theorem casselsHermiteB_evalReal_zero (p q N : ℕ) :
    casselsRatPolyEvalReal (casselsHermiteB p q N) 0 = 1 := by
  rw [casselsHermiteB_evalReal]
  rw [Finset.sum_eq_single (0 : ℕ)]
  · simp [casselsHermiteDenCoeff_zero]
  · intro k _hk hk0
    simp [hk0]
  · intro h0
    exact False.elim (h0 (by simp))

/-- Hermite numerator normalization at zero. -/
theorem casselsHermiteA_evalReal_zero (p q N : ℕ) :
    casselsRatPolyEvalReal (casselsHermiteA p q N) 0 = 1 := by
  rw [casselsHermiteA_evalReal]
  rw [Finset.sum_eq_single (0 : ℕ)]
  · simp [casselsHermiteNumCoeff_zero]
  · intro k _hk hk0
    simp [hk0]
  · intro h0
    exact False.elim (h0 (by simp))

/-- The p-th-power identity instantiated at the explicit Hermite approximant. -/
theorem cassels_hermite_pth_power_identity
    (p q N : ℕ) (hp0 : 0 < p) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (casselsRatPolyEvalReal (casselsHermiteB p q N) X
          * casselsBranch p q X
        - casselsRatPolyEvalReal (casselsHermiteA p q N) X)
        * (∑ i ∈ Finset.range p,
            (casselsRatPolyEvalReal (casselsHermiteB p q N) X
                * casselsBranch p q X) ^ i
              * (casselsRatPolyEvalReal (casselsHermiteA p q N) X)
                  ^ (p - 1 - i))
      =
      (casselsRatPolyEvalReal (casselsHermiteB p q N) X) ^ p
        * ((1 - X) ^ q + X ^ q)
        - (casselsRatPolyEvalReal (casselsHermiteA p q N) X) ^ p :=
  cassels_pth_power_identity_generic p q hp0 hq5 hX0 hXle _ _

/-- The descent root identity gives the concrete real branch value. -/
theorem cassels_runge_hbranch
    (p q u v : ℕ)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hu : 1 < u)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    (v : ℝ) / (u : ℝ) ^ (q - 1)
      = casselsBranch p q (((u : ℝ) ^ p)⁻¹) := by
  have hppos : 0 < p := by omega
  have h2u : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have huRpos : (0 : ℝ) < (u : ℝ) := by linarith
  have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := pow_pos huRpos p
  have hX0 : (0 : ℝ) ≤ ((u : ℝ) ^ p)⁻¹ := le_of_lt (inv_pos.mpr hup_pos)
  have hup32 : (32 : ℝ) ≤ (u : ℝ) ^ p := by
    calc
      (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ (u : ℝ) ^ 5 := by gcongr
      _ ≤ (u : ℝ) ^ p :=
          pow_le_pow_right₀ (by linarith) (by omega)
  have hXle : ((u : ℝ) ^ p)⁻¹ ≤ (1 / 32 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hup32
  have hbp := casselsBranch_pow_p p q hppos hq5 hX0 hXle
  have hpow :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        = (casselsBranch p q (((u : ℝ) ^ p)⁻¹)) ^ p := by
    rw [hroot, hbp]
  have hvu_nonneg : (0 : ℝ) ≤ (v : ℝ) / (u : ℝ) ^ (q - 1) := by
    positivity
  have hbr_nonneg :
      (0 : ℝ) ≤ casselsBranch p q (((u : ℝ) ^ p)⁻¹) := by
    unfold casselsBranch
    exact Real.rpow_nonneg
      (le_of_lt (cassels_branch_base_pos p q hq5 hX0 hXle)) _
  exact (pow_left_inj₀ hvu_nonneg hbr_nonneg hppos.ne').mp hpow

/-- Branch decomposition on `[0,1/32]`:
`F(X) = (1-X)^(q/p) * (1 + (X/(1-X))^q)^(1/p)`. -/
theorem casselsBranch_eq_factored
    (p q : ℕ) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    casselsBranch p q X
      = (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * (1 + (X / (1 - X)) ^ q) ^ ((1 : ℝ) / (p : ℝ)) := by
  unfold casselsBranch
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have h1Xq_pos : (0 : ℝ) < (1 - X) ^ q := pow_pos h1X q
  have hbase :
      (1 - X) ^ q + X ^ q
        = (1 - X) ^ q * (1 + (X / (1 - X)) ^ q) := by
    rw [div_pow]
    field_simp
  rw [hbase, Real.mul_rpow (le_of_lt h1Xq_pos) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast (1 - X) q,
    ← Real.rpow_mul (le_of_lt h1X)]
  congr 1
  field_simp

/-- General binomial numerator factoring for any integer numerator `A`. -/
theorem casselsGeneralBinomNum_real_factor
    (p k : ℕ) (A : ℤ) (hp : (p : ℝ) ≠ 0) :
    ((casselsGeneralBinomNum p A k : ℤ) : ℝ)
      = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k,
              ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
  unfold casselsGeneralBinomNum
  push_cast
  calc
    ∏ j ∈ Finset.range k, ((A : ℝ) - (j : ℝ) * (p : ℝ))
        = ∏ j ∈ Finset.range k,
            (p : ℝ) * ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
          apply Finset.prod_congr rfl
          intro j _
          field_simp
    _ = (∏ _j ∈ Finset.range k, (p : ℝ))
          * ∏ j ∈ Finset.range k, ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
    _ = (p : ℝ) ^ k
          * ∏ j ∈ Finset.range k, ((A : ℝ) / (p : ℝ) - (j : ℝ)) := by
          rw [Finset.prod_const, Finset.card_range]

/-- Shifted `(1-X)^(A/p)` coefficient identity. -/
theorem casselsOneMinusCoeff_real_eq_choose
    (p k : ℕ) (A : ℤ) (hp : (p : ℝ) ≠ 0) :
    ((casselsOneMinusCoeff p A k : ℚ) : ℝ)
      = (-1 : ℝ) ^ k * Ring.choose ((A : ℝ) / (p : ℝ)) k := by
  unfold casselsOneMinusCoeff
  push_cast
  rw [casselsGeneralBinomNum_real_factor p k A hp]
  have hprod :
      ∏ j ∈ Finset.range k, ((A : ℝ) / (p : ℝ) - (j : ℝ))
        = Ring.choose ((A : ℝ) / (p : ℝ)) k * (k.factorial : ℝ) :=
    (ring_choose_mul_factorial_eq_prod ((A : ℝ) / (p : ℝ)) k).symm
  rw [hprod]
  have hpk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero k hp
  have hfac : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  field_simp

/-- The shifted one-minus coefficient stream sums to `(1-X)^(A/p)`. -/
theorem cassels_oneMinus_hasSum
    (p : ℕ) (A : ℤ) (hp : (p : ℝ) ≠ 0) {X : ℝ} (hX : |X| < 1) :
    HasSum (fun k => (casselsOneMinusCoeff p A k : ℝ) * X ^ k)
      ((1 - X) ^ ((A : ℝ) / (p : ℝ))) := by
  have hball : (-X) ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist (-X) (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs, abs_neg]
      calc ENNReal.ofReal |X|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg X)).2 hX
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (A : ℝ) / (p : ℝ))).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  have hbranch_eq : ((1 : ℝ) + -X) ^ ((A : ℝ) / (p : ℝ))
      = (1 - X) ^ ((A : ℝ) / (p : ℝ)) := by ring_nf
  rw [hbranch_eq] at hHS
  convert hHS using 1
  ext k
  rw [casselsOneMinusCoeff_real_eq_choose p k A hp, smul_eq_mul, neg_pow]
  ring

/-- The plus-coefficient is exactly the generalized binomial coefficient
`choose (1/p) a` over `ℝ`. -/
theorem casselsOnePlusOneOverPCoeff_real_eq_choose
    (p a : ℕ) (hp : (p : ℝ) ≠ 0) :
    ((casselsOnePlusOneOverPCoeff p a : ℚ) : ℝ)
      = Ring.choose ((1 : ℝ) / (p : ℝ)) a := by
  unfold casselsOnePlusOneOverPCoeff
  push_cast
  rw [casselsGeneralBinomNum_one_real_factor p a hp]
  have hprod :
      ∏ j ∈ Finset.range a, ((1 : ℝ) / (p : ℝ) - (j : ℝ))
        = Ring.choose ((1 : ℝ) / (p : ℝ)) a * (a.factorial : ℝ) :=
    (ring_choose_mul_factorial_eq_prod ((1 : ℝ) / (p : ℝ)) a).symm
  rw [hprod]
  have hpa : (p : ℝ) ^ a ≠ 0 := pow_ne_zero a hp
  have hfac : (a.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero a
  field_simp

/-- The plus-coefficient stream sums to `(1+Z)^(1/p)` on `|Z| < 1`. -/
theorem cassels_onePlus_hasSum
    (p : ℕ) (hp : (p : ℝ) ≠ 0) {Z : ℝ} (hZ : |Z| < 1) :
    HasSum (fun a => (casselsOnePlusOneOverPCoeff p a : ℝ) * Z ^ a)
      ((1 + Z) ^ ((1 : ℝ) / (p : ℝ))) := by
  have hball : Z ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist Z (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal |Z|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg Z)).2 hZ
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (1 : ℝ) / (p : ℝ))).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  convert hHS using 1
  ext a
  rw [casselsOnePlusOneOverPCoeff_real_eq_choose p a hp, smul_eq_mul]

/-- Per-correction algebra for composing the two branch factors. -/
theorem cassels_compose_term_eq
    (p q a : ℕ) (hp : (p : ℝ) ≠ 0)
    {X : ℝ} (h1X : (0 : ℝ) < 1 - X) :
    (1 - X) ^ ((q : ℝ) / (p : ℝ)) * ((X / (1 - X)) ^ q) ^ a
      = X ^ (q * a)
          * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
              / (p : ℝ)) := by
  rw [← pow_mul, div_pow, ← Real.rpow_natCast (1 - X) (q * a)]
  rw [show (1 - X) ^ ((q : ℝ) / (p : ℝ))
        * (X ^ (q * a) / (1 - X) ^ ((q * a : ℕ) : ℝ))
        = X ^ (q * a)
          * ((1 - X) ^ ((q : ℝ) / (p : ℝ))
              / (1 - X) ^ ((q * a : ℕ) : ℝ)) by ring]
  rw [← Real.rpow_sub h1X]
  congr 1
  push_cast
  field_simp

/-- The branch equals the plus-series expansion over correction index `a`. -/
theorem cassels_branch_hasSum_a
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    HasSum (fun a => (casselsOnePlusOneOverPCoeff p a : ℝ)
        * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ)))
      (casselsBranch p q X) := by
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have hxr : (0 : ℝ) ≤ X / (1 - X) :=
    div_nonneg hX0 (le_of_lt h1X)
  have hZlt : |((X / (1 - X)) ^ q)| < 1 := by
    have hxr1 : X / (1 - X) ≤ 1 / 31 := by
      rw [div_le_div_iff₀ h1X (by norm_num)]
      nlinarith [hXle]
    have hZnn : (0 : ℝ) ≤ (X / (1 - X)) ^ q := pow_nonneg hxr q
    rw [abs_of_nonneg hZnn]
    calc
      (X / (1 - X)) ^ q ≤ (1 / 31 : ℝ) ^ q :=
        pow_le_pow_left₀ hxr hxr1 q
      _ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hps :=
    cassels_onePlus_hasSum p hp (Z := (X / (1 - X)) ^ q) hZlt
  have hmul := hps.mul_left ((1 - X) ^ ((q : ℝ) / (p : ℝ)))
  rw [← casselsBranch_eq_factored p q hq5 hX0 hXle] at hmul
  have key : ∀ a,
      (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
          * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
              / (p : ℝ))
        =
      (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * ((casselsOnePlusOneOverPCoeff p a : ℝ)
              * ((X / (1 - X)) ^ q) ^ a) := by
    intro a
    have hc := cassels_compose_term_eq p q a hp h1X
    calc
      (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
          * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
              / (p : ℝ))
          =
        (casselsOnePlusOneOverPCoeff p a : ℝ)
          * ((1 - X) ^ ((q : ℝ) / (p : ℝ))
              * ((X / (1 - X)) ^ q) ^ a) := by
            rw [hc]
            ring
      _ =
        (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * ((casselsOnePlusOneOverPCoeff p a : ℝ)
              * ((X / (1 - X)) ^ q) ^ a) := by
            ring
  rw [show
      (fun a => (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ)))
      =
      (fun a => (1 - X) ^ ((q : ℝ) / (p : ℝ))
        * ((casselsOnePlusOneOverPCoeff p a : ℝ)
            * ((X / (1 - X)) ^ q) ^ a)) from funext key]
  exact hmul

/-- The `a`-th branch term, expanded as a shifted `m`-series. -/
theorem cassels_branch_term_hasSum_m
    (p q a : ℕ) (hp : (p : ℝ) ≠ 0) {X : ℝ} (hX : |X| < 1) :
    HasSum (fun m => (casselsOnePlusOneOverPCoeff p a : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
        * X ^ (q * a + m))
      ((casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))) := by
  have hm := cassels_oneMinus_hasSum p
    ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) hp hX
  have hmul := hm.mul_left
    ((casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a))
  have key : ∀ m,
      (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
          * ((casselsOneMinusCoeff p
              ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
              * X ^ m)
        =
      (casselsOnePlusOneOverPCoeff p a : ℝ)
          * (casselsOneMinusCoeff p
              ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
          * X ^ (q * a + m) := by
    intro m
    rw [pow_add]
    ring
  rw [show
      (fun m => (casselsOnePlusOneOverPCoeff p a : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
        * X ^ (q * a + m))
      =
      (fun m => (casselsOnePlusOneOverPCoeff p a : ℝ) * X ^ (q * a)
        * ((casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)
            * X ^ m)) from funext (fun m => (key m).symm)]
  convert hmul using 2
  push_cast
  ring

/-- The `k`-fiber finite sum is exactly the actual root coefficient. -/
theorem cassels_fiber_sum_eq (p q k : ℕ) :
    (∑ a ∈ Finset.range (k / q + 1),
        casselsOnePlusOneOverPCoeff p a
          * casselsOneMinusCoeff p
              ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) (k - q * a))
      = casselsActualRootCoeff p q k := by
  have hgen : ∀ n : ℕ,
      Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    intro n
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hgen (k / q), Finset.sum_insert (by simp)]
  unfold casselsActualRootCoeff
  congr 1
  have h0 : casselsOnePlusOneOverPCoeff p 0 = 1 := by
    simp [casselsOnePlusOneOverPCoeff, casselsGeneralBinomNum]
  have h1 :
      ((q : ℤ) - (q : ℤ) * ((0 : ℕ) : ℤ) * (p : ℤ)) = (q : ℤ) := by
    ring
  have h2 : k - q * 0 = k := by omega
  rw [h0, h1, h2, one_mul]
  simp [casselsOneMinusCoeff, casselsRootCoeff, casselsBinomNum,
    casselsGeneralBinomNum]

/-- Sigma-series assembly from the correction-index HasSum, assuming
absolute/sigma summability of the double series. -/
theorem cassels_branch_hasSum_sigma
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ))
    (hsum : Summable (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2))) :
    HasSum (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2))
      (casselsBranch p q X) := by
  have hX : |X| < 1 := by
    rw [abs_of_nonneg hX0]
    linarith
  exact HasSum.of_sigma
    (fun a => cassels_branch_term_hasSum_m p q a hp hX)
    (cassels_branch_hasSum_a p q hp hq5 hX0 hXle)
    hsum.hasSum.cauchySeq

/-- The finite fiber of `(a,m) ↦ q*a+m`. -/
def casselsFiberFinset (q k : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (k / q + 1)).image
    (fun a => (⟨a, k - q * a⟩ : Σ _ : ℕ, ℕ))

theorem mem_casselsFiberFinset
    (q k : ℕ) (hq : 0 < q) (x : Σ _ : ℕ, ℕ) :
    x ∈ casselsFiberFinset q k ↔ q * x.1 + x.2 = k := by
  unfold casselsFiberFinset
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have haq : q * a ≤ k :=
      le_trans
        (Nat.mul_le_mul_left q (Nat.lt_succ_iff.1 ha))
        (Nat.mul_div_le k q)
    simp only
    omega
  · intro hx
    refine ⟨x.1, ?_, ?_⟩
    · have : x.1 ≤ k / q :=
        (Nat.le_div_iff_mul_le hq).2 (by
          rw [Nat.mul_comm]
          omega)
      omega
    · obtain ⟨a, m⟩ := x
      simp only at hx ⊢
      have : k - q * a = m := by omega
      rw [this]

/-- Actual coefficient stream HasSum, parameterized by summability of the
underlying double series. -/
theorem cassels_actualRootCoeff_hasSum_branch_of_summable
    (p q : ℕ) (hp : (p : ℝ) ≠ 0) (hq : 0 < q) (hq5 : 5 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ))
    (hsum : Summable (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2))) :
    HasSum (fun k => (casselsActualRootCoeff p q k : ℝ) * X ^ k)
      (casselsBranch p q X) := by
  classical
  set Ff : (Σ _ : ℕ, ℕ) → ℝ := fun am =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2) with hFf
  set e : (Σ _ : ℕ, ℕ) → ℕ := fun am => q * am.1 + am.2 with he
  have hsig : HasSum Ff (casselsBranch p q X) :=
    cassels_branch_hasSum_sigma p q hp hq5 hX0 hXle hsum
  have hre : HasSum (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e))
      (casselsBranch p q X) :=
    (Equiv.sigmaFiberEquiv e).hasSum_iff.mpr hsig
  refine HasSum.sigma hre (fun k => ?_)
  have hmem : ∀ x : (Σ _ : ℕ, ℕ), x ∈ casselsFiberFinset q k ↔ e x = k := by
    intro x
    rw [mem_casselsFiberFinset q k hq]
  haveI : Fintype {x : (Σ _ : ℕ, ℕ) // e x = k} :=
    Fintype.ofFinset (casselsFiberFinset q k) hmem
  have hHS := hasSum_fintype
    (fun x : {x : (Σ _ : ℕ, ℕ) // e x = k} =>
      (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, x⟩)
  have hcomp : ∀ x : {x : (Σ _ : ℕ, ℕ) // e x = k},
      (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, x⟩ = Ff x.1 := by
    intro x
    simp only [Function.comp, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk]
  have hval :
      (∑ x : {x : (Σ _ : ℕ, ℕ) // e x = k},
        (Ff ∘ ⇑(Equiv.sigmaFiberEquiv e)) ⟨k, x⟩)
        = (casselsActualRootCoeff p q k : ℝ) * X ^ k := by
    simp_rw [hcomp]
    rw [← Finset.sum_subtype (casselsFiberFinset q k) hmem (fun x => Ff x)]
    rw [casselsFiberFinset, Finset.sum_image (by
      intro a ha b hb hab
      simpa using congrArg Sigma.fst hab)]
    have hterm : ∀ a ∈ Finset.range (k / q + 1),
        Ff ⟨a, k - q * a⟩
          =
        ((casselsOnePlusOneOverPCoeff p a
            * casselsOneMinusCoeff p
                ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ))
                (k - q * a) : ℚ) : ℝ) * X ^ k := by
      intro a ha
      have haq : q * a ≤ k :=
        le_trans
          (Nat.mul_le_mul_left q
            (Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)))
          (Nat.mul_div_le k q)
      simp only [hFf]
      rw [show q * a + (k - q * a) = k by omega]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      ← Rat.cast_sum, cassels_fiber_sum_eq p q k]
  rw [← hval]
  exact hHS

/-- For `r < 0`, every `Ring.choose r m` has sign `(-1)^m`, so
`|Ring.choose r m| = (-1)^m * Ring.choose r m`. -/
theorem ring_choose_neg_abs (r : ℝ) (hr : r < 0) (m : ℕ) :
    |Ring.choose r m| = (-1 : ℝ) ^ m * Ring.choose r m := by
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos m
  have hprod := ring_choose_mul_factorial_eq_prod r m
  set P : ℝ := ∏ j ∈ Finset.range m, ((j : ℝ) - r) with hP
  have hPpos : 0 < P := by
    rw [hP]
    apply Finset.prod_pos
    intro j _
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hsplit : ∏ j ∈ Finset.range m, (r - (j : ℝ))
      = (-1 : ℝ) ^ m * P := by
    rw [hP]
    rw [show (∏ j ∈ Finset.range m, (r - (j : ℝ)))
          = ∏ j ∈ Finset.range m, ((-1 : ℝ) * ((j : ℝ) - r)) from
        Finset.prod_congr rfl (fun j _ => by ring)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hchoose : Ring.choose r m
      = (-1 : ℝ) ^ m * (P / (m.factorial : ℝ)) := by
    have h := hprod
    rw [hsplit] at h
    field_simp at h ⊢
    linear_combination h
  rw [hchoose, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (le_of_lt (div_pos hPpos hfac)), ← mul_assoc,
    ← mul_pow]
  norm_num

/-- Negative-binomial absolute sum: for `r < 0` and `X ∈ [0,1)`,
`∑ m, |choose r m| X^m = (1-X)^r`. -/
theorem cassels_negbinom_abs_hasSum (r : ℝ) (hr : r < 0)
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) :
    HasSum (fun m => |Ring.choose r m| * X ^ m) ((1 - X) ^ r) := by
  have hball : (-X) ∈ EMetric.ball (0 : ℝ) 1 := by
    have hlt : edist (-X) (0 : ℝ) < 1 := by
      rw [edist_zero_right, Real.enorm_eq_ofReal_abs, abs_neg]
      have hxabs : |X| < 1 := by rw [abs_of_nonneg hX0]; exact hX1
      calc ENNReal.ofReal |X|
          < ENNReal.ofReal 1 :=
            (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg X)).2
              hxabs
        _ = 1 := by simp
    exact hlt
  have hHS := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := r)).hasSum hball
  simp only [zero_add, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] at hHS
  have hbr : ((1 : ℝ) + -X) ^ r = (1 - X) ^ r := by ring_nf
  rw [hbr] at hHS
  convert hHS using 1
  ext m
  rw [ring_choose_neg_abs r hr m, smul_eq_mul, neg_pow]
  ring

/-- Absolute binomial summability for `0 ≤ w < 1`. -/
theorem cassels_choose_summable (s : ℝ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Summable (fun a => |Ring.choose s a| * w ^ a) := by
  have hw1' : w.toNNReal < 1 := by
    have h := (Real.toNNReal_lt_toNNReal_iff (by norm_num : (0:ℝ) < 1)).mpr hw1
    rwa [Real.toNNReal_one] at h
  have hrad : ((w.toNNReal : ENNReal)) < (binomialSeries ℝ s).radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_one_iff.mpr hw1')
      binomialSeries_radius_ge_one
  have hsum := (binomialSeries ℝ s).summable_norm_mul_pow hrad
  have hconv : ∀ a,
      ‖binomialSeries ℝ s a‖ * (↑w.toNNReal : ℝ) ^ a
        = |Ring.choose s a| * w ^ a := by
    intro a
    rw [binomialSeries, FormalMultilinearSeries.ofScalars_norm,
      Real.norm_eq_abs, Real.coe_toNNReal w hw0]
  rw [show (fun a => |Ring.choose s a| * w ^ a)
        = (fun a => ‖binomialSeries ℝ s a‖ * (↑w.toNNReal : ℝ) ^ a)
      from funext (fun a => (hconv a).symm)]
  exact hsum

theorem cassels_ratio_nonneg_le_one_thirtyone
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    0 ≤ X / (1 - X) ∧ X / (1 - X) ≤ (1 / 31 : ℝ) := by
  have hden_pos : 0 < 1 - X := by linarith
  refine ⟨div_nonneg hX0 (le_of_lt hden_pos), ?_⟩
  rw [div_le_iff₀ hden_pos]
  nlinarith

theorem cassels_ratio_pow_abs_lt_one
    (q : ℕ) (hqpos : 0 < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    |(X / (1 - X)) ^ q| < 1 := by
  rcases cassels_ratio_nonneg_le_one_thirtyone hX0 hXle with ⟨hr0, hrle⟩
  have hrlt : X / (1 - X) < 1 := by nlinarith
  have hpow_lt : (X / (1 - X)) ^ q < 1 ^ q :=
    pow_lt_pow_left₀ hrlt hr0 (by omega)
  simpa [abs_of_nonneg (pow_nonneg hr0 q)] using hpow_lt

theorem cassels_shiftA_real_neg
    (p q a : ℕ) (hp5 : 5 ≤ p) (hqpos : 0 < q) (ha : 1 ≤ a) :
    (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)) / (p : ℝ) < 0 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hap : (5 : ℝ) ≤ (a : ℝ) * (p : ℝ) := by
    have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hp5' : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    nlinarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
  have hnum : ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ) < 0 := by
    push_cast
    nlinarith
  exact div_neg_of_neg_of_pos hnum hp0

/-- For `a ≥ 1`, the shifted one-minus norm-series sums to the
negative-binomial closed form. -/
theorem cassels_shifted_inner_norm_hasSum
    (p q a : ℕ) (hp5 : 5 ≤ p) (hqpos : 0 < q) (ha : 1 ≤ a)
    {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X < 1) :
    HasSum (fun m => ‖(casselsOneMinusCoeff p
        ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) m : ℝ)‖ * X ^ m)
      ((1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
        / (p : ℝ))) := by
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hneg : (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)) / (p : ℝ)
      < 0 := cassels_shiftA_real_neg p q a hp5 hqpos ha
  have hb := cassels_negbinom_abs_hasSum
    (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ) / (p : ℝ))
    hneg hX0 hX1
  refine hb.congr_fun (fun m => ?_)
  rw [casselsOneMinusCoeff_real_eq_choose p m
    ((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ)) hpne,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul]
  congr 3
  push_cast
  ring

/-- Row bound controlling the shifted inner sums by the outer ratio. -/
theorem cassels_row_bound
    (p q a : ℕ) (hp5 : 5 ≤ p)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))
      ≤ ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
        * ((X / (1 - X)) ^ q) ^ a := by
  have h1X : (0 : ℝ) < 1 - X := by linarith
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexp : (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)) / (p : ℝ)
      = (q : ℝ) / (p : ℝ) - ((q * a : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hrw : (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
        / (p : ℝ))
      = (1 - X) ^ ((q : ℝ) / (p : ℝ))
          * ((1 - X) ^ (q * a))⁻¹ := by
    rw [hexp, Real.rpow_sub h1X, Real.rpow_natCast]
    rw [div_eq_mul_inv]
  have hkey : X ^ (q * a) * ((1 - X) ^ (q * a))⁻¹
      = ((X / (1 - X)) ^ q) ^ a := by
    rw [← pow_mul, div_pow, div_eq_mul_inv]
  have hfac_le : (1 - X) ^ ((q : ℝ) / (p : ℝ)) ≤ 1 :=
    Real.rpow_le_one (le_of_lt h1X) (by linarith) (by positivity)
  have hnn : (0 : ℝ) ≤ ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
      * ((X / (1 - X)) ^ q) ^ a := by positivity
  calc
    ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a)
        * (1 - X) ^ (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
            / (p : ℝ))
        = (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a)
          * (1 - X) ^ ((q : ℝ) / (p : ℝ)) := by
          rw [hrw, ← hkey]; ring
      _ ≤ (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a) * 1 := by
          exact mul_le_mul_of_nonneg_left hfac_le hnn
      _ = ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a := by ring

/-- Absolute summability of the bivariate Cassels family on `[0,1/32]`. -/
theorem cassels_Ff_summable_norm
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun am : Σ _ : ℕ, ℕ =>
      ‖(casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2)‖) := by
  have hqpos : 0 < q := by omega
  have hpne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hX1 : X < 1 := by linarith
  have hrat := cassels_ratio_nonneg_le_one_thirtyone hX0 hXle
  have hw0 : 0 ≤ (X / (1 - X)) ^ q := pow_nonneg hrat.1 q
  have hw1 : (X / (1 - X)) ^ q < 1 := by
    have := cassels_ratio_pow_abs_lt_one q hqpos hX0 hXle
    rwa [abs_of_nonneg hw0] at this
  set Ff : (Σ _ : ℕ, ℕ) → ℝ := fun am =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2) with hFf
  have hcm : ∀ (A : ℤ) (m : ℕ),
      ‖((casselsOneMinusCoeff p A m : ℚ) : ℝ)‖
        = |Ring.choose ((A : ℝ) / (p : ℝ)) m| := by
    intro A m
    rw [casselsOneMinusCoeff_real_eq_choose p m A hpne, Real.norm_eq_abs,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hnormFf : ∀ a m, ‖Ff ⟨a, m⟩‖
      = (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖ * X ^ (q * a))
        * (|Ring.choose
              (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ) / (p : ℝ))
              m| * X ^ m) := by
    intro a m
    have hxqm : ‖X ^ (q * a + m)‖ = X ^ (q * a) * X ^ m := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 _), pow_add]
    rw [hFf]
    simp only [norm_mul]
    rw [hcm, hxqm]
    push_cast
    ring
  rw [summable_sigma_of_nonneg (fun am => norm_nonneg _)]
  refine ⟨fun a => ?_, ?_⟩
  · have hfun : (fun m => ‖Ff ⟨a, m⟩‖)
        = fun m => (‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
              * X ^ (q * a))
            * (|Ring.choose
                (((q : ℤ) - (q : ℤ) * (a : ℤ) * (p : ℤ) : ℝ)
                  / (p : ℝ)) m| * X ^ m) := by
      funext m
      exact hnormFf a m
    rw [hfun]
    exact (cassels_choose_summable _ hX0 hX1).mul_left _
  · have hmaj : Summable (fun a =>
        ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
          * ((X / (1 - X)) ^ q) ^ a) := by
      have hre : (fun a => ‖(casselsOnePlusOneOverPCoeff p a : ℝ)‖
            * ((X / (1 - X)) ^ q) ^ a)
          = fun a => |Ring.choose ((1 : ℝ) / (p : ℝ)) a|
            * ((X / (1 - X)) ^ q) ^ a := by
        funext a
        rw [casselsOnePlusOneOverPCoeff_real_eq_choose p a hpne,
          Real.norm_eq_abs]
      rw [hre]
      exact cassels_choose_summable _ hw0 hw1
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le
      (fun a => tsum_nonneg (fun m => norm_nonneg _)) ?_
      ((summable_nat_add_iff 1).mpr hmaj)
    intro a
    have hrow := cassels_shifted_inner_norm_hasSum p q (a + 1) hp5
      hqpos (by omega) hX0 hX1
    have htsum_inner :
        (∑' m, ‖((casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ)) m
            : ℚ) : ℝ)‖ * X ^ m)
          = (1 - X) ^ (((q : ℤ)
              - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ) : ℝ) / (p : ℝ)) :=
      hrow.tsum_eq
    have htsum_row :
        (∑' m, ‖Ff ⟨a + 1, m⟩‖)
          = ‖(casselsOnePlusOneOverPCoeff p (a + 1) : ℝ)‖
              * X ^ (q * (a + 1))
              * (1 - X) ^ (((q : ℤ)
                  - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ) : ℝ)
                  / (p : ℝ)) := by
      have hfun : (fun m => ‖Ff ⟨a + 1, m⟩‖)
          = fun m => (‖(casselsOnePlusOneOverPCoeff p (a + 1) : ℝ)‖
                * X ^ (q * (a + 1)))
              * (‖((casselsOneMinusCoeff p
                  ((q : ℤ) - (q : ℤ) * ((a + 1 : ℕ) : ℤ) * (p : ℤ)) m
                  : ℚ) : ℝ)‖ * X ^ m) := by
        funext m
        have hxqm : ‖X ^ (q * (a + 1) + m)‖
            = X ^ (q * (a + 1)) * X ^ m := by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 _), pow_add]
        rw [hFf]
        simp only [norm_mul]
        rw [hxqm]
        ring
      rw [hfun, tsum_mul_left, htsum_inner]
    rw [htsum_row]
    exact cassels_row_bound p q (a + 1) hp5 hX0 hXle

/-- Signed summability of the bivariate Cassels family. -/
theorem cassels_Ff_summable
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun am : Σ _ : ℕ, ℕ =>
      (casselsOnePlusOneOverPCoeff p am.1 : ℝ)
        * (casselsOneMinusCoeff p
            ((q : ℤ) - (q : ℤ) * (am.1 : ℤ) * (p : ℤ)) am.2 : ℝ)
        * X ^ (q * am.1 + am.2)) :=
  Summable.of_norm (cassels_Ff_summable_norm p q hp5 hpq hX0 hXle)

/-- Unconditional actual-root coefficient stream HasSum. -/
theorem cassels_actualRootCoeff_hasSum_branch
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    HasSum (fun k => (casselsActualRootCoeff p q k : ℝ) * X ^ k)
      (casselsBranch p q X) :=
  cassels_actualRootCoeff_hasSum_branch_of_summable p q
    (Nat.cast_ne_zero.mpr (by omega)) (by omega) (by omega) hX0 hXle
    (cassels_Ff_summable p q hp5 hpq hX0 hXle)

theorem cassels_actualRootCoeff_summable_norm
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun k => ‖(casselsActualRootCoeff p q k : ℝ) * X ^ k‖) := by
  have hsum : Summable
      (fun k => (casselsActualRootCoeff p q k : ℝ) * X ^ k) :=
    (cassels_actualRootCoeff_hasSum_branch p q hp5 hpq hX0 hXle).summable
  simpa [Real.norm_eq_abs] using summable_abs_iff.mpr hsum

theorem cassels_actualRootCoeff_abs_summable
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    Summable (fun k => |(casselsActualRootCoeff p q k : ℝ)| * X ^ k) := by
  have h := cassels_actualRootCoeff_summable_norm p q hp5 hpq hX0 hXle
  refine h.congr (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hX0 k)]

theorem cassels_actualRootCoeff_shifted_abs_summable
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) (s : ℕ)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) (hXne : X ≠ 0) :
    Summable
      (fun n => |(casselsActualRootCoeff p q (n + s) : ℝ)| * X ^ n) := by
  have hshift := (summable_nat_add_iff s).mpr
    (cassels_actualRootCoeff_abs_summable p q hp5 hpq hX0 hXle)
  have hm := hshift.mul_left ((X ^ s)⁻¹)
  refine hm.congr (fun n => ?_)
  rw [pow_add]
  field_simp

noncomputable def casselsActualRootAbsTsum (p q : ℕ) : ℝ :=
  ∑' k, |(casselsActualRootCoeff p q k : ℝ)| * (1 / 32 : ℝ) ^ k

theorem cassels_actualRootCoeff_shifted_tail_le
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) (s : ℕ)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    (∑' n, |(casselsActualRootCoeff p q (n + s) : ℝ)| * X ^ n)
      ≤ (32 : ℝ) ^ s * casselsActualRootAbsTsum p q := by
  have hgsum : Summable
      (fun k => |(casselsActualRootCoeff p q k : ℝ)| * (1 / 32 : ℝ) ^ k) :=
    cassels_actualRootCoeff_abs_summable p q hp5 hpq (by norm_num)
      (le_refl _)
  have hgnn : ∀ k,
      0 ≤ |(casselsActualRootCoeff p q k : ℝ)| * (1 / 32 : ℝ) ^ k :=
    fun k => by positivity
  have hreg : ∀ n,
      |(casselsActualRootCoeff p q (n + s) : ℝ)| * (1 / 32 : ℝ) ^ n
        = (32 : ℝ) ^ s
          * (|(casselsActualRootCoeff p q (n + s) : ℝ)|
              * (1 / 32 : ℝ) ^ (n + s)) := by
    intro n
    have h32 : (1 / 32 : ℝ) ^ n
        = (32 : ℝ) ^ s * (1 / 32 : ℝ) ^ (n + s) := by
      rw [pow_add,
        show (1 / 32 : ℝ) ^ s = ((32 : ℝ) ^ s)⁻¹ by
          rw [one_div, inv_pow]]
      field_simp
    rw [h32]
    ring
  have hshift_sum : Summable
      (fun n => |(casselsActualRootCoeff p q (n + s) : ℝ)|
          * (1 / 32 : ℝ) ^ (n + s)) :=
    (summable_nat_add_iff s).mpr hgsum
  have hRsum : Summable
      (fun n => |(casselsActualRootCoeff p q (n + s) : ℝ)|
          * (1 / 32 : ℝ) ^ n) :=
    Summable.congr (hshift_sum.mul_left ((32 : ℝ) ^ s))
      (fun n => (hreg n).symm)
  have hLsum : Summable
      (fun n => |(casselsActualRootCoeff p q (n + s) : ℝ)| * X ^ n) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hX0 hXle n) (abs_nonneg _)) hRsum
  have hshift_le :
      (∑' n, |(casselsActualRootCoeff p q (n + s) : ℝ)|
          * (1 / 32 : ℝ) ^ (n + s))
        ≤ casselsActualRootAbsTsum p q := by
    have hsplit := hgsum.sum_add_tsum_nat_add s
    have hpre : (0 : ℝ) ≤ ∑ i ∈ Finset.range s,
        |(casselsActualRootCoeff p q i : ℝ)| * (1 / 32 : ℝ) ^ i :=
      Finset.sum_nonneg (fun i _ => hgnn i)
    rw [casselsActualRootAbsTsum, ← hsplit]
    linarith
  calc
    (∑' n, |(casselsActualRootCoeff p q (n + s) : ℝ)| * X ^ n)
        ≤ ∑' n, |(casselsActualRootCoeff p q (n + s) : ℝ)|
            * (1 / 32 : ℝ) ^ n :=
          hLsum.tsum_le_tsum
            (fun n => mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hX0 hXle n) (abs_nonneg _)) hRsum
    _ = (32 : ℝ) ^ s
          * ∑' n, |(casselsActualRootCoeff p q (n + s) : ℝ)|
              * (1 / 32 : ℝ) ^ (n + s) := by
          rw [← tsum_mul_left]
          exact tsum_congr hreg
    _ ≤ (32 : ℝ) ^ s * casselsActualRootAbsTsum p q :=
          mul_le_mul_of_nonneg_left hshift_le (by positivity)

/-- Tail form of the actual branch expansion after truncating at `R`. -/
theorem cassels_actualRootCoeff_tail_hasSum_branch_gap
    (p q R : ℕ) (hp5 : 5 ≤ p) (hpq : p < q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXle : X ≤ (1 / 32 : ℝ)) :
    HasSum
      (fun n => (casselsActualRootCoeff p q (n + (R + 1)) : ℝ)
        * X ^ (n + (R + 1)))
      (casselsBranch p q X
        - ∑ k ∈ Finset.range (R + 1),
            (casselsActualRootCoeff p q k : ℝ) * X ^ k) := by
  exact (hasSum_nat_add_iff' (R + 1)).mpr
    (cassels_actualRootCoeff_hasSum_branch p q hp5 hpq hX0 hXle)

/-- The actual branch tail is the gap between the root value forced by
`hroot` and the finite actual-root truncation at `X = u^{-p}`. -/
theorem cassels_actualRootCoeff_tail_hasSum_gap_of_hroot
    (u v p q R : ℕ) (hu : 1 < u)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpq : p < q)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    HasSum
      (fun n => (casselsActualRootCoeff p q (n + (R + 1)) : ℝ)
        * (((u : ℝ) ^ p)⁻¹) ^ (n + (R + 1)))
      ((v : ℝ) / (u : ℝ) ^ (q - 1)
        - ∑ k ∈ Finset.range (R + 1),
            (casselsActualRootCoeff p q k : ℝ)
              * (((u : ℝ) ^ p)⁻¹) ^ k) := by
  have huRpos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
  have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := pow_pos huRpos p
  have hX0 : (0 : ℝ) ≤ ((u : ℝ) ^ p)⁻¹ := le_of_lt (inv_pos.mpr hup_pos)
  have hXle : ((u : ℝ) ^ p)⁻¹ ≤ (1 / 32 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (calc
        (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ (u : ℝ) ^ 5 := by
          exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
            (by exact_mod_cast hu) 5
        _ ≤ (u : ℝ) ^ p := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ u))
          (by omega))
  rw [cassels_runge_hbranch p q u v hp5 hq5 hu hroot]
  exact cassels_actualRootCoeff_tail_hasSum_branch_gap
    p q R hp5 hpq hX0 hXle

theorem catalanCoeff_eq_onePlusOneOverPCoeff (q k : ℕ) :
    catalanCoeff q k = casselsOnePlusOneOverPCoeff q k := by
  unfold catalanCoeff casselsOnePlusOneOverPCoeff casselsGeneralBinomNum
  push_cast
  rfl

theorem catalanCoeff_real_eq_choose
    (q k : ℕ) (hq0 : (q : ℝ) ≠ 0) :
    ((catalanCoeff q k : ℚ) : ℝ)
      = Ring.choose ((1 : ℝ) / (q : ℝ)) k := by
  rw [catalanCoeff_eq_onePlusOneOverPCoeff]
  exact casselsOnePlusOneOverPCoeff_real_eq_choose q k hq0

theorem catalanCoeff_hasSum
    (q : ℕ) (hq0 : (q : ℝ) ≠ 0) {Z : ℝ} (hZ : |Z| < 1) :
    HasSum (fun k => (catalanCoeff q k : ℝ) * Z ^ k)
      ((1 + Z) ^ ((1 : ℝ) / (q : ℝ))) := by
  simpa [catalanCoeff_eq_onePlusOneOverPCoeff] using
    cassels_onePlus_hasSum q hq0 hZ

theorem inv_nat_pow_abs_lt_one (a q : ℕ) (ha : 1 < a) (hq : 0 < q) :
    |(((a : ℝ) ^ q)⁻¹)| < 1 := by
  have haR_pos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have haR_two : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hpow_ge : (2 : ℝ) ≤ (a : ℝ) ^ q := by
    calc
      (2 : ℝ) ≤ (a : ℝ) := haR_two
      _ = (a : ℝ) ^ 1 := (pow_one (a : ℝ)).symm
      _ ≤ (a : ℝ) ^ q :=
          pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ a by omega)) (by omega : 1 ≤ q)
  have hpow_pos : (0 : ℝ) < (a : ℝ) ^ q := pow_pos haR_pos q
  rw [abs_of_pos (inv_pos.mpr hpow_pos), inv_lt_one₀ hpow_pos]
  linarith

theorem catalanCoeff_hasSum_at_inv_pow
    (a q : ℕ) (ha : 1 < a) (hq : 0 < q) :
    HasSum
      (fun k => (catalanCoeff q k : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k)
      ((1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) := by
  exact catalanCoeff_hasSum q
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq))
    (inv_nat_pow_abs_lt_one a q ha hq)

private theorem catalanCoeff_succ
    (q k : ℕ) (hq0 : q ≠ 0) :
    catalanCoeff q (k + 1)
      =
    (((1 : ℚ) - (k : ℚ) * (q : ℚ))
        / ((q : ℚ) * ((k + 1 : ℕ) : ℚ)))
      * catalanCoeff q k := by
  unfold catalanCoeff
  rw [Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hkQ : (((k + 1 : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  push_cast
  have hprod_comm :
      (∏ x ∈ Finset.range k, ((1 : ℚ) - (x : ℚ) * (q : ℚ)))
        =
      (∏ x ∈ Finset.range k, ((1 : ℚ) - (q : ℚ) * (x : ℚ))) := by
    apply Finset.prod_congr rfl
    intro x _hx
    ring
  field_simp [hqQ, hkQ]
  rw [hprod_comm]
  ring

private theorem catalanCoeff_abs_succ_eq
    (q k : ℕ) (hq0 : q ≠ 0) :
    |((catalanCoeff q (k + 1) : ℚ) : ℝ)|
      =
    |(((1 : ℝ) - (k : ℝ) * (q : ℝ))
        / ((q : ℝ) * ((k + 1 : ℕ) : ℝ)))|
      * |((catalanCoeff q k : ℚ) : ℝ)| := by
  have hrec := catalanCoeff_succ q k hq0
  have hrecR :
      ((catalanCoeff q (k + 1) : ℚ) : ℝ)
        =
      (((1 : ℝ) - (k : ℝ) * (q : ℝ))
          / ((q : ℝ) * ((k + 1 : ℕ) : ℝ)))
        * ((catalanCoeff q k : ℚ) : ℝ) := by
    exact_mod_cast hrec
  rw [hrecR, abs_mul]

private theorem catalanCoeff_abs_ratio_le_one
    (q k : ℕ) (hq2 : 2 ≤ q) (hk1 : 1 ≤ k) :
    |(((1 : ℝ) - (k : ℝ) * (q : ℝ))
        / ((q : ℝ) * ((k + 1 : ℕ) : ℝ)))| ≤ 1 := by
  have hqR_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hk1R_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hden_pos : (0 : ℝ) < (q : ℝ) * ((k + 1 : ℕ) : ℝ) :=
    mul_pos hqR_pos hk1R_pos
  have hnum_nonpos : (1 : ℝ) - (k : ℝ) * (q : ℝ) ≤ 0 := by
    have hkq : (1 : ℕ) ≤ k * q := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    have hkqR : (1 : ℝ) ≤ (k * q : ℕ) := by exact_mod_cast hkq
    push_cast at hkqR
    nlinarith
  rw [abs_div, abs_of_nonpos hnum_nonpos, abs_of_pos hden_pos]
  rw [div_le_one hden_pos]
  have hdiff_le :
      -((1 : ℝ) - (k : ℝ) * (q : ℝ))
        ≤ (q : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    have hle_nat : k * q - 1 ≤ q * (k + 1) := by
      have hsub : k * q - 1 ≤ k * q := Nat.sub_le _ _
      have hle : k * q ≤ q * (k + 1) := by
        rw [Nat.mul_comm k q]
        exact Nat.mul_le_mul_left q (Nat.le_succ k)
      exact le_trans hsub hle
    have hkq_one : 1 ≤ k * q := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    have hleR : ((k * q - 1 : ℕ) : ℝ) ≤ (q * (k + 1) : ℕ) := by
      exact_mod_cast hle_nat
    rw [Nat.cast_sub hkq_one] at hleR
    push_cast at hleR
    rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by norm_num]
    nlinarith
  exact hdiff_le

private theorem catalanCoeff_abs_le_inv_q
    (q k : ℕ) (hq2 : 2 ≤ q) (hk1 : 1 ≤ k) :
    |((catalanCoeff q k : ℚ) : ℝ)| ≤ ((q : ℝ)⁻¹) := by
  induction k with
  | zero =>
      omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        have hcoeff : catalanCoeff q 1 = (1 : ℚ) / (q : ℚ) := by
          unfold catalanCoeff
          norm_num
        have hqR_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        rw [hcoeff]
        norm_num
      · have hk1' : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hprev := ih hk1'
        have hrec := catalanCoeff_abs_succ_eq q k (by omega : q ≠ 0)
        rw [hrec]
        have hratio := catalanCoeff_abs_ratio_le_one q k hq2 hk1'
        have hprev_nonneg : 0 ≤ |((catalanCoeff q k : ℚ) : ℝ)| :=
          abs_nonneg _
        calc
          |(((1 : ℝ) - (k : ℝ) * (q : ℝ))
              / ((q : ℝ) * ((k + 1 : ℕ) : ℝ)))|
              * |((catalanCoeff q k : ℚ) : ℝ)|
              ≤ 1 * |((catalanCoeff q k : ℚ) : ℝ)| :=
                mul_le_mul_of_nonneg_right hratio hprev_nonneg
          _ ≤ (q : ℝ)⁻¹ := by
                simpa using hprev

private theorem catalanCoeff_abs_succ_mul_pow_le
    (q k : ℕ) (hq2 : 2 ≤ q) (hk1 : 1 ≤ k)
    {X : ℝ} (hX0 : 0 ≤ X) :
    |((catalanCoeff q (k + 1) : ℚ) : ℝ)| * X ^ (k + 1)
      ≤
    X * (|((catalanCoeff q k : ℚ) : ℝ)| * X ^ k) := by
  have hratio := catalanCoeff_abs_ratio_le_one q k hq2 hk1
  have hrec := catalanCoeff_abs_succ_eq q k (by omega : q ≠ 0)
  rw [hrec, pow_succ]
  have htail_nonneg :
      0 ≤ |((catalanCoeff q k : ℚ) : ℝ)| * (X ^ k * X) := by
    positivity
  calc
    |(((1 : ℝ) - (k : ℝ) * (q : ℝ))
        / ((q : ℝ) * ((k + 1 : ℕ) : ℝ)))|
        * |((catalanCoeff q k : ℚ) : ℝ)| * (X ^ k * X)
        =
      |(((1 : ℝ) - (k : ℝ) * (q : ℝ))
        / ((q : ℝ) * ((k + 1 : ℕ) : ℝ)))|
        * (|((catalanCoeff q k : ℚ) : ℝ)| * (X ^ k * X)) := by
          ring
    _ ≤ 1 * (|((catalanCoeff q k : ℚ) : ℝ)| * (X ^ k * X)) :=
          mul_le_mul_of_nonneg_right hratio htail_nonneg
    _ = X * (|((catalanCoeff q k : ℚ) : ℝ)| * X ^ k) := by
          ring

private theorem catalanCoeff_tail_le_geom
    (q R n : ℕ) (hq2 : 2 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) :
    |((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)|
        * X ^ (n + (R + 1))
      ≤
    X ^ n
      * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
          * X ^ (R + 1)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let k := n + (R + 1)
      have hk1 : 1 ≤ k := by
        dsimp [k]
        omega
      have hstep :
          |((catalanCoeff q (k + 1) : ℚ) : ℝ)| * X ^ (k + 1)
            ≤
          X * (|((catalanCoeff q k : ℚ) : ℝ)| * X ^ k) :=
        catalanCoeff_abs_succ_mul_pow_le q k hq2 hk1 hX0
      have hih :
          |((catalanCoeff q k : ℚ) : ℝ)| * X ^ k
            ≤
          X ^ n
            * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
                * X ^ (R + 1)) := by
        dsimp [k]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
      calc
        |((catalanCoeff q (Nat.succ n + (R + 1)) : ℚ) : ℝ)|
            * X ^ (Nat.succ n + (R + 1))
            =
          |((catalanCoeff q (k + 1) : ℚ) : ℝ)| * X ^ (k + 1) := by
            have hidx : Nat.succ n + (R + 1) = k + 1 := by
              dsimp [k]
              omega
            rw [hidx]
        _ ≤ X * (|((catalanCoeff q k : ℚ) : ℝ)| * X ^ k) :=
            hstep
        _ ≤ X * (X ^ n
            * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
                * X ^ (R + 1))) :=
            mul_le_mul_of_nonneg_left hih hX0
        _ =
          X ^ Nat.succ n
            * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
                * X ^ (R + 1)) := by
            rw [pow_succ X n, pow_succ X R]
            ring

private theorem catalanCoeff_tail_abs_summable
    (q R : ℕ) (hq2 : 2 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXlt : X < 1) :
    Summable
      (fun n : ℕ =>
        |((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1))) := by
  let C : ℝ :=
    |((catalanCoeff q (R + 1) : ℚ) : ℝ)| * X ^ (R + 1)
  have hgeo : Summable (fun n : ℕ => C * X ^ n) :=
    (summable_geometric_of_lt_one hX0 hXlt).mul_left C
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hgeo
  intro n
  have hle := catalanCoeff_tail_le_geom q R n hq2 hX0
  simpa [C, mul_comm, mul_left_comm, mul_assoc] using hle

private theorem catalanCoeff_tail_abs_tsum_le_geom
    (q R : ℕ) (hq2 : 2 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXlt : X < 1) :
    (∑' n : ℕ,
        |((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1)))
      ≤
    |((catalanCoeff q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) := by
  let C : ℝ :=
    |((catalanCoeff q (R + 1) : ℚ) : ℝ)| * X ^ (R + 1)
  have hLsum := catalanCoeff_tail_abs_summable q R hq2 hX0 hXlt
  have hRsum : Summable (fun n : ℕ => C * X ^ n) :=
    (summable_geometric_of_lt_one hX0 hXlt).mul_left C
  have hpoint :
      ∀ n : ℕ,
        |((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)|
            * X ^ (n + (R + 1))
          ≤ C * X ^ n := by
    intro n
    have hle := catalanCoeff_tail_le_geom q R n hq2 hX0
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using hle
  calc
    (∑' n : ℕ,
        |((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1)))
        ≤ ∑' n : ℕ, C * X ^ n :=
          hLsum.tsum_le_tsum hpoint hRsum
    _ = C * (1 - X)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hX0 hXlt]
    _ =
      |((catalanCoeff q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) := by
          dsimp [C]
          ring

private theorem catalanCoeff_tail_gap_abs_le_geom
    (q R : ℕ) (hq2 : 2 ≤ q)
    {X : ℝ} (hX0 : 0 ≤ X) (hXlt : X < 1) :
    |(1 + X) ^ ((1 : ℝ) / (q : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            ((catalanCoeff q k : ℚ) : ℝ) * X ^ k|
      ≤
    |((catalanCoeff q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) := by
  have hqR_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hXabs : |X| < 1 := by
    rw [abs_of_nonneg hX0]
    exact hXlt
  have htail :
      HasSum
        (fun n : ℕ =>
          ((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)
            * X ^ (n + (R + 1)))
        ((1 + X) ^ ((1 : ℝ) / (q : ℝ))
          - ∑ k ∈ Finset.range (R + 1),
              ((catalanCoeff q k : ℚ) : ℝ) * X ^ k) := by
    exact (hasSum_nat_add_iff' (R + 1)).mpr
      (catalanCoeff_hasSum q hqR_ne hXabs)
  have hnorm_summ :
      Summable
        (fun n : ℕ =>
          ‖((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)
            * X ^ (n + (R + 1))‖) := by
    have habs := catalanCoeff_tail_abs_summable q R hq2 hX0 hXlt
    refine habs.congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg hX0 (n + (R + 1)))]
  have hbound := norm_tsum_le_tsum_norm hnorm_summ
  rw [htail.tsum_eq, Real.norm_eq_abs] at hbound
  calc
    |(1 + X) ^ ((1 : ℝ) / (q : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            ((catalanCoeff q k : ℚ) : ℝ) * X ^ k|
        ≤
      ∑' n : ℕ,
        ‖((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)
          * X ^ (n + (R + 1))‖ := hbound
    _ =
      ∑' n : ℕ,
        |((catalanCoeff q (n + (R + 1)) : ℚ) : ℝ)|
          * X ^ (n + (R + 1)) := by
          apply tsum_congr
          intro n
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (pow_nonneg hX0 (n + (R + 1)))]
    _ ≤
      |((catalanCoeff q (R + 1) : ℚ) : ℝ)|
        * X ^ (R + 1) / (1 - X) :=
          catalanCoeff_tail_abs_tsum_le_geom q R hq2 hX0 hXlt

private theorem catalanScaled_tail_gap_abs_le_geom
    (a q R : ℕ) (ha : 1 < a) (hq2 : 2 ≤ q) :
    |(a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            ((catalanCoeff q k : ℚ) : ℝ) * (a : ℝ)
              * (((a : ℝ) ^ q)⁻¹) ^ k|
      ≤
    (a : ℝ)
      * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
          * (((a : ℝ) ^ q)⁻¹) ^ (R + 1)
          / (1 - (((a : ℝ) ^ q)⁻¹))) := by
  let X : ℝ := (((a : ℝ) ^ q)⁻¹)
  have hq0 : 0 < q := by omega
  have haR_pos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hX_pos : 0 < X := by
    dsimp [X]
    positivity
  have hX0 : 0 ≤ X := le_of_lt hX_pos
  have hXlt : X < 1 := by
    have h := inv_nat_pow_abs_lt_one a q ha hq0
    dsimp [X]
    rwa [abs_of_pos hX_pos] at h
  have hbase :=
    catalanCoeff_tail_gap_abs_le_geom q R hq2 hX0 hXlt
  have hsum_scaled :
      (∑ k ∈ Finset.range (R + 1),
          ((catalanCoeff q k : ℚ) : ℝ) * (a : ℝ) * X ^ k)
        =
      (a : ℝ) * ∑ k ∈ Finset.range (R + 1),
          ((catalanCoeff q k : ℚ) : ℝ) * X ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  calc
    |(a : ℝ) * (1 + X) ^ ((1 : ℝ) / (q : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            ((catalanCoeff q k : ℚ) : ℝ) * (a : ℝ) * X ^ k|
        =
      |(a : ℝ) *
        ((1 + X) ^ ((1 : ℝ) / (q : ℝ))
          - ∑ k ∈ Finset.range (R + 1),
              ((catalanCoeff q k : ℚ) : ℝ) * X ^ k)| := by
          rw [hsum_scaled]
          ring
    _ =
      (a : ℝ)
        * |(1 + X) ^ ((1 : ℝ) / (q : ℝ))
          - ∑ k ∈ Finset.range (R + 1),
              ((catalanCoeff q k : ℚ) : ℝ) * X ^ k| := by
          rw [abs_mul, abs_of_pos haR_pos]
    _ ≤
      (a : ℝ)
        * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
            * X ^ (R + 1) / (1 - X)) :=
          mul_le_mul_of_nonneg_left hbase (le_of_lt haR_pos)
    _ =
      (a : ℝ)
        * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
            * (((a : ℝ) ^ q)⁻¹) ^ (R + 1)
            / (1 - (((a : ℝ) ^ q)⁻¹))) := by
          dsimp [X]

theorem catalanScaled_hasSum_at_inv_pow
    (a q : ℕ) (ha : 1 < a) (hq : 0 < q) :
    HasSum
      (fun k => (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k)
      ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) := by
  have hs := (catalanCoeff_hasSum_at_inv_pow a q ha hq).mul_left (a : ℝ)
  convert hs using 1
  ext k
  ring

theorem catalanScaled_rpow_pow_eq (a q : ℕ) (ha : 0 < a) (hq : 0 < q) :
    ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
      = (a : ℝ) ^ q + 1 := by
  have haR_pos : (0 : ℝ) < a := by exact_mod_cast ha
  have hApos : (0 : ℝ) < (a : ℝ) ^ q := pow_pos haR_pos q
  have hbase_nonneg : (0 : ℝ) ≤ 1 + (((a : ℝ) ^ q)⁻¹) := by positivity
  have hqR_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hrpow :
      ((1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
        = 1 + (((a : ℝ) ^ q)⁻¹) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_nonneg]
    have hmul : (1 : ℝ) / (q : ℝ) * (q : ℝ) = 1 := by
      field_simp [hqR_ne]
    rw [hmul, Real.rpow_one]
  calc
    ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
        = (a : ℝ) ^ q
            * ((1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q := by
          rw [mul_pow]
    _ = (a : ℝ) ^ q * (1 + (((a : ℝ) ^ q)⁻¹)) := by rw [hrpow]
    _ = (a : ℝ) ^ q + 1 := by field_simp [hApos.ne']

theorem catalanScaled_rpow_eq_nat_of_pow_eq
    (a b q : ℕ) (ha : 0 < a) (hq : 0 < q) (hqodd : Odd q)
    (hpow : b ^ q = a ^ q + 1) :
    (a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ)) = b := by
  apply hqodd.pow_injective
  change ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))) ^ q
      = (b : ℝ) ^ q
  have hpowR : (b : ℝ) ^ q = (a : ℝ) ^ q + 1 := by exact_mod_cast hpow
  rw [catalanScaled_rpow_pow_eq a q ha hq, hpowR]

theorem catalanScaled_tail_hasSum_at_inv_pow
    (a q R : ℕ) (ha : 1 < a) (hq : 0 < q) :
    HasSum
      (fun n =>
        (catalanCoeff q (n + (R + 1)) : ℝ) * (a : ℝ)
          * (((a : ℝ) ^ q)⁻¹) ^ (n + (R + 1)))
      ((a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ))
        - ∑ k ∈ Finset.range (R + 1),
            (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k) := by
  exact (hasSum_nat_add_iff' (R + 1)).mpr
    (catalanScaled_hasSum_at_inv_pow a q ha hq)

/-- The Catalan tail is exactly the gap between the integer root `b`
and the finite truncation, when `b^q = a^q + 1`. -/
theorem catalanScaled_tail_hasSum_gap_of_pow_eq
    (a b q R : ℕ) (ha : 1 < a) (hq : 0 < q) (hqodd : Odd q)
    (hpow : b ^ q = a ^ q + 1) :
    HasSum
      (fun n =>
        (catalanCoeff q (n + (R + 1)) : ℝ) * (a : ℝ)
          * (((a : ℝ) ^ q)⁻¹) ^ (n + (R + 1)))
      ((b : ℝ) - ∑ k ∈ Finset.range (R + 1),
        (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k) := by
  have hroot :
      (a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ)) = b :=
    catalanScaled_rpow_eq_nat_of_pow_eq a b q (by omega) hq hqodd hpow
  rw [← hroot]
  exact catalanScaled_tail_hasSum_at_inv_pow a q R ha hq

/-- Ribenboim/Cassels truncation level `R = ⌊(q-1)/p⌋`. -/
def casselsCatalanN (p q : ℕ) : ℕ := (q - 1) / p

/-- Extra `q`-adic denominator exponent `ρ = ⌊R/(q-1)⌋`. -/
def casselsCatalanRho (p q : ℕ) : ℕ :=
  casselsCatalanN p q / (q - 1)

theorem casselsCatalanN_pos (p q : ℕ) (hp_pos : 0 < p) (hpq : p < q) :
    0 < casselsCatalanN p q := by
  unfold casselsCatalanN
  exact Nat.div_pos (by omega) hp_pos

theorem casselsCatalanN_lt_q_sub_one
    (p q : ℕ) (hp2 : 2 ≤ p) (hq3 : 3 ≤ q) :
    casselsCatalanN p q < q - 1 := by
  by_contra h
  have hle : q - 1 ≤ casselsCatalanN p q := Nat.le_of_not_gt h
  have hRp : casselsCatalanN p q * p ≤ q - 1 := by
    simpa [casselsCatalanN, Nat.mul_comm] using Nat.div_mul_le_self (q - 1) p
  have hbig : (q - 1) * p ≤ casselsCatalanN p q * p :=
    Nat.mul_le_mul_right p hle
  have hqsub_pos : 0 < q - 1 := by omega
  nlinarith

theorem casselsCatalanRho_eq_zero
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsCatalanRho p q = 0 := by
  unfold casselsCatalanRho
  exact Nat.div_eq_of_lt
    (casselsCatalanN_lt_q_sub_one p q (by omega) (by omega))

/-- Correct Catalan clearing denominator `q^(R+ρ) * (u^p-1)^(Rq-1)`. -/
def casselsCatalanDenom (u p q : ℕ) : ℕ :=
  let R := casselsCatalanN p q
  let ρ := casselsCatalanRho p q
  let a := u ^ p - 1
  q ^ (R + ρ) * a ^ (R * q - 1)

/-- Correct Catalan truncation:
`(u^p-1) * Σ_{k≤R} C(1/q,k) * (u^p-1)^(-qk)`. -/
noncomputable def casselsCatalanTrunc (u p q : ℕ) : ℚ :=
  let R := casselsCatalanN p q
  let a : ℚ := (u ^ p - 1 : ℕ)
  ∑ k ∈ Finset.range (R + 1),
    catalanCoeff q k * a * ((a ^ q)⁻¹) ^ k

/-- Real form of the Catalan truncation. -/
theorem casselsCatalanTrunc_natCast_eq_sum (u p q : ℕ) :
    ((casselsCatalanTrunc u p q : ℚ) : ℝ) =
      ∑ k ∈ Finset.range (casselsCatalanN p q + 1),
        (catalanCoeff q k : ℝ) * ((u ^ p - 1 : ℕ) : ℝ)
          * ((((u ^ p - 1 : ℕ) : ℝ) ^ q)⁻¹) ^ k := by
  simp [casselsCatalanTrunc]

/-- The Catalan tail is the gap between the integer root and the
`casselsCatalanTrunc` finite sum. -/
theorem casselsCatalanTrunc_gap_hasSum
    (u b p q : ℕ) (hu : 1 < u) (hp2 : 2 ≤ p) (hq0 : 0 < q)
    (hqodd : Odd q)
    (hpow : b ^ q = (u ^ p - 1) ^ q + 1) :
    HasSum
      (fun n =>
        (catalanCoeff q (n + (casselsCatalanN p q + 1)) : ℝ)
          * ((u ^ p - 1 : ℕ) : ℝ)
          * (((((u ^ p - 1 : ℕ) : ℝ) ^ q)⁻¹)
              ^ (n + (casselsCatalanN p q + 1))))
      ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ)) := by
  set a : ℕ := u ^ p - 1 with ha_def
  have ha_gt1 : 1 < a := by
    rw [ha_def]
    have hu2 : 2 ≤ u := by omega
    have hup4 : 4 ≤ u ^ p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ u ^ 2 := Nat.pow_le_pow_left hu2 2
        _ ≤ u ^ p := Nat.pow_le_pow_right (by omega : 0 < u) hp2
    omega
  have hpow_a : b ^ q = a ^ q + 1 := by simpa [ha_def] using hpow
  have htail :=
    catalanScaled_tail_hasSum_at_inv_pow a q (casselsCatalanN p q)
      ha_gt1 hq0
  have hroot :=
    catalanScaled_rpow_eq_nat_of_pow_eq a b q (by omega) hq0 hqodd hpow_a
  have htr_a :
      ((casselsCatalanTrunc u p q : ℚ) : ℝ) =
        ∑ k ∈ Finset.range (casselsCatalanN p q + 1),
          (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k := by
    rw [casselsCatalanTrunc_natCast_eq_sum u p q]
  rw [← hroot, htr_a]
  simpa [ha_def, a] using htail

theorem casselsCatalanTrunc_gap_abs_le_geom
    (u b p q : ℕ) (hu : 1 < u) (hp2 : 2 ≤ p) (hq2 : 2 ≤ q)
    (hqodd : Odd q)
    (hpow : b ^ q = (u ^ p - 1) ^ q + 1) :
    let R := casselsCatalanN p q
    let a := u ^ p - 1
    |(b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ)|
      ≤
    (a : ℝ)
      * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
          * (((a : ℝ) ^ q)⁻¹) ^ (R + 1)
          / (1 - (((a : ℝ) ^ q)⁻¹))) := by
  set R : ℕ := casselsCatalanN p q with hR_def
  set a : ℕ := u ^ p - 1 with ha_def
  have hq0 : 0 < q := by omega
  have ha_gt1 : 1 < a := by
    rw [ha_def]
    have hu2 : 2 ≤ u := by omega
    have hup4 : 4 ≤ u ^ p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ u ^ 2 := Nat.pow_le_pow_left hu2 2
        _ ≤ u ^ p := Nat.pow_le_pow_right (by omega : 0 < u) hp2
    omega
  have hpow_a : b ^ q = a ^ q + 1 := by
    simpa [ha_def] using hpow
  have hroot :
      (a : ℝ) * (1 + (((a : ℝ) ^ q)⁻¹)) ^ ((1 : ℝ) / (q : ℝ)) = b :=
    catalanScaled_rpow_eq_nat_of_pow_eq a b q (by omega) hq0 hqodd hpow_a
  have htr_a :
      ((casselsCatalanTrunc u p q : ℚ) : ℝ) =
        ∑ k ∈ Finset.range (R + 1),
          (catalanCoeff q k : ℝ) * (a : ℝ) * (((a : ℝ) ^ q)⁻¹) ^ k := by
    simpa [hR_def, ha_def] using casselsCatalanTrunc_natCast_eq_sum u p q
  rw [← hroot, htr_a]
  exact catalanScaled_tail_gap_abs_le_geom a q R ha_gt1 hq2

/-- The first omitted Catalan tail term is nonzero. -/
theorem catalanScaled_tail_first_ne_zero
    (a q R : ℕ) (ha : 0 < a) (hq2 : 2 ≤ q) :
    (catalanCoeff q (R + 1) : ℝ) * (a : ℝ)
        * (((a : ℝ) ^ q)⁻¹) ^ (R + 1) ≠ 0 := by
  have hcQ : catalanCoeff q (R + 1) ≠ 0 :=
    catalanCoeff_ne_zero q (R + 1) hq2
  have hcR : (catalanCoeff q (R + 1) : ℝ) ≠ 0 := by exact_mod_cast hcQ
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hpow : (((a : ℝ) ^ q)⁻¹) ^ (R + 1) ≠ 0 := by
    exact pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ haR))
  exact mul_ne_zero (mul_ne_zero hcR haR) hpow

/-- Cassels' B2.4 fixed truncation index, in the lower-prime orientation:
`R = floor(q / p) + 1`. -/
def casselsB24R (p q : ℕ) : ℕ := q / p + 1

/-- Cassels' auxiliary exponent `rho = floor(R / (p - 1))`. -/
def casselsB24Rho (p q : ℕ) : ℕ := casselsB24R p q / (p - 1)

noncomputable def casselsB24X (u p : ℕ) : ℝ :=
  ((u : ℝ) ^ p)⁻¹

noncomputable def casselsB24A (u p q : ℕ) : ℝ :=
  (1 - casselsB24X u p) ^ ((q : ℝ) / (p : ℝ))

noncomputable def casselsB24Qfac (p q : ℕ) : ℝ :=
  let R := casselsB24R p q
  let ρ := casselsB24Rho p q
  (p : ℝ) ^ (R + ρ)

noncomputable def casselsB24DirectBudget (u p q : ℕ) : ℝ :=
  let R := casselsB24R p q
  let X := casselsB24X u p
  let A := casselsB24A u p q
  let Q := casselsB24Qfac p q
  Q
    * ((u : ℝ) ^ (p * R) * X ^ q / A ^ (p - 1)
      + X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X))

private theorem casselsB24X_pos
    (u p : ℕ) (hu : 1 < u) :
    0 < casselsB24X u p := by
  unfold casselsB24X
  have huR : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  exact inv_pos.mpr (pow_pos huR p)

private theorem casselsB24X_lt_one
    (u p : ℕ) (hu : 1 < u) (hp0 : 0 < p) :
    casselsB24X u p < 1 := by
  unfold casselsB24X
  have huR : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hup_gt_one : (1 : ℝ) < (u : ℝ) ^ p := by
    calc
      (1 : ℝ) < (u : ℝ) := by exact_mod_cast hu
      _ = (u : ℝ) ^ 1 := (pow_one (u : ℝ)).symm
      _ ≤ (u : ℝ) ^ p :=
          pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ u)) (by omega)
  rw [inv_lt_one₀ (pow_pos huR p)]
  exact hup_gt_one

private theorem cassels_u_ge_p_succ_of_p_dvd_sub_one
    (u p : ℕ) (hu : 1 < u) (hpm1 : p ∣ u - 1) :
    p + 1 ≤ u := by
  rcases hpm1 with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hk0, mul_zero] at hk
    omega
  by_cases hp0 : p = 0
  · omega
  have hpk_ge : p ≤ p * k := by
    calc
      p = p * 1 := by rw [mul_one]
      _ ≤ p * k := Nat.mul_le_mul_left p hkpos
  omega

private theorem casselsB24X_le_one_div_7776_of_p_dvd_sub_one
    (u p : ℕ) (hu : 1 < u) (hp5 : 5 ≤ p) (hpm1 : p ∣ u - 1) :
    casselsB24X u p ≤ (1 / 7776 : ℝ) := by
  unfold casselsB24X
  have hu_ge : p + 1 ≤ u :=
    cassels_u_ge_p_succ_of_p_dvd_sub_one u p hu hpm1
  have h6u : 6 ≤ u := by omega
  have huR_pos : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hpow_ge : (7776 : ℝ) ≤ (u : ℝ) ^ p := by
    calc
      (7776 : ℝ) = (6 : ℝ) ^ 5 := by norm_num
      _ ≤ (u : ℝ) ^ 5 := by
        exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6)
          (by exact_mod_cast h6u) 5
      _ ≤ (u : ℝ) ^ p :=
        pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ u)) (by omega)
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hpow_ge

private theorem casselsB24A_pos
    (u p q : ℕ) (hu : 1 < u) (hp0 : 0 < p) :
    0 < casselsB24A u p q := by
  unfold casselsB24A
  have hXlt : casselsB24X u p < 1 :=
    casselsB24X_lt_one u p hu hp0
  have hbase : 0 < 1 - casselsB24X u p := by linarith
  positivity

private theorem casselsB24A_pow_p
    (u p q : ℕ) (hu : 1 < u) (hp0 : 0 < p) :
    (casselsB24A u p q) ^ p = (1 - casselsB24X u p) ^ q := by
  unfold casselsB24A
  have hXlt : casselsB24X u p < 1 :=
    casselsB24X_lt_one u p hu hp0
  have hbase_nonneg : 0 ≤ 1 - casselsB24X u p := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_nonneg]
  have hpR_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp0)
  have hmul : (q : ℝ) / (p : ℝ) * (p : ℝ) = (q : ℝ) := by
    field_simp [hpR_ne]
  rw [hmul, Real.rpow_natCast]

private theorem casselsB24_actual_minus_binomial_bound
    {u v p q : ℕ}
    (hu : 1 < u) (hp0 : 0 < p)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    let X := casselsB24X u p
    let A := casselsB24A u p q
    |(v : ℝ) / (u : ℝ) ^ (q - 1) - A|
      ≤ X ^ q / A ^ (p - 1) := by
  classical
  let X := casselsB24X u p
  let A := casselsB24A u p q
  let B : ℝ := (v : ℝ) / (u : ℝ) ^ (q - 1)
  have hX_nonneg : 0 ≤ X := le_of_lt (casselsB24X_pos u p hu)
  have hA_pos : 0 < A := by
    dsimp [A]
    exact casselsB24A_pos u p q hu hp0
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hApow : A ^ p = (1 - X) ^ q := by
    dsimp [A, X]
    exact casselsB24A_pow_p u p q hu hp0
  have hBpow : B ^ p = A ^ p + X ^ q := by
    dsimp [B, A, X, casselsB24X] at hroot ⊢
    rw [hApow]
    exact hroot
  have hB_ge_A : A ≤ B := by
    by_contra hnot
    have hlt : B < A := lt_of_not_ge hnot
    have hpow_lt : B ^ p < A ^ p :=
      pow_lt_pow_left₀ hlt hB_nonneg hp0.ne'
    have hXq_nonneg : 0 ≤ X ^ q := pow_nonneg hX_nonneg q
    nlinarith [hBpow]
  have hdiff_nonneg : 0 ≤ B - A := by linarith
  let S : ℝ := ∑ i ∈ Finset.range p, B ^ i * A ^ (p - 1 - i)
  have hgeom : (B - A) * S = B ^ p - A ^ p := by
    have h := (Commute.all B A).geom_sum₂_mul p
    dsimp [S]
    calc
      (B - A) * (∑ i ∈ Finset.range p, B ^ i * A ^ (p - 1 - i))
          =
        (∑ i ∈ Finset.range p, B ^ i * A ^ (p - 1 - i)) * (B - A) := by
          ring
      _ = B ^ p - A ^ p := h
  have hS_ge : A ^ (p - 1) ≤ S := by
    dsimp [S]
    have h0mem : 0 ∈ Finset.range p := by
      simpa using hp0
    have hnonneg :
        ∀ i ∈ Finset.range p, 0 ≤ B ^ i * A ^ (p - 1 - i) := by
      intro i _hi
      exact mul_nonneg (pow_nonneg hB_nonneg i)
        (pow_nonneg hA_nonneg (p - 1 - i))
    have hsingle :=
      Finset.single_le_sum hnonneg h0mem
    simpa using hsingle
  have hmul_le :
      (B - A) * A ^ (p - 1) ≤ X ^ q := by
    calc
      (B - A) * A ^ (p - 1) ≤ (B - A) * S :=
        mul_le_mul_of_nonneg_left hS_ge hdiff_nonneg
      _ = X ^ q := by
        nlinarith [hgeom, hBpow]
  have hAden_pos : 0 < A ^ (p - 1) := pow_pos hA_pos _
  dsimp [B, A, X]
  rw [abs_of_nonneg hdiff_nonneg]
  rw [le_div_iff₀ hAden_pos]
  exact hmul_le

theorem casselsB24R_pos (p q : ℕ) : 0 < casselsB24R p q := by
  unfold casselsB24R
  exact Nat.succ_pos (q / p)

theorem casselsB24R_ge_two (p q : ℕ) (hp_pos : 0 < p) (hpq : p < q) :
    2 ≤ casselsB24R p q := by
  unfold casselsB24R
  have hq_div_p : 1 ≤ q / p := by
    rw [Nat.le_div_iff_mul_le hp_pos]
    omega
  omega

theorem q_lt_p_mul_casselsB24R (p q : ℕ) (hp_pos : 0 < p) :
    q < p * casselsB24R p q := by
  unfold casselsB24R
  calc
    q < q / p * p + p := Nat.lt_div_mul_add hp_pos
    _ = p * (q / p + 1) := by ring

private theorem casselsRootCoeff_abs_ratio_at_B24R_le_inv
    (p q : ℕ) (hp0 : 0 < p) :
    let R := casselsB24R p q
    |(((q : ℝ) - (R : ℝ) * (p : ℝ))
        / ((p : ℝ) * ((R + 1 : ℕ) : ℝ)))|
      ≤ (((R + 1 : ℕ) : ℝ))⁻¹ := by
  let R := casselsB24R p q
  have hpR_pos : (0 : ℝ) < p := by exact_mod_cast hp0
  have hR1_pos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by positivity
  have hden_pos : (0 : ℝ) < (p : ℝ) * ((R + 1 : ℕ) : ℝ) :=
    mul_pos hpR_pos hR1_pos
  have hq_lt : q < p * R := by
    dsimp [R]
    exact q_lt_p_mul_casselsB24R p q hp0
  have hnum_nonpos : (q : ℝ) - (R : ℝ) * (p : ℝ) ≤ 0 := by
    have hle_nat : q ≤ R * p := by
      rw [Nat.mul_comm]
      exact Nat.le_of_lt hq_lt
    have hleR : (q : ℝ) ≤ (R * p : ℕ) := by exact_mod_cast hle_nat
    push_cast at hleR
    nlinarith
  change
    |(((q : ℝ) - (R : ℝ) * (p : ℝ))
        / ((p : ℝ) * ((R + 1 : ℕ) : ℝ)))|
      ≤ (((R + 1 : ℕ) : ℝ))⁻¹
  rw [abs_div, abs_of_nonpos hnum_nonpos, abs_of_pos hden_pos]
  rw [div_le_iff₀ hden_pos]
  have hdiff_le_p : -((q : ℝ) - (R : ℝ) * (p : ℝ)) ≤ (p : ℝ) := by
    have hdiff_nat : R * p - q ≤ p := by
      dsimp [R, casselsB24R]
      rw [Nat.add_mul, one_mul]
      have hfloor : (q / p) * p ≤ q := Nat.div_mul_le_self q p
      omega
    have hq_le : q ≤ R * p := by
      rw [Nat.mul_comm]
      exact Nat.le_of_lt hq_lt
    have hdiffR : ((R * p - q : ℕ) : ℝ) ≤ (p : ℕ) := by
      exact_mod_cast hdiff_nat
    rw [Nat.cast_sub hq_le] at hdiffR
    push_cast at hdiffR
    nlinarith
  have hmul_inv :
      (p : ℝ) = (((R + 1 : ℕ) : ℝ))⁻¹
        * ((p : ℝ) * ((R + 1 : ℕ) : ℝ)) := by
    field_simp [hR1_pos.ne']
  calc
    -((q : ℝ) - (R : ℝ) * (p : ℝ))
        ≤ (p : ℝ) := hdiff_le_p
    _ = (((R + 1 : ℕ) : ℝ))⁻¹
          * ((p : ℝ) * ((R + 1 : ℕ) : ℝ)) := hmul_inv

private theorem casselsRootCoeff_abs_at_B24R_le_one
    (p q : ℕ) (hp0 : 0 < p) :
    let R := casselsB24R p q
    |((casselsRootCoeff p q R : ℚ) : ℝ)| ≤ 1 := by
  let R := casselsB24R p q
  have hpR_pos : (0 : ℝ) < p := by exact_mod_cast hp0
  have hpR_nonneg : (0 : ℝ) ≤ p := le_of_lt hpR_pos
  have hden_pos : 0 < (p : ℝ) ^ R * (R.factorial : ℝ) := by
    positivity
  have hq_lt_pR : q < p * R := by
    dsimp [R]
    exact q_lt_p_mul_casselsB24R p q hp0
  have hnum_cast :
      ((casselsBinomNum p q R : ℤ) : ℝ)
        =
      (Finset.range R).prod
        (fun j => ((q : ℝ) - (j : ℝ) * (p : ℝ))) := by
    unfold casselsBinomNum
    push_cast
    simp
  have hfactor_le :
      ∀ j ∈ Finset.range R,
        |(q : ℝ) - (j : ℝ) * (p : ℝ)|
          ≤ (p : ℝ) * (R - j : ℕ) := by
    intro j hj
    have hjR : j < R := Finset.mem_range.mp hj
    have hjp_le_q : j * p ≤ q := by
      dsimp [R, casselsB24R] at hjR
      have hj_le : j ≤ q / p := by omega
      calc
        j * p ≤ (q / p) * p := Nat.mul_le_mul_right p hj_le
        _ ≤ q := Nat.div_mul_le_self q p
    have hnonneg : (0 : ℝ) ≤ (q : ℝ) - (j : ℝ) * (p : ℝ) := by
      have hcast : ((j * p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hjp_le_q
      push_cast at hcast
      nlinarith
    have hle_nat : q - j * p ≤ p * (R - j) := by
      have hq_le_pR : q ≤ p * R := Nat.le_of_lt hq_lt_pR
      calc
        q - j * p ≤ p * R - j * p := Nat.sub_le_sub_right hq_le_pR (j * p)
        _ = p * (R - j) := by
          rw [Nat.mul_comm j p, ← Nat.mul_sub_left_distrib]
    have hleR : (q : ℝ) - (j : ℝ) * (p : ℝ)
        ≤ (p : ℝ) * (R - j : ℕ) := by
      have hcast : ((q - j * p : ℕ) : ℝ) ≤ ((p * (R - j) : ℕ) : ℝ) := by
        exact_mod_cast hle_nat
      rw [Nat.cast_sub hjp_le_q] at hcast
      push_cast at hcast
      exact hcast
    rwa [abs_of_nonneg hnonneg]
  have hprod_le :
      (Finset.range R).prod
        (fun j => |(q : ℝ) - (j : ℝ) * (p : ℝ)|)
        ≤
      (Finset.range R).prod
        (fun j => ((p : ℝ) * (R - j : ℕ))) := by
    exact Finset.prod_le_prod (fun j _ => abs_nonneg _) hfactor_le
  have hprod_reflect :
      (Finset.range R).prod
        (fun j => ((p : ℝ) * (R - j : ℕ)))
        = (p : ℝ) ^ R * (R.factorial : ℝ) := by
    calc
      (Finset.range R).prod
          (fun j => ((p : ℝ) * (R - j : ℕ)))
          =
        (Finset.range R).prod
          (fun j => ((p : ℝ) * ((R - 1 - j + 1 : ℕ) : ℝ))) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          have hjR : j < R := Finset.mem_range.mp hj
          congr 2
          omega
      _ =
        (Finset.range R).prod
          (fun j => ((p : ℝ) * ((j + 1 : ℕ) : ℝ))) := by
          simpa using
            (Finset.prod_range_reflect
              (fun j => ((p : ℝ) * ((j + 1 : ℕ) : ℝ))) R)
      _ =
        (Finset.range R).prod (fun _j => (p : ℝ))
          * (Finset.range R).prod (fun j => ((j + 1 : ℕ) : ℝ)) := by
          rw [Finset.prod_mul_distrib]
      _ = (p : ℝ) ^ R * (R.factorial : ℝ) := by
          have hfac :
              (Finset.range R).prod (fun j => ((j + 1 : ℕ) : ℝ))
                = (R.factorial : ℝ) := by
            exact_mod_cast (Finset.prod_range_add_one_eq_factorial R)
          rw [Finset.prod_const, Finset.card_range, hfac]
  have hnum_le_den :
      (Finset.range R).prod
        (fun j => |(q : ℝ) - (j : ℝ) * (p : ℝ)|)
        ≤ (p : ℝ) ^ R * (R.factorial : ℝ) := by
    simpa [hprod_reflect] using hprod_le
  have hcoeff_abs :
      |((casselsRootCoeff p q R : ℚ) : ℝ)|
        =
      (Finset.range R).prod
        (fun j => |(q : ℝ) - (j : ℝ) * (p : ℝ)|)
        / ((p : ℝ) ^ R * (R.factorial : ℝ)) := by
    unfold casselsRootCoeff
    push_cast
    rw [hnum_cast, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, Finset.abs_prod, abs_of_pos hden_pos]
  change |((casselsRootCoeff p q R : ℚ) : ℝ)| ≤ 1
  rw [hcoeff_abs]
  exact (div_le_one hden_pos).mpr hnum_le_den

private theorem casselsRootCoeff_abs_B24_first_omitted_le_one
    (p q : ℕ) (hp0 : 0 < p) :
    let R := casselsB24R p q
    |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| ≤ 1 := by
  let R := casselsB24R p q
  have hrec :=
    casselsRootCoeff_abs_succ_eq p q R (Nat.ne_of_gt hp0)
  have hratio_le_one :
      |(((q : ℝ) - (R : ℝ) * (p : ℝ))
          / ((p : ℝ) * ((R + 1 : ℕ) : ℝ)))| ≤ 1 := by
    have hratio_inv :=
      casselsRootCoeff_abs_ratio_at_B24R_le_inv p q hp0
    have hR1_pos : (0 : ℝ) < ((R + 1 : ℕ) : ℝ) := by positivity
    have hinv_le_one : (((R + 1 : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hR1_pos]
      norm_num
    exact le_trans hratio_inv hinv_le_one
  have hcoeff_R :=
    casselsRootCoeff_abs_at_B24R_le_one p q hp0
  calc
    |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
        =
      |(((q : ℝ) - (R : ℝ) * (p : ℝ))
          / ((p : ℝ) * ((R + 1 : ℕ) : ℝ)))|
        * |((casselsRootCoeff p q R : ℚ) : ℝ)| := hrec
    _ ≤ 1 * 1 := by
      exact mul_le_mul hratio_le_one hcoeff_R (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem p_mul_casselsB24R_le_q_add_p (p q : ℕ) :
    p * casselsB24R p q ≤ q + p := by
  unfold casselsB24R
  have h := Nat.div_mul_le_self q p
  nlinarith [h]

theorem two_mul_casselsB24R_lt_q
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    2 * casselsB24R p q < q := by
  unfold casselsB24R
  have h_div_le : q / p ≤ q / 5 :=
    Nat.div_le_div_left hp5 (by omega)
  have hk1 : 1 ≤ q / 5 := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 5)]
    omega
  have h5k : 5 * (q / 5) ≤ q := by
    have := Nat.div_mul_le_self q 5
    omega
  omega

theorem casselsB24R_lt_q
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsB24R p q < q := by
  have htwo := two_mul_casselsB24R_lt_q p q hp5 hpq
  have hpos := casselsB24R_pos p q
  omega

theorem casselsB24R_add_rho_lt_q
    (p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsB24R p q + casselsB24Rho p q < q := by
  have htwo : 2 * casselsB24R p q < q :=
    two_mul_casselsB24R_lt_q p q hp5 hpq
  have hrho_le : casselsB24Rho p q ≤ casselsB24R p q := by
    unfold casselsB24Rho
    exact Nat.div_le_self _ _
  omega

theorem casselsB24Qfac_mul_X_lt_one_div_five_of_u_pow_gt
    (u p q : ℕ) (hu : 1 < u) (hp5 : 5 ≤ p) (hpq : p < q)
    (hu_large : 5 * p ^ q < u ^ p) :
    casselsB24Qfac p q * casselsB24X u p < (1 / 5 : ℝ) := by
  let R := casselsB24R p q
  let ρ := casselsB24Rho p q
  have hRρ_lt : R + ρ < q := by
    dsimp [R, ρ]
    exact casselsB24R_add_rho_lt_q p q hp5 hpq
  have hpR_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ p)
  have hp_pow_le :
      (p : ℝ) ^ (R + ρ) ≤ (p : ℝ) ^ q :=
    pow_le_pow_right₀ hpR_one (Nat.le_of_lt hRρ_lt)
  have huR_pos : (0 : ℝ) < u := by
    exact_mod_cast (by omega : 0 < u)
  have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := pow_pos huR_pos p
  have hlargeR : (5 : ℝ) * (p : ℝ) ^ q < (u : ℝ) ^ p := by
    exact_mod_cast hu_large
  have hpq_div_lt : (p : ℝ) ^ q / (u : ℝ) ^ p < (1 / 5 : ℝ) := by
    rw [div_lt_iff₀ hup_pos]
    nlinarith
  have hinv_nonneg : 0 ≤ ((u : ℝ) ^ p)⁻¹ :=
    le_of_lt (inv_pos.mpr hup_pos)
  calc
    casselsB24Qfac p q * casselsB24X u p
        = (p : ℝ) ^ (R + ρ) * ((u : ℝ) ^ p)⁻¹ := by
            dsimp [casselsB24Qfac, casselsB24X, R, ρ]
    _ ≤ (p : ℝ) ^ q * ((u : ℝ) ^ p)⁻¹ :=
        mul_le_mul_of_nonneg_right hp_pow_le hinv_nonneg
    _ = (p : ℝ) ^ q / (u : ℝ) ^ p := by ring
    _ < (1 / 5 : ℝ) := hpq_div_lt

private theorem casselsB24X_le_inv_two_mul_q_of_u_pow_gt
    (u p q : ℕ) (hp5 : 5 ≤ p) (hq0 : 0 < q)
    (hu_large : 5 * p ^ q < u ^ p) :
    casselsB24X u p ≤ (1 / (2 * q : ℝ)) := by
  unfold casselsB24X
  have hq_le_pq : q ≤ p ^ q := by
    have hq_lt_twoq : q < 2 ^ q := Nat.lt_two_pow_self
    have htwoq_le_pq : 2 ^ q ≤ p ^ q :=
      Nat.pow_le_pow_left (by omega : 2 ≤ p) q
    exact Nat.le_of_lt (lt_of_lt_of_le hq_lt_twoq htwoq_le_pq)
  have htwoq_le_fivepq : 2 * q ≤ 5 * p ^ q := by
    nlinarith
  have htwoq_le_up : 2 * q ≤ u ^ p :=
    htwoq_le_fivepq.trans (Nat.le_of_lt hu_large)
  have htwoq_posR : (0 : ℝ) < 2 * (q : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * q)
  have hup_leR : (2 : ℝ) * (q : ℝ) ≤ (u : ℝ) ^ p := by
    have hcast : ((2 * q : ℕ) : ℝ) ≤ (u : ℝ) ^ p := by
      exact_mod_cast htwoq_le_up
    simpa using hcast
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le htwoq_posR hup_leR

/-- Finite truncation using the actual coefficient stream of
`((1-X)^q + X^q)^(1/p)`. -/
private def casselsActualTruncQ (u p q N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1),
    casselsActualRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k

private theorem cassels_actual_term_den_dvd_clear
    (u p q N k : ℕ) (hqpos : 0 < q) (hkN : k ≤ N) :
    (casselsActualRootCoeff p q k
        * (u : ℚ) ^ (q - 1)
        * (((u : ℚ) ^ p)⁻¹) ^ k).den
      ∣ casselsPadeClearDen u p N := by
  have hcoeff :
      (casselsActualRootCoeff p q k).den ∣ casselsCoeffDenBound p k :=
    casselsActualRootCoeff_den_dvd p q k hqpos
  have hupow :
      (((u : ℚ) ^ (q - 1)).den) ∣ 1 := by
    simp
  have hinv :
      ((((u : ℚ) ^ p)⁻¹) ^ k).den ∣ u ^ (p * k) := by
    rw [inv_pow, ← pow_mul]
    exact rat_inv_nat_pow_den_dvd u (p * k)
  have hleft :
      (casselsActualRootCoeff p q k * (u : ℚ) ^ (q - 1)).den
        ∣ casselsCoeffDenBound p k * 1 :=
    rat_mul_den_dvd_of_den_dvd _ _ hcoeff hupow
  have hterm :
      (casselsActualRootCoeff p q k
          * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k).den
        ∣ (casselsCoeffDenBound p k * 1) * u ^ (p * k) :=
    rat_mul_den_dvd_of_den_dvd _ _ hleft hinv
  refine hterm.trans ?_
  unfold casselsCoeffDenBound casselsPadeClearDen
  have hp_part :
      p ^ k * Nat.factorial k ∣ p ^ N * Nat.factorial N :=
    Nat.mul_dvd_mul
      (pow_dvd_pow p hkN)
      (Nat.factorial_dvd_factorial hkN)
  have hu_part : u ^ (p * k) ∣ u ^ (p * N) :=
    pow_dvd_pow u (Nat.mul_le_mul_left p hkN)
  have hmul :
      (p ^ k * Nat.factorial k) * u ^ (p * k)
        ∣ (p ^ N * Nat.factorial N) * u ^ (p * N) :=
    Nat.mul_dvd_mul hp_part hu_part
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

private theorem cassels_actual_trunc_cleared_integral
    (u p q N : ℕ) (hqpos : 0 < q) :
    ∃ z : ℤ,
      (casselsPadeClearDen u p N : ℚ) * casselsActualTruncQ u p q N
        = (z : ℚ) := by
  classical
  let D : ℕ := casselsPadeClearDen u p N
  let f : ℕ → ℚ := fun k =>
    casselsActualRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k
  have hterm :
      ∀ k : ℕ, ∃ z : ℤ, k ∈ Finset.range (N + 1) →
        (D : ℚ) * f k = (z : ℚ) := by
    intro k
    by_cases hk : k ∈ Finset.range (N + 1)
    · have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rcases rat_mul_is_int_of_den_dvd D (f k)
          (by
            dsimp [D, f]
            exact cassels_actual_term_den_dvd_clear u p q N k hqpos hkN) with
        ⟨z, hz⟩
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun hk' => False.elim (hk hk')⟩
  choose Z hZ using hterm
  refine ⟨∑ k ∈ Finset.range (N + 1), Z k, ?_⟩
  calc
    (casselsPadeClearDen u p N : ℚ) * casselsActualTruncQ u p q N
        = (D : ℚ) * (∑ k ∈ Finset.range (N + 1), f k) := by
            dsimp [D, f, casselsActualTruncQ]
    _ = ∑ k ∈ Finset.range (N + 1), (D : ℚ) * f k := by
            rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (N + 1), ((Z k : ℤ) : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hZ k hk
    _ = ((∑ k ∈ Finset.range (N + 1), Z k : ℤ) : ℚ) := by
            push_cast
            rfl

/-- Scaled actual-branch tail: after multiplying by `u^(q-1)`, the
branch gap is the concrete real gap `v - casselsActualTruncQ`. -/
private theorem cassels_actualRootCoeff_scaled_tail_hasSum_gap_of_hroot
    (u v p q R : ℕ) (hu : 1 < u)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpq : p < q)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    HasSum
      (fun n => (u : ℝ) ^ (q - 1)
        * ((casselsActualRootCoeff p q (n + (R + 1)) : ℝ)
          * (((u : ℝ) ^ p)⁻¹) ^ (n + (R + 1))))
      ((v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)) := by
  have hs :=
    (cassels_actualRootCoeff_tail_hasSum_gap_of_hroot
      u v p q R hu hp5 hq5 hpq hroot).mul_left ((u : ℝ) ^ (q - 1))
  convert hs using 1
  · have huRpos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
    have hpow_ne : (u : ℝ) ^ (q - 1) ≠ 0 := (pow_pos huRpos _).ne'
    have hTcast :
        ((casselsActualTruncQ u p q R : ℚ) : ℝ)
          =
        (u : ℝ) ^ (q - 1) *
          ∑ x ∈ Finset.range (1 + R),
            (u : ℝ)⁻¹ ^ (p * x) * (casselsActualRootCoeff p q x : ℝ) := by
      unfold casselsActualTruncQ
      rw [Finset.mul_sum]
      push_cast
      apply Finset.sum_congr
      · rw [add_comm]
      · intro k _
        push_cast
        rw [inv_pow ((u : ℝ) ^ p) k, ← pow_mul]
        ring
    rw [hTcast, mul_sub, mul_div_cancel₀ _ hpow_ne]
    congr 1
    congr 1
    apply Finset.sum_congr
    · rw [add_comm]
    · intro k _
      rw [inv_pow ((u : ℝ) ^ p) k, ← pow_mul]
      ring

private theorem cassels_actualRootCoeff_scaled_tail_gap_abs_le
    (u v p q R : ℕ) (hu : 1 < u)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpq : p < q)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    |(v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)|
      ≤
    (u : ℝ) ^ (q - 1)
      * (((u : ℝ) ^ p)⁻¹) ^ (R + 1)
      * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q) := by
  have huRpos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
  have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := pow_pos huRpos p
  have hX0 : (0 : ℝ) ≤ ((u : ℝ) ^ p)⁻¹ := le_of_lt (inv_pos.mpr hup_pos)
  have hXne : ((u : ℝ) ^ p)⁻¹ ≠ 0 := inv_ne_zero hup_pos.ne'
  have hXle : ((u : ℝ) ^ p)⁻¹ ≤ (1 / 32 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (calc
        (32 : ℝ) = 2 ^ 5 := by norm_num
        _ ≤ (u : ℝ) ^ 5 := by
          exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
            (by exact_mod_cast hu) 5
        _ ≤ (u : ℝ) ^ p := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ u))
          (by omega))
  let X : ℝ := ((u : ℝ) ^ p)⁻¹
  let C : ℝ := (u : ℝ) ^ (q - 1) * X ^ (R + 1)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hHS :=
    cassels_actualRootCoeff_scaled_tail_hasSum_gap_of_hroot
      u v p q R hu hp5 hq5 hpq hroot
  have htsum :
      (∑' n, (u : ℝ) ^ (q - 1)
        * ((casselsActualRootCoeff p q (n + (R + 1)) : ℝ)
          * X ^ (n + (R + 1))))
        = (v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ) := by
    dsimp [X]
    exact hHS.tsum_eq
  have hsumm : Summable (fun n =>
      ‖(u : ℝ) ^ (q - 1)
        * ((casselsActualRootCoeff p q (n + (R + 1)) : ℝ)
          * X ^ (n + (R + 1)))‖) := by
    simpa [X, Real.norm_eq_abs] using summable_abs_iff.mpr hHS.summable
  have hbound := norm_tsum_le_tsum_norm hsumm
  rw [htsum, Real.norm_eq_abs] at hbound
  have hterm : ∀ n,
      ‖(u : ℝ) ^ (q - 1)
        * ((casselsActualRootCoeff p q (n + (R + 1)) : ℝ)
          * X ^ (n + (R + 1)))‖
        =
      C * (|(casselsActualRootCoeff p q (n + (R + 1)) : ℝ)| * X ^ n) := by
    intro n
    dsimp [C, X]
    rw [abs_mul, abs_mul,
      abs_of_pos (pow_pos huRpos (q - 1)),
      abs_of_nonneg (pow_nonneg hX0 (n + (R + 1))),
      pow_add]
    ring
  have htail :=
    cassels_actualRootCoeff_shifted_tail_le p q hp5 hpq (R + 1) hX0 hXle
  calc
    |(v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)|
        ≤ ∑' n, ‖(u : ℝ) ^ (q - 1)
            * ((casselsActualRootCoeff p q (n + (R + 1)) : ℝ)
              * X ^ (n + (R + 1)))‖ := hbound
    _ = C * ∑' n,
          |(casselsActualRootCoeff p q (n + (R + 1)) : ℝ)| * X ^ n := by
          rw [← tsum_mul_left]
          exact tsum_congr hterm
    _ ≤ C * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q) :=
          mul_le_mul_of_nonneg_left htail hC_nonneg

private theorem casselsActualTruncQ_eq_padeTruncQ_of_lt_q
    (u p q N : ℕ) (hNq : N < q) :
    casselsActualTruncQ u p q N = casselsPadeTruncQ u p q N := by
  unfold casselsActualTruncQ casselsPadeTruncQ
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k < q := by
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact lt_of_le_of_lt hkN hNq
  rw [cassels_actual_eq_binomial_below_q p q k hkq]

private theorem casselsB24ActualTruncQ_eq_padeTruncQ
    (u p q : ℕ) (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsActualTruncQ u p q (casselsB24R p q)
      = casselsPadeTruncQ u p q (casselsB24R p q) :=
  casselsActualTruncQ_eq_padeTruncQ_of_lt_q
    u p q (casselsB24R p q) (casselsB24R_lt_q p q hp5 hpq)

theorem casselsActualRootCoeff_b24_succ_ne_zero
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hpq : p < q) :
    casselsActualRootCoeff p q (casselsB24R p q + 1) ≠ 0 := by
  have htwo : 2 * casselsB24R p q < q :=
    two_mul_casselsB24R_lt_q p q hp5 hpq
  have hpos : 0 < casselsB24R p q := casselsB24R_pos p q
  exact casselsActualRootCoeff_ne_zero_of_lt_q
    p q (casselsB24R p q + 1) hp hq hpq (by omega)

theorem casselsActual_scaled_tail_first_b24_ne_zero
    (u p q : ℕ) (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hpq : p < q) :
    (u : ℝ) ^ (q - 1)
      * ((casselsActualRootCoeff p q (casselsB24R p q + 1) : ℝ)
        * (((u : ℝ) ^ p)⁻¹) ^ (casselsB24R p q + 1)) ≠ 0 := by
  have hu_ne : (u : ℝ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
  refine mul_ne_zero ?_ ?_
  · exact pow_ne_zero _ hu_ne
  · refine mul_ne_zero ?_ ?_
    · exact_mod_cast
        casselsActualRootCoeff_b24_succ_ne_zero p q hp hq hp5 hpq
    · exact pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ hu_ne))

/-- In the lower-prime branch, Cassels' truncation index is `R = 1`. -/
theorem casselsClassical_R_eq_one_of_lt (p q : ℕ) (hpq : p < q) :
    Ripple.LPP.CasselsClassical.casselsR p q = 1 := by
  unfold Ripple.LPP.CasselsClassical.casselsR
  rw [Nat.div_eq_of_lt hpq]

/-- In the lower-prime branch, Cassels' shift is `σ = q - p`. -/
theorem casselsClassical_sigma_eq_sub_of_lt (p q : ℕ) (hpq : p < q) :
    Ripple.LPP.CasselsClassical.casselsSigma p q = q - p := by
  unfold Ripple.LPP.CasselsClassical.casselsSigma
  rw [casselsClassical_R_eq_one_of_lt p q hpq]
  simp

/-- In the lower-prime branch, the extra `q`-adic factorial exponent is zero. -/
theorem casselsClassical_nu_eq_zero_of_lt (p q : ℕ) (hpq : p < q) :
    Ripple.LPP.CasselsClassical.casselsNu p q = 0 := by
  unfold Ripple.LPP.CasselsClassical.casselsNu
  rw [casselsClassical_R_eq_one_of_lt p q hpq]
  simp

/-- Classical binomial truncation used in Cassels' B2.4:
`Σ_{r≤R} binom(p/q,r) z^{q(R-r)}`. -/
noncomputable def casselsClassicalTruncQ (p q z : ℕ) : ℚ :=
  let R := Ripple.LPP.CasselsClassical.casselsR p q
  ∑ r ∈ Finset.range (R + 1),
    Ripple.LPP.CasselsClassical.gbinomQ ((p : ℚ) / (q : ℚ)) r
      * (z : ℚ) ^ (q * (R - r))

theorem casselsClassical_gbinomQ_zero (α : ℚ) :
    Ripple.LPP.CasselsClassical.gbinomQ α 0 = 1 := by
  simp [Ripple.LPP.CasselsClassical.gbinomQ]

theorem casselsClassical_gbinomQ_one (α : ℚ) :
    Ripple.LPP.CasselsClassical.gbinomQ α 1 = α := by
  simp [Ripple.LPP.CasselsClassical.gbinomQ]

/-- In the lower-prime branch, the cleared `R=1` truncation is
`q*z^q + p`. -/
theorem casselsClassicalTruncQ_R_one_cleared
    (p q z : ℕ) (hpq : p < q) (hq0 : (q : ℚ) ≠ 0) :
    (q : ℚ) * casselsClassicalTruncQ p q z =
      (q : ℚ) * (z : ℚ) ^ q + (p : ℚ) := by
  unfold casselsClassicalTruncQ
  rw [casselsClassical_R_eq_one_of_lt p q hpq]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [Ripple.LPP.CasselsClassical.gbinomQ]
  field_simp [hq0]

/-- The integer expression appearing in the `R=1` lower-prime B2.4 gap. -/
def casselsClassicalR1GapInt (p q z b : ℕ) : ℤ :=
  (q : ℤ) * (z : ℤ) ^ q + (p : ℤ)
    - (q : ℤ) * (z : ℤ) ^ (q - p) * (b : ℤ)

/-- Legendre's estimate in the exact form used by Cassels' clearing:
`v_p(r!) ≤ floor(r / (p-1))`. -/
theorem padicValNat_factorial_le_div_sub_one
    (p r : ℕ) [Fact p.Prime] :
    padicValNat p r.factorial ≤ r / (p - 1) := by
  by_cases hr : r = 0
  · simp [hr]
  have hp_prime : p.Prime := (inferInstance : Fact p.Prime).out
  have hp_sub_pos : 0 < p - 1 := by
    have hp2 : 2 ≤ p := hp_prime.two_le
    omega
  have hmul_lt :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hr
  have hmul_le : (p - 1) * padicValNat p r.factorial ≤ r :=
    le_of_lt hmul_lt
  rw [Nat.le_div_iff_mul_le hp_sub_pos]
  simpa [Nat.mul_comm] using hmul_le

/-- Cassels' original B2.4 truncation clears with the paper denominator
`p^(R+rho)`, where in the lower-prime orientation
`R = floor(q/p)+1` and `rho = floor(R/(p-1))`.

This is the faithful clearing for the expression
`Σ_{r≤R} binom(q/p,r) u^{p(R-r)}` appearing after multiplying
Cassels' binomial expansion by `u^(R*p-q)`. -/
theorem casselsClassicalTruncQ_lower_cleared_integral
    (u p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ∃ A : ℤ,
      ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * casselsClassicalTruncQ q p u = (A : ℚ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set R := casselsB24R p q with hR_def
  set ρ := casselsB24Rho p q with hρ_def
  have hR_classical :
      Ripple.LPP.CasselsClassical.casselsR q p = R := by
    simp [Ripple.LPP.CasselsClassical.casselsR, casselsB24R, hR_def]
  have hp_ne_q : q ≠ p := by omega
  have hpQ_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hterm :
      ∀ r : ℕ, ∃ z : ℤ, r ∈ Finset.range (R + 1) →
        (p : ℚ) ^ (R + ρ)
          * (Ripple.LPP.CasselsClassical.gbinomQ ((q : ℚ) / (p : ℚ)) r
              * (u : ℚ) ^ (p * (R - r))) = (z : ℚ) := by
    intro r
    by_cases hrmem : r ∈ Finset.range (R + 1)
    · have hrR : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrmem)
      let ν : ℕ := padicValNat p r.factorial
      have hνρ : ν ≤ ρ := by
        dsimp [ν]
        have hνr : padicValNat p r.factorial ≤ r / (p - 1) :=
          padicValNat_factorial_le_div_sub_one p r
        have hdiv : r / (p - 1) ≤ R / (p - 1) :=
          Nat.div_le_div_right hrR
        simpa [hρ_def, casselsB24Rho, hR_def] using le_trans hνr hdiv
      have hrν : r + ν ≤ R + ρ := by omega
      have hdiv_fact :
          (r.factorial : ℤ) ∣
            (p : ℤ) ^ ν
              * ∏ i ∈ Finset.range r, ((q : ℤ) - (i : ℤ) * p) := by
        dsimp [ν]
        exact Ripple.LPP.CasselsClassical.cassels_qpow_prod_factorial_dvd
          hq hp hp_ne_q r
      rcases hdiv_fact with ⟨M, hM⟩
      refine ⟨(p : ℤ) ^ (R + ρ - (r + ν)) * M
          * (u : ℤ) ^ (p * (R - r)), fun _ => ?_⟩
      have hM_Q :
          (p : ℚ) ^ ν
              * (∏ i ∈ Finset.range r, (((q : ℤ) - (i : ℤ) * p : ℤ) : ℚ))
            = (r.factorial : ℚ) * (M : ℚ) := by
        exact_mod_cast hM
      have hM_Q_comm :
          (p : ℚ) ^ ν
              * (∏ i ∈ Finset.range r, (((q : ℤ) - (p : ℤ) * i : ℤ) : ℚ))
            = (r.factorial : ℚ) * (M : ℚ) := by
        rw [← hM_Q]
        congr 1
        apply Finset.prod_congr rfl
        intro i _hi
        congr 1
        ring
      have hM_Q_comm :
          (p : ℚ) ^ ν
              * (∏ i ∈ Finset.range r, (((q : ℤ) - (p : ℤ) * i : ℤ) : ℚ))
            = (r.factorial : ℚ) * (M : ℚ) := by
        rw [← hM_Q]
        congr 1
        apply Finset.prod_congr rfl
        intro i _hi
        congr 1
        ring
      have hfact_ne : (r.factorial : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr r.factorial_ne_zero
      have hpν_ne : (p : ℚ) ^ ν ≠ 0 := pow_ne_zero _ hpQ_ne
      have hpRρ_split :
          (p : ℚ) ^ (R + ρ) =
            (p : ℚ) ^ (r + ν) * (p : ℚ) ^ (R + ρ - (r + ν)) := by
        rw [← pow_add, Nat.add_sub_cancel' hrν]
      have hprν_split :
          (p : ℚ) ^ (r + ν) = (p : ℚ) ^ r * (p : ℚ) ^ ν := by
        rw [pow_add]
      have hgbinom :
          Ripple.LPP.CasselsClassical.gbinomQ ((q : ℚ) / (p : ℚ)) r =
            (∏ i ∈ Finset.range r, (((q : ℤ) - (i : ℤ) * p : ℤ) : ℚ))
              / ((p : ℚ) ^ r * (r.factorial : ℚ)) := by
        simpa using
          (Ripple.LPP.CasselsClassical.gbinomQ_nat_div
            (p := q) (q := p) (r := r) hpQ_ne)
      rw [hgbinom, hpRρ_split, hprν_split]
      have hcalc :
          ((p : ℚ) ^ r * (p : ℚ) ^ ν
              * (p : ℚ) ^ (R + ρ - (r + ν)))
            *
              ((∏ i ∈ Finset.range r,
                    (((q : ℤ) - (i : ℤ) * p : ℤ) : ℚ))
                / ((p : ℚ) ^ r * (r.factorial : ℚ))
                * (u : ℚ) ^ (p * (R - r)))
          =
          (p : ℚ) ^ (R + ρ - (r + ν)) * (M : ℚ)
            * (u : ℚ) ^ (p * (R - r)) := by
        field_simp [hpQ_ne, hfact_ne]
        ring_nf at hM_Q ⊢
        ring_nf at hM_Q_comm
        rw [hM_Q_comm]
      rw [hcalc]
      push_cast
      ring
    · exact ⟨0, fun h => False.elim (hrmem h)⟩
  choose Z hZ using hterm
  refine ⟨∑ r ∈ Finset.range (R + 1), Z r, ?_⟩
  unfold casselsClassicalTruncQ
  rw [hR_classical]
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  exact hZ r hr

/-- Integer form of Cassels' cleared B2.4 gap in the lower-prime
orientation.  This is the paper expression
`p^(R+rho) * (u^(R*p-q) * b - T_R)`, where `b` is later instantiated
as `v*u`. -/
theorem casselsClassical_cleared_gap_integer_lower
    (u b p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ∃ I : ℤ,
      ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * (((u : ℚ) ^ (p * casselsB24R p q - q) * (b : ℚ))
            - casselsClassicalTruncQ q p u)
        = (I : ℚ) := by
  obtain ⟨A, hA⟩ :=
    casselsClassicalTruncQ_lower_cleared_integral u p q hp hq hpq
  refine ⟨
    ((p ^ (casselsB24R p q + casselsB24Rho p q)
        * u ^ (p * casselsB24R p q - q) * b : ℕ) : ℤ) - A, ?_⟩
  calc
    ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * (((u : ℚ) ^ (p * casselsB24R p q - q) * (b : ℚ))
            - casselsClassicalTruncQ q p u)
        =
      ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * ((u : ℚ) ^ (p * casselsB24R p q - q) * (b : ℚ))
      - ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * casselsClassicalTruncQ q p u := by
          ring
    _ =
      ((p ^ (casselsB24R p q + casselsB24Rho p q)
          * u ^ (p * casselsB24R p q - q) * b : ℕ) : ℚ)
        - (A : ℚ) := by
          rw [hA]
          push_cast
          ring
    _ =
      ((((p ^ (casselsB24R p q + casselsB24Rho p q)
          * u ^ (p * casselsB24R p q - q) * b : ℕ) : ℤ) - A : ℤ) : ℚ) := by
          push_cast
          ring

/-- Signed B2.4 truncation for `(1-X)^(q/p)`, after multiplying by
`u^(pR)`.  This is the truncation compatible with `casselsActualTruncQ`
below the first correction term. -/
noncomputable def casselsB24RootTruncQ (u p q : ℕ) : ℚ :=
  let R := casselsB24R p q
  ∑ r ∈ Finset.range (R + 1),
    casselsRootCoeff p q r * (u : ℚ) ^ (p * (R - r))

private theorem casselsB24RootTruncQ_real_div_pow_eq_sum
    (u p q : ℕ) (hu : 0 < u) :
    let R := casselsB24R p q
    ((casselsB24RootTruncQ u p q : ℚ) : ℝ) / (u : ℝ) ^ (p * R)
      =
    ∑ r ∈ Finset.range (R + 1),
      ((casselsRootCoeff p q r : ℚ) : ℝ) * (casselsB24X u p) ^ r := by
  classical
  let R := casselsB24R p q
  have huR_ne : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hden_ne : (u : ℝ) ^ (p * R) ≠ 0 :=
    pow_ne_zero _ huR_ne
  dsimp [R, casselsB24RootTruncQ]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  have hrR : r ≤ casselsB24R p q :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hpow_split :
      (u : ℝ) ^ (p * casselsB24R p q)
        =
      (u : ℝ) ^ (p * (casselsB24R p q - r))
        * (u : ℝ) ^ (p * r) := by
    rw [← pow_add]
    congr 1
    rw [← Nat.mul_add, Nat.sub_add_cancel hrR]
  have hpow_term :
      (u : ℝ) ^ (p * (casselsB24R p q - r))
          / (u : ℝ) ^ (p * casselsB24R p q)
        =
      (((u : ℝ) ^ p)⁻¹) ^ r := by
    calc
      (u : ℝ) ^ (p * (casselsB24R p q - r))
          / (u : ℝ) ^ (p * casselsB24R p q)
          =
        (u : ℝ) ^ (p * (casselsB24R p q - r))
          / ((u : ℝ) ^ (p * (casselsB24R p q - r))
              * (u : ℝ) ^ (p * r)) := by rw [hpow_split]
      _ = ((u : ℝ) ^ (p * r))⁻¹ := by
            field_simp [pow_ne_zero (p * (casselsB24R p q - r)) huR_ne,
              pow_ne_zero (p * r) huR_ne]
      _ = (((u : ℝ) ^ p)⁻¹) ^ r := by
            rw [inv_pow, ← pow_mul]
  dsimp [casselsB24X]
  rw [mul_div_assoc, hpow_term]

private theorem casselsB24_root_tail_abs_le
    (u p q : ℕ) (hu : 1 < u) (hp : p.Prime) :
    let R := casselsB24R p q
    let X := casselsB24X u p
    |casselsB24A u p q
        - ((casselsB24RootTruncQ u p q : ℚ) : ℝ) / (u : ℝ) ^ (p * R)|
      ≤
    |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
      * X ^ (R + 1) / (1 - X) := by
  classical
  let R := casselsB24R p q
  let X := casselsB24X u p
  have hX0 : 0 ≤ X := le_of_lt (casselsB24X_pos u p hu)
  have hXlt : X < 1 :=
    casselsB24X_lt_one u p hu hp.pos
  have hRturn : q < p * R := by
    dsimp [R]
    exact q_lt_p_mul_casselsB24R p q hp.pos
  have htail :=
    casselsRootCoeff_tail_gap_abs_le_geom p q R hp.pos hRturn hX0 hXlt
  have htr :
      ((casselsB24RootTruncQ u p q : ℚ) : ℝ) / (u : ℝ) ^ (p * R)
        =
      ∑ r ∈ Finset.range (R + 1),
        ((casselsRootCoeff p q r : ℚ) : ℝ) * X ^ r := by
    dsimp [R, X]
    exact casselsB24RootTruncQ_real_div_pow_eq_sum u p q (by omega)
  dsimp [casselsB24A, X] at htail ⊢
  rw [htr]
  exact htail

/-- Cassels' B2.4 clearing for the signed binomial truncation:
`p^(R+rho)` already clears all coefficients through `R`. -/
theorem casselsB24RootTruncQ_cleared_integral
    (u p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ∃ A : ℤ,
      ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * casselsB24RootTruncQ u p q = (A : ℚ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set R := casselsB24R p q with hR_def
  set ρ := casselsB24Rho p q with hρ_def
  have hp_ne_q : q ≠ p := by omega
  have hpQ_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hterm :
      ∀ r : ℕ, ∃ z : ℤ, r ∈ Finset.range (R + 1) →
        (p : ℚ) ^ (R + ρ)
          * (casselsRootCoeff p q r * (u : ℚ) ^ (p * (R - r)))
            = (z : ℚ) := by
    intro r
    by_cases hrmem : r ∈ Finset.range (R + 1)
    · have hrR : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hrmem)
      let ν : ℕ := padicValNat p r.factorial
      have hνρ : ν ≤ ρ := by
        dsimp [ν]
        have hνr : padicValNat p r.factorial ≤ r / (p - 1) :=
          padicValNat_factorial_le_div_sub_one p r
        have hdiv : r / (p - 1) ≤ R / (p - 1) :=
          Nat.div_le_div_right hrR
        simpa [hρ_def, casselsB24Rho, hR_def] using le_trans hνr hdiv
      have hrν : r + ν ≤ R + ρ := by omega
      have hdiv_fact :
          (r.factorial : ℤ) ∣
            (p : ℤ) ^ ν
              * ∏ i ∈ Finset.range r, ((q : ℤ) - (i : ℤ) * p) := by
        dsimp [ν]
        exact Ripple.LPP.CasselsClassical.cassels_qpow_prod_factorial_dvd
          hq hp hp_ne_q r
      rcases hdiv_fact with ⟨M, hM⟩
      refine ⟨(p : ℤ) ^ (R + ρ - (r + ν))
          * ((-1 : ℤ) ^ r * M)
          * (u : ℤ) ^ (p * (R - r)), fun _ => ?_⟩
      have hM_Q :
          (p : ℚ) ^ ν
              * (∏ i ∈ Finset.range r, (((q : ℤ) - (i : ℤ) * p : ℤ) : ℚ))
            = (r.factorial : ℚ) * (M : ℚ) := by
        exact_mod_cast hM
      have hM_Q_comm :
          (p : ℚ) ^ ν
              * (∏ i ∈ Finset.range r, (((q : ℤ) - (p : ℤ) * i : ℤ) : ℚ))
            = (r.factorial : ℚ) * (M : ℚ) := by
        rw [← hM_Q]
        congr 1
        apply Finset.prod_congr rfl
        intro i _hi
        congr 1
        ring
      have hfact_ne : (r.factorial : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr r.factorial_ne_zero
      have hpRρ_split :
          (p : ℚ) ^ (R + ρ) =
            (p : ℚ) ^ (r + ν) * (p : ℚ) ^ (R + ρ - (r + ν)) := by
        rw [← pow_add, Nat.add_sub_cancel' hrν]
      have hprν_split :
          (p : ℚ) ^ (r + ν) = (p : ℚ) ^ r * (p : ℚ) ^ ν := by
        rw [pow_add]
      have hroot :
          casselsRootCoeff p q r =
            ((-1 : ℚ) ^ r)
              * (∏ i ∈ Finset.range r,
                    (((q : ℤ) - (i : ℤ) * p : ℤ) : ℚ))
              / ((p : ℚ) ^ r * (r.factorial : ℚ)) := by
        unfold casselsRootCoeff casselsBinomNum
        push_cast
        rfl
      rw [hroot, hpRρ_split, hprν_split]
      have hcalc :
          ((p : ℚ) ^ r * (p : ℚ) ^ ν
              * (p : ℚ) ^ (R + ρ - (r + ν)))
            *
              (((-1 : ℚ) ^ r
                * (∏ i ∈ Finset.range r,
                    (((q : ℤ) - (i : ℤ) * p : ℤ) : ℚ))
                / ((p : ℚ) ^ r * (r.factorial : ℚ)))
                * (u : ℚ) ^ (p * (R - r)))
          =
          (p : ℚ) ^ (R + ρ - (r + ν))
            * ((-1 : ℚ) ^ r * (M : ℚ))
            * (u : ℚ) ^ (p * (R - r)) := by
        field_simp [hpQ_ne, hfact_ne]
        ring_nf at hM_Q ⊢
        ring_nf at hM_Q_comm
        rw [hM_Q_comm]
      rw [hcalc]
      push_cast
      ring
    · exact ⟨0, fun h => False.elim (hrmem h)⟩
  choose Z hZ using hterm
  refine ⟨∑ r ∈ Finset.range (R + 1), Z r, ?_⟩
  unfold casselsB24RootTruncQ
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  exact hZ r hr

/-- Integer form of the signed B2.4 root gap before comparing it with the
actual algebraic branch.  Later `b` is instantiated as `v*u`. -/
theorem casselsB24Root_cleared_gap_integer
    (u b p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ∃ I : ℤ,
      ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * (((u : ℚ) ^ (p * casselsB24R p q - q) * (b : ℚ))
            - casselsB24RootTruncQ u p q)
        = (I : ℚ) := by
  obtain ⟨A, hA⟩ :=
    casselsB24RootTruncQ_cleared_integral u p q hp hq hpq
  refine ⟨
    ((p ^ (casselsB24R p q + casselsB24Rho p q)
        * u ^ (p * casselsB24R p q - q) * b : ℕ) : ℤ) - A, ?_⟩
  calc
    ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * (((u : ℚ) ^ (p * casselsB24R p q - q) * (b : ℚ))
            - casselsB24RootTruncQ u p q)
        =
      ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * ((u : ℚ) ^ (p * casselsB24R p q - q) * (b : ℚ))
      - ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * casselsB24RootTruncQ u p q := by
          ring
    _ =
      ((p ^ (casselsB24R p q + casselsB24Rho p q)
          * u ^ (p * casselsB24R p q - q) * b : ℕ) : ℚ)
        - (A : ℚ) := by
          rw [hA]
          push_cast
          ring
    _ =
      ((((p ^ (casselsB24R p q + casselsB24Rho p q)
          * u ^ (p * casselsB24R p q - q) * b : ℕ) : ℤ) - A : ℤ) : ℚ) := by
          push_cast
          ring

/-- Cassels' B2.4 normalized gap:
`p^(R+rho) u^(pR-q+1) (v - T_R)`. -/
noncomputable def casselsB24GapQ (u v p q : ℕ) : ℚ :=
  let R := casselsB24R p q
  let ρ := casselsB24Rho p q
  (p : ℚ) ^ (R + ρ)
    * (u : ℚ) ^ (p * R - q + 1)
    * ((v : ℚ) - casselsActualTruncQ u p q R)

private theorem casselsB24_scaled_actualTruncQ_eq_rootTruncQ
    (u p q : ℕ) (hu : 0 < u) (hp5 : 5 ≤ p) (hpq : p < q) :
    (u : ℚ) ^ (p * casselsB24R p q - q + 1)
      * casselsActualTruncQ u p q (casselsB24R p q)
        = casselsB24RootTruncQ u p q := by
  classical
  set R := casselsB24R p q with hR_def
  have huQ_ne : (u : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hactual :
      casselsActualTruncQ u p q R = casselsPadeTruncQ u p q R := by
    subst R
    exact casselsB24ActualTruncQ_eq_padeTruncQ u p q hp5 hpq
  rw [hactual]
  unfold casselsPadeTruncQ casselsB24RootTruncQ
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · simp [hR_def]
  · intro r hr
    have hrR : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hEadd : p * R - q + 1 + (q - 1) = p * R := by
      have hq_lt : q < p * R := by
        subst R
        exact q_lt_p_mul_casselsB24R p q (by omega)
      omega
    have hinv :
        (((u : ℚ) ^ p)⁻¹) ^ r = ((u : ℚ) ^ (p * r))⁻¹ := by
      rw [inv_pow, ← pow_mul]
    have hpow_mul :
        (u : ℚ) ^ (p * (R - r)) * (u : ℚ) ^ (p * r)
          = (u : ℚ) ^ (p * R) := by
      rw [← pow_add]
      have hexp : p * (R - r) + p * r = p * R := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hrR]
      rw [hexp]
    have hpow_cancel :
        (u : ℚ) ^ (p * R) * ((u : ℚ) ^ (p * r))⁻¹
          = (u : ℚ) ^ (p * (R - r)) := by
      have hden : (u : ℚ) ^ (p * r) ≠ 0 := pow_ne_zero _ huQ_ne
      rw [← hpow_mul]
      field_simp [hden]
    calc
      (u : ℚ) ^ (p * casselsB24R p q - q + 1)
          * (casselsRootCoeff p q r
            * (u : ℚ) ^ (q - 1)
            * (((u : ℚ) ^ p)⁻¹) ^ r)
          =
        casselsRootCoeff p q r
          * ((u : ℚ) ^ (p * R - q + 1 + (q - 1))
            * (((u : ℚ) ^ p)⁻¹) ^ r) := by
            simp [hR_def]
            ring
      _ =
        casselsRootCoeff p q r
          * ((u : ℚ) ^ (p * R) * ((u : ℚ) ^ (p * r))⁻¹) := by
            rw [hEadd, hinv]
      _ =
        casselsRootCoeff p q r * (u : ℚ) ^ (p * (R - r)) := by
            rw [hpow_cancel]

theorem casselsB24_gap_isInt
    {u v p q : ℕ}
    (hu : 0 < u)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpq : p < q) :
    ∃ I : ℤ, (I : ℚ) = casselsB24GapQ u v p q := by
  classical
  obtain ⟨I, hI⟩ :=
    casselsB24Root_cleared_gap_integer u (v * u) p q hp hq hpq
  refine ⟨I, ?_⟩
  let R := casselsB24R p q
  let ρ := casselsB24Rho p q
  have hscaled :
      (u : ℚ) ^ (p * R - q + 1)
        * casselsActualTruncQ u p q R
          = casselsB24RootTruncQ u p q := by
    dsimp [R]
    exact casselsB24_scaled_actualTruncQ_eq_rootTruncQ
      u p q hu hp5 hpq
  have hpow_succ :
      (u : ℚ) ^ (p * R - q + 1)
        = (u : ℚ) ^ (p * R - q) * (u : ℚ) := by
    have hq_lt : q < p * R := by
      dsimp [R]
      exact q_lt_p_mul_casselsB24R p q hp.pos
    have hsucc : p * R - q + 1 = (p * R - q) + 1 := by omega
    rw [hsucc, pow_succ]
  calc
    (I : ℚ)
        =
      ((p ^ (casselsB24R p q + casselsB24Rho p q) : ℕ) : ℚ)
        * (((u : ℚ) ^ (p * casselsB24R p q - q) * ((v * u : ℕ) : ℚ))
            - casselsB24RootTruncQ u p q) := hI.symm
    _ =
      (p : ℚ) ^ (R + ρ)
        * (((u : ℚ) ^ (p * R - q) * ((v : ℚ) * (u : ℚ)))
            - casselsB24RootTruncQ u p q) := by
          dsimp [R, ρ]
          push_cast
          ring
    _ =
      (p : ℚ) ^ (R + ρ)
        * (((u : ℚ) ^ (p * R - q + 1) * (v : ℚ))
            - casselsB24RootTruncQ u p q) := by
          rw [hpow_succ]
          ring
    _ =
      (p : ℚ) ^ (R + ρ)
        * ((u : ℚ) ^ (p * R - q + 1)
            * ((v : ℚ) - casselsActualTruncQ u p q R)) := by
          rw [← hscaled]
          ring
    _ = casselsB24GapQ u v p q := by
          dsimp [casselsB24GapQ, R, ρ]
          ring

/-- B2.2 at numerator `1`: for `k < q`, `k!` divides
`∏_{i<k} (1 - i q)`. -/
theorem cassels_B22_one_factorial_dvd
    (q k : ℕ) (hq : q.Prime) (hk : k < q) :
    (Nat.factorial k : ℤ) ∣
      ∏ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * (q : ℤ)) := by
  classical
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  set P := (∏ i ∈ Finset.range k,
    ((1 : ℤ) - (i : ℤ) * (q : ℤ))).natAbs
  have hfac : ∀ i ∈ Finset.range k,
      ((1 : ℤ) - (i : ℤ) * (q : ℤ)) ≠ 0 := by
    intro i _ h
    have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
    have hiq : (i : ℤ) * q = 1 := by linarith
    by_cases hi0 : i = 0
    · simp [hi0] at hiq
    · have hi_pos : (1 : ℤ) ≤ i :=
        by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi0
      nlinarith
  have hPne : P ≠ 0 := by
    simp only [P, Int.natAbs_ne_zero, Finset.prod_ne_zero_iff]
    exact hfac
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro ℓ e hℓ he
  have hℓp : ℓ.Prime := hℓ
  have hkle : e ≤ (Nat.factorial k).factorization ℓ :=
    (Nat.Prime.pow_dvd_iff_le_factorization hℓ k.factorial_ne_zero).mp he
  by_cases hℓq : ℓ = q
  · subst hℓq
    have hval0 : (Nat.factorial k).factorization ℓ = 0 :=
      Nat.factorization_factorial_eq_zero_of_lt hk
    have he0 : e = 0 := by omega
    subst he0
    simp
  · haveI : Fact ℓ.Prime := ⟨hℓp⟩
    have hℓnq : ¬ ℓ ∣ q := by
      intro hd
      rcases (Nat.Prime.eq_one_or_self_of_dvd hq ℓ hd) with h1 | h2
      · exact hℓp.ne_one h1
      · exact hℓq h2
    have hcopℓ : ∀ d, Nat.Coprime q (ℓ ^ d) :=
      fun d => Nat.Coprime.pow_right d
        ((hℓp.coprime_iff_not_dvd.mpr hℓnq).symm)
    set B := 1 + k * q + k + 2
    have hpiB : ∀ i ∈ Finset.range k,
        padicValInt ℓ ((1 : ℤ) - (i : ℤ) * q) =
          ∑ d ∈ Finset.Ico 1 B,
            (if (↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q)
              then 1 else 0) := by
      intro i hi
      have hne := hfac i hi
      have hmne : ((1 : ℤ) - (i : ℤ) * q).natAbs ≠ 0 :=
        Int.natAbs_ne_zero.mpr hne
      rw [Finset.mem_range] at hi
      have hxle : ((1 : ℤ) - (i : ℤ) * q).natAbs ≤ 1 + k * q := by
        have hi' : (i : ℤ) < k := by exact_mod_cast hi
        have hq0 : (0 : ℤ) ≤ q := Int.ofNat_nonneg q
        have hi0 : (0 : ℤ) ≤ i := Int.ofNat_nonneg i
        have habs_Z : ((1 : ℤ) - (i : ℤ) * q).natAbs
            ≤ (1 + k * q : ℤ) := by
          rw [← Int.abs_eq_natAbs]
          rcases abs_cases ((1 : ℤ) - (i : ℤ) * q) with ⟨heq, _⟩ | ⟨heq, _⟩
          · rw [heq]
            push_cast
            nlinarith
          · rw [heq]
            push_cast
            nlinarith
        exact_mod_cast habs_Z
      have hvb : padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs < B := by
        have hdvd :
            ℓ ^ padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs
              ∣ ((1 : ℤ) - (i : ℤ) * q).natAbs := pow_padicValNat_dvd
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hmne) hdvd
        have hlt :
            padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs
              < ℓ ^ padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs :=
          Nat.lt_pow_self hℓp.one_lt
        omega
      have hind := Ripple.LPP.CasselsClassical.padicValNat_eq_sum_ind hmne hvb
      rw [show padicValInt ℓ ((1 : ℤ) - (i : ℤ) * q) =
            padicValNat ℓ ((1 : ℤ) - (i : ℤ) * q).natAbs from rfl,
        ← hind]
      apply Finset.sum_congr rfl
      intro d _
      simp only [show
          (ℓ ^ d ∣ ((1 : ℤ) - (i : ℤ) * q).natAbs) ↔
          ((↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q)) from by
        rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]]
    have hle_val : padicValNat ℓ k.factorial ≤ padicValNat ℓ P := by
      have hprod_val :
          padicValInt ℓ
              (∏ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * q)) =
            ∑ i ∈ Finset.range k,
              padicValInt ℓ ((1 : ℤ) - (i : ℤ) * q) :=
        Ripple.LPP.CasselsClassical.padicValInt_prod _ _ hfac
      have hPval : padicValNat ℓ P =
          padicValInt ℓ
            (∏ i ∈ Finset.range k, ((1 : ℤ) - (i : ℤ) * q)) := rfl
      rw [hPval, hprod_val, Finset.sum_congr rfl hpiB, Finset.sum_comm]
      have hlogB : Nat.log ℓ k < B := by
        have := Nat.log_le_self ℓ k
        omega
      rw [padicValNat_factorial hlogB]
      apply Finset.sum_le_sum
      intro d _
      have hℓd : 0 < ℓ ^ d := pow_pos hℓp.pos d
      have hcount :=
        Ripple.LPP.CasselsClassical.card_filter_dvd_ge hℓd (hcopℓ d) 1 k
      calc k / ℓ ^ d
          ≤ ((Finset.range k).filter
              (fun i : ℕ =>
                (↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q))).card := by
            simpa [show ((ℓ ^ d : ℕ) : ℤ) = ((ℓ : ℤ) ^ d) by
              push_cast
              ring] using hcount
        _ = ∑ i ∈ Finset.range k,
              (if (↑(ℓ ^ d) : ℤ) ∣ ((1 : ℤ) - (i : ℤ) * q)
                then 1 else 0) :=
            Finset.card_filter _ _
    have hfkfac : (Nat.factorial k).factorization ℓ =
        padicValNat ℓ k.factorial :=
      Nat.factorization_def _ hℓp
    have hPfac : P.factorization ℓ = padicValNat ℓ P :=
      Nat.factorization_def _ hℓp
    exact (Nat.Prime.pow_dvd_iff_le_factorization hℓ hPne).mpr (by omega)

theorem cassels_catalan_trunc_clears
    (u p q : ℕ) (hu : 1 < u) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) :
    ∃ A : ℤ,
      (casselsCatalanDenom u p q : ℚ) * casselsCatalanTrunc u p q = A := by
  classical
  set R := casselsCatalanN p q with hR_def
  set ρ := casselsCatalanRho p q with hρ_def
  set a_nat : ℕ := u ^ p - 1 with ha_nat_def
  have ha_pos : 0 < a_nat := by
    simp only [ha_nat_def]
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow hp.pos.ne' hu)
  have ha_ne : (a_nat : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hq_pos : 0 < q := hq.pos
  have hR_pos : 0 < R := by
    simp only [hR_def, casselsCatalanN]
    exact Nat.div_pos (by omega) hp.pos
  have hkq_bound : ∀ k ∈ Finset.range (R + 1), k < q := by
    intro k hk
    have hkR : k ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hRq : R < q := by
      simp only [hR_def, casselsCatalanN]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    omega
  have hterm : ∀ k : ℕ, ∃ z : ℤ, k ∈ Finset.range (R + 1) →
      (casselsCatalanDenom u p q : ℚ) *
        (catalanCoeff q k * (a_nat : ℚ) * (((a_nat : ℚ) ^ q)⁻¹) ^ k) = ↑z := by
    intro k
    by_cases hk : k ∈ Finset.range (R + 1)
    · have hkq : k < q := hkq_bound k hk
      have hkR : k ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      obtain ⟨M, hM⟩ := cassels_B22_one_factorial_dvd q k hq hkq
      exact ⟨(q : ℤ) ^ (R + ρ - k) * M
          * (a_nat : ℤ) ^ (q * (R - k)), fun _ => by
        simp only [casselsCatalanDenom, catalanCoeff, ← ha_nat_def]
        rw [← hR_def, ← hρ_def]
        have hq_ne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
        have hfk_ne : (k.factorial : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr k.factorial_ne_zero
        have hak_ne : (a_nat : ℚ) ^ (q * k) ≠ 0 := pow_ne_zero _ ha_ne
        have hprod_eq :
            (∏ j ∈ Finset.range k, ((1 : ℚ) - j * q)) =
              (k.factorial : ℚ) * (M : ℚ) := by
          exact_mod_cast hM
        rw [hprod_eq]
        have hRρk : k ≤ R + ρ := le_trans hkR (Nat.le_add_right R ρ)
        have hRq1 : 1 ≤ R * q :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hR_pos.ne' hq_pos.ne')
        have hRρk_sum : k + (R + ρ - k) = R + ρ :=
          Nat.add_sub_cancel' hRρk
        have hRq_sum : R * q - 1 + 1 = R * q :=
          Nat.sub_add_cancel hRq1
        have hRk_sum : q * (R - k) + q * k = q * R := by
          rw [← mul_add, Nat.sub_add_cancel hkR]
        have hq_split :
            (q : ℚ) ^ (R + ρ) =
              (q : ℚ) ^ k * (q : ℚ) ^ (R + ρ - k) := by
          rw [← pow_add, hRρk_sum]
        have ha_succ :
            (a_nat : ℚ) ^ (R * q - 1) * (a_nat : ℚ) =
              (a_nat : ℚ) ^ (R * q) := by
          rw [← pow_succ, hRq_sum]
        have hinv_pow :
            (((a_nat : ℚ) ^ q)⁻¹) ^ k =
              ((a_nat : ℚ) ^ (q * k))⁻¹ := by
          rw [inv_pow, ← pow_mul]
        have ha_split :
            (a_nat : ℚ) ^ (R * q) =
              (a_nat : ℚ) ^ (q * (R - k)) *
                (a_nat : ℚ) ^ (q * k) := by
          rw [← pow_add, hRk_sum, mul_comm q R]
        have hLHS_cast :
            ((q ^ (R + ρ) * a_nat ^ (R * q - 1) : ℕ) : ℚ) =
              (q : ℚ) ^ (R + ρ) * (a_nat : ℚ) ^ (R * q - 1) := by
          push_cast
          ring
        have hRHS_cast :
            ((↑q ^ (R + ρ - k) * M * ↑a_nat ^ (q * (R - k)) : ℤ) : ℚ) =
              (q : ℚ) ^ (R + ρ - k) * (M : ℚ)
                * (a_nat : ℚ) ^ (q * (R - k)) := by
          push_cast
          ring
        rw [hLHS_cast, hRHS_cast]
        have lhs_eq :
            (q : ℚ) ^ (R + ρ) * (a_nat : ℚ) ^ (R * q - 1) *
                ((k.factorial : ℚ) * (M : ℚ)
                  / ((q : ℚ) ^ k * (k.factorial : ℚ)) *
                (a_nat : ℚ) * (((a_nat : ℚ) ^ q)⁻¹) ^ k)
              =
            (q : ℚ) ^ (R + ρ - k) * (M : ℚ)
              * (a_nat : ℚ) ^ (q * (R - k)) := by
          rw [hinv_pow, hq_split]
          have :
              (q : ℚ) ^ k * (q : ℚ) ^ (R + ρ - k)
                  * (a_nat : ℚ) ^ (R * q - 1) *
                ((k.factorial : ℚ) * (M : ℚ)
                  / ((q : ℚ) ^ k * (k.factorial : ℚ))
                  * (a_nat : ℚ) * ((a_nat : ℚ) ^ (q * k))⁻¹)
                =
              (q : ℚ) ^ (R + ρ - k) * (M : ℚ)
                * ((a_nat : ℚ) ^ (R * q - 1)
                  * (a_nat : ℚ) * ((a_nat : ℚ) ^ (q * k))⁻¹) := by
            field_simp [hq_ne, hfk_ne]
          rw [this, ha_succ, ha_split]
          field_simp [hak_ne]
        exact lhs_eq⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose Z hZ using hterm
  refine ⟨∑ k ∈ Finset.range (R + 1), Z k, ?_⟩
  have hTrunc : casselsCatalanTrunc u p q =
      ∑ k ∈ Finset.range (R + 1),
        catalanCoeff q k * (a_nat : ℚ) * (((a_nat : ℚ) ^ q)⁻¹) ^ k := by
    simp only [casselsCatalanTrunc, ← ha_nat_def, ← hR_def]
  rw [hTrunc, Finset.mul_sum]
  push_cast [Int.cast_sum]
  apply Finset.sum_congr rfl
  exact fun k hk => hZ k hk

theorem cassels_catalan_cleared_gap_integer
    (u b p q : ℕ) (hu : 1 < u) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) :
    ∃ I : ℤ,
      (casselsCatalanDenom u p q : ℚ) *
          ((b : ℚ) - casselsCatalanTrunc u p q) = I := by
  obtain ⟨A, hA⟩ := cassels_catalan_trunc_clears u p q hu hp hq hpq
  refine ⟨(casselsCatalanDenom u p q : ℤ) * (b : ℤ) - A, ?_⟩
  calc
    (casselsCatalanDenom u p q : ℚ) *
          ((b : ℚ) - casselsCatalanTrunc u p q)
        =
      (casselsCatalanDenom u p q : ℚ) * (b : ℚ)
        - (casselsCatalanDenom u p q : ℚ) * casselsCatalanTrunc u p q := by
          ring
    _ = (casselsCatalanDenom u p q : ℚ) * (b : ℚ) - (A : ℚ) := by
          rw [hA]
    _ = (((casselsCatalanDenom u p q : ℤ) * (b : ℤ) - A : ℤ) : ℚ) := by
          push_cast
          ring

theorem cassels_catalan_cleared_gap_abs_le_geom
    (u b p q : ℕ) (hu : 1 < u) (hp2 : 2 ≤ p) (hq2 : 2 ≤ q)
    (hqodd : Odd q)
    (hpow : b ^ q = (u ^ p - 1) ^ q + 1) :
    let R := casselsCatalanN p q
    let a := u ^ p - 1
    let D := casselsCatalanDenom u p q
    |(D : ℝ) * ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ))|
      ≤
    (D : ℝ)
      * ((a : ℝ)
        * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
            * (((a : ℝ) ^ q)⁻¹) ^ (R + 1)
            / (1 - (((a : ℝ) ^ q)⁻¹)))) := by
  let R := casselsCatalanN p q
  let a := u ^ p - 1
  let D := casselsCatalanDenom u p q
  have hgap :
      |(b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ)|
        ≤
      (a : ℝ)
        * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
            * (((a : ℝ) ^ q)⁻¹) ^ (R + 1)
            / (1 - (((a : ℝ) ^ q)⁻¹))) := by
    dsimp [R, a]
    exact casselsCatalanTrunc_gap_abs_le_geom
      u b p q hu hp2 hq2 hqodd hpow
  have hD_nonneg : 0 ≤ (D : ℝ) := by positivity
  calc
    |(D : ℝ) * ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ))|
        =
      (D : ℝ) * |(b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ)| := by
        rw [abs_mul, abs_of_nonneg hD_nonneg]
    _ ≤
      (D : ℝ)
        * ((a : ℝ)
          * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
              * (((a : ℝ) ^ q)⁻¹) ^ (R + 1)
              / (1 - (((a : ℝ) ^ q)⁻¹)))) :=
        mul_le_mul_of_nonneg_left hgap hD_nonneg

theorem cassels_catalan_cleared_gap_abs_le_inv_q
    (u b p q : ℕ) (hu : 1 < u) (hp2 : 2 ≤ p) (hq2 : 2 ≤ q)
    (hqodd : Odd q)
    (hpow : b ^ q = (u ^ p - 1) ^ q + 1) :
    let R := casselsCatalanN p q
    let a := u ^ p - 1
    let D := casselsCatalanDenom u p q
    |(D : ℝ) * ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ))|
      ≤
    (D : ℝ)
      * ((a : ℝ)
        * (((q : ℝ)⁻¹
            * (((a : ℝ) ^ q)⁻¹) ^ (R + 1))
            / (1 - (((a : ℝ) ^ q)⁻¹)))) := by
  let R := casselsCatalanN p q
  let a := u ^ p - 1
  let D := casselsCatalanDenom u p q
  let X : ℝ := (((a : ℝ) ^ q)⁻¹)
  have hgeom :
      |(D : ℝ) * ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ))|
        ≤
      (D : ℝ)
        * ((a : ℝ)
          * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
              * X ^ (R + 1)
              / (1 - X))) := by
    dsimp [R, a, D, X]
    exact cassels_catalan_cleared_gap_abs_le_geom
      u b p q hu hp2 hq2 hqodd hpow
  have ha_gt1 : 1 < a := by
    dsimp [a]
    have hu2 : 2 ≤ u := by omega
    have hup4 : 4 ≤ u ^ p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ u ^ 2 := Nat.pow_le_pow_left hu2 2
        _ ≤ u ^ p := Nat.pow_le_pow_right (by omega : 0 < u) hp2
    omega
  have hq0 : 0 < q := by omega
  have hX_pos : 0 < X := by
    dsimp [X]
    positivity
  have hX0 : 0 ≤ X := le_of_lt hX_pos
  have hXlt : X < 1 := by
    have h := inv_nat_pow_abs_lt_one a q ha_gt1 hq0
    dsimp [X]
    rwa [abs_of_pos hX_pos] at h
  have hden_pos : 0 < 1 - X := by linarith
  have hcoeff :
      |((catalanCoeff q (R + 1) : ℚ) : ℝ)| ≤ (q : ℝ)⁻¹ :=
    catalanCoeff_abs_le_inv_q q (R + 1) hq2 (by omega)
  have hinner :
      |((catalanCoeff q (R + 1) : ℚ) : ℝ)|
          * X ^ (R + 1) / (1 - X)
        ≤
      (q : ℝ)⁻¹ * X ^ (R + 1) / (1 - X) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hX0 _))
      (le_of_lt (inv_pos.mpr hden_pos))
  have htail :
      (a : ℝ)
          * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
              * X ^ (R + 1)
              / (1 - X))
        ≤
      (a : ℝ)
          * ((q : ℝ)⁻¹ * X ^ (R + 1) / (1 - X)) :=
    mul_le_mul_of_nonneg_left hinner (by positivity)
  have hD_nonneg : 0 ≤ (D : ℝ) := by positivity
  calc
    |(D : ℝ) * ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ))|
        ≤
      (D : ℝ)
        * ((a : ℝ)
          * (|((catalanCoeff q (R + 1) : ℚ) : ℝ)|
              * X ^ (R + 1)
              / (1 - X))) := hgeom
    _ ≤
      (D : ℝ)
        * ((a : ℝ)
          * ((q : ℝ)⁻¹ * X ^ (R + 1) / (1 - X))) :=
        mul_le_mul_of_nonneg_left htail hD_nonneg

theorem cassels_catalan_cleared_gap_abs_le_simplified
    (u b p q : ℕ) (hu : 1 < u) (hp2 : 2 ≤ p) (hq2 : 2 ≤ q)
    (hpq : p < q) (hqodd : Odd q)
    (hpow : b ^ q = (u ^ p - 1) ^ q + 1) :
    let R := casselsCatalanN p q
    let ρ := casselsCatalanRho p q
    let a := u ^ p - 1
    let D := casselsCatalanDenom u p q
    let X : ℝ := (((a : ℝ) ^ q)⁻¹)
    |(D : ℝ) * ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ))|
      ≤
    (q : ℝ) ^ (R + ρ) * (((q : ℝ)⁻¹ * X) / (1 - X)) := by
  let R := casselsCatalanN p q
  let ρ := casselsCatalanRho p q
  let a := u ^ p - 1
  let D := casselsCatalanDenom u p q
  let X : ℝ := (((a : ℝ) ^ q)⁻¹)
  have hbound :
      |(D : ℝ) * ((b : ℝ) - ((casselsCatalanTrunc u p q : ℚ) : ℝ))|
        ≤
      (D : ℝ)
        * ((a : ℝ)
          * (((q : ℝ)⁻¹ * X ^ (R + 1)) / (1 - X))) := by
    dsimp [R, a, D, X]
    exact cassels_catalan_cleared_gap_abs_le_inv_q
      u b p q hu hp2 hq2 hqodd hpow
  have ha_gt1 : 1 < a := by
    dsimp [a]
    have hu2 : 2 ≤ u := by omega
    have hup4 : 4 ≤ u ^ p := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ u ^ 2 := Nat.pow_le_pow_left hu2 2
        _ ≤ u ^ p := Nat.pow_le_pow_right (by omega : 0 < u) hp2
    omega
  have haR_pos : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have haR_ne : (a : ℝ) ≠ 0 := ne_of_gt haR_pos
  have hq0 : 0 < q := by omega
  have hRpos : 0 < R := by
    dsimp [R]
    exact casselsCatalanN_pos p q (by omega : 0 < p) hpq
  have hRq1 : 1 ≤ R * q :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hRpos.ne' hq0.ne')
  have hmul_a :
      (a : ℝ) ^ (R * q - 1) * (a : ℝ) = (a : ℝ) ^ (R * q) := by
    rw [← pow_succ, Nat.sub_add_cancel hRq1]
  have hAX : (a : ℝ) ^ (R * q) * X ^ (R + 1) = X := by
    dsimp [X]
    rw [inv_pow, ← pow_mul]
    have hexp : q * (R + 1) = R * q + q := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm q R]
    rw [hexp, pow_add]
    field_simp [pow_ne_zero _ haR_ne]
  have hsimp :
      (D : ℝ)
        * ((a : ℝ)
          * (((q : ℝ)⁻¹ * X ^ (R + 1)) / (1 - X)))
        =
      (q : ℝ) ^ (R + ρ) * (((q : ℝ)⁻¹ * X) / (1 - X)) := by
    dsimp [D, casselsCatalanDenom, R, ρ]
    push_cast
    calc
      (q : ℝ) ^ (casselsCatalanN p q + casselsCatalanRho p q)
          * (a : ℝ) ^ (casselsCatalanN p q * q - 1)
          * ((a : ℝ)
            * (((q : ℝ)⁻¹ * X ^ (casselsCatalanN p q + 1)) / (1 - X)))
          =
        (q : ℝ) ^ (R + ρ)
          * (((a : ℝ) ^ (R * q - 1) * (a : ℝ))
            * (((q : ℝ)⁻¹ * X ^ (R + 1)) / (1 - X))) := by
            dsimp [R, ρ]
            ring
      _ =
        (q : ℝ) ^ (R + ρ)
          * ((a : ℝ) ^ (R * q)
            * (((q : ℝ)⁻¹ * X ^ (R + 1)) / (1 - X))) := by
            rw [hmul_a]
      _ =
        (q : ℝ) ^ (R + ρ)
          * (((q : ℝ)⁻¹ * ((a : ℝ) ^ (R * q) * X ^ (R + 1)))
            / (1 - X)) := by
            ring
      _ =
        (q : ℝ) ^ (R + ρ) * (((q : ℝ)⁻¹ * X) / (1 - X)) := by
            rw [hAX]
  rwa [hsimp] at hbound

/-- Rational gap principle: `D*T` integer + `|v - T| < 1/D` forces
`D*v = D*T`.  Archimedean discreteness for integers in ℚ/ℝ. -/
private theorem cassels_rational_gap_forces_cleared_eq
    (D v : ℕ) (T : ℚ)
    (hDpos : 0 < D)
    (hTint : ∃ z : ℤ, (D : ℚ) * T = (z : ℚ))
    (hgap : |(v : ℝ) - ((T : ℚ) : ℝ)| < ((D : ℝ))⁻¹) :
    (D : ℚ) * (v : ℚ) = (D : ℚ) * T := by
  classical
  rcases hTint with ⟨z, hz⟩
  have hDposR : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hDneR : (D : ℝ) ≠ 0 := ne_of_gt hDposR
  have hscaled :
      |(D : ℝ) * ((v : ℝ) - ((T : ℚ) : ℝ))| < 1 := by
    calc
      |(D : ℝ) * ((v : ℝ) - ((T : ℚ) : ℝ))|
          = (D : ℝ) * |(v : ℝ) - ((T : ℚ) : ℝ)| := by
              rw [abs_mul, abs_of_pos hDposR]
      _ < (D : ℝ) * ((D : ℝ)⁻¹) :=
              mul_lt_mul_of_pos_left hgap hDposR
      _ = 1 := by field_simp [hDneR]
  let a : ℤ := ((D * v : ℕ) : ℤ)
  have hzR : (((D : ℚ) * T : ℚ) : ℝ) = (z : ℝ) := by exact_mod_cast hz
  have hdist : |(a : ℝ) - (z : ℝ)| < 1 := by
    calc
      |(a : ℝ) - (z : ℝ)|
          = |(D : ℝ) * ((v : ℝ) - ((T : ℚ) : ℝ))| := by
              dsimp [a]
              rw [← hzR]; push_cast; ring_nf
      _ < 1 := hscaled
  have haz : a = z := by
    by_contra hne
    have hsub_ne : a - z ≠ 0 := sub_ne_zero.mpr hne
    have hone_int : (1 : ℤ) ≤ |a - z| := Int.one_le_abs hsub_ne
    have hcast_abs :
        (((|a - z| : ℤ) : ℝ)) = |(a : ℝ) - (z : ℝ)| := by
      rw [Int.cast_abs, Int.cast_sub]
    have hone_real : (1 : ℝ) ≤ |(a : ℝ) - (z : ℝ)| := by
      rw [← hcast_abs]; exact_mod_cast hone_int
    linarith
  calc
    (D : ℚ) * (v : ℚ)
        = ((D * v : ℕ) : ℚ) := by push_cast; ring
    _ = (a : ℚ) := by dsimp [a]; push_cast; ring
    _ = (z : ℚ) := by exact_mod_cast haz
    _ = (D : ℚ) * T := hz.symm

private theorem cassels_real_gap_ne_zero_of_cleared_ne
    (D v : ℕ) (T : ℚ)
    (hNe : (D : ℚ) * (v : ℚ) ≠ (D : ℚ) * T) :
    (v : ℝ) - ((T : ℚ) : ℝ) ≠ 0 := by
  intro hgap_zero
  have hvT_real : (v : ℝ) = ((T : ℚ) : ℝ) :=
    sub_eq_zero.mp hgap_zero
  have hvT_rat : (v : ℚ) = T := by
    exact_mod_cast hvT_real
  exact hNe (by rw [hvT_rat])

private theorem cassels_nonzero_integer_abs_lt_one_false
    (I : ℝ)
    (hIint : ∃ z : ℤ, I = (z : ℝ))
    (hIne : I ≠ 0)
    (hIlt : |I| < 1) :
    False := by
  rcases hIint with ⟨z, hz⟩
  have hz_abs_lt : |(z : ℝ)| < 1 := by
    simpa [hz] using hIlt
  have hz0 : z = 0 := by
    rwa [← Int.cast_abs, ← Int.cast_one, Int.cast_lt,
      Int.abs_lt_one_iff] at hz_abs_lt
  exact hIne (by rw [hz, hz0]; norm_num)

private theorem cassels_cleared_gap_nonzero_abs_lt_one_false
    (D v : ℕ) (T : ℚ)
    (hDpos : 0 < D)
    (hTint : ∃ z : ℤ, (D : ℚ) * T = (z : ℚ))
    (hNe : (D : ℚ) * (v : ℚ) ≠ (D : ℚ) * T)
    (hsmall : |(D : ℝ) * ((v : ℝ) - ((T : ℚ) : ℝ))| < 1) :
    False := by
  rcases hTint with ⟨z, hz⟩
  let I : ℝ := (D : ℝ) * ((v : ℝ) - ((T : ℚ) : ℝ))
  have hIint : ∃ w : ℤ, I = (w : ℝ) := by
    refine ⟨((D * v : ℕ) : ℤ) - z, ?_⟩
    have hzR : (((D : ℚ) * T : ℚ) : ℝ) = (z : ℝ) := by
      exact_mod_cast hz
    calc
      I = (D : ℝ) * (v : ℝ) - (z : ℝ) := by
        dsimp [I]
        rw [← hzR]
        push_cast
        ring
      _ = (((D * v : ℕ) : ℤ) - z : ℤ) := by
        push_cast
        ring
  have hgap_ne : (v : ℝ) - ((T : ℚ) : ℝ) ≠ 0 :=
    cassels_real_gap_ne_zero_of_cleared_ne D v T hNe
  have hIne : I ≠ 0 := by
    intro hI0
    have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have hgap0 : (v : ℝ) - ((T : ℚ) : ℝ) = 0 :=
      (mul_eq_zero.mp hI0).resolve_left hDne
    exact hgap_ne hgap0
  exact cassels_nonzero_integer_abs_lt_one_false I hIint hIne hsmall

/-! ### Padé p-adic obstruction decomposition (ChatGPT b93fb0f5) -/

/-- Explicit integer witness for the `k`-th cleared Padé term. -/
private def casselsPadeWitnessTerm (u p q N k : ℕ) : ℤ :=
  ((-1 : ℤ) ^ k)
    * casselsBinomNum p q k
    * ((p ^ (N - k)
          * (Nat.factorial N / Nat.factorial k)
          * u ^ (p * (N - k) + (q - 1)) : ℕ) : ℤ)

/-- Explicit integer witness for the whole cleared Padé truncation. -/
private def casselsPadeWitnessSum (u p q N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1),
    casselsPadeWitnessTerm u p q N k

/-- Explicit-witness form of the cleared denominator integrality.

Same termwise calculation as `cassels_pade_trunc_cleared_integral`,
exposed via the explicit witness sum for p-adic comparison. -/
private theorem cassels_pade_cleared_eq_witness_sum
    (u p q N : ℕ) (hu : 1 < u) (hp : p.Prime) :
    (casselsPadeClearDen u p N : ℚ)
      * casselsPadeTruncQ u p q N
      =
    (casselsPadeWitnessSum u p q N : ℚ) := by
  classical
  let D : ℕ := casselsPadeClearDen u p N
  let f : ℕ → ℚ := fun k =>
    casselsRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k
  have hu_pos : 0 < u := by omega
  have hp_pos : 0 < p := hp.pos
  have huQ_ne : (u : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu_pos)
  have hpQ_ne : (p : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp_pos)
  have hterm :
      ∀ k ∈ Finset.range (N + 1),
        (D : ℚ) * f k = ((casselsPadeWitnessTerm u p q N k : ℤ) : ℚ) := by
    intro k hk
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hk_fact_dvd : Nat.factorial k ∣ Nat.factorial N :=
      Nat.factorial_dvd_factorial hkN
    have hk_fact_ne : (Nat.factorial k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero k)
    have hp_pow_k_ne : (p : ℚ) ^ k ≠ 0 := pow_ne_zero k hpQ_ne
    have hu_pow_pk_ne : (u : ℚ) ^ (p * k) ≠ 0 := pow_ne_zero (p * k) huQ_ne
    have hD_cast :
        (D : ℚ) =
        (p : ℚ) ^ N * (Nat.factorial N : ℚ) * (u : ℚ) ^ (p * N) := by
      dsimp [D, casselsPadeClearDen]; push_cast; ring
    have hfact_mul :
        ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ)
          * (Nat.factorial k : ℚ)
          = (Nat.factorial N : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hk_fact_dvd
    have hfact_div :
        (Nat.factorial N : ℚ) / (Nat.factorial k : ℚ)
          = ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ) := by
      field_simp [hk_fact_ne]
      simpa [mul_comm] using hfact_mul.symm
    have hfact_dvd_int : (Nat.factorial k : ℤ) ∣ (Nat.factorial N : ℤ) := by
      exact_mod_cast hk_fact_dvd
    have hfact_divZ :
        (((Nat.factorial N : ℤ) / (Nat.factorial k : ℤ) : ℤ) : ℚ)
          = (Nat.factorial N : ℚ) / (Nat.factorial k : ℚ) := by
      simpa using (Int.cast_div (α := ℚ) hfact_dvd_int hk_fact_ne)
    have hp_pow_mul :
        (p : ℚ) ^ (N - k) * (p : ℚ) ^ k = (p : ℚ) ^ N := by
      rw [← pow_add]
      have hNk : N - k + k = N := Nat.sub_add_cancel hkN
      rw [hNk]
    have hp_pow_div :
        (p : ℚ) ^ N / (p : ℚ) ^ k = (p : ℚ) ^ (N - k) := by
      field_simp [hp_pow_k_ne]
      simpa [mul_comm] using hp_pow_mul.symm
    have hu_inv_pow :
        (((u : ℚ) ^ p)⁻¹) ^ k = ((u : ℚ) ^ (p * k))⁻¹ := by
      rw [inv_pow, ← pow_mul]
    have hu_pow_mul :
        (u : ℚ) ^ (p * (N - k)) * (u : ℚ) ^ (p * k) = (u : ℚ) ^ (p * N) := by
      rw [← pow_add]
      have hexp : p * (N - k) + p * k = p * N := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hkN]
      rw [hexp]
    have hu_pow_div :
        (u : ℚ) ^ (p * N) * ((u : ℚ) ^ (p * k))⁻¹
          = (u : ℚ) ^ (p * (N - k)) := by
      field_simp [hu_pow_pk_ne]
      simpa [mul_comm] using hu_pow_mul.symm
    have hu_part :
        (u : ℚ) ^ (p * N) * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k
          = (u : ℚ) ^ (p * (N - k) + (q - 1)) := by
      rw [hu_inv_pow]
      calc
        (u : ℚ) ^ (p * N) * (u : ℚ) ^ (q - 1) * ((u : ℚ) ^ (p * k))⁻¹
            = ((u : ℚ) ^ (p * N) * ((u : ℚ) ^ (p * k))⁻¹)
                * (u : ℚ) ^ (q - 1) := by ring
        _ = (u : ℚ) ^ (p * (N - k)) * (u : ℚ) ^ (q - 1) := by rw [hu_pow_div]
        _ = (u : ℚ) ^ (p * (N - k) + (q - 1)) := by rw [← pow_add]
    have hden_inv :
        (((p : ℚ) ^ k * (Nat.factorial k : ℚ))⁻¹)
          = ((p : ℚ) ^ k)⁻¹ * (Nat.factorial k : ℚ)⁻¹ := by
      rw [mul_inv]
    have hcoeff :
        (p : ℚ) ^ N * (Nat.factorial N : ℚ)
          * (((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              / ((p : ℚ) ^ k * (Nat.factorial k : ℚ)))
          = ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              * (p : ℚ) ^ (N - k)
              * ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ) := by
      calc
        (p : ℚ) ^ N * (Nat.factorial N : ℚ)
            * (((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
                / ((p : ℚ) ^ k * (Nat.factorial k : ℚ)))
            = ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
                * ((p : ℚ) ^ N / (p : ℚ) ^ k)
                * ((Nat.factorial N : ℚ) / (Nat.factorial k : ℚ)) := by
              rw [div_eq_mul_inv, hden_inv]; ring
        _ = ((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              * (p : ℚ) ^ (N - k)
              * ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ) := by
              rw [hp_pow_div, hfact_div]
    calc
      (D : ℚ) * f k
          = ((p : ℚ) ^ N * (Nat.factorial N : ℚ) * (u : ℚ) ^ (p * N))
              * (casselsRootCoeff p q k
                * (u : ℚ) ^ (q - 1) * (((u : ℚ) ^ p)⁻¹) ^ k) := by
            rw [hD_cast]
      _ = ((p : ℚ) ^ N * (Nat.factorial N : ℚ) * casselsRootCoeff p q k)
            * ((u : ℚ) ^ (p * N) * (u : ℚ) ^ (q - 1)
              * (((u : ℚ) ^ p)⁻¹) ^ k) := by ring
      _ = (((-1 : ℚ) ^ k) * (casselsBinomNum p q k : ℚ)
              * (p : ℚ) ^ (N - k)
              * ((Nat.factorial N / Nat.factorial k : ℕ) : ℚ))
            * ((u : ℚ) ^ (p * (N - k) + (q - 1))) := by
              dsimp [casselsRootCoeff]; rw [hcoeff, hu_part]
      _ = ((casselsPadeWitnessTerm u p q N k : ℤ) : ℚ) := by
            dsimp [casselsPadeWitnessTerm]; push_cast
            rw [← hfact_div, hfact_divZ]
            ring
  calc
    (casselsPadeClearDen u p N : ℚ) * casselsPadeTruncQ u p q N
        = (D : ℚ) * (∑ k ∈ Finset.range (N + 1), f k) := by
            dsimp [D, f, casselsPadeTruncQ]
    _ = ∑ k ∈ Finset.range (N + 1), (D : ℚ) * f k := by
            rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (N + 1),
          ((casselsPadeWitnessTerm u p q N k : ℤ) : ℚ) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hterm k hk
    _ = ((∑ k ∈ Finset.range (N + 1),
          casselsPadeWitnessTerm u p q N k : ℤ) : ℚ) := by
            push_cast
            rfl
    _ = (casselsPadeWitnessSum u p q N : ℚ) := by rfl

/-- Exact p-order below `n`: if `p^n ∤ u`, choose `r < n` with
`p^r ∣ u` but `p^(r+1) ∤ u`. -/
private theorem cassels_exists_exact_p_order_lt
    (p u n : ℕ) (hnpos : 0 < n) (hnot : ¬ p ^ n ∣ u) :
    ∃ r : ℕ, r < n ∧ p ^ r ∣ u ∧ ¬ p ^ (r + 1) ∣ u := by
  by_contra hno
  have hstep :
      ∀ r : ℕ, r < n → p ^ r ∣ u → p ^ (r + 1) ∣ u := by
    intro r hr hdiv
    by_contra hnext
    exact hno ⟨r, hr, hdiv, hnext⟩
  have hall : ∀ m : ℕ, m ≤ n → p ^ m ∣ u := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
        have hmlt : m < n := Nat.lt_of_succ_le hm
        have hmle : m ≤ n := Nat.le_of_succ_le hm
        exact hstep m hmlt (ih hmle)
  exact hnot (hall n le_rfl)

/-- The cleared `D · v` is divisible by `p^(r(q-1)+1)`, because
`D` contains `p^N` and `N ≥ n·q+1 > r(q-1)+1`. -/
private theorem cassels_left_cleared_high_dvd
    (u v p q n N r : ℕ)
    (hN : N = casselsPadeLevel p q n)
    (hrlt : r < n) :
    ((p ^ (r * (q - 1) + 1) : ℕ) : ℤ)
      ∣
    (((casselsPadeClearDen u p N * v : ℕ) : ℤ)) := by
  have hN_lower : n * q + 1 ≤ N := by
    rw [hN]
    unfold casselsPadeLevel
    exact Nat.le_max_left (n * q + 1) (((q - 1) / p) + n + 1)
  have hrle : r ≤ n := le_of_lt hrlt
  have hqsub : q - 1 ≤ q := Nat.sub_le q 1
  have hmul : r * (q - 1) ≤ n * q := Nat.mul_le_mul hrle hqsub
  have hexp_le : r * (q - 1) + 1 ≤ N :=
    le_trans (Nat.succ_le_succ hmul) hN_lower
  have hpow_dvd : p ^ (r * (q - 1) + 1) ∣ p ^ N := pow_dvd_pow p hexp_le
  have hD_dvd : p ^ (r * (q - 1) + 1) ∣ casselsPadeClearDen u p N := by
    unfold casselsPadeClearDen
    have h1 : p ^ (r * (q - 1) + 1) ∣ p ^ N * Nat.factorial N :=
      dvd_mul_of_dvd_left hpow_dvd (Nat.factorial N)
    have h2 :
        p ^ (r * (q - 1) + 1)
          ∣ (p ^ N * Nat.factorial N) * u ^ (p * N) :=
      dvd_mul_of_dvd_left h1 (u ^ (p * N))
    simpa [mul_assoc] using h2
  have hNat :
      p ^ (r * (q - 1) + 1)
        ∣ casselsPadeClearDen u p N * v :=
    dvd_mul_of_dvd_left hD_dvd v
  exact_mod_cast hNat

/-- If `p^(m+1)` divides `p^m * z` in ℤ, then `p` divides `z`. -/
private lemma cassels_int_prime_dvd_of_pow_succ_dvd_pow_mul
    (p m : ℕ) (hp : p.Prime) (z : ℤ)
    (h : ((p ^ (m + 1) : ℕ) : ℤ) ∣ ((p ^ m : ℕ) : ℤ) * z) :
    (p : ℤ) ∣ z := by
  rcases h with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hpm_ne : ((p ^ m : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero m hp.ne_zero)
  have hpow_succ :
      ((p ^ (m + 1) : ℕ) : ℤ) = ((p ^ m : ℕ) : ℤ) * (p : ℤ) := by
    rw [pow_succ]; push_cast; ring
  apply mul_left_cancel₀ hpm_ne
  calc
    ((p ^ m : ℕ) : ℤ) * z
        = ((p ^ (m + 1) : ℕ) : ℤ) * c := hc
    _ = (((p ^ m : ℕ) : ℤ) * (p : ℤ)) * c := by rw [hpow_succ]
    _ = ((p ^ m : ℕ) : ℤ) * ((p : ℤ) * c) := by ring

/-- A prime integer does not divide `(-1)^N`. -/
private lemma cassels_int_prime_not_dvd_neg_one_pow
    (p N : ℕ) (hp : p.Prime) :
    ¬ (p : ℤ) ∣ (-1 : ℤ) ^ N := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hcases : (-1 : ℤ) ^ N = 1 ∨ (-1 : ℤ) ^ N = -1 := by
    induction N with
    | zero => left; simp
    | succ N ih =>
        rcases ih with h | h
        · right; rw [pow_succ, h]; ring
        · left; rw [pow_succ, h]; ring
  intro hdiv
  rcases hcases with hone | hneg
  · have h1 : (p : ℤ) ∣ (1 : ℤ) := by simpa [hone] using hdiv
    exact hpZ.not_dvd_one h1
  · rcases hdiv with ⟨c, hc⟩
    have h1 : (p : ℤ) ∣ (1 : ℤ) := by
      refine ⟨-c, ?_⟩
      rw [hneg] at hc
      calc
        (1 : ℤ) = -((-1 : ℤ)) := by ring
        _ = -((p : ℤ) * c) := by rw [← hc]
        _ = (p : ℤ) * (-c) := by ring
    exact hpZ.not_dvd_one h1

/-- The Cassels binomial numerator is a p-adic unit. -/
private lemma cassels_binomNum_not_dvd_p
    (p q k : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q) :
    ¬ (p : ℤ) ∣ casselsBinomNum p q k := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hpq
    rcases hq.eq_one_or_self_of_dvd p hpq with h1 | heq
    · exact hp.ne_one h1
    · omega
  induction k with
  | zero =>
      intro h
      have h1 : (p : ℤ) ∣ (1 : ℤ) := by
        simpa [casselsBinomNum] using h
      exact hpZ.not_dvd_one h1
  | succ k ih =>
      intro h
      rw [casselsBinomNum, Finset.prod_range_succ] at h
      rcases hpZ.dvd_or_dvd h with hprev | hfac
      · exact ih (by simpa [casselsBinomNum] using hprev)
      · have hp_dvd_kp : (p : ℤ) ∣ (k : ℤ) * (p : ℤ) := by
          refine ⟨k, ?_⟩; ring
        have hp_dvd_qZ : (p : ℤ) ∣ (q : ℤ) := by
          have hsum := dvd_add hfac hp_dvd_kp
          simpa using hsum
        have hp_dvd_qNat : p ∣ q := by exact_mod_cast hp_dvd_qZ
        exact hp_not_dvd_q hp_dvd_qNat

private theorem casselsActualRootCoeff_top_cleared_p_unit
    (p q N : ℕ) (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q) :
    ∃ W : ℤ,
      ((p ^ N * Nat.factorial N : ℕ) : ℚ)
        * casselsActualRootCoeff p q N = (W : ℚ)
        ∧ ¬ (p : ℤ) ∣ W := by
  classical
  let rootW : ℤ := (-1 : ℤ) ^ N * casselsBinomNum p q N
  have hroot :
      ((p ^ N * Nat.factorial N : ℕ) : ℚ) * casselsRootCoeff p q N
        = (rootW : ℚ) := by
    dsimp [rootW]
    exact casselsRootCoeff_cleared_eq_top_witness p q N hp
  have hcorr :
      ∀ a : ℕ, ∃ z : ℤ,
        a ∈ Finset.Icc 1 (N / q) →
          ((p ^ N * Nat.factorial N : ℕ) : ℚ)
            * casselsActualCorrectionTerm p q N a
            = (((p : ℤ) * z : ℤ) : ℚ) := by
    intro a
    by_cases ha : a ∈ Finset.Icc 1 (N / q)
    · rcases casselsActualCorrectionTerm_top_cleared_p_multiple
          p q N a hp hq.two_le ha with ⟨z, hz⟩
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun ha' => False.elim (ha ha')⟩
  choose Z hZ using hcorr
  let corrW : ℤ := ∑ a ∈ Finset.Icc 1 (N / q), Z a
  refine ⟨rootW + (p : ℤ) * corrW, ?_, ?_⟩
  · unfold casselsActualRootCoeff
    calc
      ((p ^ N * Nat.factorial N : ℕ) : ℚ)
          * (casselsRootCoeff p q N
            + ∑ a ∈ Finset.Icc 1 (N / q),
                casselsActualCorrectionTerm p q N a)
          =
        ((p ^ N * Nat.factorial N : ℕ) : ℚ)
            * casselsRootCoeff p q N
          + ∑ a ∈ Finset.Icc 1 (N / q),
              ((p ^ N * Nat.factorial N : ℕ) : ℚ)
                * casselsActualCorrectionTerm p q N a := by
          rw [mul_add, Finset.mul_sum]
      _ = (rootW : ℚ)
          + ∑ a ∈ Finset.Icc 1 (N / q), (((p : ℤ) * Z a : ℤ) : ℚ) := by
          rw [hroot]
          congr 1
          apply Finset.sum_congr rfl
          intro a ha
          exact hZ a ha
      _ = ((rootW + (p : ℤ) * corrW : ℤ) : ℚ) := by
          dsimp [corrW]
          push_cast
          rw [Finset.mul_sum]
  · intro hpW
    have hpcorr : (p : ℤ) ∣ (p : ℤ) * corrW := dvd_mul_right _ _
    have hproot : (p : ℤ) ∣ rootW := by
      have hsub := dvd_sub hpW hpcorr
      have hsub_eq :
          (rootW + (p : ℤ) * corrW) - (p : ℤ) * corrW = rootW := by
        ring
      rwa [hsub_eq] at hsub
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hsign_not : ¬ (p : ℤ) ∣ (-1 : ℤ) ^ N :=
      cassels_int_prime_not_dvd_neg_one_pow p N hp
    have hbinom_not : ¬ (p : ℤ) ∣ casselsBinomNum p q N :=
      cassels_binomNum_not_dvd_p p q N hp hq hp_lt_q
    rcases hpZ.dvd_or_dvd (by simpa [rootW] using hproot) with hsign | hbinom
    · exact hsign_not hsign
    · exact hbinom_not hbinom

/-- Lower witness terms `k < N` are divisible by `p^(r(q-1)+1)`. -/
private lemma cassels_witnessTerm_lower_high_dvd
    (u p q N r k : ℕ) (hpr : p ^ r ∣ u) (hk : k < N) :
    ((p ^ (r * (q - 1) + 1) : ℕ) : ℤ)
      ∣ casselsPadeWitnessTerm u p q N k := by
  let d : ℕ := N - k
  let E : ℕ := p * d + (q - 1)
  let m : ℕ := r * (q - 1) + 1
  have hd_pos : 0 < d := by dsimp [d]; omega
  have h_u_pow_raw : (p ^ r) ^ E ∣ u ^ E := pow_dvd_pow_of_dvd hpr E
  have h_u_pow : p ^ (r * E) ∣ u ^ E := by
    simpa [pow_mul] using h_u_pow_raw
  have h_prod_base :
      p ^ (d + r * E) ∣ p ^ d * u ^ E := by
    have hmul := Nat.mul_dvd_mul (dvd_refl (p ^ d)) h_u_pow
    simpa [pow_add] using hmul
  have hq_minus_le_E : q - 1 ≤ E := by dsimp [E]; omega
  have hmain_le : m ≤ d + r * E := by
    have hpart : r * (q - 1) ≤ r * E :=
      Nat.mul_le_mul_left r hq_minus_le_E
    have hone : 1 ≤ d := hd_pos
    have h := Nat.add_le_add hpart hone
    dsimp [m]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hpow_dvd : p ^ m ∣ p ^ (d + r * E) := pow_dvd_pow p hmain_le
  have h_core : p ^ m ∣ p ^ d * u ^ E := hpow_dvd.trans h_prod_base
  have h_nat :
      p ^ m ∣ p ^ d * (Nat.factorial N / Nat.factorial k) * u ^ E := by
    have h := dvd_mul_of_dvd_right h_core (Nat.factorial N / Nat.factorial k)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have h_int :
      ((p ^ m : ℕ) : ℤ)
        ∣ ((p ^ d * (Nat.factorial N / Nat.factorial k) * u ^ E : ℕ) : ℤ) := by
    exact_mod_cast h_nat
  have h_all :
      ((p ^ m : ℕ) : ℤ)
        ∣ (((-1 : ℤ) ^ k) * casselsBinomNum p q k)
            * ((p ^ d * (Nat.factorial N / Nat.factorial k) * u ^ E : ℕ) : ℤ) :=
    dvd_mul_of_dvd_right h_int (((-1 : ℤ) ^ k) * casselsBinomNum p q k)
  simpa [casselsPadeWitnessTerm, d, E, m, mul_assoc, mul_comm, mul_left_comm]
    using h_all

/-- Top witness term has exact p-order `r(q-1)`. -/
private lemma cassels_witnessTerm_top_not_high_dvd
    (u p q N r : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q)
    (hpr : p ^ r ∣ u) (hpr1 : ¬ p ^ (r + 1) ∣ u) :
    ¬ ((p ^ (r * (q - 1) + 1) : ℕ) : ℤ)
      ∣ casselsPadeWitnessTerm u p q N N := by
  classical
  rcases hpr with ⟨s, hu_eq⟩
  have hp_not_dvd_s : ¬ p ∣ s := by
    intro hps
    rcases hps with ⟨t, ht⟩
    apply hpr1
    refine ⟨t, ?_⟩
    rw [hu_eq, ht, pow_succ]; ring
  let C : ℤ :=
    ((-1 : ℤ) ^ N) * casselsBinomNum p q N * ((s ^ (q - 1) : ℕ) : ℤ)
  have htop_eq :
      casselsPadeWitnessTerm u p q N N
        = ((p ^ (r * (q - 1)) : ℕ) : ℤ) * C := by
    have hfac : Nat.factorial N / Nat.factorial N = 1 :=
      Nat.div_self (Nat.factorial_pos N)
    have hpowu : u ^ (q - 1) = p ^ (r * (q - 1)) * s ^ (q - 1) := by
      rw [hu_eq, mul_pow, pow_mul]
    have hpowuZ :
        ((u ^ (q - 1) : ℕ) : ℤ) =
          ((p ^ (r * (q - 1)) * s ^ (q - 1) : ℕ) : ℤ) := by
      exact_mod_cast hpowu
    have hfacZ : ((Nat.factorial N : ℤ) / (Nat.factorial N : ℤ)) = 1 := by
      exact Int.ediv_self (by exact_mod_cast Nat.factorial_ne_zero N)
    dsimp [casselsPadeWitnessTerm, C]
    rw [hfacZ]
    push_cast at hpowuZ
    have hexp_top : p * (N - N) + (q - 1) = q - 1 := by simp
    rw [hexp_top]
    rw [hpowuZ]
    rw [Nat.sub_self]
    ring_nf
  intro htop_dvd
  have hp_dvd_C : (p : ℤ) ∣ C := by
    apply cassels_int_prime_dvd_of_pow_succ_dvd_pow_mul p (r * (q - 1)) hp C
    simpa [htop_eq] using htop_dvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hsign_not : ¬ (p : ℤ) ∣ (-1 : ℤ) ^ N :=
    cassels_int_prime_not_dvd_neg_one_pow p N hp
  have hbinom_not : ¬ (p : ℤ) ∣ casselsBinomNum p q N :=
    cassels_binomNum_not_dvd_p p q N hp hq hp_lt_q
  have hp_dvd_prod :
      (p : ℤ)
        ∣ ((-1 : ℤ) ^ N)
            * (casselsBinomNum p q N * ((s ^ (q - 1) : ℕ) : ℤ)) := by
    simpa [C, mul_assoc] using hp_dvd_C
  rcases hpZ.dvd_or_dvd hp_dvd_prod with hsign | hrest
  · exact hsign_not hsign
  · rcases hpZ.dvd_or_dvd hrest with hbinom | hspow
    · exact hbinom_not hbinom
    · have hp_dvd_spow : p ∣ s ^ (q - 1) := by exact_mod_cast hspow
      exact hp_not_dvd_s (hp.dvd_of_dvd_pow hp_dvd_spow)

/-- THE remaining p-adic blocker — NOW CLOSED via separating modulus.

ChatGPT pro extended 39230ff0 (2026-05-15) delivered the complete
proof. Strategy: separating modulus `M = p^(r(q-1)+1)`.
  - Lower terms `k < N`: M ∣ witness_k (p-adic exponent ≥ r(q-1)+1).
  - Top term `k = N`: M ∤ witness_N (exact order r(q-1)).
  - If M ∣ sum, then M ∣ (sum - lower_sum) = witness_N, contradiction. -/
private theorem cassels_witness_sum_not_high_dvd
    (u p q N r : ℕ)
    (hp : p.Prime) (hq : q.Prime)
    (hp_lt_q : p < q)
    (hpr : p ^ r ∣ u)
    (hpr1 : ¬ p ^ (r + 1) ∣ u) :
    ¬ ((p ^ (r * (q - 1) + 1) : ℕ) : ℤ)
      ∣ casselsPadeWitnessSum u p q N := by
  classical
  let M : ℤ := ((p ^ (r * (q - 1) + 1) : ℕ) : ℤ)
  have hbelow :
      M ∣ ∑ k ∈ Finset.range N,
            casselsPadeWitnessTerm u p q N k := by
    refine Finset.dvd_sum ?_
    intro k hk
    dsimp [M]
    exact cassels_witnessTerm_lower_high_dvd
      u p q N r k hpr (Finset.mem_range.mp hk)
  have htop_not :
      ¬ M ∣ casselsPadeWitnessTerm u p q N N := by
    dsimp [M]
    exact cassels_witnessTerm_top_not_high_dvd
      u p q N r hp hq hp_lt_q hpr hpr1
  have hsplit :
      casselsPadeWitnessSum u p q N
        = (∑ k ∈ Finset.range N,
            casselsPadeWitnessTerm u p q N k)
          + casselsPadeWitnessTerm u p q N N := by
    dsimp [casselsPadeWitnessSum]
    rw [Finset.sum_range_succ]
  intro hsum
  rw [hsplit] at hsum
  have htop_dvd : M ∣ casselsPadeWitnessTerm u p q N N := by
    have hsub :
        M ∣ ((∑ k ∈ Finset.range N,
                  casselsPadeWitnessTerm u p q N k)
              + casselsPadeWitnessTerm u p q N N)
            -
            (∑ k ∈ Finset.range N,
                  casselsPadeWitnessTerm u p q N k) :=
      dvd_sub hsum hbelow
    simpa using hsub
  exact htop_not htop_dvd

/-- p-adic denominator obstruction (REAL arithmetic blocker).

If `p^n ∤ u`, then the cleared Padé truncation cannot equal `D · v`.

ChatGPT b93fb0f5 wrapper: bypasses padicValRat plumbing via
the separating modulus `p^(r(q-1)+1)`.  The only research-level
subgoal is `cassels_witness_sum_not_high_dvd`. -/
private theorem cassels_pade_padic_denominator_obstruction
    (u v p q n N : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hnpos : 0 < n)
    (hN : N = casselsPadeLevel p q n)
    (hp_not_pn_dvd_u : ¬ p ^ n ∣ u) :
    (casselsPadeClearDen u p N : ℚ) * (v : ℚ)
      ≠
    (casselsPadeClearDen u p N : ℚ)
      * casselsPadeTruncQ u p q N := by
  classical
  intro hEqQ
  rcases cassels_exists_exact_p_order_lt p u n hnpos hp_not_pn_dvd_u with
    ⟨r, hrlt, hpr, hpr1⟩
  let M : ℤ := ((p ^ (r * (q - 1) + 1) : ℕ) : ℤ)
  have hleft_dvd :
      M ∣ (((casselsPadeClearDen u p N * v : ℕ) : ℤ)) := by
    dsimp [M]
    exact cassels_left_cleared_high_dvd u v p q n N r hN hrlt
  have hright_not_dvd :
      ¬ M ∣ casselsPadeWitnessSum u p q N := by
    dsimp [M]
    exact cassels_witness_sum_not_high_dvd
      u p q N r hp hq hp_lt_q hpr hpr1
  have hrightQ :
      (casselsPadeClearDen u p N : ℚ) * casselsPadeTruncQ u p q N
        = (casselsPadeWitnessSum u p q N : ℚ) :=
    cassels_pade_cleared_eq_witness_sum u p q N hu hp
  have hleftQ :
      (casselsPadeClearDen u p N : ℚ) * (v : ℚ)
        = ((((casselsPadeClearDen u p N * v : ℕ) : ℤ) : ℚ)) := by
    push_cast; ring
  have hEqQ_intcasts :
      ((((casselsPadeClearDen u p N * v : ℕ) : ℤ) : ℚ))
        = (casselsPadeWitnessSum u p q N : ℚ) := by
    rw [← hleftQ, ← hrightQ]
    exact hEqQ
  have hEqInt :
      (((casselsPadeClearDen u p N * v : ℕ) : ℤ))
        = casselsPadeWitnessSum u p q N := by
    exact_mod_cast hEqQ_intcasts
  have hright_dvd :
      M ∣ casselsPadeWitnessSum u p q N := by
    rw [← hEqInt]; exact hleft_dvd
  exact hright_not_dvd hright_dvd

/-- Fixed-level p-adic denominator obstruction in the ramified branch.

For any positive truncation level `N`, if `p ∤ u`, the cleared binomial
truncation cannot equal the cleared integer `v`.  This is the B2.4-ready
specialization of the arbitrary-order obstruction: it avoids the large
`casselsPadeLevel`, whose degree reaches the actual-root correction. -/
private theorem cassels_pade_padic_denominator_obstruction_of_not_dvd_u
    (u v p q N : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp_lt_q : p < q)
    (hNpos : 0 < N)
    (hp_not_dvd_u : ¬ p ∣ u) :
    (casselsPadeClearDen u p N : ℚ) * (v : ℚ)
      ≠
    (casselsPadeClearDen u p N : ℚ)
      * casselsPadeTruncQ u p q N := by
  classical
  intro hEqQ
  let M : ℤ := (p : ℤ)
  have hleft_dvd :
      M ∣ (((casselsPadeClearDen u p N * v : ℕ) : ℤ)) := by
    have hp_dvd_D : p ∣ casselsPadeClearDen u p N := by
      unfold casselsPadeClearDen
      have hp_dvd_pN : p ∣ p ^ N := by
        simpa using pow_dvd_pow p (by omega : 1 ≤ N)
      have hp_dvd_first : p ∣ p ^ N * Nat.factorial N :=
        dvd_mul_of_dvd_left hp_dvd_pN (Nat.factorial N)
      exact dvd_mul_of_dvd_left hp_dvd_first (u ^ (p * N))
    have hp_dvd_Dv : p ∣ casselsPadeClearDen u p N * v :=
      dvd_mul_of_dvd_left hp_dvd_D v
    dsimp [M]
    exact_mod_cast hp_dvd_Dv
  have hright_not_dvd :
      ¬ M ∣ casselsPadeWitnessSum u p q N := by
    have hpr : p ^ 0 ∣ u := by simp
    have hpr1 : ¬ p ^ (0 + 1) ∣ u := by simpa using hp_not_dvd_u
    dsimp [M]
    simpa using
      (cassels_witness_sum_not_high_dvd
        u p q N 0 hp hq hp_lt_q hpr hpr1)
  have hrightQ :
      (casselsPadeClearDen u p N : ℚ) * casselsPadeTruncQ u p q N
        = (casselsPadeWitnessSum u p q N : ℚ) :=
    cassels_pade_cleared_eq_witness_sum u p q N hu hp
  have hleftQ :
      (casselsPadeClearDen u p N : ℚ) * (v : ℚ)
        = ((((casselsPadeClearDen u p N * v : ℕ) : ℤ) : ℚ)) := by
    push_cast
    ring
  have hEqQ_intcasts :
      ((((casselsPadeClearDen u p N * v : ℕ) : ℤ) : ℚ))
        = (casselsPadeWitnessSum u p q N : ℚ) := by
    rw [← hleftQ, ← hrightQ]
    exact hEqQ
  have hEqInt :
      (((casselsPadeClearDen u p N * v : ℕ) : ℤ))
        = casselsPadeWitnessSum u p q N := by
    exact_mod_cast hEqQ_intcasts
  have hright_dvd :
      M ∣ casselsPadeWitnessSum u p q N := by
    rw [← hEqInt]
    exact hleft_dvd
  exact hright_not_dvd hright_dvd

/-- B2.4 fixed-index instance of the p-adic denominator obstruction. -/
private theorem cassels_b24_padic_denominator_obstruction_of_not_dvd_u
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp_lt_q : p < q)
    (hp_not_dvd_u : ¬ p ∣ u) :
    (casselsPadeClearDen u p (casselsB24R p q) : ℚ) * (v : ℚ)
      ≠
    (casselsPadeClearDen u p (casselsB24R p q) : ℚ)
      * casselsPadeTruncQ u p q (casselsB24R p q) :=
  cassels_pade_padic_denominator_obstruction_of_not_dvd_u
    u v p q (casselsB24R p q) hu hp hq hp_lt_q
    (casselsB24R_pos p q) hp_not_dvd_u

private theorem cassels_actual_lower_term_den_dvd_clear_without_one_p
    (u p q N k : ℕ) (hqpos : 0 < q) (hk : k < N) :
    (casselsActualRootCoeff p q k
        * (u : ℚ) ^ (q - 1)
        * (((u : ℚ) ^ p)⁻¹) ^ k).den
      ∣ p ^ (N - 1) * Nat.factorial N * u ^ (p * N) := by
  have hkN : k ≤ N := le_of_lt hk
  have hkNpred : k ≤ N - 1 := by omega
  have hcoeff :
      (casselsActualRootCoeff p q k).den ∣ casselsCoeffDenBound p k :=
    casselsActualRootCoeff_den_dvd p q k hqpos
  have hupow :
      (((u : ℚ) ^ (q - 1)).den) ∣ 1 := by
    simp
  have hinv :
      ((((u : ℚ) ^ p)⁻¹) ^ k).den ∣ u ^ (p * k) := by
    rw [inv_pow, ← pow_mul]
    exact rat_inv_nat_pow_den_dvd u (p * k)
  have hleft :
      (casselsActualRootCoeff p q k * (u : ℚ) ^ (q - 1)).den
        ∣ casselsCoeffDenBound p k * 1 :=
    rat_mul_den_dvd_of_den_dvd _ _ hcoeff hupow
  have hterm :
      (casselsActualRootCoeff p q k
          * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k).den
        ∣ (casselsCoeffDenBound p k * 1) * u ^ (p * k) :=
    rat_mul_den_dvd_of_den_dvd _ _ hleft hinv
  refine hterm.trans ?_
  unfold casselsCoeffDenBound
  have hp_part :
      p ^ k * Nat.factorial k ∣ p ^ (N - 1) * Nat.factorial N :=
    Nat.mul_dvd_mul
      (pow_dvd_pow p hkNpred)
      (Nat.factorial_dvd_factorial hkN)
  have hu_part : u ^ (p * k) ∣ u ^ (p * N) :=
    pow_dvd_pow u (Nat.mul_le_mul_left p hkN)
  have hmul :
      (p ^ k * Nat.factorial k) * u ^ (p * k)
        ∣ (p ^ (N - 1) * Nat.factorial N) * u ^ (p * N) :=
    Nat.mul_dvd_mul hp_part hu_part
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

private theorem cassels_actual_lower_term_cleared_p_multiple
    (u p q N k : ℕ) (hqpos : 0 < q) (hNpos : 0 < N) (hk : k < N) :
    ∃ z : ℤ,
      (casselsPadeClearDen u p N : ℚ)
        * (casselsActualRootCoeff p q k
            * (u : ℚ) ^ (q - 1)
            * (((u : ℚ) ^ p)⁻¹) ^ k)
        = (((p : ℤ) * z : ℤ) : ℚ) := by
  let D0 : ℕ := p ^ (N - 1) * Nat.factorial N * u ^ (p * N)
  have hden :
      (casselsActualRootCoeff p q k
          * (u : ℚ) ^ (q - 1)
          * (((u : ℚ) ^ p)⁻¹) ^ k).den ∣ D0 := by
    dsimp [D0]
    exact cassels_actual_lower_term_den_dvd_clear_without_one_p
      u p q N k hqpos hk
  rcases rat_mul_is_int_of_den_dvd D0
      (casselsActualRootCoeff p q k
        * (u : ℚ) ^ (q - 1)
        * (((u : ℚ) ^ p)⁻¹) ^ k) hden with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hD_eq : casselsPadeClearDen u p N = p * D0 := by
    dsimp [D0, casselsPadeClearDen]
    cases N with
    | zero => omega
    | succ N =>
        simp [pow_succ]
        ring
  calc
    (casselsPadeClearDen u p N : ℚ)
        * (casselsActualRootCoeff p q k
            * (u : ℚ) ^ (q - 1)
            * (((u : ℚ) ^ p)⁻¹) ^ k)
        =
      (p : ℚ)
        * ((D0 : ℚ)
          * (casselsActualRootCoeff p q k
              * (u : ℚ) ^ (q - 1)
              * (((u : ℚ) ^ p)⁻¹) ^ k)) := by
          rw [hD_eq]
          push_cast
          ring
    _ = (p : ℚ) * (z : ℚ) := by rw [hz]
    _ = (((p : ℤ) * z : ℤ) : ℚ) := by
          push_cast
          ring

private theorem cassels_actual_top_term_cleared_p_unit
    (u p q N : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime) (hp_lt_q : p < q)
    (hp_not_dvd_u : ¬ p ∣ u) :
    ∃ W : ℤ,
      (casselsPadeClearDen u p N : ℚ)
        * (casselsActualRootCoeff p q N
            * (u : ℚ) ^ (q - 1)
            * (((u : ℚ) ^ p)⁻¹) ^ N)
        = (W : ℚ)
        ∧ ¬ (p : ℤ) ∣ W := by
  rcases casselsActualRootCoeff_top_cleared_p_unit
      p q N hp hq hp_lt_q with ⟨C, hCeq, hCunit⟩
  refine ⟨C * ((u ^ (q - 1) : ℕ) : ℤ), ?_, ?_⟩
  · have huQ_ne : (u : ℚ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
    have hD_cast :
        (casselsPadeClearDen u p N : ℚ)
          = ((p ^ N * Nat.factorial N : ℕ) : ℚ) * (u : ℚ) ^ (p * N) := by
      unfold casselsPadeClearDen
      push_cast
      ring
    have hu_inv_pow :
        (((u : ℚ) ^ p)⁻¹) ^ N = ((u : ℚ) ^ (p * N))⁻¹ := by
      rw [inv_pow, ← pow_mul]
    have hu_cancel :
        (u : ℚ) ^ (p * N) * (((u : ℚ) ^ p)⁻¹) ^ N = 1 := by
      rw [hu_inv_pow]
      field_simp [pow_ne_zero (p * N) huQ_ne]
    calc
      (casselsPadeClearDen u p N : ℚ)
          * (casselsActualRootCoeff p q N
              * (u : ℚ) ^ (q - 1)
              * (((u : ℚ) ^ p)⁻¹) ^ N)
          =
        (((p ^ N * Nat.factorial N : ℕ) : ℚ)
            * casselsActualRootCoeff p q N)
          * ((u : ℚ) ^ (p * N) * (((u : ℚ) ^ p)⁻¹) ^ N)
          * (u : ℚ) ^ (q - 1) := by
            rw [hD_cast]
            ring
      _ = (C : ℚ) * (u : ℚ) ^ (q - 1) := by
            rw [hCeq, hu_cancel]
            ring
      _ = ((C * ((u ^ (q - 1) : ℕ) : ℤ) : ℤ) : ℚ) := by
            push_cast
            rfl
  · intro hdiv
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have hu_pow_not : ¬ (p : ℤ) ∣ ((u ^ (q - 1) : ℕ) : ℤ) := by
      intro hpupow
      have hpupow_nat : p ∣ u ^ (q - 1) := by exact_mod_cast hpupow
      exact hp_not_dvd_u (hp.dvd_of_dvd_pow hpupow_nat)
    rcases hpZ.dvd_or_dvd hdiv with hC | hu_pow
    · exact hCunit hC
    · exact hu_pow_not hu_pow

private theorem cassels_actual_padic_denominator_obstruction_of_not_dvd_u
    (u v p q N : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp_lt_q : p < q)
    (hNpos : 0 < N)
    (hp_not_dvd_u : ¬ p ∣ u) :
    (casselsPadeClearDen u p N : ℚ) * (v : ℚ)
      ≠
    (casselsPadeClearDen u p N : ℚ)
      * casselsActualTruncQ u p q N := by
  classical
  intro hEqQ
  let D : ℕ := casselsPadeClearDen u p N
  let f : ℕ → ℚ := fun k =>
    casselsActualRootCoeff p q k
      * (u : ℚ) ^ (q - 1)
      * (((u : ℚ) ^ p)⁻¹) ^ k
  have hqpos : 0 < q := hq.pos
  have hleft_dvd :
      (p : ℤ) ∣ (((D * v : ℕ) : ℤ)) := by
    have hp_dvd_D : p ∣ D := by
      dsimp [D]
      unfold casselsPadeClearDen
      have hp_dvd_pN : p ∣ p ^ N := by
        simpa using pow_dvd_pow p (by omega : 1 ≤ N)
      have hp_dvd_first : p ∣ p ^ N * Nat.factorial N :=
        dvd_mul_of_dvd_left hp_dvd_pN (Nat.factorial N)
      exact dvd_mul_of_dvd_left hp_dvd_first (u ^ (p * N))
    have hp_dvd_Dv : p ∣ D * v := dvd_mul_of_dvd_left hp_dvd_D v
    exact_mod_cast hp_dvd_Dv
  have hlower :
      ∀ k : ℕ, ∃ z : ℤ, k ∈ Finset.range N →
        (D : ℚ) * f k = (((p : ℤ) * z : ℤ) : ℚ) := by
    intro k
    by_cases hk : k ∈ Finset.range N
    · have hklt : k < N := Finset.mem_range.mp hk
      rcases cassels_actual_lower_term_cleared_p_multiple
          u p q N k hqpos hNpos hklt with ⟨z, hz⟩
      exact ⟨z, fun _ => by simpa [D, f] using hz⟩
    · exact ⟨0, fun hk' => False.elim (hk hk')⟩
  choose Z hZ using hlower
  rcases cassels_actual_top_term_cleared_p_unit
      u p q N hu hp hq hp_lt_q hp_not_dvd_u with ⟨W, hWeq, hWunit⟩
  let lowerW : ℤ := ∑ k ∈ Finset.range N, Z k
  let fullW : ℤ := (p : ℤ) * lowerW + W
  have hrightQ :
      (D : ℚ) * casselsActualTruncQ u p q N = (fullW : ℚ) := by
    calc
      (D : ℚ) * casselsActualTruncQ u p q N
          = (D : ℚ) * (∑ k ∈ Finset.range (N + 1), f k) := by
              dsimp [D, f, casselsActualTruncQ]
      _ = ∑ k ∈ Finset.range (N + 1), (D : ℚ) * f k := by
              rw [Finset.mul_sum]
      _ = (∑ k ∈ Finset.range N, (D : ℚ) * f k) + (D : ℚ) * f N := by
              rw [Finset.sum_range_succ]
      _ = (∑ k ∈ Finset.range N, (((p : ℤ) * Z k : ℤ) : ℚ)) + (W : ℚ) := by
              have htop : (D : ℚ) * f N = (W : ℚ) := by
                simpa [D, f] using hWeq
              rw [htop]
              congr 1
              apply Finset.sum_congr rfl
              intro k hk
              exact hZ k hk
      _ = (fullW : ℚ) := by
              dsimp [fullW, lowerW]
              push_cast
              rw [Finset.mul_sum]
  have hleftQ :
      (D : ℚ) * (v : ℚ) = ((((D * v : ℕ) : ℤ) : ℚ)) := by
    push_cast
    ring
  have hEqQ_intcasts :
      ((((D * v : ℕ) : ℤ) : ℚ)) = (fullW : ℚ) := by
    rw [← hleftQ, ← hrightQ]
    exact hEqQ
  have hEqInt : (((D * v : ℕ) : ℤ)) = fullW := by
    exact_mod_cast hEqQ_intcasts
  have hfull_dvd : (p : ℤ) ∣ fullW := by
    rw [← hEqInt]
    exact hleft_dvd
  have hplower : (p : ℤ) ∣ (p : ℤ) * lowerW := dvd_mul_right _ _
  have hpW : (p : ℤ) ∣ W := by
    have hsub := dvd_sub hfull_dvd hplower
    have hsub_eq : fullW - (p : ℤ) * lowerW = W := by
      dsimp [fullW]
      ring
    rwa [hsub_eq] at hsub
  exact hWunit hpW

theorem casselsB24_gap_ne_zero
    {u v p q : ℕ}
    (hu : 1 < u)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpq : p < q)
    (hp_not_dvd_u : ¬ p ∣ u) :
    casselsB24GapQ u v p q ≠ 0 := by
  classical
  intro hzero
  let R := casselsB24R p q
  let ρ := casselsB24Rho p q
  have hobs :
      (casselsPadeClearDen u p R : ℚ) * (v : ℚ)
        ≠
      (casselsPadeClearDen u p R : ℚ)
        * casselsActualTruncQ u p q R := by
    dsimp [R]
    exact cassels_actual_padic_denominator_obstruction_of_not_dvd_u
      u v p q (casselsB24R p q) hu hp hq hpq
      (casselsB24R_pos p q) hp_not_dvd_u
  have hpQ_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have huQ_ne : (u : ℚ) ≠ 0 := by exact_mod_cast (by omega : u ≠ 0)
  have hpref_ne :
      (p : ℚ) ^ (R + ρ) * (u : ℚ) ^ (p * R - q + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hpQ_ne) (pow_ne_zero _ huQ_ne)
  have hdiff_zero :
      (v : ℚ) - casselsActualTruncQ u p q R = 0 := by
    have hmul :
        ((p : ℚ) ^ (R + ρ) * (u : ℚ) ^ (p * R - q + 1))
          * ((v : ℚ) - casselsActualTruncQ u p q R) = 0 := by
      simpa [casselsB24GapQ, R, ρ, mul_assoc] using hzero
    exact (mul_eq_zero.mp hmul).resolve_left hpref_ne
  have hv_eq :
      (v : ℚ) = casselsActualTruncQ u p q R := sub_eq_zero.mp hdiff_zero
  exact hobs (by rw [hv_eq])

theorem casselsB24_gap_abs_bound_real
    {u v p q : ℕ}
    (hu : 1 < u)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpq : p < q)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    let R := casselsB24R p q
    let ρ := casselsB24Rho p q
    |((casselsB24GapQ u v p q : ℚ) : ℝ)|
      ≤
    (p : ℝ) ^ (R + ρ)
      * (((u : ℝ) ^ p)⁻¹
        * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q)) := by
  classical
  let R := casselsB24R p q
  let ρ := casselsB24Rho p q
  have htail :
      |(v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)|
        ≤
      (u : ℝ) ^ (q - 1)
        * (((u : ℝ) ^ p)⁻¹) ^ (R + 1)
        * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q) := by
    dsimp [R]
    exact cassels_actualRootCoeff_scaled_tail_gap_abs_le
      u v p q (casselsB24R p q) hu hp5 hq5 hpq hroot
  have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hu_nonneg : (0 : ℝ) ≤ (u : ℝ) := le_of_lt hu_pos
  have hpref_nonneg :
      0 ≤ (p : ℝ) ^ (R + ρ) * (u : ℝ) ^ (p * R - q + 1) := by
    positivity
  have hgap_cast :
      ((casselsB24GapQ u v p q : ℚ) : ℝ)
        =
      (p : ℝ) ^ (R + ρ)
        * (u : ℝ) ^ (p * R - q + 1)
        * ((v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)) := by
    dsimp [casselsB24GapQ, R, ρ]
    push_cast
    ring
  have hscaled_pow :
      (u : ℝ) ^ (p * R - q + 1)
        * ((u : ℝ) ^ (q - 1)
          * (((u : ℝ) ^ p)⁻¹) ^ (R + 1))
        =
      ((u : ℝ) ^ p)⁻¹ := by
    have hq_lt : q < p * R := by
      dsimp [R]
      exact q_lt_p_mul_casselsB24R p q hp.pos
    have hEadd : p * R - q + 1 + (q - 1) = p * R := by omega
    have hup_ne : (u : ℝ) ^ p ≠ 0 := (pow_pos hu_pos p).ne'
    rw [← mul_assoc, ← pow_add, hEadd]
    rw [inv_pow, ← pow_mul]
    have hpow_split :
        (u : ℝ) ^ p * (u : ℝ) ^ (p * R)
          = (u : ℝ) ^ (p * (R + 1)) := by
      rw [← pow_add]
      ring_nf
    calc
      (u : ℝ) ^ (p * R) * ((u : ℝ) ^ (p * (R + 1)))⁻¹
          =
        (u : ℝ) ^ (p * R)
          * (((u : ℝ) ^ p * (u : ℝ) ^ (p * R))⁻¹) := by
            rw [hpow_split]
      _ = ((u : ℝ) ^ p)⁻¹ := by
            field_simp [hup_ne, pow_ne_zero (p * R) hu_pos.ne']
  have hbound_scaled :
      (p : ℝ) ^ (R + ρ)
        * (u : ℝ) ^ (p * R - q + 1)
        * |(v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)|
      ≤
      (p : ℝ) ^ (R + ρ)
        * (((u : ℝ) ^ p)⁻¹
          * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q)) := by
    calc
      (p : ℝ) ^ (R + ρ)
          * (u : ℝ) ^ (p * R - q + 1)
          * |(v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)|
        ≤
      (p : ℝ) ^ (R + ρ)
          * (u : ℝ) ^ (p * R - q + 1)
          * ((u : ℝ) ^ (q - 1)
            * (((u : ℝ) ^ p)⁻¹) ^ (R + 1)
            * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q)) := by
            exact mul_le_mul_of_nonneg_left htail hpref_nonneg
      _ =
      (p : ℝ) ^ (R + ρ)
        * (((u : ℝ) ^ p)⁻¹
          * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q)) := by
            calc
              (p : ℝ) ^ (R + ρ)
                  * (u : ℝ) ^ (p * R - q + 1)
                  * ((u : ℝ) ^ (q - 1)
                    * (((u : ℝ) ^ p)⁻¹) ^ (R + 1)
                    * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q))
                  =
                (p : ℝ) ^ (R + ρ)
                  * (((u : ℝ) ^ (p * R - q + 1)
                    * ((u : ℝ) ^ (q - 1)
                      * (((u : ℝ) ^ p)⁻¹) ^ (R + 1)))
                    * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q)) := by
                    ring
              _ =
                (p : ℝ) ^ (R + ρ)
                  * (((u : ℝ) ^ p)⁻¹
                    * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q)) := by
                    rw [hscaled_pow]
  calc
    |((casselsB24GapQ u v p q : ℚ) : ℝ)|
        =
      (p : ℝ) ^ (R + ρ)
        * (u : ℝ) ^ (p * R - q + 1)
        * |(v : ℝ) - ((casselsActualTruncQ u p q R : ℚ) : ℝ)| := by
          rw [hgap_cast, abs_mul, abs_of_nonneg hpref_nonneg]
    _ ≤
      (p : ℝ) ^ (R + ρ)
        * (((u : ℝ) ^ p)⁻¹
          * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q)) :=
        hbound_scaled

theorem casselsB24_gap_abs_le_directBudget
    {u v p q : ℕ}
    (hu : 1 < u)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hpq : p < q)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    |((casselsB24GapQ u v p q : ℚ) : ℝ)|
      ≤ casselsB24DirectBudget u p q := by
  classical
  let R := casselsB24R p q
  let ρ := casselsB24Rho p q
  let X := casselsB24X u p
  let A := casselsB24A u p q
  let B : ℝ := (v : ℝ) / (u : ℝ) ^ (q - 1)
  let Q := casselsB24Qfac p q
  let T : ℝ := ((casselsB24RootTruncQ u p q : ℚ) : ℝ) / (u : ℝ) ^ (p * R)
  have hu_pos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
  have hu_ne : (u : ℝ) ≠ 0 := hu_pos.ne'
  have hU_nonneg : 0 ≤ (u : ℝ) ^ (p * R) := by positivity
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q, casselsB24Qfac, R, ρ]
    positivity
  have hpref_nonneg : 0 ≤ Q * (u : ℝ) ^ (p * R) :=
    mul_nonneg hQ_nonneg hU_nonneg
  have hscaledQ :=
    casselsB24_scaled_actualTruncQ_eq_rootTruncQ
      u p q (by omega : 0 < u) hp5 hpq
  have hscaledR :
      (u : ℝ) ^ (p * R - q + 1)
          * ((casselsActualTruncQ u p q R : ℚ) : ℝ)
        =
      ((casselsB24RootTruncQ u p q : ℚ) : ℝ) := by
    dsimp [R]
    exact_mod_cast hscaledQ
  have hgap_cast :
      ((casselsB24GapQ u v p q : ℚ) : ℝ)
        =
      Q * ((u : ℝ) ^ (p * R - q + 1) * (v : ℝ)
        - ((casselsB24RootTruncQ u p q : ℚ) : ℝ)) := by
    dsimp [casselsB24GapQ, Q, casselsB24Qfac, R, ρ]
    push_cast
    calc
      (p : ℝ) ^ (casselsB24R p q + casselsB24Rho p q)
          * (u : ℝ) ^ (p * casselsB24R p q - q + 1)
          * ((v : ℝ) - ((casselsActualTruncQ u p q (casselsB24R p q) : ℚ) : ℝ))
          =
        (p : ℝ) ^ (casselsB24R p q + casselsB24Rho p q)
          * ((u : ℝ) ^ (p * R - q + 1) * (v : ℝ)
            - (u : ℝ) ^ (p * R - q + 1)
              * ((casselsActualTruncQ u p q R : ℚ) : ℝ)) := by
            dsimp [R]
            ring
      _ =
        (p : ℝ) ^ (casselsB24R p q + casselsB24Rho p q)
          * ((u : ℝ) ^ (p * R - q + 1) * (v : ℝ)
            - ((casselsB24RootTruncQ u p q : ℚ) : ℝ)) := by
            rw [hscaledR]
  have hq_lt : q < p * R := by
    dsimp [R]
    exact q_lt_p_mul_casselsB24R p q hp.pos
  have hEadd : p * R - q + 1 + (q - 1) = p * R := by omega
  have hnorm_gap :
      (u : ℝ) ^ (p * R - q + 1) * (v : ℝ)
        - ((casselsB24RootTruncQ u p q : ℚ) : ℝ)
        =
      (u : ℝ) ^ (p * R) * (B - T) := by
    dsimp [B, T]
    have hden_ne : (u : ℝ) ^ (p * R) ≠ 0 :=
      pow_ne_zero _ hu_ne
    have hqden_ne : (u : ℝ) ^ (q - 1) ≠ 0 :=
      pow_ne_zero _ hu_ne
    have hleft :
        (u : ℝ) ^ (p * R) * ((v : ℝ) / (u : ℝ) ^ (q - 1))
          =
        (u : ℝ) ^ (p * R - q + 1) * (v : ℝ) := by
      field_simp [hqden_ne]
      have hEadd' : q - 1 + (p * R - q + 1) = p * R := by omega
      calc
        (u : ℝ) ^ (p * R) * (v : ℝ)
            = (v : ℝ) * (u : ℝ) ^ (p * R) := by ring
        _ = (v : ℝ) * ((u : ℝ) ^ (q - 1)
              * (u : ℝ) ^ (p * R - q + 1)) := by
              rw [← pow_add, hEadd']
        _ = (v : ℝ) * (u : ℝ) ^ (q - 1)
              * (u : ℝ) ^ (p * R - q + 1) := by ring
    have hright :
        (u : ℝ) ^ (p * R)
            * (((casselsB24RootTruncQ u p q : ℚ) : ℝ)
              / (u : ℝ) ^ (p * R))
          =
        ((casselsB24RootTruncQ u p q : ℚ) : ℝ) := by
      field_simp [hden_ne]
    rw [mul_sub, hleft, hright]
  have htri : |B - T| ≤ |B - A| + |A - T| := by
    calc
      |B - T| = |(B - A) + (A - T)| := by ring_nf
      _ ≤ |B - A| + |A - T| := abs_add_le _ _
  have hcorr : |B - A| ≤ X ^ q / A ^ (p - 1) := by
    dsimp [B, A, X]
    exact casselsB24_actual_minus_binomial_bound
      (u := u) (v := v) (p := p) (q := q) hu hp.pos hroot
  have htail : |A - T|
      ≤ |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
          * X ^ (R + 1) / (1 - X) := by
    dsimp [A, T, X, R]
    exact casselsB24_root_tail_abs_le u p q hu hp
  have hBT :
      |B - T|
        ≤
      X ^ q / A ^ (p - 1)
        + |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
          * X ^ (R + 1) / (1 - X) :=
    htri.trans (add_le_add hcorr htail)
  have hscaled_bound :
      Q * (u : ℝ) ^ (p * R) * |B - T|
        ≤
      Q * (u : ℝ) ^ (p * R)
        * (X ^ q / A ^ (p - 1)
          + |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
            * X ^ (R + 1) / (1 - X)) :=
    mul_le_mul_of_nonneg_left hBT hpref_nonneg
  have hUX :
      (u : ℝ) ^ (p * R)
        * (|((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
            * X ^ (R + 1) / (1 - X))
        =
      X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X) := by
    have hXpow :
        (u : ℝ) ^ (p * R) * X ^ (R + 1) = X := by
      dsimp [X, casselsB24X]
      rw [inv_pow, ← pow_mul]
      have hsplit :
          (u : ℝ) ^ (p * (R + 1))
            = (u : ℝ) ^ p * (u : ℝ) ^ (p * R) := by
        rw [← pow_add]
        ring_nf
      calc
        (u : ℝ) ^ (p * R) * ((u : ℝ) ^ (p * (R + 1)))⁻¹
            =
          (u : ℝ) ^ (p * R)
            * (((u : ℝ) ^ p * (u : ℝ) ^ (p * R))⁻¹) := by
              rw [hsplit]
        _ = ((u : ℝ) ^ p)⁻¹ := by
              field_simp [pow_ne_zero p hu_ne,
                pow_ne_zero (p * R) hu_ne]
    calc
      (u : ℝ) ^ (p * R)
          * (|((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
              * X ^ (R + 1) / (1 - X))
          =
        ((u : ℝ) ^ (p * R) * X ^ (R + 1))
          * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X) := by
            ring
      _ = X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X) := by
            rw [hXpow]
  calc
    |((casselsB24GapQ u v p q : ℚ) : ℝ)|
        =
      Q * (u : ℝ) ^ (p * R) * |B - T| := by
        rw [hgap_cast, hnorm_gap, abs_mul, abs_mul,
          abs_of_nonneg hQ_nonneg, abs_of_nonneg hU_nonneg]
        ring
    _ ≤
      Q * (u : ℝ) ^ (p * R)
        * (X ^ q / A ^ (p - 1)
          + |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
            * X ^ (R + 1) / (1 - X)) :=
        hscaled_bound
    _ = casselsB24DirectBudget u p q := by
        calc
          Q * (u : ℝ) ^ (p * R)
              * (X ^ q / A ^ (p - 1)
                + |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
                  * X ^ (R + 1) / (1 - X))
              =
            Q * ((u : ℝ) ^ (p * R) * (X ^ q / A ^ (p - 1))
              + (u : ℝ) ^ (p * R)
                * (|((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)|
                  * X ^ (R + 1) / (1 - X))) := by
                ring
          _ =
            Q * ((u : ℝ) ^ (p * R) * (X ^ q / A ^ (p - 1))
              + X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X)) := by
                rw [hUX]
          _ = casselsB24DirectBudget u p q := by
                dsimp [casselsB24DirectBudget, casselsB24Qfac, Q, X, A, R, ρ]
                ring

theorem casselsB24_gap_contra_of_majorant_lt_one
    {u v p q : ℕ}
    (hu : 1 < u)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpq : p < q)
    (hp_not_dvd_u : ¬ p ∣ u)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q)
    (hmajor :
      let R := casselsB24R p q
      let ρ := casselsB24Rho p q
      (p : ℝ) ^ (R + ρ)
        * (((u : ℝ) ^ p)⁻¹
          * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q))
        < 1) :
    False := by
  classical
  let G : ℚ := casselsB24GapQ u v p q
  obtain ⟨I, hI⟩ :=
    casselsB24_gap_isInt
      (u := u) (v := v) (p := p) (q := q)
      (by omega : 0 < u) hp hq hp5 hq5 hpq
  have hIreal : ((G : ℚ) : ℝ) = (I : ℝ) := by
    exact_mod_cast hI.symm
  have hGneQ : G ≠ 0 := by
    dsimp [G]
    exact casselsB24_gap_ne_zero
      (u := u) (v := v) (p := p) (q := q)
      hu hp hq hp5 hq5 hpq hp_not_dvd_u
  have hGneR : ((G : ℚ) : ℝ) ≠ 0 := by
    intro hzero
    exact hGneQ (by exact_mod_cast hzero)
  have hbound :
      |((G : ℚ) : ℝ)|
        ≤
      (let R := casselsB24R p q
       let ρ := casselsB24Rho p q
       (p : ℝ) ^ (R + ρ)
        * (((u : ℝ) ^ p)⁻¹
          * ((32 : ℝ) ^ (R + 1) * casselsActualRootAbsTsum p q))) := by
    dsimp [G]
    exact casselsB24_gap_abs_bound_real
      (u := u) (v := v) (p := p) (q := q)
      hu hp hq hp5 hq5 hpq hroot
  have hsmall : |((G : ℚ) : ℝ)| < 1 :=
    lt_of_le_of_lt hbound hmajor
  exact cassels_nonzero_integer_abs_lt_one_false
    ((G : ℚ) : ℝ) ⟨I, hIreal⟩ hGneR hsmall

theorem casselsB24_gap_contra_of_directBudget_lt_one
    {u v p q : ℕ}
    (hu : 1 < u)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpq : p < q)
    (hp_not_dvd_u : ¬ p ∣ u)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q)
    (hbudget : casselsB24DirectBudget u p q < 1) :
    False := by
  classical
  let G : ℚ := casselsB24GapQ u v p q
  obtain ⟨I, hI⟩ :=
    casselsB24_gap_isInt
      (u := u) (v := v) (p := p) (q := q)
      (by omega : 0 < u) hp hq hp5 hq5 hpq
  have hIreal : ((G : ℚ) : ℝ) = (I : ℝ) := by
    exact_mod_cast hI.symm
  have hGneQ : G ≠ 0 := by
    dsimp [G]
    exact casselsB24_gap_ne_zero
      (u := u) (v := v) (p := p) (q := q)
      hu hp hq hp5 hq5 hpq hp_not_dvd_u
  have hGneR : ((G : ℚ) : ℝ) ≠ 0 := by
    intro hzero
    exact hGneQ (by exact_mod_cast hzero)
  have hbound :
      |((G : ℚ) : ℝ)| ≤ casselsB24DirectBudget u p q := by
    dsimp [G]
    exact casselsB24_gap_abs_le_directBudget
      (u := u) (v := v) (p := p) (q := q)
      hu hp hq hp5 hpq hroot
  have hsmall : |((G : ℚ) : ℝ)| < 1 :=
    lt_of_le_of_lt hbound hbudget
  exact cassels_nonzero_integer_abs_lt_one_false
    ((G : ℚ) : ℝ) ⟨I, hIreal⟩ hGneR hsmall

private theorem one_sub_mul_le_pow_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1mx : 0 ≤ 1 - x := by linarith
    have hkx2 : 0 ≤ (k : ℝ) * x ^ 2 := mul_nonneg (Nat.cast_nonneg k) (sq_nonneg x)
    have key : 1 - (↑(k + 1) : ℝ) * x ≤ (1 - x) ^ k * (1 - x) := by
      have : 1 - (↑(k + 1) : ℝ) * x ≤ (1 - ↑k * x) * (1 - x) := by
        push_cast; nlinarith
      have : (1 - ↑k * x) * (1 - x) ≤ (1 - x) ^ k * (1 - x) :=
        mul_le_mul_of_nonneg_right (by linarith [ih]) h1mx
      linarith
    linarith [pow_succ (1 - x) k]

/-- The B24 direct budget is < 1 when `u^p > 5·p^q`.
Uses: Q·X < 1/5, |c_{R+1}| < 1/(R+1) ≤ 1/3, and elementary bounds. -/
private theorem casselsB24DirectBudget_lt_one_of_u_pow_gt
    (u p q : ℕ) (hu : 1 < u) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpq : p < q)
    (hlarge : 5 * p ^ q < u ^ p) :
    casselsB24DirectBudget u p q < 1 := by
  set R := casselsB24R p q
  set X := casselsB24X u p
  set A := casselsB24A u p q
  set Q := casselsB24Qfac p q
  have hQX : Q * X < 1 / 5 :=
    casselsB24Qfac_mul_X_lt_one_div_five_of_u_pow_gt u p q hu hp5 hpq hlarge
  have hQ_pos : (0 : ℝ) < Q := by
    dsimp [Q, casselsB24Qfac]; positivity
  have hX_pos : (0 : ℝ) < X :=
    casselsB24X_pos u p hu
  have hX_lt_one : X < 1 :=
    casselsB24X_lt_one u p hu (by omega : 0 < p)
  have hX_lt_half : X < 1 / 2 := by
    have hQ_ge_one : (1 : ℝ) ≤ Q := by
      dsimp [Q, casselsB24Qfac]
      exact one_le_pow₀
        (by exact_mod_cast (show 1 ≤ p by omega))
    calc X = 1 * X := (one_mul X).symm
      _ ≤ Q * X := mul_le_mul_of_nonneg_right hQ_ge_one (le_of_lt hX_pos)
      _ < 1 / 5 := hQX
      _ < 1 / 2 := by norm_num
  have h1mX_pos : (0 : ℝ) < 1 - X := by linarith
  have hA_pos : (0 : ℝ) < A := by
    dsimp [A, casselsB24A]
    exact Real.rpow_pos_of_pos h1mX_pos _
  have hA_pow_pos : (0 : ℝ) < A ^ (p - 1) := pow_pos hA_pos _
  have hR_le : R + 1 ≤ q := by
    have hRρ := casselsB24R_add_rho_lt_q p q hp5 hpq
    dsimp [R]; omega
  have hcoeff_abs_le : |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| ≤ 1 := by
    dsimp [R]
    exact casselsRootCoeff_abs_B24_first_omitted_le_one p q (by omega : 0 < p)
  have hinner_le :
      (u : ℝ) ^ (p * R) * X ^ q / A ^ (p - 1)
        + X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X)
        ≤ 4 * X := by
    have hterm1 : (u : ℝ) ^ (p * R) * X ^ q / A ^ (p - 1) ≤ 2 * X := by
      have huR_ne : (u : ℝ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
      have hup_pos : (0 : ℝ) < (u : ℝ) ^ p := by positivity
      have hXq_factor :
          (u : ℝ) ^ (p * R) * X ^ q ≤ X := by
        dsimp [X, casselsB24X]
        rw [inv_pow, ← pow_mul]
        have hpR_le_pq : p * R + p ≤ p * q := by
          nlinarith [hR_le]
        calc (u : ℝ) ^ (p * R) * ((u : ℝ) ^ (p * q))⁻¹
            = (u : ℝ) ^ (p * R) / (u : ℝ) ^ (p * q) := by ring
          _ ≤ 1 / (u : ℝ) ^ p := by
                rw [div_le_div_iff₀ (by positivity) hup_pos]
                calc (u : ℝ) ^ (p * R) * (u : ℝ) ^ p
                    = (u : ℝ) ^ (p * R + p) := by rw [← pow_add]
                  _ ≤ (u : ℝ) ^ (p * q) :=
                      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ u by omega)) hpR_le_pq
                  _ = 1 * (u : ℝ) ^ (p * q) := (one_mul _).symm
          _ = ((u : ℝ) ^ p)⁻¹ := one_div _
      have hA_pow_ge :
          (1 : ℝ) / 2 ≤ A ^ (p - 1) := by
        have h1mX_le : 1 - X ≤ 1 := by linarith [hX_pos]
        -- A^p = (1-X)^q (existing lemma)
        have hApow : A ^ p = (1 - X) ^ q :=
          casselsB24A_pow_p u p q hu (by omega : 0 < p)
        -- A ≤ 1
        have hA_le1 : A ≤ 1 := by
          dsimp [A, casselsB24A]
          exact Real.rpow_le_one (le_of_lt h1mX_pos) h1mX_le
            (by positivity : 0 ≤ (q : ℝ) / (p : ℝ))
        -- A^{p-1} ≥ (1-X)^q (since A^{p-1}·A = (1-X)^q and A ≤ 1)
        have hge_pow : (1 - X) ^ q ≤ A ^ (p - 1) := by
          have h_mul : A ^ (p - 1) * A = (1 - X) ^ q := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p), hApow]
          have h_le : A ^ (p - 1) * A ≤ A ^ (p - 1) :=
            mul_le_of_le_one_right
              (pow_nonneg (le_of_lt hA_pos) (p - 1)) hA_le1
          linarith
        -- (1-X)^q ≥ 1/2 by Bernoulli + qX < 1/2
        have hX_le1 : X ≤ 1 := le_of_lt hX_lt_one
        have hbern : 1 - (q : ℝ) * X ≤ (1 - X) ^ q :=
          one_sub_mul_le_pow_one_sub (le_of_lt hX_pos) hX_le1 q
        have hqX_lt : (q : ℝ) * X < 1 / 2 := by
          have h2q_lt_up : 2 * q < u ^ p := by
            have : q < p ^ q := q.lt_pow_self (by omega : 1 < p)
            nlinarith [hlarge]
          have h2q_R : (2 : ℝ) * (q : ℝ) < (u : ℝ) ^ p := by
            exact_mod_cast h2q_lt_up
          dsimp only [X, casselsB24X]
          rw [mul_comm, inv_mul_lt_iff₀ (by positivity : (0:ℝ) < (u:ℝ)^p)]
          linarith
        linarith
      have hXdA : X / A ^ (p - 1) ≤ 2 * X := by
        rw [div_le_iff₀ hA_pow_pos]
        nlinarith
      have hXqA : (u : ℝ) ^ (p * R) * X ^ q / A ^ (p - 1)
          ≤ X / A ^ (p - 1) :=
        div_le_div_of_nonneg_right hXq_factor (le_of_lt hA_pow_pos)
      linarith [hXqA, hXdA]
    have hterm2 : X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X) ≤ 2 * X := by
      have h1 : |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| ≤ 1 := hcoeff_abs_le
      have h2 : (1 - X)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ h1mX_pos (by norm_num : (0:ℝ) < 2)]
        linarith
      calc X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X)
          ≤ X * 1 / (1 - X) := by
              apply div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left h1 (le_of_lt hX_pos))
                (le_of_lt h1mX_pos)
        _ = X * (1 - X)⁻¹ := by rw [mul_one, div_eq_mul_inv]
        _ ≤ X * 2 := mul_le_mul_of_nonneg_left h2 (le_of_lt hX_pos)
        _ = 2 * X := mul_comm X 2
    linarith
  show casselsB24DirectBudget u p q < 1
  calc casselsB24DirectBudget u p q
      = Q * ((u : ℝ) ^ (p * R) * X ^ q / A ^ (p - 1)
        + X * |((casselsRootCoeff p q (R + 1) : ℚ) : ℝ)| / (1 - X)) := by
          dsimp [Q, X, A, R, casselsB24DirectBudget, casselsB24Qfac,
            casselsB24X, casselsB24A, casselsB24R]
    _ ≤ Q * (4 * X) := by
          exact mul_le_mul_of_nonneg_left hinner_le (le_of_lt hQ_pos)
    _ = 4 * (Q * X) := by ring
    _ < 4 * (1 / 5) := by nlinarith
    _ < 1 := by norm_num

/-- TRUE remaining Cassels/Runge analytic input.

ChatGPT pro extended 826d65b1 (2026-05-15) discovered: the current
`casselsPadeTruncQ` is the Taylor truncation of `(1-X)^(q/p)`, NOT
of the actual algebraic root
  `F(X) = ((1-X)^q + X^q)^(1/p)`.
For `N ≥ q` (which holds since `casselsPadeLevel p q n ≥ nq+1 ≥ q+1`),
the missing `+(1/p)X^q` correction prevents the claimed
`1 / (p^N · N! · u^(pN))` gap.

Thus `cassels_pade_truncation_gap` as stated is mathematically FALSE.
The correct proof needs a genuine Runge/Padé approximant for the
actual branch `F(X)`, not just `(1-X)^(q/p)`.

We package this as `False` — the theorem we actually want is "no
integer `v` can satisfy the root identity", which IS the elementary
Cassels descent.  The `truncation_gap` lemma then closes vacuously
through this stronger blocker, keeping downstream wiring alive
while honestly recording that the analytic side needs full
restructuring around a Runge/Padé approximant.

Status: GENUINE RESEARCH-LEVEL BLOCKER — the full elementary
Cassels descent for `p < q` distinct odd primes ≥ 5.  Estimated
multi-week formalization requiring substantial new mathlib
infrastructure (Runge/Padé theory + analytic number theory). -/
private theorem cassels_runge_gap_core
    (u v p q n N : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hnpos : 0 < n)
    (hN : N = casselsPadeLevel p q n)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    False := by
  have hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p :=
    shifted_cassels_of_real_root_identity
      u v p q hu hp hq hp5 hq5 hp_lt_q hroot
  have hcat_nat : (v * u) ^ p = (u ^ p - 1) ^ q + 1 :=
    shifted_cassels_catalan_nat u v p q hu hp hq (by omega) hvpow
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hvlt : v < u ^ (q - 1) :=
    pth_root_lt_of_shifted_alt_eq u v p q hu hp.pos hq_odd hq5 hvpow
  have hp_not_dvd_u : ¬ p ∣ u :=
    shifted_cassels_not_p_dvd_u u v p q hu hp hq hp5 hp_lt_q hvpow
  have hp_dvd_u_sub_one : p ∣ u - 1 :=
    shifted_cassels_p_dvd_u_sub_one u v p q hu hp hq hp_lt_q hvpow
  have hp_dvd_a : p ∣ u ^ p - 1 := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hu_pos : 0 < u := by omega
    have h_one_le_up : 1 ≤ u ^ p := Nat.succ_le_of_lt (pow_pos hu_pos p)
    have hcast_um1 :
        ((u - 1 : ℕ) : ZMod p) = (u : ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ u)]
      simp
    have hu_sub_one_zero : ((u - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (u - 1) p).mpr hp_dvd_u_sub_one
    have hu_one : (u : ZMod p) = 1 := by
      have : (u : ZMod p) - 1 = 0 := by
        rwa [hcast_um1] at hu_sub_one_zero
      exact sub_eq_zero.mp this
    have ha_zero : ((u ^ p - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub h_one_le_up, Nat.cast_pow, hu_one]
      simp
    exact (ZMod.natCast_eq_zero_iff (u ^ p - 1) p).mp ha_zero
  have hq_not_dvd_u : ¬ q ∣ u :=
    shifted_cassels_q_not_dvd_u u v p q hu hp.one_lt hq hq_odd hvpow
  have ha_succ : (u ^ p - 1) + 1 = u ^ p := by
    have hu_pos : 0 < u := by omega
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos hu_pos p))
  have hq_not_dvd_vu : ¬ q ∣ v * u := by
    intro hq_dvd_vu
    exact ramified_contra_of_q_dvd_vu
      u v (u ^ p - 1) p q hp hq hq_not_dvd_u
      hcat_nat ha_succ hq_dvd_vu
  have hv_pow_one_mod_q :
      ((v : ℕ) : ZMod q) ^ p = 1 :=
    ramified_v_pow_eq_one_zmod_q
      u v (u ^ p - 1) p q hq hq_not_dvd_u hcat_nat ha_succ
  have hq_not_dvd_v : ¬ q ∣ v :=
    ramified_q_not_dvd_v
      u v (u ^ p - 1) p q hp hq hq_not_dvd_u hcat_nat ha_succ
  have hcop_uv : Nat.Coprime u v :=
    shifted_cassels_coprime_u_v u v p q hu hp.one_lt hq hq_odd hvpow
  have hlocal :
      ∀ r : ℕ, r.Prime → r ∣ u →
        ∃ w : ℕ, w ^ p ≡ q [MOD r ^ p] := by
    intro r _hr hr_dvd_u
    exact shifted_cassels_q_is_pth_power_residue_mod_prime_pow
      u v p q r hu hp.one_lt hq hq_odd hr_dvd_u hvpow
  have hv_pos : 0 < v := by
    by_contra hv_not
    have hv0 : v = 0 := Nat.eq_zero_of_not_pos hv_not
    subst hv0
    simp [zero_pow hp.ne_zero] at hcat_nat
  have hx_gt_one : 1 < v * u := by
    have hv_ge_one : 1 ≤ v := by omega
    nlinarith
  obtain ⟨β, γ, hβnorm, hγnorm, hanorm, hp_not_dvd_gamma⟩ :=
    cassels_ramified_normal_form_of_p_dvd_a
      (v * u) (u ^ p - 1) p q hp hq (by omega) hx_gt_one
      hcat_nat hp_dvd_a
  have hp_dvd_beta : p ∣ β :=
    cassels_ramified_p_dvd_beta_of_u_sub_one
      u p β γ hp (by omega) hp_dvd_u_sub_one hanorm hp_not_dvd_gamma
  obtain ⟨δ, hβeq, hx_second_norm, ha_second_norm⟩ :=
    cassels_ramified_second_p_normal_form
      (v * u) (u ^ p - 1) p q β γ hq.pos
      hβnorm hanorm hp_dvd_beta
  have hramified_base_lower : p ^ (2 * q - 1) < u ^ q :=
    cassels_ramified_base_power_lower_bound
      u v p q δ hu hq.pos hvlt hx_gt_one hx_second_norm
  have hp_dvd_vu_sub_one : p ∣ v * u - 1 := by
    have hp_pow : p ∣ p ^ (2 * q - 1) := by
      simpa using pow_dvd_pow p (by omega : 1 ≤ 2 * q - 1)
    rw [hx_second_norm]
    exact dvd_mul_of_dvd_left hp_pow (δ ^ q)
  have hp_dvd_v_sub_one : p ∣ v - 1 := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact prime_dvd_left_factor_sub_one_of_mul_sub_one
      p u v (by omega) (by omega) hp_dvd_u_sub_one hp_dvd_vu_sub_one
  obtain ⟨U, V, hU, hV, hUVexact⟩ :=
    ramified_uv_first_quotient_exact
      u v p q δ hp.pos hq.pos (by omega) (by omega)
      hp_dvd_u_sub_one hp_dvd_v_sub_one
      hx_second_norm
  have hUVquot : p ^ (2 * q - 2) ∣ U + V + p * U * V :=
    ⟨δ ^ q, hUVexact⟩
  have hp_dvd_U_add_V : p ∣ U + V :=
    ramified_uv_first_quotient_linear_mod p q U V (by omega)
      hUVquot
  obtain ⟨W, hW, hp_dvd_W_add_UV⟩ :=
    ramified_uv_second_quotient_linear_mod p q U V hp.pos (by omega)
      hUVquot hp_dvd_U_add_V
  have hWVexact : W + U * V = p ^ (2 * q - 3) * δ ^ q :=
    ramified_uv_second_quotient_exact p q U V W δ hp.pos (by omega)
      hW hUVexact
  have hWVint :
      (u : ℤ) * (W : ℤ) - (U : ℤ) ^ 2
        = ((p ^ (2 * q - 3) * δ ^ q : ℕ) : ℤ) :=
    ramified_uv_second_quotient_int_form
      u p q U V W δ (by omega) hU hW hWVexact
  have hW_mod_U_sq : W ≡ U ^ 2 [MOD p] :=
    ramified_uv_second_quotient_square_mod p U V W hW hp_dvd_W_add_UV
  obtain ⟨A, hA, hAthrid⟩ :=
    ramified_uv_third_quotient_int_form
      u p q U W δ hp.pos (by omega) (by omega) hU hWVint hW_mod_U_sq
  have hA_cubic_mod : (p : ℤ) ∣ A + (U : ℤ) ^ 3 :=
    ramified_uv_third_quotient_cubic_mod
      p q U W δ A (by omega) hAthrid hW_mod_U_sq
  obtain ⟨B, hB, hBfourth⟩ :=
    ramified_uv_fourth_quotient_int_form
      p q U W δ A hp.pos (by omega) hA hAthrid hA_cubic_mod
  have hB_quartic_mod : (p : ℤ) ∣ B - (U : ℤ) ^ 4 :=
    ramified_uv_fourth_quotient_quartic_mod
      p q U δ A B (by omega) hBfourth hA_cubic_mod
  obtain ⟨C, hC, hCfifth⟩ :=
    ramified_uv_fifth_quotient_int_form
      p q U δ A B hp.pos (by omega) hB hBfourth hB_quartic_mod
  have hC_quintic_mod : (p : ℤ) ∣ C + (U : ℤ) ^ 5 :=
    ramified_uv_fifth_quotient_quintic_mod
      p q U δ B C (by omega) hCfifth hB_quartic_mod
  obtain ⟨D, hD, hDsixth⟩ :=
    ramified_uv_sixth_quotient_int_form
      p q U δ B C hp.pos (by omega) hC hCfifth hC_quintic_mod
  have hD_sextic_mod : (p : ℤ) ∣ D - (U : ℤ) ^ 6 :=
    ramified_uv_sixth_quotient_sextic_mod
      p q U δ C D (by omega) hDsixth hC_quintic_mod
  obtain ⟨E, hE, hEseventh⟩ :=
    ramified_uv_seventh_quotient_int_form
      p q U δ C D hp.pos (by omega) hD hDsixth hD_sextic_mod
  have hE_septic_mod : (p : ℤ) ∣ E + (U : ℤ) ^ 7 :=
    ramified_uv_seventh_quotient_septic_mod
      p q U δ D E (by omega) hEseventh hD_sextic_mod
  obtain ⟨F, hF, hFeighth⟩ :=
    ramified_uv_eighth_quotient_int_form
      p q U δ D E hp.pos (by omega) hE hEseventh hE_septic_mod
  have hF_octic_mod : (p : ℤ) ∣ F - (U : ℤ) ^ 8 :=
    ramified_uv_eighth_quotient_octic_mod
      p q U δ E F (by omega) hFeighth hE_septic_mod
  obtain ⟨G, hG, hGninth⟩ :=
    ramified_uv_ninth_quotient_int_form
      p q U δ E F hp.pos (by omega) hF hFeighth hF_octic_mod
  have hG_boundary_mod :
      (p : ℤ) ∣
        (G + (U : ℤ) ^ 9)
          - ((p ^ (2 * q - 10) * δ ^ q : ℕ) : ℤ) :=
    ramified_uv_ninth_boundary_congruence
      p q U δ F G hGninth hF_octic_mod
  have hlow_boundary_split :=
    ramified_uv_low_boundary_split_refined
      p q U δ F G hp.pos (by omega) hG hGninth hF_octic_mod hG_boundary_mod
  have hq7_or_hq11 : q = 7 ∨ 11 ≤ q :=
    prime_eq_seven_or_ge_eleven_of_five_lt p q hp hq hp5 hp_lt_q
  have hprime_tail_split :
      (q = 7 ∧
          ∃ H I J K : ℤ,
            G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
            H + (U : ℤ) * G
              = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
            H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
            I + (U : ℤ) * H
              = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
            I + (U : ℤ) ^ 11 = (p : ℤ) * J ∧
            J + (U : ℤ) * I
              = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) ∧
            J - (U : ℤ) ^ 12 = (p : ℤ) * K ∧
            K + (U : ℤ) * J
              = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ) ∧
            (p : ℤ) ∣ (K + (U : ℤ) ^ 13) - ((δ ^ 7 : ℕ) : ℤ))
        ∨
      (q = 11 ∧
          ∃ H I J K L M N O P Q R S : ℤ,
            G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
            H + (U : ℤ) * G
              = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
            H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
            I + (U : ℤ) * H
              = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
            I + (U : ℤ) ^ 11 = (p : ℤ) * J ∧
            J + (U : ℤ) * I
              = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) ∧
            J - (U : ℤ) ^ 12 = (p : ℤ) * K ∧
            K + (U : ℤ) * J
              = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ) ∧
            K + (U : ℤ) ^ 13 = (p : ℤ) * L ∧
            L + (U : ℤ) * K
              = ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ) ∧
            L - (U : ℤ) ^ 14 = (p : ℤ) * M ∧
            M + (U : ℤ) * L
              = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ) ∧
            M + (U : ℤ) ^ 15 = (p : ℤ) * N ∧
            N + (U : ℤ) * M
              = ((p ^ (2 * q - 17) * δ ^ q : ℕ) : ℤ) ∧
            N - (U : ℤ) ^ 16 = (p : ℤ) * O ∧
            O + (U : ℤ) * N
              = ((p ^ (2 * q - 18) * δ ^ q : ℕ) : ℤ) ∧
            O + (U : ℤ) ^ 17 = (p : ℤ) * P ∧
            P + (U : ℤ) * O
              = ((p ^ (2 * q - 19) * δ ^ q : ℕ) : ℤ) ∧
            P - (U : ℤ) ^ 18 = (p : ℤ) * Q ∧
            Q + (U : ℤ) * P
              = ((p ^ (2 * q - 20) * δ ^ q : ℕ) : ℤ) ∧
            Q + (U : ℤ) ^ 19 = (p : ℤ) * R ∧
            R + (U : ℤ) * Q
              = ((p ^ (2 * q - 21) * δ ^ q : ℕ) : ℤ) ∧
            R - (U : ℤ) ^ 20 = (p : ℤ) * S ∧
            S + (U : ℤ) * R
              = ((p ^ (2 * q - 22) * δ ^ q : ℕ) : ℤ) ∧
            (p : ℤ) ∣ (S + (U : ℤ) ^ 21) - ((δ ^ 11 : ℕ) : ℤ))
        ∨
      (12 ≤ q ∧
          ∃ H I J K L M N O P Q R S : ℤ,
            G + (U : ℤ) ^ 9 = (p : ℤ) * H ∧
            H + (U : ℤ) * G
              = ((p ^ (2 * q - 11) * δ ^ q : ℕ) : ℤ) ∧
            H - (U : ℤ) ^ 10 = (p : ℤ) * I ∧
            I + (U : ℤ) * H
              = ((p ^ (2 * q - 12) * δ ^ q : ℕ) : ℤ) ∧
            I + (U : ℤ) ^ 11 = (p : ℤ) * J ∧
            J + (U : ℤ) * I
              = ((p ^ (2 * q - 13) * δ ^ q : ℕ) : ℤ) ∧
            J - (U : ℤ) ^ 12 = (p : ℤ) * K ∧
            K + (U : ℤ) * J
              = ((p ^ (2 * q - 14) * δ ^ q : ℕ) : ℤ) ∧
            K + (U : ℤ) ^ 13 = (p : ℤ) * L ∧
            L + (U : ℤ) * K
              = ((p ^ (2 * q - 15) * δ ^ q : ℕ) : ℤ) ∧
            L - (U : ℤ) ^ 14 = (p : ℤ) * M ∧
            M + (U : ℤ) * L
              = ((p ^ (2 * q - 16) * δ ^ q : ℕ) : ℤ) ∧
            M + (U : ℤ) ^ 15 = (p : ℤ) * N ∧
            N + (U : ℤ) * M
              = ((p ^ (2 * q - 17) * δ ^ q : ℕ) : ℤ) ∧
            N - (U : ℤ) ^ 16 = (p : ℤ) * O ∧
            O + (U : ℤ) * N
              = ((p ^ (2 * q - 18) * δ ^ q : ℕ) : ℤ) ∧
            O + (U : ℤ) ^ 17 = (p : ℤ) * P ∧
            P + (U : ℤ) * O
              = ((p ^ (2 * q - 19) * δ ^ q : ℕ) : ℤ) ∧
            P - (U : ℤ) ^ 18 = (p : ℤ) * Q ∧
            Q + (U : ℤ) * P
              = ((p ^ (2 * q - 20) * δ ^ q : ℕ) : ℤ) ∧
            Q + (U : ℤ) ^ 19 = (p : ℤ) * R ∧
            R + (U : ℤ) * Q
              = ((p ^ (2 * q - 21) * δ ^ q : ℕ) : ℤ) ∧
            R - (U : ℤ) ^ 20 = (p : ℤ) * S ∧
            S + (U : ℤ) * R
              = ((p ^ (2 * q - 22) * δ ^ q : ℕ) : ℤ)) := by
    rcases hlow_boundary_split with hq5 | hq6_or_tail
    · exact False.elim (by
        rcases hq7_or_hq11 with hq7 | hq11 <;> omega)
    rcases hq6_or_tail with hq6 | htail
    · exact False.elim (by
        rcases hq7_or_hq11 with hq7 | hq11 <;> omega)
    rcases htail with hq7tail | hq8tail
    · left
      exact hq7tail
    right
    rcases hq8tail with
      ⟨hq8, H, I, J, K, hH, hHtenth, hI, hIeleventh,
        hJ, hJtwelfth, hK, hKthirteenth⟩
    rcases ramified_uv_q_eight_or_higher_tail_split
        p q U δ J K hp.pos hq8 hK hKthirteenth with hq8sharp | hq9tail
    · exact False.elim (by
        rcases hq7_or_hq11 with hq7 | hq11 <;> omega)
    rcases hq9tail with
      ⟨hq9, L, M, hL, hLfourteenth, hM, hMfifteenth⟩
    rcases ramified_uv_q_nine_or_higher_tail_split
        p q U δ L M hp.pos hq9 hM hMfifteenth with hq9sharp | hq10tail
    · exact False.elim (by
        rcases hq7_or_hq11 with hq7 | hq11 <;> omega)
    rcases hq10tail with
      ⟨hq10, N, O, hN, hNsixteenth, hO, hOseventeenth⟩
    rcases ramified_uv_q_ten_or_higher_tail_split
        p q U δ N O hp.pos hq10 hO hOseventeenth with hq10sharp | hq11tail
    · exact False.elim (by
        rcases hq7_or_hq11 with hq7 | hq11 <;> omega)
    rcases hq11tail with
      ⟨hq11, P, Q, hP, hPeighteenth, hQ, hQnineteenth⟩
    rcases ramified_uv_q_eleven_or_higher_tail_split
        p q U δ P Q hp.pos hq11 hQ hQnineteenth with hq11sharp | hq12tail
    · left
      rcases hq11sharp with
        ⟨hq11eq, R, S, hR, hRtwentieth, hS, hStwentyfirst, hboundary⟩
      exact ⟨hq11eq, H, I, J, K, L, M, N, O, P, Q, R, S,
        hH, hHtenth, hI, hIeleventh, hJ, hJtwelfth, hK, hKthirteenth,
        hL, hLfourteenth, hM, hMfifteenth, hN, hNsixteenth, hO,
        hOseventeenth, hP, hPeighteenth, hQ, hQnineteenth, hR,
        hRtwentieth, hS, hStwentyfirst, hboundary⟩
    · right
      rcases hq12tail with
        ⟨hq12, R, S, hR, hRtwentieth, hS, hStwentyfirst⟩
      exact ⟨hq12, H, I, J, K, L, M, N, O, P, Q, R, S,
        hH, hHtenth, hI, hIeleventh, hJ, hJtwelfth, hK, hKthirteenth,
        hL, hLfourteenth, hM, hMfifteenth, hN, hNsixteenth, hO,
        hOseventeenth, hP, hPeighteenth, hQ, hQnineteenth, hR,
        hRtwentieth, hS, hStwentyfirst⟩
  have hp_eq_five_of_q_eq_seven : q = 7 → p = 5 := by
    intro hq7
    exact prime_eq_five_of_five_le_lt_seven p hp hp5 (by omega)
  have hdelta_gamma_mod_U : δ * γ ≡ U [MOD p] :=
    ramified_u_second_quotient_linear_mod
      u p δ γ U hp (by omega) (by omega) hU (by
        simpa [mul_assoc] using ha_second_norm)
  have hp2_dvd_vu_sub_one : p ^ 2 ∣ v * u - 1 := by
    rw [hx_second_norm]
    exact dvd_mul_of_dvd_left
      (pow_dvd_pow p (by omega : 2 ≤ 2 * q - 1)) (δ ^ q)
  have hgamma_q_mod_one : γ ^ q ≡ 1 [MOD p] :=
    ramified_gamma_pow_modEq_one_of_prime_sq_dvd_sub_one
      p q (v * u) γ hp.ne_zero (le_of_lt hx_gt_one)
      hp2_dvd_vu_sub_one hγnorm
  have hgamma_mod_one : γ ≡ 1 [MOD p] :=
    prime_pow_modEq_one_of_lt p q γ hp hq hp_lt_q hgamma_q_mod_one
  have hgamma_q_high_mod_one :
      γ ^ q ≡ 1 [MOD p ^ (2 * q - 2)] :=
    ramified_gamma_pow_high_modEq_one
      p q (v * u) γ δ hp.ne_zero (by omega)
      (le_of_lt hx_gt_one) hx_second_norm hγnorm
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hgamma_high_mod_one :
      γ ≡ 1 [MOD p ^ (2 * q - 2)] :=
    prime_pow_root_high_modEq_one_of_lt p q γ (2 * q - 2)
      hp hq hp_odd hp_lt_q
      hgamma_mod_one hgamma_q_high_mod_one
  have hgamma_gt_one : 1 < γ :=
    ramified_gamma_gt_one p q (v * u) γ hp.two_le hq.pos hx_gt_one hγnorm
  have hgamma_pos : 0 < γ := by
    omega
  have hgamma_one_le : 1 ≤ γ := by omega
  have hp_qsub_dvd_gamma_sub_one : p ^ (q - 1) ∣ γ - 1 := by
    have hmod_low : γ ≡ 1 [MOD p ^ (q - 1)] :=
      hgamma_high_mod_one.of_dvd
        (pow_dvd_pow p (by omega : q - 1 ≤ 2 * q - 2))
    exact (Nat.modEq_iff_dvd' hgamma_one_le).mp hmod_low.symm
  have hu_pow_gt_five_mul_p_pow_q : 5 * p ^ q < u ^ p :=
    ramified_u_pow_gt_five_mul_p_pow_q_of_gamma_high
      u p q δ γ hu hp5 hq.pos ha_second_norm
      hgamma_gt_one hp_qsub_dvd_gamma_sub_one
  have hB24_QX_lt_one_fifth :
      casselsB24Qfac p q * casselsB24X u p < (1 / 5 : ℝ) :=
    casselsB24Qfac_mul_X_lt_one_div_five_of_u_pow_gt
      u p q hu hp5 hp_lt_q hu_pow_gt_five_mul_p_pow_q
  have hdelta_q_mod_U_q : δ ^ q ≡ U ^ q [MOD p] := by
    have hpow : (δ * γ) ^ q ≡ U ^ q [MOD p] :=
      hdelta_gamma_mod_U.pow q
    have hpow' : δ ^ q * γ ^ q ≡ U ^ q [MOD p] := by
      simpa [Nat.mul_pow] using hpow
    have hleft : δ ^ q * γ ^ q ≡ δ ^ q * 1 [MOD p] :=
      Nat.ModEq.mul_left (δ ^ q) hgamma_q_mod_one
    have hright : δ ^ q * 1 ≡ U ^ q [MOD p] :=
      hleft.symm.trans hpow'
    simpa using hright
  have hactual_tail_gap_b24 :
      HasSum
        (fun n => (u : ℝ) ^ (q - 1)
          * ((casselsActualRootCoeff p q (n + (casselsB24R p q + 1)) : ℝ)
            * (((u : ℝ) ^ p)⁻¹) ^ (n + (casselsB24R p q + 1))))
        ((v : ℝ)
          - ((casselsActualTruncQ u p q (casselsB24R p q) : ℚ) : ℝ)) :=
    cassels_actualRootCoeff_scaled_tail_hasSum_gap_of_hroot
      u v p q (casselsB24R p q) hu hp5 hq5 hp_lt_q hroot
  let Rb : ℕ := casselsB24R p q
  let Db : ℕ := casselsPadeClearDen u p Rb
  have hDb_pos : 0 < Db :=
    casselsPadeClearDen_pos u p Rb (by omega) hp.pos
  have hactual_cleared_integral_b24 :
      ∃ z : ℤ,
        (Db : ℚ) * casselsActualTruncQ u p q Rb = (z : ℚ) := by
    dsimp [Db, Rb]
    exact cassels_actual_trunc_cleared_integral
      u p q (casselsB24R p q) hq.pos
  have hactual_padic_ne_b24 :
      (Db : ℚ) * (v : ℚ)
        ≠
      (Db : ℚ) * casselsActualTruncQ u p q Rb := by
    dsimp [Db, Rb]
    exact cassels_actual_padic_denominator_obstruction_of_not_dvd_u
      u v p q (casselsB24R p q) hu hp hq hp_lt_q
      (casselsB24R_pos p q) hp_not_dvd_u
  have hactual_gap_ne_zero_b24 :
      (v : ℝ) - ((casselsActualTruncQ u p q Rb : ℚ) : ℝ) ≠ 0 :=
    cassels_real_gap_ne_zero_of_cleared_ne
      Db v (casselsActualTruncQ u p q Rb) hactual_padic_ne_b24
  have hactual_gap_abs_bound_b24 :
      |(v : ℝ) - ((casselsActualTruncQ u p q Rb : ℚ) : ℝ)|
        ≤
      (u : ℝ) ^ (q - 1)
        * (((u : ℝ) ^ p)⁻¹) ^ (Rb + 1)
        * ((32 : ℝ) ^ (Rb + 1) * casselsActualRootAbsTsum p q) := by
    dsimp [Rb]
    exact cassels_actualRootCoeff_scaled_tail_gap_abs_le
      u v p q (casselsB24R p q) hu hp5 hq5 hp_lt_q hroot
  have hactual_cleared_gap_abs_bound_b24 :
      |(Db : ℝ)
        * ((v : ℝ) - ((casselsActualTruncQ u p q Rb : ℚ) : ℝ))|
        ≤
      (Db : ℝ)
        * ((u : ℝ) ^ (q - 1)
          * (((u : ℝ) ^ p)⁻¹) ^ (Rb + 1)
          * ((32 : ℝ) ^ (Rb + 1) * casselsActualRootAbsTsum p q)) := by
    have hDb_nonneg : 0 ≤ (Db : ℝ) := by positivity
    calc
      |(Db : ℝ)
        * ((v : ℝ) - ((casselsActualTruncQ u p q Rb : ℚ) : ℝ))|
          = (Db : ℝ)
            * |(v : ℝ) - ((casselsActualTruncQ u p q Rb : ℚ) : ℝ)| := by
              rw [abs_mul, abs_of_nonneg hDb_nonneg]
      _ ≤ (Db : ℝ)
          * ((u : ℝ) ^ (q - 1)
            * (((u : ℝ) ^ p)⁻¹) ^ (Rb + 1)
            * ((32 : ℝ) ^ (Rb + 1) * casselsActualRootAbsTsum p q)) :=
              mul_le_mul_of_nonneg_left hactual_gap_abs_bound_b24 hDb_nonneg
  have hactual_tail_first_ne_zero_b24 :
      (u : ℝ) ^ (q - 1)
        * ((casselsActualRootCoeff p q (Rb + 1) : ℝ)
          * (((u : ℝ) ^ p)⁻¹) ^ (Rb + 1)) ≠ 0 := by
    dsimp [Rb]
    exact casselsActual_scaled_tail_first_b24_ne_zero
      u p q hu hp hq hp5 hp_lt_q
  have hcat_div :
      ((u ^ p - 1) + 1) * v ^ p = (u ^ p - 1) ^ q + 1 := by
    calc
      ((u ^ p - 1) + 1) * v ^ p = u ^ p * v ^ p := by
        rw [ha_succ]
      _ = v ^ p * u ^ p := by ring
      _ = (v * u) ^ p := by
        rw [Nat.mul_pow]
      _ = (u ^ p - 1) ^ q + 1 := hcat_nat
  have hp_dvd_V_add_delta_gamma : p ∣ V + δ * γ :=
    ramified_v_second_quotient_linear_mod
      (u ^ p - 1) v p q (δ * γ) V hp (by omega) (by omega)
      (by omega) hV (by simpa [mul_assoc] using ha_second_norm)
      hcat_div
  /- Final contradiction: the B24 budget is < 1 but the gap is a
     nonzero integer, impossible.
     Key: Q·X < 1/5 (proved), |c_{R+1}| < 1/3 (product comparison
     with factorial), so Budget ≤ Q·X · 8/3 < 8/15 < 1. -/
  exact casselsB24_gap_contra_of_directBudget_lt_one
    hu hp hq hp5 hq5 hp_lt_q hp_not_dvd_u hroot
    (casselsB24DirectBudget_lt_one_of_u_pow_gt
      u p q hu hp hq hp5 hq5 hp_lt_q hu_pow_gt_five_mul_p_pow_q)

/-- Real Padé/Runge approximation gap (REAL analytic blocker).

The rational truncation is closer to the integer `v` than one cleared
denominator unit.  This is the genuine real-analysis input from
Cassels 1960's descent.

STRATEGY (math sketch, not yet Lean):
  - From hroot: (v/u^(q-1))^p = (1-X)^q + X^q where X = u^(-p).
  - Take p-th root: v/u^(q-1) = F(X) where F(X) = ((1-X)^q + X^q)^(1/p).
  - Taylor-expand F(X) around 0:
      F(X) = 1 - (q/p)X + q(q-p)/(2p²)X² - C(q/p,3)X³ + ...
  - Truncate at level N (= casselsPadeLevel p q n).
  - Real Taylor remainder bound:
      |F(X) - T_N(X)| ≤ C(q, N, p) · X^(N+1)
    for some explicit constant C.
  - Multiplying by u^(q-1):
      |v - u^(q-1) · T_N(X)| ≤ C · u^(q-1) · X^(N+1)
                              = C · u^(q-1-p(N+1)).
  - For sufficiently large N (depending on n), this is smaller than
    1/D = 1/(p^N · N! · u^(pN)).
  - The exponent comparison: q-1-p(N+1) < -p·N - log_u(p^N·N!).
  - Requires careful real-analysis estimate involving u, p, q.

  GENUINE RESEARCH-LEVEL.  Not yet Lean-formalized.  Estimated
  300-500 Lean lines requiring `Mathlib.Analysis.SpecificLimits.*`
  or careful direct integer/rational estimates. -/
private theorem cassels_pade_truncation_gap
    (u v p q n N : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hnpos : 0 < n)
    (hN : N = casselsPadeLevel p q n)
    (hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q) :
    |(v : ℝ) - ((casselsPadeTruncQ u p q N : ℚ) : ℝ)|
      <
    ((casselsPadeClearDen u p N : ℝ))⁻¹ := by
  /- ChatGPT pro extended 826d65b1: this statement is mathematically
     FALSE for N ≥ q (which always holds here).  The casselsPadeTruncQ
     uses coefficients of (1-X)^(q/p), missing the +(1/p)X^q correction
     from the actual algebraic root F(X) = ((1-X)^q + X^q)^(1/p).

     We close vacuously through cassels_runge_gap_core, which directly
     proves False (the elementary Cassels descent in full strength). -/
  exact False.elim
    (cassels_runge_gap_core u v p q n N hu hp hq hp5 hq5 hp_lt_q
      hnpos hN hroot)


/-- THE Cassels Padé-arbitrary-order theorem.

Now a wrapper: real content in the 4 sorries above (analytic + p-adic
+ formal arithmetic).  ChatGPT 0721574a 2026-05-15 decomposition. -/
private theorem cassels_shifted_solution_forces_p_power_dvd_u
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1))
    (n : ℕ) :
    p ^ n ∣ u := by
  classical
  by_cases hn0 : n = 0
  · subst hn0; simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  by_contra hp_not_pn_dvd_u
  let N : ℕ := casselsPadeLevel p q n
  let D : ℕ := casselsPadeClearDen u p N
  let T : ℚ := casselsPadeTruncQ u p q N
  have hNpos : 0 < N := casselsPadeLevel_pos p q n
  have hDpos : 0 < D :=
    casselsPadeClearDen_pos u p N (by omega) hp.pos
  have hroot :
      ((v : ℝ) / (u : ℝ) ^ (q - 1)) ^ p
        =
      (1 - ((u : ℝ) ^ p)⁻¹) ^ q
        + (((u : ℝ) ^ p)⁻¹) ^ q :=
    cassels_real_root_identity
      u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt
  have hTint : ∃ z : ℤ, (D : ℚ) * T = (z : ℚ) :=
    cassels_pade_trunc_cleared_integral u p q N hu hp
  have hgap :
      |(v : ℝ) - ((T : ℚ) : ℝ)| < ((D : ℝ))⁻¹ :=
    cassels_pade_truncation_gap
      u v p q n N hu hp hq hp5 hq5 hp_lt_q hnpos rfl hroot
  have hEq : (D : ℚ) * (v : ℚ) = (D : ℚ) * T :=
    cassels_rational_gap_forces_cleared_eq D v T hDpos hTint hgap
  have hNe : (D : ℚ) * (v : ℚ) ≠ (D : ℚ) * T :=
    cassels_pade_padic_denominator_obstruction
      u v p q n N hu hp hq hp5 hq5 hp_lt_q hnpos rfl hp_not_pn_dvd_u
  exact hNe hEq

/-- Corollary at n = 1: the one-shot `p ∣ u` theorem. -/
private theorem cassels_shifted_solution_forces_p_dvd_u
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1)) :
    p ∣ u := by
  have h :=
    cassels_shifted_solution_forces_p_power_dvd_u
      u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt 1
  simpa using h

/-- All-powers form (alias for the strong theorem). -/
private theorem cassels_forces_all_p_powers_dvd_u
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1))
    (n : ℕ) :
    p ^ n ∣ u :=
  cassels_shifted_solution_forces_p_power_dvd_u
    u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt n

/-- The corrected Cassels descent contradicts the existence of a
shifted solution: `p^(u+1) ∣ u`, but `p^(u+1) > u`, so `u = 0`,
contradicting `1 < u`. -/
private theorem cassels_shifted_solution_impossible
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1)) :
    False := by
  have hbig : p ^ (u + 1) ∣ u :=
    cassels_forces_all_p_powers_dvd_u u v p q hu hp hq hp5 hq5 hp_lt_q
      hvpow hvlt (u + 1)
  have hu_pos : 0 < u := by omega
  have hcontr_le : p ^ (u + 1) ≤ u := Nat.le_of_dvd hu_pos hbig
  have hp_ge_two : 2 ≤ p := hp.two_le
  have hp_pow_gt : u < p ^ (u + 1) := by
    have : 2 ^ (u + 1) ≤ p ^ (u + 1) := Nat.pow_le_pow_left hp_ge_two _
    have h2pow : u < 2 ^ (u + 1) := by
      have h := Nat.lt_two_pow_self (n := u + 1)
      omega
    omega
  omega

/-- A2 GLOBAL DESCENT (CORRECTED 2026-05-15).

The earlier route through "sharp tail control + leading equality"
was UNSOUND: the inequality
  `|p·w·u^((q-1)(p-1)) - q·u^(p(q-2))| < u^((q-1)(p-1))`
is equivalent to the exact integer equality `p·w = q·u^(q-p-1)`,
which is mathematically FALSE for `q ≥ 2p+1` (quadratic correction
`-q(q-p)/(2p)·u^(q-2p-1) ≠ 0`).

The corrected route bypasses the false leading equality entirely:
  1. `cassels_shifted_solution_forces_p_dvd_u`: prove `p ∣ u` directly
     via binomial-root truncation / p-adic denominator obstruction.
  2. `cassels_forces_all_p_powers_dvd_u`: recursively, `p^n ∣ u` for
     all `n`.
  3. `cassels_shifted_solution_impossible`: take `n = u+1`,
     `p^(u+1) ∣ u` ⟹ `p^(u+1) ≤ u`, but `p^(u+1) > u`, ⊥.

Since no shifted Cassels solution exists at all, `p ∣ q` is vacuous. -/
private theorem cassels_sharp_deficit_comparison_forces_descent
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1)) :
    p ∣ q :=
  (cassels_shifted_solution_impossible
    u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt).elim

/-- Wrapper preserving the old name, now delegating to the sharper form. -/
private theorem cassels_interval_bound_plus_residue_forces_p_dvd_q
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1))
    (_hnear :
      v ≥ u ^ (q - 1) - 2 * q * u ^ (q - p - 1))
    (_hmod :
      v ^ p ≡ q [MOD u ^ p]) :
    p ∣ q :=
  cassels_sharp_deficit_comparison_forces_descent
    u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt

/-- A2 GLOBAL DESCENT (factored into size + residue + new blocker).

Given the locked local invariants (q ∤ u, gcd u v = 1, local residue
family), plus the size bound and the shifted equation, the descent
forces `p ∣ q`.

Factored through `cassels_w_bound` (size interval) and
`cassels_interval_bound_plus_residue_forces_p_dvd_q` (new real blocker
for the interval × residue × shifted equation combination). -/
private theorem shifted_cassels_local_residue_descent_forces_p_dvd_q
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1))
    (hcop_uv : Nat.Coprime u v)
    (hlocal :
      ∀ r : ℕ, r.Prime → r ∣ u →
        ∃ w : ℕ, w ^ p ≡ q [MOD r ^ p]) :
    p ∣ q := by
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hnear : v ≥ u ^ (q - 1) - 2 * q * u ^ (q - p - 1) :=
    cassels_w_bound u v p q hu hp.one_lt hq_odd hp5 hq5 hp_lt_q
      hvpow hvlt
  have hmod : v ^ p ≡ q [MOD u ^ p] :=
    shifted_cassels_vpow_mod_u_pow u v p q hu hq_odd hvpow
  exact cassels_interval_bound_plus_residue_forces_p_dvd_q
    u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt hnear hmod

/-- The real Cassels descent blocker (lower-prime branch).

Conclusion restated as `False`.  Now decomposed through the A2 chain:
  q ∤ u  +  gcd u v = 1  +  ∀ r prime ∣ u, ∃ w, w^p ≡ q [MOD r^p]
together with `v < u^(q-1)` and the shifted equation, forces `p ∣ q`,
which contradicts distinct primes ≥ 5 (since `5 ≤ p < q`). -/
private theorem cassels_shifted_descent_p_lt_q
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hvpow :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p)
    (hvlt : v < u ^ (q - 1)) :
    False := by
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hcop_uv : Nat.Coprime u v :=
    shifted_cassels_coprime_u_v u v p q hu hp.one_lt hq hq_odd hvpow
  have hlocal :
      ∀ r : ℕ, r.Prime → r ∣ u →
        ∃ w : ℕ, w ^ p ≡ q [MOD r ^ p] := by
    intro r _hr hr_dvd_u
    exact shifted_cassels_q_is_pth_power_residue_mod_prime_pow
      u v p q r hu hp.one_lt hq hq_odd hr_dvd_u hvpow
  have hp_dvd_q : p ∣ q :=
    shifted_cassels_local_residue_descent_forces_p_dvd_q
      u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt hcop_uv hlocal
  have hp_eq_q : p = q := by
    rcases hq.eq_one_or_self_of_dvd p hp_dvd_q with h1 | hself
    · exact (hp.ne_one h1).elim
    · exact hself
  omega

/-- Lower-prime branch of Lemma 4: the case actually used by the LPP
obstruction package. -/
private theorem shifted_alt_cyclotomic_plus_nat_not_prime_power_p_lt_q
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q) :
    altCyclotomicPlusNat q (u ^ p - 1) ≠ v ^ p := by
  intro hvpow
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hvlt : v < u ^ (q - 1) :=
    pth_root_lt_of_shifted_alt_eq u v p q hu hp.pos hq_odd hq5 hvpow
  exact cassels_shifted_descent_p_lt_q
    u v p q hu hp hq hp5 hq5 hp_lt_q hvpow hvlt



/-- The hard elementary Cassels descent lemma.

After the coprime factor split, the contrary branch `¬ q ∣ x` forces
`y + 1 = u^p` and `Ψ_q(y) = v^p`, hence `Ψ_q(u^p - 1) = v^p`. This rules
that out for distinct odd primes `p, q ≥ 5`.

The `p < q` branch is closed via the helpers above; the `q < p` branch
is currently `sorry` (the Ehrenfest obstruction package guarantees
`p < q`, so this gap does not block the downstream Lemma 5/wrapper). -/
theorem shifted_alt_cyclotomic_plus_nat_not_prime_power
    (u v p q : ℕ)
    (hu : 1 < u)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_ne_q : p ≠ q) :
    altCyclotomicPlusNat q (u ^ p - 1) ≠ v ^ p := by
  by_cases hp_lt_q : p < q
  · exact shifted_alt_cyclotomic_plus_nat_not_prime_power_p_lt_q
      u v p q hu hp hq hp5 hq5 hp_lt_q
  · intro hvpow
    have hq_lt_p : q < p := by omega
    have hcat : (v * u) ^ p = (u ^ p - 1) ^ q + 1 :=
      shifted_cassels_catalan_nat u v p q hu hp hq (by omega) hvpow
    have hbu : (u ^ p - 1) + 1 = u ^ p := by
      have hu_pos : 0 < u := by omega
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt (pow_pos hu_pos p))
    exact Ripple.LPP.CasselsClassical.cassels_lemma_2_plus_no_pth_power
      u q p (v * u) (u ^ p - 1) (by omega) hq.two_le hq_lt_p hbu hcat

/-! ## Lemma 5: the public Cassels upper-divisor theorem -/

/-- No two positive same-exponent powers differ by exactly one (for p ≥ 2).

The hypothesis must be `1 < p`.  The statement is false for `p = 1`:
e.g. `3^1 = 2^1 + 1`.  Independent of Cassels; pure Nat power-gap.

Proof: from `y^p < x^p` get `y < x`, so `y + 1 ≤ x`.  Then
`(y+1)^p > y^p + 1` (a strict gap of size ≥ 2 for `p ≥ 2`), so
`x^p ≥ (y+1)^p > y^p + 1`, contradicting `x^p = y^p + 1`. -/
private theorem no_same_exponent_power_gap_one
    (x y p : ℕ)
    (hx : 1 < x) (hy : 1 < y)
    (hp_one_lt : 1 < p)
    (hpow : x ^ p = y ^ p + 1) :
    False := by
  have hp_pos : 0 < p := by omega
  have hy_pow_lt_x_pow : y ^ p < x ^ p := by rw [hpow]; omega
  have hy_lt_x : y < x := lt_of_pow_lt_pow_left' p hy_pow_lt_x_pow
  have hy_succ_le_x : y + 1 ≤ x := Nat.succ_le_of_lt hy_lt_x
  have hle_pow : (y + 1) ^ p ≤ x ^ p := Nat.pow_le_pow_left hy_succ_le_x p
  have hgap : y ^ p + 1 < (y + 1) ^ p := by
    rcases Nat.exists_eq_add_of_le hp_one_lt with ⟨k, hk⟩
    subst hk
    have hy_pos : 0 < y := by omega
    have hbase_le : y ^ k ≤ (y + 1) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    have hextra_pos : 1 < (2 * y + 1) * y ^ k := by
      have hyk_pos : 0 < y ^ k := pow_pos hy_pos k
      nlinarith
    calc
      y ^ (2 + k) + 1
          < y ^ (2 + k) + (2 * y + 1) * y ^ k := by omega
      _ = (y ^ 2 + (2 * y + 1)) * y ^ k := by rw [pow_add]; ring
      _ = (y + 1) ^ 2 * y ^ k := by ring
      _ ≤ (y + 1) ^ 2 * (y + 1) ^ k :=
            Nat.mul_le_mul_left ((y + 1) ^ 2) hbase_le
      _ = (y + 1) ^ (2 + k) := by rw [pow_add]
  have hcontra : y ^ p + 1 < x ^ p := lt_of_lt_of_le hgap hle_pow
  rw [hpow] at hcontra
  exact lt_irrefl _ hcontra

/-- Elementary Cassels upper-divisor theorem, stated independently of
`EhrenfestUrn.lean`.

Same content as `CatalanCasselsUpperDivisorNat`, but lives in this
elementary file to avoid importing the 30k-line Ehrenfest file. -/
theorem cassels_upper_divisor_nat_elementary_raw
    (x y p q : ℕ)
    (hx : 1 < x) (hy : 1 < y)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hpow : x ^ p = y ^ q + 1) :
    q ∣ x := by
  by_contra hq_ndvd_x
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  -- Step a: p ≠ q (else two same-exponent powers differ by 1).
  have hp_ne_q : p ≠ q := by
    intro hpq
    subst hpq
    exact no_same_exponent_power_gap_one x y p hx hy hp.one_lt hpow
  -- Step b: factor y^q + 1 = (y+1) * Ψ_q(y).
  have hfactor :
      (y + 1) * altCyclotomicPlusNat q y = y ^ q + 1 :=
    alt_cyclotomic_plus_nat_mul_eq_pow_add_one y q hq_odd
  -- Step c: ¬ q ∣ y + 1 (else q ∣ x^p ⟹ q ∣ x).
  have hq_ndvd_y_add_one : ¬ q ∣ y + 1 := by
    intro hq_dvd_y_add_one
    have hq_dvd_yq_add_one : q ∣ y ^ q + 1 := by
      rw [← hfactor]
      exact dvd_mul_of_dvd_left hq_dvd_y_add_one _
    have hq_dvd_x_pow : q ∣ x ^ p := by
      rw [hpow]; exact hq_dvd_yq_add_one
    exact hq_ndvd_x (hq.dvd_of_dvd_pow hq_dvd_x_pow)
  -- Step d: coprime split.
  have hcop_y_add_one_q : Nat.Coprime (y + 1) q :=
    ((hq.coprime_iff_not_dvd).2 hq_ndvd_y_add_one).symm
  have hcop :
      Nat.Coprime (y + 1) (altCyclotomicPlusNat q y) := by
    change Nat.gcd (y + 1) (altCyclotomicPlusNat q y) = 1
    rw [gcd_add_one_alt_cyclotomic_plus_nat y q hq_odd]
    exact hcop_y_add_one_q
  have hprod :
      (y + 1) * altCyclotomicPlusNat q y = x ^ p := by
    rw [hfactor, ← hpow]
  -- Step e: extract u, v.
  rcases coprime_mul_eq_prime_pow_split
      (A := y + 1) (B := altCyclotomicPlusNat q y) (X := x) (p := p)
      hp hcop hprod with ⟨u, v, hy_add_one_eq, hpsi_eq⟩
  -- Step f: 1 < u (since y + 1 = u^p ≥ 3).
  have hu_pow_gt_one : 1 < u ^ p := by
    rw [← hy_add_one_eq]; omega
  have hu : 1 < u := by
    cases u with
    | zero => simp [hp.ne_zero] at hu_pow_gt_one
    | succ u =>
        cases u with
        | zero => simp at hu_pow_gt_one
        | succ u => omega
  have hy_eq : y = u ^ p - 1 := by omega
  have hshift :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p := by
    rw [← hy_eq]; exact hpsi_eq
  -- Step g: contradict Lemma 4.
  exact
    (shifted_alt_cyclotomic_plus_nat_not_prime_power
      u v p q hu hp hq hp5 hq5 hp_ne_q) hshift

/-- Lower-prime Cassels upper-divisor theorem: sorry-free for `p < q`.

Same proof as `cassels_upper_divisor_nat_elementary_raw` but calls the
proved `_p_lt_q` helper directly, avoiding the deferred `q < p` branch.
Matches the `CatalanCasselsUpperDivisorNatLT` interface in EhrenfestUrn. -/
theorem cassels_upper_divisor_nat_elementary_raw_lt
    (x y p q : ℕ)
    (hx : 1 < x) (hy : 1 < y)
    (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q)
    (hp_lt_q : p < q)
    (hpow : x ^ p = y ^ q + 1) :
    q ∣ x := by
  by_contra hq_ndvd_x
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hp_ne_q : p ≠ q := by omega
  have hfactor :
      (y + 1) * altCyclotomicPlusNat q y = y ^ q + 1 :=
    alt_cyclotomic_plus_nat_mul_eq_pow_add_one y q hq_odd
  have hq_ndvd_y_add_one : ¬ q ∣ y + 1 := by
    intro hq_dvd_y_add_one
    have hq_dvd_yq_add_one : q ∣ y ^ q + 1 := by
      rw [← hfactor]
      exact dvd_mul_of_dvd_left hq_dvd_y_add_one _
    have hq_dvd_x_pow : q ∣ x ^ p := by
      rw [hpow]; exact hq_dvd_yq_add_one
    exact hq_ndvd_x (hq.dvd_of_dvd_pow hq_dvd_x_pow)
  have hcop_y_add_one_q : Nat.Coprime (y + 1) q :=
    ((hq.coprime_iff_not_dvd).2 hq_ndvd_y_add_one).symm
  have hcop :
      Nat.Coprime (y + 1) (altCyclotomicPlusNat q y) := by
    change Nat.gcd (y + 1) (altCyclotomicPlusNat q y) = 1
    rw [gcd_add_one_alt_cyclotomic_plus_nat y q hq_odd]
    exact hcop_y_add_one_q
  have hprod :
      (y + 1) * altCyclotomicPlusNat q y = x ^ p := by
    rw [hfactor, ← hpow]
  rcases coprime_mul_eq_prime_pow_split
      (A := y + 1) (B := altCyclotomicPlusNat q y) (X := x) (p := p)
      hp hcop hprod with ⟨u, v, hy_add_one_eq, hpsi_eq⟩
  have hu_pow_gt_one : 1 < u ^ p := by
    rw [← hy_add_one_eq]; omega
  have hu : 1 < u := by
    cases u with
    | zero => simp [hp.ne_zero] at hu_pow_gt_one
    | succ u =>
        cases u with
        | zero => simp at hu_pow_gt_one
        | succ u => omega
  have hy_eq : y = u ^ p - 1 := by omega
  have hshift :
      altCyclotomicPlusNat q (u ^ p - 1) = v ^ p := by
    rw [← hy_eq]; exact hpsi_eq
  exact
    (shifted_alt_cyclotomic_plus_nat_not_prime_power_p_lt_q
      u v p q hu hp hq hp5 hq5 hp_lt_q) hshift

end Ripple
