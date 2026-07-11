/-
Cassels-1960 elementary descent — faithful formalization.

Following J. W. S. Cassels, "On the equation a^x − b^y = 1, II",
Proc. Camb. Phil. Soc. 56 (1960), 97–103 (file: `ref/Cassels-1960...pdf`).

This file replaces the abstract-Cramer / Padé-approximant framework of
`CasselsActualPade.lean` (which was empirically shown super-factorial,
see CHECKPOINT cont.11–14, 18) with Cassels' actual proof structure:
elementary GCD lemma + binomial-series truncation at `R = [p/q] + 1`
with explicit integer-clearing `z^{Rq−p} · q^{R+ρ}`.

Step 1 here: **Lemma 1 of Cassels (eq 4-2, 4-3) preliminaries** —
the alternating-quotient factorization and its congruence mod (c+1).
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

namespace Ripple.LPP.CasselsClassical

open Finset

/-- The alternating-sign quotient: `(c^p + 1)/(c+1) = ∑_{i<p} c^i · (-1)^(p-1-i)`
for odd `p`.  Defined directly as the sum over ℤ. -/
def altQuot (c : ℤ) (p : ℕ) : ℤ :=
  ∑ i ∈ range p, c ^ i * (-1 : ℤ) ^ (p - 1 - i)

/-- Cassels-1960 (Section 4, geometric identity used in Lemma 1): for odd `p`,
`(∑_{i<p} c^i · (-1)^{p-1-i}) · (c + 1) = c^p + 1` over ℤ.
This is `Commute.geom_sum₂_mul` specialised to `x=c, y=-1` for odd `p`. -/
lemma altQuot_mul_c_add_one (c : ℤ) (p : ℕ) (hpodd : Odd p) :
    altQuot c p * (c + 1) = c ^ p + 1 := by
  unfold altQuot
  have h := (Commute.all c (-1 : ℤ)).geom_sum₂_mul p
  have h1 : (c : ℤ) - (-1) = c + 1 := by ring
  have h2 : (-1 : ℤ) ^ p = -1 := hpodd.neg_one_pow
  rw [h1, h2] at h
  linarith [h]

/-- Each summand `c^i · (-1)^(p-1-i)` is `≡ 1 (mod c+1)` for odd `p`:
`c ≡ -1 (mod c+1)`, so the product collapses to `(-1)^{p-1} = 1`. -/
lemma altQuot_term_modEq_one (c : ℤ) (p i : ℕ) (hpodd : Odd p) (hi : i < p) :
    (c ^ i * (-1 : ℤ) ^ (p - 1 - i)) ≡ 1 [ZMOD (c + 1)] := by
  have hc : c ≡ -1 [ZMOD (c + 1)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-1, by ring⟩
  have hci : (c : ℤ) ^ i ≡ (-1) ^ i [ZMOD (c + 1)] := hc.pow i
  have hcomb : (c : ℤ) ^ i * (-1 : ℤ) ^ (p - 1 - i)
      ≡ (-1) ^ i * (-1) ^ (p - 1 - i) [ZMOD (c + 1)] :=
    hci.mul_right _
  have hadd : i + (p - 1 - i) = p - 1 := by omega
  have hcollapse : ((-1 : ℤ)) ^ i * (-1) ^ (p - 1 - i) = (-1) ^ (p - 1) := by
    rw [← pow_add, hadd]
  have hpm1_even : Even (p - 1) := by
    rcases hpodd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hpm1 : (-1 : ℤ) ^ (p - 1) = 1 := hpm1_even.neg_one_pow
  rw [hcollapse, hpm1] at hcomb
  exact hcomb

/-- Sum-of-congruences for `Int.ModEq` over a `Finset`: pointwise congruence
of summands implies congruence of sums.  (Helper for `altQuot_modEq_p`.) -/
lemma Finset.sum_modEq_of_forall {α : Type*} {f g : α → ℤ} {s : Finset α} {m : ℤ}
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD m]) :
    (∑ i ∈ s, f i) ≡ (∑ i ∈ s, g i) [ZMOD m] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Int.ModEq.refl]
  | @insert a s hns ih =>
    rw [Finset.sum_insert hns, Finset.sum_insert hns]
    refine (h a (mem_insert_self _ _)).add ?_
    exact ih (fun i hi => h i (mem_insert_of_mem hi))

/-- **Cassels-1960 (eq 4-3, +1 case)**: for odd `p`, `altQuot c p ≡ p (mod c+1)`. -/
theorem altQuot_modEq_p (c : ℤ) (p : ℕ) (hpodd : Odd p) :
    altQuot c p ≡ (p : ℤ) [ZMOD (c + 1)] := by
  unfold altQuot
  calc (∑ i ∈ range p, c ^ i * (-1 : ℤ) ^ (p - 1 - i))
      ≡ ∑ _i ∈ range p, (1 : ℤ) [ZMOD (c + 1)] :=
        Finset.sum_modEq_of_forall (fun i hi =>
          altQuot_term_modEq_one c p i hpodd (mem_range.mp hi))
    _ = (p : ℤ) := by simp

/-- **Cassels-1960 Lemma 1 (eq 4-2, +1 case)**: for odd prime `p` and integer
`c` with `c + 1 ≠ 0`, `gcd(altQuot c p, c+1) ∣ p`.  Since `p` is prime, the
gcd equals `1` or `p`.

This is the first true Cassels-1960 lemma in the new (non-Padé) architecture.
The quotient `(c^p+1)/(c+1)` is `altQuot c p` (from `altQuot_mul_c_add_one`).
Combining the factorization with the congruence `altQuot ≡ p (mod c+1)` gives
the gcd-divides-p conclusion directly. -/
theorem cassels_lemma_1_add (p : ℕ) (hp_prime : p.Prime) (hp2 : 2 < p)
    (c : ℤ) :
    (Int.gcd (altQuot c p) (c + 1) : ℤ) ∣ (p : ℤ) := by
  have hpodd : Odd p := hp_prime.odd_of_ne_two (by omega)
  have hmod := altQuot_modEq_p c p hpodd
  -- altQuot ≡ p (mod c+1)  ⇒  (c+1) ∣ p − altQuot
  have hdvd : (c + 1) ∣ ((p : ℤ) - altQuot c p) := Int.ModEq.dvd hmod
  have hg1 : (Int.gcd (altQuot c p) (c + 1) : ℤ) ∣ altQuot c p :=
    Int.gcd_dvd_left _ _
  have hg2 : (Int.gcd (altQuot c p) (c + 1) : ℤ) ∣ (c + 1) :=
    Int.gcd_dvd_right _ _
  have hg_diff : (Int.gcd (altQuot c p) (c + 1) : ℤ)
      ∣ ((p : ℤ) - altQuot c p) := hg2.trans hdvd
  have hsum : (Int.gcd (altQuot c p) (c + 1) : ℤ)
      ∣ (altQuot c p + ((p : ℤ) - altQuot c p)) :=
    dvd_add hg1 hg_diff
  simpa using hsum

/-- Corollary: the gcd is either `1` or `p`. -/
theorem cassels_lemma_1_add_gcd_eq (p : ℕ) (hp_prime : p.Prime) (hp2 : 2 < p)
    (c : ℤ) :
    Int.gcd (altQuot c p) (c + 1) = 1 ∨ Int.gcd (altQuot c p) (c + 1) = p := by
  have hdvd := cassels_lemma_1_add p hp_prime hp2 c
  have hdvd_nat : Int.gcd (altQuot c p) (c + 1) ∣ p := by
    have : (Int.gcd (altQuot c p) (c + 1) : ℤ) ∣ (p : ℤ) := hdvd
    exact_mod_cast this
  exact (Nat.Prime.eq_one_or_self_of_dvd hp_prime _ hdvd_nat).imp id id

/-! ### `−1` case: `(c^p − 1)/(c − 1)` — the simpler companion of Lemma 1.

For ANY `p` (no odd hypothesis needed) and integer `c`,
`c^p − 1 = (c − 1) · (∑_{i<p} c^i)`, and the quotient `∑_{i<p} c^i ≡ p (mod c − 1)`.
Lemma 1 then follows for the `−1` case. -/

/-- The "positive" geometric quotient: `(c^p − 1)/(c − 1) = ∑_{i<p} c^i`. -/
def posQuot (c : ℤ) (p : ℕ) : ℤ :=
  ∑ i ∈ range p, c ^ i

/-- Standard geometric factorization: `(∑_{i<p} c^i) · (c − 1) = c^p − 1`. -/
lemma posQuot_mul_c_sub_one (c : ℤ) (p : ℕ) :
    posQuot c p * (c - 1) = c ^ p - 1 := by
  unfold posQuot
  have h := (Commute.all c (1 : ℤ)).geom_sum₂_mul p
  -- h : (∑ i ∈ range p, c^i · 1^(p-1-i)) · (c - 1) = c^p - 1^p
  simp at h
  exact h

/-- `c ≡ 1 (mod c − 1)`, so `c^i ≡ 1` and the geometric sum `≡ p (mod c − 1)`. -/
lemma posQuot_modEq_p (c : ℤ) (p : ℕ) :
    posQuot c p ≡ (p : ℤ) [ZMOD (c - 1)] := by
  unfold posQuot
  have hc : c ≡ 1 [ZMOD (c - 1)] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-1, by ring⟩
  have hterm : ∀ i ∈ range p, (c ^ i : ℤ) ≡ 1 [ZMOD (c - 1)] := by
    intro i _
    have := hc.pow i
    simpa using this
  calc (∑ i ∈ range p, c ^ i)
      ≡ ∑ _i ∈ range p, (1 : ℤ) [ZMOD (c - 1)] :=
        Finset.sum_modEq_of_forall hterm
    _ = (p : ℤ) := by simp

/-- **Cassels Lemma 1 (−1 case)**: for prime `p ≥ 2` and integer `c`,
`gcd((c^p−1)/(c−1), c−1) = gcd(posQuot c p, c−1) ∣ p`. -/
theorem cassels_lemma_1_sub (p : ℕ) (hp_prime : p.Prime) (c : ℤ) :
    (Int.gcd (posQuot c p) (c - 1) : ℤ) ∣ (p : ℤ) := by
  have hmod := posQuot_modEq_p c p
  have hdvd : (c - 1) ∣ ((p : ℤ) - posQuot c p) := Int.ModEq.dvd hmod
  have hg1 : (Int.gcd (posQuot c p) (c - 1) : ℤ) ∣ posQuot c p :=
    Int.gcd_dvd_left _ _
  have hg2 : (Int.gcd (posQuot c p) (c - 1) : ℤ) ∣ (c - 1) :=
    Int.gcd_dvd_right _ _
  have hg_diff : (Int.gcd (posQuot c p) (c - 1) : ℤ)
      ∣ ((p : ℤ) - posQuot c p) := hg2.trans hdvd
  have hsum : (Int.gcd (posQuot c p) (c - 1) : ℤ)
      ∣ (posQuot c p + ((p : ℤ) - posQuot c p)) :=
    dvd_add hg1 hg_diff
  simpa using hsum

/-- The `−1`-case gcd is `1` or `p`. -/
theorem cassels_lemma_1_sub_gcd_eq (p : ℕ) (hp_prime : p.Prime) (c : ℤ) :
    Int.gcd (posQuot c p) (c - 1) = 1 ∨ Int.gcd (posQuot c p) (c - 1) = p := by
  have hdvd := cassels_lemma_1_sub p hp_prime c
  have hdvd_nat : Int.gcd (posQuot c p) (c - 1) ∣ p := by
    have : (Int.gcd (posQuot c p) (c - 1) : ℤ) ∣ (p : ℤ) := hdvd
    exact_mod_cast this
  exact (Nat.Prime.eq_one_or_self_of_dvd hp_prime _ hdvd_nat).imp id id

/-! ### Corollary of Lemma 1 (Cassels-1960 eq 4-5/4-6, `−1` case)

If `p^j ∣ (c − 1)` (`j ≥ 1`, `p` an odd prime) then
`(c^p − 1)/(c − 1) = posQuot c p ≡ p  (mod p^{j+1})`.

Elementary proof, NO binomial theorem: the algebraic identity
`posQuot c p − p = (c − 1)·∑_{i<p} posQuot c i`, plus `p ∣ ∑_{i<p} i`
(Gauss, `p` odd) lifts the mod-`(c−1)` congruence one `p`-adic order. -/

/-- Generalised `posQuot ≡ card`: if `c ≡ 1 [ZMOD m]` then for every
`i`, `posQuot c i ≡ i [ZMOD m]`. -/
lemma posQuot_modEq_of_c_modEq_one {c m : ℤ} (i : ℕ)
    (hc : c ≡ 1 [ZMOD m]) : posQuot c i ≡ (i : ℤ) [ZMOD m] := by
  unfold posQuot
  have hterm : ∀ k ∈ range i, (c ^ k : ℤ) ≡ 1 [ZMOD m] := by
    intro k _; simpa using hc.pow k
  calc (∑ k ∈ range i, c ^ k)
      ≡ ∑ _k ∈ range i, (1 : ℤ) [ZMOD m] :=
        Finset.sum_modEq_of_forall hterm
    _ = (i : ℤ) := by simp

/-- **Cassels-1960 Corollary of Lemma 1 (`−1` case).**  For an odd
prime `p`, `j ≥ 1`, and `p^j ∣ (c − 1)`:
`p^{j+1} ∣ (posQuot c p − p)`, i.e. `posQuot c p ≡ p (mod p^{j+1})`. -/
theorem cassels_cor_lemma_1_sub
    (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (c : ℤ) (j : ℕ) (hj : 1 ≤ j)
    (hdvd : (p : ℤ) ^ j ∣ (c - 1)) :
    (p : ℤ) ^ (j + 1) ∣ (posQuot c p - (p : ℤ)) := by
  set T : ℤ := ∑ i ∈ range p, posQuot c i with hT
  -- algebraic identity: posQuot c p − p = (c−1)·T
  have hPT : posQuot c p - (p : ℤ) = (c - 1) * T := by
    have hp_eq : (p : ℤ) = ∑ _i ∈ range p, (1 : ℤ) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hpos_eq : posQuot c p = ∑ i ∈ range p, c ^ i := rfl
    rw [hpos_eq, hp_eq, ← Finset.sum_sub_distrib, hT, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← posQuot_mul_c_sub_one c i]; ring
  -- p ∣ (c−1)
  have hpc : (p : ℤ) ∣ (c - 1) :=
    dvd_trans (dvd_pow_self (p : ℤ) (by omega : j ≠ 0)) hdvd
  have hc1 : c ≡ 1 [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have : (p : ℤ) ∣ -(c - 1) := (dvd_neg).mpr hpc
    simpa [neg_sub] using this
  -- T ≡ ∑_{i<p} i [ZMOD p]
  have hTmod : T ≡ ∑ i ∈ range p, (i : ℤ) [ZMOD (p : ℤ)] := by
    rw [hT]
    exact Finset.sum_modEq_of_forall
      (fun i _ => posQuot_modEq_of_c_modEq_one i hc1)
  -- p ∣ ∑_{i<p} i  (Gauss in ℕ, p odd ⇒ coprime to 2)
  have hp_dvd_sumN : p ∣ (∑ i ∈ Finset.range p, i) := by
    have hN : (∑ i ∈ Finset.range p, i) * 2 = p * (p - 1) :=
      Finset.sum_range_id_mul_two p
    have hpdvd : p ∣ (∑ i ∈ Finset.range p, i) * 2 := by
      rw [hN]; exact Dvd.intro _ rfl
    have hcop : Nat.Coprime p 2 :=
      (hp.coprime_iff_not_dvd).mpr
        (fun h2 => by
          have := Nat.le_of_dvd (by norm_num) h2; omega)
    exact Nat.Coprime.dvd_of_dvd_mul_right hcop hpdvd
  have hp_dvd_sum : (p : ℤ) ∣ (∑ i ∈ range p, (i : ℤ)) := by
    have hcast : (∑ i ∈ range p, (i : ℤ))
        = ((∑ i ∈ Finset.range p, i : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
    rw [hcast]
    exact_mod_cast hp_dvd_sumN
  -- p ∣ T
  have hpT : (p : ℤ) ∣ T := by
    have hSmod : (∑ i ∈ range p, (i : ℤ)) ≡ 0 [ZMOD (p : ℤ)] :=
      (Int.modEq_zero_iff_dvd).mpr hp_dvd_sum
    exact (Int.modEq_zero_iff_dvd).mp (hTmod.trans hSmod)
  -- p^{j+1} = p^j · p ∣ (c−1)·T
  have hfin : (p : ℤ) ^ (j + 1) ∣ (c - 1) * T := by
    rw [pow_succ]
    exact mul_dvd_mul hdvd hpT
  rw [hPT]; exact hfin

/-- For odd `p`, the alternating `+1`-quotient equals the positive
`−1`-quotient at `−c`: `altQuot c p = posQuot (−c) p`.  (Both are
`(c^p+1)/(c+1)`; termwise `(-1)^{p-1-i} = (-1)^i` for odd `p`.) -/
lemma altQuot_eq_posQuot_neg (c : ℤ) (p : ℕ) (hpodd : Odd p) :
    altQuot c p = posQuot (-c) p := by
  unfold altQuot posQuot
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hpe : Even (p - 1) := by
    rcases hpodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have hexp : (-1 : ℤ) ^ (p - 1 - i) = (-1 : ℤ) ^ i := by
    have hsum : (p - 1 - i) + i = p - 1 := by omega
    have hmul : ((-1 : ℤ)) ^ (p - 1 - i) * (-1) ^ i = (-1) ^ (p - 1) := by
      rw [← pow_add, hsum]
    have hpm1 : ((-1 : ℤ)) ^ (p - 1) = 1 := hpe.neg_one_pow
    have hii : ((-1 : ℤ)) ^ i * (-1) ^ i = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨i, rfl⟩
    calc (-1 : ℤ) ^ (p - 1 - i)
        = (-1) ^ (p - 1 - i) * ((-1) ^ i * (-1) ^ i) := by rw [hii]; ring
      _ = ((-1) ^ (p - 1 - i) * (-1) ^ i) * (-1) ^ i := by ring
      _ = (-1) ^ (p - 1) * (-1) ^ i := by rw [hmul]
      _ = (-1) ^ i := by rw [hpm1]; ring
  rw [neg_pow, hexp]; ring

/-- **Cassels-1960 Corollary of Lemma 1 (`+1` case).**  For an odd
prime `p`, `j ≥ 1`, and `p^j ∣ (c + 1)`:
`p^{j+1} ∣ (altQuot c p − p)`, i.e. `(c^p+1)/(c+1) ≡ p (mod p^{j+1})`. -/
theorem cassels_cor_lemma_1_add
    (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (c : ℤ) (j : ℕ) (hj : 1 ≤ j)
    (hdvd : (p : ℤ) ^ j ∣ (c + 1)) :
    (p : ℤ) ^ (j + 1) ∣ (altQuot c p - (p : ℤ)) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hdvd' : (p : ℤ) ^ j ∣ ((-c) - 1) := by
    have : ((-c) - 1) = -(c + 1) := by ring
    rw [this]; exact (dvd_neg).mpr hdvd
  have hsub := cassels_cor_lemma_1_sub p hp hp2 (-c) j hj hdvd'
  rwa [← altQuot_eq_posQuot_neg c p hpodd] at hsub

/-! ### Cassels-1960 p.100 size inequality (towards Lemma 2)

The contradiction in Lemma 2 (case `b±1 = u^p`) rests on the elementary
inequality, for `2 ≤ u`, `2 ≤ q < p`:
  `(u^q − 1)^p < (u^p − 1)^q`.
Clean algebraic proof (no calculus): `u^p − 1 > u^{p−q}·(u^q − 1)`
(their difference is `u^{p−q} − 1 > 0`); raise to the `q`-th power; then
`(u^q)^{p−q} ≥ (u^q − 1)^{p−q}`. -/

/-- `u^{p−q} · (u^q − 1) < u^p − 1` for `2 ≤ u`, `q < p`
(difference `= u^{p−q} − 1 ≥ 1`). -/
lemma u_pow_sub_one_gt (u q p : ℕ) (hu : 2 ≤ u) (hqp : q < p) :
    u ^ (p - q) * (u ^ q - 1) < u ^ p - 1 := by
  have hpq : p - q + q = p := by omega
  have hpow : u ^ (p - q) * u ^ q = u ^ p := by rw [← pow_add, hpq]
  have hupq2 : 2 ≤ u ^ (p - q) := by
    calc (2 : ℕ) ≤ u := hu
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ (p - q) := Nat.pow_le_pow_right (by omega) (by omega)
  have hupple : u ^ (p - q) ≤ u ^ p :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hkey : u ^ (p - q) * (u ^ q - 1) = u ^ p - u ^ (p - q) := by
    rw [Nat.mul_sub_one, hpow]
  rw [hkey]; omega

/-- **Cassels-1960 p.100 size inequality**: for `2 ≤ u`, `2 ≤ q < p`,
`(u^q − 1)^p < (u^p − 1)^q`.  (Used in Lemma 2's contradiction.) -/
theorem cassels_size_ineq (u q p : ℕ) (hu : 2 ≤ u) (hq : 2 ≤ q)
    (hqp : q < p) :
    (u ^ q - 1) ^ p < (u ^ p - 1) ^ q := by
  have hpq : p - q + q = p := by omega
  -- step 1: u^{p-q}·(u^q-1) < u^p-1
  have h1 := u_pow_sub_one_gt u q p hu hqp
  -- step 2: raise to q-th power (strict, base nonneg, q ≥ 1)
  have h2 : (u ^ (p - q) * (u ^ q - 1)) ^ q < (u ^ p - 1) ^ q :=
    Nat.pow_lt_pow_left h1 (by omega)
  -- step 3: (u^{p-q}·(u^q-1))^q = (u^q)^{p-q}·(u^q-1)^q
  have h3 : (u ^ (p - q) * (u ^ q - 1)) ^ q
      = (u ^ q) ^ (p - q) * (u ^ q - 1) ^ q := by
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (p - q) q]
  -- step 4: (u^q-1)^{p-q} ≤ (u^q)^{p-q}
  have h4 : (u ^ q - 1) ^ (p - q) ≤ (u ^ q) ^ (p - q) :=
    Nat.pow_le_pow_left (by omega) _
  -- step 5: chain
  calc (u ^ q - 1) ^ p
      = (u ^ q - 1) ^ (p - q) * (u ^ q - 1) ^ q := by
        rw [← pow_add, hpq]
    _ ≤ (u ^ q) ^ (p - q) * (u ^ q - 1) ^ q :=
        Nat.mul_le_mul_right _ h4
    _ = (u ^ (p - q) * (u ^ q - 1)) ^ q := by rw [h3]
    _ < (u ^ p - 1) ^ q := h2

/-- Consecutive `q`-th powers (`q ≥ 2`) of values `≥ 2` differ by `≥ 2`:
`x^q ≥ (x−1)^q + 2` for `2 ≤ x`, `2 ≤ q`.  (`(x−1)^q ≤ (x−1)·x^{q−1}`,
`x^q = x·x^{q−1}`, gap `≥ x^{q−1} ≥ 2`.) -/
lemma pow_gap_ge_two (x q : ℕ) (hx : 2 ≤ x) (hq : 2 ≤ q) :
    (x - 1) ^ q + 2 ≤ x ^ q := by
  have hq1 : q - 1 + 1 = q := by omega
  have hxm1 : x - 1 + 1 = x := by omega
  have hsplit_x : x ^ q = x * x ^ (q - 1) := by
    rw [← pow_succ', hq1]
  have hsplit_xm1 : (x - 1) ^ q = (x - 1) * (x - 1) ^ (q - 1) := by
    rw [← pow_succ', hq1]
  have hle : (x - 1) ^ (q - 1) ≤ x ^ (q - 1) :=
    Nat.pow_le_pow_left (by omega) _
  have hxq1_ge : 2 ≤ x ^ (q - 1) := by
    calc (2 : ℕ) ≤ x := hx
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc (x - 1) ^ q + 2
      = (x - 1) * (x - 1) ^ (q - 1) + 2 := by rw [hsplit_xm1]
    _ ≤ (x - 1) * x ^ (q - 1) + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) 2
    _ ≤ (x - 1) * x ^ (q - 1) + x ^ (q - 1) :=
        Nat.add_le_add_left hxq1_ge _
    _ = x * x ^ (q - 1) := by
        have hX : (x - 1) * x ^ (q - 1) + x ^ (q - 1)
            = ((x - 1) + 1) * x ^ (q - 1) := by ring
        rw [hX, show (x - 1) + 1 = x from by omega]
    _ = x ^ q := hsplit_x.symm

/-- **Cassels-1960 Lemma 2, `+1` case — size contradiction.**  If
`b + 1 = u^p` and `a^p = b^q + 1` with `2 ≤ u`, `2 ≤ q < p`, then `False`.
(`a^p = (u^p−1)^q + 1 < (u^p)^q = (u^q)^p` ⇒ `a ≤ u^q − 1` ⇒
`a^p ≤ (u^q−1)^p < (u^p−1)^q = b^q < a^p`, via `cassels_size_ineq`.) -/
theorem cassels_lemma_2_plus_no_pth_power
    (u q p a b : ℕ) (hu : 2 ≤ u) (hq : 2 ≤ q) (hqp : q < p)
    (hbu : b + 1 = u ^ p) (hab : a ^ p = b ^ q + 1) : False := by
  have hb : b = u ^ p - 1 := by omega
  have hupp : 2 ≤ u ^ p := by
    calc (2 : ℕ) ≤ u := hu
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ p := Nat.pow_le_pow_right (by omega) (by omega)
  -- a^p = (u^p−1)^q + 1 < (u^p)^q
  have hap_lt : a ^ p < (u ^ p) ^ q := by
    have hgap := pow_gap_ge_two (u ^ p) q hupp hq
    -- (u^p−1)^q + 2 ≤ (u^p)^q, so (u^p−1)^q + 1 < (u^p)^q
    rw [hab, hb]; omega
  -- (u^p)^q = (u^q)^p
  have hcomm : (u ^ p) ^ q = (u ^ q) ^ p := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hcomm] at hap_lt
  -- a^p < (u^q)^p ⇒ a < u^q
  have ha_lt : a < u ^ q := by
    rcases lt_or_ge a (u ^ q) with h | h
    · exact h
    · exact absurd (Nat.pow_le_pow_left h p) (Nat.not_le.mpr hap_lt)
  have ha_le : a ≤ u ^ q - 1 := by omega
  -- a^p ≤ (u^q − 1)^p
  have hap_le : a ^ p ≤ (u ^ q - 1) ^ p := Nat.pow_le_pow_left ha_le p
  -- (u^q − 1)^p < (u^p − 1)^q
  have hsize := cassels_size_ineq u q p hu hq hqp
  -- chain: a^p ≤ (u^q−1)^p < (u^p−1)^q = b^q < b^q+1 = a^p
  have hbq : (u ^ p - 1) ^ q = b ^ q := by rw [hb]
  omega

/-- **Cassels-1960 Lemma 2, `+1` case (full).**  For primes `2 < q < p`
and `b ≥ 2` with `a^p = b^q + 1`, we have `q ∣ (b + 1)`.

Proof: if not, `gcd(b+1, (b^q+1)/(b+1)) = 1` (Lemma 1 + `q ∤ b+1`),
so the coprime factorization `(b+1)·Q = a^p` makes `b+1` a perfect
`p`-th power (`exists_eq_pow_of_mul_eq_pow`); then
`cassels_lemma_2_plus_no_pth_power` gives a contradiction. -/
theorem cassels_lemma_2_plus
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hq2 : 2 < q)
    (hqp : q < p) (hb : 2 ≤ b) (hab : a ^ p = b ^ q + 1) :
    q ∣ (b + 1) := by
  by_contra hndvd
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hbZ1 : ((b : ℤ) + 1) ≠ 0 := by positivity
  have hfact : altQuot (b : ℤ) q * ((b : ℤ) + 1) = (b : ℤ) ^ q + 1 :=
    altQuot_mul_c_add_one (b : ℤ) q hq_odd
  -- (b+1) ∣ (b^q+1) in ℕ
  have hdvdN : (b + 1) ∣ (b ^ q + 1) := by
    have hZ : ((b : ℤ) + 1) ∣ ((b : ℤ) ^ q + 1) :=
      ⟨altQuot (b : ℤ) q, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((b + 1 : ℕ) : ℤ) ∣ ((b ^ q + 1 : ℕ) : ℤ) := by
      push_cast; exact hZ
    exact_mod_cast h2
  set Q := (b ^ q + 1) / (b + 1) with hQ
  have hQmul : (b + 1) * Q = b ^ q + 1 := Nat.mul_div_cancel' hdvdN
  -- altQuot (b:ℤ) q = (Q:ℤ)
  have haltQ : altQuot (b : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((b : ℤ) + 1) = (b : ℤ) ^ q + 1 := by
      have hc : ((b + 1 : ℕ) : ℤ) * (Q : ℤ) = ((b ^ q + 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      push_cast at hc
      rw [mul_comm]
      exact hc
    have := hfact.trans hQZ.symm
    exact mul_right_cancel₀ hbZ1 this
  have hgcd := cassels_lemma_1_add_gcd_eq q hq hq2 (b : ℤ)
  rw [haltQ] at hgcd
  have hbridge : Int.gcd (Q : ℤ) ((b : ℤ) + 1) = Nat.gcd Q (b + 1) := by
    have hb1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hb1, Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [hbridge] at hgcd
  -- q ∤ (b+1) ⇒ gcd ≠ q ⇒ gcd = 1 ⇒ coprime
  have hcop : Nat.Coprime (b + 1) Q := by
    rcases hgcd with h1 | hqe
    · simpa [Nat.Coprime, Nat.gcd_comm] using h1
    · exact absurd
        (dvd_trans (by rw [hqe] : q ∣ Nat.gcd Q (b + 1))
          (Nat.gcd_dvd_right _ _)) hndvd
  have hprod : (b + 1) * Q = a ^ p := by rw [hQmul, ← hab]
  have hunit : IsUnit (gcd (b + 1) Q) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit hprod
  -- u ≥ 2  (b+1 = u^p ≥ 3)
  have hbp3 : 3 ≤ b + 1 := by omega
  have hup : u ^ p = b + 1 := hu.symm
  have hu2 : 2 ≤ u := by
    rcases Nat.lt_or_ge u 2 with hlt | hge
    · exfalso
      have hle1 : u ^ p ≤ 1 := by
        calc u ^ p ≤ 1 ^ p := Nat.pow_le_pow_left (by omega) p
          _ = 1 := one_pow p
      omega
    · exact hge
  exact cassels_lemma_2_plus_no_pth_power u q p a b hu2 (by omega) hqp
    hu hab

/-! ### `−1` branch of Lemma 2 (symmetric)

`a^p = b^q − 1` with `b − 1 = u^p` is impossible, via the companion
size inequality `(u^p + 1)^q < (u^q + 1)^p`. -/

/-- `u^p + 1 < u^{p−q}·(u^q + 1)` for `2 ≤ u`, `q < p`. -/
lemma u_pow_add_one_lt (u q p : ℕ) (hu : 2 ≤ u) (hqp : q < p) :
    u ^ p + 1 < u ^ (p - q) * (u ^ q + 1) := by
  have hpq : p - q + q = p := by omega
  have hpow : u ^ (p - q) * u ^ q = u ^ p := by rw [← pow_add, hpq]
  have hupq2 : 2 ≤ u ^ (p - q) := by
    calc (2 : ℕ) ≤ u := hu
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ (p - q) := Nat.pow_le_pow_right (by omega) (by omega)
  have hkey : u ^ (p - q) * (u ^ q + 1) = u ^ p + u ^ (p - q) := by
    rw [Nat.mul_add, Nat.mul_one, hpow]
  rw [hkey]; omega

/-- **Companion size inequality**: for `2 ≤ u`, `2 ≤ q < p`,
`(u^p + 1)^q < (u^q + 1)^p`. -/
theorem cassels_size_ineq_plus (u q p : ℕ) (hu : 2 ≤ u) (hq : 2 ≤ q)
    (hqp : q < p) :
    (u ^ p + 1) ^ q < (u ^ q + 1) ^ p := by
  have hpq : p - q + q = p := by omega
  have h1 := u_pow_add_one_lt u q p hu hqp
  have h2 : (u ^ p + 1) ^ q < (u ^ (p - q) * (u ^ q + 1)) ^ q :=
    Nat.pow_lt_pow_left h1 (by omega)
  have h3 : (u ^ (p - q) * (u ^ q + 1)) ^ q
      = (u ^ q) ^ (p - q) * (u ^ q + 1) ^ q := by
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (p - q) q]
  have h4 : (u ^ q) ^ (p - q) ≤ (u ^ q + 1) ^ (p - q) :=
    Nat.pow_le_pow_left (by omega) _
  calc (u ^ p + 1) ^ q
      < (u ^ (p - q) * (u ^ q + 1)) ^ q := h2
    _ = (u ^ q) ^ (p - q) * (u ^ q + 1) ^ q := h3
    _ ≤ (u ^ q + 1) ^ (p - q) * (u ^ q + 1) ^ q :=
        Nat.mul_le_mul_right _ h4
    _ = (u ^ q + 1) ^ p := by rw [← pow_add, hpq]

/-- **Cassels-1960 Lemma 2, `−1` case — size contradiction.**  If
`b − 1 = u^p` (`b ≥ 2`) and `a^p = b^q − 1` with `2 ≤ u`, `2 ≤ q < p`,
then `False`. -/
theorem cassels_lemma_2_minus_no_pth_power
    (u q p a b : ℕ) (hu : 2 ≤ u) (hq : 2 ≤ q) (hqp : q < p) (hb : 2 ≤ b)
    (hbu : b - 1 = u ^ p) (hab : a ^ p = b ^ q - 1) : False := by
  have hb1 : b = u ^ p + 1 := by omega
  have hupp : 2 ≤ u ^ p := by
    calc (2 : ℕ) ≤ u := hu
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ p := Nat.pow_le_pow_right (by omega) (by omega)
  -- gap: b^q = (u^p+1)^q ≥ (u^p)^q + 2
  have hgap2 : (u ^ p) ^ q + 2 ≤ b ^ q := by
    have := pow_gap_ge_two (u ^ p + 1) q (by omega) hq
    have hxm1 : u ^ p + 1 - 1 = u ^ p := by omega
    rw [hxm1] at this
    rw [hb1]; omega
  have hcomm : (u ^ q) ^ p = (u ^ p) ^ q := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hbqpos : 1 ≤ b ^ q := Nat.one_le_pow _ _ (by omega)
  -- a ≥ u^q+1 : else a ≤ u^q ⇒ a^p ≤ (u^q)^p = (u^p)^q < b^q-1 = a^p
  have ha_ge : u ^ q + 1 ≤ a := by
    by_contra hcon
    have ha_le : a ≤ u ^ q := by omega
    have hap_le_uqp : a ^ p ≤ (u ^ q) ^ p := Nat.pow_le_pow_left ha_le p
    omega
  have hap_le : (u ^ q + 1) ^ p ≤ a ^ p := Nat.pow_le_pow_left ha_ge p
  have hsize := cassels_size_ineq_plus u q p hu hq hqp
  -- a^p ≥ (u^q+1)^p > (u^p+1)^q = b^q > b^q - 1 = a^p
  have hbq_eq : (u ^ p + 1) ^ q = b ^ q := by rw [hb1]
  omega

/-- **Cassels-1960 Lemma 2, `−1` case (full).**  For primes `p`, `q`
with `q < p`, `b ≥ 3`, if `a^p = b^q − 1` then `q ∣ (b − 1)`.

The `b ≥ 3` hypothesis is the non-degenerate regime: at `b = 2` the
conclusion `q ∣ 1` is false and `a^p = 2^q − 1` is the trivial
Mersenne–perfect-power sub-case handled outside this elementary size
descent.  For the genuine application (`p, q ≥ 5`, astronomically large
`b`) `b ≥ 3` is automatic. -/
theorem cassels_lemma_2_minus
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hqp : q < p) (hb : 3 ≤ b) (hab : a ^ p = b ^ q - 1) :
    q ∣ (b - 1) := by
  by_contra hndvd
  have hq2 : 2 ≤ q := hq.two_le
  have h1b : (1 : ℕ) ≤ b := by omega
  have hbqpos : 1 ≤ b ^ q := Nat.one_le_pow _ _ (by omega)
  have hbZ1 : ((b : ℤ) - 1) ≠ 0 := by
    have h3 : (3 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    omega
  have hfact : posQuot (b : ℤ) q * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 :=
    posQuot_mul_c_sub_one (b : ℤ) q
  have hcastm1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub h1b, Nat.cast_one]
  have hcastbq : ((b ^ q - 1 : ℕ) : ℤ) = (b : ℤ) ^ q - 1 := by
    rw [Nat.cast_sub hbqpos, Nat.cast_pow, Nat.cast_one]
  -- (b-1) ∣ (b^q-1) in ℕ
  have hdvdN : (b - 1) ∣ (b ^ q - 1) := by
    have hZ : ((b : ℤ) - 1) ∣ ((b : ℤ) ^ q - 1) :=
      ⟨posQuot (b : ℤ) q, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((b - 1 : ℕ) : ℤ) ∣ ((b ^ q - 1 : ℕ) : ℤ) := by
      rw [hcastm1, hcastbq]; exact hZ
    exact_mod_cast h2
  set Q := (b ^ q - 1) / (b - 1) with hQ
  have hQmul : (b - 1) * Q = b ^ q - 1 := Nat.mul_div_cancel' hdvdN
  have haltQ : posQuot (b : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 := by
      have hc : ((b - 1 : ℕ) : ℤ) * (Q : ℤ) = ((b ^ q - 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      rw [hcastm1, hcastbq] at hc
      rw [mul_comm]; exact hc
    have := hfact.trans hQZ.symm
    exact mul_right_cancel₀ hbZ1 this
  have hgcd := cassels_lemma_1_sub_gcd_eq q hq (b : ℤ)
  rw [haltQ] at hgcd
  have hbridge : Int.gcd (Q : ℤ) ((b : ℤ) - 1) = Nat.gcd Q (b - 1) := by
    rw [← hcastm1, Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [hbridge] at hgcd
  have hcop : Nat.Coprime (b - 1) Q := by
    rcases hgcd with h1 | hqe
    · simpa [Nat.Coprime, Nat.gcd_comm] using h1
    · exact absurd
        (dvd_trans (by rw [hqe] : q ∣ Nat.gcd Q (b - 1))
          (Nat.gcd_dvd_right _ _)) hndvd
  have hprod : (b - 1) * Q = a ^ p := by rw [hQmul, ← hab]
  have hunit : IsUnit (gcd (b - 1) Q) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit hprod
  -- u ≥ 2  (b-1 = u^p ≥ 2 since b ≥ 3)
  have hu2 : 2 ≤ u := by
    rcases Nat.lt_or_ge u 2 with hlt | hge
    · exfalso
      have hle1 : u ^ p ≤ 1 := by
        calc u ^ p ≤ 1 ^ p := Nat.pow_le_pow_left (by omega) p
          _ = 1 := one_pow p
      omega
    · exact hge
  exact cassels_lemma_2_minus_no_pth_power u q p a b hu2 hq2 hqp
    (by omega) hu hab

/-! ### Towards Corollary 1 of Lemma 2 (Cassels-1960 eq 4-8/4-9)

Cassels: "(4-8) and (4-9) follow at once from Lemmas 1 and 2."  The
first concrete step is upgrading Lemma 1's `gcd ∈ {1, q}` to the
**exact** value `gcd = q`, once Lemma 2 has supplied `q ∣ (b±1)`. -/

/-- **Exact gcd, `+1` case.**  For an odd prime `q` and `q ∣ (b+1)`:
`gcd((b^q+1)/(b+1), b+1) = gcd(altQuot b q, b+1) = q`.  (Lemma 1 gives
`∈ {1,q}`; `q ∣ (b+1)` and `q ∣ altQuot b q` exclude `1`.) -/
theorem cassels_gcd_add_eq_q (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (b : ℤ) (hqb : (q : ℤ) ∣ (b + 1)) :
    Int.gcd (altQuot b q) (b + 1) = q := by
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hcong : (-b) ≡ 1 [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have h : (1 : ℤ) - (-b) = b + 1 := by ring
    rw [h]; exact hqb
  have hpq : posQuot (-b) q ≡ (q : ℤ) [ZMOD (q : ℤ)] :=
    posQuot_modEq_of_c_modEq_one q hcong
  have hq_dvd_alt : (q : ℤ) ∣ altQuot b q := by
    rw [altQuot_eq_posQuot_neg b q hqodd]
    have hz : posQuot (-b) q ≡ 0 [ZMOD (q : ℤ)] :=
      hpq.trans (Int.modEq_zero_iff_dvd.mpr (dvd_refl _))
    exact (Int.modEq_zero_iff_dvd).mp hz
  have hq_dvd_gcd : q ∣ Int.gcd (altQuot b q) (b + 1) :=
    Int.dvd_gcd hq_dvd_alt hqb
  rcases cassels_lemma_1_add_gcd_eq q hq hq2 b with h1 | hq'
  · exfalso
    rw [h1] at hq_dvd_gcd
    have : q ≤ 1 := Nat.le_of_dvd (by norm_num) hq_dvd_gcd
    omega
  · exact hq'

/-- **Exact gcd, `−1` case.**  For a prime `q` and `q ∣ (b−1)`:
`gcd((b^q−1)/(b−1), b−1) = gcd(posQuot b q, b−1) = q`. -/
theorem cassels_gcd_sub_eq_q (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (b : ℤ) (hqb : (q : ℤ) ∣ (b - 1)) :
    Int.gcd (posQuot b q) (b - 1) = q := by
  have hcong : b ≡ 1 [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have h : (1 : ℤ) - b = -(b - 1) := by ring
    rw [h]; exact (dvd_neg).mpr hqb
  have hpq : posQuot b q ≡ (q : ℤ) [ZMOD (q : ℤ)] :=
    posQuot_modEq_of_c_modEq_one q hcong
  have hq_dvd_pos : (q : ℤ) ∣ posQuot b q := by
    have hz : posQuot b q ≡ 0 [ZMOD (q : ℤ)] :=
      hpq.trans (Int.modEq_zero_iff_dvd.mpr (dvd_refl _))
    exact (Int.modEq_zero_iff_dvd).mp hz
  have hq_dvd_gcd : q ∣ Int.gcd (posQuot b q) (b - 1) :=
    Int.dvd_gcd hq_dvd_pos hqb
  rcases cassels_lemma_1_sub_gcd_eq q hq b with h1 | hq'
  · exfalso
    rw [h1] at hq_dvd_gcd
    have : q ≤ 1 := Nat.le_of_dvd (by norm_num) hq_dvd_gcd
    omega
  · exact hq'

/-- **`q ∣ a` (`+1` case).**  Odd prime `q`, `q ∣ (b+1)`,
`a^p = b^q+1`  ⟹  `q ∣ a`.  (Fork-independent; every route needs it.) -/
theorem cassels_q_dvd_a_plus (p q a b : ℕ) (hp : 0 < p)
    (hq : q.Prime) (hq2 : 2 < q) (hqb : q ∣ (b + 1))
    (hab : a ^ p = b ^ q + 1) : q ∣ a := by
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hb : (b : ℤ) ≡ -1 [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have h : (-1 : ℤ) - b = -(b + 1) := by ring
    rw [h]; exact (dvd_neg).mpr (by exact_mod_cast hqb)
  have hbq : (b : ℤ) ^ q ≡ (-1) ^ q [ZMOD (q : ℤ)] := hb.pow q
  have hneg : ((-1 : ℤ)) ^ q = -1 := hqodd.neg_one_pow
  have hsum : (b : ℤ) ^ q + 1 ≡ 0 [ZMOD (q : ℤ)] := by
    calc (b : ℤ) ^ q + 1
        ≡ (-1) ^ q + 1 [ZMOD (q : ℤ)] := hbq.add_right 1
      _ = 0 := by rw [hneg]; ring
  have hqdvd_apZ : (q : ℤ) ∣ ((a : ℤ) ^ p) := by
    have hd : (q : ℤ) ∣ ((b : ℤ) ^ q + 1) := (Int.modEq_zero_iff_dvd).mp hsum
    have hcast : (a : ℤ) ^ p = (b : ℤ) ^ q + 1 := by exact_mod_cast hab
    rw [hcast]; exact hd
  have hqdvd_ap : q ∣ a ^ p := by exact_mod_cast hqdvd_apZ
  exact hq.dvd_of_dvd_pow hqdvd_ap

/-- **`q ∣ a` (`−1` case).**  Prime `q`, `q ∣ (b−1)`, `b ≥ 1`,
`a^p = b^q−1`  ⟹  `q ∣ a`. -/
theorem cassels_q_dvd_a_minus (p q a b : ℕ) (hp : 0 < p)
    (hq : q.Prime) (hb1 : 1 ≤ b) (hqb : q ∣ (b - 1))
    (hab : a ^ p = b ^ q - 1) : q ∣ a := by
  have hbqpos : 1 ≤ b ^ q := Nat.one_le_pow _ _ (by omega)
  have hb : (b : ℤ) ≡ 1 [ZMOD (q : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have h : (1 : ℤ) - b = -((b : ℤ) - 1) := by ring
    rw [h]
    refine (dvd_neg).mpr ?_
    have : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
      rw [Nat.cast_sub hb1, Nat.cast_one]
    rw [← this]; exact_mod_cast hqb
  have hbq : (b : ℤ) ^ q ≡ (1 : ℤ) ^ q [ZMOD (q : ℤ)] := hb.pow q
  have hsum : (b : ℤ) ^ q - 1 ≡ 0 [ZMOD (q : ℤ)] := by
    calc (b : ℤ) ^ q - 1
        ≡ (1 : ℤ) ^ q - 1 [ZMOD (q : ℤ)] := hbq.sub_right 1
      _ = 0 := by ring
  have hqdvd_apZ : (q : ℤ) ∣ ((a : ℤ) ^ p) := by
    have hd : (q : ℤ) ∣ ((b : ℤ) ^ q - 1) := (Int.modEq_zero_iff_dvd).mp hsum
    have hcast : (a : ℤ) ^ p = (b : ℤ) ^ q - 1 := by
      have : ((b ^ q - 1 : ℕ) : ℤ) = (b : ℤ) ^ q - 1 := by
        rw [Nat.cast_sub hbqpos, Nat.cast_pow, Nat.cast_one]
      rw [← this]; exact_mod_cast hab
    rw [hcast]; exact hd
  have hqdvd_ap : q ∣ a ^ p := by exact_mod_cast hqdvd_apZ
  exact hq.dvd_of_dvd_pow hqdvd_ap

/-! ### Exact `q`-adic valuation of the quotient (Cor 1 of Lemma 2 core)

`v_q((b^q±1)/(b±1)) = 1` exactly when `q ∣ (b±1)`.  This is the
load-bearing input for Cassels' coprime `p`-th-power split in
Cor 1 — and it is RIGOROUS and exponent-unambiguous (proven from
the Corollary of Lemma 1 at `j=1`), independent of the `gap_core`
architectural fork. -/

/-- `+1` case: `q ∣ (b+1)` (odd prime `q`) ⟹ `q ∣ altQuot b q`
and `¬ q² ∣ altQuot b q`, i.e. `v_q(altQuot b q) = 1` exactly. -/
theorem cassels_vq_altQuot_eq_one (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (b : ℤ) (hqb : (q : ℤ) ∣ (b + 1)) :
    (q : ℤ) ∣ altQuot b q ∧ ¬ ((q : ℤ) ^ 2 ∣ altQuot b q) := by
  have hj : (1 : ℕ) ≤ 1 := le_refl 1
  have hdvd1 : (q : ℤ) ^ 1 ∣ (b + 1) := by simpa using hqb
  have hcor := cassels_cor_lemma_1_add q hq hq2 b 1 hj hdvd1
  -- hcor : (q:ℤ)^2 ∣ (altQuot b q − q)
  have hq2dvd : (q : ℤ) ^ 2 ∣ (altQuot b q - (q : ℤ)) := by
    simpa using hcor
  have hqdvd : (q : ℤ) ∣ altQuot b q := by
    have h1 : (q : ℤ) ∣ (altQuot b q - (q : ℤ)) :=
      dvd_trans (dvd_pow_self (q : ℤ) (by norm_num : (2:ℕ) ≠ 0)) hq2dvd
    have h2 : (q : ℤ) ∣ (q : ℤ) := dvd_refl _
    have : (q : ℤ) ∣ ((altQuot b q - (q : ℤ)) + (q : ℤ)) := dvd_add h1 h2
    simpa using this
  refine ⟨hqdvd, ?_⟩
  intro hsq
  -- q² ∣ altQuot and q² ∣ (altQuot − q) ⇒ q² ∣ q ⇒ q ∣ 1, contra
  have hq2dvdq : (q : ℤ) ^ 2 ∣ (q : ℤ) := by
    have := dvd_sub hsq hq2dvd
    simpa using this
  have hqle : (q : ℤ) ^ 2 ≤ (q : ℤ) := by
    refine Int.le_of_dvd ?_ hq2dvdq
    have : (0 : ℤ) < (q : ℤ) := by
      have : 0 < q := hq.pos
      exact_mod_cast this
    linarith
  have hqpos : (0 : ℤ) < (q : ℤ) := by
    have : 0 < q := hq.pos
    exact_mod_cast this
  nlinarith [hqle, hqpos]

/-- `−1` case: `q ∣ (b−1)` (prime `q`) ⟹ `q ∣ posQuot b q`
and `¬ q² ∣ posQuot b q`, i.e. `v_q(posQuot b q) = 1` exactly. -/
theorem cassels_vq_posQuot_eq_one (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (b : ℤ) (hqb : (q : ℤ) ∣ (b - 1)) :
    (q : ℤ) ∣ posQuot b q ∧ ¬ ((q : ℤ) ^ 2 ∣ posQuot b q) := by
  have hj : (1 : ℕ) ≤ 1 := le_refl 1
  have hdvd1 : (q : ℤ) ^ 1 ∣ (b - 1) := by simpa using hqb
  have hcor := cassels_cor_lemma_1_sub q hq hq2 b 1 hj hdvd1
  have hq2dvd : (q : ℤ) ^ 2 ∣ (posQuot b q - (q : ℤ)) := by
    simpa using hcor
  have hqdvd : (q : ℤ) ∣ posQuot b q := by
    have h1 : (q : ℤ) ∣ (posQuot b q - (q : ℤ)) :=
      dvd_trans (dvd_pow_self (q : ℤ) (by norm_num : (2:ℕ) ≠ 0)) hq2dvd
    have : (q : ℤ) ∣ ((posQuot b q - (q : ℤ)) + (q : ℤ)) :=
      dvd_add h1 (dvd_refl _)
    simpa using this
  refine ⟨hqdvd, ?_⟩
  intro hsq
  have hq2dvdq : (q : ℤ) ^ 2 ∣ (q : ℤ) := by
    have := dvd_sub hsq hq2dvd
    simpa using this
  have hqpos : (0 : ℤ) < (q : ℤ) := by
    have : 0 < q := hq.pos
    exact_mod_cast this
  have hqle : (q : ℤ) ^ 2 ≤ (q : ℤ) :=
    Int.le_of_dvd hqpos hq2dvdq
  nlinarith [hqle, hqpos]

/-! ### `p`-adic valuation arithmetic of Cor 1 (rigorous, fork-free)

The genuine valuation content of Cassels Cor 1: `p ∣ (v_q(b±1) + 1)`,
i.e. `v_q(b±1) ≡ −1 (mod p)`.  Derived from `v_q(quot)=1` +
multiplicativity + `v_q` of a `p`-th power; exponent-honest (no
guessing of the `p−1` form, which is the `v_q(a)=1` instance). -/

/-- `+1` case: `q ∣ (b+1)`, `a^p = b^q+1` ⟹ `p ∣ (v_q(b+1) + 1)`. -/
theorem cassels_p_dvd_vq_succ_plus
    (p q a b : ℕ) (hp : 0 < p) (hq : q.Prime) (hq2 : 2 < q)
    (hb : 2 ≤ b) (hqb : (q : ℤ) ∣ ((b : ℤ) + 1))
    (hab : a ^ p = b ^ q + 1) :
    p ∣ (padicValInt q ((b : ℤ) + 1) + 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hfact : altQuot (b : ℤ) q * ((b : ℤ) + 1) = (b : ℤ) ^ q + 1 :=
    altQuot_mul_c_add_one (b : ℤ) q hqodd
  have habZ : (a : ℤ) ^ p = (b : ℤ) ^ q + 1 := by exact_mod_cast hab
  have hprod : (a : ℤ) ^ p = altQuot (b : ℤ) q * ((b : ℤ) + 1) := by
    rw [habZ, ← hfact]
  have hb1ne : ((b : ℤ) + 1) ≠ 0 := by positivity
  have haZ : (a : ℤ) ≠ 0 := by
    intro h
    have hzp : (a : ℤ) ^ p = 0 := by rw [h]; exact zero_pow (by omega)
    rw [hzp] at habZ
    have hbq : (0 : ℤ) ≤ (b : ℤ) ^ q := by positivity
    omega
  have haltne : altQuot (b : ℤ) q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact (pow_ne_zero p haZ) hprod
  have hvalt1 : padicValInt q (altQuot (b : ℤ) q) = 1 := by
    obtain ⟨hd, hnd⟩ := cassels_vq_altQuot_eq_one q hq hq2 (b : ℤ) hqb
    have hge1 : 1 ≤ padicValInt q (altQuot (b : ℤ) q) := by
      rcases (padicValInt_dvd_iff_of_ne_one hq.ne_one 1
          (altQuot (b : ℤ) q)).mp (by simpa using hd) with h0 | hle
      · exact absurd h0 haltne
      · exact hle
    have hle1 : padicValInt q (altQuot (b : ℤ) q) ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have h2le : 2 ≤ padicValInt q (altQuot (b : ℤ) q) := by omega
      exact hnd ((padicValInt_dvd_iff_of_ne_one hq.ne_one 2
        (altQuot (b : ℤ) q)).mpr (Or.inr h2le))
    omega
  have hpow : padicValInt q ((a : ℤ) ^ p)
      = p * padicValInt q (a : ℤ) := by
    unfold padicValInt
    rw [Int.natAbs_pow,
      padicValNat.pow p (Int.natAbs_ne_zero.mpr haZ)]
  have hmul : padicValInt q ((a : ℤ) ^ p)
      = padicValInt q (altQuot (b : ℤ) q)
        + padicValInt q ((b : ℤ) + 1) := by
    rw [hprod]; exact padicValInt.mul haltne hb1ne
  rw [hpow, hvalt1] at hmul
  exact ⟨padicValInt q (a : ℤ), by omega⟩

/-- `−1` case: `q ∣ (b−1)`, `a^p = b^q−1`, `b ≥ 2` ⟹
`p ∣ (v_q(b−1) + 1)`. -/
theorem cassels_p_dvd_vq_succ_minus
    (p q a b : ℕ) (hp : 0 < p) (hq : q.Prime) (hq2 : 2 < q)
    (hb : 2 ≤ b) (hqb : (q : ℤ) ∣ ((b : ℤ) - 1))
    (hab : a ^ p = b ^ q - 1) :
    p ∣ (padicValInt q ((b : ℤ) - 1) + 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hbqpos : 1 ≤ b ^ q := Nat.one_le_pow _ _ (by omega)
  have hfact : posQuot (b : ℤ) q * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 :=
    posQuot_mul_c_sub_one (b : ℤ) q
  have habZ : (a : ℤ) ^ p = (b : ℤ) ^ q - 1 := by
    have hc : ((b ^ q - 1 : ℕ) : ℤ) = (b : ℤ) ^ q - 1 := by
      rw [Nat.cast_sub hbqpos, Nat.cast_pow, Nat.cast_one]
    rw [← hc]; exact_mod_cast hab
  have hprod : (a : ℤ) ^ p = posQuot (b : ℤ) q * ((b : ℤ) - 1) := by
    rw [habZ, ← hfact]
  have hb1ne : ((b : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    intro h; omega
  have haZ : (a : ℤ) ≠ 0 := by
    intro h
    have hzp : (a : ℤ) ^ p = 0 := by rw [h]; exact zero_pow (by omega)
    rw [hzp] at habZ
    have hb2q : 2 ≤ b ^ q :=
      le_trans hb (Nat.le_self_pow (by omega : q ≠ 0) b)
    have hbge2 : (2 : ℤ) ≤ (b : ℤ) ^ q := by exact_mod_cast hb2q
    omega
  have hposne : posQuot (b : ℤ) q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact (pow_ne_zero p haZ) hprod
  have hvpos1 : padicValInt q (posQuot (b : ℤ) q) = 1 := by
    obtain ⟨hd, hnd⟩ := cassels_vq_posQuot_eq_one q hq hq2 (b : ℤ) hqb
    have hge1 : 1 ≤ padicValInt q (posQuot (b : ℤ) q) := by
      rcases (padicValInt_dvd_iff_of_ne_one hq.ne_one 1
          (posQuot (b : ℤ) q)).mp (by simpa using hd) with h0 | hle
      · exact absurd h0 hposne
      · exact hle
    have hle1 : padicValInt q (posQuot (b : ℤ) q) ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have h2le : 2 ≤ padicValInt q (posQuot (b : ℤ) q) := by omega
      exact hnd ((padicValInt_dvd_iff_of_ne_one hq.ne_one 2
        (posQuot (b : ℤ) q)).mpr (Or.inr h2le))
    omega
  have hpow : padicValInt q ((a : ℤ) ^ p)
      = p * padicValInt q (a : ℤ) := by
    unfold padicValInt
    rw [Int.natAbs_pow,
      padicValNat.pow p (Int.natAbs_ne_zero.mpr haZ)]
  have hmul : padicValInt q ((a : ℤ) ^ p)
      = padicValInt q (posQuot (b : ℤ) q)
        + padicValInt q ((b : ℤ) - 1) := by
    rw [hprod]; exact padicValInt.mul hposne hb1ne
  rw [hpow, hvpos1] at hmul
  exact ⟨padicValInt q (a : ℤ), by omega⟩

/-! ### Cassels Corollary 1 of Lemma 2 — coprime `p`-th-power split

`a^p = b^q+1`, `q ∣ (b+1)`  ⟹  `b+1 = q^j · u^p` where
`j = padicValNat q (b+1)` and `p ∣ (j+1)`.  (Cassels' `b+1 =
q^{p-1}·u^p` is the `j=p−1` instance, i.e. `v_q(a)=1`.)
Fork-independent; the genuine content of Cassels eq 4-8. -/
theorem cassels_cor1_split_plus
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hq2 : 2 < q)
    (hb : 2 ≤ b) (hqb : q ∣ (b + 1))
    (hab : a ^ p = b ^ q + 1) :
    ∃ u : ℕ, b + 1 = q ^ padicValNat q (b + 1) * u ^ p
      ∧ p ∣ (padicValNat q (b + 1) + 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hqbZ : (q : ℤ) ∣ ((b : ℤ) + 1) := by exact_mod_cast hqb
  have hbZ1 : ((b : ℤ) + 1) ≠ 0 := by positivity
  have hfact : altQuot (b : ℤ) q * ((b : ℤ) + 1) = (b : ℤ) ^ q + 1 :=
    altQuot_mul_c_add_one (b : ℤ) q hq_odd
  have hdvdN : (b + 1) ∣ (b ^ q + 1) := by
    have hZ : ((b : ℤ) + 1) ∣ ((b : ℤ) ^ q + 1) :=
      ⟨altQuot (b : ℤ) q, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((b + 1 : ℕ) : ℤ) ∣ ((b ^ q + 1 : ℕ) : ℤ) := by
      push_cast; exact hZ
    exact_mod_cast h2
  set Q := (b ^ q + 1) / (b + 1) with hQ
  have hQmul : (b + 1) * Q = b ^ q + 1 := Nat.mul_div_cancel' hdvdN
  have hprodN : (b + 1) * Q = a ^ p := by rw [hQmul, ← hab]
  have haltQ : altQuot (b : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((b : ℤ) + 1) = (b : ℤ) ^ q + 1 := by
      have hc : ((b + 1 : ℕ) : ℤ) * (Q : ℤ) = ((b ^ q + 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      push_cast at hc; rw [mul_comm]; exact hc
    exact mul_right_cancel₀ hbZ1 (hfact.trans hQZ.symm)
  -- Nat.gcd (b+1) Q = q
  have hgcdZ := cassels_gcd_add_eq_q q hq hq2 (b : ℤ) hqbZ
  rw [haltQ] at hgcdZ
  have hbridge : Int.gcd (Q : ℤ) ((b : ℤ) + 1) = Nat.gcd Q (b + 1) := by
    have hb1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hb1, Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [hbridge] at hgcdZ
  have hgcdN : Nat.gcd (b + 1) Q = q := by
    rw [Nat.gcd_comm]; exact hgcdZ
  -- v_q(Q) = 1 ⇒ Q = q * t, q ∤ t
  have hvq := cassels_vq_altQuot_eq_one q hq hq2 (b : ℤ) hqbZ
  rw [haltQ] at hvq
  obtain ⟨hqQZ, hnqQZ⟩ := hvq
  have hqQ : q ∣ Q := by exact_mod_cast hqQZ
  have hnq2Q : ¬ q ^ 2 ∣ Q := by
    intro h
    exact hnqQZ (by exact_mod_cast h)
  set t := Q / q with ht
  have hQt : Q = q * t := (Nat.mul_div_cancel' hqQ).symm
  have hqt : ¬ q ∣ t := by
    intro ⟨c, hc⟩
    exact hnq2Q ⟨c, by rw [hQt, hc]; ring⟩
  -- b+1 = q^j * s, q ∤ s
  set j := padicValNat q (b + 1) with hj
  have hb1ne : b + 1 ≠ 0 := by omega
  have hqjdvd : q ^ j ∣ (b + 1) := pow_padicValNat_dvd
  set s := (b + 1) / q ^ j with hs
  have hb1split : b + 1 = q ^ j * s :=
    (Nat.mul_div_cancel' hqjdvd).symm
  have hqs : ¬ q ∣ s := by
    intro ⟨c, hc⟩
    have hd : q ^ (j + 1) ∣ (b + 1) := by
      rw [hb1split, hc, pow_succ]; exact ⟨c, by ring⟩
    exact (pow_succ_padicValNat_not_dvd (p := q) hb1ne) hd
  -- a^p = q^(j+1) * (s*t)
  have hap_eq : a ^ p = q ^ (j + 1) * (s * t) := by
    rw [← hprodN, hb1split, hQt, pow_succ]; ring
  -- Coprime s t  (gcd s t ∣ gcd (b+1) Q = q, and q ∤ s)
  have hst_cop : Nat.Coprime s t := by
    have hsdvd : s ∣ (b + 1) := ⟨q ^ j, by rw [hb1split]; ring⟩
    have htdvd : t ∣ Q := ⟨q, by rw [hQt]; ring⟩
    have hgst : Nat.gcd s t ∣ q := by
      have : Nat.gcd s t ∣ Nat.gcd (b + 1) Q :=
        Nat.dvd_gcd
          (dvd_trans (Nat.gcd_dvd_left s t) hsdvd)
          (dvd_trans (Nat.gcd_dvd_right s t) htdvd)
      rwa [hgcdN] at this
    rcases (Nat.dvd_prime hq).mp hgst with h1 | hqg
    · exact h1
    · exact absurd (hqg ▸ Nat.gcd_dvd_left s t) hqs
  -- Coprime (q^(j+1)) (s*t)
  have hq_nmst : ¬ q ∣ (s * t) := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with hs' | ht'
    · exact hqs hs'
    · exact hqt ht'
  have hcop_main : Nat.Coprime (q ^ (j + 1)) (s * t) :=
    Nat.Coprime.pow_left _
      ((hq.coprime_iff_not_dvd).mpr hq_nmst)
  -- extract: s*t is a p-th power, then s is (Coprime s t)
  have hcop_main' : Nat.Coprime (s * t) (q ^ (j + 1)) := hcop_main.symm
  have hunit1 : IsUnit (gcd (s * t) (q ^ (j + 1))) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop_main'
  have hprod1 : (s * t) * (q ^ (j + 1)) = a ^ p := by
    rw [hap_eq]; ring
  obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hunit1 hprod1
  -- hy : s * t = y ^ p ; now split via Coprime s t
  have hunit2 : IsUnit (gcd s t) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hst_cop
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit2 hy
  -- p ∣ (j+1)  via cassels_p_dvd_vq_succ_plus
  have hpj : p ∣ (padicValNat q (b + 1) + 1) := by
    have hpos := cassels_p_dvd_vq_succ_plus p q a b hp.pos hq hq2 hb
      hqbZ hab
    have hcastpv : padicValInt q ((b : ℤ) + 1) = padicValNat q (b + 1) := by
      rw [show ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) by push_cast; ring]
      exact padicValInt.of_nat
    rwa [hcastpv] at hpos
  exact ⟨u, by rw [hb1split, hu], by rw [hj]; exact hpj⟩

/-- **Cassels Cor 1 of Lemma 2 (`−1` case).**  `a^p = b^q−1`,
`q ∣ (b−1)`, `b ≥ 2`  ⟹  `b−1 = q^j · u^p` where
`j = padicValNat q (b−1)` and `p ∣ (j+1)`.  Symmetric mirror of
`cassels_cor1_split_plus` via `posQuot`. -/
theorem cassels_cor1_split_minus
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hq2 : 2 < q)
    (hb : 2 ≤ b) (hqb : q ∣ (b - 1))
    (hab : a ^ p = b ^ q - 1) :
    ∃ u : ℕ, b - 1 = q ^ padicValNat q (b - 1) * u ^ p
      ∧ p ∣ (padicValNat q (b - 1) + 1) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h1b : (1 : ℕ) ≤ b := by omega
  have hbqpos : 1 ≤ b ^ q := Nat.one_le_pow _ _ (by omega)
  have hqbZ : (q : ℤ) ∣ ((b : ℤ) - 1) := by
    have hc : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
      rw [Nat.cast_sub h1b, Nat.cast_one]
    rw [← hc]; exact_mod_cast hqb
  have hcastm1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub h1b, Nat.cast_one]
  have hcastbq : ((b ^ q - 1 : ℕ) : ℤ) = (b : ℤ) ^ q - 1 := by
    rw [Nat.cast_sub hbqpos, Nat.cast_pow, Nat.cast_one]
  have hbZ1 : ((b : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    intro h; omega
  have hfact : posQuot (b : ℤ) q * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 :=
    posQuot_mul_c_sub_one (b : ℤ) q
  have hdvdN : (b - 1) ∣ (b ^ q - 1) := by
    have hZ : ((b : ℤ) - 1) ∣ ((b : ℤ) ^ q - 1) :=
      ⟨posQuot (b : ℤ) q, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((b - 1 : ℕ) : ℤ) ∣ ((b ^ q - 1 : ℕ) : ℤ) := by
      rw [hcastm1, hcastbq]; exact hZ
    exact_mod_cast h2
  set Q := (b ^ q - 1) / (b - 1) with hQ
  have hQmul : (b - 1) * Q = b ^ q - 1 := Nat.mul_div_cancel' hdvdN
  have hprodN : (b - 1) * Q = a ^ p := by rw [hQmul, ← hab]
  have hposQ : posQuot (b : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 := by
      have hc : ((b - 1 : ℕ) : ℤ) * (Q : ℤ) = ((b ^ q - 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      rw [hcastm1, hcastbq] at hc
      rw [mul_comm]; exact hc
    exact mul_right_cancel₀ hbZ1 (hfact.trans hQZ.symm)
  have hgcdZ := cassels_gcd_sub_eq_q q hq hq2 (b : ℤ) hqbZ
  rw [hposQ] at hgcdZ
  have hbridge : Int.gcd (Q : ℤ) ((b : ℤ) - 1) = Nat.gcd Q (b - 1) := by
    rw [← hcastm1, Int.gcd_eq_natAbs, Int.natAbs_natCast,
      Int.natAbs_natCast]
  rw [hbridge] at hgcdZ
  have hgcdN : Nat.gcd (b - 1) Q = q := by
    rw [Nat.gcd_comm]; exact hgcdZ
  have hvq := cassels_vq_posQuot_eq_one q hq hq2 (b : ℤ) hqbZ
  rw [hposQ] at hvq
  obtain ⟨hqQZ, hnqQZ⟩ := hvq
  have hqQ : q ∣ Q := by exact_mod_cast hqQZ
  have hnq2Q : ¬ q ^ 2 ∣ Q := by
    intro h
    exact hnqQZ (by exact_mod_cast h)
  set t := Q / q with ht
  have hQt : Q = q * t := (Nat.mul_div_cancel' hqQ).symm
  have hqt : ¬ q ∣ t := by
    intro ⟨c, hc⟩
    exact hnq2Q ⟨c, by rw [hQt, hc]; ring⟩
  set j := padicValNat q (b - 1) with hj
  have hb1ne : b - 1 ≠ 0 := by omega
  have hqjdvd : q ^ j ∣ (b - 1) := pow_padicValNat_dvd
  set s := (b - 1) / q ^ j with hs
  have hb1split : b - 1 = q ^ j * s :=
    (Nat.mul_div_cancel' hqjdvd).symm
  have hqs : ¬ q ∣ s := by
    intro ⟨c, hc⟩
    have hd : q ^ (j + 1) ∣ (b - 1) := by
      rw [hb1split, hc, pow_succ]; exact ⟨c, by ring⟩
    exact (pow_succ_padicValNat_not_dvd (p := q) hb1ne) hd
  have hap_eq : a ^ p = q ^ (j + 1) * (s * t) := by
    rw [← hprodN, hb1split, hQt, pow_succ]; ring
  have hst_cop : Nat.Coprime s t := by
    have hsdvd : s ∣ (b - 1) := ⟨q ^ j, by rw [hb1split]; ring⟩
    have htdvd : t ∣ Q := ⟨q, by rw [hQt]; ring⟩
    have hgst : Nat.gcd s t ∣ q := by
      have : Nat.gcd s t ∣ Nat.gcd (b - 1) Q :=
        Nat.dvd_gcd
          (dvd_trans (Nat.gcd_dvd_left s t) hsdvd)
          (dvd_trans (Nat.gcd_dvd_right s t) htdvd)
      rwa [hgcdN] at this
    rcases (Nat.dvd_prime hq).mp hgst with h1 | hqg
    · exact h1
    · exact absurd (hqg ▸ Nat.gcd_dvd_left s t) hqs
  have hq_nmst : ¬ q ∣ (s * t) := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with hs' | ht'
    · exact hqs hs'
    · exact hqt ht'
  have hcop_main : Nat.Coprime (q ^ (j + 1)) (s * t) :=
    Nat.Coprime.pow_left _
      ((hq.coprime_iff_not_dvd).mpr hq_nmst)
  have hcop_main' : Nat.Coprime (s * t) (q ^ (j + 1)) := hcop_main.symm
  have hunit1 : IsUnit (gcd (s * t) (q ^ (j + 1))) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop_main'
  have hprod1 : (s * t) * (q ^ (j + 1)) = a ^ p := by
    rw [hap_eq]; ring
  obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hunit1 hprod1
  have hunit2 : IsUnit (gcd s t) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hst_cop
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit2 hy
  have hpj : p ∣ (padicValNat q (b - 1) + 1) := by
    have hpos := cassels_p_dvd_vq_succ_minus p q a b hp.pos hq hq2 hb
      hqbZ hab
    have hcastpv : padicValInt q ((b : ℤ) - 1) = padicValNat q (b - 1) := by
      rw [← hcastm1]; exact padicValInt.of_nat
    rwa [hcastpv] at hpos
  exact ⟨u, by rw [hb1split, hu], by rw [hj]; exact hpj⟩

/-- **Cassels Cor 2 of Lemma 2 (`+1`), product form.**  `a^p=b^q+1`,
`q ∣ (b+1)`  ⟹  `∃ k u w, 0 < k ∧ a = q^k·u·w ∧ q∤u ∧ q∤w`.
Cassels' `a = quv` is the `k=1` (v_q(a)=1) instance. -/
theorem cassels_cor2_a_factor_plus
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hq2 : 2 < q)
    (hb : 2 ≤ b) (hqb : q ∣ (b + 1))
    (hab : a ^ p = b ^ q + 1) :
    ∃ k u w : ℕ, 0 < k ∧ a = q ^ k * u * w ∧ ¬ q ∣ u ∧ ¬ q ∣ w := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_odd : Odd q := hq.odd_of_ne_two (by omega)
  have hqbZ : (q : ℤ) ∣ ((b : ℤ) + 1) := by exact_mod_cast hqb
  have hbZ1 : ((b : ℤ) + 1) ≠ 0 := by positivity
  have hfact : altQuot (b : ℤ) q * ((b : ℤ) + 1) = (b : ℤ) ^ q + 1 :=
    altQuot_mul_c_add_one (b : ℤ) q hq_odd
  have hdvdN : (b + 1) ∣ (b ^ q + 1) := by
    have hZ : ((b : ℤ) + 1) ∣ ((b : ℤ) ^ q + 1) :=
      ⟨altQuot (b : ℤ) q, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((b + 1 : ℕ) : ℤ) ∣ ((b ^ q + 1 : ℕ) : ℤ) := by
      push_cast; exact hZ
    exact_mod_cast h2
  set Q := (b ^ q + 1) / (b + 1) with hQ
  have hQmul : (b + 1) * Q = b ^ q + 1 := Nat.mul_div_cancel' hdvdN
  have hprodN : (b + 1) * Q = a ^ p := by rw [hQmul, ← hab]
  have haltQ : altQuot (b : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((b : ℤ) + 1) = (b : ℤ) ^ q + 1 := by
      have hc : ((b + 1 : ℕ) : ℤ) * (Q : ℤ) = ((b ^ q + 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      push_cast at hc; rw [mul_comm]; exact hc
    exact mul_right_cancel₀ hbZ1 (hfact.trans hQZ.symm)
  have hgcdZ := cassels_gcd_add_eq_q q hq hq2 (b : ℤ) hqbZ
  rw [haltQ] at hgcdZ
  have hbridge : Int.gcd (Q : ℤ) ((b : ℤ) + 1) = Nat.gcd Q (b + 1) := by
    have hb1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hb1, Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [hbridge] at hgcdZ
  have hgcdN : Nat.gcd (b + 1) Q = q := by rw [Nat.gcd_comm]; exact hgcdZ
  have hvq := cassels_vq_altQuot_eq_one q hq hq2 (b : ℤ) hqbZ
  rw [haltQ] at hvq
  obtain ⟨hqQZ, hnqQZ⟩ := hvq
  have hqQ : q ∣ Q := by exact_mod_cast hqQZ
  have hnq2Q : ¬ q ^ 2 ∣ Q := fun h => hnqQZ (by exact_mod_cast h)
  set t := Q / q with ht
  have hQt : Q = q * t := (Nat.mul_div_cancel' hqQ).symm
  have hqt : ¬ q ∣ t := fun ⟨c, hc⟩ => hnq2Q ⟨c, by rw [hQt, hc]; ring⟩
  set j := padicValNat q (b + 1) with hj
  have hb1ne : b + 1 ≠ 0 := by omega
  have hqjdvd : q ^ j ∣ (b + 1) := pow_padicValNat_dvd
  set s := (b + 1) / q ^ j with hs
  have hb1split : b + 1 = q ^ j * s := (Nat.mul_div_cancel' hqjdvd).symm
  have hqs : ¬ q ∣ s := by
    intro ⟨c, hc⟩
    have hd : q ^ (j + 1) ∣ (b + 1) := by
      rw [hb1split, hc, pow_succ]; exact ⟨c, by ring⟩
    exact (pow_succ_padicValNat_not_dvd (p := q) hb1ne) hd
  have hap_eq : a ^ p = q ^ (j + 1) * (s * t) := by
    rw [← hprodN, hb1split, hQt, pow_succ]; ring
  have hst_cop : Nat.Coprime s t := by
    have hsdvd : s ∣ (b + 1) := ⟨q ^ j, by rw [hb1split]; ring⟩
    have htdvd : t ∣ Q := ⟨q, by rw [hQt]; ring⟩
    have hgst : Nat.gcd s t ∣ q := by
      have : Nat.gcd s t ∣ Nat.gcd (b + 1) Q :=
        Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left s t) hsdvd)
          (dvd_trans (Nat.gcd_dvd_right s t) htdvd)
      rwa [hgcdN] at this
    rcases (Nat.dvd_prime hq).mp hgst with h1 | hqg
    · exact h1
    · exact absurd (hqg ▸ Nat.gcd_dvd_left s t) hqs
  have hq_nmst : ¬ q ∣ (s * t) := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with hs' | ht'
    · exact hqs hs'
    · exact hqt ht'
  have hcop_main : Nat.Coprime (q ^ (j + 1)) (s * t) :=
    Nat.Coprime.pow_left _ ((hq.coprime_iff_not_dvd).mpr hq_nmst)
  -- s, t each p-th powers
  have hunit1 : IsUnit (gcd (s * t) (q ^ (j + 1))) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop_main.symm
  have hprod1 : (s * t) * (q ^ (j + 1)) = a ^ p := by rw [hap_eq]; ring
  obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hunit1 hprod1
  have hunit2 : IsUnit (gcd s t) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]; simpa [Nat.Coprime] using hst_cop
  obtain ⟨uu, huu⟩ := exists_eq_pow_of_mul_eq_pow hunit2 hy
  have hunit3 : IsUnit (gcd t s) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hst_cop.symm
  obtain ⟨ww, hww⟩ :=
    exists_eq_pow_of_mul_eq_pow hunit3 (by rw [Nat.mul_comm]; exact hy)
  -- p ∣ (j+1) ⇒ j+1 = p*k, k>0
  have hpj : p ∣ (j + 1) := by
    have hpos := cassels_p_dvd_vq_succ_plus p q a b hp.pos hq hq2 hb
      hqbZ hab
    have hcastpv : padicValInt q ((b : ℤ) + 1) = padicValNat q (b + 1) := by
      rw [show ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) by push_cast; ring]
      exact padicValInt.of_nat
    rw [hcastpv] at hpos; rw [hj]; exact hpos
  obtain ⟨k, hk⟩ := hpj
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · simp [h0] at hk
    · exact hpos
  -- a^p = (q^k * uu * ww)^p ⇒ a = q^k*uu*ww
  have hap2 : a ^ p = (q ^ k * uu * ww) ^ p := by
    rw [hap_eq, huu, hww, hk, mul_pow, mul_pow, ← pow_mul,
      Nat.mul_comm p k]
    ring
  have haeq : a = q ^ k * uu * ww :=
    Nat.pow_left_injective hp.pos.ne' hap2
  have hquu : ¬ q ∣ uu :=
    fun h => hqs (huu ▸ dvd_pow h hp.pos.ne')
  have hqww : ¬ q ∣ ww :=
    fun h => hqt (hww ▸ dvd_pow h hp.pos.ne')
  exact ⟨k, uu, ww, hkpos, haeq, hquu, hqww⟩

/-- **Cassels Cor 2 of Lemma 2 (`−1`), product form.**  `a^p=b^q−1`,
`q ∣ (b−1)`, `b ≥ 2`  ⟹  `∃ k u w, 0<k ∧ a = q^k·u·w ∧ q∤u ∧ q∤w`. -/
theorem cassels_cor2_a_factor_minus
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hq2 : 2 < q)
    (hb : 2 ≤ b) (hqb : q ∣ (b - 1))
    (hab : a ^ p = b ^ q - 1) :
    ∃ k u w : ℕ, 0 < k ∧ a = q ^ k * u * w ∧ ¬ q ∣ u ∧ ¬ q ∣ w := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h1b : (1 : ℕ) ≤ b := by omega
  have hbqpos : 1 ≤ b ^ q := Nat.one_le_pow _ _ (by omega)
  have hqbZ : (q : ℤ) ∣ ((b : ℤ) - 1) := by
    have hc : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
      rw [Nat.cast_sub h1b, Nat.cast_one]
    rw [← hc]; exact_mod_cast hqb
  have hcastm1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub h1b, Nat.cast_one]
  have hcastbq : ((b ^ q - 1 : ℕ) : ℤ) = (b : ℤ) ^ q - 1 := by
    rw [Nat.cast_sub hbqpos, Nat.cast_pow, Nat.cast_one]
  have hbZ1 : ((b : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    intro h; omega
  have hfact : posQuot (b : ℤ) q * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 :=
    posQuot_mul_c_sub_one (b : ℤ) q
  have hdvdN : (b - 1) ∣ (b ^ q - 1) := by
    have hZ : ((b : ℤ) - 1) ∣ ((b : ℤ) ^ q - 1) :=
      ⟨posQuot (b : ℤ) q, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((b - 1 : ℕ) : ℤ) ∣ ((b ^ q - 1 : ℕ) : ℤ) := by
      rw [hcastm1, hcastbq]; exact hZ
    exact_mod_cast h2
  set Q := (b ^ q - 1) / (b - 1) with hQ
  have hQmul : (b - 1) * Q = b ^ q - 1 := Nat.mul_div_cancel' hdvdN
  have hprodN : (b - 1) * Q = a ^ p := by rw [hQmul, ← hab]
  have hposQ : posQuot (b : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 := by
      have hc : ((b - 1 : ℕ) : ℤ) * (Q : ℤ) = ((b ^ q - 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      rw [hcastm1, hcastbq] at hc
      rw [mul_comm]; exact hc
    exact mul_right_cancel₀ hbZ1 (hfact.trans hQZ.symm)
  have hgcdZ := cassels_gcd_sub_eq_q q hq hq2 (b : ℤ) hqbZ
  rw [hposQ] at hgcdZ
  have hbridge : Int.gcd (Q : ℤ) ((b : ℤ) - 1) = Nat.gcd Q (b - 1) := by
    rw [← hcastm1, Int.gcd_eq_natAbs, Int.natAbs_natCast,
      Int.natAbs_natCast]
  rw [hbridge] at hgcdZ
  have hgcdN : Nat.gcd (b - 1) Q = q := by
    rw [Nat.gcd_comm]; exact hgcdZ
  have hvq := cassels_vq_posQuot_eq_one q hq hq2 (b : ℤ) hqbZ
  rw [hposQ] at hvq
  obtain ⟨hqQZ, hnqQZ⟩ := hvq
  have hqQ : q ∣ Q := by exact_mod_cast hqQZ
  have hnq2Q : ¬ q ^ 2 ∣ Q := fun h => hnqQZ (by exact_mod_cast h)
  set t := Q / q with ht
  have hQt : Q = q * t := (Nat.mul_div_cancel' hqQ).symm
  have hqt : ¬ q ∣ t := fun ⟨c, hc⟩ => hnq2Q ⟨c, by rw [hQt, hc]; ring⟩
  set j := padicValNat q (b - 1) with hj
  have hb1ne : b - 1 ≠ 0 := by omega
  have hqjdvd : q ^ j ∣ (b - 1) := pow_padicValNat_dvd
  set s := (b - 1) / q ^ j with hs
  have hb1split : b - 1 = q ^ j * s := (Nat.mul_div_cancel' hqjdvd).symm
  have hqs : ¬ q ∣ s := by
    intro ⟨c, hc⟩
    have hd : q ^ (j + 1) ∣ (b - 1) := by
      rw [hb1split, hc, pow_succ]; exact ⟨c, by ring⟩
    exact (pow_succ_padicValNat_not_dvd (p := q) hb1ne) hd
  have hap_eq : a ^ p = q ^ (j + 1) * (s * t) := by
    rw [← hprodN, hb1split, hQt, pow_succ]; ring
  have hst_cop : Nat.Coprime s t := by
    have hsdvd : s ∣ (b - 1) := ⟨q ^ j, by rw [hb1split]; ring⟩
    have htdvd : t ∣ Q := ⟨q, by rw [hQt]; ring⟩
    have hgst : Nat.gcd s t ∣ q := by
      have : Nat.gcd s t ∣ Nat.gcd (b - 1) Q :=
        Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left s t) hsdvd)
          (dvd_trans (Nat.gcd_dvd_right s t) htdvd)
      rwa [hgcdN] at this
    rcases (Nat.dvd_prime hq).mp hgst with h1 | hqg
    · exact h1
    · exact absurd (hqg ▸ Nat.gcd_dvd_left s t) hqs
  have hq_nmst : ¬ q ∣ (s * t) := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with hs' | ht'
    · exact hqs hs'
    · exact hqt ht'
  have hcop_main : Nat.Coprime (q ^ (j + 1)) (s * t) :=
    Nat.Coprime.pow_left _ ((hq.coprime_iff_not_dvd).mpr hq_nmst)
  have hunit1 : IsUnit (gcd (s * t) (q ^ (j + 1))) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop_main.symm
  have hprod1 : (s * t) * (q ^ (j + 1)) = a ^ p := by rw [hap_eq]; ring
  obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hunit1 hprod1
  have hunit2 : IsUnit (gcd s t) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]; simpa [Nat.Coprime] using hst_cop
  obtain ⟨uu, huu⟩ := exists_eq_pow_of_mul_eq_pow hunit2 hy
  have hunit3 : IsUnit (gcd t s) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hst_cop.symm
  obtain ⟨ww, hww⟩ :=
    exists_eq_pow_of_mul_eq_pow hunit3 (by rw [Nat.mul_comm]; exact hy)
  have hpj : p ∣ (j + 1) := by
    have hpos := cassels_p_dvd_vq_succ_minus p q a b hp.pos hq hq2 hb
      hqbZ hab
    have hcastpv : padicValInt q ((b : ℤ) - 1) = padicValNat q (b - 1) := by
      rw [← hcastm1]; exact padicValInt.of_nat
    rw [hcastpv] at hpos; rw [hj]; exact hpos
  obtain ⟨k, hk⟩ := hpj
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · simp [h0] at hk
    · exact hpos
  have hap2 : a ^ p = (q ^ k * uu * ww) ^ p := by
    rw [hap_eq, huu, hww, hk, mul_pow, mul_pow, ← pow_mul,
      Nat.mul_comm p k]
    ring
  have haeq : a = q ^ k * uu * ww :=
    Nat.pow_left_injective hp.pos.ne' hap2
  have hquu : ¬ q ∣ uu :=
    fun h => hqs (huu ▸ dvd_pow h hp.pos.ne')
  have hqww : ¬ q ∣ ww :=
    fun h => hqt (hww ▸ dvd_pow h hp.pos.ne')
  exact ⟨k, uu, ww, hkpos, haeq, hquu, hqww⟩

/-- Quotient half of Cassels Cor 1 (`−1` case).  If `a^p = b^q−1`
and the ramified prime `q` divides `b−1`, then the geometric quotient
`(b^q−1)/(b−1)` is exactly `q` times a `p`-th power. -/
theorem cassels_cor1_quot_split_minus
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hq2 : 2 < q)
    (hb : 2 ≤ b) (hqb : q ∣ (b - 1))
    (hab : a ^ p = b ^ q - 1) :
    ∃ w : ℕ, (b ^ q - 1) / (b - 1) = q * w ^ p := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h1b : (1 : ℕ) ≤ b := by omega
  have hbqpos : 1 ≤ b ^ q := Nat.one_le_pow _ _ (by omega)
  have hqbZ : (q : ℤ) ∣ ((b : ℤ) - 1) := by
    have hc : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
      rw [Nat.cast_sub h1b, Nat.cast_one]
    rw [← hc]; exact_mod_cast hqb
  have hcastm1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub h1b, Nat.cast_one]
  have hcastbq : ((b ^ q - 1 : ℕ) : ℤ) = (b : ℤ) ^ q - 1 := by
    rw [Nat.cast_sub hbqpos, Nat.cast_pow, Nat.cast_one]
  have hbZ1 : ((b : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    intro h; omega
  have hfact : posQuot (b : ℤ) q * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 :=
    posQuot_mul_c_sub_one (b : ℤ) q
  have hdvdN : (b - 1) ∣ (b ^ q - 1) := by
    have hZ : ((b : ℤ) - 1) ∣ ((b : ℤ) ^ q - 1) :=
      ⟨posQuot (b : ℤ) q, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((b - 1 : ℕ) : ℤ) ∣ ((b ^ q - 1 : ℕ) : ℤ) := by
      rw [hcastm1, hcastbq]; exact hZ
    exact_mod_cast h2
  set Q := (b ^ q - 1) / (b - 1) with hQ
  have hQmul : (b - 1) * Q = b ^ q - 1 := Nat.mul_div_cancel' hdvdN
  have hprodN : (b - 1) * Q = a ^ p := by rw [hQmul, ← hab]
  have hposQ : posQuot (b : ℤ) q = (Q : ℤ) := by
    have hQZ : (Q : ℤ) * ((b : ℤ) - 1) = (b : ℤ) ^ q - 1 := by
      have hc : ((b - 1 : ℕ) : ℤ) * (Q : ℤ) = ((b ^ q - 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hQmul
      rw [hcastm1, hcastbq] at hc
      rw [mul_comm]; exact hc
    exact mul_right_cancel₀ hbZ1 (hfact.trans hQZ.symm)
  have hgcdZ := cassels_gcd_sub_eq_q q hq hq2 (b : ℤ) hqbZ
  rw [hposQ] at hgcdZ
  have hbridge : Int.gcd (Q : ℤ) ((b : ℤ) - 1) = Nat.gcd Q (b - 1) := by
    rw [← hcastm1, Int.gcd_eq_natAbs, Int.natAbs_natCast,
      Int.natAbs_natCast]
  rw [hbridge] at hgcdZ
  have hgcdN : Nat.gcd (b - 1) Q = q := by
    rw [Nat.gcd_comm]; exact hgcdZ
  have hvq := cassels_vq_posQuot_eq_one q hq hq2 (b : ℤ) hqbZ
  rw [hposQ] at hvq
  obtain ⟨hqQZ, hnqQZ⟩ := hvq
  have hqQ : q ∣ Q := by exact_mod_cast hqQZ
  have hnq2Q : ¬ q ^ 2 ∣ Q := fun h => hnqQZ (by exact_mod_cast h)
  set t := Q / q with ht
  have hQt : Q = q * t := (Nat.mul_div_cancel' hqQ).symm
  have hqt : ¬ q ∣ t := fun ⟨c, hc⟩ => hnq2Q ⟨c, by rw [hQt, hc]; ring⟩
  set j := padicValNat q (b - 1) with hj
  have hb1ne : b - 1 ≠ 0 := by omega
  have hqjdvd : q ^ j ∣ (b - 1) := pow_padicValNat_dvd
  set s := (b - 1) / q ^ j with hs
  have hb1split : b - 1 = q ^ j * s := (Nat.mul_div_cancel' hqjdvd).symm
  have hqs : ¬ q ∣ s := by
    intro ⟨c, hc⟩
    have hd : q ^ (j + 1) ∣ (b - 1) := by
      rw [hb1split, hc, pow_succ]; exact ⟨c, by ring⟩
    exact (pow_succ_padicValNat_not_dvd (p := q) hb1ne) hd
  have hap_eq : a ^ p = q ^ (j + 1) * (s * t) := by
    rw [← hprodN, hb1split, hQt, pow_succ]; ring
  have hst_cop : Nat.Coprime s t := by
    have hsdvd : s ∣ (b - 1) := ⟨q ^ j, by rw [hb1split]; ring⟩
    have htdvd : t ∣ Q := ⟨q, by rw [hQt]; ring⟩
    have hgst : Nat.gcd s t ∣ q := by
      have : Nat.gcd s t ∣ Nat.gcd (b - 1) Q :=
        Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left s t) hsdvd)
          (dvd_trans (Nat.gcd_dvd_right s t) htdvd)
      rwa [hgcdN] at this
    rcases (Nat.dvd_prime hq).mp hgst with h1 | hqg
    · exact h1
    · exact absurd (hqg ▸ Nat.gcd_dvd_left s t) hqs
  have hq_nmst : ¬ q ∣ (s * t) := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with hs' | ht'
    · exact hqs hs'
    · exact hqt ht'
  have hcop_main : Nat.Coprime (q ^ (j + 1)) (s * t) :=
    Nat.Coprime.pow_left _ ((hq.coprime_iff_not_dvd).mpr hq_nmst)
  have hunit1 : IsUnit (gcd (s * t) (q ^ (j + 1))) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop_main.symm
  have hprod1 : (s * t) * (q ^ (j + 1)) = a ^ p := by rw [hap_eq]; ring
  obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hunit1 hprod1
  have hunit3 : IsUnit (gcd t s) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hst_cop.symm
  obtain ⟨w, hww⟩ :=
    exists_eq_pow_of_mul_eq_pow hunit3 (by rw [Nat.mul_comm]; exact hy)
  exact ⟨w, by rw [hQt, hww]⟩

/-! ### Reductio substitution (Cassels-1960 4-14′ / Ribenboim A1.1)

The reductio that proves the `p ∣ a` half: if `b^q = a^p − 1` and
`p ∤ (a−1)` then `a − 1` is a perfect `q`-th power.  First-principles
mirror of Lemma 2's coprime extraction (NO degraded-OCR dependence):
`a^p−1 = (a−1)·posQuot a p`, Lemma 1 gives `gcd ∈ {1,p}`, `p∤(a−1)`
excludes `p`, so the coprime factors of the `q`-th power `b^q` are
each `q`-th powers. -/
theorem cassels_reductio_subst
    (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime)
    (ha : 2 ≤ a) (hpa1 : ¬ p ∣ (a - 1))
    (hbq : b ^ q = a ^ p - 1) :
    ∃ z : ℕ, a - 1 = z ^ q := by
  have h1a : (1 : ℕ) ≤ a := by omega
  have hap1 : 1 ≤ a ^ p := Nat.one_le_pow _ _ (by omega)
  have hcastm1 : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
    rw [Nat.cast_sub h1a, Nat.cast_one]
  have hcastap : ((a ^ p - 1 : ℕ) : ℤ) = (a : ℤ) ^ p - 1 := by
    rw [Nat.cast_sub hap1, Nat.cast_pow, Nat.cast_one]
  have haZ1 : ((a : ℤ) - 1) ≠ 0 := by
    have : (2 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    intro h; omega
  have hfact : posQuot (a : ℤ) p * ((a : ℤ) - 1) = (a : ℤ) ^ p - 1 :=
    posQuot_mul_c_sub_one (a : ℤ) p
  have hdvdN : (a - 1) ∣ (a ^ p - 1) := by
    have hZ : ((a : ℤ) - 1) ∣ ((a : ℤ) ^ p - 1) :=
      ⟨posQuot (a : ℤ) p, by rw [mul_comm]; exact hfact.symm⟩
    have h2 : ((a - 1 : ℕ) : ℤ) ∣ ((a ^ p - 1 : ℕ) : ℤ) := by
      rw [hcastm1, hcastap]; exact hZ
    exact_mod_cast h2
  set R := (a ^ p - 1) / (a - 1) with hR
  have hRmul : (a - 1) * R = a ^ p - 1 := Nat.mul_div_cancel' hdvdN
  have hposR : posQuot (a : ℤ) p = (R : ℤ) := by
    have hRZ : (R : ℤ) * ((a : ℤ) - 1) = (a : ℤ) ^ p - 1 := by
      have hc : ((a - 1 : ℕ) : ℤ) * (R : ℤ) = ((a ^ p - 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hRmul
      rw [hcastm1, hcastap] at hc
      rw [mul_comm]; exact hc
    exact mul_right_cancel₀ haZ1 (hfact.trans hRZ.symm)
  have hgcdZ := cassels_lemma_1_sub_gcd_eq p hp (a : ℤ)
  rw [hposR] at hgcdZ
  have hbridge : Int.gcd (R : ℤ) ((a : ℤ) - 1) = Nat.gcd R (a - 1) := by
    rw [← hcastm1, Int.gcd_eq_natAbs, Int.natAbs_natCast,
      Int.natAbs_natCast]
  rw [hbridge] at hgcdZ
  have hcop : Nat.Coprime (a - 1) R := by
    rcases hgcdZ with h1 | hpe
    · simpa [Nat.Coprime, Nat.gcd_comm] using h1
    · exact absurd
        (dvd_trans (by rw [hpe] : p ∣ Nat.gcd R (a - 1))
          (Nat.gcd_dvd_right _ _)) hpa1
  have hprod : (a - 1) * R = b ^ q := by rw [hRmul, ← hbq]
  have hunit : IsUnit (gcd (a - 1) R) := by
    rw [gcd_eq_nat_gcd, Nat.isUnit_iff]
    simpa [Nat.Coprime] using hcop
  obtain ⟨z, hz⟩ := exists_eq_pow_of_mul_eq_pow hunit hprod
  exact ⟨z, hz⟩

/-! ### Scaffolding for B2.2: `padicValInt` over a `Finset.prod`

`v_ℓ(∏ f) = ∑ v_ℓ(f)` when every factor is nonzero and `ℓ` is
prime.  Needed by every proof strategy of the factorial-valuation
linchpin (Cassels B2.2). -/
theorem padicValInt_prod {ℓ : ℕ} [Fact ℓ.Prime]
    {α : Type*} (s : Finset α) (f : α → ℤ) (hf : ∀ a ∈ s, f a ≠ 0) :
    padicValInt ℓ (∏ a ∈ s, f a) = ∑ a ∈ s, padicValInt ℓ (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [padicValInt]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
      have hfs : (∏ x ∈ s, f x) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr
          (fun x hx => hf x (Finset.mem_insert_of_mem hx))
      rw [padicValInt.mul hfa hfs,
        ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))]

/-- Scaffolding for B2.2 (Legendre route): a fixed residue class
meets `r` consecutive naturals in at least `r / d` points. -/
theorem card_filter_mod_ge {d : ℕ} (hd : 0 < d) (c r : ℕ) :
    r / d ≤ ((Finset.range r).filter (fun i => i % d = c % d)).card := by
  classical
  set c' := c % d with hc'
  have hc'd : c' < d := Nat.mod_lt _ hd
  -- inject range (r/d) ↪ filtered set via j ↦ c' + j*d
  have hmap : ∀ j ∈ Finset.range (r / d),
      c' + j * d ∈ (Finset.range r).filter (fun i => i % d = c % d) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjd : j * d + d ≤ r / d * d := by
      have : j + 1 ≤ r / d := hj
      calc j * d + d = (j + 1) * d := by ring
        _ ≤ r / d * d := Nat.mul_le_mul_right d this
    have hbound : c' + j * d < r := by
      have hrd : r / d * d ≤ r := Nat.div_mul_le_self r d
      omega
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hbound, ?_⟩
    rw [← hc', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc'd]
  have hinj : Set.InjOn (fun j => c' + j * d)
      (Finset.range (r / d) : Set ℕ) := by
    intro x _ y _ hxy
    simp only at hxy
    have : x * d = y * d := by omega
    exact Nat.eq_of_mul_eq_mul_right hd this
  have := Finset.card_le_card_of_injOn (fun j => c' + j * d) hmap hinj
  simpa using this

/-- B2.2 scaffolding: when `gcd(q,d)=1`, the solutions of
`d ∣ (p − i·q)` over `ℤ` form a single residue class mod `d`
(via the `ZMod d` unit), so `≥ r/d` of `i ∈ range r` satisfy it. -/
theorem card_filter_dvd_ge {q d : ℕ} (hd : 0 < d)
    (hcop : Nat.Coprime q d) (p r : ℕ) :
    r / d ≤ ((Finset.range r).filter
      (fun i : ℕ => (d : ℤ) ∣ ((p : ℤ) - (i : ℤ) * q))).card := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set u : (ZMod d)ˣ := ZMod.unitOfCoprime q hcop with hu
  set w : ZMod d := (p : ZMod d) * ((u⁻¹ : (ZMod d)ˣ) : ZMod d) with hw
  set c : ℕ := w.val with hcdef
  have hclt : c < d := ZMod.val_lt w
  have hcmod : c % d = c := Nat.mod_eq_of_lt hclt
  have huq : ((u : (ZMod d)ˣ) : ZMod d) = (q : ZMod d) :=
    ZMod.coe_unitOfCoprime q hcop
  have hpred : ∀ i : ℕ,
      ((d : ℤ) ∣ ((p : ℤ) - (i : ℤ) * q)) ↔ i % d = c % d := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcast : (((p : ℤ) - (i : ℤ) * (q : ℤ) : ℤ) : ZMod d)
        = (p : ZMod d) - (i : ZMod d) * (q : ZMod d) := by push_cast; ring
    rw [hcast, hcmod, sub_eq_zero]
    have hiff1 : ((p : ZMod d) = (i : ZMod d) * (q : ZMod d))
        ↔ ((i : ZMod d) = w) := by
      rw [← huq, hw]
      constructor
      · intro h; rw [h, mul_assoc, Units.mul_inv, mul_one]
      · intro h; rw [h, mul_assoc, Units.inv_mul, mul_one]
    rw [hiff1]
    constructor
    · intro h
      have hv : ((i : ZMod d)).val = w.val := by rw [h]
      rw [ZMod.val_natCast] at hv
      rw [hcdef]; exact hv
    · intro h
      apply ZMod.val_injective d
      rw [ZMod.val_natCast, ← hcdef]; exact h
  have hfilter_eq : (Finset.range r).filter
      (fun i : ℕ => (d : ℤ) ∣ ((p : ℤ) - (i : ℤ) * q))
      = (Finset.range r).filter (fun i => i % d = c % d) :=
    Finset.filter_congr (fun i _ => hpred i)
  rw [hfilter_eq]
  exact card_filter_mod_ge hd c r

/-- B2.2 scaffolding: the `ℓ`-adic valuation of `m ≠ 0` as a sum of
divisibility indicators over `Ico 1 B` (`B` bigger than the
valuation).  `v_ℓ(m) = #{e ∈ [1,B) : ℓ^e ∣ m}`. -/
theorem padicValNat_eq_sum_ind {ℓ : ℕ} [Fact ℓ.Prime] {m B : ℕ}
    (hm : m ≠ 0) (hB : padicValNat ℓ m < B) :
    ∑ e ∈ Finset.Ico 1 B, (if ℓ ^ e ∣ m then 1 else 0)
      = padicValNat ℓ m := by
  classical
  set v := padicValNat ℓ m with hv
  have hcongr : ∀ e ∈ Finset.Ico 1 B,
      (if ℓ ^ e ∣ m then (1 : ℕ) else 0) = (if e ≤ v then 1 else 0) := by
    intro e _
    by_cases h : ℓ ^ e ∣ m
    · rw [if_pos h, if_pos ((padicValNat_dvd_iff_le hm).mp h)]
    · rw [if_neg h,
        if_neg (fun hle => h ((padicValNat_dvd_iff_le hm).mpr hle))]
  rw [Finset.sum_congr rfl hcongr, ← Finset.card_filter]
  have hset : (Finset.Ico 1 B).filter (fun e => e ≤ v)
      = Finset.Ico 1 (v + 1) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]
  omega

/-! ### Cassels-1960 Lemma B2.2 — the factorial-valuation linchpin

For a prime `ℓ ∤ q` and distinct primes `p ≠ q`:
`v_ℓ(r!) ≤ v_ℓ(∏_{i<r}(p − i·q))`.  This is WHY Cassels' binomial
truncation is `q^{O(N)}`-scale, not factorial-scale: for every
prime `ℓ ≠ q` the factorial `r!` is absorbed by the product, so
the only denominator the cleared truncation can carry is a power
of `q`.  Proof: Legendre + Fubini over the four scaffolding
bricks (`padicValInt_prod`, `padicValNat_eq_sum_ind`,
`card_filter_dvd_ge`, `padicValNat_factorial`). -/
theorem cassels_B22 {ℓ : ℕ} [Fact ℓ.Prime] {q : ℕ} (hℓq : ¬ ℓ ∣ q)
    {p : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (r : ℕ) :
    padicValNat ℓ (Nat.factorial r) ≤
      padicValInt ℓ (∏ i ∈ Finset.range r, ((p : ℤ) - (i : ℤ) * q)) := by
  classical
  have hℓ : ℓ.Prime := (inferInstance : Fact ℓ.Prime).out
  -- factors nonzero (p ≠ i*q for distinct primes)
  have hfac : ∀ i ∈ Finset.range r, ((p : ℤ) - (i : ℤ) * q) ≠ 0 := by
    intro i _ h
    have hpiqZ : (p : ℤ) = (i : ℤ) * q := by linarith
    have hpiq : p = i * q := by exact_mod_cast hpiqZ
    have hqp : q ∣ p := ⟨i, by rw [hpiq]; ring⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp q hqp) with h1 | h2
    · exact hq.ne_one h1
    · exact hpq h2.symm
  rw [padicValInt_prod _ _ hfac]
  set B := p + r * q + r + 2 with hBdef
  -- Coprime q (ℓ^e)
  have hcopℓ : ∀ e, Nat.Coprime q (ℓ ^ e) := by
    intro e
    exact (Nat.Coprime.pow_right e
      ((hℓ.coprime_iff_not_dvd.mpr hℓq).symm))
  -- per-i: padicValInt ℓ (p−iq) = ∑_{e∈Ico 1 B} [ℓ^e ∣ (p−iq)]ℤ
  have hpiB : ∀ i ∈ Finset.range r,
      padicValInt ℓ ((p : ℤ) - (i : ℤ) * q)
        = ∑ e ∈ Finset.Ico 1 B,
            (if (↑(ℓ ^ e) : ℤ) ∣ ((p : ℤ) - (i : ℤ) * q)
              then 1 else 0) := by
    intro i hi
    have hne := hfac i hi
    have hmne : (((p : ℤ) - (i : ℤ) * q)).natAbs ≠ 0 :=
      Int.natAbs_ne_zero.mpr hne
    rw [Finset.mem_range] at hi
    -- bound: v_ℓ(|x|) < B
    have hxle : (((p : ℤ) - (i : ℤ) * q)).natAbs ≤ p + r * q := by
      have habs : |((p : ℤ) - (i : ℤ) * q)| ≤ (p : ℤ) + r * q := by
        have hi' : (i : ℤ) ≤ (r : ℤ) := by exact_mod_cast Nat.le_of_lt hi
        rcases abs_cases ((p : ℤ) - (i : ℤ) * q) with
          ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
          nlinarith [Int.natCast_nonneg q, Int.natCast_nonneg i,
            Int.natCast_nonneg p, hi']
      have : ((((p : ℤ) - (i : ℤ) * q)).natAbs : ℤ) ≤ (p : ℤ) + r * q := by
        rw [← Int.abs_eq_natAbs]; exact habs
      exact_mod_cast this
    have hvb : padicValNat ℓ (((p : ℤ) - (i : ℤ) * q)).natAbs < B := by
      have hdvd : ℓ ^ padicValNat ℓ (((p : ℤ) - (i : ℤ) * q)).natAbs
          ∣ (((p : ℤ) - (i : ℤ) * q)).natAbs := pow_padicValNat_dvd
      have hle : ℓ ^ padicValNat ℓ (((p : ℤ) - (i : ℤ) * q)).natAbs
          ≤ (((p : ℤ) - (i : ℤ) * q)).natAbs :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hmne) hdvd
      have hlt : padicValNat ℓ (((p : ℤ) - (i : ℤ) * q)).natAbs
          < ℓ ^ padicValNat ℓ (((p : ℤ) - (i : ℤ) * q)).natAbs :=
        Nat.lt_pow_self hℓ.one_lt
      omega
    have := padicValNat_eq_sum_ind hmne hvb
    rw [show padicValInt ℓ ((p : ℤ) - (i : ℤ) * q)
        = padicValNat ℓ (((p : ℤ) - (i : ℤ) * q)).natAbs from rfl,
      ← this]
    apply Finset.sum_congr rfl
    intro e _
    have hiff : (ℓ ^ e ∣ (((p : ℤ) - (i : ℤ) * q)).natAbs)
        ↔ ((↑(ℓ ^ e) : ℤ) ∣ ((p : ℤ) - (i : ℤ) * q)) := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    simp only [hiff]
  rw [Finset.sum_congr rfl hpiB]
  -- Fubini: ∑_i ∑_e = ∑_e ∑_i
  rw [Finset.sum_comm]
  -- Legendre: v_ℓ(r!) = ∑_{e∈Ico 1 B} ⌊r/ℓ^e⌋
  have hlogB : Nat.log ℓ r < B := by
    have : Nat.log ℓ r ≤ r := Nat.log_le_self ℓ r
    omega
  rw [padicValNat_factorial hlogB]
  -- termwise: ⌊r/ℓ^e⌋ ≤ ∑_i [ℓ^e ∣ (p−iq)]
  apply Finset.sum_le_sum
  intro e he
  have hℓe : 0 < ℓ ^ e := pow_pos hℓ.pos e
  have hcount := card_filter_dvd_ge hℓe (hcopℓ e) p r
  calc r / ℓ ^ e
      ≤ ((Finset.range r).filter
          (fun i : ℕ => (↑(ℓ ^ e) : ℤ) ∣ ((p : ℤ) - (i : ℤ) * q))).card := by
        have hcast : ((ℓ ^ e : ℕ) : ℤ) = ((ℓ : ℤ) ^ e) := by push_cast; ring
        simpa [hcast] using hcount
    _ = ∑ i ∈ Finset.range r,
          (if (↑(ℓ ^ e) : ℤ) ∣ ((p : ℤ) - (i : ℤ) * q) then 1 else 0) := by
        rw [Finset.card_filter]

/-- B2.2 payload: `r! ∣ q^{v_q(r!)} · ∏_{i<r}(p−i·q)`.  For every
prime `ℓ`: if `ℓ=q` the explicit `q`-power supplies enough; if
`ℓ≠q`, `cassels_B22` gives `v_ℓ(r!) ≤ v_ℓ(∏)`.  This is the exact
integrality fact the binomial-coefficient clearing consumes. -/
theorem cassels_factorial_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (r : ℕ) :
    Nat.factorial r ∣
      q ^ (padicValNat q (Nat.factorial r))
        * (∏ i ∈ Finset.range r, ((p : ℤ) - (i : ℤ) * q)).natAbs := by
  classical
  set P := (∏ i ∈ Finset.range r, ((p : ℤ) - (i : ℤ) * q)).natAbs with hP
  have hrne : Nat.factorial r ≠ 0 := Nat.factorial_ne_zero r
  have hPne : P ≠ 0 := by
    rw [hP, Int.natAbs_ne_zero, Finset.prod_ne_zero_iff]
    intro i _ h
    have hpiqZ : (p : ℤ) = (i : ℤ) * q := by linarith
    have hpiq : p = i * q := by exact_mod_cast hpiqZ
    have hqp : q ∣ p := ⟨i, by rw [hpiq]; ring⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp q hqp) with h1 | h2
    · exact hq.ne_one h1
    · exact hpq h2.symm
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro ℓ k hℓ hk
  have hℓp : ℓ.Prime := hℓ
  have hkle : k ≤ (Nat.factorial r).factorization ℓ :=
    (Nat.Prime.pow_dvd_iff_le_factorization hℓ hrne).mp hk
  have hfr : (Nat.factorial r).factorization ℓ
      = padicValNat ℓ (Nat.factorial r) :=
    Nat.factorization_def _ hℓp
  by_cases hℓq : ℓ = q
  · subst hℓq
    have hkv : k ≤ padicValNat ℓ (Nat.factorial r) := by omega
    exact dvd_trans (pow_dvd_pow ℓ hkv) (dvd_mul_right _ _)
  · haveI : Fact ℓ.Prime := ⟨hℓp⟩
    have hℓnq : ¬ ℓ ∣ q := by
      intro hd
      rcases (Nat.Prime.eq_one_or_self_of_dvd hq ℓ hd) with h1 | h2
      · exact hℓp.ne_one h1
      · exact hℓq h2
    have hB := cassels_B22 hℓnq hp hq hpq r
    have hPval : padicValInt ℓ
        (∏ i ∈ Finset.range r, ((p : ℤ) - (i : ℤ) * q))
        = padicValNat ℓ P := rfl
    rw [hPval] at hB
    have hPfac : P.factorization ℓ = padicValNat ℓ P :=
      Nat.factorization_def _ hℓp
    have hkP : k ≤ P.factorization ℓ := by omega
    exact dvd_mul_of_dvd_right
      ((Nat.Prime.pow_dvd_iff_le_factorization hℓ hPne).mpr hkP) _

/-- ℤ form of the B2.2 payload: `(r! : ℤ) ∣ q^{v_q(r!)} · ∏(p−iq)`
(signed product).  Direct cast of `cassels_factorial_dvd` through
`natAbs`. -/
theorem cassels_qpow_prod_factorial_dvd {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (r : ℕ) :
    (Nat.factorial r : ℤ) ∣
      (q : ℤ) ^ (padicValNat q (Nat.factorial r))
        * ∏ i ∈ Finset.range r, ((p : ℤ) - (i : ℤ) * q) := by
  have hN := cassels_factorial_dvd hp hq hpq r
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, Int.natAbs_mul,
    Int.natAbs_pow, Int.natAbs_natCast]
  exact hN

/-! ### Generalized binomial coefficient and truncation (PIECE 2)

Definitions and the integrality-clearing lemma, following ChatGPT's
design.  The `gbinomQ` is the rational generalized binomial
coefficient; `casselsTruncQ` is the truncation; the clearing lemma
consumes `cassels_qpow_prod_factorial_dvd`. -/

/-- Generalized binomial coefficient over ℚ. -/
noncomputable def gbinomQ (α : ℚ) (r : ℕ) : ℚ :=
  (∏ i ∈ Finset.range r, (α - (i : ℚ))) / (Nat.factorial r : ℚ)

/-- Cassels truncation parameters. -/
def casselsR (p q : ℕ) : ℕ := p / q + 1
def casselsSigma (p q : ℕ) : ℕ := casselsR p q * q - p
def casselsNu (p q : ℕ) : ℕ :=
  padicValNat q (Nat.factorial (casselsR p q))

/-- The coefficient identity: `C(p/q, r) = ∏(p−iq) / (q^r · r!)`. -/
theorem gbinomQ_nat_div {p q r : ℕ} (hq0 : (q : ℚ) ≠ 0) :
    gbinomQ ((p : ℚ) / (q : ℚ)) r =
      (∏ i ∈ Finset.range r, (((p : ℤ) - (i : ℤ) * q : ℤ) : ℚ))
        / ((q : ℚ) ^ r * (Nat.factorial r : ℚ)) := by
  unfold gbinomQ
  have hfactor : ∀ i ∈ Finset.range r,
      ((p : ℚ) / (q : ℚ) - (i : ℚ))
        = (((p : ℤ) - (i : ℤ) * q : ℤ) : ℚ) / (q : ℚ) := by
    intro i _
    field_simp
    push_cast
    ring
  rw [Finset.prod_congr rfl hfactor, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_range, div_div]

end Ripple.LPP.CasselsClassical
