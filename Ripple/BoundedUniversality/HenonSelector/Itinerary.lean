/-
Ripple.BoundedUniversality.HenonSelector.Itinerary
------------------------------
Bi-infinite binary sequences, the shift map, and the abstract
Arai-Ishii coding interface (HenonCoding structure).
-/

import Ripple.BoundedUniversality.HenonSelector.Henon
import Ripple.BoundedUniversality.HenonSelector.Markov

namespace Ripple.BoundedUniversality.HenonSelector

abbrev BinSeq := ℤ → Bool

def shift (s : BinSeq) : BinSeq :=
  fun n => s (n + 1)

def IsKPeriodicSeq (s : BinSeq) (k : ℕ) : Prop :=
  ∀ n : ℤ, s (n + (k : ℤ)) = s n

def IsPeriodicSeq (s : BinSeq) : Prop :=
  ∃ k : ℕ, 0 < k ∧ Nat.iterate shift k s = s

theorem shift_iter_apply (s : BinSeq) (k : ℕ) (n : ℤ) :
    (Nat.iterate shift k s) n = s (n + (k : ℤ)) := by
  induction k generalizing s n with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [ih (shift s) n]
    simp only [shift]
    push_cast; ring_nf

theorem isPeriodicSeq_iff_pointwise (s : BinSeq) (k : ℕ) :
    Nat.iterate shift k s = s ↔ IsKPeriodicSeq s k := by
  constructor
  · intro h n
    have := congr_fun h n
    simp [shift_iter_apply] at this
    exact this
  · intro h
    funext n
    simp [shift_iter_apply]
    exact h n

/-
HenonCoding: abstract specification of the Arai-Ishii coding map
ω : {0,1}^ℤ → Ω(f_{9,1}). Its existence is Theorem 2.12(ii) of
Arai-Ishii 2015. We axiomatize it as a structure rather than proving
it from hyperbolic dynamics (which requires infrastructure not in Mathlib).
-/

structure HenonCoding where
  omega : BinSeq → Point2
  omega_injective : Function.Injective omega
  conjugacy : ∀ s : BinSeq, henon91 (omega s) = omega (shift s)
  omega_in_dpre : ∀ s : BinSeq, Dpre (omega s)
  symbol_zero : ∀ s : BinSeq, s 0 = false ↔ (omega s).1 < 0
  symbol_one  : ∀ s : BinSeq, s 0 = true  ↔ 0 < (omega s).1
  periodic_point_isAlg :
    ∀ (s : BinSeq) (k : ℕ), 0 < k →
      IsKPeriodicSeq s k →
      IsAlgPoint (omega s)

theorem conjugacy_iter (hc : HenonCoding) (k : ℕ) (s : BinSeq) :
    Nat.iterate henon91 k (hc.omega s) = hc.omega (Nat.iterate shift k s) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [hc.conjugacy]
    exact ih (shift s)

theorem periodic_itinerary_fixed
    (hc : HenonCoding) {s : BinSeq} {k : ℕ}
    (hk : Nat.iterate shift k s = s) :
    Nat.iterate henon91 k (hc.omega s) = hc.omega s := by
  rw [conjugacy_iter hc k s, hk]

theorem henon_periodic_omega_to_shift_periodic
    (hc : HenonCoding) {s : BinSeq}
    (hper : IsHenonPeriodic (hc.omega s)) :
    IsPeriodicSeq s := by
  rcases hper with ⟨k, hkpos, hk⟩
  refine ⟨k, hkpos, ?_⟩
  apply hc.omega_injective
  rw [← conjugacy_iter hc k s]
  exact hk

end Ripple.BoundedUniversality.HenonSelector
