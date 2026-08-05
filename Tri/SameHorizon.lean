/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.EscapeSplit
import Tri.Ladder

/-!
# Same-horizon event unions

`Reaches.comp` is sequential: it adds horizons.  Several paper arguments
instead intersect good events measured under one terminal law at one common
horizon.  This file supplies the corresponding finite union bounds.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- Failure of an intersection is at most the sum of the two failure masses. -/
theorem terminalFailureMass_inter_le
    (p : PMF α)
    (Q R : α → Prop)
    [DecidablePred Q] [DecidablePred R] :
    terminalFailureMass p (fun z => Q z ∧ R z) ≤
      terminalFailureMass p Q + terminalFailureMass p R := by
  unfold terminalFailureMass
  calc
    ∑' z, (if Q z ∧ R z then 0 else p z)
        ≤ ∑' z,
            ((if Q z then 0 else p z) +
             (if R z then 0 else p z)) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          by_cases hQ : Q z <;> by_cases hR : R z
          · simp [hQ, hR]
          · simp [hQ, hR]
          · simp [hQ, hR]
          · simp only [hQ, hR, false_and, if_false]
            calc
              p z = p z + 0 := (add_zero _).symm
              _ ≤ p z + p z := add_le_add le_rfl bot_le
    _ = (∑' z, if Q z then 0 else p z) +
        (∑' z, if R z then 0 else p z) :=
      ENNReal.tsum_add

/-- Intersect two postconditions under the same kernel and horizon. -/
theorem Reaches.and_same_horizon
    {K : α → PMF α}
    {P Q R : α → Prop}
    [DecidablePred Q] [DecidablePred R]
    {T : ℕ} {εQ εR : ℝ≥0∞}
    (hQ : Reaches K T P Q εQ)
    (hR : Reaches K T P R εR) :
    Reaches K T P (fun z => Q z ∧ R z) (εQ + εR) := by
  intro s hs
  exact
    (terminalFailureMass_inter_le
      (iter K T s) Q R).trans
      (add_le_add (hQ s hs) (hR s hs))

/-- Three-way same-horizon union bound. -/
theorem Reaches.and3_same_horizon
    {K : α → PMF α}
    {P Q₁ Q₂ Q₃ : α → Prop}
    [DecidablePred Q₁] [DecidablePred Q₂] [DecidablePred Q₃]
    {T : ℕ} {ε₁ ε₂ ε₃ : ℝ≥0∞}
    (h₁ : Reaches K T P Q₁ ε₁)
    (h₂ : Reaches K T P Q₂ ε₂)
    (h₃ : Reaches K T P Q₃ ε₃) :
    Reaches K T P
      (fun z => Q₁ z ∧ (Q₂ z ∧ Q₃ z))
      (ε₁ + ε₂ + ε₃) := by
  simpa [add_assoc] using
    h₁.and_same_horizon (h₂.and_same_horizon h₃)

/-- If every bad terminal state lies in one of three charged events, their
same-horizon estimates imply the desired postcondition. -/
theorem Reaches.of_same_horizon_bad_cover3
    {K : α → PMF α}
    {P Good B₁ B₂ B₃ : α → Prop}
    [DecidablePred Good]
    [DecidablePred B₁] [DecidablePred B₂] [DecidablePred B₃]
    {T : ℕ} {ε₁ ε₂ ε₃ : ℝ≥0∞}
    (h₁ : Reaches K T P (fun z => ¬ B₁ z) ε₁)
    (h₂ : Reaches K T P (fun z => ¬ B₂ z) ε₂)
    (h₃ : Reaches K T P (fun z => ¬ B₃ z) ε₃)
    (hcover : ∀ z, ¬ Good z → B₁ z ∨ B₂ z ∨ B₃ z) :
    Reaches K T P Good (ε₁ + ε₂ + ε₃) := by
  have hall :=
    Reaches.and3_same_horizon h₁ h₂ h₃
  exact hall.mono_post (by
    intro z hz
    by_contra hbad
    rcases hcover z hbad with hB₁ | hB₂ | hB₃
    · exact hz.1 hB₁
    · exact hz.2.1 hB₂
    · exact hz.2.2 hB₃)

/-- Terminal membership in a bad set for the ordinary chain is dominated by
the probability of having hit that set by the same horizon. -/
theorem terminalEventMass_iter_le_hitProb
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (T : ℕ) (s : α) :
    terminalFailureMass (iter K T s) (fun z => ¬ B z) ≤
      hitProb B K T s := by
  induction T generalizing s with
  | zero =>
      unfold terminalFailureMass hitProb expect ind
      simp [iter, PMF.pure_apply]
  | succ T ih =>
      by_cases hs : B s
      · rw [hitProb_eq_one_of_mem B K (T + 1) s hs]
        exact terminalFailureMass_le_one _ _
      · rw [iter_succ, terminalFailureMass_bind,
          hitProb_succ_of_not B K T s hs]
        unfold expect
        exact ENNReal.tsum_le_tsum fun x =>
          mul_le_mul_right (ih x) _

/-- Convert a first-hit estimate to the same-horizon terminal complement form
consumed by the event-union lemmas. -/
theorem Reaches.of_hitProb
    {K : α → PMF α}
    {P B : α → Prop} [DecidablePred B]
    {T : ℕ} {ε : ℝ≥0∞}
    (h : ∀ s, P s → hitProb B K T s ≤ ε) :
    Reaches K T P (fun z => ¬ B z) ε := by
  intro s hs
  exact (terminalEventMass_iter_le_hitProb B K T s).trans
    (h s hs)

end Tri

#print axioms Tri.terminalFailureMass_inter_le
#print axioms Tri.Reaches.and_same_horizon
#print axioms Tri.Reaches.and3_same_horizon
#print axioms Tri.Reaches.of_same_horizon_bad_cover3
#print axioms Tri.terminalEventMass_iter_le_hitProb
#print axioms Tri.Reaches.of_hitProb
