/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Classes

/-!
# Window `𝒦_1 + I → 𝒦_2` (FIX3-SCWB-T32 Lemma 4.2, Lemma 5.2)

From `𝒦_1(q, w) + I` the non-clock reactions keep the state in `Win12 q x` (`win12_fire`):
`I + S_{q,1} → S_{q,2}` fires once, then `S_{q,1} + S_{q,2} → 2 S_{q,2}`; the memory changes only
by the `S_{q,2}`-catalysed restores and `T + M → T* + M*`, which preserve `𝒜(x)`.  The target
`𝒦_2(q, w)` is closed (`k2_fire`).

Potential (expected remaining time, units `v/k`):
`V12 w = [I = 1]/m + aut m (max #S_{q,2} 1) + hrm (#M† + #T† + #D* + #B*)/m`;
`win12_drift`: off the target the non-clock drift of `V12` is at most `-1`.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

/-- States of the window `𝒦_1(q, w) + I → 𝒦_2(q, w)`, together with `𝒦_1(q, w)` itself
(`I = 0`, `S_{q,2} = 0`). -/
def Win12 (m T0 : ℕ) (q : Q) (x : ℕ) (w : State (Sp Q L)) : Prop :=
  OnlyState [.s1 q, .s2 q, .i] w ∧ w (.s1 q) + w (.s2 q) = m ∧
    ((w .i = 1 ∧ w (.s2 q) = 0) ∨ w .i = 0) ∧ MemA m T0 x (memv w)

/-- Number of memory molecules still to be restored. -/
def restY (w : State (Sp Q L)) : ℕ := w (.mem .md) + w (.mem .td) + w (.mem .ds) + w (.mem .bs)

/-- Potential of the window `𝒦_1 + I → 𝒦_2`. -/
noncomputable def V12 (m : ℕ) (q : Q) (w : State (Sp Q L)) : ℝ :=
  (if w .i = 1 then 1 / (m : ℝ) else 0) + aut m (max (w (.s2 q)) 1) + hrm (restY w) / m

theorem memv_fire_of_state {C : CTM Q} {i : Rx Q L} {w : State (Sp Q L)}
    (h1 : ∀ y, src1 i ≠ .mem y) (h2 : ∀ y, src2 C i ≠ .mem y) (h3 : ∀ y, out C i (.mem y) = 0) :
    memv ((rxn C i).fire w) = memv w := by
  funext y
  simp only [memv, fire_apply, h3, add_zero]
  rw [if_neg (Ne.symm (h1 y)), if_neg (Ne.symm (h2 y))]
  simp

/-- **Lemma 4.2 (closure).** Non-clock reactions keep the window and do not increase `V12`. -/
theorem win12_fire {m T0 x : ℕ} {q : Q} {w : State (Sp Q L)} (h : Win12 m T0 q x w)
    (i : Rx Q L) (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    Win12 m T0 q x ((rxn C i).fire w) ∧ V12 m q ((rxn C i).fire w) ≤ V12 m q w ∧
      ((w .i = 1 ∨ 1 ≤ w (.s2 q)) ↔
        (((rxn C i).fire w) .i = 1 ∨ 1 ≤ ((rxn C i).fire w) (.s2 q))) := by
  obtain ⟨hO, hs, hst, hM⟩ := h
  rw [rate_ne_zero_iff] at hr
  cases i with
  | tick => exact absurd trivial hi
  | up c => exact absurd trivial hi
  | down c => exact absurd trivial hi
  | eps q' b => exact absurd (hO (.u q' b) trivial (by simp)) hr.2
  | auto41 q' b => exact absurd (hO (.u q' b) trivial (by simp)) hr.1
  | adv12 q' =>
    by_cases hq : q' = q
    · subst hq
      simp only [src1, src2] at hr
      have hI : w .i = 1 ∧ w (.s2 q') = 0 := by omega
      have hmem : memv ((rxn C (.adv12 q')).fire w) = memv w :=
        memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
      refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, hmem ▸ hM⟩, ?_, ?_⟩
      · cases s <;> simp_all [out, Sp.IsState]
      · simp [src1, src2, out]; omega
      · simp [src1, src2, out]; omega
      · have hY : restY ((rxn C (.adv12 q')).fire w) = restY w := by
          simp [restY, src1, src2, out]
        simp only [V12, hY, Reaction.fire_apply, rxn_l, rxn_r, src1, src2, out, one_apply, Pi.add_apply]
        simp [hI.1, hI.2]
      · simp [src1, src2, out]; omega
    · exact absurd (hO (.s1 q') trivial (by simp [hq])) (by simpa [src2] using hr.2)
  | auto12 q' =>
    by_cases hq : q' = q
    · subst hq
      simp only [src1, src2] at hr
      have hI : w .i = 0 ∧ 1 ≤ w (.s2 q') := by omega
      have hmem : memv ((rxn C (.auto12 q')).fire w) = memv w :=
        memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
      refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, hmem ▸ hM⟩, ?_, ?_⟩
      · cases s <;> simp_all [out, Sp.IsState]
      · simp [src1, src2, out]; omega
      · simp [src1, src2, out]; omega
      · have hY : restY ((rxn C (.auto12 q')).fire w) = restY w := by
          simp [restY, src1, src2, out]
        simp only [V12, hY, Reaction.fire_apply, rxn_l, rxn_r, src1, src2, out, one_apply, Pi.add_apply]
        simp only [if_true, reduceCtorEq, if_false, Sp.s1.injEq, Sp.s2.injEq, add_zero,
          tsub_zero, hI.1]
        have : max (w (.s2 q')) 1 ≤ max (w (.s2 q') - 1 + 2) 1 := by omega
        have := aut_anti (m := m) this
        simp only [zero_ne_one, if_false] at *
        linarith
      · simp [src1, src2, out]; omega
    · exact absurd (hO (.s1 q') trivial (by simp [hq])) (by simpa [src1] using hr.1)
  | adv23 q' =>
    have h2 : w (.s2 q') ≠ 0 := by simpa [src2] using hr.2
    have hq : q' = q := by
      by_contra hq; exact h2 (hO (.s2 q') trivial (by simp [hq]))
    subst hq
    simp only [src1] at hr
    omega
  | auto23 q' =>
    exact absurd (hO (.s3 q') trivial (by simp)) (by simpa [src2] using hr.2)
  | adv3 q' =>
    exact absurd (hO (.s3 q') trivial (by simp)) (by simpa [src2] using hr.2)
  | rt q' => exact absurd (hO (.rq q') trivial (by simp)) (by simpa [src1] using hr.1)
  | rm q' => exact absurd (hO (.rq q') trivial (by simp)) (by simpa [src1] using hr.1)
  | auto34 q' b =>
    exact absurd (hO (.s3 q') trivial (by simp)) (by simpa [src1] using hr.1)
  | rsM q' =>
    have h1 : w (.s2 q') ≠ 0 := by simpa [src1] using hr.1
    have hq : q' = q := by
      by_contra hq; exact h1 (hO (.s2 q') trivial (by simp [hq]))
    subst hq
    have h2 : w (.mem .md) ≠ 0 := by simpa [src2] using hr.2
    refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, ?_⟩, ?_, by simp [src1, src2, out]; omega⟩
    · cases s <;> simp_all [out, Sp.IsState]
    · simp [src1, src2, out]; omega
    · simp [src1, src2, out]; omega
    · simp only [MemA, memv_apply] at hM ⊢; simp [src1, src2, out]; omega
    · have hY : restY ((rxn C (.rsM q')).fire w) + 1 = restY w := by
        simp [restY, src1, src2, out]; omega
      have hI : ((rxn C (.rsM q')).fire w) .i = w .i := by simp [src1, src2, out]
      have hS : ((rxn C (.rsM q')).fire w) (.s2 q') = w (.s2 q') := by
        simp [src1, src2, out]; omega
      simp only [V12, hI, hS]
      have := hrm_mono (show restY ((rxn C (.rsM q')).fire w) ≤ restY w by omega)
      gcongr
  | rsT q' =>
    have h1 : w (.s2 q') ≠ 0 := by simpa [src1] using hr.1
    have hq : q' = q := by
      by_contra hq; exact h1 (hO (.s2 q') trivial (by simp [hq]))
    subst hq
    have h2 : w (.mem .td) ≠ 0 := by simpa [src2] using hr.2
    refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, ?_⟩, ?_, by simp [src1, src2, out]; omega⟩
    · cases s <;> simp_all [out, Sp.IsState]
    · simp [src1, src2, out]; omega
    · simp [src1, src2, out]; omega
    · simp only [MemA, memv_apply] at hM ⊢; simp [src1, src2, out]; omega
    · have hY : restY ((rxn C (.rsT q')).fire w) + 1 = restY w := by
        simp [restY, src1, src2, out]; omega
      have hI : ((rxn C (.rsT q')).fire w) .i = w .i := by simp [src1, src2, out]
      have hS : ((rxn C (.rsT q')).fire w) (.s2 q') = w (.s2 q') := by
        simp [src1, src2, out]; omega
      simp only [V12, hI, hS]
      have := hrm_mono (show restY ((rxn C (.rsT q')).fire w) ≤ restY w by omega)
      gcongr
  | rsD q' =>
    have h1 : w (.s2 q') ≠ 0 := by simpa [src1] using hr.1
    have hq : q' = q := by
      by_contra hq; exact h1 (hO (.s2 q') trivial (by simp [hq]))
    subst hq
    have h2 : w (.mem .ds) ≠ 0 := by simpa [src2] using hr.2
    refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, ?_⟩, ?_, by simp [src1, src2, out]; omega⟩
    · cases s <;> simp_all [out, Sp.IsState]
    · simp [src1, src2, out]; omega
    · simp [src1, src2, out]; omega
    · simp only [MemA, memv_apply] at hM ⊢; simp [src1, src2, out]; omega
    · have hY : restY ((rxn C (.rsD q')).fire w) + 1 = restY w := by
        simp [restY, src1, src2, out]; omega
      have hI : ((rxn C (.rsD q')).fire w) .i = w .i := by simp [src1, src2, out]
      have hS : ((rxn C (.rsD q')).fire w) (.s2 q') = w (.s2 q') := by
        simp [src1, src2, out]; omega
      simp only [V12, hI, hS]
      have := hrm_mono (show restY ((rxn C (.rsD q')).fire w) ≤ restY w by omega)
      gcongr
  | rsB q' =>
    have h1 : w (.s2 q') ≠ 0 := by simpa [src1] using hr.1
    have hq : q' = q := by
      by_contra hq; exact h1 (hO (.s2 q') trivial (by simp [hq]))
    subst hq
    have h2 : w (.mem .bs) ≠ 0 := by simpa [src2] using hr.2
    refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, ?_⟩, ?_, by simp [src1, src2, out]; omega⟩
    · cases s <;> simp_all [out, Sp.IsState]
    · simp [src1, src2, out]; omega
    · simp [src1, src2, out]; omega
    · simp only [MemA, memv_apply] at hM ⊢; simp [src1, src2, out]; omega
    · have hY : restY ((rxn C (.rsB q')).fire w) + 1 = restY w := by
        simp [restY, src1, src2, out]; omega
      have hI : ((rxn C (.rsB q')).fire w) .i = w .i := by simp [src1, src2, out]
      have hS : ((rxn C (.rsB q')).fire w) (.s2 q') = w (.s2 q') := by
        simp [src1, src2, out]; omega
      simp only [V12, hI, hS]
      have := hrm_mono (show restY ((rxn C (.rsB q')).fire w) ≤ restY w by omega)
      gcongr
  | pair =>
    simp only [src1, src2] at hr
    refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, ?_⟩, ?_, by simp [src1, src2, out]⟩
    · cases s <;> simp_all [out, Sp.IsState]
    · simp [src1, src2, out]; omega
    · simp [src1, src2, out]; omega
    · simp only [MemA, memv_apply] at hM ⊢; simp [src1, src2, out]; omega
    · have hY : restY ((rxn C .pair).fire w) = restY w := by
        simp [restY, src1, src2, out]
      have hI : ((rxn C .pair).fire w) .i = w .i := by simp [src1, src2, out]
      have h2 : ((rxn C .pair).fire w) (.s2 q) = w (.s2 q) := by
        simp [src1, src2, out]
      simp only [V12, hI, h2, hY, le_refl]
  | k2 =>
    have : w (.mem .k2) = 0 := hM.2.2.2.2.2.2
    exact absurd this (by simpa [src1] using hr.1)
  | k1 =>
    have : w (.mem .k1) = 0 := hM.2.2.2.2.2.1
    exact absurd this (by simpa [src1] using hr.1)
  | cMs q' b | cTs q' b | cT q' b | cM q' b | cD q' b | cB q' b =>
    exact absurd (hO (.u q' b) trivial (by simp)) (by simpa [src1] using hr.1)

/-! ### Target, drift and start -/

theorem V12_nonneg (m : ℕ) (q : Q) (w : State (Sp Q L)) : 0 ≤ V12 m q w := by
  unfold V12
  have := aut_nonneg m (max (w (.s2 q)) 1)
  have := hrm_nonneg (restY w)
  have : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
  positivity

/-- `𝒦_1(q, w)` is the part of the window with `I = 0` and `S_{q,2} = 0`. -/
theorem k1_iff_win12 {m T0 x : ℕ} {q : Q} {w : State (Sp Q L)} :
    K1 m T0 q x w ↔ Win12 m T0 q x w ∧ w .i = 0 ∧ w (.s2 q) = 0 := by
  constructor
  · rintro ⟨hO, hs, hM⟩
    have h2 : w (.s2 q) = 0 := hO (.s2 q) trivial (by simp)
    have hi : w .i = 0 := hO .i trivial (by simp)
    refine ⟨⟨fun s hs' hn => hO s hs' (by simp_all), by omega, Or.inr hi, hM⟩, hi, h2⟩
  · rintro ⟨⟨hO, hs, _, hM⟩, hi, h2⟩
    refine ⟨fun s hs' hn => ?_, by omega, hM⟩
    by_cases h1 : s = .s2 q
    · rw [h1, h2]
    · by_cases h3 : s = .i
      · rw [h3, hi]
      · exact hO s hs' (by simp_all)

/-- The target `𝒦_2(q, w)` is the zero set of `V12` in the window. -/
theorem k2_iff_V12 {m T0 x : ℕ} (hm : 2 ≤ m) {q : Q} {w : State (Sp Q L)}
    (h : Win12 m T0 q x w) : K2 m T0 q x w ↔ V12 m q w = 0 := by
  obtain ⟨hO, hs, hst, hM⟩ := h
  constructor
  · rintro ⟨hO2, h2, _, hR⟩
    have hi : w .i = 0 := hO2 .i trivial (by simp)
    simp only [MemReset, memv_apply] at hR
    have hY : restY w = 0 := by simp only [restY]; omega
    simp [V12, hi, h2, hY, aut_eq_zero_of (le_max_left m 1), hrm]
  · intro hV
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have a1 := aut_nonneg m (max (w (.s2 q)) 1)
    have a2 : 0 ≤ hrm (restY w) / m := div_nonneg (hrm_nonneg _) hm'.le
    have a3 : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
    unfold V12 at hV
    have e3 : (if w .i = 1 then 1 / (m : ℝ) else 0) = 0 := by linarith
    have e1 : aut m (max (w (.s2 q)) 1) = 0 := by linarith
    have e2 : hrm (restY w) / m = 0 := by linarith
    have hi : w .i = 0 := by
      rcases hst with h | h
      · rw [if_pos h.1] at e3; exact absurd e3 (by positivity)
      · exact h
    have h2 : m ≤ w (.s2 q) := by
      by_contra hlt
      exact absurd e1 (aut_pos (le_max_right _ _) (by omega)).ne'
    have hY : restY w = 0 := (hrm_eq_zero_iff _).mp
      ((div_eq_zero_iff.mp e2).resolve_right hm'.ne')
    simp only [restY] at hY
    refine ⟨fun s hs' hn => ?_, by omega, hM, by simp only [MemReset, memv_apply]; omega⟩
    by_cases e : s = .s1 q
    · rw [e]; omega
    · by_cases e' : s = .i
      · rw [e', hi]
      · exact hO s hs' (by simp_all)

/-- **Lemma 5.2 (drift).** Off the target, with the window active, the non-clock drift of
`V12` is at most `-1`. -/
theorem win12_drift {m T0 x : ℕ} (hm : 2 ≤ m) {q : Q} {w : State (Sp Q L)}
    (h : Win12 m T0 q x w) (hK : ¬ K2 m T0 q x w) (hact : w .i = 1 ∨ 1 ≤ w (.s2 q)) :
    drift C (V12 m q) w ≤ -1 := by
  have hmono : ∀ i : Rx Q L, ¬ i.IsClock → rate C i w ≠ 0 →
      V12 m q ((rxn C i).fire w) ≤ V12 m q w := fun i hi hr => (win12_fire C h i hi hr).2.1
  obtain ⟨hO, hs, hst, hM⟩ := h
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rcases hst with ⟨hi, h2⟩ | hi
  · -- stage `I = 1`: the reaction `I + S_{q,1} → S_{q,2}` has rate `m`
    refine (drift_le_sum C _ w hmono {.adv12 q}).trans (le_of_eq ?_)
    rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
    have hY : restY ((rxn C (.adv12 q)).fire w) = restY w := by simp [restY, src1, src2, out]
    have e : V12 m q ((rxn C (.adv12 q)).fire w) = V12 m q w - 1 / m := by
      simp only [V12, hY]
      simp [src1, src2, out, hi, h2]
      ring
    rw [e, rate_eq]
    simp only [src1, src2, hi]
    have : w (.s1 q) = m := by omega
    rw [this]
    field_simp
    ring
  · rcases Nat.lt_or_ge (w (.s2 q)) m with hlt | hge
    · -- autocatalysis `S_{q,1} + S_{q,2} → 2 S_{q,2}` at rate `j (m - j)`
      have hj : 1 ≤ w (.s2 q) := by rcases hact with h' | h' <;> omega
      refine (drift_le_sum C _ w hmono {.auto12 q}).trans (le_of_eq ?_)
      rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
      have hY : restY ((rxn C (.auto12 q)).fire w) = restY w := by
        simp [restY, src1, src2, out]
      have e : V12 m q ((rxn C (.auto12 q)).fire w) - V12 m q w =
          aut m (w (.s2 q) + 1) - aut m (w (.s2 q)) := by
        simp only [V12, hY]
        simp [src1, src2, out, hi]
        try rw [max_eq_left (by omega : 1 ≤ w (.s2 q) - 1 + 2)]
        rw [max_eq_left hj, show w (.s2 q) - 1 + 2 = w (.s2 q) + 1 by omega]
      rw [e, rate_eq]
      simp only [src1, src2]
      have := aut_drift (m := m) hj hlt
      rw [show w (.s1 q) = m - w (.s2 q) by omega]
      push_cast at this ⊢
      linear_combination this
    · -- restores, catalysed by `m` molecules of `S_{q,2}`
      have h2 : w (.s2 q) = m := by omega
      have hY1 : 1 ≤ restY w := by
        by_contra hY0
        apply hK
        rw [k2_iff_V12 hm ⟨hO, hs, Or.inr hi, hM⟩]
        have : restY w = 0 := by omega
        simp [V12, hi, h2, this, aut_eq_zero_of (le_max_left m 1), hrm]
      have hYr : (0 : ℝ) < restY w := by exact_mod_cast hY1
      refine (drift_le_sum C _ w hmono {.rsM q, .rsT q, .rsD q, .rsB q}).trans (le_of_eq ?_)
      have key : ∀ (lab : Rx Q L) (y : Mem), lab ∈ [Rx.rsM q, .rsT q, .rsD q, .rsB q] →
          src1 lab = .s2 q → src2 C lab = .mem y →
          (1 ≤ w (.mem y) → restY ((rxn C lab).fire w) + 1 = restY w ∧
            ((rxn C lab).fire w) .i = w .i ∧ ((rxn C lab).fire w) (.s2 q) = w (.s2 q)) →
          (if lab.IsClock then 0 else (rate C lab w : ℝ) *
            (V12 m q ((rxn C lab).fire w) - V12 m q w)) = -(w (.mem y) : ℝ) / restY w := by
        intro lab y hlab h1 h2' hfx
        rw [if_neg (by simp at hlab; rcases hlab with rfl | rfl | rfl | rfl <;> simp [Rx.IsClock]),
          rate_eq, h1, h2']
        rcases Nat.eq_zero_or_pos (w (.mem y)) with h0 | hpos
        · simp [h0]
        · obtain ⟨hY, hI, hS⟩ := hfx hpos
          have e : V12 m q ((rxn C lab).fire w) - V12 m q w =
              -(1 / ((restY w : ℝ) * m)) := by
            simp only [V12, hI, hS]
            rw [← hY, hrm_succ]
            push_cast
            field_simp
            ring
          rw [e, h2]
          push_cast
          field_simp
      rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        Finset.sum_singleton]
      rw [key (.rsM q) .md (by simp) rfl rfl (fun h' => ⟨by simp [restY, src1, src2, out]; omega,
          by simp [src1, src2, out], by simp [src1, src2, out]; omega⟩),
        key (.rsT q) .td (by simp) rfl rfl (fun h' => ⟨by simp [restY, src1, src2, out]; omega,
          by simp [src1, src2, out], by simp [src1, src2, out]; omega⟩),
        key (.rsD q) .ds (by simp) rfl rfl (fun h' => ⟨by simp [restY, src1, src2, out]; omega,
          by simp [src1, src2, out], by simp [src1, src2, out]; omega⟩),
        key (.rsB q) .bs (by simp) rfl rfl (fun h' => ⟨by simp [restY, src1, src2, out]; omega,
          by simp [src1, src2, out], by simp [src1, src2, out]; omega⟩)]
      have : ((w (.mem .md) : ℝ) + w (.mem .td) + w (.mem .ds) + w (.mem .bs)) = restY w := by
        simp [restY]
      field_simp
      linarith

/-- **Start of the window** (tick from `𝒦_1`), with the bound of Lemma 5.2. -/
theorem win12_start {m T0 x : ℕ} {q : Q} {w : State (Sp Q L)} (h : K1 m T0 q x w) :
    Win12 m T0 q x (w + one .i) ∧
      V12 m q (w + one .i) ≤ 1 / m + aut m 1 + hrm (x + T0 + m + 1) / m := by
  obtain ⟨hO, hs, hM⟩ := h
  have h2 : w (.s2 q) = 0 := hO (.s2 q) trivial (by simp)
  have hi : w .i = 0 := hO .i trivial (by simp)
  have hmem : memv (w + one .i) = memv w := by funext y; simp
  refine ⟨⟨fun s hs' hn => ?_, by simp; omega, Or.inl ⟨by simp [hi], by simp [h2]⟩, hmem ▸ hM⟩, ?_⟩
  · have : s ≠ .i := fun e => hn (by simp [e])
    simp [this, hO s hs' (by simp_all)]
  · simp only [V12]
    have hY : restY (w + one .i) ≤ x + T0 + m + 1 := by
      simp only [MemA, memv_apply] at hM
      simp [restY]; omega
    simp only [Pi.add_apply, one_apply, if_true, hi, h2, zero_add, if_neg (show
      (Sp.s2 q : Sp Q L) ≠ .i by simp), add_zero, max_eq_right (zero_le_one' ℕ)]
    have : hrm (restY (w + one .i)) ≤ hrm (x + T0 + m + 1) := hrm_mono hY
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    gcongr

end Ripple.sCRNUniversality.ClockedCTM
