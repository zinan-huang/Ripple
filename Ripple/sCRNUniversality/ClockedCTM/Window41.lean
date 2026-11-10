/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Window23

/-!
# Window `𝒦_4 + I → 𝒦_1` (FIX3-SCWB-T32 Lemma 4.5, Lemma 5.1)

From `𝒦_4(q, b; w') + I`: `I + U_{q,b} → S_{q',1}` (`q' = q_b`) fires once, then
`U_{q,b} + S_{q',1} → 2 S_{q',1}`; no memory reaction is enabled (`win41_fire`).  The target is
`𝒦_1(q', w')`.  Potential `V41 w = [I = 1]/m + aut m (max #S_{q',1} 1)`.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

/-- States of the window `𝒦_4(q, b; w') + I → 𝒦_1(q_b, w')`. -/
def Win41 (m T0 : ℕ) (q : Q) (b : Bool) (x' : ℕ) (w : State (Sp Q L)) : Prop :=
  OnlyState [.u q b, .s1 (C.next q b).1, .i] w ∧ w (.u q b) + w (.s1 (C.next q b).1) = m ∧
    ((w .i = 1 ∧ w (.s1 (C.next q b).1) = 0) ∨ (w .i = 0 ∧ 1 ≤ w (.s1 (C.next q b).1))) ∧
    Mem4 m T0 x' (memv w)

/-- Potential of the window `𝒦_4 + I → 𝒦_1`. -/
noncomputable def V41 (m : ℕ) (q : Q) (b : Bool) (w : State (Sp Q L)) : ℝ :=
  (if w .i = 1 then 1 / (m : ℝ) else 0) + aut m (max (w (.s1 (C.next q b).1)) 1)

theorem memA_of_mem4 {m T0 x' : ℕ} {v : Mem → ℕ} (h : Mem4 m T0 x' v) : MemA m T0 x' v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, h11, h12⟩ <;> omega

/-- **Lemma 4.5 (closure).** -/
theorem win41_fire {m T0 x' : ℕ} {q : Q} {b : Bool} {w : State (Sp Q L)}
    (h : Win41 C m T0 q b x' w) (i : Rx Q L) (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    Win41 C m T0 q b x' ((rxn C i).fire w) ∧ V41 C m q b ((rxn C i).fire w) ≤ V41 C m q b w := by
  obtain ⟨hO, hs, hst, hM⟩ := h
  have hM' := hM
  simp only [Mem4, memv_apply] at hM'
  rw [rate_ne_zero_iff] at hr
  set q' := (C.next q b).1 with hq'
  cases i with
  | tick => exact absurd trivial hi
  | up c => exact absurd trivial hi
  | down c => exact absurd trivial hi
  | eps q'' b' =>
    by_cases hqb : q'' = q ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := hqb
      simp only [src1, src2] at hr
      have hI : w .i = 1 ∧ w (.s1 q') = 0 := by omega
      have hmem : memv ((rxn C (.eps q'' b')).fire w) = memv w :=
        memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
      refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, hmem ▸ hM⟩, ?_⟩
      · cases s <;> simp_all [out, Sp.IsState]
      · simp [src1, src2, out, ← hq'] <;> omega
      · simp [src1, src2, out, ← hq'] <;> omega
      · simp only [V41, ← hq']
        simp [src1, src2, out, hI.1, hI.2, ← hq']
    · refine absurd (hO (.u q'' b') trivial ?_) (by simpa [src2] using hr.2)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun e => hqb ?_, by simp, by simp⟩
      simp only [Sp.u.injEq] at e
      exact e
  | auto41 q'' b' =>
    by_cases hqb : q'' = q ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := hqb
      simp only [src1, src2, ← hq'] at hr
      have hI : w .i = 0 ∧ 1 ≤ w (.s1 q') := by omega
      have hmem : memv ((rxn C (.auto41 q'' b')).fire w) = memv w :=
        memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
      refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, hmem ▸ hM⟩, ?_⟩
      · cases s <;> simp_all [out, Sp.IsState]
      · simp [src1, src2, out, ← hq'] <;> omega
      · simp [src1, src2, out, ← hq'] <;> omega
      · simp only [V41, ← hq']
        simp [src1, src2, out, hI.1, ← hq']
        have h1 := aut_anti (m := m) (show max (w (.s1 q')) 1 ≤ max (w (.s1 q') - 1 + 2) 1 by omega)
        have h2 := aut_anti (m := m) (show max (w (.s1 q')) 1 ≤ w (.s1 q') - 1 + 2 by omega)
        linarith
    · refine absurd (hO (.u q'' b') trivial ?_) (by simpa [src1] using hr.1)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun e => hqb ?_, by simp, by simp⟩
      simp only [Sp.u.injEq] at e
      exact e
  | adv12 q'' =>
    have h1 : w (.s1 q'') ≠ 0 := by simpa [src2] using hr.2
    have hq : q'' = q' := by
      by_contra hq; exact h1 (hO (.s1 q'') trivial (by simp [hq]))
    subst hq
    simp only [src1] at hr
    omega
  | auto12 q'' => exact absurd (hO (.s2 q'') trivial (by simp)) (by simpa [src2] using hr.2)
  | adv23 q'' => exact absurd (hO (.s2 q'') trivial (by simp)) (by simpa [src2] using hr.2)
  | auto23 q'' => exact absurd (hO (.s2 q'') trivial (by simp)) (by simpa [src1] using hr.1)
  | adv3 q'' => exact absurd (hO (.s3 q'') trivial (by simp)) (by simpa [src2] using hr.2)
  | rt q'' => exact absurd (hO (.rq q'') trivial (by simp)) (by simpa [src1] using hr.1)
  | rm q'' => exact absurd (hO (.rq q'') trivial (by simp)) (by simpa [src1] using hr.1)
  | auto34 q'' b' => exact absurd (hO (.s3 q'') trivial (by simp)) (by simpa [src1] using hr.1)
  | rsM q'' | rsT q'' | rsD q'' | rsB q'' =>
    exact absurd (hO (.s2 q'') trivial (by simp)) (by simpa [src1] using hr.1)
  | pair => exact absurd hM'.2.2.2.2.2.2.1 (by simpa [src1] using hr.1)
  | k2 => exact absurd hM'.2.2.2.2.2.2.2.2.2.2.2 (by simpa [src1] using hr.1)
  | k1 => exact absurd hM'.2.2.2.2.2.2.2.2.2.2.1 (by simpa [src1] using hr.1)
  | cMs q'' b' => exact absurd hM'.2.2.2.2.2.1 (by simpa [src2] using hr.2)
  | cTs q'' b' => exact absurd hM'.2.2.2.2.2.2.2.1 (by simpa [src2] using hr.2)
  | cT q'' b' => exact absurd hM'.2.2.2.2.2.2.1 (by simpa [src2] using hr.2)
  | cM q'' b' => exact absurd hM'.2.2.2.2.1 (by simpa [src2] using hr.2)
  | cD q'' b' => exact absurd hM'.2.2.2.2.2.2.2.2.1 (by simpa [src2] using hr.2)
  | cB q'' b' => exact absurd hM'.2.2.2.2.2.2.2.2.2.1 (by simpa [src2] using hr.2)

theorem V41_nonneg (m : ℕ) (q : Q) (b : Bool) (w : State (Sp Q L)) : 0 ≤ V41 C m q b w := by
  unfold V41
  have := aut_nonneg m (max (w (.s1 (C.next q b).1)) 1)
  have : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
  linarith

/-- The target `𝒦_1(q_b, w')` is the zero set of `V41` in the window. -/
theorem k1_iff_V41 {m T0 x' : ℕ} (hm : 2 ≤ m) {q : Q} {b : Bool} {w : State (Sp Q L)}
    (h : Win41 C m T0 q b x' w) : K1 m T0 (C.next q b).1 x' w ↔ V41 C m q b w = 0 := by
  obtain ⟨hO, hs, hst, hM⟩ := h
  constructor
  · rintro ⟨hO1, h1, _⟩
    have hi : w .i = 0 := hO1 .i trivial (by simp)
    simp [V41, hi, h1, aut_eq_zero_of (le_max_left m 1)]
  · intro hV
    have a1 := aut_nonneg m (max (w (.s1 (C.next q b).1)) 1)
    have a3 : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
    unfold V41 at hV
    have e3 : (if w .i = 1 then 1 / (m : ℝ) else 0) = 0 := by linarith
    have e1 : aut m (max (w (.s1 (C.next q b).1)) 1) = 0 := by linarith
    have hi : w .i = 0 := by
      rcases hst with h | h
      · rw [if_pos h.1] at e3
        have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
        exact absurd e3 (by positivity)
      · exact h.1
    have h1 : m ≤ w (.s1 (C.next q b).1) := by
      by_contra hlt
      exact absurd e1 (aut_pos (le_max_right _ _) (by omega)).ne'
    refine ⟨fun s hs' hn => ?_, by omega, memA_of_mem4 hM⟩
    by_cases e : s = .u q b
    · rw [e]; omega
    · by_cases e' : s = .i
      · rw [e', hi]
      · exact hO s hs' (by simp_all)

/-- **Lemma 5.1 (drift).** -/
theorem win41_drift {m T0 x' : ℕ} (hm : 2 ≤ m) {q : Q} {b : Bool} {w : State (Sp Q L)}
    (h : Win41 C m T0 q b x' w) (hK : ¬ K1 m T0 (C.next q b).1 x' w) :
    drift C (V41 C m q b) w ≤ -1 := by
  have hmono : ∀ i : Rx Q L, ¬ i.IsClock → rate C i w ≠ 0 →
      V41 C m q b ((rxn C i).fire w) ≤ V41 C m q b w := fun i hi hr => (win41_fire C h i hi hr).2
  have hW := h
  obtain ⟨hO, hs, hst, hM⟩ := h
  set q' := (C.next q b).1 with hq'
  rcases hst with ⟨hi, h1⟩ | ⟨hi, h1⟩
  · refine (drift_le_sum C _ w hmono {.eps q b}).trans (le_of_eq ?_)
    rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
    have e : V41 C m q b ((rxn C (.eps q b)).fire w) = V41 C m q b w - 1 / m := by
      simp only [V41, ← hq']
      simp [src1, src2, out, hi, h1, ← hq']
      try ring
    rw [e, rate_eq]
    simp only [src1, src2, hi]
    rw [show w (.u q b) = m by omega]
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [show V41 C m q b w - 1 / (m : ℝ) - V41 C m q b w = -(1 / (m : ℝ)) by ring]
    push_cast
    rw [one_mul, mul_neg, mul_one_div_cancel hm'.ne']
  · rcases Nat.lt_or_ge (w (.s1 q')) m with hlt | hge
    · refine (drift_le_sum C _ w hmono {.auto41 q b}).trans (le_of_eq ?_)
      rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
      have e : V41 C m q b ((rxn C (.auto41 q b)).fire w) - V41 C m q b w =
          aut m (w (.s1 q') + 1) - aut m (w (.s1 q')) := by
        simp only [V41, ← hq']
        simp [src1, src2, out, hi, ← hq']
        try rw [max_eq_left (by omega : 1 ≤ w (.s1 q') - 1 + 2)]
        rw [max_eq_left h1, show w (.s1 q') - 1 + 2 = w (.s1 q') + 1 by omega]
      rw [e, rate_eq]
      simp only [src1, src2, ← hq']
      have := aut_drift (m := m) h1 hlt
      rw [show w (.u q b) = m - w (.s1 q') by omega]
      push_cast at this ⊢
      linear_combination this
    · exfalso
      apply hK
      rw [k1_iff_V41 C hm hW]
      simp [V41, hi, ← hq', aut_eq_zero_of (show m ≤ max (w (.s1 q')) 1 by omega)]

/-- **Start of the window** (tick from `𝒦_4`). -/
theorem win41_start {m T0 x' : ℕ} (hm : 1 ≤ m) {q : Q} {b : Bool} {w : State (Sp Q L)}
    (h : K4 m T0 q b x' w) :
    Win41 C m T0 q b x' (w + one .i) ∧ V41 C m q b (w + one .i) ≤ 1 / m + aut m 1 := by
  obtain ⟨hO, hs, hM⟩ := h
  have h1 : w (.s1 (C.next q b).1) = 0 := hO _ trivial (by simp)
  have hi : w .i = 0 := hO .i trivial (by simp)
  have hmem : memv (w + one .i) = memv w := by funext y; simp
  refine ⟨⟨fun s hs' hn => ?_, by simp; omega, Or.inl ⟨by simp [hi], by simp [h1]⟩,
    hmem ▸ hM⟩, ?_⟩
  · have : s ≠ .i := fun e => hn (by simp [e])
    simp [this, hO s hs' (by simp_all)]
  · have ei : (w + one .i : State (Sp Q L)) .i = 1 := by simp [hi]
    have e1 : (w + one .i : State (Sp Q L)) (.s1 (C.next q b).1) = 0 := by simp [h1]
    simp only [V41, ei, e1, if_true, max_eq_right (zero_le_one' ℕ), le_refl]

end Ripple.sCRNUniversality.ClockedCTM
