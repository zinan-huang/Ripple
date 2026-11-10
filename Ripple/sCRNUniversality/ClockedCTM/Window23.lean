/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Window12

/-!
# Window `𝒦_2 + I → 𝒦_3` (FIX3-SCWB-T32 Lemma 4.3, Lemma 5.3)

From `𝒦_2(q, w) + I`: `I + S_{q,2} → S_{q,3}` fires once, then `S_{q,2} + S_{q,3} → 2 S_{q,3}`;
the restores have no reactant; only `T + M → T* + M*` changes the memory, and it keeps
`#M - #T = x - T0` (`win23_fire`).  The target `𝒦_3(q, w)` is reached when `S_{q,2} = 0` and
`min(#T, #M) = 0`.

Potential: `V23 w = [I = 1]/m + aut m (max #S_{q,3} 1) + cmp Δ (min #T #M)`, where
`Δ = |x - T0|` and `cmp Δ n = Σ_{k < n} 1/((k+1)(k+1+Δ))` is the expected annihilation time
(Lemma 1.3(b)).
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

/-- `cmp Δ n = Σ_{k < n} 1/((k+1)(k+1+Δ))`. -/
noncomputable def cmp (Δ n : ℕ) : ℝ := ∑ k ∈ Finset.range n, 1 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + Δ))

theorem cmp_succ (Δ n : ℕ) : cmp Δ (n + 1) = cmp Δ n + 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + Δ)) := by
  simp [cmp, Finset.sum_range_succ]

theorem cmp_nonneg (Δ n : ℕ) : 0 ≤ cmp Δ n := Finset.sum_nonneg fun _ _ => by positivity

theorem cmp_mono (Δ : ℕ) {a b : ℕ} (h : a ≤ b) : cmp Δ a ≤ cmp Δ b := by
  unfold cmp
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    fun _ _ _ => by positivity

theorem cmp_eq_zero_iff (Δ n : ℕ) : cmp Δ n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [cmp_succ] at h
    have := cmp_nonneg Δ k
    have : 0 < 1 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + Δ)) := by positivity
    linarith
  · rintro rfl; simp [cmp]

/-- `cmp Δ n ≤ hrm n / Δ`. -/
theorem cmp_le_hrm_div {Δ : ℕ} (hΔ : 1 ≤ Δ) (n : ℕ) : cmp Δ n ≤ hrm n / Δ := by
  unfold cmp hrm
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- States of the window `𝒦_2(q, w) + I → 𝒦_3(q, w)`. -/
def Win23 (m T0 : ℕ) (q : Q) (x : ℕ) (w : State (Sp Q L)) : Prop :=
  OnlyState [.s2 q, .s3 q, .i] w ∧ w (.s2 q) + w (.s3 q) = m ∧
    ((w .i = 1 ∧ w (.s3 q) = 0) ∨ (w .i = 0 ∧ 1 ≤ w (.s3 q))) ∧ MemA m T0 x (memv w) ∧
    MemReset (memv w)

/-- `Δ = |x - T0|`. -/
def gap (T0 x : ℕ) : ℕ := if x ≤ T0 then T0 - x else x - T0

/-- Potential of the window `𝒦_2 + I → 𝒦_3`. -/
noncomputable def V23 (m T0 : ℕ) (q : Q) (x : ℕ) (w : State (Sp Q L)) : ℝ :=
  (if w .i = 1 then 1 / (m : ℝ) else 0) + aut m (max (w (.s3 q)) 1) +
    cmp (gap T0 x) (min (w (.mem .t)) (w (.mem .m)))

/-- In the memory class with restored memory, `#M + T0 = #T + x`. -/
theorem m_add_T0 {m T0 x : ℕ} {v : Mem → ℕ} (hM : MemA m T0 x v) (hR : MemReset v) :
    v .m + T0 = v .t + x := by
  obtain ⟨h1, h2, h3, -⟩ := hM
  obtain ⟨r1, r2, -⟩ := hR
  omega

/-- The comparison reaction `T + M → T* + M*` has rate `q (q + Δ)` with `q = min(#T, #M)`. -/
theorem pair_rate {m T0 x : ℕ} {w : State (Sp Q L)} (hM : MemA m T0 x (memv w))
    (hR : MemReset (memv w)) :
    w (.mem .t) * w (.mem .m) =
      min (w (.mem .t)) (w (.mem .m)) * (min (w (.mem .t)) (w (.mem .m)) + gap T0 x) := by
  have := m_add_T0 hM hR
  simp only [memv_apply] at this
  unfold gap
  split_ifs with h
  · rw [min_eq_right (by omega), show w (.mem .m) + (T0 - x) = w (.mem .t) by omega, mul_comm]
  · rw [min_eq_left (by omega), show w (.mem .t) + (x - T0) = w (.mem .m) by omega]

/-- **Lemma 4.3 (closure).** -/
theorem win23_fire {m T0 x : ℕ} {q : Q} {w : State (Sp Q L)} (h : Win23 m T0 q x w)
    (i : Rx Q L) (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    Win23 m T0 q x ((rxn C i).fire w) ∧ V23 m T0 q x ((rxn C i).fire w) ≤ V23 m T0 q x w := by
  obtain ⟨hO, hs, hst, hM, hR⟩ := h
  have hM' := hM
  have hR' := hR
  simp only [MemA, MemReset, memv_apply] at hM' hR'
  rw [rate_ne_zero_iff] at hr
  cases i with
  | tick => exact absurd trivial hi
  | up c => exact absurd trivial hi
  | down c => exact absurd trivial hi
  | eps q' b => exact absurd (hO (.u q' b) trivial (by simp)) hr.2
  | auto41 q' b => exact absurd (hO (.u q' b) trivial (by simp)) hr.1
  | adv12 q' => exact absurd (hO (.s1 q') trivial (by simp)) (by simpa [src2] using hr.2)
  | auto12 q' => exact absurd (hO (.s1 q') trivial (by simp)) (by simpa [src1] using hr.1)
  | adv23 q' =>
    by_cases hq : q' = q
    · subst hq
      simp only [src1, src2] at hr
      have hI : w .i = 1 ∧ w (.s3 q') = 0 := by omega
      have hmem : memv ((rxn C (.adv23 q')).fire w) = memv w :=
        memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
      refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, hmem ▸ hM, hmem ▸ hR⟩, ?_⟩
      · cases s <;> simp_all [out, Sp.IsState]
      · simp [src1, src2, out] <;> omega
      · simp [src1, src2, out] <;> omega
      · simp only [V23]
        simp [src1, src2, out, hI.1, hI.2]
    · exact absurd (hO (.s2 q') trivial (by simp [hq])) (by simpa [src2] using hr.2)
  | auto23 q' =>
    by_cases hq : q' = q
    · subst hq
      simp only [src1, src2] at hr
      have hI : w .i = 0 ∧ 1 ≤ w (.s3 q') := by omega
      have hmem : memv ((rxn C (.auto23 q')).fire w) = memv w :=
        memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
      refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, hmem ▸ hM, hmem ▸ hR⟩, ?_⟩
      · cases s <;> simp_all [out, Sp.IsState]
      · simp [src1, src2, out] <;> omega
      · simp [src1, src2, out] <;> omega
      · simp only [V23]
        simp [src1, src2, out, hI.1]
        have h1 := aut_anti (m := m) (show max (w (.s3 q')) 1 ≤ max (w (.s3 q') - 1 + 2) 1 by omega)
        have h2 := aut_anti (m := m) (show max (w (.s3 q')) 1 ≤ w (.s3 q') - 1 + 2 by omega)
        linarith
    · exact absurd (hO (.s2 q') trivial (by simp [hq])) (by simpa [src1] using hr.1)
  | adv3 q' =>
    have h3 : w (.s3 q') ≠ 0 := by simpa [src2] using hr.2
    have hq : q' = q := by
      by_contra hq; exact h3 (hO (.s3 q') trivial (by simp [hq]))
    subst hq
    simp only [src1] at hr
    omega
  | rt q' => exact absurd (hO (.rq q') trivial (by simp)) (by simpa [src1] using hr.1)
  | rm q' => exact absurd (hO (.rq q') trivial (by simp)) (by simpa [src1] using hr.1)
  | auto34 q' b => exact absurd (hO (.u q' b) trivial (by simp)) (by simpa [src2] using hr.2)
  | rsM q' => exact absurd hR'.1 (by simpa [src2] using hr.2)
  | rsT q' => exact absurd hR'.2.1 (by simpa [src2] using hr.2)
  | rsD q' => exact absurd hR'.2.2.1 (by simpa [src2] using hr.2)
  | rsB q' => exact absurd hR'.2.2.2 (by simpa [src2] using hr.2)
  | pair =>
    simp only [src1, src2] at hr
    refine ⟨⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · cases s <;> simp_all [out, Sp.IsState]
    · simp [src1, src2, out] <;> omega
    · simp [src1, src2, out] <;> omega
    · simp only [MemA, memv_apply]; simp [src1, src2, out] <;> omega
    · simp only [MemReset, memv_apply]; simp [src1, src2, out] <;> omega
    · simp only [V23]
      have e1 : ((rxn C .pair).fire w) .i = w .i := by simp [src1, src2, out]
      have e2 : ((rxn C .pair).fire w) (.s3 q) = w (.s3 q) := by simp [src1, src2, out]
      have e3 : min (((rxn C .pair).fire w) (.mem .t)) (((rxn C .pair).fire w) (.mem .m)) ≤
          min (w (.mem .t)) (w (.mem .m)) := by simp [src1, src2, out] <;> omega
      rw [e1, e2]
      linarith [cmp_mono (gap T0 x) e3]
  | k2 => exact absurd hM'.2.2.2.2.2.2 (by simpa [src1] using hr.1)
  | k1 => exact absurd hM'.2.2.2.2.2.1 (by simpa [src1] using hr.1)
  | cMs q' b | cTs q' b | cT q' b | cM q' b | cD q' b | cB q' b =>
    exact absurd (hO (.u q' b) trivial (by simp)) (by simpa [src1] using hr.1)

theorem V23_nonneg (m T0 : ℕ) (q : Q) (x : ℕ) (w : State (Sp Q L)) : 0 ≤ V23 m T0 q x w := by
  unfold V23
  have := aut_nonneg m (max (w (.s3 q)) 1)
  have := cmp_nonneg (gap T0 x) (min (w (.mem .t)) (w (.mem .m)))
  have : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
  linarith

/-- The target `𝒦_3(q, w)` is the zero set of `V23` in the window. -/
theorem k3_iff_V23 {m T0 x : ℕ} (hm : 2 ≤ m) {q : Q} {w : State (Sp Q L)}
    (h : Win23 m T0 q x w) : K3 m T0 q x w ↔ V23 m T0 q x w = 0 := by
  obtain ⟨hO, hs, hst, hM, hR⟩ := h
  constructor
  · rintro ⟨hO3, h3, _, _, hTM⟩
    have hi : w .i = 0 := hO3 .i trivial (by simp)
    have hmin : min (w (.mem .t)) (w (.mem .m)) = 0 := by omega
    simp [V23, hi, h3, hmin, aut_eq_zero_of (le_max_left m 1), cmp]
  · intro hV
    have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have a1 := aut_nonneg m (max (w (.s3 q)) 1)
    have a2 := cmp_nonneg (gap T0 x) (min (w (.mem .t)) (w (.mem .m)))
    have a3 : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
    unfold V23 at hV
    have e3 : (if w .i = 1 then 1 / (m : ℝ) else 0) = 0 := by linarith
    have e1 : aut m (max (w (.s3 q)) 1) = 0 := by linarith
    have e2 : cmp (gap T0 x) (min (w (.mem .t)) (w (.mem .m))) = 0 := by linarith
    have hi : w .i = 0 := by
      rcases hst with h | h
      · rw [if_pos h.1] at e3; exact absurd e3 (by positivity)
      · exact h.1
    have h3 : m ≤ w (.s3 q) := by
      by_contra hlt
      exact absurd e1 (aut_pos (le_max_right _ _) (by omega)).ne'
    have hmin := (cmp_eq_zero_iff _ _).mp e2
    refine ⟨fun s hs' hn => ?_, by omega, hM, hR, by omega⟩
    by_cases e : s = .s2 q
    · rw [e]; omega
    · by_cases e' : s = .i
      · rw [e', hi]
      · exact hO s hs' (by simp_all)

/-- **Lemma 5.3 (drift).** -/
theorem win23_drift {m T0 x : ℕ} (hm : 2 ≤ m) {q : Q} {w : State (Sp Q L)}
    (h : Win23 m T0 q x w) (hK : ¬ K3 m T0 q x w) :
    drift C (V23 m T0 q x) w ≤ -1 := by
  have hmono : ∀ i : Rx Q L, ¬ i.IsClock → rate C i w ≠ 0 →
      V23 m T0 q x ((rxn C i).fire w) ≤ V23 m T0 q x w := fun i hi hr => (win23_fire C h i hi hr).2
  have hW := h
  obtain ⟨hO, hs, hst, hM, hR⟩ := h
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rcases hst with ⟨hi, h3⟩ | ⟨hi, h3⟩
  · refine (drift_le_sum C _ w hmono {.adv23 q}).trans (le_of_eq ?_)
    rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
    have e : V23 m T0 q x ((rxn C (.adv23 q)).fire w) = V23 m T0 q x w - 1 / m := by
      simp only [V23]
      simp [src1, src2, out, hi, h3]
      ring
    rw [e, rate_eq]
    simp only [src1, src2, hi, h3]
    rw [show w (.s2 q) = m by omega]
    field_simp
    ring
  · rcases Nat.lt_or_ge (w (.s3 q)) m with hlt | hge
    · refine (drift_le_sum C _ w hmono {.auto23 q}).trans (le_of_eq ?_)
      rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
      have e : V23 m T0 q x ((rxn C (.auto23 q)).fire w) - V23 m T0 q x w =
          aut m (w (.s3 q) + 1) - aut m (w (.s3 q)) := by
        simp only [V23]
        simp [src1, src2, out, hi]
        try rw [max_eq_left (by omega : 1 ≤ w (.s3 q) - 1 + 2)]
        rw [max_eq_left h3, show w (.s3 q) - 1 + 2 = w (.s3 q) + 1 by omega]
      rw [e, rate_eq]
      simp only [src1, src2]
      have := aut_drift (m := m) h3 hlt
      rw [show w (.s2 q) = m - w (.s3 q) by omega]
      push_cast at this ⊢
      linear_combination this
    · -- comparison `T + M → T* + M*`
      have h3' : w (.s3 q) = m := by omega
      have hmin : 1 ≤ min (w (.mem .t)) (w (.mem .m)) := by
        by_contra h0
        apply hK
        rw [k3_iff_V23 hm hW]
        have : min (w (.mem .t)) (w (.mem .m)) = 0 := by omega
        simp [V23, hi, h3', this, aut_eq_zero_of (le_max_left m 1), cmp]
      refine (drift_le_sum C _ w hmono {.pair}).trans (le_of_eq ?_)
      rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
      have hfire : min (((rxn C .pair).fire w) (.mem .t)) (((rxn C .pair).fire w) (.mem .m)) + 1 =
          min (w (.mem .t)) (w (.mem .m)) := by simp [src1, src2, out]; omega
      have e1 : ((rxn C .pair).fire w) .i = w .i := by simp [src1, src2, out]
      have e2 : ((rxn C .pair).fire w) (.s3 q) = w (.s3 q) := by simp [src1, src2, out]
      have e : V23 m T0 q x ((rxn C .pair).fire w) - V23 m T0 q x w =
          -(1 / (((min (w (.mem .t)) (w (.mem .m)) : ℕ) : ℝ) *
            (((min (w (.mem .t)) (w (.mem .m)) : ℕ) : ℝ) + (gap T0 x : ℝ)))) := by
        simp only [V23, e1, e2]
        rw [← hfire, cmp_succ]
        push_cast
        ring
      rw [e, rate_eq]
      simp only [src1, src2]
      rw [pair_rate hM hR]
      have hk0 : (0 : ℝ) < ((min (w (.mem .t)) (w (.mem .m)) : ℕ) : ℝ) := by exact_mod_cast hmin
      have hpos : (0 : ℝ) < ((min (w (.mem .t)) (w (.mem .m)) : ℕ) : ℝ) *
          (((min (w (.mem .t)) (w (.mem .m)) : ℕ) : ℝ) + (gap T0 x : ℝ)) := by positivity
      rw [Nat.cast_mul, Nat.cast_add, mul_neg, mul_one_div_cancel hpos.ne']

/-- **Start of the window** (tick from `𝒦_2`). -/
theorem win23_start {m T0 x : ℕ} {q : Q} {w : State (Sp Q L)} (h : K2 m T0 q x w) :
    Win23 m T0 q x (w + one .i) ∧
      V23 m T0 q x (w + one .i) ≤ 1 / m + aut m 1 + cmp (gap T0 x) T0 := by
  obtain ⟨hO, hs, hM, hR⟩ := h
  have h3 : w (.s3 q) = 0 := hO (.s3 q) trivial (by simp)
  have hi : w .i = 0 := hO .i trivial (by simp)
  have hmem : memv (w + one .i) = memv w := by funext y; simp
  refine ⟨⟨fun s hs' hn => ?_, by simp; omega, Or.inl ⟨by simp [hi], by simp [h3]⟩,
    hmem ▸ hM, hmem ▸ hR⟩, ?_⟩
  · have : s ≠ .i := fun e => hn (by simp [e])
    simp [this, hO s hs' (by simp_all)]
  · have et : (w + one .i : State (Sp Q L)) (.mem .t) = w (.mem .t) := by simp
    have em : (w + one .i : State (Sp Q L)) (.mem .m) = w (.mem .m) := by simp
    have ei : (w + one .i : State (Sp Q L)) .i = 1 := by simp [hi]
    have e3 : (w + one .i : State (Sp Q L)) (.s3 q) = 0 := by simp [h3]
    simp only [V23, et, em, ei, e3, if_true, max_eq_right (zero_le_one' ℕ)]
    have hT : min (w (.mem .t)) (w (.mem .m)) ≤ T0 := by
      simp only [MemA, memv_apply] at hM
      omega
    linarith [cmp_mono (gap T0 x) hT]

end Ripple.sCRNUniversality.ClockedCTM
