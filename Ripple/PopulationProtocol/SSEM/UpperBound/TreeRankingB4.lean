/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage B4: the tree ranking finishes before any expiry or median-timer depletion

P2 Lemma 7.4 (B4) for P_EM, the second half of P3 Lemma 11. From a valid tree with every agent
computing, Unsettled errorcounts `≥ 80n + 1` and median timer `≥ 180` (`RTPaper`), within
`20 n²` interactions all agents are Settled with distinct ranks and median timer `≥ 99`
(`RTheta 99`), with probability `≥ 0.77` (`stageB4`).

The not-hit probability is split (`probNotHitBy_le_three`) at the first exit from the tree class
`TreeOK4` (valid tree, all computing, errorcounts `≥ 2`, median timer `≥ 99`):

* staying in the class without reaching the goal: additive drift of `Φ = n(n-1) phiT`
  (`phi_drift`, P2 Lemma 6.1) gives `Φ(X) / (20 n²) ≤ (55/12)/20 < 0.2292`;
* exit through an errorcount `≤ 1`: `Σ 2·2^{-ec}` grows by `1 + 2/n` per step,
  `≤ n · 2^{-80n} · e^{40n}`;
* exit through the median timer: `2^tExp` grows by `1 + 2/(n(n-1))` per step (ticks, P3 Lemma 4),
  `≤ 2^{129-210} e^{41}`.

`b4_notHit` is the abstract bound (any `trank`, `θ`, extra invariant `E`, goal `G`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingPot

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- The tree class with all agents computing. -/
structure TreeOK4 (E : Config (AgentState n) Opinion n → Prop) (θ : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop where
  core : TreeCore (kC C)
  comp : AllCompK (kC C)
  ec : ∀ w, (C w).1.role = .Unsettled → 2 ≤ (C w).1.errorcount
  med : ∀ w, MedAt (C w).1 → θ ≤ (C w).1.timer
  extra : E C

theorem TreeOK4.hyp {E : Config (AgentState n) Opinion n → Prop} {θ : ℕ}
    {C : Config (AgentState n) Opinion n} (h : TreeOK4 E θ C) (hθ : 2 ≤ θ) : TreeStepHyp C :=
  ⟨h.core, h.ec, fun w hw => hθ.trans (h.med w hw)⟩

theorem one_le_ecV_two {C : Config (AgentState n) Opinion n} {w : Fin n}
    (hw : (C w).1.role = .Unsettled) (hle : (C w).1.errorcount ≤ 1) : 1 ≤ ecV 2 C := by
  classical
  refine le_trans ?_ (Finset.single_le_sum (f := fun w => if (C w).1.role = .Unsettled then
    (2 : ℝ≥0∞) * 2⁻¹ ^ (C w).1.errorcount else 0) (fun _ _ => zero_le) (Finset.mem_univ w))
  simp only [if_pos hw]
  calc (1 : ℝ≥0∞) = 2 * 2⁻¹ ^ 1 := by
        rw [pow_one, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
    _ ≤ 2 * 2⁻¹ ^ (C w).1.errorcount :=
        mul_le_mul_left' (pow_le_pow_right_of_le_one' (by norm_num) hle) _

section B4

variable {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}

/-- **Stage B4, abstract form.** -/
theorem b4_notHit (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hT0 : 2 ≤ 7 * (trank + 4)) {θ : ℕ}
    (hθ : 2 ≤ θ) (hθT : θ ≤ 7 * (trank + 4)) (E G : Config (AgentState n) Opinion n → Prop)
    (hE : ∀ C, TreeOK4 E θ C → ∀ u v, u ≠ v →
      E (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v))
    (hG : ∀ C, TreeOK4 E θ C → (∀ w, (C w).1.role = .Settled) → G C)
    (X : Config (AgentState n) Opinion n) (hX : TreeOK4 E θ X) (W : ℕ) (hW : 1 ≤ W) :
    probNotHitBy (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) hn2 X G W ≤
      phiE X / W + (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ W * ecV 2 X +
        (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ W *
          (2 ^ tExp (7 * (trank + 4)) X * (2 ^ (7 * (trank + 4) - θ + 1))⁻¹) := by
  classical
  set P := protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  set T₀ := 7 * (trank + 4) with hT₀
  set c : ℝ≥0∞ := (2 ^ (T₀ - θ + 1))⁻¹ with hc
  let S : Config (AgentState n) Opinion n → Prop := fun C => G C ∨ ¬ TreeOK4 E θ C
  let T₁ : Config (AgentState n) Opinion n → Prop := fun C =>
    ∃ w, (C w).1.role = .Unsettled ∧ (C w).1.errorcount ≤ 1
  let Ok : Config (AgentState n) Opinion n → Prop := fun C =>
    TreeCore (kC C) ∧ AllCompK (kC C) ∧ E C
  let T₂ : Config (AgentState n) Opinion n → Prop := fun C =>
    ¬ Ok C ∨ ∃ w, MedAt (C w).1 ∧ (C w).1.timer < θ
  have hS : ∀ C, S C → G C ∨ T₁ C ∨ T₂ C := by
    intro C hC
    rcases hC with hg | hnot
    · exact Or.inl hg
    · right
      by_contra hc'
      apply hnot
      have h1 : ¬ T₁ C := fun h => hc' (Or.inl h)
      have h2 : ¬ T₂ C := fun h => hc' (Or.inr h)
      have hOk : Ok C := by by_contra h; exact h2 (Or.inl h)
      exact ⟨hOk.1, hOk.2.1, fun w hw => by
        by_contra hlt; exact h1 ⟨w, hw, by omega⟩, fun w hw => by
        by_contra hlt; exact h2 (Or.inr ⟨w, hw, by omega⟩), hOk.2.2⟩
  have hnS : ∀ C, ¬ S C → TreeOK4 E θ C ∧ ¬ G C := by
    intro C hC
    exact ⟨by by_contra h; exact hC (Or.inr h), fun h => hC (Or.inl h)⟩
  have hstepOk : ∀ C, TreeOK4 E θ C → ∀ u v, u ≠ v → Ok (C.step P u v) := by
    intro C hC u v huv
    obtain ⟨h1, -, -, h4⟩ := tree_step_core (trank := trank) (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) C (hC.hyp hθ) huv hT0 hn3
    exact ⟨h1, h4 hC.comp, hE C hC u v huv⟩
  refine (probNotHitBy_le_three P hn2 X G S T₁ T₂ hS W).trans ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- drift
    have hd := prefixMass_avoid_le_drift P hn2 X S (fun _ => True) phiE trivial
      (fun _ _ _ _ => trivial) (fun C _ hC => by
        obtain ⟨h4, hg⟩ := hnS C hC
        refine phi_drift (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          (hn := hn) hn2 hn3 hT0 C (h4.hyp hθ) h4.comp ?_
        by_contra hU
        apply hg
        apply hG C h4
        intro w
        have h1 := h4.comp w
        cases hr : (C w).1.role
        · exact absurd hr h1
        · rfl
        · exact absurd ⟨w, hr⟩ hU) W
    have hW0 : (W : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl (ENNReal.natCast_ne_top W)), mul_comm]
    exact hd
  · -- errorcount exit
    exact prefixMass_hitFirst_le P hn2 X S T₁ (fun _ => True) (ecV 2) _ le_self_add
      (fun C ⟨w, hw, hle⟩ => Or.inr fun h => by have := h.ec w hw; omega) trivial
      (fun _ _ _ _ => trivial)
      (fun C _ hC => ecV_step (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn2 hn3 hT0 2 C ((hnS C hC).1.hyp hθ) (hnS C hC).1.comp)
      (fun C _ ⟨w, hw, hle⟩ => one_le_ecV_two hw hle) W
  · -- timer exit
    have hXOk : Ok X := ⟨hX.core, hX.comp, hX.extra⟩
    have h := prefixMass_hitFirst_le P hn2 X S T₂ (fun _ => True)
      (fun C => if Ok C then 2 ^ tExp T₀ C * c else 1) _ le_self_add
      (fun C hC => by
        rcases hC with h | ⟨w, hw, hlt⟩
        · exact Or.inr fun h' => h ⟨h'.core, h'.comp, h'.extra⟩
        · exact Or.inr fun h' => by have := h'.med w hw; omega) trivial
      (fun _ _ _ _ => trivial)
      (fun C _ hC => expV_step (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn2 hn3 hT0 Ok c C ((hnS C hC).1.hyp hθ)
        ⟨(hnS C hC).1.core, (hnS C hC).1.comp, (hnS C hC).1.extra⟩
        (hstepOk C (hnS C hC).1))
      (fun C _ hC => by
        simp only
        split_ifs with hOk
        · rcases hC with h | ⟨w, hw, hlt⟩
          · exact absurd hOk h
          · have hm := medTimer_eq (T₀ := T₀) hOk.1 hw
            have hge : T₀ - θ + 1 ≤ tExp T₀ C := by
              unfold tExp; rw [hm]; split_ifs <;> omega
            calc (1 : ℝ≥0∞) = 2 ^ (T₀ - θ + 1) * c := by
                  rw [hc, ENNReal.mul_inv_cancel (by positivity) (by simp)]
              _ ≤ 2 ^ tExp T₀ C * c :=
                  mul_le_mul_right' (pow_le_pow_right₀ (by norm_num) hge) _
        · exact le_rfl) W
    simp only [if_pos hXOk] at h
    exact h

end B4

end Ripple.PopulationProtocol.SSEM
