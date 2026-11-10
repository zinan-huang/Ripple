/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage B3: everybody wakes, the tree starts (P2 Lemma 7.3 for P_EM)

The first half of P3 Lemma 11. From a fully dormant configuration with exactly one leader
(`FDOne`), the run stays a valid tree (`TreeOK3`: `TreeCore`, Unsettled errorcounts `≥ B`,
median timer `≥ θ`) until every agent is computing; with `B = 80n + 1`, `θ = 180` this is the
class `RTPaper` from which stage B4 starts.

The not-hit probability is split at the first exit from `TreeOK3`:

* the run stays in `TreeOK3` with a dormant agent: `Σ_{dormant} 2^{dt}` shrinks by `1 - 1/n` per
  step (a dormant agent's delay timer drops at each of its interactions, and it wakes at `0`;
  P2 Lemma 2.4 (c), (d)), so this has probability `≤ (1 - 1/n)^W n 2^{Dmax}`;
* exit through an errorcount `< B`: `Σ_{Unsettled} 2^{B-1-ec} + Σ_{dormant} 2^{B-1-Emax}` grows
  by `1 + 2/n` per step;
* exit through the median timer: as in stage B4 (`expV_step`).
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingB4

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- The tree class of the wake phase. -/
structure TreeOK3 (E : Config (AgentState n) Opinion n → Prop) (B θ : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop where
  core : TreeCore (kC C)
  ec : ∀ w, (C w).1.role = .Unsettled → B ≤ (C w).1.errorcount
  med : ∀ w, MedAt (C w).1 → θ ≤ (C w).1.timer
  extra : E C

theorem TreeOK3.hyp {E : Config (AgentState n) Opinion n → Prop} {B θ : ℕ}
    {C : Config (AgentState n) Opinion n} (h : TreeOK3 E B θ C) (hB : 2 ≤ B) (hθ : 2 ≤ θ) :
    TreeStepHyp C :=
  ⟨h.core, fun w hw => hB.trans (h.ec w hw), fun w hw => hθ.trans (h.med w hw)⟩

/-- The dormancy potential `Σ_{Resetting} 2^{dt}`. -/
noncomputable def dormV (C : Config (AgentState n) Opinion n) : ℝ≥0∞ :=
  ∑ w, if (C w).1.role = .Resetting then 2 ^ (C w).1.delaytimer else 0

/-- One agent's term of the wake-phase errorcount potential: a dormant agent counts as an
Unsettled agent with errorcount `E` (the value it wakes with). -/
noncomputable def ecTerm (a : ℝ≥0∞) (E : ℕ) (s : AgentState n) : ℝ≥0∞ :=
  if s.role = .Unsettled then a * 2⁻¹ ^ s.errorcount
    else if s.role = .Resetting then a * 2⁻¹ ^ E else 0

/-- The wake-phase errorcount potential. -/
noncomputable def ecV3 (a : ℝ≥0∞) (E : ℕ) (C : Config (AgentState n) Opinion n) : ℝ≥0∞ :=
  ∑ w, ecTerm a E (C w).1

section B3

variable {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}

theorem dormV_ne_top (C : Config (AgentState n) Opinion n) : dormV C ≠ ⊤ := by
  unfold dormV
  rw [ne_eq, ENNReal.sum_eq_top]
  rintro ⟨w, -, hw⟩
  split_ifs at hw
  · exact ENNReal.pow_ne_top (by norm_num) hw
  · exact ENNReal.zero_ne_top hw

/-- **Dormancy potential**: `E[V(next)] ≤ (1 - 1/n) V`. -/
theorem dormV_step (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hT0 : 2 ≤ 7 * (trank + 4))
    (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        dormV (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ≤
      (1 - (n : ℝ≥0∞)⁻¹) * dormV C := by
  classical
  set t : Fin n → ℝ≥0∞ := fun w =>
    if (C w).1.role = .Resetting then 2 ^ (C w).1.delaytimer else 0 with ht
  have hpt : ∀ p : Fin n × Fin n,
      uniformPair n hn2 p *
        (dormV (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) +
          (t p.1 + t p.2) * 2⁻¹) ≤ uniformPair n hn2 p * dormV C := by
    rintro ⟨u, v⟩
    by_cases huv : u = v
    · subst huv; rw [uniformPair_apply_self, zero_mul, zero_mul]
    · apply mul_le_mul_left'
      set C' := C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
      have hw : ∀ w, (if (C' w).1.role = .Resetting then 2 ^ (C' w).1.delaytimer else 0) +
          ((if w = u then t w else 0) + (if w = v then t w else 0)) * 2⁻¹ ≤ t w := by
        intro w
        have hhalf : t w * 2⁻¹ ≤ t w := by
          calc t w * 2⁻¹ ≤ t w * 1 := mul_le_mul_left' (by norm_num) _
            _ = t w := mul_one _
        by_cases hR : (C' w).1.role = .Resetting
        · rw [if_pos hR]
          rcases tree_step_nonSettled (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C h huv hT0 hn3 w (by rw [hR]; decide) with ⟨hwu, hwv, e⟩ | ⟨hwp, hs⟩
          · rw [if_neg hwu, if_neg hwv, add_zero, zero_mul, add_zero]
            have e' : C' w = C w := e
            have hR0 : (C w).1.role = .Resetting := by rw [← e']; exact hR
            simp only [ht, if_pos hR0]
            rw [e']
          · obtain ⟨hR0, -, hdt⟩ := hs.resetting hR
            have key : 2 ^ (C' w).1.delaytimer + t w * 2⁻¹ = t w := by
              simp only [ht, if_pos hR0]
              rw [← hdt, pow_succ, mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
                mul_one, mul_two]
            rcases hwp with hwp | hwp
            · rw [if_pos hwp, if_neg (by rw [hwp]; exact huv), add_zero]; exact key.le
            · rw [if_neg (by rw [hwp]; exact Ne.symm huv), if_pos hwp, zero_add]; exact key.le
        · rw [if_neg hR, zero_add]
          by_cases hwu : w = u
          · rw [if_pos hwu, if_neg (by rw [hwu]; exact huv), add_zero]; exact hhalf
          · by_cases hwv : w = v
            · rw [if_neg hwu, if_pos hwv, zero_add]; exact hhalf
            · rw [if_neg hwu, if_neg hwv, add_zero, zero_mul]; exact zero_le
      calc dormV C' + (t u + t v) * 2⁻¹
          = ∑ w, ((if (C' w).1.role = .Resetting then 2 ^ (C' w).1.delaytimer else 0) +
              ((if w = u then t w else 0) + (if w = v then t w else 0)) * 2⁻¹) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_add_distrib,
              Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ _),
              if_pos (Finset.mem_univ _)]
            rfl
        _ ≤ ∑ w, t w := Finset.sum_le_sum fun w _ => hw w
        _ = dormV C := rfl
  have hsum := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hpt p
  rw [← Finset.sum_mul, uniformPair_sum_one hn2, one_mul] at hsum
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have hend : ∑ p : Fin n × Fin n, uniformPair n hn2 p * ((t p.1 + t p.2) * 2⁻¹) =
      (n : ℝ≥0∞)⁻¹ * dormV C := by
    simp only [← mul_assoc, ← Finset.sum_mul]
    rw [uniformPair_sum_endpoints hn2 t]
    have : ∑ w, t w = dormV C := rfl
    rw [this, mul_comm _ (2⁻¹ : ℝ≥0∞), ← mul_assoc, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [hend] at hsum
  have hfin : (n : ℝ≥0∞)⁻¹ * dormV C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by exact_mod_cast (show n ≠ 0 by omega)))
      (dormV_ne_top C)
  rw [ENNReal.sub_mul (fun _ _ => dormV_ne_top C), one_mul]
  exact ENNReal.le_sub_of_add_le_right hfin hsum

/-- **Wake-phase errorcount potential**: `E[V(next)] ≤ (1 + 2/n) V`. -/
theorem ecV3_step (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hT0 : 2 ≤ 7 * (trank + 4)) (a : ℝ≥0∞)
    (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        ecV3 a Emax (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2)
      ≤ (1 + 2 * (n : ℝ≥0∞)⁻¹) * ecV3 a Emax C := by
  classical
  have hpt : ∀ p : Fin n × Fin n,
      ecV3 a Emax (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2)
        ≤ ecV3 a Emax C + (ecTerm a Emax (C p.1).1 + ecTerm a Emax (C p.2).1) := by
    rintro ⟨u, v⟩
    by_cases huv : u = v
    · subst huv; rw [step_self]; exact le_self_add
    · have hw : ∀ w, ecTerm a Emax
            (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1 ≤
          ecTerm a Emax (C w).1 + (if w = u then ecTerm a Emax (C w).1 else 0) +
            (if w = v then ecTerm a Emax (C w).1 else 0) := by
        intro w
        by_cases hS : (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
            w).1.role = .Settled
        · have h0 : ecTerm a Emax
              (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1 = 0 := by
            unfold ecTerm
            rw [if_neg (by rw [hS]; decide), if_neg (by rw [hS]; decide)]
          rw [h0]; exact zero_le
        rcases tree_step_nonSettled (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
          C h huv hT0 hn3 w hS with ⟨hwu, hwv, e⟩ | ⟨hwp, hs⟩
        · rw [if_neg hwu, if_neg hwv, add_zero, add_zero, e]
        · have key : ecTerm a Emax
              (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1 ≤
              ecTerm a Emax (C w).1 + ecTerm a Emax (C w).1 := by
            unfold ecTerm
            by_cases hU : (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
                w).1.role = .Unsettled
            · rw [if_pos hU]
              rcases hs.unsettled hU with ⟨hU0, hle⟩ | ⟨hR0, hE⟩
              · rw [if_pos hU0]
                calc a * 2⁻¹ ^ (C.step (protocolPEM n trank Rmax
                        (rankDeltaOSSR Rmax Emax Dmax hn)) u v w).1.errorcount
                    ≤ a * (2 * 2⁻¹ ^ (C w).1.errorcount) :=
                      mul_le_mul_left' (two_inv_pow_le hle) a
                  _ = _ := by ring
              · have hnU : ¬ (C w).1.role = .Unsettled := by rw [hR0]; decide
                rw [if_neg hnU, if_pos hR0, hE]
                exact le_self_add
            · rw [if_neg hU]
              by_cases hR : (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn))
                  u v w).1.role = .Resetting
              · rw [if_pos hR]
                obtain ⟨hR0, -, -⟩ := hs.resetting hR
                have hnU : ¬ (C w).1.role = .Unsettled := by rw [hR0]; decide
                rw [if_neg hnU, if_pos hR0]
                exact le_self_add
              · rw [if_neg hR]; exact zero_le
          rcases hwp with hwp | hwp
          · have hwv : ¬ w = v := by rw [hwp]; exact huv
            rw [if_pos hwp, if_neg hwv, add_zero]; exact key
          · have hwu : ¬ w = u := by rw [hwp]; exact Ne.symm huv
            rw [if_neg hwu, if_pos hwp, add_zero]; exact key
      calc ecV3 a Emax (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)
          ≤ ∑ w, (ecTerm a Emax (C w).1 + (if w = u then ecTerm a Emax (C w).1 else 0) +
              (if w = v then ecTerm a Emax (C w).1 else 0)) :=
            Finset.sum_le_sum fun w _ => hw w
        _ = ecV3 a Emax C + (ecTerm a Emax (C u).1 + ecTerm a Emax (C v).1) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
              Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
            simp only [ecV3]
            ring
  calc ∑ p : Fin n × Fin n, uniformPair n hn2 p * _
      ≤ ∑ p : Fin n × Fin n, uniformPair n hn2 p *
          (ecV3 a Emax C + (ecTerm a Emax (C p.1).1 + ecTerm a Emax (C p.2).1)) :=
        Finset.sum_le_sum fun p _ => mul_le_mul_left' (hpt p) _
    _ = ecV3 a Emax C + 2 * (n : ℝ≥0∞)⁻¹ * ∑ w, ecTerm a Emax (C w).1 := by
        rw [← uniformPair_sum_endpoints hn2 (fun w => ecTerm a Emax (C w).1)]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, uniformPair_sum_one hn2,
          one_mul]
    _ = (1 + 2 * (n : ℝ≥0∞)⁻¹) * ecV3 a Emax C := by
        simp only [ecV3]; ring

theorem one_le_two_pow_mul_inv {m e : ℕ} (h : e ≤ m) :
    (1 : ℝ≥0∞) ≤ 2 ^ m * 2⁻¹ ^ e := by
  calc (1 : ℝ≥0∞) = 2 ^ m * 2⁻¹ ^ m := by
        rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (by positivity) (by simp)]
    _ ≤ 2 ^ m * 2⁻¹ ^ e := mul_le_mul_left' (pow_le_pow_right_of_le_one' (by norm_num) h) _

/-- **Stage B3, abstract form.** Split at the first exit from `TreeOK3`: dormancy potential,
errorcount potential (with `a = 2^{B-1}`), median-timer potential. -/
theorem b3_notHit (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hT0 : 2 ≤ 7 * (trank + 4)) {B θ : ℕ}
    (hB : 2 ≤ B) (hθ : 2 ≤ θ) (hθT : θ ≤ 7 * (trank + 4))
    (E G : Config (AgentState n) Opinion n → Prop)
    (hE : ∀ C, TreeOK3 E B θ C → ∀ u v, u ≠ v →
      E (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v))
    (hG : ∀ C, TreeOK3 E B θ C → AllCompK (kC C) → G C)
    (X : Config (AgentState n) Opinion n) (hX : TreeOK3 E B θ X) (W : ℕ) :
    probNotHitBy (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) hn2 X G W ≤
      (1 - (n : ℝ≥0∞)⁻¹) ^ W * dormV X + (1 + 2 * (n : ℝ≥0∞)⁻¹) ^ W * ecV3 (2 ^ (B - 1)) Emax X +
        (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ W *
          (2 ^ tExp (7 * (trank + 4)) X * (2 ^ (7 * (trank + 4) - θ + 1))⁻¹) := by
  classical
  set P := protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn) with hP
  set T₀ := 7 * (trank + 4) with hT₀
  set c : ℝ≥0∞ := (2 ^ (T₀ - θ + 1))⁻¹ with hc
  let S : Config (AgentState n) Opinion n → Prop := fun C =>
    (TreeOK3 E B θ C ∧ AllCompK (kC C)) ∨ ¬ TreeOK3 E B θ C
  let T₁ : Config (AgentState n) Opinion n → Prop := fun C =>
    ∃ w, (C w).1.role = .Unsettled ∧ (C w).1.errorcount + 1 ≤ B
  let Ok : Config (AgentState n) Opinion n → Prop := fun C => TreeCore (kC C) ∧ E C
  let T₂ : Config (AgentState n) Opinion n → Prop := fun C =>
    ¬ Ok C ∨ ∃ w, MedAt (C w).1 ∧ (C w).1.timer < θ
  have hS : ∀ C, S C → G C ∨ T₁ C ∨ T₂ C := by
    intro C hC
    rcases hC with ⟨h3, hc'⟩ | hnot
    · exact Or.inl (hG C h3 hc')
    · right
      by_contra hc'
      apply hnot
      have h1 : ¬ T₁ C := fun h => hc' (Or.inl h)
      have h2 : ¬ T₂ C := fun h => hc' (Or.inr h)
      have hOk : Ok C := by by_contra h; exact h2 (Or.inl h)
      exact ⟨hOk.1, fun w hw => by
        by_contra hlt; exact h1 ⟨w, hw, by omega⟩, fun w hw => by
        by_contra hlt; exact h2 (Or.inr ⟨w, hw, by omega⟩), hOk.2⟩
  have hnS : ∀ C, ¬ S C → TreeOK3 E B θ C ∧ ¬ AllCompK (kC C) := by
    intro C hC
    have h3 : TreeOK3 E B θ C := by by_contra h; exact hC (Or.inr h)
    exact ⟨h3, fun h => hC (Or.inl ⟨h3, h⟩)⟩
  have hstepOk : ∀ C, TreeOK3 E B θ C → ∀ u v, u ≠ v → Ok (C.step P u v) := by
    intro C hC u v huv
    obtain ⟨h1, -, -, -⟩ := tree_step_core (trank := trank) (Rmax := Rmax) (Emax := Emax)
      (Dmax := Dmax) (hn := hn) C (hC.hyp hB (by omega)) huv hT0 hn3
    exact ⟨h1, hE C hC u v huv⟩
  refine (probNotHitBy_le_three P hn2 X G S T₁ T₂ hS W).trans ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- dormancy
    exact prefixMass_avoid_le_potential P hn2 X S (fun _ => True) dormV _ trivial
      (fun _ _ _ _ => trivial)
      (fun C _ hC => dormV_step (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn2 hn3 hT0 C ((hnS C hC).1.hyp hB hθ))
      (fun C _ hC => by
        have hnc := (hnS C hC).2
        simp only [AllCompK, not_forall, not_not] at hnc
        obtain ⟨w, hw⟩ := hnc
        have hw' : (C w).1.role = .Resetting := hw
        refine le_trans ?_ (Finset.single_le_sum (f := fun w => if (C w).1.role = .Resetting
          then (2 : ℝ≥0∞) ^ (C w).1.delaytimer else 0) (fun _ _ => zero_le) (Finset.mem_univ w))
        simp only [if_pos hw']
        exact one_le_pow₀ (by norm_num)) W
  · -- errorcount exit
    exact prefixMass_hitFirst_le P hn2 X S T₁ (fun _ => True) (ecV3 (2 ^ (B - 1)) Emax) _
      le_self_add
      (fun C ⟨w, hw, hle⟩ => Or.inr fun h => by have := h.ec w hw; omega) trivial
      (fun _ _ _ _ => trivial)
      (fun C _ hC => ecV3_step (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn2 hn3 hT0 _ C ((hnS C hC).1.hyp hB hθ))
      (fun C _ ⟨w, hw, hle⟩ => by
        refine le_trans ?_ (Finset.single_le_sum (f := fun w => ecTerm (2 ^ (B - 1)) Emax
          (C w).1) (fun _ _ => zero_le) (Finset.mem_univ w))
        simp only [ecTerm, if_pos hw]
        exact one_le_two_pow_mul_inv (by omega)) W
  · -- timer exit
    have hXOk : Ok X := ⟨hX.core, hX.extra⟩
    have h := prefixMass_hitFirst_le P hn2 X S T₂ (fun _ => True)
      (fun C => if Ok C then 2 ^ tExp T₀ C * c else 1) _ le_self_add
      (fun C hC => by
        rcases hC with h | ⟨w, hw, hlt⟩
        · exact Or.inr fun h' => h ⟨h'.core, h'.extra⟩
        · exact Or.inr fun h' => by have := h'.med w hw; omega) trivial
      (fun _ _ _ _ => trivial)
      (fun C _ hC => expV_step (trank := trank) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        (hn := hn) hn2 hn3 hT0 Ok c C ((hnS C hC).1.hyp hB hθ)
        ⟨(hnS C hC).1.core, (hnS C hC).1.extra⟩
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

end B3

end Ripple.PopulationProtocol.SSEM
