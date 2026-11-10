/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stage A: from every good configuration to `S_rank ∪ PT_L` (P3 Lemma 9)

P3 Lemma 9 (= P2 Proposition 7.6 for P_EM): from every good configuration, `H = S_rank ∪ PT_L`
is hit within `t₁ + 241 n²` interactions with probability at least `0.86` (`stageA`).

Every trigger lands in `PT_L ⊆ H` (`ptl_of_trig`), so along a run that has not hit `H` no
interaction is a trigger. The proof chains four stages:

| stage | from | to | window | probability | P2 |
|---|---|---|---|---|---|
| `stageA1` | any good | no propagating agent, or `H` | `t₃₃` | `0.9997` | Lemma 5.1 |
| `stageA2` | no propagating agent | no Resetting agent, or `H` | `32 n²` | `0.99999` | Cor. 2.5 |
| `stageA3` | no Resetting agent | all Settled, or `H` | `208 n²` | `0.99999` | Lemma 2.7 |
| `stageA4` | all Settled | `H` | `n²` | `0.8646` | Prop. 7.6, A4 |

* A1: without triggers the effective resetcounts follow the max-minus-one process from their
  initial values (`step_rc`), which is `0` after `t₃₃` interactions except with probability
  `1/(3n)` (`phi_term_le`). Unlike P2, no case split on `PT` is needed: the bound on the
  max-minus-one process holds from every initial vector bounded by `Rmax`.
* A2, A3: per agent, the delay timer (resp. errorcount) plus the number of interactions stays
  at most `Dmax = 32 n` (resp. `Emax = 208 n`), and is positive after the first interaction
  (`step_dorm`, `step_comp`); an agent with `Dmax` (resp. `Emax`) interactions has therefore
  woken (resp. settled). The lower tail of interaction counts (`count_lower_real`) gives
  failure at most `10⁻⁵`.
* A4: outside `S_rank`, two Settled agents share a rank; drawing either ordered pair of them is
  a collision trigger (`step_collision`), so the miss probability is at most
  `(1 - 2/(n(n-1)))^{n²} ≤ e^{-2}`.

The product `0.9997 · 0.99999² · 0.8646 ≥ 0.86` and the window `t₃₃ + 241 n² ≤ t₁ + 241 n²`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.StagesAStep
import Ripple.PopulationProtocol.SSEM.UpperBound.StagesB1
import Ripple.PopulationProtocol.SSEM.UpperBound.StagesSRankC

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### Classes -/

/-- The target of Stage A: `S_rank ∪ PT_L`. -/
abbrev HitA (C : Config (AgentState n) Opinion n) : Prop := SRank C ∨ PTL C

/-- No propagating agent: every effective resetcount is `0`. -/
def NoProp (C : Config (AgentState n) Opinion n) : Prop := ∀ v, effRc (C v).1 = 0

/-- No Resetting agent. -/
def FullComp (C : Config (AgentState n) Opinion n) : Prop := ∀ v, (C v).1.role ≠ .Resetting

/-- All agents Settled. -/
def AllSet (C : Config (AgentState n) Opinion n) : Prop := ∀ v, (C v).1.role = .Settled

/-! ### Invariants along runs that avoid the goal -/

/-- Along a run that avoids `Goal`, an invariant relating the configuration to an iterated
pair-driven vector holds, provided every off-diagonal step from the invariant outside `Goal`
keeps it or enters `Goal`, and the vector update is trivial on diagonal pairs. -/
theorem pathAvoids_inv_iter {Q X Y α : Type*} (P : Protocol Q X Y) (C₀ : Config Q X n)
    (Goal : Config Q X n → Prop) (init : Fin n → α)
    (stp : (Fin n → α) → Fin n × Fin n → Fin n → α) (hdiag : ∀ x i, stp x (i, i) = x)
    (Inv : (Fin n → α) → Config Q X n → Prop) (h₀ : Inv init C₀)
    (hstep : ∀ x C, Inv x C → ¬ Goal C → ∀ i j : Fin n, i ≠ j →
      Inv (stp x (i, j)) (C.step P i j) ∨ Goal (C.step P i j)) :
    ∀ (K : ℕ) (σ : SchedulerPrefix n K), PathAvoids P C₀ Goal K σ →
      Inv (prefixIter init stp K σ) (runPrefix P C₀ K σ)
  | 0, _, _ => h₀
  | K + 1, σ, h => by
      have hK : PathAvoids P C₀ Goal K (Fin.init σ) := h.1
      have hI := pathAvoids_inv_iter P C₀ Goal init stp hdiag Inv h₀ hstep K (Fin.init σ) hK
      have hG := pathAvoids_final P C₀ Goal K (Fin.init σ) hK
      have hlast : ¬ Goal (runPrefix P C₀ (K + 1) σ) := h.2
      rw [runPrefix_succ] at hlast ⊢
      rw [prefixIter_succ]
      generalize σ (Fin.last K) = p at hlast ⊢
      obtain ⟨i, j⟩ := p
      by_cases hij : i = j
      · subst hij
        have hs : (runPrefix P C₀ K (Fin.init σ)).step P i i = runPrefix P C₀ K (Fin.init σ) := by
          simp [Config.step]
        rw [hdiag, hs]
        exact hI
      · rcases hstep _ _ hI hG i j hij with h' | h'
        · exact h'
        · exact absurd h' hlast

theorem maxStep_diag (x : Fin n → ℕ) (i : Fin n) : maxStep x (i, i) = x := by
  funext w
  simp [maxStep, pairUpd]

theorem cntStep_diag (x : Fin n → ℕ) (i : Fin n) : cntStep x (i, i) = x := by
  funext w
  simp [cntStep, mem_PairsInvolving]

/-! ### Lower tail of interaction counts -/

theorem uniformPair_sum_half_pow (hn : 2 ≤ n) (v : Fin n) :
    ∑ p : Fin n × Fin n, uniformPair n hn p *
        (if p ∈ PairsInvolving n v then (2 : ℝ≥0∞)⁻¹ else 1) = 1 - (n : ℝ≥0∞)⁻¹ := by
  classical
  have h1 : ∀ p : Fin n × Fin n, uniformPair n hn p *
      (if p ∈ PairsInvolving n v then (2 : ℝ≥0∞)⁻¹ else 1) +
        (if p ∈ PairsInvolving n v then uniformPair n hn p * 2⁻¹ else 0) =
      uniformPair n hn p := by
    intro p
    split_ifs
    · rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    · rw [mul_one, add_zero]
  have h2 : ∑ p : Fin n × Fin n,
      (if p ∈ PairsInvolving n v then uniformPair n hn p * 2⁻¹ else 0) = (n : ℝ≥0∞)⁻¹ := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul]
    have := pairSetMass_pairsInvolving n hn v
    unfold pairSetMass at this
    rw [this, mul_comm (2 : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
      mul_one]
  have h3 := Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) => h1 p)
  rw [Finset.sum_add_distrib, h2, uniformPair_sum_one hn] at h3
  have hne : (n : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (by omega))
  exact ENNReal.eq_sub_of_add_eq hne h3

/-- **Lower tail of one interaction count.** -/
theorem count_lower_le (hn : 2 ≤ n) (v : Fin n) (K D : ℕ) :
    (2⁻¹ : ℝ≥0∞) ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure {σ | cntIter K σ v < D} ≤
      (1 - (n : ℝ≥0∞)⁻¹) ^ K := by
  classical
  have hE := schedulerPrefix_expect_le_pow hn (fun K σ => (2⁻¹ : ℝ≥0∞) ^ cntIter K σ v)
    (1 - (n : ℝ≥0∞)⁻¹) (by
      intro K σ
      simp only [cntIter, prefixIter_snoc, cntStep]
      have h2 : ∀ p : Fin n × Fin n, uniformPair n hn p *
          (2⁻¹ : ℝ≥0∞) ^ (if p ∈ PairsInvolving n v then
            prefixIter (fun _ => 0) cntStep K σ v + 1
            else prefixIter (fun _ => 0) cntStep K σ v) =
          (2⁻¹ : ℝ≥0∞) ^ prefixIter (fun _ => 0) cntStep K σ v *
            (uniformPair n hn p * (if p ∈ PairsInvolving n v then 2⁻¹ else 1)) := by
        intro p
        split_ifs
        · rw [pow_succ]; ring
        · ring
      rw [Finset.sum_congr rfl (fun p _ => h2 p), ← Finset.mul_sum,
        uniformPair_sum_half_pow hn v, mul_comm]) K
  simp only [cntIter, prefixIter, pow_zero, mul_one] at hE
  refine le_trans ?_ hE
  have hM := schedulerPrefix_markov hn K (fun σ => (2⁻¹ : ℝ≥0∞) ^ cntIter K σ v)
    ((2⁻¹ : ℝ≥0∞) ^ D)
  refine le_trans (mul_le_mul' le_rfl (MeasureTheory.measure_mono ?_)) hM
  intro σ hσ
  exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (le_of_lt hσ)

/-- **Some agent has fewer than `D` interactions** (union bound). -/
theorem count_lower_some_le (hn : 2 ≤ n) (K D : ℕ) :
    (2⁻¹ : ℝ≥0∞) ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ | ∃ v, cntIter K σ v < D} ≤ n * (1 - (n : ℝ≥0∞)⁻¹) ^ K := by
  classical
  have hU : {σ : SchedulerPrefix n K | ∃ v, cntIter K σ v < D} =
      ⋃ v, {σ | cntIter K σ v < D} := by
    ext σ; simp
  rw [hU]
  calc (2⁻¹ : ℝ≥0∞) ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure
        (⋃ v, {σ | cntIter K σ v < D})
      ≤ (2⁻¹ : ℝ≥0∞) ^ D * ∑ v : Fin n, (schedulerPrefixPMF n hn K).toOuterMeasure
          {σ | cntIter K σ v < D} :=
        mul_le_mul' le_rfl (MeasureTheory.measure_iUnion_fintype_le _ _)
    _ = ∑ v : Fin n, (2⁻¹ : ℝ≥0∞) ^ D * (schedulerPrefixPMF n hn K).toOuterMeasure
          {σ | cntIter K σ v < D} := Finset.mul_sum _ _ _
    _ ≤ ∑ _v : Fin n, (1 - (n : ℝ≥0∞)⁻¹) ^ K :=
        Finset.sum_le_sum fun v _ => count_lower_le hn v K D
    _ = n * (1 - (n : ℝ≥0∞)⁻¹) ^ K := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- **Lower count tail with constants**: in `c n²` interactions (`c ≥ 32`, `n ≥ 1608`) some
agent has fewer than `c n` interactions with probability at most `10⁻⁵`. -/
theorem count_lower_real (hN : 1608 ≤ n) (hn2 : 2 ≤ n) (c : ℕ) (hc : 32 ≤ c) :
    (schedulerPrefixPMF n hn2 (c * n ^ 2)).toOuterMeasure
      {σ | ∃ v, cntIter (c * n ^ 2) σ v < c * n} ≤ ENNReal.ofReal (1 / 100000) := by
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  have h := count_lower_some_le hn2 (c * n ^ 2) (c * n)
  have h2 : (2 : ℝ≥0∞) ^ (c * n) * (2⁻¹ : ℝ≥0∞) ^ (c * n) = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have hM : (schedulerPrefixPMF n hn2 (c * n ^ 2)).toOuterMeasure
      {σ | ∃ v, cntIter (c * n ^ 2) σ v < c * n} ≤
      (2 : ℝ≥0∞) ^ (c * n) * (n * (1 - (n : ℝ≥0∞)⁻¹) ^ (c * n ^ 2)) := by
    calc _ = (2 : ℝ≥0∞) ^ (c * n) * ((2⁻¹ : ℝ≥0∞) ^ (c * n) *
          (schedulerPrefixPMF n hn2 (c * n ^ 2)).toOuterMeasure
            {σ | ∃ v, cntIter (c * n ^ 2) σ v < c * n}) := by
          rw [← mul_assoc, h2, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl h
  refine hM.trans ?_
  have h1n : (0 : ℝ) ≤ 1 - 1 / n := by
    rw [sub_nonneg, div_le_one hn0]; linarith
  have hinv : (1 - (n : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 - 1 / n) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, one_div,
      ENNReal.ofReal_inv_of_pos hn0, ENNReal.ofReal_natCast]
  rw [hinv, ← ENNReal.ofReal_pow h1n, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul (by positivity), two_pow_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hl2 := Real.log_two_lt_d9
  have hc' : (32 : ℝ) ≤ c := by exact_mod_cast hc
  have hcn : (32 : ℝ) * n ≤ (c : ℝ) * n := by nlinarith
  have hKr : (((c * n ^ 2 : ℕ)) : ℝ) = (c : ℝ) * (n : ℝ) ^ 2 := by push_cast; ring
  have hx : (1 - 1 / (n : ℝ)) ^ (c * n ^ 2) ≤ Real.exp (-((c : ℝ) * n)) := by
    refine (one_sub_pow_le_exp (by positivity) (by rw [div_le_one hn0]; linarith) _).trans
      (le_of_eq ?_)
    congr 1
    rw [hKr]
    field_simp
  have hnexp : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  have h2D : (2 : ℝ) ^ (c * n) = Real.exp ((c : ℝ) * n * Real.log 2) := by
    rw [show (c : ℝ) * n = ((c * n : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log two_pos]
  have hcn0 : (0 : ℝ) ≤ (c : ℝ) * n := by positivity
  have hyl : (c : ℝ) * n * Real.log 2 ≤ (c : ℝ) * n * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hl2.le hcn0
  calc (2 : ℝ) ^ (c * n) * ((n : ℝ) * (1 - 1 / (n : ℝ)) ^ (c * n ^ 2))
      ≤ Real.exp ((c : ℝ) * n * Real.log 2) * (Real.exp n * Real.exp (-((c : ℝ) * n))) := by
        rw [h2D]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hnexp hx (pow_nonneg h1n _) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = Real.exp ((c : ℝ) * n * Real.log 2 + (n + -((c : ℝ) * n))) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-6 + -6) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-6) * Real.exp (-6) := Real.exp_add _ _
    _ ≤ 0.002479 * 0.002479 :=
        mul_le_mul exp_neg_six_lt.le exp_neg_six_lt.le (Real.exp_pos _).le (by norm_num)
    _ ≤ 1 / 100000 := by norm_num

/-! ### Per-agent invariants through one step -/

section Agents

variable {hn : 0 < n}

/-- A per-agent invariant `Iv state count` passes through one off-diagonal step if it passes
from each input to the corresponding output. -/
theorem step_agents {Iv : AgentState n → ℕ → Prop} (Ok : AgentState n → AgentState n → Prop)
    (hOk : ∀ s t k, Iv s k → Ok s t → Iv t (k + 1))
    (C : Config (AgentState n) Opinion n) (c : Fin n → ℕ) {i j : Fin n} (hij : i ≠ j)
    (hC : ∀ w, Iv (C w).1 (c w))
    (h₁ : Ok (C i).1 ((PEM40 n hn).δ (C i, C j)).1)
    (h₂ : Ok (C j).1 ((PEM40 n hn).δ (C i, C j)).2) :
    ∀ w, Iv ((C.step (PEM40 n hn) i j) w).1 (cntStep c (i, j) w) := by
  intro w
  have hmi : (i, j) ∈ PairsInvolving n i := (mem_PairsInvolving n i (i, j)).mpr ⟨hij, Or.inl rfl⟩
  have hmj : (i, j) ∈ PairsInvolving n j := (mem_PairsInvolving n j (i, j)).mpr ⟨hij, Or.inr rfl⟩
  by_cases hwi : w = i
  · rw [hwi, step_fst C hij, show cntStep c (i, j) i = c i + 1 from if_pos hmi]
    exact hOk _ _ _ (hC i) h₁
  · by_cases hwj : w = j
    · rw [hwj, step_snd C hij, show cntStep c (i, j) j = c j + 1 from if_pos hmj]
      exact hOk _ _ _ (hC j) h₂
    · have hnw : (i, j) ∉ PairsInvolving n w := by
        intro h
        rcases ((mem_PairsInvolving n w (i, j)).mp h).2 with h' | h'
        · exact hwi h'.symm
        · exact hwj h'.symm
      rw [step_other' _ C i j w hwi hwj, show cntStep c (i, j) w = c w from if_neg hnw]
      exact hC w

end Agents

/-- Dormant agents: delay timer plus interactions at most `Dmax`, positive delay timer after
the first interaction. -/
def DormInv (n : ℕ) (s : AgentState n) (k : ℕ) : Prop :=
  effRc s = 0 ∧ (s.role = .Resetting → s.delaytimer + k ≤ 32 * n ∧ (1 ≤ k → 1 ≤ s.delaytimer))

theorem dormInv_step (s t : AgentState n) (k : ℕ) (hs : DormInv n s k) (h : DormOK s t) :
    DormInv n t (k + 1) := by
  refine ⟨?_, fun ht => ?_⟩
  · by_cases ht : t.role = .Resetting
    · rw [effRc_of_resetting ht]; exact (h ht).2.1
    · exact effRc_of_not_resetting ht
  · obtain ⟨h1, -, h3, h4⟩ := h ht
    have := (hs.2 h1).1
    exact ⟨by omega, fun _ => h4⟩

/-- Unsettled agents: errorcount plus interactions at most `Emax`, positive errorcount after
the first interaction. -/
def CompInv (n : ℕ) (s : AgentState n) (k : ℕ) : Prop :=
  s.role ≠ .Resetting ∧
    (s.role = .Unsettled → s.errorcount + k ≤ 208 * n ∧ (1 ≤ k → 1 ≤ s.errorcount))

theorem compInv_step (s t : AgentState n) (k : ℕ) (hs : CompInv n s k) (h : CompOK s t) :
    CompInv n t (k + 1) := by
  refine ⟨h.1, fun ht => ?_⟩
  obtain ⟨h1, h3, h4⟩ := h.2.2 ht
  have := (hs.2 h1).1
  exact ⟨by omega, fun _ => h4⟩

/-! ### The four stages -/

/-- **Stage A1** (P2 Lemma 5.1 with `τ_H` in place of `τ_PT`). -/
theorem stageA1 : StageBound (fun _ => True) (fun C => NoProp C ∨ HitA C) dormWindow 0.9997 := by
  classical
  intro n hN hn hn2 X hX _
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  set P := PEM40 n hn
  set K := dormWindow n
  have hy : ∀ v, effRc (X v).1 ≤ rmaxPaper n := fun v => by
    unfold effRc
    split_ifs
    · exact (hX v).2.1
    · exact Nat.zero_le _
  have hinv := pathAvoids_inv_iter P X (fun C => NoProp C ∨ HitA C) (fun w => effRc (X w).1)
    maxStep maxStep_diag (fun x C => ∀ w, effRc (C w).1 = x w) (fun w => rfl) (by
      intro x C hI _ i j hij
      rcases step_rc (hn := hn) C i j with hT | ⟨h1, h2⟩
      · exact Or.inr (Or.inr (Or.inr (ptl_of_trig C hij hT)))
      · left
        intro w
        simp only [maxStep, pairUpd]
        by_cases hwi : w = i
        · rw [hwi, if_pos ⟨hij, Or.inl rfl⟩, step_fst C hij, ← hI i, ← hI j]
          exact h1
        · by_cases hwj : w = j
          · rw [hwj, if_pos ⟨hij, Or.inr rfl⟩, step_snd C hij, ← hI i, ← hI j]
            exact h2
          · rw [if_neg (fun h => h.2.elim hwi hwj), step_other' _ C i j w hwi hwj]
            exact hI w)
  have hsub : {σ | PathAvoids P X (fun C => NoProp C ∨ HitA C) K σ} ⊆
      {σ | 3 ≤ PhiN (maxFrom (fun w => effRc (X w).1) K σ)} := by
    intro σ hσ
    by_contra hlt
    simp only [Set.mem_setOf_eq, not_le] at hlt
    apply pathAvoids_final P X _ K σ hσ
    refine Or.inl (fun v => ?_)
    have hv : effRc ((runPrefix P X K σ) v).1 = maxFrom (fun w => effRc (X w).1) K σ v :=
      hinv K σ hσ v
    rw [hv]
    by_contra hne
    have h3 := three_le_phiN hne
    have hle : phiN (maxFrom (fun w => effRc (X w).1) K σ v) ≤
        PhiN (maxFrom (fun w => effRc (X w).1) K σ) :=
      Finset.single_le_sum (f := fun w => phiN (maxFrom (fun w => effRc (X w).1) K σ w))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  have hnot : probNotHitBy P hn2 X (fun C => NoProp C ∨ HitA C) K ≤
      ENNReal.ofReal (1 / (3 * n)) := by
    refine (probNotHitBy_le_prefixMass_avoid P hn2 X _ K).trans
      ((MeasureTheory.measure_mono hsub).trans ?_)
    have hp := phi_term_le hn2 (fun w => effRc (X w).1) (rmaxPaper n) hy K (Nat.le_ceil _)
    have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
    have h3' : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
    rw [← ENNReal.mul_le_mul_iff_right h3 h3']
    refine hp.trans (le_of_eq ?_)
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
  apply ofReal_le_probHitBy_of_probNotHitBy_le P hn2 X _ K 0.9997 _ (by norm_num)
    (by positivity) _ hnot
  have : (1 : ℝ) / (3 * n) ≤ 1 / (3 * 1608) := by gcongr
  linarith [this, show (1 : ℝ) / (3 * 1608) ≤ 0.0003 by norm_num]

/-- **Stage A2** (P2 Corollary 2.5 with Corollary 1.6 row 3). -/
theorem stageA2 :
    StageBound NoProp (fun C => FullComp C ∨ HitA C) (fun n => 32 * n ^ 2) 0.99999 := by
  classical
  intro n hN hn hn2 X hX hA
  set P := PEM40 n hn
  have h0 : ∀ w, DormInv n (X w).1 0 := fun w =>
    ⟨hA w, fun _ => ⟨by have := (hX w).2.2.2.1; omega, fun h => absurd h (by omega)⟩⟩
  have hinv := pathAvoids_inv_iter P X (fun C => FullComp C ∨ HitA C) (fun _ => 0) cntStep
    cntStep_diag (fun c C => ∀ w, DormInv n (C w).1 (c w)) h0 (by
      intro c C hI _ i j hij
      rcases step_dorm (hn := hn) C i j (hI i).1 (hI j).1 with hT | ⟨h1, h2⟩
      · exact Or.inr (Or.inr (Or.inr (ptl_of_trig C hij hT)))
      · exact Or.inl (step_agents DormOK dormInv_step C c hij hI h1 h2))
  have hsub : {σ | PathAvoids P X (fun C => FullComp C ∨ HitA C) (32 * n ^ 2) σ} ⊆
      {σ | ∃ v, cntIter (32 * n ^ 2) σ v < 32 * n} := by
    intro σ hσ
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_exists, not_lt] at hcon
    apply pathAvoids_final P X _ _ σ hσ
    refine Or.inl (fun v hv => ?_)
    obtain ⟨h1, h2⟩ := (hinv _ σ hσ v).2 hv
    have h3 := hcon v
    have h' : cntIter (32 * n ^ 2) σ v = prefixIter (fun _ => 0) cntStep (32 * n ^ 2) σ v := rfl
    have := h2 (by omega)
    omega
  have hnot : probNotHitBy P hn2 X (fun C => FullComp C ∨ HitA C) (32 * n ^ 2) ≤
      ENNReal.ofReal (1 / 100000) :=
    (probNotHitBy_le_prefixMass_avoid P hn2 X _ _).trans
      ((MeasureTheory.measure_mono hsub).trans (count_lower_real hN hn2 32 le_rfl))
  exact ofReal_le_probHitBy_of_probNotHitBy_le P hn2 X _ _ 0.99999 _ (by norm_num)
    (by norm_num) (by norm_num) hnot

/-- **Stage A3** (P2 Lemma 2.7 with Corollary 1.6 row 5). -/
theorem stageA3 :
    StageBound FullComp (fun C => AllSet C ∨ HitA C) (fun n => 208 * n ^ 2) 0.99999 := by
  classical
  intro n hN hn hn2 X hX hA
  set P := PEM40 n hn
  have h0 : ∀ w, CompInv n (X w).1 0 := fun w =>
    ⟨hA w, fun _ => ⟨by have := (hX w).2.2.1; omega, fun h => absurd h (by omega)⟩⟩
  have hinv := pathAvoids_inv_iter P X (fun C => AllSet C ∨ HitA C) (fun _ => 0) cntStep
    cntStep_diag (fun c C => ∀ w, CompInv n (C w).1 (c w)) h0 (by
      intro c C hI _ i j hij
      rcases step_comp (hn := hn) C i j (hI i).1 (hI j).1 with hT | ⟨h1, h2⟩
      · exact Or.inr (Or.inr (Or.inr (ptl_of_trig C hij hT)))
      · exact Or.inl (step_agents CompOK compInv_step C c hij hI h1 h2))
  have hsub : {σ | PathAvoids P X (fun C => AllSet C ∨ HitA C) (208 * n ^ 2) σ} ⊆
      {σ | ∃ v, cntIter (208 * n ^ 2) σ v < 208 * n} := by
    intro σ hσ
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_exists, not_lt] at hcon
    apply pathAvoids_final P X _ _ σ hσ
    refine Or.inl (fun v => ?_)
    obtain ⟨h1, h2⟩ := hinv _ σ hσ v
    have h3 := hcon v
    have h' : cntIter (208 * n ^ 2) σ v =
        prefixIter (fun _ => 0) cntStep (208 * n ^ 2) σ v := rfl
    cases hr : ((runPrefix P X (208 * n ^ 2) σ) v).1.role with
    | Resetting => exact absurd hr h1
    | Settled => rfl
    | Unsettled =>
        obtain ⟨h4, h5⟩ := h2 hr
        have := h5 (by omega)
        omega
  have hnot : probNotHitBy P hn2 X (fun C => AllSet C ∨ HitA C) (208 * n ^ 2) ≤
      ENNReal.ofReal (1 / 100000) :=
    (probNotHitBy_le_prefixMass_avoid P hn2 X _ _).trans
      ((MeasureTheory.measure_mono hsub).trans (count_lower_real hN hn2 208 (by norm_num)))
  exact ofReal_le_probHitBy_of_probNotHitBy_le P hn2 X _ _ 0.99999 _ (by norm_num)
    (by norm_num) (by norm_num) hnot

theorem exp_neg_two_le : Real.exp (-2) ≤ 0.1354 := by
  have he := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 2 < Real.exp 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
  calc (0.1354 : ℝ)⁻¹ ≤ 2.7182818283 ^ 2 := by norm_num
    _ ≤ Real.exp 2 := h2.le

/-- **Stage A4** (P2 Proposition 7.6, stage A4): collisions of equal ranks. -/
theorem stageA4 : StageBound AllSet HitA (fun n => n ^ 2) 0.8646 := by
  classical
  intro n hN hn hn2 X _ hA
  set P := PEM40 n hn
  have hpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hD : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hpos
  set m : ℝ := 2 / ((n * (n - 1) : ℕ) : ℝ) with hm
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 1 := by
    rw [hm, div_le_one hD]
    have : 2 ≤ n * (n - 1) :=
      Nat.le_trans (by omega : 2 ≤ n - 1) (Nat.le_mul_of_pos_left _ (by omega))
    exact_mod_cast this
  have hInv : ∀ C : Config (AgentState n) Opinion n, AllSet C → ¬ HitA C → ∀ i j : Fin n,
      AllSet (C.step P i j) ∨ HitA (C.step P i j) := by
    intro C hC _ i j
    by_cases hij : i = j
    · subst hij
      left
      have hs : C.step P i i = C := by simp [Config.step]
      rw [hs]
      exact hC
    · rcases step_settled (hn := hn) C i j (hC i) (hC j) with hT | ⟨o₁, o₂⟩
      · exact Or.inr (Or.inr (ptl_of_trig C hij hT))
      · left
        intro w
        by_cases hwi : w = i
        · rw [hwi, step_fst C hij]; exact o₁
        · by_cases hwj : w = j
          · rw [hwj, step_snd C hij]; exact o₂
          · rw [step_other' _ C i j w hwi hwj]; exact hC w
  have hstep : ∀ C : Config (AgentState n) Opinion n, AllSet C → ¬ HitA C →
      ∃ S : Finset (Fin n × Fin n), (∀ p ∈ S, HitA (C.step P p.1 p.2)) ∧
        ENNReal.ofReal m ≤ ∑ p ∈ S, uniformPair n hn2 p := by
    intro C hC hnot
    have hinj : ¬ Function.Injective (fun v => (C v).1.rank) :=
      fun hi => hnot (Or.inl ⟨hC, hi⟩)
    obtain ⟨u, w, huw, hne⟩ : ∃ u w : Fin n, (C u).1.rank = (C w).1.rank ∧ u ≠ w := by
      by_contra hcon
      push Not at hcon
      exact hinj (fun a b hab => hcon a b hab)
    have hpne : (u, w) ≠ (w, u) := fun h => hne (Prod.ext_iff.mp h).1
    have hS : ∀ p ∈ ({(u, w), (w, u)} : Finset (Fin n × Fin n)), p.1 ≠ p.2 := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hne
      · exact Ne.symm hne
    refine ⟨{(u, w), (w, u)}, ?_, ?_⟩
    · intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Or.inr (ptl_of_trig C hne (step_collision C u w (hC u) (hC w) huw))
      · exact Or.inr (ptl_of_trig C (Ne.symm hne)
          (step_collision C w u (hC w) (hC u) huw.symm))
    · rw [uniformPair_mass_card hn2 _ hS, Finset.card_pair hpne]
      apply le_of_eq
      rw [hm]
      norm_num
  have hgeom := probNotHitBy_le_geom P hn2 X HitA AllSet m hm0 hA hInv hstep (n ^ 2)
  have hreal : (1 - m) ^ (n ^ 2) ≤ Real.exp (-2) := by
    refine (one_sub_pow_le_exp hm0 hm1 _).trans (Real.exp_le_exp.mpr ?_)
    have hle : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : n * (n - 1) ≤ n ^ 2 := by
        rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast this
    have h2 : 2 ≤ m * ((n ^ 2 : ℕ) : ℝ) := by
      rw [hm, Nat.cast_pow, div_mul_eq_mul_div, le_div_iff₀ hD]
      linarith
    linarith
  have hnot : probNotHitBy P hn2 X HitA (n ^ 2) ≤ ENNReal.ofReal (Real.exp (-2)) := by
    refine hgeom.trans ?_
    rw [← ENNReal.ofReal_pow (by linarith)]
    exact ENNReal.ofReal_le_ofReal hreal
  exact ofReal_le_probHitBy_of_probNotHitBy_le P hn2 X HitA (n ^ 2) 0.8646 (Real.exp (-2))
    (by norm_num) (Real.exp_pos _).le (by linarith [exp_neg_two_le]) hnot

/-! ### Composition -/

theorem StageBound.compH {A M B : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop}
    {W₁ W₂ : ℕ → ℕ} {q₁ q₂ : ℝ} (h₁ : StageBound A (fun C => M C ∨ HitA C) W₁ q₁)
    (h₂ : StageBound M (fun C => B C ∨ HitA C) W₂ q₂) (hq₁ : 0 ≤ q₁) (hq₂ : q₂ ≤ 1) :
    StageBound A (fun C => B C ∨ HitA C) (fun n => W₁ n + W₂ n) (q₁ * q₂) := by
  refine h₁.comp ?_ hq₁
  intro n hN hn hn2 X hX hA
  rcases hA with hM | hH
  · exact h₂ n hN hn hn2 X hX hM
  · exact stage_goal (PEM40 n hn) hn2 GoodPaper (fun C => B C ∨ HitA C) (W₂ n) _
      (ENNReal.ofReal_le_one.mpr hq₂) X hX (Or.inr hH)

theorem StageBound.compH' {A M : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop}
    {W₁ W₂ : ℕ → ℕ} {q₁ q₂ : ℝ} (h₁ : StageBound A (fun C => M C ∨ HitA C) W₁ q₁)
    (h₂ : StageBound M HitA W₂ q₂) (hq₁ : 0 ≤ q₁) (hq₂ : q₂ ≤ 1) :
    StageBound A HitA (fun n => W₁ n + W₂ n) (q₁ * q₂) := by
  refine h₁.comp ?_ hq₁
  intro n hN hn hn2 X hX hA
  rcases hA with hM | hH
  · exact h₂ n hN hn hn2 X hX hM
  · exact stage_goal (PEM40 n hn) hn2 GoodPaper HitA (W₂ n) _
      (ENNReal.ofReal_le_one.mpr hq₂) X hX hH

/-- **Stage A** (P3 Lemma 9). -/
theorem stageA : StageA := by
  have h := ((stageA1.compH stageA2 (by norm_num) (by norm_num)).compH stageA3 (by norm_num)
    (by norm_num)).compH' stageA4 (by norm_num) (by norm_num)
  change StageBound (fun _ => True) HitA (fun n => tOne n + 241 * n ^ 2) 0.86
  refine h.mono (fun n _ => ?_) (by norm_num)
  change dormWindow n + 32 * n ^ 2 + 208 * n ^ 2 + n ^ 2 ≤ tOne n + 241 * n ^ 2
  unfold tOne
  omega

/-- Non-vacuity: at `n = 1608` a good configuration (all agents Unsettled) lies outside
`S_rank ∪ PT_L`, so `stageA` says something about it. -/
example : ∃ X : Config (AgentState 1608) Opinion 1608, GoodPaper X ∧ ¬ HitA X := by
  refine ⟨fun _ => (⟨.Unsettled, 0, .F, 0, .phi, 0, 0, 1, 0⟩, .A), fun _ => ?_, ?_⟩
  · exact ⟨by norm_num, Nat.zero_le _, by norm_num, Nat.zero_le _, by norm_num⟩
  · rintro (⟨h, -⟩ | ⟨⟨v, hv, -⟩, -⟩)
    · exact Role.noConfusion (h 0)
    · exact Role.noConfusion hv

end Ripple.PopulationProtocol.SSEM
