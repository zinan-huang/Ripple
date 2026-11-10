/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The uniform window for P_EM from six stage bounds (P3 Theorem 22)

Configuration classes of P3 §1.3 for the flat paper instance, the six stage bounds of P3 as
propositions, and their composition (`pemPaperWindow_of_stages`): if the six stage bounds hold,
then `PEMPaperWindow 40 208 32 1608 1043 (1/5)`, hence `KanayaThm4Time`
(`kanayaThm4Time_of_stages`).

| stage | P3 | from | to | window | probability |
|---|---|---|---|---|---|
| `StageA` | Lemma 9 | any good | `SRank ∪ PTL` | `t₁ + 241 n²` | `0.86` |
| `StageA'` | Lemma 13 | `SRank` | `Decided ∪ PTL` | `23 n²` | `0.915` |
| `Epoch1` | Prop. 15 | `PTL` | `Decided` | `t₁ + t₂ + 75 n²` | `0.515` |
| `StageC` | Lemma 17 | `Decided` | `S_em ∪ ZTwo` | `311 n²` | `0.997` |
| `Epoch2` | Prop. 20 | `ZTwo` | `Cons` | `t₁ + t₂ + 75 n²` | `0.515` |
| `StageE` | Lemma 21 | `Cons` | `S_em` | `308 n²` | `0.999` |

Here `t₁ = propWindow n + dormWindow n ≤ n²/2` (`two_t1_le`) and `t₂ = 4 n (n - 1)`. The
product of the probabilities is at least `0.2`, and the windows add up to at most `1043 n²`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.Thm4Assembly
import Ripple.PopulationProtocol.SSEM.UpperBound.DormancyPaper

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped ENNReal

variable {n : ℕ}

/-! ### Classes (P3 §1.3) -/

/-- All agents satisfy the range bounds of the paper instance (`trank = 40`, `e = 208`,
`d = 32`). -/
def GoodPaper (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v, GoodPEM (7 * (40 + 4)) (208 * n) (rmaxPaper n) (32 * n) (C v).1

/-- Median-type ranks: `m* = ⌈n/2⌉ - 1`, and also `m* + 1` when `n` is even. -/
def IsMedType (n r : ℕ) : Prop := r + 1 = ceilHalf n ∨ (n % 2 = 0 ∧ r = ceilHalf n)

/-- `PT_L`: some agent is triggered (Resetting with `resetcount = Rmax`) and some agent is a
leader. -/
def PTL (C : Config (AgentState n) Opinion n) : Prop :=
  (∃ v, (C v).1.role = .Resetting ∧ (C v).1.resetcount = rmaxPaper n) ∧
    ∃ v, (C v).1.leader = .L

/-- `S_rank`: all agents Settled with pairwise distinct ranks. -/
def SRank (C : Config (AgentState n) Opinion n) : Prop :=
  (∀ v, (C v).1.role = .Settled) ∧ Function.Injective (fun v => (C v).1.rank)

/-- `R(θ)`: `S_rank` with median timer at least `θ`. -/
def RTheta (θ : ℕ) (C : Config (AgentState n) Opinion n) : Prop :=
  SRank C ∧ ∀ v, (C v).1.rank.val + 1 = ceilHalf n → θ ≤ (C v).1.timer

/-- `S_sw`: `S_rank` with inputs sorted by rank. -/
def SSorted (C : Config (AgentState n) Opinion n) : Prop :=
  SRank C ∧ ∀ v, ((C v).2 = Opinion.A ↔ (C v).1.rank.val < nAOf C)

/-- `D`: sorted, and every agent of median-type rank has the majority answer. -/
def Decided (C : Config (AgentState n) Opinion n) : Prop :=
  SSorted C ∧ ∀ v, IsMedType n (C v).1.rank.val → (C v).1.answer = majorityAnswer C

/-- `Z`: exactly two agents are Resetting, both triggered leaders with the majority answer; all
other agents are Settled with pairwise distinct ranks, none of them the median rank. -/
def ZTwo (C : Config (AgentState n) Opinion n) : Prop :=
  ∃ s s' : Fin n, s ≠ s' ∧
    (∀ w, (w = s ∨ w = s') → (C w).1.role = .Resetting ∧ (C w).1.resetcount = rmaxPaper n ∧
      (C w).1.leader = .L ∧ (C w).1.answer = majorityAnswer C) ∧
    (∀ w, w ≠ s → w ≠ s' → (C w).1.role = .Settled ∧ (C w).1.rank.val + 1 ≠ ceilHalf n) ∧
    (∀ w w', w ≠ s → w ≠ s' → w' ≠ s → w' ≠ s' → (C w).1.rank = (C w').1.rank → w = w')

/-! ### Stage bounds (P3) -/

/-- The paper instance with `trank = 40`, `e = 208`, `d = 32`. -/
noncomputable abbrev PEM40 (n : ℕ) (hn : 0 < n) : Protocol (AgentState n) Opinion Output :=
  protocolPEMPaper n 40 208 32 hn

/-- `t₁ = K₃₂ + t₃₃`. -/
noncomputable def tOne (n : ℕ) : ℕ := propWindow n + dormWindow n

/-- A stage bound: from every good configuration in `A`, `B` is hit within `W n` interactions
with probability at least `q`, for all `n ≥ 1608`. -/
def StageBound (A B : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop) (W : ℕ → ℕ)
    (q : ℝ) : Prop :=
  ∀ n, 1608 ≤ n → ∀ (hn : 0 < n) (hn2 : 2 ≤ n) (X : Config (AgentState n) Opinion n),
    GoodPaper X → A X → ENNReal.ofReal q ≤ probHitBy (PEM40 n hn) hn2 X B (W n)

/-- **Stage A** (P3 Lemma 9): from every good configuration to `S_rank ∪ PT_L`. -/
def StageA : Prop :=
  StageBound (fun _ => True) (fun C => SRank C ∨ PTL C) (fun n => tOne n + 241 * n ^ 2) 0.86

/-- **Stage A′** (P3 Lemma 13): `S_rank → D ∪ PT_L`. -/
def StageA' : Prop :=
  StageBound SRank (fun C => Decided C ∨ PTL C) (fun n => 23 * n ^ 2) 0.915

/-- **Epoch 1** (P3 Proposition 15): `PT_L → D`. -/
def Epoch1 : Prop :=
  StageBound PTL Decided (fun n => tOne n + 4 * n * (n - 1) + 75 * n ^ 2) 0.515

/-- **Stage C** (P3 Lemma 17): `D → S_em ∪ Z`. -/
def StageC : Prop :=
  StageBound Decided (fun C => IsSilentConsensus C ∨ ZTwo C) (fun n => 311 * n ^ 2) 0.997

/-- **Epoch 2** (P3 Proposition 20): `Z → Cons`. -/
def Epoch2 : Prop :=
  StageBound ZTwo IsConsensusConfig (fun n => tOne n + 4 * n * (n - 1) + 75 * n ^ 2) 0.515

/-- **Stage E** (P3 Lemma 21): `Cons → S_em`. -/
def StageE : Prop :=
  StageBound IsConsensusConfig IsSilentConsensus (fun n => 308 * n ^ 2) 0.999

/-! ### Composition -/

section Compose

variable (P : Protocol (AgentState n) Opinion Output) (hn2 : 2 ≤ n)
  (Good : Config (AgentState n) Opinion n → Prop)
  (hGood : ∀ C, Good C → ∀ i j : Fin n, Good (C.step P i j))

include hGood in
theorem stage_compose (A Mid B : Config (AgentState n) Opinion n → Prop) (t₁ t₂ : ℕ)
    (q₁ q₂ : ℝ≥0∞)
    (h₁ : ∀ X, Good X → A X → q₁ ≤ probHitBy P hn2 X Mid t₁)
    (h₂ : ∀ Y, Good Y → Mid Y → q₂ ≤ probHitBy P hn2 Y B t₂) :
    ∀ X, Good X → A X → q₁ * q₂ ≤ probHitBy P hn2 X B (t₁ + t₂) := by
  classical
  intro X hX hA
  have he := probHitBy_eq_and_inv_of_invariant P hn2 X Mid Good hX hGood t₁
  have h1 : q₁ ≤ ProbHitWithin P hn2 X (fun C => Mid C ∧ Good C) t₁ := by
    rw [he]; exact h₁ X hX hA
  exact probHitBy_add_ge_mul P hn2 X (fun C => Mid C ∧ Good C) B t₁ t₂ q₁ q₂ h1
    (fun C hC => h₂ C hC.2 hC.1)

theorem stage_mono (A B : Config (AgentState n) Opinion n → Prop) (t t' : ℕ) (q q' : ℝ≥0∞)
    (h : ∀ X, Good X → A X → q ≤ probHitBy P hn2 X B t) (ht : t ≤ t') (hq : q' ≤ q) :
    ∀ X, Good X → A X → q' ≤ probHitBy P hn2 X B t' := fun X hX hA =>
  hq.trans ((h X hX hA).trans (probHitBy_mono_time_of_le P hn2 X B ht))

theorem stage_or (A₁ A₂ B : Config (AgentState n) Opinion n → Prop) (t : ℕ) (q : ℝ≥0∞)
    (h₁ : ∀ X, Good X → A₁ X → q ≤ probHitBy P hn2 X B t)
    (h₂ : ∀ X, Good X → A₂ X → q ≤ probHitBy P hn2 X B t) :
    ∀ X, Good X → (A₁ X ∨ A₂ X) → q ≤ probHitBy P hn2 X B t := fun X hX hA =>
  hA.elim (h₁ X hX) (h₂ X hX)

theorem stage_goal (B : Config (AgentState n) Opinion n → Prop) (t : ℕ) (q : ℝ≥0∞)
    (hq : q ≤ 1) : ∀ X, Good X → B X → q ≤ probHitBy P hn2 X B t := fun X _ hB =>
  hq.trans ((probHitBy_zero_of_goal P hn2 X B hB).symm.le.trans
    (probHitBy_mono_time_of_le P hn2 X B (Nat.zero_le t)))

end Compose

theorem goodPaper_step {hn : 0 < n} (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n)
    (hC : GoodPaper C) (i j : Fin n) : GoodPaper (C.step (PEM40 n hn) i j) :=
  (pemPaperSimulation (trank := 40) (e := 208) (d := 32) hn hn2 (by norm_num)).goodC_step hC i j

/-- `2 t₁ ≤ n²` for `n ≥ 1608`. -/
theorem two_tOne_le (hN : 1608 ≤ n) : 2 * tOne n ≤ n ^ 2 := by
  have hn' : (1608 : ℝ) ≤ n := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by linarith
  set L := Real.log n with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  -- log 3 ≤ 1.1 and log 1608 ≤ 7.5, from `exp 1 > 2.7182818`
  have he := Real.exp_one_gt_d9
  have hl3 : Real.log 3 ≤ 1.1 := by
    have h : (3 : ℝ) ^ 10 ≤ Real.exp 11 := by
      rw [show (11 : ℝ) = (11 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      calc (3 : ℝ) ^ 10 ≤ 2.7182818283 ^ 11 := by norm_num
        _ ≤ Real.exp 1 ^ 11 := by gcongr
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_exp] at this
    push_cast at this
    linarith
  have hl1608 : Real.log 1608 ≤ 7.5 := by
    have h : (1608 : ℝ) ^ 2 ≤ Real.exp 15 := by
      rw [show (15 : ℝ) = (15 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      calc (1608 : ℝ) ^ 2 ≤ 2.7182818283 ^ 15 := by norm_num
        _ ≤ Real.exp 1 ^ 15 := by gcongr
    have := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_exp] at this
    push_cast at this
    linarith
  have hLn : L ≤ 6.5 + n / 1608 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / 1608 by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have hl3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hR : (rmaxPaper n : ℝ) ≤ 60 * L + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hP : (propWindow n : ℝ) ≤ 4 * n * L + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hD : (dormWindow n : ℝ) ≤ (3 * (n : ℝ) / 2) * (2 * L + (rmaxPaper n : ℝ) * Real.log 3) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hRl : (rmaxPaper n : ℝ) * Real.log 3 ≤ (60 * L + 1) * 1.1 :=
    mul_le_mul hR hl3 hl3' (by positivity)
  have hreal : 2 * ((propWindow n : ℝ) + dormWindow n) ≤ (n : ℝ) ^ 2 := by
    have h1 : (dormWindow n : ℝ) ≤ (3 * (n : ℝ) / 2) * (2 * L + (60 * L + 1) * 1.1) + 1 :=
      hD.trans (by gcongr)
    nlinarith
  unfold tOne
  exact_mod_cast hreal

/-- **The uniform window from the six stage bounds** (P3 Theorem 22). -/
theorem pemPaperWindow_of_stages (hA : StageA) (hA' : StageA') (h1 : Epoch1) (hC : StageC)
    (h2 : Epoch2) (hE : StageE) : PEMPaperWindow 40 208 32 1608 1043 5⁻¹ := by
  classical
  intro n hN hn hn2 X hX
  set P := PEM40 n hn
  have hG : ∀ C, GoodPaper C → ∀ i j : Fin n, GoodPaper (C.step P i j) :=
    fun C hC i j => goodPaper_step hn2 C hC i j
  set KB := tOne n + 4 * n * (n - 1) + 75 * n ^ 2
  -- probabilities
  set qA := ENNReal.ofReal 0.86
  set qA' := ENNReal.ofReal 0.915
  set qB := ENNReal.ofReal 0.515
  set qC := ENNReal.ofReal 0.997
  set qE := ENNReal.ofReal 0.999
  have hqB1 : qB ≤ 1 := ENNReal.ofReal_le_one.mpr (by norm_num)
  have hqA'1 : qA' ≤ 1 := ENNReal.ofReal_le_one.mpr (by norm_num)
  -- from Cons
  have sE := hE n hN hn hn2
  -- from Z: Epoch2 then StageE
  have sZ := stage_compose P hn2 GoodPaper hG ZTwo IsConsensusConfig IsSilentConsensus KB
    (308 * n ^ 2) qB qE (h2 n hN hn hn2) sE
  -- from S_em ∪ Z
  have sEmZ := stage_or P hn2 GoodPaper IsSilentConsensus ZTwo IsSilentConsensus
    (KB + 308 * n ^ 2) (qB * qE)
    (stage_goal P hn2 GoodPaper IsSilentConsensus _ _
      (mul_le_one' hqB1 (ENNReal.ofReal_le_one.mpr (by norm_num)))) sZ
  -- from D
  have sD := stage_compose P hn2 GoodPaper hG Decided (fun C => IsSilentConsensus C ∨ ZTwo C)
    IsSilentConsensus (311 * n ^ 2) (KB + 308 * n ^ 2) qC (qB * qE) (hC n hN hn hn2) sEmZ
  set VD := 311 * n ^ 2 + (KB + 308 * n ^ 2)
  set qD := qC * (qB * qE)
  -- from PT_L
  have sPT := stage_compose P hn2 GoodPaper hG PTL Decided IsSilentConsensus KB VD qB qD
    (h1 n hN hn hn2) sD
  -- from D ∪ PT_L
  have sDPT := stage_or P hn2 GoodPaper Decided PTL IsSilentConsensus (KB + VD) (qB * qD)
    (stage_mono P hn2 GoodPaper Decided IsSilentConsensus VD (KB + VD) qD (qB * qD) sD
      (Nat.le_add_left _ _) (mul_le_of_le_one_left zero_le hqB1)) sPT
  -- from S_rank
  have sSR := stage_compose P hn2 GoodPaper hG SRank (fun C => Decided C ∨ PTL C)
    IsSilentConsensus (23 * n ^ 2) (KB + VD) qA' (qB * qD) (hA' n hN hn hn2) sDPT
  -- from S_rank ∪ PT_L
  have sSRPT := stage_or P hn2 GoodPaper SRank PTL IsSilentConsensus (23 * n ^ 2 + (KB + VD))
    (qA' * (qB * qD)) sSR
    (stage_mono P hn2 GoodPaper PTL IsSilentConsensus (KB + VD) (23 * n ^ 2 + (KB + VD))
      (qB * qD) (qA' * (qB * qD)) sPT (Nat.le_add_left _ _)
      (mul_le_of_le_one_left zero_le hqA'1))
  -- from any good configuration
  have sAll := stage_compose P hn2 GoodPaper hG (fun _ => True) (fun C => SRank C ∨ PTL C)
    IsSilentConsensus (tOne n + 241 * n ^ 2) (23 * n ^ 2 + (KB + VD)) qA (qA' * (qB * qD))
    (hA n hN hn hn2) sSRPT X hX trivial
  -- window and probability
  have hW : tOne n + 241 * n ^ 2 + (23 * n ^ 2 + (KB + VD)) ≤ 1043 * n ^ 2 := by
    have h2t := two_tOne_le hN
    have hnn : 4 * n * (n - 1) ≤ 4 * n ^ 2 := by
      have : n - 1 ≤ n := Nat.sub_le n 1
      nlinarith
    simp only [KB, VD]
    omega
  have hq : (5 : ℝ≥0∞)⁻¹ ≤ qA * (qA' * (qB * qD)) := by
    simp only [qA, qA', qB, qD, qC, qE]
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    rw [show (5 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 5) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact hq.trans (sAll.trans (probHitBy_mono_time_of_le P hn2 X _ hW))

/-- **Kanaya Theorem 4, time part, from the six stage bounds.** -/
theorem kanayaThm4Time_of_stages (hA : StageA) (hA' : StageA') (h1 : Epoch1) (hC : StageC)
    (h2 : Epoch2) (hE : StageE) : KanayaThm4Time :=
  kanayaThm4Time_of_window (pemPaperWindow_of_stages hA hA' h1 hC h2 hE)

end Ripple.PopulationProtocol.SSEM
