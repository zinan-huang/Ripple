/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The two epochs of P3 from their stages

Epoch 1 (P3 Proposition 15, `PT_L → D`) is the composition of

| stage | P3 | from | to | window | probability |
|---|---|---|---|---|---|
| `StageB1` | Lemma 10 (B1) | `PTL` | `FDLHalf` | `t₁` | `0.998` |
| `StageB2` | Lemma 10 (B2) | `FDLHalf` | `FDOne` | `4 n (n - 1)` | `0.7499` |
| `StageB34` | Lemma 11 | `FDOne` | `RTheta 99` | `52 n²` | `0.753` |
| `StageB56` | Lemma 14 | `RTheta 99` | `Decided` | `23 n²` | `0.915` |

and Epoch 2 (P3 Proposition 20, `Z → Cons`) of the answer-tracking versions `StageB1Z`
(Lemma 19), `StageB2M`, `StageB34M`, `StageB56M`. `99 = T₀ - 209` with `T₀ = 308`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.WindowCompose

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped ENNReal

variable {n : ℕ}

/-! ### Classes -/

/-- Fully dormant: every agent Resetting with `resetcount = 0`. -/
def FD (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v, (C v).1.role = .Resetting ∧ (C v).1.resetcount = 0

/-- `FD_L^{½}`: fully dormant, some leader, every delay timer at least `⌊Dmax/2⌋ + 1`. -/
def FDLHalf (C : Config (AgentState n) Opinion n) : Prop :=
  FD C ∧ (∃ v, (C v).1.leader = .L) ∧ ∀ v, 16 * n + 1 ≤ (C v).1.delaytimer

/-- `FD_1`: fully dormant with exactly one leader. -/
def FDOne (C : Config (AgentState n) Opinion n) : Prop :=
  FD C ∧ ∃! v, (C v).1.leader = .L

/-- Every agent has the majority answer. -/
def AllMaj (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v, (C v).1.answer = majorityAnswer C

/-- Every Settled agent of non-median-type rank has the majority answer. -/
def AnsOK (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v, (C v).1.role = .Settled → ¬ IsMedType n (C v).1.rank.val →
    (C v).1.answer = majorityAnswer C

/-! ### Stage bounds -/

def StageB1 : Prop := StageBound PTL FDLHalf tOne 0.998
def StageB2 : Prop := StageBound FDLHalf FDOne (fun n => 4 * n * (n - 1)) 0.7499
def StageB34 : Prop := StageBound FDOne (RTheta 99) (fun n => 52 * n ^ 2) 0.753
def StageB56 : Prop := StageBound (RTheta 99) Decided (fun n => 23 * n ^ 2) 0.915

def StageB1Z : Prop := StageBound ZTwo (fun C => FDLHalf C ∧ AllMaj C) tOne 0.9978
def StageB2M : Prop :=
  StageBound (fun C => FDLHalf C ∧ AllMaj C) (fun C => FDOne C ∧ AllMaj C)
    (fun n => 4 * n * (n - 1)) 0.7499
def StageB34M : Prop :=
  StageBound (fun C => FDOne C ∧ AllMaj C) (fun C => RTheta 99 C ∧ AnsOK C)
    (fun n => 52 * n ^ 2) 0.753
def StageB56M : Prop :=
  StageBound (fun C => RTheta 99 C ∧ AnsOK C) IsConsensusConfig (fun n => 23 * n ^ 2) 0.915

/-! ### Composition of stage bounds -/

theorem StageBound.comp {A M B : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop}
    {W₁ W₂ : ℕ → ℕ} {q₁ q₂ : ℝ} (h₁ : StageBound A M W₁ q₁) (h₂ : StageBound M B W₂ q₂)
    (hq₁ : 0 ≤ q₁) : StageBound A B (fun n => W₁ n + W₂ n) (q₁ * q₂) := by
  intro n hN hn hn2 X hX hA
  rw [ENNReal.ofReal_mul hq₁]
  exact stage_compose (PEM40 n hn) hn2 GoodPaper (fun C hC i j => goodPaper_step hn2 C hC i j)
    A M B (W₁ n) (W₂ n) _ _ (h₁ n hN hn hn2) (h₂ n hN hn hn2) X hX hA

theorem StageBound.mono {A B : ∀ {n : ℕ}, Config (AgentState n) Opinion n → Prop}
    {W W' : ℕ → ℕ} {q q' : ℝ} (h : StageBound A B W q) (hW : ∀ n, 1608 ≤ n → W n ≤ W' n)
    (hq : q' ≤ q) : StageBound A B W' q' := by
  intro n hN hn hn2 X hX hA
  exact (ENNReal.ofReal_le_ofReal hq).trans ((h n hN hn hn2 X hX hA).trans
    (probHitBy_mono_time_of_le _ hn2 X _ (hW n hN)))

theorem epoch_window (n : ℕ) :
    tOne n + 4 * n * (n - 1) + 52 * n ^ 2 + 23 * n ^ 2 ≤ tOne n + 4 * n * (n - 1) + 75 * n ^ 2 := by
  omega

/-- **Epoch 1** (P3 Proposition 15) from its four stages. -/
theorem epoch1_of_stages (h1 : StageB1) (h2 : StageB2) (h3 : StageB34) (h4 : StageB56) :
    Epoch1 :=
  (((h1.comp h2 (by norm_num)).comp h3 (by norm_num)).comp h4 (by norm_num)).mono
    (fun n _ => epoch_window n) (by norm_num)

/-- **Epoch 2** (P3 Proposition 20) from its four stages. -/
theorem epoch2_of_stages (h1 : StageB1Z) (h2 : StageB2M) (h3 : StageB34M) (h4 : StageB56M) :
    Epoch2 :=
  (((h1.comp h2 (by norm_num)).comp h3 (by norm_num)).comp h4 (by norm_num)).mono
    (fun n _ => epoch_window n) (by norm_num)

end Ripple.PopulationProtocol.SSEM
