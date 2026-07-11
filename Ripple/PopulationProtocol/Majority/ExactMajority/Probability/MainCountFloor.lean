/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `MainCountFloor` — the `mainCount ≥ n/3` floor over Phase-1→5 (C5c-B).

The headline slot-5 carries `hMainFloor : (n:ℝ)/3 ≤ mainCount c5` as a POINTWISE fact at a synthetic
config.  The honest version is a CK composition: from the role-split-good event (Phase 0, where
`mainCount ≥ n/3` holds by `mainCount_lower_of_RoleSplitGood`), the Main pool stays above `n/3`
through the Phase-1→5 horizon except with probability `εMain`.

`mainFloor_tail_from_roleSplit_and_survival` composes the landed role-split tail (`εRole`) with the
Main-floor survival (`εMain`) via the verified `ChapmanKolmogorovChain.ck_bad_extend`.  The genuine
probabilistic content (`MainFloorSurvival`) is reduced to a single `MainFloorBennettAtom` whose
`hdrift`/`hbudget` (the one-sided Main-loss MGF/Bennett contraction) are demanded ONLY on the gate
`Gate ⊇ RoleSplitGood`, never on all configs.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Provenance: ChatGPT (family3 task f31c7abd) C5c draft, audited against `0f7a9c4`
(`mainCount_lower_of_RoleSplitGood`, `WindowConcentration.windowDrift_tail`, `ck_bad_extend` confirmed).
Reference: `AUDIT_HEADLINE_THEOREMS.md` (core C5c); Doty et al. (arXiv:2106.10201v2) §7.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ChapmanKolmogorovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration

namespace ExactMajority

namespace MainCountFloor

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-- The Main-count floor event: at least `n/3` Mains. -/
def MainFloor (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)

/-- The honest Main-floor survival atom: from a role-split-good config, the Main pool stays above
`n/3` through the `t15` horizon except with probability `εMain`.  Gated by `RoleSplitGood`, not a
universal over arbitrary configs. -/
def MainFloorSurvival (ηRole : ℝ) (n t15 : ℕ) (εMain : ℝ≥0∞) : Prop :=
  ∀ b : Config (AgentState L K),
    RoleSplitConcentration.RoleSplitGood (L := L) (K := K) ηRole n b →
    ((NonuniformMajority L K).transitionKernel ^ t15) b
      {c | ¬ MainFloor (L := L) (K := K) n c} ≤ εMain

/-- **The Main-floor tail by CK composition.**  Compose the landed role-split tail with the Main-floor
survival via `ck_bad_extend`: `(K^(tRole+t15)) c₀ {¬ MainFloor} ≤ εRole + εMain`. -/
theorem mainFloor_tail_from_roleSplit_and_survival
    {ηRole : ℝ} {n : ℕ} (tRole t15 : ℕ)
    (c₀ : Config (AgentState L K)) (εRole εMain : ℝ≥0∞)
    (hRole :
      ((NonuniformMajority L K).transitionKernel ^ tRole) c₀
        {b | ¬ RoleSplitConcentration.RoleSplitGood (L := L) (K := K) ηRole n b} ≤ εRole)
    (hSurvive : MainFloorSurvival (L := L) (K := K) ηRole n t15 εMain) :
    ((NonuniformMajority L K).transitionKernel ^ (tRole + t15)) c₀
      {c | ¬ MainFloor (L := L) (K := K) n c} ≤ εRole + εMain :=
  ChapmanKolmogorovChain.ck_bad_extend
    ((NonuniformMajority L K).transitionKernel)
    (fun b => RoleSplitConcentration.RoleSplitGood (L := L) (K := K) ηRole n b)
    (fun c => MainFloor (L := L) (K := K) n c)
    tRole t15 c₀ εRole εMain hRole hSurvive

/-- A Bennett-ready Main-floor survival atom.  The one-sided Main-loss potential `Ψ` contracts at rate
`r` on the gate `Gate` (which contains `RoleSplitGood`); failing the floor forces `Ψ` above `θ`. -/
structure MainFloorBennettAtom (ηRole : ℝ) (n t15 : ℕ) (εMain : ℝ≥0∞) where
  Gate : Config (AgentState L K) → Prop
  hGate_of_roleGood :
    ∀ b, RoleSplitConcentration.RoleSplitGood (L := L) (K := K) ηRole n b → Gate b
  hGate_abs :
    ∀ c c', Gate c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Gate c'
  Ψ : Config (AgentState L K) → ℝ≥0∞
  hΨ : Measurable Ψ
  r : ℝ≥0∞
  θ : ℝ≥0∞
  hθ : θ ≠ 0
  hθ_top : θ ≠ ⊤
  hlink : ∀ c, ¬ MainFloor (L := L) (K := K) n c → θ ≤ Ψ c
  hdrift :
    ∀ c, Gate c →
      ∫⁻ c', Ψ c' ∂((NonuniformMajority L K).transitionKernel c) ≤ r * Ψ c
  hbudget :
    ∀ b, RoleSplitConcentration.RoleSplitGood (L := L) (K := K) ηRole n b →
      r ^ t15 * Ψ b / θ ≤ εMain

/-- **Main-floor survival from a Bennett atom** (consumer of `windowDrift_tail`). -/
theorem mainFloor_survival_of_bennett
    {ηRole : ℝ} {n t15 : ℕ} {εMain : ℝ≥0∞}
    (A : MainFloorBennettAtom (L := L) (K := K) ηRole n t15 εMain) :
    MainFloorSurvival (L := L) (K := K) ηRole n t15 εMain := by
  intro b hbGood
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ t15) b
        {c | ¬ MainFloor (L := L) (K := K) n c}
        ≤ A.r ^ t15 * A.Ψ b / A.θ :=
    WindowConcentration.windowDrift_tail (NonuniformMajority L K)
      A.Ψ A.hΨ A.Gate A.hGate_abs A.r A.hdrift
      (fun c => MainFloor (L := L) (K := K) n c) A.θ A.hθ A.hθ_top A.hlink
      t15 b (A.hGate_of_roleGood b hbGood)
  exact htail.trans (A.hbudget b hbGood)

end MainCountFloor

end ExactMajority
