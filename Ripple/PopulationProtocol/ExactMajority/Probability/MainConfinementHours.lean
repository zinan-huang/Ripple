/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `MainConfinementHours` — discharge Theorem 6.2's `hHourTail` from per-hour gated MGF atoms (C5c-A).

`MainExponentConfinement.theorem6_2_main_confinement_whp` carries a GLOBAL tail
`hHourTail : (K^phase3to5Time) c₀ {¬ MainProfileConfinedToUseful c} ≤ η` and just reads off the
0.92·|M| confinement.  This file produces that `hHourTail` FAITHFULLY from the per-hour Main-profile
squaring: a sequence of hour-good gates `Good 0 → … → Good H`, each transition a single squaring
contraction (`main_profile_hour_squaring` = `WindowConcentration.windowDrift_tail`) on the hour-local
gate `Q`, composed by the verified finite CK union `ChapmanKolmogorovChain.ck_chain_bad_bound_lt`.

The genuine probabilistic content is isolated in the `MainHourSquaringHypotheses` fields `hdrift` (the
one-step MGF/Bennett contraction on the gate `Q`) and `hbudget` (the optimized arithmetic) — demanded
ONLY on `Q`, never on arbitrary configs.  `Phase5AllWin` is NOT used as an invariant (it is not
kernel-closed, `Phase5ClosureFalse`); the gates `Good i` / `Q` are the genuine hour windows.

NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Checked against `0f7a9c4`
(`main_profile_hour_squaring` field shapes confirmed; the CK iteration extracted to the verified
`ChapmanKolmogorovChain.ck_chain_bad_bound_lt`).
Reference: `AUDIT_HEADLINE_THEOREMS.md` (core C5c); Doty et al. (arXiv:2106.10201v2) Theorem 6.2.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ChapmanKolmogorovChain
import Ripple.PopulationProtocol.ExactMajority.Probability.MainExponentConfinement

namespace Ripple.PopulationProtocol.ExactMajority

namespace MainExponentConfinement

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-- **One genuine per-hour Main-profile squaring atom.**  `Q` is the hour-local good gate (not all
configurations); `hdrift` is the MGF/Bennett one-step contraction ON `Q`; `hbudget` is the optimized
Bennett arithmetic.  All genuinely-probabilistic content lives in these two fields, gated by `Q`. -/
structure MainHourSquaringHypotheses
    (hourLen : ℕ)
    (Good GoodNext : Config (AgentState L K) → Prop)
    (ηhour : ℝ≥0∞) where
  Φ : Config (AgentState L K) → ℝ≥0∞
  hΦ : Measurable Φ
  Q : Config (AgentState L K) → Prop
  hQ_abs :
    ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c'
  r : ℝ≥0∞
  Post : Config (AgentState L K) → Prop
  θ : ℝ≥0∞
  hθ : θ ≠ 0
  hθ_top : θ ≠ ⊤
  /-- The current hour good event lies inside the gate on which drift is genuine. -/
  hQ_of_good : ∀ c, Good c → Q c
  /-- If the hour `Post` holds, the next-hour good event holds. -/
  hgood_next_of_post : ∀ c, Post c → GoodNext c
  /-- Failing the postcondition forces the potential above the threshold. -/
  hlink : ∀ c, ¬ Post c → θ ≤ Φ c
  /-- The Bennett/MGF one-step contraction on the genuine gate `Q`. -/
  hdrift :
    ∀ c, Q c →
      ∫⁻ c', Φ c' ∂((NonuniformMajority L K).transitionKernel c) ≤ r * Φ c
  /-- The optimized Bennett arithmetic for this hour. -/
  hbudget :
    ∀ c, Good c → r ^ hourLen * Φ c / θ ≤ ηhour

/-- **Per-hour tail from a squaring atom.**  From an hour-good start, the `hourLen`-block misses the
next-hour good event with probability `≤ ηhour`.  Pure consumer of `main_profile_hour_squaring`. -/
theorem hour_tail_of_squaring
    {hourLen : ℕ} {Good GoodNext : Config (AgentState L K) → Prop} {ηhour : ℝ≥0∞}
    (A : MainHourSquaringHypotheses (L := L) (K := K) hourLen Good GoodNext ηhour)
    (c : Config (AgentState L K)) (hcGood : Good c) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) c
        {x | ¬ GoodNext x} ≤ ηhour := by
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ hourLen) c {x | ¬ A.Post x}
        ≤ A.r ^ hourLen * A.Φ c / A.θ :=
    main_profile_hour_squaring (L := L) (K := K)
      A.Φ A.hΦ A.Q A.hQ_abs A.r A.hdrift A.Post A.θ A.hθ A.hθ_top A.hlink
      hourLen c (A.hQ_of_good c hcGood)
  have hsub : {x : Config (AgentState L K) | ¬ GoodNext x} ⊆ {x | ¬ A.Post x} :=
    fun x hx hpost => hx (A.hgood_next_of_post x hpost)
  exact (measure_mono hsub).trans (htail.trans (A.hbudget c hcGood))

/-- **The all-hours confinement tail — the discharged `hHourTail`.**  Iterating the per-hour squaring
atoms over the `H` Phase-3→5 hours via the verified finite CK union yields the global confinement tail
`(K^(∑ hourLen)) c₀ {¬ MainProfileConfinedToUseful c} ≤ η`, the exact tail
`theorem6_2_main_confinement_whp` carries.  `hReadout` is the deterministic collapse→confinement
readout after all hours. -/
theorem main_confinement_tail_of_hour_squaring
    (H : ℕ) (hourLen : ℕ → ℕ)
    (Good : ℕ → Config (AgentState L K) → Prop) (ηhour : ℕ → ℝ≥0∞)
    (atoms : ∀ i, i < H →
      MainHourSquaringHypotheses (L := L) (K := K) (hourLen i) (Good i) (Good (i + 1)) (ηhour i))
    (c₀ : Config (AgentState L K)) (hGood0 : Good 0 c₀)
    (hReadout : ∀ c, Good H c → MainProfileConfinedToUseful (L := L) (K := K) c)
    (η : ℝ≥0∞) (hBudget : (∑ i ∈ Finset.range H, ηhour i) ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ (ChapmanKolmogorovChain.hourPrefix hourLen H)) c₀
      {c | ¬ MainProfileConfinedToUseful (L := L) (K := K) c} ≤ η := by
  have hchain :
      ((NonuniformMajority L K).transitionKernel ^ (ChapmanKolmogorovChain.hourPrefix hourLen H)) c₀
        {x | ¬ Good H x} ≤ ∑ i ∈ Finset.range H, ηhour i :=
    ChapmanKolmogorovChain.ck_chain_bad_bound_lt
      ((NonuniformMajority L K).transitionKernel) Good hourLen ηhour c₀ hGood0 H
      (fun i hi y hy => hour_tail_of_squaring (atoms i hi) y hy)
  have hsub :
      {c : Config (AgentState L K) | ¬ MainProfileConfinedToUseful (L := L) (K := K) c}
        ⊆ {c | ¬ Good H c} :=
    fun c hc hGood => hc (hReadout c hGood)
  exact (measure_mono hsub).trans (hchain.trans hBudget)

/-- **End-to-end Brick A from per-hour atoms.**  The headline Theorem-6.2 confinement conclusion
(`¬(0.92·|M| ≤ #usefulMains)` fails w.p. `≤ η`) produced directly from the per-hour squaring atoms,
chaining `main_confinement_tail_of_hour_squaring` into the existing `theorem6_2_main_confinement_whp`.
This is the discharged form of the previously-carried `hHourTail`. -/
theorem theorem6_2_main_confinement_whp_from_hours
    (n H : ℕ) (hourLen : ℕ → ℕ)
    (Good : ℕ → Config (AgentState L K) → Prop) (ηhour : ℕ → ℝ≥0∞)
    (atoms : ∀ i, i < H →
      MainHourSquaringHypotheses (L := L) (K := K) (hourLen i) (Good i) (Good (i + 1)) (ηhour i))
    (phase3to5Time : ℕ) (hTime : phase3to5Time = ChapmanKolmogorovChain.hourPrefix hourLen H)
    (c₀ : Config (AgentState L K)) (hGood0 : Good 0 c₀)
    (hReadout : ∀ c, Good H c → MainProfileConfinedToUseful (L := L) (K := K) c)
    (η : ℝ≥0∞) (hBudget : (∑ i ∈ Finset.range H, ηhour i) ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬
        ((0.92 : ℝ) *
          (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
          ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ))}
      ≤ η := by
  subst hTime
  exact theorem6_2_main_confinement_whp n η (ChapmanKolmogorovChain.hourPrefix hourLen H) c₀
    (main_confinement_tail_of_hour_squaring H hourLen Good ηhour atoms c₀ hGood0 hReadout η hBudget)

end MainExponentConfinement

end Ripple.PopulationProtocol.ExactMajority
