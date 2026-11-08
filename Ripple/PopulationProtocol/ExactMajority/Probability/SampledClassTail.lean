/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SampledClassTail — re-basing the Lemma 7.1 sampled-class concentration on the KILLED gate

`Phase035Endpoints.lean`'s slot-5 survey pins the `hConc` carry to provenance: the per-step MGF
drift (`Phase5Convergence.sampledClass_windowDrift_contraction`) and the threshold link
(`Phase5Convergence.sampledFloor_link`) are LANDED, but they do not assemble via
`WindowConcentration.windowDrift_PhaseConvergence` for two honest reasons recorded there:

* (a) the start window `Phase5AllWin` is NOT absorbing (a zero-counter clock pair advances both
  clocks to phase 6, leaving the window);
* (b) the MGF drift needs a rise-probability floor `hrfloor` (the static-class-profile rate
  bound) — the genuine Chernoff content.

## The superwindow re-base verdict (verified against the FROZEN rules)

The prompt's proposed fix — re-base on the *absorbing* superwindow `PhaseGE5Win` and argue the
sampled-class count is FROZEN on the phase-≥6 part — is **FALSE for the rise/contraction
direction**, verified against the actual transition rules:

* `sampledReserveClass i a := a.role = Role.reserve ∧ a.hour.val = i` (`Phase5Convergence:278`).
* `Phase6Transition` (`Transition.lean:1209`) routes a Reserve+Main pair through `doSplit`
  (`Transition.lean:1154`), whose FIRST output sets `role := .main` (`Transition.lean:1160`).
  So a class-`i` Reserve that participates in a phase-6 split FLIPS role `reserve → main` and is
  REMOVED from `sampledReserveClassU i` — the count is non-increasing on phase 6 and STRICTLY
  decreases on a split.  Hence on `PhaseGE5Win` the deficit potential `Φ = exp(−s·N)` can RISE,
  breaking the contraction `∫Φ dK ≤ ρ·Φ`.  This is exactly the obstruction the `Phase5Convergence`
  campaign note (lines 1041-1046) already records ("Phase-6 `doSplit` converts a class-`i` Reserve
  to a Main, consuming it"); the superwindow is absorbing but NOT a drift carrier.

So the superwindow does not give the drift "for free".  The HONEST re-base that removes the
absorption obstruction WITHOUT a false freeze claim is the **killed-affine engine**
(`GatedDrift.real_window_killed_affine`, `KilledAffineTail.lean`): the gate `G := Phase5AllWin n`
carries the drift (where it genuinely holds), the killed kernel `killK_now K G` absorbs
STRUCTURALLY (cemetery `killΦ = 0`), and the real chain is dominated by `killed-tail + escape`.

## What this file LANDS (0 sorry / 0 axiom / no native_decide)

* `sampledClassPot` — the deficit potential `Φ(c) = ofReal(exp(−s·sampledReserveClassU i c))`.
* `sampledClassDrift_on_gate` — the per-step MULTIPLICATIVE drift `∫Φ dK ≤ ρ·Φ` (immigration
  `b = 0`) on the gate `Phase5AllWin n`, threading the rate floor `hrfloor` as the carried
  Chernoff hypothesis (blocker (b)).  A thin lift of the landed
  `sampledClass_windowDrift_contraction`.
* `sampledClass_killed_tail` — the **pure killed tail** (NO escape, NO exit bridge): the killed
  walk's floor-failure mass decays as `ρᵗ·Φ(c₀)/θ` with `θ = exp(−s·K₀)`.  This is the cleanest
  decaying object, landed unconditionally given the rate floor — it makes the absorption obstruction
  (blocker (a)) DISAPPEAR.
* `sampledClass_real_window` — the **real-chain** sampled-class floor tail:
  `(Kᵗ) c₀ {¬sampledFloor i K₀} ≤ ρᵗ·Φ(c₀)/θ + ∑_{τ<t} (Kᵀ) c₀ {θ' ≤ Φ}`, via
  `real_window_killed_affine`.  The escape prefix is the genuine Phase-5/Phase-6 *separation*
  (paper footnote 11 / Lemma 5.2): leaving `Phase5AllWin` is the clock-timing event, NOT a
  self-referential `sampledReserveClassU`-threshold, so the exit bridge is CARRIED as an explicit
  hypothesis, not manufactured.
* `hConcDemand_of_real_window` — wires `sampledClass_real_window` into the exact
  `Phase035Endpoints.hConcDemand` shape the slot-5 carry meets, given a uniform per-`τ` escape bound.

## How much of `hConc` this closes

The absorption obstruction (blocker (a)) is RESOLVED structurally by the killed kernel — the pure
killed tail `sampledClass_killed_tail` is fully landed (axiom-clean) from the rate floor alone.
The two GENUINELY-probabilistic residuals that remain pinned are exactly the survey's named atoms:
(b) the rate floor `hrfloor` (the in-house Chernoff rise-probability content) and the clock-timing
escape (the Phase-5/Phase-6 separation).  Neither is a deterministic atom; both are carried as
explicit, named hypotheses with file:line provenance — pinned, not hidden.

This file is APPEND-ONLY and edits NO existing file.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.KilledAffineTail
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase035Endpoints

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SampledClassTail

open Phase5Convergence ReserveSampling GatedDrift

variable {L K : ℕ}

/-! ## Part 1 — the deficit potential and the gate. -/

/-- The sampled-class **deficit potential** at level `i`, rate `s`:
`Φ(c) = ofReal(exp(−s·sampledReserveClassU i c))`.  Failing the sampled-class floor
(`sampledReserveClassU i < K₀`) forces `Φ ≥ θ = ofReal(exp(−s·K₀))` (the `sampledFloor_link`). -/
noncomputable def sampledClassPot (i : Fin (L + 1)) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(s * (sampledReserveClassU (L := L) (K := K) i c : ℝ))))

/-- The killed-engine **gate** for the sampled-class drift: the Phase-5 structural window
`Phase5AllWin n` (where the per-step drift `sampledClass_windowDrift_contraction` genuinely
holds, by support-monotonicity of `sampledReserveClassU i`).  The killed kernel absorbs the
`Phase5AllWin` EXIT structurally. -/
def sampledClassGate (n : ℕ) : Set (Config (AgentState L K)) :=
  {c | Phase5AllWin (L := L) (K := K) n c}

/-! ## Part 2 — the per-step multiplicative drift on the gate (rate floor carried). -/

/-- **The sampled-class drift on the gate** (multiplicative, `b = 0`).  On the gate
`Phase5AllWin n`, with the carried rise-probability floor `hrfloor` (the Chernoff rate bound,
blocker (b)), the deficit potential `Φ = sampledClassPot i s` contracts at rate
`ρ = ofReal(1 − r(1 − e^{−s}))`:
`∫Φ dK(c) ≤ ρ·Φ(c) + 0`.  A thin lift of the landed
`Phase5Convergence.sampledClass_windowDrift_contraction` into the affine-engine `hdrift_G`
shape with `b = 0`. -/
theorem sampledClassDrift_on_gate (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hrfloor : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      ENNReal.ofReal r ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | sampledReserveClassU (L := L) (K := K) i c + 1
            ≤ sampledReserveClassU (L := L) (K := K) i c'})
    (x : Config (AgentState L K)) (hx : x ∈ sampledClassGate (L := L) (K := K) n) :
    ∫⁻ y, sampledClassPot (L := L) (K := K) i s y
        ∂((NonuniformMajority L K).transitionKernel x)
      ≤ ENNReal.ofReal (1 - r * (1 - Real.exp (-s))) * sampledClassPot (L := L) (K := K) i s x
        + 0 := by
  rw [add_zero]
  exact sampledClass_windowDrift_contraction (L := L) (K := K) σ i hiL n hn s hs r hr0 hr1 x hx
    (hrfloor x hx)

/-! ## Part 3 — the pure killed tail (no escape, no exit bridge). -/

/-- **The pure killed sampled-class tail** (the cleanest decaying object; blocker (a) removed).
The KILLED walk's floor-failure mass — trajectories that STAY in the gate `Phase5AllWin n` and
end with `sampledReserveClassU i < K₀`, i.e. `θ ≤ killΦ Φ` at `θ = exp(−s·K₀)` — is bounded by
the clean geometric budget `ρᵗ·Φ(c₀)/θ`, with `ρ = ofReal(1 − r(1 − e^{−s}))`.  This is
`GatedDrift.killed_now_affine_tail` at the sampled-class instantiation (`b = 0`): NO `1 ≤ ρ`
requirement (it DECAYS when `ρ < 1`), and NO absorbing-`Q` hypothesis — the killed kernel absorbs
structurally.  The only carried content is the rate floor `hrfloor` (blocker (b)). -/
theorem sampledClass_killed_tail (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hrfloor : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      ENNReal.ofReal r ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | sampledReserveClassU (L := L) (K := K) i c + 1
            ≤ sampledReserveClassU (L := L) (K := K) i c'})
    (K₀ t : ℕ) (c₀ : Config (AgentState L K)) :
    (killK_now (NonuniformMajority L K).transitionKernel
        (sampledClassGate (L := L) (K := K) n) ^ t) (some c₀)
        {o | ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
          ≤ killΦ (sampledClassPot (L := L) (K := K) i s) o}
      ≤ ENNReal.ofReal (1 - r * (1 - Real.exp (-s))) ^ t
          * sampledClassPot (L := L) (K := K) i s c₀
        / ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) := by
  have hdrift := sampledClassDrift_on_gate (L := L) (K := K) σ i hiL n hn s hs r hr0 hr1 hrfloor
  have h := killed_now_affine_tail
    (K := (NonuniformMajority L K).transitionKernel)
    (G := sampledClassGate (L := L) (K := K) n)
    (sampledClassPot (L := L) (K := K) i s)
    (ENNReal.ofReal (1 - r * (1 - Real.exp (-s)))) 0
    hdrift t c₀ (ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))))
    (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _)
    ENNReal.ofReal_ne_top
  -- the `b = 0` summand collapses.
  simpa using h

/-! ## Part 4 — the real-chain window (killed tail + the carried clock-separation escape). -/

/-- **The real-chain sampled-class floor tail.**  Via `GatedDrift.real_window_killed_affine`:
the REAL chain's `t`-step sampled-class floor-failure mass is bounded by the killed tail PLUS the
escape prefix:
`(Kᵗ) c₀ {¬sampledFloor i K₀} ≤ ρᵗ·Φ(c₀)/θ + ∑_{τ<t} (Kᵀ) c₀ {θ' ≤ Φ}`,
with `θ = θ' = exp(−s·K₀)`.

The escape prefix is the genuine **Phase-5/Phase-6 separation** (paper footnote 11 / Lemma 5.2):
the exit bridge `hbridge : ∀ c ∈ gate, Φ c < θ' → K c gateᶜ = 0` says "leaving `Phase5AllWin` is
impossible while the sampled-class count is below `K₀`".  Leaving `Phase5AllWin` is the CLOCK-timing
event (a zero-counter pair advances to phase 6), which is NOT a `sampledReserveClassU`-threshold
event, so `hbridge` is CARRIED as an explicit hypothesis — the precise clock-separation residual,
pinned not hidden. -/
theorem sampledClass_real_window (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hrfloor : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      ENNReal.ofReal r ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | sampledReserveClassU (L := L) (K := K) i c + 1
            ≤ sampledReserveClassU (L := L) (K := K) i c'})
    (K₀ : ℕ)
    (hbridge : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      sampledClassPot (L := L) (K := K) i s c
          < ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) →
      (NonuniformMajority L K).transitionKernel c
        (sampledClassGate (L := L) (K := K) n)ᶜ = 0)
    (t : ℕ) (c₀ : Config (AgentState L K)) (hc₀ : Phase5AllWin (L := L) (K := K) n c₀) :
    ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ sampledFloor (L := L) (K := K) i K₀ c}
      ≤ (ENNReal.ofReal (1 - r * (1 - Real.exp (-s))) ^ t
            * sampledClassPot (L := L) (K := K) i s c₀ + 0)
          / ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
        + ∑ τ ∈ Finset.range t,
            ((NonuniformMajority L K).transitionKernel ^ τ) c₀
              {c | ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
                ≤ sampledClassPot (L := L) (K := K) i s c} := by
  classical
  set θ := ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) with hθ
  -- the threshold link: ¬sampledFloor ⟹ θ ≤ Φ.
  have hlink : {c : Config (AgentState L K) | ¬ sampledFloor (L := L) (K := K) i K₀ c}
      ⊆ {c | θ ≤ sampledClassPot (L := L) (K := K) i s c} := by
    intro c hc
    exact sampledFloor_link (L := L) (K := K) i K₀ s hs c hc
  refine le_trans (measure_mono hlink) ?_
  -- the affine drift on the gate (b = 0).
  have hdrift := sampledClassDrift_on_gate (L := L) (K := K) σ i hiL n hn s hs r hr0 hr1 hrfloor
  have h := real_window_killed_affine
    (K := (NonuniformMajority L K).transitionKernel)
    (G := sampledClassGate (L := L) (K := K) n)
    (sampledClassPot (L := L) (K := K) i s)
    (ENNReal.ofReal (1 - r * (1 - Real.exp (-s)))) 0
    hdrift θ θ
    (by simp only [hθ, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _)
    ENNReal.ofReal_ne_top hbridge t c₀ hc₀
  -- collapse the `0 * ∑` immigration term in the engine's numerator to `+ 0`.
  simpa only [zero_mul] using h

/-! ## Part 5 — wiring into the `Phase035Endpoints.hConcDemand` shape. -/

/-- **`hConcDemand` discharged from the real window** (given a uniform escape bound).  This
produces the exact `Phase035Endpoints.hConcDemand n i K₀ M₀ t εConc c₀` shape — the sampled-class
floor tail the slot-5 carry meets — from:
* the rate floor `hrfloor` (blocker (b), the Chernoff content);
* the clock-separation exit bridge `hbridge` (the Phase-5/Phase-6 escape);
* a uniform per-`τ` escape bound `hβ` (each prefix threshold mass ≤ `β`);
* the single arithmetic fit `hε` that the killed budget + `t·β` lands under `εConc`.

The genuinely-probabilistic residuals are exactly `hrfloor`, `hbridge`, and the per-`τ` escape
bound — the survey's named atoms, now consumed by an explicit assembler instead of an opaque
carry. -/
theorem hConcDemand_of_real_window (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hrfloor : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      ENNReal.ofReal r ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {c' | sampledReserveClassU (L := L) (K := K) i c + 1
            ≤ sampledReserveClassU (L := L) (K := K) i c'})
    (K₀ M₀ t : ℕ) (εConc : ℝ≥0)
    (hbridge : ∀ c, Phase5AllWin (L := L) (K := K) n c →
      sampledClassPot (L := L) (K := K) i s c
          < ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ)))) →
      (NonuniformMajority L K).transitionKernel c
        (sampledClassGate (L := L) (K := K) n)ᶜ = 0)
    (β : ℝ≥0∞)
    (hβ : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ → ∀ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ τ) c₀
        {c | ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
          ≤ sampledClassPot (L := L) (K := K) i s c} ≤ β)
    (hε : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ →
      (ENNReal.ofReal (1 - r * (1 - Real.exp (-s))) ^ t
            * sampledClassPot (L := L) (K := K) i s c₀ + 0)
          / ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
        + (t : ℝ≥0∞) * β ≤ (εConc : ℝ≥0∞)) :
    ∀ c₀, Phase035Endpoints.hConcDemand (L := L) (K := K) n i K₀ M₀ t εConc c₀ := by
  intro c₀
  unfold Phase035Endpoints.hConcDemand
  intro hwin _hbud
  refine le_trans (sampledClass_real_window (L := L) (K := K) σ i hiL n hn s hs r hr0 hr1
    hrfloor K₀ hbridge t c₀ hwin) ?_
  refine le_trans (add_le_add le_rfl ?_) (hε c₀ hwin)
  -- collapse the escape prefix sum by the uniform bound.
  refine le_trans (Finset.sum_le_sum (hβ c₀ hwin)) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end SampledClassTail

end Ripple.PopulationProtocol.ExactMajority
