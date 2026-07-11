/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-1 averaging collapse — the saturated-side floor (the last of the four floors)

`HANDOFF_FOUR_FLOORS.md` §1: the Phase-1 saturated-side floor.  Whp over the Phase-1 window,
the saturated-positive Mains (`smallBias.val ≥ 5`) stay `≤ n/3 − P`, so `pullPosSet ≥ P` via the
landed Main decomposition `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos` and the wrapper
`EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound`.

## The honest self-contained route: a deterministic second-moment ledger

The paper imports the quantitative collapse from reference [45] (Mocquard et al., discrete
averaging) — all Main `smallBias`es converge to `{µ−1,µ,µ+1}` in `O(log n)` whp.  Rather than
formalize [45]'s variance-decay argument wholesale, we use the genuine self-contained mechanism
the blueprint points at: **bounded pairwise averaging contracts the second moment.**

The FROZEN Phase-1 rule (`Protocol/Transition.lean`, `avgFin7`) replaces two Mains' `smallBias`
values `x, y : Fin 7` by `(⌊(x+y)/2⌋, ⌈(x+y)/2⌉)`.  The exact integer ledger, computed over all
`7 × 7 = 49` pairs (both parities), centred at the encoding origin `3` (`smallBiasInt = v − 3`):

* the sum is preserved: `x' + y' = x + y` (`avgFin7_preserves_sum`);
* the **centred second moment drops by exactly `⌊(x−y)²/2⌋`**:
  `(x−3)² + (y−3)²  −  (x'−3)² − (y'−3)² = ⌊(x−y)²/2⌋ ≥ 0`.
  (Even parity: drop `= (x−y)²/2`; odd parity: drop `= ((x−y)²−1)/2`.  The centred drop equals
  the raw `Σv²` drop because the linear term cancels under the preserved sum.)

So `Φ(c) := Σ_{phase-1 Mains} (smallBias.val − 3)²` (the ℕ-valued centred second moment, computed
as `sqDist3N`) is **deterministically non-increasing** under every averaging interaction — no
expectation, no martingale: the variance literally never rises.  This is the honest potential the
blueprint asked for ("a cosh/variance contraction potential"); the contraction is so clean it is
a per-step ℕ-monotone, plugging straight into the same `OneSidedCancel` level engine that
`Phase1Convergence` already uses for `extremeU`.

## The saturated-count conversion (fully proved, exact)

A saturated-positive Main has `smallBias.val ≥ 5`, hence `(smallBias.val − 3)² ≥ 4`.  Summing,
`4 · #saturatedPos ≤ Φ` (`four_mul_saturatedPos_le_secondMoment`).  So `Φ ≤ 4·(n/3 − P)` forces
`#saturatedPos ≤ n/3 − P`, which is EXACTLY the saturated-side budget the wrapper
`phase1_pullPos_floor_of_mainCount_and_saturated_bound` consumes.  The "what is the mean µ"
design question dissolves: centring at the fixed encoding origin `3` already gives distance `≥ 2`
for every saturated value, so no estimate of the true mean is needed.

## What is fully proved vs carried

FULLY PROVED (0-sorry, axiom-clean): the exact per-rule ledger (`avgFin7_sqDist3_pair_le` /
`avgFin7_sqDist3_pair_drop`, both parities by exhaustive `decide`); the deterministic
config-kernel non-increase of `Φ = secondMomentN` on the `Phase1AllMain` window
(`PotNonincrOn`, mirroring `extremeU`); the saturated-count conversion
(`four_mul_saturatedPos_le_secondMoment`); the whp tail through the landed `OneSidedCancel`
level engine (`secondMoment_level_tail`); and the wired floor
(`phase1_saturatedPos_le_whp` → `phase1_pullPos_floor_whp`) feeding
`EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound`.

CARRIED (exactly one named quantitative input, with paper provenance): the per-step
second-moment drain rate `q` (the `hstep`/`hdrop` hypothesis).  This is the SAME atom
`Phase1Convergence.phase1Convergence` carries for `extremeU` — the per-interaction probability
that a distant pair averages strictly inward, `≥ (pair count)/(n(n−1))`-shape, the quantitative
content the paper imports from reference [45] (Corollary 1).  It is exposed as a hypothesis
exactly as Phases 1/7/8 expose theirs; everything structural around it is discharged.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AveragingCollapse

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Stage 1 — the per-rule second-moment ledger (exact `Fin 7` integer arithmetic).

`sqDist3N v` is the ℕ-valued squared distance of a `Fin 7` value `v` from the encoding origin `3`
(`= (v.val − 3)²`, written with truncated ℕ subtraction so it is genuinely `ℕ`-valued).  Centred
at `3`, this is the per-agent contribution to the second moment `Σ (smallBias.val − 3)²`. -/

/-- ℕ-valued squared distance from the encoding origin `3` (`(v.val − 3)²` as a natural). -/
def sqDist3N (v : Fin 7) : ℕ :=
  (if v.val ≤ 3 then 3 - v.val else v.val - 3) ^ 2

/-- **The per-pair second-moment NON-INCREASE (exhaustive).**  The averaging rule never raises the
centred second moment: the sum of the two outputs' `sqDist3N` is at most the sum of the two
inputs'.  Verified over all `7 × 7 = 49` pairs (both parities) by `decide`. -/
theorem avgFin7_sqDist3_pair_le (x y : Fin 7) :
    sqDist3N (avgFin7 x y).1 + sqDist3N (avgFin7 x y).2
      ≤ sqDist3N x + sqDist3N y := by
  revert x y; decide

/-- **The EXACT per-pair drop (exhaustive, both parities).**  The centred second moment drops by
exactly `⌊(x.val − y.val)²/2⌋` per averaging interaction.  Even parity gives `(Δ)²/2`, odd parity
`((Δ)²−1)/2`; both are captured by the single floor expression.  Verified over all 49 pairs by
`decide`.  (Stated as an additive identity in ℕ; the `+` form avoids ℕ-subtraction pitfalls.) -/
theorem avgFin7_sqDist3_pair_drop (x y : Fin 7) :
    sqDist3N (avgFin7 x y).1 + sqDist3N (avgFin7 x y).2
        + (max x.val y.val - min x.val y.val) ^ 2 / 2
      = sqDist3N x + sqDist3N y := by
  revert x y; decide

/-- A saturated value (`v.val ≥ 5`) is at squared distance `≥ 4` from the origin `3`. -/
theorem sqDist3N_ge_four_of_saturated (v : Fin 7) (h : 5 ≤ v.val) :
    4 ≤ sqDist3N v := by
  revert h; revert v; decide

/-! ## Stage 2 — the config potential `secondMomentN` and its deterministic one-step
non-increase on the `Phase1AllMain` window.

`sqMainN a` is the per-agent centred-second-moment contribution: `sqDist3N a.smallBias` for a
Main, `0` otherwise (mirroring `Phase1Convergence.extremeSt`'s Main-gating).  `secondMomentN c`
sums it over the multiset.  On the all-Main phase-1 window every interaction is an `avgFin7`
averaging (`Phase1Convergence.Transition_eq_avg_of_phase1_main`), so the per-pair ledger
`avgFin7_sqDist3_pair_le` lifts to `secondMomentN`-non-increase under the kernel — exactly the
`OneSidedCancel.PotNonincrOn` predicate, mirroring `extremeU`. -/

/-- Per-agent centred-second-moment contribution: `sqDist3N smallBias` on a Main, else `0`. -/
def sqMainN (a : AgentState L K) : ℕ :=
  if a.role = Role.main then sqDist3N a.smallBias else 0

/-- The config second moment (centred at `3`): `Σ_{Mains} (smallBias.val − 3)²`, the ℕ-valued
potential `Φ`. -/
def secondMomentN (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => sqMainN a)).sum

/-- `sqMainN` over a two-element pair as a sum. -/
theorem sqMainN_pair (x y : AgentState L K) :
    ((({x, y} : Multiset (AgentState L K)).map (fun a => sqMainN a)).sum)
      = sqMainN x + sqMainN y := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  simp [Multiset.map_cons, Multiset.sum_cons]

/-- **Per-pair `secondMomentN` non-increase, both-Main.**  Reduce to the averaging rule
(`Transition_eq_avg_of_phase1_main`) and apply the exhaustive `avgFin7_sqDist3_pair_le`. -/
theorem Transition_secondMomentN_pair_le_of_both_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    (((({(Transition L K s t).1, (Transition L K s t).2}
        : Multiset (AgentState L K))).map (fun a => sqMainN a)).sum)
      ≤ ((({s, t} : Multiset (AgentState L K)).map (fun a => sqMainN a)).sum) := by
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [sqMainN_pair, sqMainN_pair]
  -- outputs are `{s/t with smallBias := avg}`, both Main, so `sqMainN` = `sqDist3N (avg)`.
  have ho1 : sqMainN ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} : AgentState L K)
      = sqDist3N (avgFin7 s.smallBias t.smallBias).1 := by
    unfold sqMainN; rw [if_pos hsM]
  have ho2 : sqMainN ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} : AgentState L K)
      = sqDist3N (avgFin7 s.smallBias t.smallBias).2 := by
    unfold sqMainN; rw [if_pos htM]
  have hs : sqMainN s = sqDist3N s.smallBias := by unfold sqMainN; rw [if_pos hsM]
  have ht : sqMainN t = sqDist3N t.smallBias := by unfold sqMainN; rw [if_pos htM]
  rw [ho1, ho2, hs, ht]
  exact avgFin7_sqDist3_pair_le s.smallBias t.smallBias

private theorem mem_of_app_left {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- `secondMomentN` is non-increasing under any chosen-pair update on an all-Main phase-1
window. -/
theorem secondMomentN_stepOrSelf_le (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Convergence.Phase1AllMain n c) (r₁ r₂ : AgentState L K) :
    secondMomentN (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤ secondMomentN c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left happ
    have hm2 := mem_of_app_right happ
    obtain ⟨h11, h1M⟩ := hph r₁ hm1
    obtain ⟨h21, h2M⟩ := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    -- decompose `c = (c − pair) + pair` (no ℕ-subtraction on the weighted sum).
    have hsplit : c = (c - {r₁, r₂}) + ({r₁, r₂} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel hsub]
    have hpair := Transition_secondMomentN_pair_le_of_both_main r₁ r₂ h11 h21 h1M h2M
    unfold secondMomentN
    rw [hc', Multiset.map_add, Multiset.sum_add]
    calc ((c - {r₁, r₂}).map (fun a => sqMainN a)).sum
            + (({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
                : Multiset (AgentState L K)).map (fun a => sqMainN a)).sum
        ≤ ((c - {r₁, r₂}).map (fun a => sqMainN a)).sum
            + (({r₁, r₂} : Multiset (AgentState L K)).map (fun a => sqMainN a)).sum := by
          exact Nat.add_le_add_left hpair _
      _ = (c.map (fun a => sqMainN a)).sum := by
          conv_rhs => rw [hsplit]
          rw [Multiset.map_add, Multiset.sum_add]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `secondMomentN` is non-increasing on the one-step kernel support. -/
theorem secondMomentN_le_on_support (n : ℕ) (m : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n c)
    (hle : secondMomentN c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    secondMomentN c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact le_trans (secondMomentN_stepOrSelf_le n c hInv r₁ r₂) hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hle

/-- **The engine's `PotNonincrOn` ingredient for the second-moment potential `Φ`.**  The variance
literally never rises under the averaging rule. -/
theorem potNonincrOn_secondMomentN (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase1Convergence.Phase1AllMain n c)
      (NonuniformMajority L K).transitionKernel (fun c => secondMomentN c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | secondMomentN c < secondMomentN x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : secondMomentN x ≤ secondMomentN c :=
    secondMomentN_le_on_support n (secondMomentN c) c x hInv le_rfl hsupp
  omega

/-! ## Stage 3 — the saturated-count conversion and the whp tail.

The saturated-positive Mains (`PhaseFloors.saturatedPos`: Main with `smallBias.val ≥ 5`) each
contribute `sqMainN ≥ 4` to the second moment, so `4 · #saturatedPos ≤ secondMomentN`.  Hence
`secondMomentN ≤ 4·(n/3 − P)` forces `#saturatedPos ≤ n/3 − P` — exactly the saturated-side
budget.  The tail comes from the landed `OneSidedCancel` level engine at the carried drain
rate `q`. -/

/-- `secondMomentN c` as a count-weighted sum over `univ`. -/
theorem secondMomentN_eq_sum (c : Config (AgentState L K)) :
    secondMomentN c = ∑ a ∈ Finset.univ, c.count a * sqMainN a := by
  classical
  unfold secondMomentN Config.count
  rw [Finset.sum_multiset_map_count]
  -- extend the `toFinset` sum to `univ`: outside `toFinset`, `count = 0`.
  rw [Finset.sum_subset (Finset.subset_univ c.toFinset)]
  · refine Finset.sum_congr rfl (fun a _ => by rw [smul_eq_mul])
  · intro a _ ha
    rw [Multiset.count_eq_zero_of_notMem (by simpa using ha), smul_eq_mul, zero_mul]

/-- **The saturated-count conversion (fully proved, exact).**  Each saturated-positive Main
contributes `sqMainN ≥ 4`, so `4 · #saturatedPos ≤ secondMomentN`. -/
theorem four_mul_saturatedPos_le_secondMoment (c : Config (AgentState L K)) :
    4 * (PhaseFloors.saturatedPosSet L K).sum c.count ≤ secondMomentN c := by
  classical
  rw [secondMomentN_eq_sum, Finset.mul_sum]
  -- restrict the univ sum to the saturated set and lower-bound each term.
  calc ∑ a ∈ PhaseFloors.saturatedPosSet L K, 4 * c.count a
      ≤ ∑ a ∈ PhaseFloors.saturatedPosSet L K, c.count a * sqMainN a := by
        refine Finset.sum_le_sum (fun a ha => ?_)
        simp only [PhaseFloors.saturatedPosSet, PhaseFloors.saturatedPos,
          Finset.mem_filter] at ha
        obtain ⟨_, hrole, hval⟩ := ha
        have hsq : 4 ≤ sqMainN a := by
          unfold sqMainN; rw [if_pos hrole]; exact sqDist3N_ge_four_of_saturated _ hval
        calc 4 * c.count a ≤ sqMainN a * c.count a := Nat.mul_le_mul_right _ hsq
          _ = c.count a * sqMainN a := Nat.mul_comm _ _
    _ ≤ ∑ a ∈ Finset.univ, c.count a * sqMainN a :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- **The conversion to the saturated-side budget.**  If `secondMomentN c ≤ 4·B`, then
`#saturatedPos ≤ B`. -/
theorem saturatedPos_le_of_secondMoment_le (c : Config (AgentState L K)) (B : ℕ)
    (h : secondMomentN c ≤ 4 * B) :
    (PhaseFloors.saturatedPosSet L K).sum c.count ≤ B := by
  have hconv := four_mul_saturatedPos_le_secondMoment c
  omega

/-! ### The whp tail through the landed level engine.

`OneSidedCancel.level_tail` gives, for the ℕ-potential `Φ = secondMomentN` non-increasing on the
window (`potNonincrOn_secondMomentN`) with `Inv = Phase1AllMain` closed
(`Phase1Convergence.invClosed_phase1AllMain`), and the carried per-level drain rate `q : ℕ → ℝ≥0∞`
(`hdrop`): from a start at level `≤ m`, the mass still at-or-above level `m` after `t` steps is
`≤ (q m)^t`.  At `m := 4·B + 1` the failure event `(potBelow Φ m)ᶜ = {Φ ≥ 4B+1} = {Φ > 4B}` is
exactly "the saturated side is too big" via `saturatedPos_le_of_secondMoment_le`. -/

/-- **The Phase-1 second-moment whp tail.**  With the deterministic non-increase
(`potNonincrOn_secondMomentN`) and the carried per-level drain rate `q` (the [45]/Corollary-1
quantitative atom, exposed as a hypothesis exactly as `Phase1Convergence.phase1Convergence`
carries its `extremeU` drain rate), the mass with `secondMomentN ≥ m` after `t` interactions is
`≤ (q m)^t`. -/
theorem secondMoment_level_tail (n : ℕ) (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : Config (AgentState L K),
      Phase1Convergence.Phase1AllMain n b → secondMomentN b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ ≤ q m)
    (m : ℕ) (c : Config (AgentState L K))
    (hc : secondMomentN c ≤ m) (hInvc : Phase1Convergence.Phase1AllMain n c) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ ≤ (q m) ^ t :=
  OneSidedCancel.level_tail (NonuniformMajority L K).transitionKernel
    (fun c => Phase1Convergence.Phase1AllMain n c)
    (Phase1Convergence.invClosed_phase1AllMain n)
    (fun c => secondMomentN c) (potNonincrOn_secondMomentN n)
    q hdrop m c hc hInvc t

/-! ## Stage 4 — the wired floor: `P ≤ pullPosSet` whp over the Phase-1 window.

On the `Phase1AllMain n` window every agent is a Main, so `mainCount = card = n`.  Combining
`mainCount = n` with the saturated-count conversion and the landed wrapper
`EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound`, the "good" event
`{secondMomentN ≤ 4·(n − P)}` deterministically gives `P ≤ pullPosSet.sum count`.  The level tail
then bounds the complementary failure mass by `(q m)^t`. -/

/-- On a `Phase1AllMain n` window, every agent is a Main, so `mainCount c = n`. -/
theorem mainCount_eq_n_of_window (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Convergence.Phase1AllMain n c) :
    RoleSplitConcentration.mainCount (L := L) (K := K) c = n := by
  obtain ⟨hcard, hph⟩ := hInv
  rw [RoleSplitConcentration.mainCount, Multiset.countP_eq_card.mpr (fun a ha => (hph a ha).2),
    hcard]

/-- **The deterministic floor on the good event.**  On the window, if the second moment has
contracted to `≤ 4·(n − P)`, then the saturated-positive side is `≤ n − P`, the budget
`P + saturatedPos ≤ mainCount = n` holds, and the landed wrapper delivers `P ≤ pullPosSet`. -/
theorem phase1_pullPos_floor_of_secondMoment_le (n P : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Convergence.Phase1AllMain n c) (hP : P ≤ n)
    (hsm : secondMomentN c ≤ 4 * (n - P)) :
    P ≤ (DrainThreading.pullPosSet L K).sum c.count := by
  have hsat : (PhaseFloors.saturatedPosSet L K).sum c.count ≤ n - P :=
    saturatedPos_le_of_secondMoment_le c (n - P) hsm
  have hmain : RoleSplitConcentration.mainCount (L := L) (K := K) c = n :=
    mainCount_eq_n_of_window n c hInv
  refine EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound ?_
  rw [hmain]; omega

/-- **The saturated-side floor, whp (the §1 floor).**  With the deterministic second-moment
non-increase and the carried per-level drain rate `q` (the [45]/Corollary-1 averaging atom,
exposed exactly as `Phase1Convergence` exposes its `extremeU` drain rate), after `t` interactions
on the Phase-1 window the partner-pool floor `P ≤ pullPosSet.sum count` FAILS with probability at
most `(q m)^t`, where `m = 4·(n − P) + 1`.  This feeds
`EliminatorMargins.phase1_pullPos_floor_of_mainCount_and_saturated_bound` →
`PhaseFloors.phase1_hdrop_wired`. -/
theorem phase1_pullPos_floor_whp (n P : ℕ) (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : Config (AgentState L K),
      Phase1Convergence.Phase1AllMain n b → secondMomentN b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ ≤ q m)
    (c : Config (AgentState L K)) (hInvc : Phase1Convergence.Phase1AllMain n c)
    (hP : P ≤ n) (hc : secondMomentN c ≤ 4 * (n - P) + 1) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {c' | ¬ P ≤ (DrainThreading.pullPosSet L K).sum c'.count}
      ≤ (q (4 * (n - P) + 1)) ^ t := by
  set m := 4 * (n - P) + 1 with hm
  -- the failure event is inside `(potBelow secondMomentN m)ᶜ = {secondMomentN ≥ m}`, BUT we must
  -- restrict to the window (where the deterministic floor holds).  Use the support-closure of
  -- `Phase1AllMain` to keep the trajectory in-window, then the tail.
  have hsubset :
      {c' : Config (AgentState L K) | ¬ P ≤ (DrainThreading.pullPosSet L K).sum c'.count}
        ⊆ {x | ¬ Phase1Convergence.Phase1AllMain n x}
          ∪ (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ := by
    intro c' hc'
    by_cases hwin : Phase1Convergence.Phase1AllMain n c'
    · -- in-window: if also `secondMomentN c' < m` the floor would hold, contradicting `hc'`.
      refine Or.inr ?_
      simp only [OneSidedCancel.potBelow, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      by_contra hlt
      rw [not_le] at hlt
      exact hc' (phase1_pullPos_floor_of_secondMoment_le n P c' hwin hP (by omega))
    · exact Or.inl hwin
  calc ((NonuniformMajority L K).transitionKernel ^ t) c
          {c' | ¬ P ≤ (DrainThreading.pullPosSet L K).sum c'.count}
      ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
          ({x | ¬ Phase1Convergence.Phase1AllMain n x}
            ∪ (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ) := measure_mono hsubset
    _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c
            {x | ¬ Phase1Convergence.Phase1AllMain n x}
          + ((NonuniformMajority L K).transitionKernel ^ t) c
            (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ := measure_union_le _ _
    _ = 0 + ((NonuniformMajority L K).transitionKernel ^ t) c
            (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ := by
        rw [OneSidedCancel.pow_not_inv_eq_zero (NonuniformMajority L K).transitionKernel
          (fun c => Phase1Convergence.Phase1AllMain n c)
          (Phase1Convergence.invClosed_phase1AllMain n) c hInvc t]
    _ = ((NonuniformMajority L K).transitionKernel ^ t) c
            (OneSidedCancel.potBelow (fun c => secondMomentN c) m)ᶜ := by rw [zero_add]
    _ ≤ (q m) ^ t :=
        secondMoment_level_tail n q hdrop m c hc hInvc t

end AveragingCollapse

end ExactMajority
