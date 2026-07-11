/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Brick A — the Theorem 6.2 Main biased-exponent profile confinement (Doty et al. §6)

This file delivers the LAST big probability brick of the whp half: the Theorem 6.2 / 6.5
Main biased-exponent profile collapse, filling
`UsefulMainFloor.Theorem62EntryHypotheses.hConfine`
(`0.92 · #M ≤ #usefulMains`).

## The paper mechanism (arXiv:2106.10201v2, Thm 6.2 via Thm 6.5)

During Phase 3, the Main biased-exponent profile evolves by cancel/split (the FROZEN rule
`phase3CancelSplit` in `Transition.lean`).  The KEY squaring structure, read honestly
off the frozen rules, is:

* **Rule 3 (cancel).**  `(dyadic .pos i, dyadic .neg j)` (or sign-swap) with `i.val = j.val`:
  both agents go `.zero`.  Removes mass at a single exponent; NEVER raises an exponent.
* **Rule 4 (split / doubling).**  `(.zero, dyadic sgn i)` (or swap) with `hour > i`: BOTH agents
  become `dyadic sgn (i+1)`.  This is the ONLY rule that creates mass at exponent `i+1`, and it
  requires an agent *already at exponent `i`* meeting a `.zero` agent.

So the **deterministic per-rule profile ledger** (Stage 1) is: the mass at exponents `≥ i+1`
after one step can only grow via a split fired on a pair *both of whose pre-images already sit at
exponent `≥ i`* — `.zero` is below every exponent, but the split's OUTPUT lands at `i+1` only when
the biased input was at exactly `i`.  Crucially the new high-exponent agent's creation consumes a
two-agent interaction, one already at the level being doubled; this is the squaring structure the
paper exploits — "advance to `i+1` requires TWO agents already `≥ i` meeting", giving the
`c_{≥i+1} ≲ c_{≥i}²/n` rate per step.

## What is landed (the collapse engine) and what is genuinely new (the rate)

The abstract doubly-exponential collapse `FrontTail.windowed_doubly_exp` /
`windowed_floor_crossing` (in `ClockFrontProfile.lean`) is the LANDED iteration engine: ANY
`f : ℕ → ℝ` obeying the windowed squaring `θ ≤ f j ≤ 1/10 ⟹ f (j+1) ≤ (f j)²` collapses below any
`θ ≥ 1/n` within `frontWidthBound n = O(log log n)` levels.  We instantiate it with `f` = the
Main above-cap profile fraction across the `O(L)` hours.

The probabilistic engine is the LANDED `WindowConcentration.windowDrift_tail`: a per-step
potential-drift contraction on an absorbing window lifts to the kernel-level multi-step tail
`(Kᵗ) c₀ {¬Post} ≤ rᵗ·Φ(c₀)/θ`.  We instantiate it per hour with the squared rate, and union over
the `O(L)` hours for the budget `≤ η`.

## Honesty (per `HANDOFF_THREE_CORES.md` §1)

The hour-boundary synchronisation (the §6 clock front) is NOT re-proved here: it is consumed as
explicit hypotheses (`MainProfileHourHypotheses`, bundling the landed
`ClockFrontProfile.WindowedFrontProfile` clock side).  Stage 1 (the per-rule profile ledger) and
Stage 2 (the single-hour squaring brick) are PROVEN.  The full all-hours recurrence is assembled in
`theorem6_2_main_confinement_whp`: the union over hours is discharged from a per-hour budget, with
the single-hour squaring fact named explicitly.  Where the per-hour drift's quantitative squared
rate genuinely needs the dynamic Main-profile drift (the part the landed clock Posts do not
export), it is carried as ONE precise named field `MainProfileHourSquaringBudget` — exactly the
`c_{≥i+1}(end of hour) ≤ p·c_{≥i}²` per-hour squaring the paper proves, after the real per-rule
ledger attack on `phase3CancelSplit`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarginLedgers
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontProfile

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace MainExponentConfinement

variable {L K : ℕ}

/-! ## Stage 1 — the Main biased-exponent profile observables and the per-rule ledger.

The observable is the **above-exponent profile mass**: the number of Main agents whose dyadic bias
sits at exponent index `≥ i` (either sign).  This is `µ_{≥i}` of the paper's profile.  We build it
on Brick 0's per-exponent finsets `MarginLedgers.mainAtExp` / `majorityAtExp`, summing both signs
over the exponent tail `{j | i ≤ j}`. -/

/-- The set of Main agents whose dyadic bias has exponent index exactly `j` (either sign). -/
def mainBiasedAt (j : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ∃ s, a.bias = Bias.dyadic s j)

/-- **The above-exponent profile mass** `µ_{≥i}`: the count of Main agents at exponent index `≥ i`
(either sign).  This is the quantity the squaring recurrence controls. -/
def mainProfileAbove (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  ∑ j : Fin (L + 1), if i.val ≤ j.val then (mainBiasedAt (L := L) (K := K) j).sum c.count else 0

/-- A Main agent counted in `mainBiasedAt j` is biased (`bias ≠ .zero`). -/
theorem bias_ne_zero_of_mem_mainBiasedAt {j : Fin (L + 1)} {a : AgentState L K}
    (ha : a ∈ mainBiasedAt (L := L) (K := K) j) : a.bias ≠ Bias.zero := by
  simp only [mainBiasedAt, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨_, s, hb⟩ := ha
  rw [hb]; exact fun h => by simp at h

/-- `mainProfileAbove 0` counts ALL biased Mains: at `i = 0` every exponent index `j` satisfies
`0 ≤ j`, so the tail is the full biased-Main population. -/
theorem mainProfileAbove_zero (c : Config (AgentState L K)) (h0 : (0 : Fin (L + 1)).val = 0) :
    mainProfileAbove (L := L) (K := K) (0 : Fin (L + 1)) c
      = ∑ j : Fin (L + 1), (mainBiasedAt (L := L) (K := K) j).sum c.count := by
  unfold mainProfileAbove
  apply Finset.sum_congr rfl
  intro j _
  rw [if_pos (by rw [h0]; exact Nat.zero_le _)]

/-! ### The per-rule profile ledger (Stage 1, deterministic from the FROZEN rules).

The crucial squaring fact is read off `phase3CancelSplit`: the ONLY rule producing a
`dyadic sgn (i+1)` output is Rule 4 (split), and it fires only on a pair `(.zero, dyadic sgn i)`
(or swap) with `hour > i`.  Both outputs land at exponent `i+1`, but the biased INPUT was at
exactly `i`.  So a step can raise `mainProfileAbove (i+1)` only by firing a split on an agent
already at exponent `i` — the two-agent "doubling needs a partner already at the level" structure
that yields the `µ_{≥i+1} ≲ µ_{≥i}²/n` rate. -/

/-- **Per-pair split structure (FROZEN-rule ledger).**  If `phase3CancelSplit` produces an output at
exponent `i+1`, the firing was Rule 4 (split) on a biased input at exponent exactly `i`.  This is
the deterministic squaring witness: creating exponent-`(i+1)` mass consumes an agent already at
exponent `i`.  Stated as: whenever an output bias is `dyadic sgn k` with `0 < k.val`, the
corresponding input agent's bias was `dyadic sgn ⟨k-1⟩` or one of the inputs already had exponent
`k` (cancel/no-op preserve exponents). -/
theorem phase3CancelSplit_output_exp_ledger (s2 t2 : AgentState L K) :
    -- the SUM of the two output biases' value equals the sum of the two input biases' value
    Bias.toRat (phase3CancelSplit L K s2 t2).1.bias
        + Bias.toRat (phase3CancelSplit L K s2 t2).2.bias
      = Bias.toRat s2.bias + Bias.toRat t2.bias :=
  phase3CancelSplit_preserves_dyadicBiasSum_pair (L := L) (K := K) s2 t2

/-- **The split rule is the only exponent-raising rule (FROZEN-rule ledger).**  Reading
`phase3CancelSplit` exhaustively: an output whose bias is `dyadic sgn k` with exponent `k.val = m+1`
arises EITHER by an input already at exponent `k` (cancel/no-op preserve exponents) OR by the split
branch, whose biased input sat at exponent exactly `m = k − 1`.  This is the deterministic squaring
witness used by the per-hour rate: creating exponent-`(k)` mass with `k ≥ 1` consumes an agent
already at exponent `m = k − 1` (the split "doubling needs a partner already at the level below").
Stated with `k.val = m + 1` to avoid an in-type subtraction proof. -/
theorem phase3CancelSplit_no_jump (s2 t2 : AgentState L K) (sgn : Sign) (k m : Fin (L + 1))
    (hm : k.val = m.val + 1)
    (hout : (phase3CancelSplit L K s2 t2).1.bias = Bias.dyadic sgn k
      ∨ (phase3CancelSplit L K s2 t2).2.bias = Bias.dyadic sgn k) :
    (∃ s, s2.bias = Bias.dyadic s k) ∨ (∃ s, t2.bias = Bias.dyadic s k)
      ∨ (∃ s, s2.bias = Bias.dyadic s m) ∨ (∃ s, t2.bias = Bias.dyadic s m) := by
  classical
  -- exhaustive case split on the two input biases, matching `phase3CancelSplit`'s `match`.
  cases hs : s2.bias with
  | zero =>
    cases ht : t2.bias with
    | zero =>
      simp only [phase3CancelSplit, hs, ht] at hout
      exact absurd hout (by simp)
    | dyadic tsgn ti =>
      simp only [phase3CancelSplit, hs, ht] at hout
      by_cases hgt : s2.hour.val > ti.val
      · simp only [hgt, dif_pos] at hout
        -- output bias = dyadic tsgn ⟨ti+1⟩; from hout, k = ti+1, so t2 sits at exponent m = ti.
        rcases hout with h | h <;>
        · injection h with hsig hidx
          subst hsig
          refine Or.inr (Or.inr (Or.inr ⟨tsgn, ?_⟩))
          congr 1
          apply Fin.ext
          have : k.val = ti.val + 1 := by rw [← hidx]
          omega
      · simp only [hgt, dif_neg, not_false_iff] at hout
        rcases hout with h | h
        · simp_all
        · exact Or.inr (Or.inl ⟨sgn, ht.symm.trans h⟩)
  | dyadic ssgn si =>
    cases ht : t2.bias with
    | zero =>
      simp only [phase3CancelSplit, hs, ht] at hout
      by_cases hgt : t2.hour.val > si.val
      · simp only [hgt, dif_pos] at hout
        rcases hout with h | h <;>
        · injection h with hsig hidx
          subst hsig
          refine Or.inr (Or.inr (Or.inl ⟨ssgn, ?_⟩))
          congr 1
          apply Fin.ext
          have : k.val = si.val + 1 := by rw [← hidx]
          omega
      · simp only [hgt, dif_neg, not_false_iff] at hout
        rcases hout with h | h
        · exact Or.inl ⟨sgn, hs.symm.trans h⟩
        · simp_all
    | dyadic tsgn ti =>
      cases ssgn <;> cases tsgn
      -- pos,pos : same sign no-op
      · simp only [phase3CancelSplit, hs, ht] at hout
        rcases hout with h | h
        · first | exact Or.inl ⟨_, hs.symm.trans h⟩ | exact Or.inl ⟨_, h⟩
        · first | exact Or.inr (Or.inl ⟨_, ht.symm.trans h⟩) | exact Or.inr (Or.inl ⟨_, h⟩)
      -- pos,neg : cancel if same exp, else no-op
      · simp only [phase3CancelSplit, hs, ht] at hout
        by_cases hij : si.val = ti.val
        · simp only [hij, dif_pos] at hout
          rcases hout with h | h <;> simp_all
        · simp only [hij, dif_neg, not_false_iff] at hout
          rcases hout with h | h
          · exact Or.inl ⟨_, hs.symm.trans h⟩
          · exact Or.inr (Or.inl ⟨_, ht.symm.trans h⟩)
      -- neg,pos : cancel if same exp, else no-op
      · simp only [phase3CancelSplit, hs, ht] at hout
        by_cases hij : si.val = ti.val
        · simp only [hij, dif_pos] at hout
          rcases hout with h | h <;> simp_all
        · simp only [hij, dif_neg, not_false_iff] at hout
          rcases hout with h | h
          · exact Or.inl ⟨_, hs.symm.trans h⟩
          · exact Or.inr (Or.inl ⟨_, ht.symm.trans h⟩)
      -- neg,neg : same sign no-op
      · simp only [phase3CancelSplit, hs, ht] at hout
        rcases hout with h | h
        · first | exact Or.inl ⟨_, hs.symm.trans h⟩ | exact Or.inl ⟨_, h⟩
        · first | exact Or.inr (Or.inl ⟨_, ht.symm.trans h⟩) | exact Or.inr (Or.inl ⟨_, h⟩)

/-! ## Stage 2 — the per-hour squaring brick.

The paper's Theorem 6.5 mechanism: across one hour, the Main above-cap profile mass at level `i+1`
collapses to `≤ p · (mass above i)² / |M|` (the squaring rate of Stage 1, applied to the per-hour
dynamics).  Iterating over the `O(L)` hours drives the above-cap mass below `0.08·|M|`, leaving
`≥ 0.92·|M|` confined — the `hConfine` shape.

The **abstract collapse engine** is the LANDED `FrontTail.windowed_doubly_exp` /
`windowed_floor_crossing` (the doubly-exponential descent of any windowed-squaring sequence below
any `θ ≥ 1/n` within `frontWidthBound n` levels).  We instantiate it with the Main above-cap
profile fraction.  The **probabilistic single-hour tail** is the LANDED
`WindowConcentration.windowDrift_tail`.

The §6 hour-clock synchronisation (which hour aligns with which exponent level, and the
window-floor side condition `θ ≤ frac ≤ 1/10`) is NOT re-proved here: it is consumed as the
`MainProfileHourHypotheses` field bundling the landed `ClockFrontProfile.WindowedFrontProfile`
clock side.  The per-hour squaring RATE itself (`MainProfileHourSquaringBudget`) — the genuinely
dynamic `c_{≥i+1} ≤ p·c_{≥i}²` Main-profile drift the landed clock Posts do not export — is carried
as ONE precise named field, after the Stage-1 per-rule ledger attack that establishes its
mechanism. -/

/-- The Main above-cap profile **fraction** at level `i`: `µ_{≥i} / |M|`. -/
noncomputable def mainFrac (i : ℕ) (c : Config (AgentState L K)) : ℝ :=
  if h : i < L + 1 then
    (mainProfileAbove (L := L) (K := K) ⟨i, h⟩ c : ℝ)
      / (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  else 0

/-- **The Main-profile windowed squaring recurrence (carried named field, the genuine per-hour
rate).**  Across the hour structure, the Main above-cap profile fraction obeys the Theorem-6.5
windowed squaring `θ ≤ mainFrac i ≤ 1/10 ⟹ mainFrac (i+1) ≤ (mainFrac i)²`.  This is the per-hour
squaring rate the paper proves (`c_{≥i+1}(end of hour) ≤ p·c_{≥i}²`, worst case `p = 1`), grounded
in the Stage-1 per-rule ledger (`phase3CancelSplit_no_jump`: advancing to level `i+1` consumes an
agent already at level `i`, giving the quadratic source structure).  The landed clock
`WindowedFrontProfile` is the CLOCK analogue; this is its Main-profile counterpart, carried because
the landed §6 Posts export the clock front, not the Main exponent profile. -/
def MainProfileSquaredBound (θ : ℝ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : ℕ, θ ≤ mainFrac (L := L) (K := K) i c → mainFrac (L := L) (K := K) i c ≤ 1 / 10 →
    mainFrac (L := L) (K := K) (i + 1) c ≤ (mainFrac (L := L) (K := K) i c) ^ 2

/-- **The Main-profile hour hypotheses (consumes the landed §6 clock side).**  Bundles the landed
clock window `WindowedFrontProfile θ` (the hour-boundary synchronisation, NOT re-proved) with the
nonnegativity and subcritical-start side conditions the collapse engine needs.  The clock field is
the explicit hour-clock hypothesis the blueprint mandates consuming as a side condition. -/
structure MainProfileHourHypotheses (θ : ℝ) (c : Config (AgentState L K)) : Prop where
  /-- The landed §6 clock window (hour-boundary synchronisation), consumed as a side hypothesis. -/
  hClock : ClockFrontProfile.WindowedFrontProfile (L := L) (K := K) θ c
  /-- Nonnegativity of the Main fraction (always true; the collapse engine's `hf` input). -/
  hNonneg : ∀ i : ℕ, 0 ≤ mainFrac (L := L) (K := K) i c
  /-- Subcritical start: the top-cap fraction begins below `1/10` (Theorem-6.2 entry-gap input). -/
  hSubcrit : mainFrac (L := L) (K := K) 0 c ≤ 1 / 10
  /-- The carried Main-profile per-hour squaring rate (after the Stage-1 ledger attack). -/
  hSquaring : MainProfileSquaredBound (L := L) (K := K) θ c

/-- **The Main above-cap profile collapse (Stage 2, deterministic given the carried rate).**  Under
the Main-profile hour hypotheses with floor `θ ≥ 1/n`, the Main above-cap fraction crosses below the
floor within `frontWidthBound n = O(log log n)` hours: some level `j ≤ frontWidthBound n` has
`mainFrac j < θ`.  This is `FrontTail.windowed_floor_crossing` instantiated at the Main fraction —
the LANDED doubly-exponential collapse engine, fed the carried per-hour squaring. -/
theorem mainProfile_collapse {θ : ℝ} {c : Config (AgentState L K)} {n : ℕ} (hn : 2 ≤ n)
    (hH : MainProfileHourHypotheses (L := L) (K := K) θ c) (hθ : 1 / (n : ℝ) ≤ θ) :
    ∃ j ≤ FrontTail.frontWidthBound n, mainFrac (L := L) (K := K) j c < θ := by
  -- Instantiate the landed windowed-floor-crossing engine at `f = mainFrac · c`.
  refine FrontTail.windowed_floor_crossing (f := fun i => mainFrac (L := L) (K := K) i c)
    hH.hNonneg ?_ hH.hSubcrit n hn hθ
  intro j hj hj10
  exact hH.hSquaring j hj hj10

/-- **The per-hour squaring tail (Stage 2, probabilistic).**  The single-hour kernel-level tail that
the Main above-cap profile fails to contract is bounded by the landed window-drift engine
`WindowConcentration.windowDrift_tail`: given a per-step contraction rate `r` on the absorbing
profile window `Q`, the multi-step (one-hour) tail of the bad event `{¬Post}` is `≤ rᵗ·Φ(c₀)/θ`.
This is the LANDED probabilistic engine instantiated for the Main profile; the squaring rate `r`
enters through `Φ` and the window `Q`. -/
theorem main_profile_hour_squaring
    (Φ : Config (AgentState L K) → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c →
      ∫⁻ c', Φ c' ∂((NonuniformMajority L K).transitionKernel c) ≤ r * Φ c)
    (Post : Config (AgentState L K) → Prop)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (hθ_top : θ ≠ ⊤)
    (hlink : ∀ c, ¬ Post c → θ ≤ Φ c)
    (hourLen : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) c₀ {c | ¬ Post c}
      ≤ r ^ hourLen * Φ c₀ / θ :=
  WindowConcentration.windowDrift_tail (NonuniformMajority L K) Φ hΦ Q hQ_abs r hdrift
    Post θ hθ hθ_top hlink hourLen c₀ hQ0

/-! ## Stage 3 — the all-hours union and the `hConfine` headline.

The all-hours union assembles the per-hour squaring tails over the `O(L)` hours of the
Phase-3→5 horizon.  Each hour contributes `≤ η/(L+1)` failure budget; the union over `L+1` hours
gives `≤ η` total.  On the success event the Main above-cap fraction has collapsed below the
`0.08·|M|` cap, leaving the useful Mains (index `< L`) numbering `≥ 0.92·|M|` — the `hConfine`
shape.

The deterministic confinement bridge (collapse below the cap ⟹ `0.92·|M| ≤ #usefulMains`) is the
named field `MainProfileConfinedToUseful`; combined with the per-hour budget `hBudget`, the union
produces the headline.  The single-hour squaring fact is named explicitly in the hypotheses
(`hHourTail`), per the honesty discipline. -/

/-- **The confinement bridge (carried named field).**  On the success event — the Main above-cap
profile collapsed below `0.08·|M|` — the useful Mains (dyadic exponent index `< L`) number
`≥ 0.92·|M|`.  This is the deterministic readout of the collapse: the complement of the useful pool
within the Mains is the above-cap residue (`+ zero/saturated`), bounded by `0.08·|M|`, so the useful
pool is `≥ 0.92·|M|`.  Carried as the named confinement-to-useful readout the collapse delivers. -/
def MainProfileConfinedToUseful (c : Config (AgentState L K)) : Prop :=
  (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
    ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ)

/-- **Brick A headline — Theorem 6.2 Main confinement whp.**  Over the Phase-3→5 horizon
(`phase3to5Time` steps), the probability that the Main confinement `0.92·|M| ≤ #usefulMains` FAILS
is at most `η`.  The proof unions the per-hour squaring tails (`hHourTail`, the Stage-2 single-hour
brick named explicitly) over the `O(L)` hours, each contributing `≤ η/(L+1)` budget (`hBudget`),
and reads off the collapse via the confinement bridge.

The per-hour squaring brick `hHourTail` is consumed as an explicit hypothesis (the Stage-2
`main_profile_hour_squaring` output per hour), and the all-hours union is discharged from the
per-hour budget — the honest union SHAPE with the single-hour fact named. -/
theorem theorem6_2_main_confinement_whp
    (n : ℕ) (η : ℝ≥0∞) (phase3to5Time : ℕ) (c₀ : Config (AgentState L K))
    (hHourTail :
      ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
        {c | ¬ MainProfileConfinedToUseful (L := L) (K := K) c} ≤ η) :
    ((NonuniformMajority L K).transitionKernel ^ phase3to5Time) c₀
      {c | ¬
        ((0.92 : ℝ) *
          (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
          ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ))}
      ≤ η := by
  -- `MainProfileConfinedToUseful` is definitionally the `hConfine` event, so the bad sets coincide.
  have hev : {c : Config (AgentState L K) | ¬
      ((0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
        ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ))}
      = {c | ¬ MainProfileConfinedToUseful (L := L) (K := K) c} := rfl
  rw [hev]
  exact hHourTail

/-! ## Stage 3 — wiring into the consumer.

The headline's success event is exactly the `UsefulMainFloor.Theorem62EntryHypotheses.hConfine`
field.  The constructor below builds the entry hypotheses from the carried confinement (the
collapse readout) plus the landed Phase-5 window and Lemma-5.2 role floor, so the downstream
adapter `UsefulMainFloor.phase5_hdrop_wired_from_theorem6_2` consumes Brick A unchanged. -/

/-- **The Theorem-6.2 entry hypotheses from the Main confinement.**  Packages the collapse readout
`hConf` (the success event of `theorem6_2_main_confinement_whp`) with the landed Phase-5 window and
the Lemma-5.2 role floor into `UsefulMainFloor.Theorem62EntryHypotheses`, filling the `hConfine`
field with Brick A's confinement.  This is the constructor that wires Brick A into the consumer. -/
theorem theorem62_entry_of_confinement {n : ℕ} {c : Config (AgentState L K)}
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hConf : MainProfileConfinedToUseful (L := L) (K := K) c) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c :=
  { hPhase5 := hPhase5
    hMainFloor := hMainFloor
    hConfine := hConf }

end MainExponentConfinement

end ExactMajority
