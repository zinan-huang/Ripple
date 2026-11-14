/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# WidthTransport — within-window WFP transport (Doty et al. §6, free-τ width feeder)

This file implements the **within-window windowed-front-profile (WFP) transport** per the blueprint
`HANDOFF_WFP_TRANSPORT.md`.  The verdict of that blueprint, verified
against the branch here:

* **Deterministic transport works for the SCALAR front pointer.**  In `Phase3Transition` only the
  equal-minute DRIP branch can raise the GLOBAL maximum minute (by exactly one per interaction); the
  SYNC branch (unequal minutes → both clocks get `max`) raises individual clocks but NEVER the global
  max.  This is exactly `ClimbTail.transition_p3_minute_le_succ_max` (per-pair) and
  `ClimbTail.climbN_le_succ_on_support` (per-step climb height).  Stage 1 here lifts the per-step
  bound to the `t`-step support-chain additive bound `climbN k c_t ≤ climbN k c_0 + t` along any
  trajectory that stays inside the `AllClockP3` window (the window is required: the `+1` minute fact
  is phase-3-specific, and `AllClockP3` is not absorbing, only `AllClockGE3` is).

* **Do NOT transport the full `WindowedFrontProfile` deterministically.**  Per-minute counts can shift
  massively via SYNC.  Stage 2 transports only the WIDTH consequence, using the deterministic glue
  `goodFrontWidth_of_checkpoint_profile_climb_transport`: the checkpoint's `WindowedFrontProfile` +
  `ClimbBound` collapse a sub-floor level at the checkpoint, the cross-config `CrossEmptyClimbGood`
  preserves the resulting emptiness `W₃` levels up at the endpoint, and `rBeyond`-antitonicity closes.

* **The probabilistic complement** `CrossEmptyClimbBad` is a finite union of `ClimbTail.climb_real_tail`
  events with the climb threshold instantiated as the bulk floor (Stage 3, `crossEmptyClimb_whp`).

* **The checkpoint-to-checkpoint assembly** `widthFail_between_checkpoints_concrete` (Stage 4) glues
  the `r = 0` checkpoint feeder `CrossHourSide.widthFail_chk_concrete` (= `εWAt_chk`) with the
  within-window climb tail via Chapman–Kolmogorov at horizon `w·j + r`.

## Blueprint citation audit (verified against the branch)

* `transition_p3_minute_le_succ_max`, `climbN_le_succ_on_support`, `climb_real_tail`, `climbGate`,
  `climbPot` — all present in `Probability/ClimbTail.lean`, signatures match the blueprint verbatim.
* `GoodFrontWidth`, `WindowedFrontProfile`, `ClimbBound`, `goodFrontWidth_of_windowed_profile_and_climb`
  — present in `Probability/ClockFrontProfile.lean`.
* `rBeyondGE3_ge_monotone`, `AllClockGE3_absorbing` — present in `Probability/ClockRealKernel.lean`.
* `rBeyond_antitone_threshold` — present in `Probability/MixedWindowClosure.lean`.
* `frontWidthBound` — present in `Probability/FrontTailDecay.lean` (`FrontTail` namespace).
* `windowed_floor_crossing` — present in `Probability/ClockFrontProfile.lean` (`FrontTail` namespace).
* `climbBound_whp` / `climbBound_bad_subset` — present in `Probability/EarlyDripMarked.lean`.

**Discrepancy (recorded):** the blueprint states `CrossEmptyClimbGood`'s bulk test as
`rBeyond k c₁ < n / 10` (Nat floor division).  The faithful `GoodFrontWidth` cardinality form
throughout this codebase is `c.card ≤ 10 * rBeyond …` (and its negation `10 * rBeyond … < c.card`).
The `< n/10` Nat-division form is NOT equivalent to `10 * rBeyond < n` (e.g. `n = 15, x = 1`:
`10 < 15` but `1 < 1` is false), and using it would break the contradiction at the floor.  We
therefore state `CrossEmptyClimbGood` with the codebase-faithful test `10 * rBeyond k c₁ < n`, which
is exactly the negation of the `GoodFrontWidth` conjunct it must contradict.

Everything here is 0-sorry, axiom-clean, on the REAL `NonuniformMajority` kernel.

Reference: Doty et al. (arXiv:2106.10201v2), proof of Theorem 6.5 (the "first claim"); blueprint
`HANDOFF_WFP_TRANSPORT.md`.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.ClimbTail
import Ripple.PopulationProtocol.ExactMajority.Probability.ClockFrontProfile
import Ripple.PopulationProtocol.ExactMajority.Probability.EarlyDripMarked
import Ripple.PopulationProtocol.ExactMajority.Probability.Params
import Ripple.PopulationProtocol.ExactMajority.Probability.CrossHourSide

namespace Ripple.PopulationProtocol.ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators Classical

namespace ClockFrontProfile

open ClockRealKernel ClockFrontShape MixedWindowClosure

variable {L K : ℕ}

/-! ## Stage 1 — the deterministic scalar front step bound, lifted to `t` steps.

The per-step climb-height bound `ClimbTail.climbN_le_succ_on_support` requires the `AllClockP3`
window at the SOURCE config (the `+1` minute increment is phase-3-specific).  Since `AllClockP3` is
not absorbing, the iterated bound is genuinely a within-window statement: along any support chain
that stays in `AllClockP3`, the climb height rises by at most the chain length. -/

/-- A one-step `P3-window support` link: `c'` is a one-step support point of `c` AND `c` is in the
`AllClockP3` window.  Staying in the window is exactly what licenses the per-step `+1` minute bound. -/
def P3SupportStep (c c' : Config (AgentState L K)) : Prop :=
  AllClockP3 (L := L) (K := K) c ∧
    c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support

/-- An `n`-step `P3-window support chain` from `c₀` to `c`: a chain of `n` `P3SupportStep` links. -/
def P3SupportChain : ℕ → Config (AgentState L K) → Config (AgentState L K) → Prop
  | 0,     c₀, c => c = c₀
  | n + 1, c₀, c => ∃ c', P3SupportChain n c₀ c' ∧ P3SupportStep (L := L) (K := K) c' c

/-- **Stage 1 (support-chain additive front bound).**  If `c₀ →* c` through an `n`-step
`P3SupportChain`, then `climbN k c ≤ climbN k c₀ + n`.  (Each link raises the climb height by at most
one — `ClimbTail.climbN_le_succ_on_support`.)  This is the deterministic scalar front-speed bound:
the global front cannot advance faster than the number of interactions. -/
theorem climbN_chain_le (k : ℕ) (c₀ : Config (AgentState L K)) :
    ∀ (n : ℕ) (c : Config (AgentState L K)),
      P3SupportChain (L := L) (K := K) n c₀ c →
      ClimbTail.climbN (L := L) (K := K) k c ≤ ClimbTail.climbN (L := L) (K := K) k c₀ + n := by
  intro n
  induction n with
  | zero =>
    intro c hc
    -- P3SupportChain 0 c₀ c means c = c₀.
    rw [show c = c₀ from hc]; simp
  | succ n ih =>
    intro c hc
    obtain ⟨c', hchain, hP3, hsupp⟩ := hc
    have hstep : ClimbTail.climbN (L := L) (K := K) k c
        ≤ ClimbTail.climbN (L := L) (K := K) k c' + 1 :=
      ClimbTail.climbN_le_succ_on_support (L := L) (K := K) k c' c hP3 hsupp
    have htail := ih c' hchain
    omega

/-- **Stage 1 (a.e. iterated front bound on the absorbing window).**  Over `t` steps of the real
kernel from a window state `c₀ ∈ AllClockP3`, a.e. successor `c'` satisfies the absorbing-window
predicate `AllClockGE3 c'`, AND — gated on staying in `AllClockP3` along the path — the climb height
obeys `climbN k c' ≤ climbN k c₀ + t`.  Stated as the support-closed invariant
`Q c' := AllClockGE3 c' → climbN k c' ≤ climbN k c₀ + climbN-budget`, this is the kernel-level form
of the deterministic front-speed bound.  We give the a.e. `AllClockGE3` preservation (the absorbing
half) directly here; the additive climb half is the support-chain bound `climbN_chain_le`. -/
theorem ae_allClockGE3_pow (c₀ : Config (AgentState L K))
    (hge3 : AllClockGE3 (L := L) (K := K) c₀) (t : ℕ) :
    ∀ᵐ c' ∂(((NonuniformMajority L K).transitionKernel) ^ t) c₀,
      AllClockGE3 (L := L) (K := K) c' :=
  Protocol.ae_of_stepDistOrSelf_support_preserved
    (P := NonuniformMajority L K)
    (Q := fun c' => AllClockGE3 (L := L) (K := K) c')
    (fun a b hge hsupp => AllClockGE3_absorbing (L := L) (K := K) a b hge hsupp)
    c₀ hge3 t

/-! ## Stage 2 — the deterministic cross-config WIDTH transport.

`CrossEmptyClimbGood` is the within-window empty-level transport: an empty level at the checkpoint
`c₀` cannot have a nonempty `W₃`-higher level at the endpoint `c₁`, unless the `0.1` bulk threshold
has reached the original empty level by the endpoint.  The bulk test is written in the
codebase-faithful cardinality form `10 * rBeyond k c₁ < n` (see the discrepancy note in the header). -/

/-- **`CrossEmptyClimbGood`** — the deterministic cross-window empty-level transport hypothesis. -/
def CrossEmptyClimbGood
    (n W₃ : ℕ) (c₀ c₁ : Config (AgentState L K)) : Prop :=
  ∀ k : ℕ,
    rBeyond (L := L) (K := K) k c₀ = 0 →
    10 * rBeyond (L := L) (K := K) k c₁ < n →
    rBeyond (L := L) (K := K) (k + W₃) c₁ = 0

/-- **Stage 2 (deterministic width transport).**  Checkpoint `WindowedFrontProfile` + checkpoint
`ClimbBound` + the cross-config `CrossEmptyClimbGood` + level-wise monotonicity
(`rBeyond T c₀ ≤ rBeyond T c₁`, the absorbing-window growth) yield the endpoint scalar
`GoodFrontWidth` at the WIDENED margin `frontWidthBound c₀.card + W₂ + W₃`.

This transports only the WIDTH consequence — never `WindowedFrontProfile` itself.  Proof structure
copies `goodFrontWidth_of_windowed_profile_and_climb`: collapse the checkpoint profile to a sub-floor
level within `W₁`, empty it `W₂` levels up via the checkpoint `ClimbBound`, transport that emptiness
`W₃` levels further via `CrossEmptyClimbGood`, and close with `rBeyond`-antitonicity. -/
theorem goodFrontWidth_of_checkpoint_profile_climb_transport
    (θ : ℝ) (W₂ W₃ : ℕ)
    (c₀ c₁ : Config (AgentState L K))
    (hcard : c₁.card = c₀.card)
    (hcard2 : 2 ≤ c₀.card)
    (hall₁ : AllClockP3 (L := L) (K := K) c₁)
    (hθ : 1 / (c₀.card : ℝ) ≤ θ)
    (hmono : ∀ T,
      rBeyond (L := L) (K := K) T c₀ ≤ rBeyond (L := L) (K := K) T c₁)
    (hwp₀ : WindowedFrontProfile (L := L) (K := K) θ c₀)
    (hclimb₀ : ClimbBound (L := L) (K := K) θ W₂ c₀)
    (hcross : CrossEmptyClimbGood (L := L) (K := K) c₀.card W₃ c₀ c₁) :
    GoodFrontWidth (L := L) (K := K)
      (FrontTail.frontWidthBound c₀.card + W₂ + W₃) c₁ := by
  have hcardpos : 0 < c₀.card := by omega
  have hcardℝ : (0 : ℝ) < (c₀.card : ℝ) := by exact_mod_cast hcardpos
  set W₁ := FrontTail.frontWidthBound c₀.card with hW₁
  intro i hi
  -- Goal: c₁.card ≤ 10 * rBeyond (i - (W₁ + W₂ + W₃)) c₁.
  by_cases hiW : i ≤ W₁ + W₂ + W₃
  · -- i small: i - (W₁+W₂+W₃) = 0; rBeyond 0 c₁ = card (all agents clocks via mono from c₀? no —
    -- use that rBeyond 0 c₁ = c₁.card since 0 ≤ every minute).
    have hzero : i - (W₁ + W₂ + W₃) = 0 := by omega
    rw [hzero]
    have hr0 : rBeyond (L := L) (K := K) 0 c₁ = c₁.card := by
      unfold rBeyond
      rw [Multiset.countP_eq_card]
      intro a ha
      exact ⟨(hall₁ a ha).1, Nat.zero_le _⟩
    rw [hr0]; omega
  · -- i large: run the checkpoint collapse from base = i - (W₁+W₂+W₃) at c₀.
    by_contra hcon
    rw [not_le] at hcon  -- 10 * rBeyond (i - (W₁+W₂+W₃)) c₁ < c₁.card
    set base := i - (W₁ + W₂ + W₃) with hbase
    -- At c₀, the fraction at base is < 1/10 (via mono and the endpoint subcriticality).
    have hbasec₀ : 10 * rBeyond (L := L) (K := K) base c₀ < c₀.card := by
      have := hmono base
      rw [hcard] at hcon
      omega
    set f : ℕ → ℝ := fun j => frac (L := L) (K := K) (base + j) c₀ with hfdef
    have hfnn : ∀ j, 0 ≤ f j := by
      intro j; simp only [hfdef, frac]; positivity
    have hrec : ∀ j, θ ≤ f j → f j ≤ 1 / 10 → f (j + 1) ≤ (f j) ^ 2 := by
      intro j hlo hhi
      simp only [hfdef] at hlo hhi ⊢
      have h := hwp₀ (base + j) hlo hhi
      rwa [show base + (j + 1) = (base + j) + 1 from by ring]
    have hf0 : f 0 ≤ 1 / 10 := by
      simp only [hfdef, Nat.add_zero, frac]
      rw [div_le_iff₀ hcardℝ]
      have : (10 : ℝ) * (rBeyond (L := L) (K := K) base c₀ : ℝ) < (c₀.card : ℝ) := by
        exact_mod_cast hbasec₀
      linarith
    -- The windowed collapse crosses the floor within W₁ levels at c₀.
    obtain ⟨j₀, hj₀le, hj₀⟩ :=
      FrontTail.windowed_floor_crossing hfnn hrec hf0 c₀.card hcard2 hθ
    simp only [hfdef] at hj₀
    -- ClimbBound at c₀ empties level base + j₀ + W₂.
    have hclimbEmpty : rBeyond (L := L) (K := K) (base + j₀ + W₂) c₀ = 0 := hclimb₀ (base + j₀) hj₀
    -- The endpoint bulk test at base + j₀ + W₂ is below n (antitone from base at c₁).
    have hbulkc₁ : 10 * rBeyond (L := L) (K := K) (base + j₀ + W₂) c₁ < c₀.card := by
      have hanti := MixedWindowClosure.rBeyond_antitone_threshold (L := L) (K := K)
        base (base + j₀ + W₂) (by omega) c₁
      rw [hcard] at hcon
      omega
    -- CrossEmptyClimbGood transports the emptiness W₃ levels up at c₁.
    have hcrossEmpty : rBeyond (L := L) (K := K) (base + j₀ + W₂ + W₃) c₁ = 0 :=
      hcross (base + j₀ + W₂) hclimbEmpty hbulkc₁
    -- base + j₀ + W₂ + W₃ ≤ i; antitone forces rBeyond i c₁ = 0, contradicting hi.
    have hle : base + j₀ + W₂ + W₃ ≤ i := by omega
    have hanti := MixedWindowClosure.rBeyond_antitone_threshold (L := L) (K := K)
      (base + j₀ + W₂ + W₃) i hle c₁
    omega

/-- **Stage 2b (width-to-width transport).**  The cleaner transport the checkpoint consumer needs:
from a checkpoint that ALREADY satisfies the scalar `GoodFrontWidth W` (the `r = 0` checkpoint feeder
`widthFail_chk_concrete` discharges its complement), level-wise monotonicity, and the cross-config
`CrossEmptyClimbGood`, the endpoint satisfies `GoodFrontWidth (W + W₃)`.

Mechanism: at the contradiction floor `10·rBeyond base c₁ < card`, monotonicity pushes the bulk below
`base` at the checkpoint `c₀`; the checkpoint width invariant's contrapositive empties level `base+W`
at `c₀`; `CrossEmptyClimbGood` transports the emptiness `W₃` levels up at `c₁`; antitonicity closes.
This consumes the checkpoint `GoodFrontWidth` directly (no profile/climb hypotheses), so the
checkpoint feeder is exactly `widthFail_chk_concrete`. -/
theorem goodFrontWidth_transport_of_width
    (W W₃ : ℕ)
    (c₀ c₁ : Config (AgentState L K))
    (hcard : c₁.card = c₀.card)
    (hall₁ : AllClockP3 (L := L) (K := K) c₁)
    (hmono : ∀ T, rBeyond (L := L) (K := K) T c₀ ≤ rBeyond (L := L) (K := K) T c₁)
    (hgood₀ : GoodFrontWidth (L := L) (K := K) W c₀)
    (hcross : CrossEmptyClimbGood (L := L) (K := K) c₀.card W₃ c₀ c₁) :
    GoodFrontWidth (L := L) (K := K) (W + W₃) c₁ := by
  intro i hi
  -- `rBeyond 0 c₁ = card` (all agents are clocks at level ≥ 0): handles the small-`i` band.
  have hr0 : rBeyond (L := L) (K := K) 0 c₁ = c₁.card := by
    unfold rBeyond
    rw [Multiset.countP_eq_card]
    intro a ha
    exact ⟨(hall₁ a ha).1, Nat.zero_le _⟩
  by_cases hiW : i ≤ W + W₃
  · -- small `i`: base = 0, and `10 * rBeyond 0 c₁ = 10 * card ≥ card`.
    have hzero : i - (W + W₃) = 0 := by omega
    rw [hzero, hr0]; omega
  by_contra hcon
  rw [not_le] at hcon  -- 10 * rBeyond (i - (W+W₃)) c₁ < c₁.card
  set base := i - (W + W₃) with hbase
  -- monotonicity pushes the bulk below `base` at the checkpoint.
  have hbasec₀ : 10 * rBeyond (L := L) (K := K) base c₀ < c₀.card := by
    have := hmono base; rw [hcard] at hcon; omega
  -- checkpoint width contrapositive: level base + W is empty at c₀.
  have hgwEmpty : rBeyond (L := L) (K := K) (base + W) c₀ = 0 := by
    by_contra hpos
    have hpos' : 0 < rBeyond (L := L) (K := K) (base + W) c₀ := Nat.pos_of_ne_zero hpos
    have hw := hgood₀ (base + W) hpos'
    simp only [Nat.add_sub_cancel] at hw
    omega
  -- the endpoint bulk test at base + W is below card (antitone from base at c₁).
  have hbulkc₁ : 10 * rBeyond (L := L) (K := K) (base + W) c₁ < c₀.card := by
    have hanti := MixedWindowClosure.rBeyond_antitone_threshold (L := L) (K := K)
      base (base + W) (by omega) c₁
    rw [hcard] at hcon; omega
  -- CrossEmptyClimbGood transports the emptiness W₃ levels up at c₁.
  have hcrossEmpty : rBeyond (L := L) (K := K) (base + W + W₃) c₁ = 0 :=
    hcross (base + W) hgwEmpty hbulkc₁
  have hle : base + W + W₃ ≤ i := by omega
  have hanti := MixedWindowClosure.rBeyond_antitone_threshold (L := L) (K := K)
    (base + W + W₃) i hle c₁
  omega

end ClockFrontProfile

/-! ## Stage 3 — the probabilistic complement `CrossEmptyClimbBad` + `crossEmptyClimb_whp`. -/

namespace EarlyDripMarked

open MeasureTheory ProbabilityTheory
open ClockRealKernel
open scoped ENNReal NNReal Real BigOperators Classical

variable {L K : ℕ}

/-- **`CrossEmptyClimbBad`** — the bad event for within-window transport: some checkpoint-empty level
`k < Tcap` is still below the bulk threshold at the endpoint, yet level `k + W₃` has become nonempty.
The bulk test uses the climb threshold `θn` (instantiated downstream as the bulk floor). -/
def CrossEmptyClimbBad
    (θn W₃ Tcap : ℕ) (c₀ : Config (AgentState L K)) :
    Set (Config (AgentState L K)) :=
  {c | ∃ k < Tcap,
    rBeyond (L := L) (K := K) k c₀ = 0 ∧
    rBeyond (L := L) (K := K) k c < θn ∧
    0 < rBeyond (L := L) (K := K) (k + W₃) c}

/-- **Stage 3 (within-window climb transport, whp).**  By unioning `ClimbTail.climb_real_tail` over
levels `k < Tcap`, with the climb threshold `θn`, the `CrossEmptyClimbBad` mass after `r` real-kernel
steps is bounded by the level-sum of gated climb tails. -/
theorem crossEmptyClimb_whp
    (θn W₃ Tcap B' r : ℕ) (hW₃ : 2 ≤ W₃)
    (s : ℝ) (hs : 0 ≤ s)
    (c₀ : Config (AgentState L K)) :
    ((NonuniformMajority L K).transitionKernel ^ r) c₀
        (CrossEmptyClimbBad (L := L) (K := K) θn W₃ Tcap c₀)
      ≤
    ∑ k ∈ Finset.range Tcap,
      ((GatedDrift.killK ((NonuniformMajority L K).transitionKernel)
          (ClimbTail.climbGate (L := L) (K := K) θn k B' θn) ^ r)
          (some c₀) {none}
       +
       (ENNReal.ofReal
          (1 + ((B' : ℝ) / (θn : ℝ)) ^ 2 * (Real.exp s - 1))) ^ r
        * ClimbTail.climbPot (L := L) (K := K) k θn s c₀
        / ENNReal.ofReal (Real.exp (s * ((W₃ : ℝ) - 1)))) := by
  classical
  have hsub : CrossEmptyClimbBad (L := L) (K := K) θn W₃ Tcap c₀
      ⊆ ⋃ k ∈ Finset.range Tcap,
          {c | rBeyond (L := L) (K := K) k c < θn ∧
            0 < rBeyond (L := L) (K := K) (k + W₃) c} := by
    intro c hc
    obtain ⟨k, hk, _hempty, hlt, hpos⟩ := hc
    rw [Set.mem_iUnion₂]
    exact ⟨k, Finset.mem_range.mpr hk, ⟨hlt, hpos⟩⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  apply Finset.sum_le_sum
  intro k _
  exact ClimbTail.climb_real_tail (L := L) (K := K) θn k B' θn W₃ hW₃ s hs r c₀

/-! ## Stage 4 — the within-window monotone lift (the `hmono` feeder for the transport).

The deterministic transport (Stage 2) consumes `hmono : ∀ T, rBeyond T c₀ ≤ rBeyond T c₁`.  Over `r`
real-kernel steps from a checkpoint `y ∈ AllClockGE3`, this holds a.e. for the endpoint, by iterating
the absorbing-window per-step monotone `ClockRealKernel.rBeyondGE3_ge_monotone`. -/

/-- **Stage 4 helper (iterated within-window monotone).**  Over `r` steps of the real kernel from a
window state `y ∈ AllClockGE3`, a.e. endpoint `c'` satisfies `rBeyond T y ≤ rBeyond T c'` for the
fixed level `T` — the absorbing-window growth, iterated.  (The invariant carried is
`fun c' => rBeyond T y ≤ rBeyond T c' ∧ AllClockGE3 c'`, support-closed via `rBeyondGE3_ge_monotone`
+ `AllClockGE3_absorbing`.) -/
theorem ae_rBeyond_ge_pow (T : ℕ) (y : Config (AgentState L K))
    (hge3 : AllClockGE3 (L := L) (K := K) y) (r : ℕ) :
    ∀ᵐ c' ∂(((NonuniformMajority L K).transitionKernel) ^ r) y,
      rBeyond (L := L) (K := K) T y ≤ rBeyond (L := L) (K := K) T c' := by
  have hjoint : ∀ᵐ c' ∂(((NonuniformMajority L K).transitionKernel) ^ r) y,
      (rBeyond (L := L) (K := K) T y ≤ rBeyond (L := L) (K := K) T c'
        ∧ AllClockGE3 (L := L) (K := K) c') := by
    refine Protocol.ae_of_stepDistOrSelf_support_preserved
      (P := NonuniformMajority L K)
      (Q := fun c' => rBeyond (L := L) (K := K) T y ≤ rBeyond (L := L) (K := K) T c'
        ∧ AllClockGE3 (L := L) (K := K) c')
      ?_ y ⟨le_rfl, hge3⟩ r
    intro a b ⟨hle, hga⟩ hsupp
    exact ⟨rBeyondGE3_ge_monotone (L := L) (K := K) T (rBeyond (L := L) (K := K) T y) a b hga hle hsupp,
      AllClockGE3_absorbing (L := L) (K := K) a b hga hsupp⟩
  filter_upwards [hjoint] with c' hc' using hc'.1

/-! ## Stage 4 — the checkpoint-to-checkpoint assembly: the generic CK reduction.

The endpoint width-failure mass at the free horizon `w·j + r` is bounded, via Chapman–Kolmogorov
(`CrossHourSide.checkpoint_side_le` at `t := w·j`, `r := r`), by the `δRem`-free checkpoint feeder
`εWAt_chk` (the checkpoint-BAD part, `CrossHourSide.widthFail_chk_concrete`) plus the within-window
climb tail (the checkpoint-GOOD part).  We expose this in the exact `checkpoint_side_le` interface the
side consumers (`hLocal` in `CrossHourSide.hside_concrete_bounded`) already use: the checkpoint-BAD
obligation `hBad` and the per-checkpoint-good-state tail obligation `hTail` are carried as hypotheses.

This is the genuine consumer-facing shape.  **Recorded discrepancy:** the blueprint's flattened RHS
(climb sum re-based at `erase mc₀` over `r` steps) is NOT provable as written — Chapman–Kolmogorov
yields the tail integrated against the checkpoint distribution, which does not collapse to a single
start-config climb sum.  The genuine within-window tail is per-checkpoint-state (the `hTail` shape
here, matching `hLocal`), discharged by the transport `goodFrontWidth_transport_of_width` + the
within-window `crossEmptyClimb_whp` at each checkpoint-good state.  See `HANDOFF_WFP_TRANSPORT.md`
status section for the residual threshold-form bridge (`10·rBeyond < n` cardinality vs `< θn`). -/

/-- **`widthFail_between_checkpoints` (generic CK reduction).**  In the exact `checkpoint_side_le`
shape: with `Entry` the checkpoint-good set, `εBad` bounding the checkpoint-BAD mass at horizon `w·j`,
and `εTail` bounding the within-window endpoint width-failure tail from each checkpoint-good state
over `r` steps, the endpoint width-failure mass at horizon `w·j + r` is `≤ εBad + εTail`.

Discharge `εBad` with `CrossHourSide.widthFail_chk_concrete` (= `εWAt_chk`, taking `Entryᶜ ⊇` its
event) and `εTail` per checkpoint-good state with `crossEmptyClimb_whp` via the transport. -/
theorem widthFail_between_checkpoints
    (n r : ℕ) (j : ℕ)
    (mc₀ : Config (MarkedAgent L K))
    (Entry Bad : Set (Config (AgentState L K)))
    (εBad εTail : ℝ≥0∞)
    (hBad : (ClockKilledMinute.realκ L K ^ (Params.w n * j))
        (eraseConfig (L := L) (K := K) mc₀) Entryᶜ ≤ εBad)
    (hTail : ∀ y ∈ Entry,
      (ClockKilledMinute.realκ L K ^ r) y Bad ≤ εTail) :
    (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀) Bad
      ≤ εBad + εTail :=
  checkpoint_side_le (κ := ClockKilledMinute.realκ L K)
    Entry Bad (Params.w n * j) r (eraseConfig (L := L) (K := K) mc₀) εBad εTail hBad hTail

open ClockFrontProfile in
/-- **`widthFail_between_checkpoints_concrete` — consumer demonstration.**  Instantiates the generic
CK reduction with the checkpoint-good set `Entry := {c | WidthSideP n c → GoodFrontWidth (W₁+W₂) c}`,
so that `Entryᶜ = {WidthSideP n ∧ ¬GoodFrontWidth (W₁+W₂)}` is EXACTLY the event bounded by
`CrossHourSide.widthFail_chk_concrete` (= `εWAt_chk`).  The endpoint Bad event is the widened
`{WidthSideP n ∧ ¬GoodFrontWidth (W₁+W₂+W₃)}`.  The checkpoint-BAD obligation is discharged cleanly by
`widthFail_chk_concrete`; the within-window tail is carried as `hTail` (the per-checkpoint-good-state
climb tail, dischargeable by `crossEmptyClimb_whp` via `goodFrontWidth_transport_of_width` — see the
handoff residual note on the threshold-form bridge).  This is the consumer-facing assembly shape. -/
theorem widthFail_between_checkpoints_concrete
    (n : ℕ) (hn : Params.N₀ ≤ n)
    (mc₀ : Config (MarkedAgent L K))
    (hcard : mc₀.card = n)
    (hge3 : AllClockGE3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hnotP3 : ¬ AllClockP3 (L := L) (K := K) (eraseConfig (L := L) (K := K) mc₀))
    (hclean : ∀ m ∈ mc₀, m.2 = false)
    (Tcap : ℕ) (hcap : ClockFrontShape.capMinute (L := L) (K := K) < Tcap)
    (W₂ W₃ : ℕ) (hW₂ : 2 ≤ W₂)
    (B' : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (j r : ℕ) (hjKK : j ≤ Params.KK L K - 1)
    (εTail : ℝ≥0∞)
    (hTail : ∀ y ∈ {c : Config (AgentState L K) |
        ClockBudgets.WidthSideP (L := L) (K := K) n c →
          GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c},
      (ClockKilledMinute.realκ L K ^ r) y
        {c | ClockBudgets.WidthSideP (L := L) (K := K) n c ∧
          ¬ GoodFrontWidth (L := L) (K := K)
            (FrontTail.frontWidthBound n + W₂ + W₃) c} ≤ εTail) :
    (ClockKilledMinute.realκ L K ^ (Params.w n * j + r))
        (eraseConfig (L := L) (K := K) mc₀)
        {c | ClockBudgets.WidthSideP (L := L) (K := K) n c ∧
          ¬ GoodFrontWidth (L := L) (K := K)
            (FrontTail.frontWidthBound n + W₂ + W₃) c}
      ≤ εWAt_chk (L := L) (K := K) n mc₀ Tcap W₂ B' s j + εTail := by
  -- Checkpoint-BAD: `Entryᶜ = {WidthSideP ∧ ¬GoodFrontWidth (W₁+W₂)}` = the `widthFail_chk` event.
  have hBad : (ClockKilledMinute.realκ L K ^ (Params.w n * j))
      (eraseConfig (L := L) (K := K) mc₀)
      {c : Config (AgentState L K) |
        ClockBudgets.WidthSideP (L := L) (K := K) n c →
          GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c}ᶜ
      ≤ εWAt_chk (L := L) (K := K) n mc₀ Tcap W₂ B' s j := by
    have hset : ({c : Config (AgentState L K) |
        ClockBudgets.WidthSideP (L := L) (K := K) n c →
          GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c}ᶜ)
        = {c | ClockBudgets.WidthSideP (L := L) (K := K) n c ∧
            ¬ GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c} := by
      ext c
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      exact Classical.not_imp
    rw [hset]
    have := widthFail_chk_concrete (L := L) (K := K) n hn mc₀ hcard hge3 hnotP3 hclean
      Tcap hcap W₂ hW₂ B' s hs j hjKK
    rwa [Nat.add_zero] at this
  exact checkpoint_side_le (κ := ClockKilledMinute.realκ L K)
    {c | ClockBudgets.WidthSideP (L := L) (K := K) n c →
        GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂) c}
    {c | ClockBudgets.WidthSideP (L := L) (K := K) n c ∧
        ¬ GoodFrontWidth (L := L) (K := K) (FrontTail.frontWidthBound n + W₂ + W₃) c}
    (Params.w n * j) r (eraseConfig (L := L) (K := K) mc₀)
    (εWAt_chk (L := L) (K := K) n mc₀ Tcap W₂ B' s j) εTail hBad hTail

end EarlyDripMarked

end Ripple.PopulationProtocol.ExactMajority
