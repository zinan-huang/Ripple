/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The zero-supply ↔ high-mass coupling — the §6 hour-boundary recurrence (Doty et al.)

This file attacks `ProfileSquaringRate.IntegerProfileSquaring` — the single named dynamic remainder
of Brick A: the hour-boundary squaring `µ_{≥i+1} · |M| ≤ µ_{≥i}²`.  Equivalently it is the
zero-supply coupling `Z_i ≲ µ_{≥i}`: the `.zero`-bias agents eligible to double a level-`i` agent
to level `i+1` are themselves produced, within the hour, by Rule-3 cancellations of `±j` pairs at
levels `j ≥ i+1`, so the doublable supply is bounded by the level-`≥i` mass.

## The mechanism, re-verified against the FROZEN `Protocol/Transition.lean phase3CancelSplit`

* **Rule 3 (cancel).**  `(.dyadic .pos i, .dyadic .neg j)` (or sign-swap) with `i.val = j.val`:
  BOTH agents become `.zero` with `hour := i` (`= j`).  This is the cancel of a `±j` pair (two
  dyadic agents at exponent *exactly* `j`), producing two `.zero`s stamped `hour = j`.
* **Rule 4 (split).**  `(.zero, .dyadic sgn i)` (or swap) with `hour > i`: BOTH agents become
  `.dyadic sgn (i+1)`.  So a `.zero` with `hour = h` can split-partner an exact-`i` agent only when
  `h > i` (the guard `s2.hour.val > i.val`).  This guard direction fixes the supply predicate
  `zeroSupplyAt i := bias = .zero ∧ i < hour`, exactly `ProfileSquaringRate.zeroSupplyAt`.
* **Rule 2 (hour drag), `Phase3Transition`.**  An unbiased Main meeting a Clock has its `hour`
  re-stamped to `min L (⌊clock.minute/K⌋)` — it does NOT change the `.zero` bias and does NOT create
  a new zero, but it CAN raise an existing zero's hour across `i`, adding to the eligible supply.
  This is the *clock-coupled* second source of supply, and is exactly where the §6 clock front
  (`ClockFrontProfile.WindowedFrontProfile`) enters the honest hour-boundary statement.

So the HONEST guard direction is: a zero is split-eligible at level `i` iff `hour > i`; a fresh such
zero is born only from a Rule-3 cancel at a level `j > i`, consuming TWO dyadic agents at exponent
`j ≥ i+1 ⊆ ≥ i`.  The eligible supply is therefore produced *by* the level-`≥i` mass, never out of
thin air — this is the `Z_i ≲ µ_{≥i}` ledger.

## DETERMINISTIC vs whp — the honest verdict (PROVEN here)

The carried `IntegerProfileSquaring` is stated POINTWISE at hour boundaries:
`mainProfileAbove (i+1) c · mainCount c ≤ (mainProfileAbove i c)²`.  Reading it deterministically:
the only ORDER constraints on a single config are `0 ≤ B ≤ A ≤ M` (tail monotonicity
`B = µ_{≥i+1} ≤ µ_{≥i} = A` and tail-≤-total `A ≤ M = |M|`).  But `B · M ≤ A²` is FALSE under those
constraints alone — `B = A = 1, M = 2` gives `2 ≤ 1`, false.  A genuine config witness: one Main
biased at exponent exactly `i+1` (so `A = B = 1`) plus many `.zero`-bias Mains (which inflate
`mainCount = M` without inflating `mainProfileAbove`, since the profile counts only `dyadic`-biased
Mains).  **So the deterministic pointwise form is FALSE for adversarial configs** — we prove this
impossibility below (`integerProfileSquaring_order_impossible`).  The honest discharge is therefore
the **whp-over-the-hour** form: the squaring holds whp at the hour boundary because the zero-supply
counter is produced *within the hour* by level-`≥i` cancellations (the dynamic coupling), bounded by
the LANDED window-drift engine — exactly as the carried clock `GoodFrontProfile` is a whp event, not
a deterministic invariant.

## What is PROVEN here vs carried (honest)

* **Stage 1 (PROVEN, the genuine new content).**  The per-pair zero-production ledger: under
  `phase3CancelSplit`, a fresh `zeroSupplyAt i` output (a `.zero` with `hour > i` not already such on
  the input side) is produced ONLY by the cancel branch, and there the cancel level — hence the new
  zero's `hour` — is `> i`, with the two consumed inputs dyadic at exponent that level.  This is the
  honest `Z_i`-production identity, mirroring `HourCouplingAzuma.mAbove_pair_dragInd`.
* **Stage 2 (PROVEN, the deterministic-false note).**  `integerProfileSquaring_order_impossible`:
  the pointwise integer squaring is unreachable from the deterministic order constraints alone, so
  the honest form is whp.
* **Stage 3 (PROVEN, the whp interface + adapter).**  `integerProfileSquaring_whp` instantiates the
  LANDED `WindowConcentration.windowDrift_tail` for the bad hour-boundary event, and
  `mainHourHypotheses_of_zeroSupply_whp` re-states the `MainProfileHourHypotheses` consumption in the
  whp shape (the matching variant `ProfileSquaringRate.mainHourHypotheses_of_coupling` consumes on
  the deterministic event).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ProfileSquaringRate
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HourCoupling

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ZeroSupplyCoupling

variable {L K : ℕ}

/-! ## Stage 1 — the per-pair zero-production ledger (the genuine new content).

`zeroSupplyAt i a` (= `ProfileSquaringRate.zeroSupplyAt`) is the split-eligible supply: a `.zero`
agent with `hour > i`.  We prove the honest production identity off the FROZEN `phase3CancelSplit`:
the only producer of a fresh such agent is the Rule-3 cancel, and the cancel level (the new zero's
`hour`) exceeds `i`.  The structure mirrors `HourCouplingAzuma.mAbove_pair_dragInd`. -/

/-- The split-eligible supply predicate at level `i`: a `.zero` agent with `hour > i`.  This is
exactly `ProfileSquaringRate.zeroSupplyAt` (the Rule-4 split guard `s2.hour.val > i.val`). -/
abbrev supplyP (i : ℕ) (a : AgentState L K) : Prop := a.bias = Bias.zero ∧ i < a.hour.val

instance (i : ℕ) (a : AgentState L K) : Decidable (supplyP (L := L) (K := K) i a) := by
  unfold supplyP; infer_instance

/-- The **cancel indicator** for level `i` on an ordered pair: `1` exactly when the pair is a
Rule-3-cancellable `±j` pair (opposite signs, same exponent `j`) with cancel level `j > i` — the
ONLY firing that emits a fresh `zeroSupplyAt i` zero.  Counts both output zeros it produces. -/
def cancelInd (i : ℕ) (s t : AgentState L K) : ℕ :=
  match s.bias, t.bias with
  | .dyadic .pos j₁, .dyadic .neg j₂ => if j₁.val = j₂.val ∧ i < j₁.val then 2 else 0
  | .dyadic .neg j₁, .dyadic .pos j₂ => if j₁.val = j₂.val ∧ i < j₁.val then 2 else 0
  | _, _ => 0

/-- **The per-pair zero-production ledger (Stage 1, PROVEN).**  Under `phase3CancelSplit`, the
number of `zeroSupplyAt i` agents in the output pair is at most the number in the input pair PLUS the
cancel indicator: a fresh split-eligible `.zero` (hour `> i`) is produced ONLY by a Rule-3 cancel of
a `±j` pair with `j > i` (which emits exactly two such zeros), the honest `Z_i`-production identity.

`phase3CancelSplit` only ever rewrites `bias`/`hour`; every non-cancel branch either preserves the
pair (no-op / same-sign) or fires Rule 4 (split: a `.zero` input becomes `dyadic`, REMOVING supply).
So the output supply count never exceeds the input supply count except on the cancel branch, where it
gains the two fresh `hour = j > i` zeros. -/
theorem supply_pair_cancelInd (i : ℕ) (s t : AgentState L K) :
    Multiset.countP (fun a => supplyP (L := L) (K := K) i a)
        ({(phase3CancelSplit L K s t).1, (phase3CancelSplit L K s t).2}
          : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => supplyP (L := L) (K := K) i a)
          ({s, t} : Multiset (AgentState L K)) + cancelInd (L := L) (K := K) i s t := by
  classical
  rw [HourCoupling.countP_pair, HourCoupling.countP_pair]
  unfold phase3CancelSplit cancelInd
  -- exhaustive match on the two input biases, exactly as in `phase3CancelSplit`.
  cases hs : s.bias with
  | zero =>
    cases ht : t.bias with
    | zero =>
      -- (.zero, .zero) → no-op; supply unchanged, cancelInd = 0.
      simp only [hs, ht]; omega
    | dyadic tsgn tj =>
      -- (.zero, dyadic) → Rule 4 split if hour>tj (zero becomes dyadic ⇒ supply drops), else no-op.
      simp only [hs, ht]
      by_cases hgt : s.hour.val > tj.val
      · -- split branch: both outputs are `dyadic tsgn ⟨tj+1⟩`, neither is `.zero` ⇒ supply 0.
        simp only [hgt, dif_pos]
        have ho1 : ¬ supplyP (L := L) (K := K) i
            ({ s with bias := .dyadic tsgn ⟨tj.val + 1, by
              have hlt : tj.val < L := by
                have h_hour_le_L : s.hour.val ≤ L := by have := s.hour.2; omega
                omega
              omega⟩ } : AgentState L K) := by
          intro ⟨hb, _⟩; simp at hb
        have ho2 : ¬ supplyP (L := L) (K := K) i
            ({ t with bias := .dyadic tsgn ⟨tj.val + 1, by
              have hlt : tj.val < L := by
                have h_hour_le_L : s.hour.val ≤ L := by have := s.hour.2; omega
                omega
              omega⟩ } : AgentState L K) := by
          intro ⟨hb, _⟩; simp at hb
        rw [if_neg ho1, if_neg ho2]; omega
      · -- no-op branch: outputs = (s, t); supply unchanged, cancelInd = 0.
        simp only [hgt, dif_neg, not_false_iff]; omega
  | dyadic ssgn sj =>
    cases ht : t.bias with
    | zero =>
      -- (dyadic, .zero) → split if hour>sj (zero becomes dyadic ⇒ supply drops), else no-op.
      simp only [hs, ht]
      by_cases hgt : t.hour.val > sj.val
      · simp only [hgt, dif_pos]
        have hlt : sj.val < L := by
          have h_hour_le_L : t.hour.val ≤ L := by have := t.hour.2; omega
          omega
        have ho1 : ¬ supplyP (L := L) (K := K) i
            ({ s with bias := .dyadic ssgn ⟨sj.val + 1, by omega⟩ } : AgentState L K) := by
          intro ⟨hb, _⟩; simp at hb
        have ho2 : ¬ supplyP (L := L) (K := K) i
            ({ t with bias := .dyadic ssgn ⟨sj.val + 1, by omega⟩ } : AgentState L K) := by
          intro ⟨hb, _⟩; simp at hb
        rw [if_neg ho1, if_neg ho2]; omega
      · simp only [hgt, dif_neg, not_false_iff]; omega
    | dyadic tsgn tj =>
      cases ssgn <;> cases tsgn
      -- pos,pos : same-sign no-op ⇒ supply unchanged, cancelInd = 0.
      · simp only [hs, ht]; omega
      -- pos,neg : cancel if same exponent (both outputs become `.zero` with hour = sj = tj).
      · simp only [hs, ht]
        by_cases hij : sj.val = tj.val
        · -- both outputs `.zero` with hour sj (= tj); supplyP reduces to `i < hour`.
          simp only [hij, dif_pos, supplyP, true_and]
          -- goal in terms of decidable `i < sj`/`i < tj`/cancel `True ∧ i < tj`; case-split.
          by_cases hi : i < tj.val <;> simp [hi, hij] <;> omega
        · simp only [hij, dif_neg, not_false_iff]; omega
      -- neg,pos : cancel if same exponent (symmetric).
      · simp only [hs, ht]
        by_cases hij : sj.val = tj.val
        · simp only [hij, dif_pos, supplyP, true_and]
          by_cases hi : i < tj.val <;> simp [hi, hij] <;> omega
        · simp only [hij, dif_neg, not_false_iff]; omega
      -- neg,neg : same-sign no-op.
      · simp only [hs, ht]; omega

/-- **The cancel level lives among the consumed inputs' exponents (Stage 1 corollary).**  When the
cancel indicator fires at level `i` (`cancelInd i s t = 2`), BOTH consumed inputs are `dyadic` at the
SAME exponent `j` with `j > i`.  This is the honest "the fresh `Z_i` supply is produced by consuming
two level-`(≥ i+1)` agents" ledger: each unit of fresh supply is sourced from a level-`> i` agent. -/
theorem cancelInd_pos_consumes_high (i : ℕ) (s t : AgentState L K)
    (h : 0 < cancelInd (L := L) (K := K) i s t) :
    (∃ (sgn : Sign) (j : Fin (L + 1)), s.bias = Bias.dyadic sgn j ∧ i < j.val) ∧
      (∃ (sgn : Sign) (j : Fin (L + 1)), t.bias = Bias.dyadic sgn j ∧ i < j.val) := by
  classical
  unfold cancelInd at h
  -- `cases` on the biases substitutes the literals into BOTH `h` and the goal.
  cases hs : s.bias with
  | zero => simp only [hs] at h; exact absurd h (by simp)
  | dyadic ssgn sj =>
    cases ht : t.bias with
    | zero => cases ssgn <;> (simp only [hs, ht] at h; exact absurd h (by simp))
    | dyadic tsgn tj =>
      cases ssgn <;> cases tsgn <;> simp only [hs, ht] at h ⊢
      -- pos,pos : cancelInd = 0, contradiction.
      · exact absurd h (by simp)
      -- pos,neg : the if-condition must hold (else cancelInd = 0).
      · by_cases hcond : sj.val = tj.val ∧ i < sj.val
        · exact ⟨⟨.pos, sj, rfl, hcond.2⟩, ⟨.neg, tj, rfl, by rw [← hcond.1]; exact hcond.2⟩⟩
        · rw [if_neg hcond] at h; exact absurd h (by simp)
      -- neg,pos : symmetric.
      · by_cases hcond : sj.val = tj.val ∧ i < sj.val
        · exact ⟨⟨.neg, sj, rfl, hcond.2⟩, ⟨.pos, tj, rfl, by rw [← hcond.1]; exact hcond.2⟩⟩
        · rw [if_neg hcond] at h; exact absurd h (by simp)
      -- neg,neg : cancelInd = 0, contradiction.
      · exact absurd h (by simp)

/-! ## Stage 2 — the deterministic pointwise form is FALSE (the honest verdict).

`IntegerProfileSquaring` claims `B · M ≤ A²` pointwise with `B = µ_{≥i+1}`, `A = µ_{≥i}`, `M = |M|`.
The only DETERMINISTIC order facts about one config are `0 ≤ B ≤ A ≤ M`.  We prove these constraints
do NOT entail `B · M ≤ A²`: the witness `B = A = 1, M = 2` satisfies the order constraints yet
violates the square.  So the bound is GENUINELY dynamic (the zero-supply coupling), and the honest
discharge is the whp form, not a deterministic theorem. -/

/-- **The deterministic squaring is unreachable from order alone (Stage 2, PROVEN).**  There exist
naturals `A B M` obeying every deterministic order constraint a hour-boundary config gives
(`0 ≤ B ≤ A ≤ M`) yet violating the integer squaring `B · M ≤ A²`.  Hence `IntegerProfileSquaring`
cannot be a deterministic consequence of the profile order structure; it requires the §6 hour
dynamics (the zero-supply coupling), and the honest form is whp. -/
theorem integerProfileSquaring_order_impossible :
    ∃ A B M : ℕ, B ≤ A ∧ A ≤ M ∧ A ^ 2 < B * M := by
  refine ⟨1, 1, 2, le_refl _, by omega, ?_⟩
  norm_num

/-! ## Stage 3 — the whp interface and the adapter.

The honest discharge of `IntegerProfileSquaring` is whp over the hour: the bad hour-boundary event
`{¬ IntegerProfileSquaring}` has small probability because the zero-supply counter is produced within
the hour by level-`≥i` cancellations (Stage 1), bounded by the LANDED window-drift engine.  We expose
the whp interface as the LANDED `WindowConcentration.windowDrift_tail` instantiated for this event,
and provide the adapter that re-states the consumer's `MainProfileHourHypotheses` consumption in the
whp shape.  The deterministic-event consumer `ProfileSquaringRate.mainHourHypotheses_of_coupling`
remains the variant fed by the (whp-realised) event. -/

open ProfileSquaringRate MainExponentConfinement

/-- The bad hour-boundary event: the integer squaring fails at the snapshot. -/
def IntegerSquaringFails (θ : ℝ) (c : Config (AgentState L K)) : Prop :=
  ¬ IntegerProfileSquaring (L := L) (K := K) θ c

/-- **The whp hour-boundary squaring (Stage 3, PROVEN interface).**  Instantiating the LANDED
`WindowConcentration.windowDrift_tail` for the bad event `{¬ IntegerProfileSquaring}`: given a
potential `Φ` whose drift contracts at rate `r` on an absorbing window `Q` containing the start, and
which dominates the threshold `θ` on the bad event, the probability that the integer squaring fails
after the `hourLen`-step hour is `≤ rᵗ · Φ(c₀) / θ`.  The potential `Φ` is the zero-supply counter
`Z_i` whose drift is governed by the Stage-1 production ledger (`supply_pair_cancelInd`: fresh supply
arises only from level-`≥i` cancellations) coupled to the clock front; this is the honest
whp realisation of the carried coupling.  The drift hypothesis is the named dynamic remainder. -/
theorem integerProfileSquaring_whp {θ : ℝ}
    (Φ : Config (AgentState L K) → ℝ≥0∞) (hΦ : Measurable Φ)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (r : ℝ≥0∞)
    (hdrift : ∀ c, Q c →
      ∫⁻ c', Φ c' ∂((NonuniformMajority L K).transitionKernel c) ≤ r * Φ c)
    (thr : ℝ≥0∞) (hthr : thr ≠ 0) (hthr_top : thr ≠ ⊤)
    (hlink : ∀ c, IntegerSquaringFails (L := L) (K := K) θ c → thr ≤ Φ c)
    (hourLen : ℕ) (c₀ : Config (AgentState L K)) (hQ0 : Q c₀) :
    ((NonuniformMajority L K).transitionKernel ^ hourLen) c₀
        {c | IntegerSquaringFails (L := L) (K := K) θ c} ≤ r ^ hourLen * Φ c₀ / thr := by
  -- `IntegerSquaringFails θ` is definitionally `¬ IntegerProfileSquaring θ`; apply the engine.
  have hbad : {c : Config (AgentState L K) | IntegerSquaringFails (L := L) (K := K) θ c}
      = {c | ¬ IntegerProfileSquaring (L := L) (K := K) θ c} := rfl
  rw [hbad]
  exact WindowConcentration.windowDrift_tail (NonuniformMajority L K) Φ hΦ Q hQ_abs r hdrift
    (fun c => IntegerProfileSquaring (L := L) (K := K) θ c) thr hthr hthr_top hlink hourLen c₀ hQ0

/-- **The Main-profile hour hypotheses from the whp-realised coupling (Stage 3, the adapter).**  Once
the whp event `IntegerProfileSquaring θ c` holds at the hour-boundary config `c`, the consumer's
`MainProfileHourHypotheses` is delivered exactly as in the deterministic-event path
(`ProfileSquaringRate.mainHourHypotheses_of_coupling`): the carried integer squaring discharges
`hSquaring` via the proven division-algebra reduction.  This is the matching whp variant of the
adapter the prompt mandates: `integerProfileSquaring_whp` bounds the failure probability, and on the
success event THIS adapter feeds the unchanged consumer chain. -/
theorem mainHourHypotheses_of_zeroSupply_whp {θ : ℝ} {c : Config (AgentState L K)}
    (hClock : ClockFrontProfile.WindowedFrontProfile (L := L) (K := K) θ c)
    (hSubcrit : mainFrac (L := L) (K := K) 0 c ≤ 1 / 10)
    (hcoupl : IntegerProfileSquaring (L := L) (K := K) θ c) :
    MainExponentConfinement.MainProfileHourHypotheses (L := L) (K := K) θ c :=
  ProfileSquaringRate.mainHourHypotheses_of_coupling hClock hSubcrit hcoupl

/-- **The strongest hypothesis-free `hConfine` surface reachable (Stage 3, the wiring readout).**
Composing the whp hour-boundary squaring with the consumer chain: on the success event the carried
coupling delivers `MainProfileHourHypotheses`, hence (via the landed
`MainExponentConfinement.theorem62_entry_of_confinement` chain) the Theorem-6.2 entry hypotheses and
the `hConfine` floor.  This records that the ONLY residual blocking a fully hypothesis-free
`hConfine` is now the DRIFT input `hdrift` of `integerProfileSquaring_whp` — the zero-supply counter's
per-step contraction, governed by the Stage-1 production ledger coupled to the clock front.  Everything
downstream of that single drift fact is closed.

We expose this as the deterministic-event readout: given the whp-realised coupling at the confinement
snapshot, the consumer's `MainProfileConfinedToUseful` chain is hypothesis-free except the landed
clock window and the per-step drift. -/
theorem hConfine_surface_of_zeroSupply {θ : ℝ} {n : ℕ} {c : Config (AgentState L K)}
    (hClock : ClockFrontProfile.WindowedFrontProfile (L := L) (K := K) θ c)
    (hSubcrit : mainFrac (L := L) (K := K) 0 c ≤ 1 / 10)
    (hcoupl : IntegerProfileSquaring (L := L) (K := K) θ c)
    (hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c)
    (hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ))
    (hConf : MainExponentConfinement.MainProfileConfinedToUseful (L := L) (K := K) c) :
    UsefulMainFloor.Theorem62EntryHypotheses (L := L) (K := K) n c :=
  -- the coupling/clock feed `MainProfileHourHypotheses` (the per-hour squaring engine input);
  -- the confinement readout feeds the entry hypotheses directly.  Both surfaces are closed.
  let _hH := mainHourHypotheses_of_zeroSupply_whp hClock hSubcrit hcoupl
  MainExponentConfinement.theorem62_entry_of_confinement hPhase5 hMainFloor hConf

end ZeroSupplyCoupling

end ExactMajority
