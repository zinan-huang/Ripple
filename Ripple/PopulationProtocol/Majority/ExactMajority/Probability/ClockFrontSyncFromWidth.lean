import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockFrontProfile

/-!
# ClockFrontSyncFromWidth — endpoint FrontSync whp from `GoodFrontWidth` whp (Phase B bridge)

The §6 engine (`EarlyDripMarked.goodFrontWidth_whp`) delivers the moving-frame width
invariant `GoodFrontWidth (frontWidthBound n + W₂)` as an ENDPOINT whp event on the real
kernel.  This file is the deterministic-glue bridge from that event to the clock's
FrontSync-shaped endpoint events, replacing the FALSE `hwin_all`/`hfeeder_all`-style
carried windows (`FrontSyncConc.FrontFeederWindow`, `ClockFrontWidth.RFeederCapWindow`,
`ClockJointInduction`'s empty cap−1 feeder) with measure bounds derived from the whp
width event:

* `rBeyond_eq_zero_of_goodWidth_of_bulk_below` — the GENERAL level-`i` emptiness: on the
  good-width event, if the `0.1` bulk has not reached within `W` of level `i`, then level
  `i` and above are empty.  `frontSync_of_goodWidth_of_bulk_below` is the `i = capMinute`
  instance; the empty cap−1 feeder (`ClockJointInduction`'s `hfeeder` conjunct) is the
  `i = capMinute − 1` instance.
* `notRBeyondZero_subset_width_union` / `rBeyond_zero_whp_of_goodFrontWidth` — the
  endpoint set-inclusion + measure union: the level-`i` non-emptiness event is covered by
  (side ∧ ¬GoodFrontWidth) ∪ ¬side ∪ ¬bulk-below, so its measure is `≤ εW + εP + εB`,
  with `εW` supplied by `goodFrontWidth_whp` (whose bad event carries the side conjunct
  `P`), `εP` the side-event failure, and `εB` the bulk-arrival bound.
* `frontSync_whp_of_goodFrontWidth` — the `i = capMinute` instance: the endpoint
  `{¬ FrontSync}` measure bound.  This is the minimal replacement for the endpoint use of
  `ClockFrontShape.FrontSyncConcentration_remaining`.

Everything here is deterministic glue + finite measure unions; the probabilistic content
lives entirely in the §6 engine inputs.
-/

namespace ExactMajority

namespace ClockFrontSyncFromWidth

open MeasureTheory ClockRealKernel ClockFrontShape ClockFrontProfile

open scoped ENNReal

variable {L K : ℕ}

/-! ## Part 1 — the general level-`i` emptiness from the width invariant -/

/-- **General level emptiness.**  On the good-width event, if the `0.1` bulk threshold has
not reached within `W` minutes of level `i` (`10 · rBeyond (i−W) < card`), then level `i`
and above are EMPTY.  The `i = capMinute` instance is
`ClockFrontProfile.frontSync_of_goodWidth_of_bulk_below`; the `i = capMinute − 1` instance
gives the empty cap−1 feeder that `ClockJointInduction` carries. -/
theorem rBeyond_eq_zero_of_goodWidth_of_bulk_below
    (W i : ℕ) (c : Config (AgentState L K))
    (hgood : GoodFrontWidth (L := L) (K := K) W c)
    (hbulk : 10 * rBeyond (L := L) (K := K) (i - W) c < c.card) :
    rBeyond (L := L) (K := K) i c = 0 := by
  by_contra h
  have hpos : 0 < rBeyond (L := L) (K := K) i c := Nat.pos_of_ne_zero h
  have hw := hgood i hpos
  omega

/-! ## Part 2 — the endpoint set inclusion

The level-`i` non-emptiness event is covered by three events: the width invariant fails
on the side event `P` (the shape `goodFrontWidth_whp` bounds), the side event `P` itself
fails, or the bulk has arrived within `W` of level `i`.  `P` is abstract here — it is
instantiated with the side conjunct carried inside the §6 engine's bad event
(`c.card = n ∧ AllClockP3 c ∧ negligibility`). -/

/-- **Endpoint set inclusion** covering level-`i` non-emptiness by the three failure
events. -/
theorem notRBeyondZero_subset_width_union
    (W i : ℕ) (P : Config (AgentState L K) → Prop) :
    {c : Config (AgentState L K) | ¬ rBeyond (L := L) (K := K) i c = 0} ⊆
      ({c | P c ∧ ¬ GoodFrontWidth (L := L) (K := K) W c} ∪ {c | ¬ P c}) ∪
      {c | ¬ (10 * rBeyond (L := L) (K := K) (i - W) c < c.card)} := by
  intro c hc
  simp only [Set.mem_setOf_eq, Set.mem_union] at hc ⊢
  by_cases hbulk : 10 * rBeyond (L := L) (K := K) (i - W) c < c.card
  · left
    by_cases hP : P c
    · exact Or.inl ⟨hP, fun hg =>
        hc (rBeyond_eq_zero_of_goodWidth_of_bulk_below W i c hg hbulk)⟩
    · exact Or.inr hP
  · exact Or.inr hbulk

/-! ## Part 3 — the endpoint measure bridges -/

/-- **Endpoint level-`i` emptiness whp.**  Given the three endpoint event bounds — the
width-failure-on-side event (`εW`, supplied by `goodFrontWidth_whp`), the side-event
failure (`εP`), and the bulk arrival (`εB`) — the level-`i` non-emptiness measure at the
horizon is `≤ εW + εP + εB`. -/
theorem rBeyond_zero_whp_of_goodFrontWidth
    (H W i : ℕ) (c₀ : Config (AgentState L K))
    (P : Config (AgentState L K) → Prop) (εW εP εB : ℝ≥0∞)
    (hwidth : ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | P c ∧ ¬ GoodFrontWidth (L := L) (K := K) W c} ≤ εW)
    (hP : ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c | ¬ P c} ≤ εP)
    (hbulk : ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ (10 * rBeyond (L := L) (K := K) (i - W) c < c.card)} ≤ εB) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ rBeyond (L := L) (K := K) i c = 0} ≤ εW + εP + εB := by
  refine le_trans (measure_mono
    (notRBeyondZero_subset_width_union (L := L) (K := K) W i P)) ?_
  refine le_trans (measure_union_le _ _) ?_
  exact add_le_add (le_trans (measure_union_le _ _) (add_le_add hwidth hP)) hbulk

/-- **Endpoint FrontSync whp** — the `i = capMinute` instance: the endpoint
`{¬ FrontSync}` measure is `≤ εW + εP + εB`.  This is the minimal genuine replacement for
the endpoint use of `ClockFrontShape.FrontSyncConcentration_remaining`, with the carried
deterministic windows replaced by the §6 whp inputs. -/
theorem frontSync_whp_of_goodFrontWidth
    (H W : ℕ) (c₀ : Config (AgentState L K))
    (P : Config (AgentState L K) → Prop) (εW εP εB : ℝ≥0∞)
    (hwidth : ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | P c ∧ ¬ GoodFrontWidth (L := L) (K := K) W c} ≤ εW)
    (hP : ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c | ¬ P c} ≤ εP)
    (hbulk : ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            (capMinute (L := L) (K := K) - W) c < c.card)} ≤ εB) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ FrontSync (L := L) (K := K) c} ≤ εW + εP + εB := by
  refine le_trans (measure_mono ?_) (rBeyond_zero_whp_of_goodFrontWidth
    (L := L) (K := K) H W (capMinute (L := L) (K := K)) c₀ P εW εP εB hwidth hP hbulk)
  intro c hc
  simp only [Set.mem_setOf_eq] at hc ⊢
  rw [frontSync_iff_rBeyond_cap_zero] at hc
  exact hc

/-- **Endpoint empty cap−1 feeder whp** — the `i = capMinute − 1` instance: the event
that the cap−1 feeder is NONEMPTY has measure `≤ εW + εP + εB` (with the bulk-below
input one level lower, at `(capMinute − 1) − W`).  This is the whp replacement for
`ClockJointInduction`'s carried `hfeeder_all` conjunct `rBeyond (capMinute − 1) = 0`. -/
theorem capFeederEmpty_whp_of_goodFrontWidth
    (H W : ℕ) (c₀ : Config (AgentState L K))
    (P : Config (AgentState L K) → Prop) (εW εP εB : ℝ≥0∞)
    (hwidth : ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | P c ∧ ¬ GoodFrontWidth (L := L) (K := K) W c} ≤ εW)
    (hP : ((NonuniformMajority L K).transitionKernel ^ H) c₀ {c | ¬ P c} ≤ εP)
    (hbulk : ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ (10 * rBeyond (L := L) (K := K)
            ((capMinute (L := L) (K := K) - 1) - W) c < c.card)} ≤ εB) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c | ¬ rBeyond (L := L) (K := K) (capMinute (L := L) (K := K) - 1) c = 0}
      ≤ εW + εP + εB :=
  rBeyond_zero_whp_of_goodFrontWidth (L := L) (K := K) H W
    (capMinute (L := L) (K := K) - 1) c₀ P εW εP εB hwidth hP hbulk

end ClockFrontSyncFromWidth

end ExactMajority
