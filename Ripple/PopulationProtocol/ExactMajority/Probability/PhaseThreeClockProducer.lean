import Ripple.PopulationProtocol.ExactMajority.Probability.StageEventSpec
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrain

/-!
# The asynchronous clock producer at the first-seed stopping time (N12, assembly form)

The Phase-0–2 entry producer (N11) is not yet available, so the N12 producer is
stated, as `PhaseOneDrainProducer` does for N11b, from a pair-log stopping time with a
state predicate at that time: the stopping time is the genuine first Phase-3 seed
`seedTime init 3`, and the state predicate is `SeedProfile` at that time (the review
repair of PHASE3: the quantifier runs over `SeedProfile` states, not over first-seed
pasts).

* `seedTime init p`: the genuine first seed time of phase `p` as a `WithTop ℕ`; its
  finite fibres are the `firstPhaseSeed` events, so it is a `PairLogPastTime`.
* `clockFailureAt init`: the failure event at the stopping time.
* `phaseClockFailure_subset`: the plan's failure set `phaseClockFailure
  (reviewedStageEvents n init)` is contained in it.
* `splice_of_local`: the disjoint first-seed splice (no measurability of the failure
  set is needed; the outer-measure subadditivity suffices).
* `asynchronous_clock_estimate_of_local`: the N12 headline follows from the local
  estimate at each finite first-seed time. That local estimate (PHASE3 P2–P15 and
  §11 on the virtual continuation) is the remaining producer work.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockProducer

open TimeTheorem PairLog StageEventSpec PhaseOneDrain

variable {L K : ℕ}

/-! ## The genuine first seed time -/

theorem firstPhaseSeed_unique (init : Cfg L K) (p : ℕ) (ω : Ω L K) {t t' : ℕ}
    (h : firstPhaseSeed init p t ω) (h' : firstPhaseSeed init p t' ω) : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨a, ha, hap⟩ := h.1
    have := h'.2 t hlt a ha
    omega
  · obtain ⟨a, ha, hap⟩ := h'.1
    have := h.2 t' hlt a ha
    omega

open Classical in
/-- The genuine first time at which some agent is in phase exactly `p` while every
earlier configuration has all phases below `p`; `⊤` if there is none. -/
def seedTime (init : Cfg L K) (p : ℕ) (ω : Ω L K) : WithTop ℕ :=
  if h : ∃ t, firstPhaseSeed init p t ω then ((Nat.find h : ℕ) : WithTop ℕ) else ⊤

open Classical in
theorem seedTime_eq_iff (init : Cfg L K) (p : ℕ) (ω : Ω L K) (s : ℕ) :
    seedTime init p ω = (s : WithTop ℕ) ↔ firstPhaseSeed init p s ω := by
  unfold seedTime
  split_ifs with h
  · constructor
    · intro hs
      have hs' : Nat.find h = s := WithTop.coe_injective hs
      rw [← hs']
      exact Nat.find_spec h
    · intro hs
      have := firstPhaseSeed_unique init p ω (Nat.find_spec h) hs
      rw [this]
  · constructor
    · intro hs
      exact absurd hs WithTop.top_ne_coe
    · intro hs
      exact absurd ⟨s, hs⟩ h

theorem seedTime_pastTime (init : Cfg L K) (p : ℕ) :
    PairLogPastTime (seedTime init p) := by
  intro s
  have hset : {ω | seedTime init p ω = (s : WithTop ℕ)} = {ω | firstPhaseSeed init p s ω} := by
    ext ω
    exact seedTime_eq_iff init p ω s
  rw [hset]
  exact firstPhaseSeed_measurableSet init p s

/-! ## The failure event at the stopping time -/

variable {n : ℕ}

/-- After an entry whose first seed is at `s`, no completed reviewed clock history. -/
def clockBadAfter (init : InputCfg n) (s : ℕ) (ω : InputLog n) : Prop :=
  (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧
    ¬ ∃ T ρ, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ reviewedClockGood init ω s T ρ

/-- The N12 failure event at the first-seed stopping time, with the `SeedProfile`
state predicate at that time. -/
def clockFailureAt (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
    SeedProfile n init (trace init ω s) ∧ clockBadAfter init s ω}

theorem phaseClockFailure_subset (init : InputCfg n) :
    phaseClockFailure (reviewedStageEvents n init) ⊆ clockFailureAt init := by
  intro ω hω
  obtain ⟨hin, hnot⟩ := hω
  obtain ⟨S, T, hT, hentry⟩ :
      ∃ S T, T ≤ earlyHorizon n ∧ AsyncEntry init ω S T := hin
  refine ⟨S, (seedTime_eq_iff init 3 ω S).mpr hentry.first_phase_seed,
    hentry.seed_profile, ⟨T, hT, hentry⟩, ?_⟩
  rintro ⟨T', ρ, hT', hentry', hgood⟩
  exact hnot (show ∃ S T ρ, T ≤ earlyHorizon n ∧ AsyncEntry init ω S T ∧
    reviewedClockGood init ω S T ρ from ⟨S, T', ρ, hT', hentry', hgood⟩)

theorem clockFailureAt_finite (init : InputCfg n) {ω : InputLog n}
    (hω : ω ∈ clockFailureAt init) : seedTime init 3 ω ≠ ⊤ := by
  obtain ⟨s, hs, -, -⟩ := hω
  rw [hs]
  exact WithTop.coe_ne_top

/-! ## The splice over the disjoint first-seed times -/

/-- `PairLog.genuine_seed_splice` without the measurability of the bad event: the
proof uses only outer-measure monotonicity and subadditivity on `B`. -/
theorem splice_of_local {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Ω → WithTop ℕ) (B : Set Ω) (ε : ℝ≥0∞)
    (hS : ∀ s : ℕ, MeasurableSet {ω | S ω = (s : WithTop ℕ)})
    (hfinite : ∀ ω ∈ B, S ω ≠ ⊤)
    (hlocal : ∀ s : ℕ,
      μ (B ∩ {ω | S ω = (s : WithTop ℕ)}) ≤ ε * μ {ω | S ω = (s : WithTop ℕ)}) :
    μ B ≤ ε := by
  let E : ℕ → Set Ω := fun s => {ω | S ω = (s : WithTop ℕ)}
  have hdisj : Pairwise (fun s t => Disjoint (E s) (E t)) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro ω hs ht
    exact hst (WithTop.coe_injective (hs.symm.trans ht))
  have hcover : B ⊆ ⋃ s : ℕ, B ∩ E s := by
    intro ω hω
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hfinite ω hω)
    exact Set.mem_iUnion.mpr ⟨s, hω, hs.symm⟩
  have hmass : (∑' s : ℕ, μ (E s)) ≤ 1 := by
    rw [← measure_iUnion hdisj hS]
    exact prob_le_one
  calc
    μ B ≤ μ (⋃ s : ℕ, B ∩ E s) := measure_mono hcover
    _ ≤ ∑' s : ℕ, μ (B ∩ E s) := measure_iUnion_le _
    _ ≤ ∑' s : ℕ, ε * μ (E s) := ENNReal.tsum_le_tsum hlocal
    _ = ε * ∑' s : ℕ, μ (E s) := by rw [ENNReal.tsum_mul_left]
    _ ≤ ε * 1 := mul_le_mul_left' hmass ε
    _ = ε := mul_one ε

/-! ## The reduction of the N12 headline to its local estimate -/

/-- The N12 headline follows from the local estimate at each finite first-seed time
`s`: on the fibre `seedTime init 3 = s` with a `SeedProfile` state at `s`, the reviewed
clock history fails with probability at most `8 / n ^ 5` times the fibre probability.
The local estimate is the content of PHASE3 P2–P15 and §11 on the virtual
continuation; it is not proved here. -/
theorem asynchronous_clock_estimate_of_local (init : InputCfg n)
    (hlocal : ∀ s : ℕ,
      law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
          SeedProfile n init (trace init ω s) ∧ clockBadAfter init s ω} ≤
        ENNReal.ofReal (8 / (n : ℝ) ^ 5) *
          law init {ω | seedTime init 3 ω = (s : WithTop ℕ)}) :
    law init (phaseClockFailure (reviewedStageEvents n init)) ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 5) := by
  refine (measure_mono (phaseClockFailure_subset init)).trans ?_
  refine splice_of_local (law init) (seedTime init 3) (clockFailureAt init) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
    (fun ω hω => clockFailureAt_finite init hω) (fun s => ?_)
  refine le_trans (measure_mono ?_) (hlocal s)
  rintro ω ⟨⟨s', hs', hprof, hbad⟩, hs⟩
  have hss : s' = s := WithTop.coe_injective (hs'.symm.trans hs)
  subst hss
  exact ⟨hs, hprof, hbad⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockProducer

end
