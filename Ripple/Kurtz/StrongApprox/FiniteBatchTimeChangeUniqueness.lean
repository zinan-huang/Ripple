-- Ripple/Kurtz/StrongApprox/FiniteBatchTimeChangeUniqueness.lean
import Ripple.Kurtz.StrongApprox.FiniteClockFirstHit

/-!
# Extensional uniqueness of the finite-batch time change

The induction invariant is equality of the arbitrary solution's scaled clocks
with the canonical record clocks.  If a pending token were reached strictly
before the next canonical record, the finite first-hit lemma would select an
earliest such token.  Before that hit all counts, hence the state, are
constant; integrating the constant rate identifies its wait with
`tokenWait`, contradicting minimality of `stepDelay`.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory Set Finset Filter Topology
open scoped BigOperators

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace BatchData

variable (D : BatchData d ι)
variable {κ : ι → Type*} [∀ l, Fintype (κ l)]
  [∀ l, DecidableEq (κ l)]
variable (arrival : ∀ l, κ l → ℝ)

/-- The exact finite-driver equation used for uniqueness. -/
structure IsTimeChangeSolution
    (X : ℝ → Fin d → ℝ) : Prop where
  measurable_path : Measurable X
  initial_eq : X 0 = D.initial
  equation : ∀ t ∈ Icc (0 : ℝ) D.horizon,
    X t = X 0 +
      ∑ l, (((D.finiteCount arrival l
        ((D.scale : ℝ) * clock D.rate X l t) : ℕ) : ℝ) /
          (D.scale : ℝ)) • D.jump l

/-- The equation rewritten with the declared initial state. -/
theorem IsTimeChangeSolution.equation_initial
    {X : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) D.horizon) :
    X t = D.initial +
      ∑ l, (((D.finiteCount arrival l
        ((D.scale : ℝ) * clock D.rate X l t) : ℕ) : ℝ) /
          (D.scale : ℝ)) • D.jump l := by
  simpa [hX.initial_eq] using hX.equation t ht

/-- Scaled accumulated clock of an arbitrary candidate solution. -/
noncomputable def solutionClock
    (X : ℝ → Fin d → ℝ) (l : ι) (t : ℝ) : ℝ :=
  (D.scale : ℝ) * clock D.rate X l t

theorem continuous_solutionClock
    {X : ℝ → Fin d → ℝ} (hXm : Measurable X) (l : ι) :
    Continuous (D.solutionClock X l) := by
  unfold solutionClock
  exact continuous_const.mul
    (continuous_clock D.rate_nonneg D.rate_le
      D.rate_measurable hXm l)

theorem monotone_solutionClock
    {X : ℝ → Fin d → ℝ} (hXm : Measurable X) (l : ι) :
    Monotone (D.solutionClock X l) := by
  intro s t hst
  unfold solutionClock
  exact mul_le_mul_of_nonneg_left
    (clock_mono D.rate_nonneg D.rate_le
      D.rate_measurable hXm l hst)
    (Nat.cast_nonneg D.scale)

/-- If a clock advances but reaches no threshold that was pending at `q₀`,
its finite count is unchanged. -/
theorem finiteCount_eq_of_no_new_arrival
    (l : ι) {q₀ q : ℝ} (hqq : q₀ ≤ q)
    (hnew : ∀ a, q₀ < arrival l a → q < arrival l a) :
    D.finiteCount arrival l q = D.finiteCount arrival l q₀ := by
  classical
  unfold finiteCount finiteArrivalCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ha
    by_contra hq₀a
    exact (not_lt_of_ge ha) (hnew a (lt_of_not_ge hq₀a))
  · intro ha
    exact ha.trans hqq

/-- A scaled solution clock is affine on an interval on which the state is
constant.  The possible value at the right endpoint is irrelevant to the
integral. -/
theorem solutionClock_eq_linear
    {X : ℝ → Fin d → ℝ} (hXm : Measurable X)
    (l : ι) {s t : ℝ} (hst : s ≤ t)
    (y : Fin d → ℝ)
    (hstate : ∀ u ∈ Ico s t, X u = y) :
    D.solutionClock X l t =
      D.solutionClock X l s +
        (D.scale : ℝ) * (t - s) * D.rate l y := by
  have hleft := intervalIntegrable_rate
    D.rate_nonneg D.rate_le D.rate_measurable hXm l 0 s
  have hright := intervalIntegrable_rate
    D.rate_nonneg D.rate_le D.rate_measurable hXm l s t
  have hpiece :
      ∫ u in s..t, D.rate l (X u) =
        (t - s) * D.rate l y := by
    have htne : ∀ᵐ u ∂volume, u ≠ t := by
      filter_upwards [(Set.countable_singleton t).ae_notMem volume] with u hu
      simpa using hu
    calc
      ∫ u in s..t, D.rate l (X u)
          = ∫ _u in s..t, D.rate l y := by
              refine intervalIntegral.integral_congr_ae ?_
              filter_upwards [htne] with u hut hu
              rw [Set.uIoc_of_le hst] at hu
              have hu' : u ∈ Ico s t :=
                ⟨hu.1.le, lt_of_le_of_ne hu.2 hut⟩
              exact congrArg (D.rate l) (hstate u hu')
      _ = (t - s) * D.rate l y := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
  unfold solutionClock clock
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hpiece]
  ring

/-- Equality of canonical and solution clocks at a record. -/
def RecordClockMatches
    (X : ℝ → Fin d → ℝ) (k : ℕ) : Prop :=
  ∀ l, (D.records arrival k).internal l =
    D.solutionClock X l (D.records arrival k).time

/-- A measurable solution cannot reach a pending token before the next
canonical record. -/
theorem solution_pending_not_reached_before_next
    {X : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {k : ℕ} (hmatch : D.RecordClockMatches arrival X k)
    {t : ℝ}
    (hleft : (D.records arrival k).time ≤ t)
    (hright : t < (D.records arrival (k + 1)).time)
    {a : Token κ}
    (ha : a ∈ D.pendingTokens arrival (D.records arrival k)) :
    D.solutionClock X a.1 t < arrival a.1 a.2 := by
  classical
  by_contra hnot
  have hcrossOne : arrival a.1 a.2 ≤ D.solutionClock X a.1 t :=
    not_lt.mp hnot
  let Pending := {z : Token κ // z ∈ D.pendingTokens arrival (D.records arrival k)}
  let q : Pending → ℝ → ℝ := fun z u =>
    D.solutionClock X z.1.1 u
  let level : Pending → ℝ := fun z => arrival z.1.1 z.1.2
  have hstart : ∀ z : Pending, q z (D.records arrival k).time < level z := by
    intro z
    have hz : (D.records arrival k).internal z.1.1 < arrival z.1.1 z.1.2 :=
      (D.mem_pendingTokens arrival _ z.1).mp z.2
    show D.solutionClock X z.1.1 (D.records arrival k).time < arrival z.1.1 z.1.2
    rw [← hmatch z.1.1]
    exact hz
  have hcross : ∃ z : Pending, level z ≤ q z t := by
    refine ⟨⟨a, ?_⟩, ?_⟩
    · exact ha
    · simpa [q, level] using hcrossOne
  obtain ⟨z, τ, hτ, hhit, hbefore⟩ :=
    exists_first_hit_from_finite_family q level
      (fun z => D.continuous_solutionClock hX.measurable_path z.1.1)
      (fun z => D.monotone_solutionClock hX.measurable_path z.1.1)
      hleft hstart hcross
  have hrAdm := D.records_admissible arrival harrival k
  have hrNextAdm := D.records_admissible arrival harrival (k + 1)
  have hstate : ∀ u ∈ Ico (D.records arrival k).time τ,
      X u = D.recordState arrival k := by
    intro u hu
    have hu0 : 0 ≤ u := hrAdm.time_nonneg.trans hu.1
    have huT : u ≤ D.horizon := by
      exact hu.2.le.trans
        (hτ.2.trans (hright.le.trans hrNextAdm.time_le))
    have hcount : ∀ l,
        D.finiteCount arrival l (D.solutionClock X l u) =
          D.finiteCount arrival l ((D.records arrival k).internal l) := by
      intro l
      have hclockLe : (D.records arrival k).internal l ≤ D.solutionClock X l u := by
        rw [hmatch l]
        exact D.monotone_solutionClock hX.measurable_path l hu.1
      apply D.finiteCount_eq_of_no_new_arrival arrival l hclockLe
      intro b hb
      let w : Pending :=
        ⟨⟨l, b⟩, (D.mem_pendingTokens arrival _ ⟨l, b⟩).mpr hb⟩
      simpa [q, level, w] using hbefore w u hu
    calc
      X u = D.initial +
          ∑ l, (((D.finiteCount arrival l
            (D.solutionClock X l u) : ℕ) : ℝ) /
              (D.scale : ℝ)) • D.jump l := by
            simpa [solutionClock] using
              IsTimeChangeSolution.equation_initial D arrival hX ⟨hu0, huT⟩
      _ = D.recordState arrival k := by
            unfold recordState clockState
            congr 1
            exact Finset.sum_congr rfl fun l _ => by rw [hcount l]
  have hlinear := D.solutionClock_eq_linear
    hX.measurable_path z.1.1 hτ.1.le
    (D.recordState arrival k) hstate
  have hhit' :
      D.solutionClock X z.1.1 τ = arrival z.1.1 z.1.2 := by
    simpa [q, level] using hhit
  have hzPending :
      (D.records arrival k).internal z.1.1 < arrival z.1.1 z.1.2 := by
    exact (D.mem_pendingTokens arrival _ z.1).mp z.2
  have hbalance :
      arrival z.1.1 z.1.2 =
        (D.records arrival k).internal z.1.1 +
          (D.scale : ℝ) * (τ - (D.records arrival k).time) *
            D.rate z.1.1 (D.recordState arrival k) := by
    rw [← hhit', hlinear, ← hmatch z.1.1]
  have hrateNe :
      D.rate z.1.1 (D.recordState arrival k) ≠ 0 := by
    intro hzero
    have heq : arrival z.1.1 z.1.2 = (D.records arrival k).internal z.1.1 := by
      simpa [hzero] using hbalance
    exact (ne_of_gt hzPending) heq
  have hratePos :
      0 < D.rate z.1.1 (D.recordState arrival k) :=
    lt_of_le_of_ne (D.rate_nonneg z.1.1 _) (Ne.symm hrateNe)
  have hscalePos : (0 : ℝ) < D.scale := by
    exact_mod_cast D.scale_pos
  have hden : 0 < (D.scale : ℝ) *
      D.rate z.1.1 (D.recordState arrival k) :=
    mul_pos hscalePos hratePos
  have hwait :
      D.tokenWait arrival (D.records arrival k) z.1 = τ - (D.records arrival k).time := by
    unfold tokenWait
    have hnum :
        arrival z.1.1 z.1.2 - (D.records arrival k).internal z.1.1 =
          (D.scale : ℝ) * (τ - (D.records arrival k).time) *
            D.rate z.1.1 (D.recordState arrival k) := by
      linarith [hbalance]
    have hrs : D.recordState arrival k =
        D.clockState arrival (D.records arrival k).internal := rfl
    rw [hnum, ← hrs]
    field_simp [ne_of_gt hden]
  have hzEnabled : z.1 ∈ D.enabledTokens arrival (D.records arrival k) := by
    exact (D.mem_enabledTokens arrival _ z.1).mpr ⟨hzPending, hratePos⟩
  have hEnabledNonempty : (D.enabledTokens arrival (D.records arrival k)).Nonempty :=
    ⟨z.1, hzEnabled⟩
  have heventLe : D.eventDelay arrival (D.records arrival k) ≤
      D.tokenWait arrival (D.records arrival k) z.1 := by
    rw [eventDelay, dif_pos hEnabledNonempty]
    exact Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨z.1, hzEnabled, rfl⟩)
  have hrt : (D.records arrival k).time < D.horizon :=
    lt_of_le_of_lt hleft (hright.trans_le hrNextAdm.time_le)
  have hstepLe : D.stepDelay arrival (D.records arrival k) ≤ D.eventDelay arrival (D.records arrival k) := by
    simp [stepDelay, hrt]
  have htStep : t - (D.records arrival k).time < D.stepDelay arrival (D.records arrival k) := by
    change t < (D.records arrival k).time + D.stepDelay arrival (D.records arrival k) at hright
    linarith
  have hτt : τ ≤ t := hτ.2
  have himpossible : τ - (D.records arrival k).time < τ - (D.records arrival k).time := by
    calc
      τ - (D.records arrival k).time ≤ t - (D.records arrival k).time := sub_le_sub_right hτt _
      _ < D.stepDelay arrival (D.records arrival k) := htStep
      _ ≤ D.eventDelay arrival (D.records arrival k) := hstepLe
      _ ≤ D.tokenWait arrival (D.records arrival k) z.1 := heventLe
      _ = τ - (D.records arrival k).time := hwait
  exact (lt_irrefl _ himpossible)

/-- Between consecutive canonical records every measurable solution is the
canonical record state. -/
theorem solution_eq_recordState_before_next
    {X : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {k : ℕ} (hmatch : D.RecordClockMatches arrival X k)
    {t : ℝ}
    (hleft : (D.records arrival k).time ≤ t)
    (hright : t < (D.records arrival (k + 1)).time) :
    X t = D.recordState arrival k := by
  have hrAdm := D.records_admissible arrival harrival k
  have hrNextAdm := D.records_admissible arrival harrival (k + 1)
  have ht0 : 0 ≤ t := hrAdm.time_nonneg.trans hleft
  have htT : t ≤ D.horizon :=
    (le_of_lt hright).trans hrNextAdm.time_le
  have hcount : ∀ l,
      D.finiteCount arrival l (D.solutionClock X l t) =
        D.finiteCount arrival l ((D.records arrival k).internal l) := by
    intro l
    have hclockLe : (D.records arrival k).internal l ≤ D.solutionClock X l t := by
      rw [hmatch l]
      exact D.monotone_solutionClock hX.measurable_path l hleft
    apply D.finiteCount_eq_of_no_new_arrival arrival l hclockLe
    intro b hb
    exact D.solution_pending_not_reached_before_next arrival hX harrival
      hmatch hleft hright
      (a := ⟨l, b⟩) ((D.mem_pendingTokens arrival _ ⟨l, b⟩).mpr hb)
  calc
    X t = D.initial +
        ∑ l, (((D.finiteCount arrival l
          (D.solutionClock X l t) : ℕ) : ℝ) /
            (D.scale : ℝ)) • D.jump l := by
          simpa [solutionClock] using
            IsTimeChangeSolution.equation_initial D arrival hX ⟨ht0, htT⟩
    _ = D.recordState arrival k := by
          unfold recordState clockState
          congr 1
          exact Finset.sum_congr rfl fun l _ => by rw [hcount l]

/-- Clock matching propagates from one canonical record to its successor. -/
theorem solution_recordClockMatches_succ
    {X : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {k : ℕ} (hmatch : D.RecordClockMatches arrival X k) :
    D.RecordClockMatches arrival X (k + 1) := by
  intro l
  have htime := D.records_time_mono arrival harrival (Nat.le_succ k)
  have hstate : ∀ u ∈ Ico
      (D.records arrival k).time
      (D.records arrival (k + 1)).time,
      X u = D.recordState arrival k := by
    intro u hu
    exact D.solution_eq_recordState_before_next arrival hX harrival
      hmatch hu.1 hu.2
  have hlinear := D.solutionClock_eq_linear
    hX.measurable_path l htime
    (D.recordState arrival k) hstate
  rw [← hmatch l] at hlinear
  simpa [records, nextRecord] using hlinear.symm

/-- The arbitrary solution's scaled clocks agree with every canonical record. -/
theorem solution_recordClockMatches
    {X : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    ∀ k, D.RecordClockMatches arrival X k := by
  intro k
  induction k with
  | zero =>
      intro l
      simp [RecordClockMatches, records, initialRecord,
        solutionClock, clock]
  | succ k ih =>
      exact D.solution_recordClockMatches_succ arrival hX harrival ih

/-- At every canonical record time, the arbitrary solution is the canonical
record state. -/
theorem solution_eq_recordState_at_record
    {X : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    (k : ℕ) :
    X (D.records arrival k).time = D.recordState arrival k := by
  have hmatch := D.solution_recordClockMatches arrival hX harrival k
  have hAdm := D.records_admissible arrival harrival k
  calc
    X (D.records arrival k).time = D.initial +
        ∑ l, (((D.finiteCount arrival l
          (D.solutionClock X l (D.records arrival k).time) : ℕ) : ℝ) /
            (D.scale : ℝ)) • D.jump l := by
          simpa [solutionClock] using
            IsTimeChangeSolution.equation_initial D arrival hX ⟨hAdm.time_nonneg, hAdm.time_le⟩
    _ = D.recordState arrival k := by
          unfold recordState clockState
          congr 1
          exact Finset.sum_congr rfl fun l _ => by rw [← hmatch l]

/-- **Extensional uniqueness.** Every measurable finite-driver solution is
the finite-batch readout on the full finite horizon. -/
theorem timeChangeSolution_eq_constructedPath
    {X : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    Set.EqOn X (D.constructedPath (κ := κ) arrival)
      (Icc (0 : ℝ) D.horizon) := by
  intro t ht
  by_cases htT : t = D.horizon
  · subst t
    have hXterminal := D.solution_eq_recordState_at_record
      arrival hX harrival (D.constructionFuel (κ := κ))
    have hrecord := D.records_terminal arrival harrival
    have hconstructed := D.constructedPath_at_horizon arrival harrival
    rw [hrecord] at hXterminal
    exact hXterminal.trans hconstructed.symm
  · have htlt : t < D.horizon := lt_of_le_of_ne ht.2 htT
    obtain ⟨k, hk, hleft, hright⟩ :=
      D.exists_record_interval arrival harrival ht.1 htlt
    have hmatch := D.solution_recordClockMatches arrival hX harrival k
    have hsolution := D.solution_eq_recordState_before_next
      arrival hX harrival hmatch hleft hright
    have hconstructed := D.constructedPath_eq_recordState
      arrival harrival hk hleft hright
    exact hsolution.trans hconstructed.symm

/-- Two measurable solutions with the same finite driver coincide. -/
theorem timeChangeSolution_unique
    {X Z : ℝ → Fin d → ℝ}
    (hX : D.IsTimeChangeSolution arrival X)
    (hZ : D.IsTimeChangeSolution arrival Z)
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    Set.EqOn X Z (Icc (0 : ℝ) D.horizon) := by
  intro t ht
  exact
    (D.timeChangeSolution_eq_constructedPath arrival hX harrival ht).trans
      (D.timeChangeSolution_eq_constructedPath arrival hZ harrival ht).symm

end BatchData

end Ripple.Kurtz.StrongApprox

end
