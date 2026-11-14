-- Ripple/Kurtz/StrongApprox/FiniteBatchTimeChange.lean
import Ripple.Kurtz.StrongApprox.PoissonPathArrivals
import Ripple.Kurtz.StrongApprox.ChainFluidLIL

/-!
# Finite-batch random-time-change construction

For finitely many positive labelled arrivals in every channel, this file builds
records by repeatedly advancing all internal clocks to the first enabled
arrival or to the physical horizon. Every tie is consumed simultaneously.
The record readout is a finite right-continuous step function.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory Set Finset Filter
open scoped BigOperators Topology

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Data of one bounded finite-horizon time-change problem. -/
structure BatchData (d : ℕ) (ι : Type*) [Fintype ι] where
  scale : ℕ
  horizon : ℝ
  initial : Fin d → ℝ
  rate : ι → (Fin d → ℝ) → ℝ
  jump : ι → Fin d → ℝ
  bound : ι → ℝ
  scale_pos : 0 < scale
  horizon_nonneg : 0 ≤ horizon
  rate_nonneg : ∀ l y, 0 ≤ rate l y
  rate_le : ∀ l y, rate l y ≤ bound l
  rate_measurable : ∀ l, Measurable (rate l)

namespace BatchData

variable (D : BatchData d ι)
variable {κ : ι → Type*} [∀ l, Fintype (κ l)] [∀ l, DecidableEq (κ l)]
variable (arrival : ∀ l, κ l → ℝ)

abbrev Token (κ : ι → Type*) := Σ l, κ l

/-- Count of labelled arrivals reached by internal clock `u`. -/
noncomputable def finiteCount (_D : BatchData d ι) (l : ι) (u : ℝ) : ℕ :=
  finiteArrivalCount (arrival l) u

/-- State forced by a vector of scaled internal clocks. -/
noncomputable def clockState (q : ι → ℝ) : Fin d → ℝ :=
  D.initial + ∑ l, (((D.finiteCount arrival l (q l) : ℝ) /
    (D.scale : ℝ)) • D.jump l)

/-- One successive-jump record: physical time and all scaled clocks. -/
structure ClockRecord (ι : Type*) where
  time : ℝ
  internal : ι → ℝ

noncomputable def initialRecord (_D : BatchData d ι) : ClockRecord ι where
  time := 0
  internal := fun _ => 0

/-- Tokens not yet reached by their channel's scaled clock. -/
noncomputable def pendingTokens (_D : BatchData d ι) (r : ClockRecord ι) : Finset (Token κ) :=
  (Finset.univ : Finset (Token κ)).filter fun a =>
    r.internal a.1 < arrival a.1 a.2

/-- Pending tokens whose channel currently has positive speed. -/
noncomputable def enabledTokens (r : ClockRecord ι) : Finset (Token κ) :=
  (D.pendingTokens arrival r).filter fun a =>
    0 < D.rate a.1 (D.clockState arrival r.internal)

/-- Physical waiting time from `r` to one pending enabled token. -/
noncomputable def tokenWait (r : ClockRecord ι) (a : Token κ) : ℝ :=
  (arrival a.1 a.2 - r.internal a.1) /
    ((D.scale : ℝ) * D.rate a.1 (D.clockState arrival r.internal))

/-- First enabled arrival delay; if no channel is enabled, use the remaining
physical horizon. -/
noncomputable def eventDelay (r : ClockRecord ι) : ℝ :=
  if h : (D.enabledTokens arrival r).Nonempty then
    ((D.enabledTokens arrival r).image (D.tokenWait arrival r)).min'
      (h.image (D.tokenWait arrival r))
  else
    D.horizon - r.time

/-- Advance either to the first enabled arrival or to the horizon. -/
noncomputable def stepDelay (r : ClockRecord ι) : ℝ :=
  if r.time < D.horizon then
    min (D.horizon - r.time) (D.eventDelay arrival r)
  else
    0

noncomputable def nextRecord (r : ClockRecord ι) : ClockRecord ι where
  time := r.time + D.stepDelay arrival r
  internal := fun l => r.internal l +
    (D.scale : ℝ) * D.stepDelay arrival r *
      D.rate l (D.clockState arrival r.internal)

noncomputable def records : ℕ → ClockRecord ι
  | 0 => D.initialRecord
  | k + 1 => D.nextRecord arrival (records k)

noncomputable def tokenBudget (_D : BatchData d ι) : ℕ := Fintype.card (Token κ)
noncomputable def constructionFuel : ℕ := D.tokenBudget (κ := κ) + 1

/-- The invariants used by the finite recursion. -/
structure Admissible (r : ClockRecord ι) : Prop where
  time_nonneg : 0 ≤ r.time
  time_le : r.time ≤ D.horizon
  internal_nonneg : ∀ l, 0 ≤ r.internal l
  internal_le : ∀ l,
    r.internal l ≤ (D.scale : ℝ) * D.bound l * r.time

private theorem bound_nonneg (l : ι) : 0 ≤ D.bound l :=
  (D.rate_nonneg l D.initial).trans (D.rate_le l D.initial)

@[simp]
theorem finiteCount_mono (l : ι) {u w : ℝ} (huw : u ≤ w) :
    D.finiteCount arrival l u ≤ D.finiteCount arrival l w :=
  finiteArrivalCount_mono (arrival l) huw

theorem clockState_zero
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    D.clockState arrival (fun _ => 0) = D.initial := by
  unfold clockState finiteCount
  have hz : ∀ l, finiteArrivalCount (arrival l) 0 = 0 :=
    fun l => finiteArrivalCount_zero (arrival l) (harrival l)
  simp [hz]

theorem mem_pendingTokens (r : ClockRecord ι) (a : Token κ) :
    a ∈ D.pendingTokens arrival r ↔ r.internal a.1 < arrival a.1 a.2 := by
  simp [pendingTokens]

theorem mem_enabledTokens (r : ClockRecord ι) (a : Token κ) :
    a ∈ D.enabledTokens arrival r ↔
      r.internal a.1 < arrival a.1 a.2 ∧
        0 < D.rate a.1 (D.clockState arrival r.internal) := by
  simp [enabledTokens, pendingTokens]

theorem tokenWait_pos
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    (r : ClockRecord ι) {a : Token κ}
    (ha : a ∈ D.enabledTokens arrival r) :
    0 < D.tokenWait arrival r a := by
  have hpending : r.internal a.1 < arrival a.1 a.2 :=
    ((D.mem_enabledTokens arrival r a).mp ha).1
  have hrate : 0 < D.rate a.1 (D.clockState arrival r.internal) :=
    ((D.mem_enabledTokens arrival r a).mp ha).2
  have hscale : (0 : ℝ) < D.scale := by exact_mod_cast D.scale_pos
  exact div_pos (sub_pos.mpr hpending) (mul_pos hscale hrate)

theorem eventDelay_pos
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r)
    (hrt : r.time < D.horizon) :
    0 < D.eventDelay arrival r := by
  classical
  by_cases hen : (D.enabledTokens arrival r).Nonempty
  · rw [eventDelay, dif_pos hen]
    rw [Finset.lt_min'_iff]
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
    exact D.tokenWait_pos arrival harrival r ha
  · rw [eventDelay, dif_neg hen]
    linarith

theorem stepDelay_pos
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r)
    (hrt : r.time < D.horizon) :
    0 < D.stepDelay arrival r := by
  rw [stepDelay, if_pos hrt]
  exact lt_min (sub_pos.mpr hrt)
    (D.eventDelay_pos arrival harrival hr hrt)

theorem stepDelay_nonneg
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r) :
    0 ≤ D.stepDelay arrival r := by
  by_cases hrt : r.time < D.horizon
  · exact (D.stepDelay_pos arrival harrival hr hrt).le
  · simp [stepDelay, hrt]

theorem stepDelay_le_remaining
    {r : ClockRecord ι} (hr : D.Admissible r) :
    D.stepDelay arrival r ≤ D.horizon - r.time := by
  by_cases hrt : r.time < D.horizon
  · simp [stepDelay, hrt]
  · simp only [stepDelay, hrt, if_false]
    exact sub_nonneg.mpr hr.time_le

theorem nextRecord_time_mono
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r) :
    r.time ≤ (D.nextRecord arrival r).time := by
  simp only [nextRecord]
  exact le_add_of_nonneg_right
    (D.stepDelay_nonneg arrival harrival hr)

theorem nextRecord_internal_mono
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r) (l : ι) :
    r.internal l ≤ (D.nextRecord arrival r).internal l := by
  simp only [nextRecord]
  apply le_add_of_nonneg_right
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (D.stepDelay_nonneg arrival harrival hr))
    (D.rate_nonneg l _)

theorem initialRecord_admissible : D.Admissible D.initialRecord := by
  refine ⟨by simp [initialRecord], by simpa [initialRecord] using D.horizon_nonneg,
    fun _ => by simp [initialRecord], ?_⟩
  intro l
  simp [initialRecord, D.bound_nonneg l]

theorem nextRecord_admissible
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r) :
    D.Admissible (D.nextRecord arrival r) := by
  have hδ0 := D.stepDelay_nonneg arrival harrival hr
  have hδT := D.stepDelay_le_remaining arrival hr
  have htime : (D.nextRecord arrival r).time ≤ D.horizon := by
    simp only [nextRecord]
    linarith
  refine ⟨hr.time_nonneg.trans (D.nextRecord_time_mono arrival harrival hr),
    htime, ?_, ?_⟩
  · intro l
    simp only [nextRecord]
    exact add_nonneg (hr.internal_nonneg l)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ0) (D.rate_nonneg l _))
  · intro l
    have hrate := D.rate_le l (D.clockState arrival r.internal)
    have hn : (0 : ℝ) ≤ D.scale := Nat.cast_nonneg _
    have hb := D.bound_nonneg l
    simp only [nextRecord]
    calc
      r.internal l + (D.scale : ℝ) * D.stepDelay arrival r *
          D.rate l (D.clockState arrival r.internal)
          ≤ (D.scale : ℝ) * D.bound l * r.time +
            (D.scale : ℝ) * D.stepDelay arrival r * D.bound l := by
              gcongr
              exact hr.internal_le l
      _ = (D.scale : ℝ) * D.bound l *
          (r.time + D.stepDelay arrival r) := by ring

/-- Every record is admissible. -/
theorem records_admissible
    (harrival : ∀ l (a : κ l), 0 < arrival l a) (k : ℕ) :
    D.Admissible (D.records arrival k) := by
  induction k with
  | zero => exact D.initialRecord_admissible
  | succ k ih => exact D.nextRecord_admissible arrival harrival ih

theorem records_time_mono
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    Monotone fun k => (D.records arrival k).time := by
  apply monotone_nat_of_le_succ
  intro k
  exact D.nextRecord_time_mono arrival harrival
    (D.records_admissible arrival harrival k)

private theorem pending_next_subset
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r) :
    D.pendingTokens arrival (D.nextRecord arrival r) ⊆
      D.pendingTokens arrival r := by
  intro a ha
  simp only [pendingTokens, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact lt_of_le_of_lt
    (D.nextRecord_internal_mono arrival harrival hr a.1) ha

/-- One nonterminal step either reaches the horizon or strictly consumes at
least one pending labelled arrival. -/
theorem nextRecord_progress
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {r : ClockRecord ι} (hr : D.Admissible r)
    (hrt : r.time < D.horizon) :
    (D.nextRecord arrival r).time = D.horizon ∨
      (D.pendingTokens arrival (D.nextRecord arrival r)).card <
        (D.pendingTokens arrival r).card := by
  classical
  by_cases hen : (D.enabledTokens arrival r).Nonempty
  · have hdelayPos := D.eventDelay_pos arrival harrival hr hrt
    by_cases hrem : D.horizon - r.time ≤ D.eventDelay arrival r
    · left
      simp [nextRecord, stepDelay, hrt, min_eq_left hrem]
    · right
      have hδ : D.stepDelay arrival r = D.eventDelay arrival r := by
        rw [stepDelay, if_pos hrt, min_eq_right (le_of_not_ge hrem)]
      have hminMem : D.eventDelay arrival r ∈
          (D.enabledTokens arrival r).image (D.tokenWait arrival r) := by
        rw [eventDelay, dif_pos hen]
        exact Finset.min'_mem _ _
      rcases Finset.mem_image.mp hminMem with ⟨a, ha, hwait⟩
      have hpending : a ∈ D.pendingTokens arrival r :=
        (D.mem_pendingTokens arrival r a).mpr
          ((D.mem_enabledTokens arrival r a).mp ha).1
      have hrate : 0 < D.rate a.1 (D.clockState arrival r.internal) :=
        ((D.mem_enabledTokens arrival r a).mp ha).2
      have hscale : (0 : ℝ) < D.scale := by exact_mod_cast D.scale_pos
      have hden : 0 < (D.scale : ℝ) *
          D.rate a.1 (D.clockState arrival r.internal) :=
        mul_pos hscale hrate
      have hreach : (D.nextRecord arrival r).internal a.1 =
          arrival a.1 a.2 := by
        simp only [nextRecord, hδ]
        rw [← hwait]
        unfold tokenWait
        field_simp [ne_of_gt hden]
        ring
      have hnot : a ∉ D.pendingTokens arrival (D.nextRecord arrival r) := by
        simp [pendingTokens, hreach]
      have hsub := D.pending_next_subset arrival harrival hr
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨a, hpending, hnot⟩
  · left
    simp [nextRecord, stepDelay, hrt, eventDelay, hen]

/-- The initial pending set contains every token. -/
theorem pending_initial_eq_univ
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    D.pendingTokens arrival D.initialRecord = Finset.univ := by
  ext a
  simp [pendingTokens, initialRecord, harrival a.1 a.2]

/-- After at most `#tokens + 1` steps, the physical horizon is reached. -/
theorem records_terminal
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    (D.records arrival (D.constructionFuel (κ := κ))).time = D.horizon := by
  classical
  have hbound : ∀ k : ℕ,
      (D.records arrival k).time < D.horizon →
      (D.pendingTokens arrival (D.records arrival k)).card + k ≤
        D.tokenBudget (κ := κ) := by
    intro k
    induction k with
    | zero =>
        intro _
        have h0 : D.records arrival 0 = D.initialRecord := rfl
        rw [h0, D.pending_initial_eq_univ arrival harrival]
        simp [tokenBudget]
    | succ k ih =>
        intro hnext
        have hmono := D.records_time_mono arrival harrival (Nat.le_succ k)
        have hprev : (D.records arrival k).time < D.horizon :=
          lt_of_le_of_lt hmono hnext
        have hprog := D.nextRecord_progress arrival harrival
          (D.records_admissible arrival harrival k) hprev
        rcases hprog with heq | hcard
        · simpa [records, heq] using hnext
        · have hle := ih hprev
          have hrec : D.records arrival (k + 1) =
              D.nextRecord arrival (D.records arrival k) := rfl
          rw [hrec]
          omega
  have hAdm := D.records_admissible arrival harrival
    (D.constructionFuel (κ := κ))
  apply le_antisymm hAdm.time_le
  by_contra hne
  have hlt : (D.records arrival (D.constructionFuel (κ := κ))).time <
      D.horizon := not_le.mp hne
  have h := hbound (D.constructionFuel (κ := κ)) hlt
  simp only [constructionFuel] at h
  omega

/-- The recursion itself is unique. This is the exact uniqueness statement
closed in this file; extensional uniqueness of every equation solution is
listed separately below. -/
theorem records_unique
    (R : ℕ → ClockRecord ι)
    (hinit : R 0 = D.initialRecord)
    (hstep : ∀ k, R (k + 1) = D.nextRecord arrival (R k)) :
    R = D.records arrival := by
  funext k
  induction k with
  | zero => simpa [records] using hinit
  | succ k ih => simpa [records, ih] using hstep k

/-- State associated with record `k`. -/
noncomputable def recordState (k : ℕ) : Fin d → ℝ :=
  D.clockState arrival (D.records arrival k).internal

/-- Finite right-continuous record readout. -/
noncomputable def constructedPath (t : ℝ) : Fin d → ℝ :=
  D.recordState arrival 0 +
    ∑ k ∈ Finset.range (D.constructionFuel (κ := κ)),
      if (D.records arrival (k + 1)).time ≤ t then
        D.recordState arrival (k + 1) - D.recordState arrival k
      else 0

private theorem sum_recordState_increment (m : ℕ) :
    D.recordState arrival 0 +
      ∑ k ∈ Finset.range m,
        (D.recordState arrival (k + 1) - D.recordState arrival k) =
      D.recordState arrival m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      abel

theorem constructedPath_measurable :
    Measurable (D.constructedPath (κ := κ) arrival) := by
  unfold constructedPath
  apply Measurable.add measurable_const
  apply Finset.measurable_sum
  intro k _
  simpa only [Set.mem_Ici] using
    (Measurable.ite measurableSet_Ici measurable_const measurable_const)

/-- Finite threshold support of the constructed path. -/
noncomputable def constructedJumpSupport : Finset ℝ :=
  (Finset.range (D.constructionFuel (κ := κ))).image fun k =>
    (D.records arrival (k + 1)).time

/-- The readout is locally constant to the right at every physical time. -/
theorem constructedPath_eventually_right (t : ℝ) :
    ∀ᶠ s in 𝓝[≥] t,
      D.constructedPath (κ := κ) arrival s =
        D.constructedPath (κ := κ) arrival t := by
  unfold constructedPath
  have hall : ∀ k ∈ Finset.range (D.constructionFuel (κ := κ)),
      ∀ᶠ s in 𝓝[≥] t,
        ((D.records arrival (k + 1)).time ≤ s) =
          ((D.records arrival (k + 1)).time ≤ t) := by
    intro k _
    by_cases hk : (D.records arrival (k + 1)).time ≤ t
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact propext ⟨fun _ => hk, fun _ => hk.trans hs⟩
    · have hlt : t < (D.records arrival (k + 1)).time := lt_of_not_ge hk
      filter_upwards
        [(eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds]
        with s hs
      exact propext ⟨fun h => absurd h (not_le.mpr hs), fun h => absurd h hk⟩
  filter_upwards [(Filter.eventually_all_finset _).mpr hall] with s hs
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [hs k hk]

/-- All physical jumps lie in one finite support. -/
theorem constructedPath_hasFiniteJumpSupport :
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      Disjoint (Ioc s t : Set ℝ)
        (D.constructedJumpSupport (κ := κ) arrival : Set ℝ) →
      D.constructedPath (κ := κ) arrival s =
        D.constructedPath (κ := κ) arrival t := by
  intro s t hst hdisj
  unfold constructedPath
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hsame :
      ((D.records arrival (k + 1)).time ≤ s) ↔
        ((D.records arrival (k + 1)).time ≤ t) := by
    constructor
    · exact fun h => h.trans hst
    · intro ht
      by_contra hs
      have hmem : (D.records arrival (k + 1)).time ∈
          D.constructedJumpSupport (κ := κ) arrival :=
        Finset.mem_image.mpr ⟨k, hk, rfl⟩
      exact Set.disjoint_left.mp hdisj
        ⟨lt_of_not_ge hs, ht⟩ hmem
  by_cases h : (D.records arrival (k + 1)).time ≤ s
  · rw [if_pos h, if_pos (hsame.mp h)]
  · rw [if_neg h, if_neg (fun ht => h (hsame.mpr ht))]

private theorem records_time_le_succ
    (harrival : ∀ l (a : κ l), 0 < arrival l a) (k : ℕ) :
    (D.records arrival k).time ≤ (D.records arrival (k + 1)).time :=
  D.records_time_mono arrival harrival (Nat.le_succ k)

/-- On one half-open record interval the finite readout is its record state. -/
theorem constructedPath_eq_recordState
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {k : ℕ} (hk : k < D.constructionFuel (κ := κ))
    {t : ℝ}
    (hleft : (D.records arrival k).time ≤ t)
    (hright : t < (D.records arrival (k + 1)).time) :
    D.constructedPath (κ := κ) arrival t = D.recordState arrival k := by
  unfold constructedPath
  have hbefore : ∀ j ∈ Finset.range k,
      (D.records arrival (j + 1)).time ≤ t := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
    exact (D.records_time_mono arrival harrival hjk).trans hleft
  have hafter : ∀ j ∈ Finset.Ico k (D.constructionFuel (κ := κ)),
      ¬ (D.records arrival (j + 1)).time ≤ t := by
    intro j hj
    have hkj : k + 1 ≤ j + 1 := Nat.succ_le_succ (Finset.mem_Ico.mp hj).1
    exact not_le.mpr (hright.trans_le
      (D.records_time_mono arrival harrival hkj))
  have h1 : ∑ j ∈ Finset.range k,
      (if (D.records arrival (j + 1)).time ≤ t then
        D.recordState arrival (j + 1) - D.recordState arrival j else 0) =
      ∑ j ∈ Finset.range k,
        (D.recordState arrival (j + 1) - D.recordState arrival j) :=
    Finset.sum_congr rfl fun j hj => if_pos (hbefore j hj)
  have h2 : ∑ j ∈ Finset.Ico k (D.constructionFuel (κ := κ)),
      (if (D.records arrival (j + 1)).time ≤ t then
        D.recordState arrival (j + 1) - D.recordState arrival j else 0) = 0 :=
    Finset.sum_eq_zero fun j hj => if_neg (hafter j hj)
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt hk), h1, h2, add_zero]
  exact D.sum_recordState_increment arrival k

/-- At the terminal horizon the readout is the terminal record state. -/
theorem constructedPath_at_horizon
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    D.constructedPath (κ := κ) arrival D.horizon =
      D.recordState arrival (D.constructionFuel (κ := κ)) := by
  unfold constructedPath
  have htrigger : ∀ k ∈ Finset.range (D.constructionFuel (κ := κ)),
      (D.records arrival (k + 1)).time ≤ D.horizon := by
    intro k _
    exact (D.records_admissible arrival harrival (k + 1)).time_le
  have h1 : ∑ k ∈ Finset.range (D.constructionFuel (κ := κ)),
      (if (D.records arrival (k + 1)).time ≤ D.horizon then
        D.recordState arrival (k + 1) - D.recordState arrival k else 0) =
      ∑ k ∈ Finset.range (D.constructionFuel (κ := κ)),
        (D.recordState arrival (k + 1) - D.recordState arrival k) :=
    Finset.sum_congr rfl fun k hk => if_pos (htrigger k hk)
  rw [h1]
  exact D.sum_recordState_increment arrival (D.constructionFuel (κ := κ))

/-- No labelled arrival is crossed strictly inside a record interval. -/
theorem finiteCount_interpolate_eq
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {k : ℕ} {t : ℝ}
    (hk : k < D.constructionFuel (κ := κ))
    (hleft : (D.records arrival k).time ≤ t)
    (hright : t < (D.records arrival (k + 1)).time)
    (l : ι) :
    D.finiteCount arrival l
        ((D.records arrival k).internal l +
          (D.scale : ℝ) *
            (t - (D.records arrival k).time) *
              D.rate l (D.recordState arrival k)) =
      D.finiteCount arrival l ((D.records arrival k).internal l) := by
  classical
  unfold finiteCount finiteArrivalCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ha
    by_contra hcross
    have hpending : (⟨l, a⟩ : Token κ) ∈
        D.pendingTokens arrival (D.records arrival k) :=
      (D.mem_pendingTokens arrival _ _).mpr (lt_of_not_ge hcross)
    by_cases hrate : D.rate l (D.recordState arrival k) = 0
    · exact hcross (by simpa [hrate] using ha)
    · have hratePos : 0 < D.rate l (D.recordState arrival k) :=
        lt_of_le_of_ne (D.rate_nonneg l _) (Ne.symm hrate)
      have henabled : (⟨l, a⟩ : Token κ) ∈
          D.enabledTokens arrival (D.records arrival k) :=
        (D.mem_enabledTokens arrival _ _).mpr ⟨lt_of_not_ge hcross, hratePos⟩
      have hwaitLe : D.eventDelay arrival (D.records arrival k) ≤
          D.tokenWait arrival (D.records arrival k) ⟨l, a⟩ := by
        have hne : (D.enabledTokens arrival (D.records arrival k)).Nonempty :=
          ⟨⟨l, a⟩, henabled⟩
        rw [eventDelay, dif_pos hne]
        exact Finset.min'_le _ _
          (Finset.mem_image_of_mem (D.tokenWait arrival (D.records arrival k)) henabled)
      have htimeStep :
          t - (D.records arrival k).time <
            D.stepDelay arrival (D.records arrival k) := by
        have e : (D.records arrival (k + 1)).time = (D.records arrival k).time +
            D.stepDelay arrival (D.records arrival k) := rfl
        rw [e] at hright
        linarith
      have hstepLeEvent :
          D.stepDelay arrival (D.records arrival k) ≤
            D.eventDelay arrival (D.records arrival k) := by
        by_cases hkt : (D.records arrival k).time < D.horizon
        · simp [stepDelay, hkt]
        · exfalso
          have hz : D.stepDelay arrival (D.records arrival k) = 0 := by
            rw [stepDelay, if_neg hkt]
          linarith
      have hbeforeWait : t - (D.records arrival k).time <
          D.tokenWait arrival (D.records arrival k) ⟨l, a⟩ :=
        htimeStep.trans_le (hstepLeEvent.trans hwaitLe)
      unfold tokenWait at hbeforeWait
      have hscale : (0 : ℝ) < D.scale := by exact_mod_cast D.scale_pos
      have hden : 0 < (D.scale : ℝ) * D.rate l (D.recordState arrival k) :=
        mul_pos hscale hratePos
      have := (lt_div_iff₀ hden).mp hbeforeWait
      nlinarith
  · intro ha
    have hδ0 : 0 ≤ t - (D.records arrival k).time := sub_nonneg.mpr hleft
    have hr0 := D.rate_nonneg l (D.recordState arrival k)
    exact ha.trans (le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ0) hr0))

/-- There is a record interval containing every `t < T`. -/
theorem exists_record_interval
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < D.horizon) :
    ∃ k < D.constructionFuel (κ := κ),
      (D.records arrival k).time ≤ t ∧
        t < (D.records arrival (k + 1)).time := by
  classical
  have hfuelPos : 0 < D.constructionFuel (κ := κ) := by
    simp [constructionFuel]
  have hex : ∃ j : ℕ,
      j < D.constructionFuel (κ := κ) ∧
        t < (D.records arrival (j + 1)).time := by
    refine ⟨D.constructionFuel (κ := κ) - 1,
      Nat.sub_lt (by omega) (by omega), ?_⟩
    have hsucc : D.constructionFuel (κ := κ) - 1 + 1 =
        D.constructionFuel (κ := κ) := by omega
    rw [hsucc, D.records_terminal arrival harrival]
    exact htT
  obtain ⟨k, ⟨hk1, hk2⟩, hkmin⟩ : ∃ k, (k < D.constructionFuel (κ := κ) ∧
      t < (D.records arrival (k + 1)).time) ∧
      ∀ m < k, ¬ (m < D.constructionFuel (κ := κ) ∧
        t < (D.records arrival (m + 1)).time) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  refine ⟨k, hk1, ?_, hk2⟩
  cases k with
  | zero => simpa [records, initialRecord] using ht0
  | succ j =>
      have hnot : ¬ t < (D.records arrival (j + 1)).time := fun h =>
        hkmin j (Nat.lt_succ_self j) ⟨by omega, h⟩
      exact not_lt.mp hnot

theorem rate_clock_split (X : ℝ → Fin d → ℝ) (hX : Measurable X) (l : ι) (a b : ℝ) :
    clock D.rate X l b = clock D.rate X l a + ∫ s in a..b, D.rate l (X s) := by
  unfold clock
  exact (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_rate D.rate_nonneg D.rate_le D.rate_measurable hX l 0 a)
    (intervalIntegrable_rate D.rate_nonneg D.rate_le D.rate_measurable hX l a b)).symm

/-- The scaled internal clock in record `k` is the actual accumulated clock of
the finite readout. -/
theorem recordInternal_eq_scaledClock
    (harrival : ∀ l (a : κ l), 0 < arrival l a)
    (k : ℕ) (l : ι) :
    (D.records arrival k).internal l =
      (D.scale : ℝ) *
        clock D.rate (D.constructedPath (κ := κ) arrival) l
          (D.records arrival k).time := by
  induction k with
  | zero => simp [records, initialRecord, clock]
  | succ k ih =>
      let r := D.records arrival k
      have hr := D.records_admissible arrival harrival k
      have hle := D.records_time_le_succ arrival harrival k
      have hXm := D.constructedPath_measurable (κ := κ) arrival
      have hpiece :
          ∫ s in (D.records arrival k).time..
              (D.records arrival (k + 1)).time,
              D.rate l (D.constructedPath (κ := κ) arrival s) =
            ((D.records arrival (k + 1)).time -
                (D.records arrival k).time) *
              D.rate l (D.recordState arrival k) := by
        have hae : ∀ᵐ s ∂volume,
            s ≠ (D.records arrival (k + 1)).time := by
          filter_upwards [(Set.countable_singleton
            (D.records arrival (k + 1)).time).ae_notMem volume] with s hs
          simpa using hs
        rw [intervalIntegral.integral_congr_ae]
        · rw [intervalIntegral.integral_const, smul_eq_mul]
        · filter_upwards [hae] with s hs hmem
          rw [Set.uIoc_of_le hle] at hmem
          have hslt : s < (D.records arrival (k + 1)).time :=
            lt_of_le_of_ne hmem.2 hs
          rw [D.constructedPath_eq_recordState arrival harrival
            (k := k) (by
              by_contra hkf
              have hterm := D.records_terminal arrival harrival
              have h1 : D.horizon ≤ (D.records arrival k).time :=
                hterm.symm.le.trans
                  (D.records_time_mono arrival harrival (not_lt.mp hkf))
              have h2 := (D.records_admissible arrival harrival (k + 1)).time_le
              exact absurd (lt_of_lt_of_le
                (hmem.1.trans (hslt.trans_le h2)) h1) (lt_irrefl _))
            hmem.1.le hslt]
      rw [D.rate_clock_split _ hXm l (D.records arrival k).time
        (D.records arrival (k + 1)).time, hpiece, mul_add, ← ih]
      simp only [records, nextRecord, recordState]
      ring

/-- The finite-batch readout solves the finite labelled-driver equation. -/
theorem constructedPath_timeChange
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    ∀ t ∈ Icc (0 : ℝ) D.horizon,
      D.constructedPath (κ := κ) arrival t = D.initial +
        ∑ l, (((D.finiteCount arrival l
          ((D.scale : ℝ) *
            clock D.rate (D.constructedPath (κ := κ) arrival) l t) : ℕ) : ℝ) /
              (D.scale : ℝ)) • D.jump l := by
  intro t ht
  by_cases hterminal : t = D.horizon
  · subst t
    rw [D.constructedPath_at_horizon arrival harrival]
    unfold recordState clockState
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [D.recordInternal_eq_scaledClock arrival harrival
      (D.constructionFuel (κ := κ)) l, D.records_terminal arrival harrival]
  · have htlt : t < D.horizon := lt_of_le_of_ne ht.2 hterminal
    obtain ⟨k, hk, hleft, hright⟩ :=
      D.exists_record_interval arrival harrival ht.1 htlt
    rw [D.constructedPath_eq_recordState arrival harrival hk hleft hright]
    unfold recordState clockState
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have hclock :
        (D.scale : ℝ) *
            clock D.rate (D.constructedPath (κ := κ) arrival) l t =
          (D.records arrival k).internal l +
            (D.scale : ℝ) *
              (t - (D.records arrival k).time) *
                D.rate l (D.recordState arrival k) := by
      have hXm := D.constructedPath_measurable (κ := κ) arrival
      have hpiece :
          ∫ s in (D.records arrival k).time..t,
              D.rate l (D.constructedPath (κ := κ) arrival s) =
            (t - (D.records arrival k).time) *
              D.rate l (D.recordState arrival k) := by
        rw [intervalIntegral.integral_congr]
        · rw [intervalIntegral.integral_const, smul_eq_mul]
        · intro s hs
          rw [Set.uIcc_of_le hleft] at hs
          by_cases hst : s = t
          · subst s
            exact congrArg (D.rate l)
              (D.constructedPath_eq_recordState arrival harrival hk
                hleft hright)
          · exact congrArg (D.rate l)
              (D.constructedPath_eq_recordState arrival harrival hk
                hs.1 ((lt_of_le_of_ne hs.2 hst).trans hright))
      rw [D.rate_clock_split _ hXm l (D.records arrival k).time t, hpiece,
        mul_add, ← D.recordInternal_eq_scaledClock arrival harrival k l]
      ring
    rw [hclock]
    exact congrArg (fun m : ℕ => ((m : ℝ) / (D.scale : ℝ)) • D.jump l)
      (D.finiteCount_interpolate_eq arrival harrival hk hleft hright l).symm

/-- The constructor's scaled clocks stay inside the deterministic envelopes. -/
theorem constructed_scaledClock_mem
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    ∀ l t, t ∈ Icc (0 : ℝ) D.horizon →
      (D.scale : ℝ) *
        clock D.rate (D.constructedPath (κ := κ) arrival) l t ∈
          Icc 0 ((D.scale : ℝ) * D.bound l * D.horizon) := by
  intro l t ht
  have hnonneg := clock_nonneg (X := D.constructedPath (κ := κ) arrival)
    D.rate_nonneg l ht.1
  have hle := clock_le D.rate_nonneg D.rate_le D.rate_measurable
    (D.constructedPath_measurable (κ := κ) arrival) l ht.1
  have hscale : (0 : ℝ) ≤ D.scale := Nat.cast_nonneg _
  have hb : D.bound l * t ≤ D.bound l * D.horizon :=
    mul_le_mul_of_nonneg_left ht.2 (D.bound_nonneg l)
  constructor
  · exact mul_nonneg hscale hnonneg
  · calc (D.scale : ℝ) * clock D.rate (D.constructedPath (κ := κ) arrival) l t
        ≤ (D.scale : ℝ) * (D.bound l * t) :=
          mul_le_mul_of_nonneg_left hle hscale
      _ ≤ (D.scale : ℝ) * (D.bound l * D.horizon) :=
          mul_le_mul_of_nonneg_left hb hscale
      _ = (D.scale : ℝ) * D.bound l * D.horizon := by ring

/-- A complete pathwise witness used by the stochastic corollary. -/
structure TimeChangeWitness
    (Y : ι → ℝ → ℕ) : Type where
  path : ℝ → Fin d → ℝ
  measurable_path : Measurable path
  initial_eq : path 0 = D.initial
  equation : ∀ t ∈ Icc (0 : ℝ) D.horizon,
    path t = D.initial +
      ∑ l, (((Y l ((D.scale : ℝ) * clock D.rate path l t) : ℕ) : ℝ) /
        (D.scale : ℝ)) • D.jump l
  scaledClock_mem : ∀ l t, t ∈ Icc (0 : ℝ) D.horizon →
    (D.scale : ℝ) * clock D.rate path l t ∈
      Icc 0 ((D.scale : ℝ) * D.bound l * D.horizon)
  eventually_right : ∀ t, ∀ᶠ s in 𝓝[≥] t, path s = path t
  jumpSupport : Finset ℝ
  eq_of_disjoint : ∀ ⦃s t : ℝ⦄, s ≤ t →
    Disjoint (Ioc s t : Set ℝ) (jumpSupport : Set ℝ) → path s = path t

/-- Existence for a finite labelled driver, allowing repeated arrivals and all
tie batches. -/
theorem finite_batch_timeChange_exists
    (harrival : ∀ l (a : κ l), 0 < arrival l a) :
    Nonempty (D.TimeChangeWitness
      (fun l u => D.finiteCount arrival l u)) := by
  refine ⟨
    { path := D.constructedPath (κ := κ) arrival
      measurable_path := D.constructedPath_measurable (κ := κ) arrival
      initial_eq := by
        have hzero := D.clockState_zero arrival harrival
        by_cases hT : D.horizon = 0
        · calc D.constructedPath (κ := κ) arrival 0
              = D.constructedPath (κ := κ) arrival D.horizon := by rw [hT]
            _ = D.recordState arrival (D.constructionFuel (κ := κ)) :=
                D.constructedPath_at_horizon arrival harrival
            _ = D.initial := by
                have hadm := D.records_admissible arrival harrival
                  (D.constructionFuel (κ := κ))
                have h3 : (D.records arrival (D.constructionFuel (κ := κ))).time = 0 := by
                  rw [D.records_terminal arrival harrival, hT]
                have hint : (D.records arrival (D.constructionFuel (κ := κ))).internal =
                    fun _ => 0 := by
                  funext l
                  have h1 := hadm.internal_le l
                  have h2 := hadm.internal_nonneg l
                  rw [h3, mul_zero] at h1
                  exact le_antisymm h1 h2
                unfold recordState
                rw [hint]
                exact hzero
        · have hTpos : 0 < D.horizon := lt_of_le_of_ne D.horizon_nonneg (Ne.symm hT)
          have hpos : 0 < (D.records arrival (0 + 1)).time := by
            have := D.stepDelay_pos arrival harrival D.initialRecord_admissible
              (by simpa [initialRecord] using hTpos)
            simpa [records, nextRecord, initialRecord] using this
          rw [D.constructedPath_eq_recordState arrival harrival
            (k := 0) (t := 0) (by simp [constructionFuel])
            (by simp [records, initialRecord]) hpos]
          simpa [recordState, records, initialRecord] using hzero
      equation := D.constructedPath_timeChange arrival harrival
      scaledClock_mem := D.constructed_scaledClock_mem arrival harrival
      eventually_right := D.constructedPath_eventually_right (κ := κ) arrival
      jumpSupport := D.constructedJumpSupport (κ := κ) arrival
      eq_of_disjoint := D.constructedPath_hasFiniteJumpSupport
        (κ := κ) arrival }⟩

end BatchData

end Ripple.Kurtz.StrongApprox

end
