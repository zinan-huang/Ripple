/-
  Ripple.CTMC.CTMCProcess — CTMC Path Construction

  Jump-and-hold construction of a CTMC path:
  - Exponential holding times with rate exitRate(current state)
  - Jumps follow the embedded DTMC of the Q-matrix

  A CTMC path records:
  - `init`: starting state
  - `jumps n`: state after the n-th jump (0-indexed, so jumps 0 = after 1st jump)
  - `times n`: cumulative time of the n-th jump
-/

import Ripple.CTMC.CTMC

namespace Ripple.CTMC

open MeasureTheory

/-- A CTMC path: sequence of (holding time, next state) pairs.
The path starts at state `init` and follows the embedded DTMC
with exponential holding times. -/
structure CTMCPath (S : Type*) where
  /-- Initial state before any jumps. -/
  init : S
  /-- State after the n-th jump. `jumps 0` is the state after the first jump. -/
  jumps : ℕ → S
  /-- Cumulative time of the n-th jump. `times n` is when the n-th jump occurs. -/
  times : ℕ → ℝ

variable {S : Type*}

/-- The state of the CTMC at time t.
If t is before the first jump, returns `init`.
Otherwise, finds the last jump that occurred at or before time t. -/
noncomputable def CTMCPath.stateAt (path : CTMCPath S) (t : ℝ) : S :=
  open Classical in
  -- Predicate: the n-th jump happens after time t
  let p (n : ℕ) : Prop := t < path.times n
  if h : ∃ n, p n then
    let n := Nat.find h
    -- n is the first jump index where t < times n
    -- If n = 0, no jumps have occurred by time t → state is init
    -- If n > 0, jump n-1 is the last one before t → state is jumps (n-1)
    if n = 0 then
      path.init
    else
      path.jumps (n - 1)
  else
    -- t is beyond all jump times; stay at the last known state
    path.init

/-- Before the first jump, the state is `init`. -/
theorem CTMCPath.stateAt_before_first (path : CTMCPath S) (t : ℝ)
    (ht : t < path.times 0) : path.stateAt t = path.init := by
  simp only [stateAt]
  have hex : ∃ n, t < path.times n := ⟨0, ht⟩
  rw [dif_pos hex]
  have h0 : Nat.find hex = 0 :=
    Nat.le_zero.mp (Nat.find_min' hex ht)
  simp [h0]

/-- Between two consecutive jumps, the state stays constant. -/
theorem CTMCPath.stateAt_between (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (n : ℕ) (t : ℝ) (hge : path.times n ≤ t) (hlt : t < path.times (n + 1)) :
    path.stateAt t = path.jumps n := by
  simp only [stateAt]
  have hex : ∃ m, t < path.times m := ⟨n + 1, hlt⟩
  rw [dif_pos hex]
  have hfind : Nat.find hex = n + 1 := by
    apply le_antisymm
    · exact Nat.find_min' hex hlt
    · by_contra h
      push Not at h
      have hlt_n : Nat.find hex ≤ n := Nat.lt_succ_iff.mp h
      have := Nat.find_spec hex
      have : path.times (Nat.find hex) ≤ path.times n := by
        exact StrictMono.monotone (fun a b hab => by
          induction hab with
          | refl => exact hstrict a
          | step _ ih => exact lt_trans ih (hstrict _)) hlt_n
      linarith
  simp [hfind]

/-- The n-th holding time. -/
noncomputable def CTMCPath.holdingTime (path : CTMCPath S) (n : ℕ) : ℝ :=
  path.times (n + 1) - path.times n

/-- Start time of the sojourn in `stateSeq n`.  The initial state starts at
clock time `0`; subsequent states start at the previous jump time. -/
noncomputable def CTMCPath.sojournStart (path : CTMCPath S) : ℕ → ℝ
  | 0 => 0
  | n + 1 => path.times n

/-- End time of the sojourn in `stateSeq n`, namely the next jump time. -/
noncomputable def CTMCPath.sojournEnd (path : CTMCPath S) (n : ℕ) : ℝ :=
  path.times n

/-- The clock-time interval on which the path stays in `stateSeq n`, up to the
next jump endpoint.  Endpoints are chosen half-open to match `stateAt` at jump
times. -/
noncomputable def CTMCPath.sojournInterval (path : CTMCPath S) (n : ℕ) :
    Set ℝ :=
  Set.Ico (path.sojournStart n) (path.sojournEnd n)

/-- Length of the sojourn in `stateSeq n`. -/
noncomputable def CTMCPath.sojournTime (path : CTMCPath S) (n : ℕ) : ℝ :=
  path.sojournEnd n - path.sojournStart n

/-- Holding times are positive for strictly increasing jump times. -/
theorem CTMCPath.holdingTime_pos (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1)) (n : ℕ) :
    0 < path.holdingTime n :=
  sub_pos.mpr (hstrict n)

@[simp]
theorem CTMCPath.sojournStart_zero (path : CTMCPath S) :
    path.sojournStart 0 = 0 := rfl

@[simp]
theorem CTMCPath.sojournStart_succ (path : CTMCPath S) (n : ℕ) :
    path.sojournStart (n + 1) = path.times n := rfl

@[simp]
theorem CTMCPath.sojournEnd_eq (path : CTMCPath S) (n : ℕ) :
    path.sojournEnd n = path.times n := rfl

@[simp]
theorem CTMCPath.sojournTime_zero (path : CTMCPath S) :
    path.sojournTime 0 = path.times 0 := by
  simp [sojournTime]

@[simp]
theorem CTMCPath.sojournTime_succ (path : CTMCPath S) (n : ℕ) :
    path.sojournTime (n + 1) = path.times (n + 1) - path.times n := by
  simp [sojournTime]

/-- Sojourn intervals have nonnegative length on compatible-style paths. -/
theorem CTMCPath.sojournTime_nonneg (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    0 ≤ path.sojournTime n := by
  cases n with
  | zero =>
      simp [sojournTime, le_of_lt hpos]
  | succ n =>
      simp [sojournTime, le_of_lt (hstrict n)]

/-- Sojourn start times are nonnegative on compatible-style paths. -/
theorem CTMCPath.sojournStart_nonneg (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) :
    0 ≤ path.sojournStart n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      induction n with
      | zero =>
          exact le_of_lt hpos
      | succ n ih =>
          exact le_trans ih (le_of_lt (hstrict n))

/-- The state sequence: init, then jumps 0, jumps 1, ... -/
def CTMCPath.stateSeq (path : CTMCPath S) : ℕ → S
  | 0 => path.init
  | n + 1 => path.jumps n

/-- A CTMC path is compatible with a Q-matrix if:
- Jump times are strictly increasing and start positive
- Consecutive states differ (actual jumps, not self-transitions) -/
def CTMCPath.IsCompatible [Fintype S] [DecidableEq S]
    (path : CTMCPath S) (Q : QMatrix S) : Prop :=
  (0 < path.times 0) ∧
  (∀ n, path.times n < path.times (n + 1)) ∧
  (path.init ≠ path.jumps 0 ∨ Q.IsAbsorbing path.init)

@[simp]
theorem CTMCPath.stateSeq_zero (path : CTMCPath S) :
    path.stateSeq 0 = path.init := rfl

@[simp]
theorem CTMCPath.stateSeq_succ (path : CTMCPath S) (n : ℕ) :
    path.stateSeq (n + 1) = path.jumps n := rfl

/-- On the half-open sojourn interval for `stateSeq n`, `stateAt` is constant
with value `stateSeq n`. -/
theorem CTMCPath.stateAt_eq_stateSeq_of_mem_sojournInterval
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (n : ℕ) {t : ℝ} (ht : t ∈ path.sojournInterval n) :
    path.stateAt t = path.stateSeq n := by
  cases n with
  | zero =>
      exact path.stateAt_before_first t ht.2
  | succ n =>
      exact path.stateAt_between hstrict n t ht.1 ht.2

/-- Sojourn intervals are Borel measurable clock-time intervals. -/
theorem CTMCPath.measurableSet_sojournInterval
    (path : CTMCPath S) (n : ℕ) :
    MeasurableSet (path.sojournInterval n) := by
  simp [sojournInterval]

/-- The integral of a state observable over one sojourn interval is the
constant state value times the sojourn length. -/
theorem CTMCPath.setIntegral_sojournInterval_stateAt
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : S → ℝ) (n : ℕ) :
    ∫ t in path.sojournInterval n, f (path.stateAt t) =
      f (path.stateSeq n) * path.sojournTime n := by
  have hconst : Set.EqOn (fun t => f (path.stateAt t))
      (fun _ : ℝ => f (path.stateSeq n)) (path.sojournInterval n) := by
    intro t ht
    simpa using congrArg f
      (path.stateAt_eq_stateSeq_of_mem_sojournInterval hstrict n ht)
  have hstart_le_end : path.sojournStart n ≤ path.sojournEnd n := by
    simpa [sojournTime, sub_nonneg] using path.sojournTime_nonneg hstrict hpos n
  calc
    ∫ t in path.sojournInterval n, f (path.stateAt t)
        = ∫ t in path.sojournInterval n, f (path.stateSeq n) := by
            exact setIntegral_congr_fun
              (path.measurableSet_sojournInterval n) hconst
    _ = volume.real (path.sojournInterval n) * f (path.stateSeq n) := by
          rw [setIntegral_const, smul_eq_mul]
    _ = f (path.stateSeq n) * path.sojournTime n := by
          rw [sojournInterval, Real.volume_real_Ico_of_le hstart_le_end]
          simp [sojournTime]
          ring

/-- A state observable along `stateAt` is integrable over each finite sojourn
interval, because it is constant there. -/
theorem CTMCPath.integrableOn_sojournInterval_stateAt
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (f : S → ℝ) (n : ℕ) :
    IntegrableOn (fun t => f (path.stateAt t)) (path.sojournInterval n) volume := by
  have hconst : Set.EqOn (fun t => f (path.stateAt t))
      (fun _ : ℝ => f (path.stateSeq n)) (path.sojournInterval n) := by
    intro t ht
    simpa using congrArg f
      (path.stateAt_eq_stateSeq_of_mem_sojournInterval hstrict n ht)
  exact (integrableOn_const measure_Ico_lt_top.ne).congr_fun hconst.symm
    (path.measurableSet_sojournInterval n)

/-- stateAt agrees with stateSeq at jump times: at time just after
the n-th jump (but before the (n+1)-th), the state is jumps n. -/
theorem CTMCPath.stateAt_eq_stateSeq_succ (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (n : ℕ) : path.stateAt (path.times n) = path.stateSeq (n + 1) := by
  cases n with
  | zero =>
    simp only [stateSeq_succ]
    exact path.stateAt_between hstrict 0 (path.times 0) le_rfl (hstrict 0)
  | succ k =>
    simp only [stateSeq_succ]
    exact path.stateAt_between hstrict (k + 1) (path.times (k + 1)) le_rfl (hstrict (k + 1))

/-- Cumulative time is monotone for strictly increasing paths. -/
theorem CTMCPath.times_strictMono (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1)) :
    StrictMono path.times := by
  intro a b hab
  induction hab with
  | refl => exact hstrict a
  | step _ ih => exact lt_trans ih (hstrict _)

/-- Jump count: the number of jumps that have occurred by time t. -/
noncomputable def CTMCPath.jumpCount (path : CTMCPath S) (t : ℝ) : ℕ :=
  open Classical in
  if h : ∃ n, t < path.times n then
    Nat.find h
  else
    0

/-- WithTop-valued jump count at a clock time: the first jump time after `t`,
or `⊤` if no future jump time exists.  This avoids the finite fallback value
used by `jumpCount` and is the natural stopping-time version. -/
noncomputable def CTMCPath.jumpCountTop (path : CTMCPath S) (t : ℝ) : WithTop ℕ :=
  open Classical in
  if h : ∃ n, t < path.times n then
    (Nat.find h : WithTop ℕ)
  else
    ⊤

@[simp]
theorem CTMCPath.jumpCountTop_eq_top_of_not_exists
    (path : CTMCPath S) {t : ℝ} (h : ¬ ∃ n, t < path.times n) :
    path.jumpCountTop t = ⊤ := by
  simp [jumpCountTop, h]

theorem CTMCPath.jumpCountTop_eq_natFind_of_exists
    (path : CTMCPath S) {t : ℝ} (h : ∃ n, t < path.times n) :
    path.jumpCountTop t = (Nat.find h : WithTop ℕ) := by
  simp [jumpCountTop, h]

theorem CTMCPath.jumpCountTop_eq_jumpCount_of_exists
    (path : CTMCPath S) {t : ℝ} (h : ∃ n, t < path.times n) :
    path.jumpCountTop t = (path.jumpCount t : WithTop ℕ) := by
  simp [jumpCountTop, jumpCount, h]

/-- For strictly increasing jump times, the WithTop jump count is at most `n`
exactly when the `n`-th jump time is after the clock time. -/
theorem CTMCPath.jumpCountTop_le_coe_iff
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (t : ℝ) (n : ℕ) :
    path.jumpCountTop t ≤ (n : WithTop ℕ) ↔ t < path.times n := by
  constructor
  · intro hle
    by_cases hfuture : ∃ m, t < path.times m
    · have hfind_le : Nat.find hfuture ≤ n := by
        have hle' : (Nat.find hfuture : WithTop ℕ) ≤ (n : WithTop ℕ) := by
          simpa [jumpCountTop, hfuture] using hle
        exact_mod_cast hle'
      exact lt_of_lt_of_le (Nat.find_spec hfuture)
        ((path.times_strictMono hstrict).monotone hfind_le)
    · simp [jumpCountTop, hfuture] at hle
  · intro htn
    have hfuture : ∃ m, t < path.times m := ⟨n, htn⟩
    rw [path.jumpCountTop_eq_natFind_of_exists hfuture]
    exact_mod_cast Nat.find_min' hfuture htn

/-- Exact finite-level characterization of the WithTop jump count, without
assuming monotone jump times. -/
theorem CTMCPath.jumpCountTop_le_coe_iff_exists_le
    (path : CTMCPath S) (t : ℝ) (n : ℕ) :
    path.jumpCountTop t ≤ (n : WithTop ℕ) ↔
      ∃ k ≤ n, t < path.times k := by
  constructor
  · intro hle
    by_cases hfuture : ∃ m, t < path.times m
    · have hfind_le : Nat.find hfuture ≤ n := by
        have hle' : (Nat.find hfuture : WithTop ℕ) ≤ (n : WithTop ℕ) := by
          simpa [jumpCountTop, hfuture] using hle
        exact_mod_cast hle'
      exact ⟨Nat.find hfuture, hfind_le, Nat.find_spec hfuture⟩
    · simp [jumpCountTop, hfuture] at hle
  · rintro ⟨k, hk, htk⟩
    have hfuture : ∃ m, t < path.times m := ⟨k, htk⟩
    rw [path.jumpCountTop_eq_natFind_of_exists hfuture]
    exact_mod_cast le_trans (Nat.find_min' hfuture htk) hk

/-- Before the first jump, the jump count is 0. -/
theorem CTMCPath.jumpCount_before_first (path : CTMCPath S) (t : ℝ)
    (ht : t < path.times 0) : path.jumpCount t = 0 := by
  simp only [jumpCount]
  have hex : ∃ n, t < path.times n := ⟨0, ht⟩
  rw [dif_pos hex]
  exact Nat.le_zero.mp (Nat.find_min' hex ht)

/-- Between the n-th and (n+1)-th jump, the jump count is n+1. -/
theorem CTMCPath.jumpCount_between (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (n : ℕ) (t : ℝ) (hge : path.times n ≤ t) (hlt : t < path.times (n + 1)) :
    path.jumpCount t = n + 1 := by
  simp only [jumpCount]
  have hex : ∃ m, t < path.times m := ⟨n + 1, hlt⟩
  rw [dif_pos hex]
  apply le_antisymm
  · exact Nat.find_min' hex hlt
  · by_contra h
    push Not at h
    have hlt_n : Nat.find hex ≤ n := Nat.lt_succ_iff.mp h
    have := Nat.find_spec hex
    have : path.times (Nat.find hex) ≤ path.times n :=
      StrictMono.monotone (path.times_strictMono hstrict) hlt_n
    linarith

/-- The explosion time: sup of all jump times.
If the process makes infinitely many jumps in finite time, this is finite. -/
noncomputable def CTMCPath.explosionTime (path : CTMCPath S) : ℝ :=
  sSup (Set.range path.times)

/-- The first jump time is positive for compatible paths. -/
theorem CTMCPath.first_jump_pos (path : CTMCPath S) [Fintype S] [DecidableEq S]
    (Q : QMatrix S) (hc : path.IsCompatible Q) : 0 < path.times 0 :=
  hc.1

/-- All jump times are positive for compatible paths. -/
theorem CTMCPath.times_pos (path : CTMCPath S) [Fintype S] [DecidableEq S]
    (Q : QMatrix S) (hc : path.IsCompatible Q) (n : ℕ) : 0 < path.times n := by
  induction n with
  | zero => exact hc.1
  | succ k ih => exact lt_trans ih (hc.2.1 k)

/-- The state just before the first jump is init. -/
theorem CTMCPath.stateAt_zero (path : CTMCPath S)
    (hpos : 0 < path.times 0) : path.stateAt 0 = path.init :=
  path.stateAt_before_first 0 hpos

/-- The state at time t depends only on the jump count.
If jumpCount = 0, state = init. If jumpCount = n+1, state = jumps n. -/
theorem CTMCPath.stateAt_eq_stateSeq_jumpCount (path : CTMCPath S)
    (_hstrict : ∀ n, path.times n < path.times (n + 1))
    (t : ℝ) (hex : ∃ n, t < path.times n) :
    path.stateAt t = path.stateSeq (path.jumpCount t) := by
  simp only [stateAt, jumpCount]
  rw [dif_pos hex, dif_pos hex]
  cases Nat.find hex with
  | zero => simp [stateSeq]
  | succ k => simp [stateSeq]

/-- If `n` is the first jump index whose jump time is after `t`, then the
state at time `t` is exactly the `n`-th state in the path state sequence. -/
theorem CTMCPath.stateAt_eq_stateSeq_of_first_time_gt (path : CTMCPath S)
    (t : ℝ) {n : ℕ}
    (hn : t < path.times n)
    (hmin : ∀ k ∈ Finset.range n, ¬ t < path.times k) :
    path.stateAt t = path.stateSeq n := by
  simp only [stateAt]
  have hex : ∃ m, t < path.times m := ⟨n, hn⟩
  rw [dif_pos hex]
  have hfind : Nat.find hex = n := by
    apply le_antisymm
    · exact Nat.find_min' hex hn
    · by_contra hle
      have hlt : Nat.find hex < n := Nat.lt_of_not_ge hle
      exact (hmin (Nat.find hex) (Finset.mem_range.mpr hlt)) (Nat.find_spec hex)
  cases n with
  | zero =>
      simp [hfind, stateSeq]
  | succ k =>
      simp [hfind, stateSeq]

/-- Jump times are nonneg for paths with positive first jump time. -/
theorem CTMCPath.times_nonneg (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (n : ℕ) : 0 ≤ path.times n := by
  induction n with
  | zero => exact le_of_lt hpos
  | succ k ih => exact le_of_lt (lt_of_le_of_lt ih (hstrict k))

/-- Holding times are equal to the difference of consecutive jump times. -/
theorem CTMCPath.holdingTime_eq (path : CTMCPath S) (n : ℕ) :
    path.holdingTime n = path.times (n + 1) - path.times n :=
  rfl

/-- The n-th jump time equals the sum of holding times.
times n = times 0 + ∑_{k=0}^{n-1} holdingTime k. -/
theorem CTMCPath.times_eq_sum_holdingTimes (path : CTMCPath S) (n : ℕ) :
    path.times n = path.times 0 + ∑ k ∈ Finset.range n, path.holdingTime k := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    simp [holdingTime]

/-! ## Non-explosion and finite jump counts -/

/-- A CTMC path is non-explosive if the jump times diverge to infinity:
for every finite time horizon T, only finitely many jumps occur. -/
def CTMCPath.NonExplosive (path : CTMCPath S) : Prop :=
  Filter.Tendsto path.times Filter.atTop Filter.atTop

/-- It is enough for non-explosion that the partial sums of holding times
diverge to infinity. -/
theorem CTMCPath.nonExplosive_of_holdingTime_sum_tendsto_atTop (path : CTMCPath S)
    (h : Filter.Tendsto
      (fun n => ∑ k ∈ Finset.range n, path.holdingTime k)
      Filter.atTop Filter.atTop) :
    path.NonExplosive := by
  rw [CTMCPath.NonExplosive]
  rw [show path.times =
      (fun n => path.times 0 + ∑ k ∈ Finset.range n, path.holdingTime k) by
    funext n
    exact path.times_eq_sum_holdingTimes n]
  exact tendsto_const_nhds.add_atTop h

/-- If holding times are nonnegative and the number of holding times at least
`ε` tends to infinity, then the holding-time partial sums diverge. -/
theorem CTMCPath.holdingTime_sum_tendsto_atTop_of_large_count_tendsto
    (path : CTMCPath S) (hnonneg : ∀ n, 0 ≤ path.holdingTime n)
    {ε : ℝ} (hε : 0 < ε)
    (hcount : Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun k => ε ≤ path.holdingTime k).card : ℝ))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, path.holdingTime k)
      Filter.atTop Filter.atTop := by
  have hscaled : Filter.Tendsto
      (fun N : ℕ =>
        ε * (((Finset.range N).filter fun k => ε ≤ path.holdingTime k).card : ℝ))
      Filter.atTop Filter.atTop :=
    hcount.const_mul_atTop hε
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hscaled
  filter_upwards with N
  calc
    ε * (((Finset.range N).filter fun k => ε ≤ path.holdingTime k).card : ℝ)
        = ∑ k ∈ (Finset.range N).filter (fun k => ε ≤ path.holdingTime k), ε := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ (Finset.range N).filter (fun k => ε ≤ path.holdingTime k),
          path.holdingTime k := by
          exact Finset.sum_le_sum fun k hk => (Finset.mem_filter.mp hk).2
    _ ≤ ∑ k ∈ Finset.range N, path.holdingTime k := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset (fun k => ε ≤ path.holdingTime k) (Finset.range N))
            (fun k _ _ => hnonneg k)

/-- Non-explosion follows if nonnegative holding times exceed a fixed positive
threshold unboundedly many times. -/
theorem CTMCPath.nonExplosive_of_large_holdingTime_count_tendsto
    (path : CTMCPath S) (hnonneg : ∀ n, 0 ≤ path.holdingTime n)
    {ε : ℝ} (hε : 0 < ε)
    (hcount : Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun k => ε ≤ path.holdingTime k).card : ℝ))
      Filter.atTop Filter.atTop) :
    path.NonExplosive :=
  path.nonExplosive_of_holdingTime_sum_tendsto_atTop
    (path.holdingTime_sum_tendsto_atTop_of_large_count_tendsto hnonneg hε hcount)

/-- Strict-threshold variant of `nonExplosive_of_large_holdingTime_count_tendsto`.
This is convenient for Borel-Cantelli inputs phrased as events
`ε < holdingTime n`. -/
theorem CTMCPath.nonExplosive_of_large_holdingTime_strict_count_tendsto
    (path : CTMCPath S) (hnonneg : ∀ n, 0 ≤ path.holdingTime n)
    {ε : ℝ} (hε : 0 < ε)
    (hcount : Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun k => ε < path.holdingTime k).card : ℝ))
      Filter.atTop Filter.atTop) :
    path.NonExplosive := by
  have hweak : Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter fun k => ε ≤ path.holdingTime k).card : ℝ))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hcount
    filter_upwards with N
    exact_mod_cast Finset.card_le_card
      (by
        intro k hk
        simp only [Finset.mem_filter] at hk ⊢
        exact ⟨hk.1, le_of_lt hk.2⟩)
  exact path.nonExplosive_of_large_holdingTime_count_tendsto hnonneg hε hweak

/-- A non-explosive path has
finitely many jumps before any finite time T. -/
theorem CTMCPath.exists_bound_of_nonExplosive (path : CTMCPath S)
    (hne : path.NonExplosive) (T : ℝ) :
    ∃ N, T < path.times N := by
  have hdiv := (Filter.tendsto_atTop_atTop.mp
    (show Filter.Tendsto path.times Filter.atTop Filter.atTop from hne)) (T + 1)
  obtain ⟨N, hN⟩ := hdiv
  exact ⟨N, by linarith [hN N le_rfl]⟩

/-- For a non-explosive path, there exists a jump time beyond any T. -/
theorem CTMCPath.jumpCount_lt_of_nonExplosive (path : CTMCPath S)
    (hne : path.NonExplosive) (_hstrict : ∀ n, path.times n < path.times (n + 1))
    (T : ℝ) : ∃ n, T < path.times n :=
  path.exists_bound_of_nonExplosive hne T

/-- On a non-explosive path, `stateAt` is always determined by `jumpCount`
at finite times, without separately passing a future-jump witness. -/
theorem CTMCPath.stateAt_eq_stateSeq_jumpCount_of_nonExplosive (path : CTMCPath S)
    (hne : path.NonExplosive)
    (hstrict : ∀ n, path.times n < path.times (n + 1)) (t : ℝ) :
    path.stateAt t = path.stateSeq (path.jumpCount t) :=
  path.stateAt_eq_stateSeq_jumpCount hstrict t
    (path.exists_bound_of_nonExplosive hne t)

/-- The jump count is monotone: if s ≤ t then jumpCount s ≤ jumpCount t. -/
theorem CTMCPath.jumpCount_mono (path : CTMCPath S)
    (_hstrict : ∀ n, path.times n < path.times (n + 1))
    {s t : ℝ} (hst : s ≤ t) (hs : ∃ n, s < path.times n)
    (ht : ∃ n, t < path.times n) :
    path.jumpCount s ≤ path.jumpCount t := by
  simp only [jumpCount, dif_pos hs, dif_pos ht]
  by_contra h
  push Not at h
  have hfind_t := Nat.find_spec ht
  have := Nat.find_min hs (show Nat.find ht < Nat.find hs from h)
  push Not at this
  linarith

/-- The state at any time before time T is determined by the first
jumpCount(T) jumps. -/
theorem CTMCPath.stateAt_of_le (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {s T : ℝ} (hst : s ≤ T) (hT : ∃ n, T < path.times n) :
    ∃ k ≤ path.jumpCount T, path.stateAt s = path.stateSeq k := by
  have hs : ∃ n, s < path.times n := by
    obtain ⟨n, hn⟩ := hT
    exact ⟨n, lt_of_le_of_lt hst hn⟩
  rw [path.stateAt_eq_stateSeq_jumpCount hstrict s hs]
  exact ⟨path.jumpCount s, path.jumpCount_mono hstrict hst hs hT, rfl⟩

/-- The jump count is bounded by n+1 when t < times(n+1). -/
theorem CTMCPath.jumpCount_le_of_lt (path : CTMCPath S)
    (_hstrict : ∀ n, path.times n < path.times (n + 1))
    {t : ℝ} {n : ℕ} (ht : t < path.times (n + 1)) :
    path.jumpCount t ≤ n + 1 := by
  simp only [jumpCount]
  have hex : ∃ m, t < path.times m := ⟨n + 1, ht⟩
  rw [dif_pos hex]
  exact Nat.find_min' hex ht

/-- If a future jump time exists, the jump time indexed by `jumpCount t` is
strictly after `t`. -/
theorem CTMCPath.lt_times_jumpCount_of_exists (path : CTMCPath S)
    {t : ℝ} (hfuture : ∃ n, t < path.times n) :
    t < path.times (path.jumpCount t) := by
  simp only [jumpCount]
  rw [dif_pos hfuture]
  exact Nat.find_spec hfuture

/-- Every jump index strictly before `jumpCount t` has jump time at or before
`t`. -/
theorem CTMCPath.times_le_of_lt_jumpCount (path : CTMCPath S)
    {t : ℝ} {k : ℕ} (hfuture : ∃ n, t < path.times n)
    (hk : k < path.jumpCount t) :
    path.times k ≤ t := by
  simp only [jumpCount] at hk
  rw [dif_pos hfuture] at hk
  by_contra hle
  push Not at hle
  have hfind_le : Nat.find hfuture ≤ k := Nat.find_min' hfuture hle
  exact (not_lt_of_ge hfind_le) hk

/-- If at least one jump has occurred by `t`, then the previous jump time is at
or before `t`. -/
theorem CTMCPath.times_pred_jumpCount_le_of_pos (path : CTMCPath S)
    {t : ℝ} (hfuture : ∃ n, t < path.times n)
    (hpos : 0 < path.jumpCount t) :
    path.times (path.jumpCount t - 1) ≤ t := by
  cases hcount : path.jumpCount t with
  | zero =>
      simp [hcount] at hpos
  | succ n =>
      have hk : n < path.jumpCount t := by
        rw [hcount]
        exact Nat.lt_succ_self n
      simpa [hcount] using path.times_le_of_lt_jumpCount hfuture hk

/-- If `jumpCount t = 0` and a future jump exists, then `t` is before the first
jump. -/
theorem CTMCPath.lt_times_zero_of_jumpCount_eq_zero (path : CTMCPath S)
    {t : ℝ} (hfuture : ∃ n, t < path.times n)
    (hcount : path.jumpCount t = 0) :
    t < path.times 0 := by
  simpa [hcount] using path.lt_times_jumpCount_of_exists hfuture

/-- If at least one jump has occurred by `t`, then `t` lies in the current
holding interval bracketed by the previous jump time and the next jump time
indexed by `jumpCount t`. -/
theorem CTMCPath.current_interval_of_jumpCount_pos (path : CTMCPath S)
    {t : ℝ} (hfuture : ∃ n, t < path.times n)
    (hpos : 0 < path.jumpCount t) :
    path.times (path.jumpCount t - 1) ≤ t ∧
      t < path.times (path.jumpCount t) :=
  ⟨path.times_pred_jumpCount_le_of_pos hfuture hpos,
    path.lt_times_jumpCount_of_exists hfuture⟩

/-- Characterization of `jumpCount t`: either it is the first jump time after
`t`, or no future jump time exists and the fallback value is `0`. -/
theorem CTMCPath.jumpCount_eq_iff (path : CTMCPath S) (t : ℝ) (n : ℕ) :
    path.jumpCount t = n ↔
      (t < path.times n ∧ ∀ k < n, ¬ t < path.times k) ∨
        (n = 0 ∧ ∀ k, ¬ t < path.times k) := by
  by_cases hfuture : ∃ k, t < path.times k
  · simp [jumpCount, hfuture, Nat.find_eq_iff hfuture]
  · have hnone : ∀ k, ¬ t < path.times k := by
      simpa [not_exists] using hfuture
    simp [jumpCount, hnone, eq_comm]

/-- A completed sojourn interval lies inside `[0,T]` whenever its index is
strictly below `jumpCount T`. -/
theorem CTMCPath.sojournInterval_subset_Icc_of_lt_jumpCount
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} (hfuture : ∃ n, T < path.times n)
    {k : ℕ} (hk : k < path.jumpCount T) :
    path.sojournInterval k ⊆ Set.Icc (0 : ℝ) T := by
  intro t ht
  constructor
  · cases k with
    | zero =>
        exact ht.1
    | succ k =>
        exact le_trans (path.times_nonneg hstrict hpos k) ht.1
  · have hend_le : path.sojournEnd k ≤ T := by
      simpa [sojournEnd] using path.times_le_of_lt_jumpCount hfuture hk
    exact le_trans (le_of_lt ht.2) hend_le

/-- Earlier sojourn intervals end before later sojourn intervals start. -/
theorem CTMCPath.sojournEnd_le_sojournStart_of_lt
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {k l : ℕ} (hkl : k < l) :
    path.sojournEnd k ≤ path.sojournStart l := by
  cases l with
  | zero =>
      exact (Nat.not_lt_zero k hkl).elim
  | succ l =>
      simp only [sojournEnd, sojournStart_succ]
      cases k with
      | zero =>
          have hle : 0 ≤ l := Nat.zero_le l
          exact (path.times_strictMono hstrict).monotone hle
      | succ k =>
          have hle : k + 1 ≤ l := Nat.succ_le_succ_iff.mp hkl
          exact (path.times_strictMono hstrict).monotone hle

/-- Sojourn intervals are pairwise disjoint on paths with strictly increasing
jump times. -/
theorem CTMCPath.pairwise_disjoint_sojournInterval
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1)) :
    Set.Pairwise Set.univ
      (fun k l => Disjoint (path.sojournInterval k) (path.sojournInterval l)) := by
  intro k _hk l _hl hkl
  rw [Set.disjoint_left]
  intro t htk htl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hend_start := path.sojournEnd_le_sojournStart_of_lt hstrict hlt
    exact not_lt_of_ge (le_trans hend_start htl.1) htk.2
  · have hend_start := path.sojournEnd_le_sojournStart_of_lt hstrict hgt
    exact not_lt_of_ge (le_trans hend_start htk.1) htl.2

/-- Integral over a finite union of completed sojourn intervals splits as the
finite sum of constant state values times sojourn lengths. -/
theorem CTMCPath.setIntegral_biUnion_sojournInterval_stateAt
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : S → ℝ) (n : ℕ) :
    ∫ t in ⋃ k ∈ Finset.range n, path.sojournInterval k, f (path.stateAt t) =
      ∑ k ∈ Finset.range n, f (path.stateSeq k) * path.sojournTime k := by
  have hmeas : ∀ k ∈ Finset.range n, MeasurableSet (path.sojournInterval k) :=
    fun k _ => path.measurableSet_sojournInterval k
  have hpair : Set.Pairwise (↑(Finset.range n))
      (fun k l => Disjoint (path.sojournInterval k) (path.sojournInterval l)) := by
    intro k hk l hl hkl
    rw [Set.disjoint_left]
    intro t htk htl
    rcases lt_or_gt_of_ne hkl with hlt | hgt
    · have hend_start := path.sojournEnd_le_sojournStart_of_lt hstrict hlt
      exact not_lt_of_ge (le_trans hend_start htl.1) htk.2
    · have hend_start := path.sojournEnd_le_sojournStart_of_lt hstrict hgt
      exact not_lt_of_ge (le_trans hend_start htk.1) htl.2
  have hint : ∀ k ∈ Finset.range n,
      IntegrableOn (fun t => f (path.stateAt t)) (path.sojournInterval k) volume :=
    fun k _ => path.integrableOn_sojournInterval_stateAt hstrict f k
  calc
    ∫ t in ⋃ k ∈ Finset.range n, path.sojournInterval k, f (path.stateAt t)
        = ∑ k ∈ Finset.range n,
            ∫ t in path.sojournInterval k, f (path.stateAt t) := by
            exact integral_biUnion_finset (Finset.range n) hmeas hpair hint
    _ = ∑ k ∈ Finset.range n, f (path.stateSeq k) * path.sojournTime k := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          exact path.setIntegral_sojournInterval_stateAt hstrict hpos f k

/-- The completed sojourn contribution up to `jumpCount T` is bounded by the
clock-time integral over `[0,T]`, for nonnegative state observables. -/
theorem CTMCPath.sum_sojournTime_mul_le_setIntegral_Icc
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : S → ℝ) {T : ℝ}
    (hfuture : ∃ n, T < path.times n)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : IntegrableOn (fun t => f (path.stateAt t))
      (Set.Icc (0 : ℝ) T) volume) :
    (∑ k ∈ Finset.range (path.jumpCount T),
      f (path.stateSeq k) * path.sojournTime k) ≤
      ∫ t in Set.Icc (0 : ℝ) T, f (path.stateAt t) := by
  let U : Set ℝ := ⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k
  have hU_subset : U ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    simp only [U, Set.mem_iUnion, exists_prop] at ht
    obtain ⟨k, hk, htk⟩ := ht
    exact path.sojournInterval_subset_Icc_of_lt_jumpCount hstrict hpos hfuture
      (Finset.mem_range.mp hk) htk
  have hU_ae : U ≤ᵐ[volume] Set.Icc (0 : ℝ) T :=
    Filter.Eventually.of_forall fun t ht => hU_subset ht
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
        fun t => f (path.stateAt t) :=
    Filter.Eventually.of_forall fun t => hf_nonneg (path.stateAt t)
  have hmono :
      ∫ t in U, f (path.stateAt t) ≤
        ∫ t in Set.Icc (0 : ℝ) T, f (path.stateAt t) :=
    setIntegral_mono_set hf_int hnonneg hU_ae
  have hsplit :
      ∫ t in U, f (path.stateAt t) =
        ∑ k ∈ Finset.range (path.jumpCount T),
          f (path.stateSeq k) * path.sojournTime k := by
    simpa [U] using
      path.setIntegral_biUnion_sojournInterval_stateAt hstrict hpos f
        (path.jumpCount T)
  rw [hsplit] at hmono
  exact hmono

/-- The elapsed time in the current sojourn at clock time `T`. -/
noncomputable def CTMCPath.currentSojournElapsed (path : CTMCPath S) (T : ℝ) : ℝ :=
  T - path.sojournStart (path.jumpCount T)

/-- At a nonnegative clock time with a future jump, the current sojourn has
already started. -/
theorem CTMCPath.sojournStart_jumpCount_le_of_exists
    (path : CTMCPath S) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) :
    path.sojournStart (path.jumpCount T) ≤ T := by
  cases hcount : path.jumpCount T with
  | zero =>
      simpa [hcount] using hT
  | succ n =>
      have hpos : 0 < path.jumpCount T := by
        rw [hcount]
        exact Nat.succ_pos n
      simpa [hcount] using path.times_pred_jumpCount_le_of_pos hfuture hpos

@[simp]
theorem CTMCPath.currentSojournElapsed_eq
    (path : CTMCPath S) (T : ℝ) :
    path.currentSojournElapsed T =
      T - path.sojournStart (path.jumpCount T) := rfl

/-- The current sojourn elapsed time is nonnegative on nonnegative clock times
with a future jump. -/
theorem CTMCPath.currentSojournElapsed_nonneg
    (path : CTMCPath S) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) :
    0 ≤ path.currentSojournElapsed T := by
  rw [currentSojournElapsed]
  exact sub_nonneg.mpr (path.sojournStart_jumpCount_le_of_exists hT hfuture)

/-- The current sojourn elapsed time is at most the clock horizon. -/
theorem CTMCPath.currentSojournElapsed_le
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} :
    path.currentSojournElapsed T ≤ T := by
  rw [currentSojournElapsed]
  have hstart_nonneg :
      0 ≤ path.sojournStart (path.jumpCount T) :=
    path.sojournStart_nonneg hstrict hpos (path.jumpCount T)
  linarith

/-- The elapsed time in the current sojourn is bounded by the full sojourn
length whenever a future jump exists. -/
theorem CTMCPath.currentSojournElapsed_le_sojournTime
    (path : CTMCPath S) {T : ℝ}
    (hfuture : ∃ n, T < path.times n) :
    path.currentSojournElapsed T ≤ path.sojournTime (path.jumpCount T) := by
  rw [currentSojournElapsed, sojournTime, sojournEnd]
  exact sub_le_sub_right
    (le_of_lt (path.lt_times_jumpCount_of_exists hfuture))
    (path.sojournStart (path.jumpCount T))

/-- Squared elapsed time in the current sojourn is bounded by the squared full
sojourn length on compatible-style paths. -/
theorem CTMCPath.currentSojournElapsed_sq_le_sojournTime_sq
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) :
    path.currentSojournElapsed T ^ 2 ≤
      path.sojournTime (path.jumpCount T) ^ 2 := by
  have hel0 : 0 ≤ path.currentSojournElapsed T :=
    path.currentSojournElapsed_nonneg hT hfuture
  have hsoj0 : 0 ≤ path.sojournTime (path.jumpCount T) :=
    path.sojournTime_nonneg hstrict hpos (path.jumpCount T)
  exact sq_le_sq'
    (le_trans (neg_nonpos.mpr hsoj0) hel0)
    (path.currentSojournElapsed_le_sojournTime hfuture)

/-- At a time with a future jump, the current sojourn interval contains the
clock time itself. -/
theorem CTMCPath.mem_sojournInterval_jumpCount
    (path : CTMCPath S) {t : ℝ} (ht : 0 ≤ t)
    (hfuture : ∃ n, t < path.times n) :
    t ∈ path.sojournInterval (path.jumpCount t) := by
  constructor
  · exact path.sojournStart_jumpCount_le_of_exists ht hfuture
  · simpa [sojournEnd] using path.lt_times_jumpCount_of_exists hfuture

/-- The completed sojourn intervals before `T`, together with the current
partial sojourn, cover `[0,T]`. -/
theorem CTMCPath.Icc_subset_completed_union_current_sojourn
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {T : ℝ}
    (hfuture : ∃ n, T < path.times n) :
    Set.Icc (0 : ℝ) T ⊆
      (⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k) ∪
        Set.Icc (path.sojournStart (path.jumpCount T)) T := by
  intro t htI
  by_cases hcur : path.sojournStart (path.jumpCount T) ≤ t
  · exact Or.inr ⟨hcur, htI.2⟩
  · have ht_future : ∃ n, t < path.times n := by
      obtain ⟨n, hn⟩ := hfuture
      exact ⟨n, lt_of_le_of_lt htI.2 hn⟩
    have hjc_le : path.jumpCount t ≤ path.jumpCount T :=
      path.jumpCount_mono hstrict htI.2 ht_future hfuture
    have hmem_t :
        t ∈ path.sojournInterval (path.jumpCount t) :=
      path.mem_sojournInterval_jumpCount htI.1 ht_future
    have hlt : path.jumpCount t < path.jumpCount T := by
      exact lt_of_le_of_ne hjc_le fun h_eq => by
        apply hcur
        simpa [h_eq] using hmem_t.1
    left
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨path.jumpCount t, Finset.mem_range.mpr hlt, hmem_t⟩

/-- The completed sojourn intervals before `T`, together with the current
partial sojourn, are contained in `[0,T]`. -/
theorem CTMCPath.completed_union_current_sojourn_subset_Icc
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ}
    (hfuture : ∃ n, T < path.times n) :
    (⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k) ∪
        Set.Icc (path.sojournStart (path.jumpCount T)) T ⊆
      Set.Icc (0 : ℝ) T := by
  intro t ht
  rcases ht with htU | htC
  · simp only [Set.mem_iUnion, exists_prop] at htU
    obtain ⟨k, hk, htk⟩ := htU
    exact path.sojournInterval_subset_Icc_of_lt_jumpCount hstrict hpos hfuture
      (Finset.mem_range.mp hk) htk
  · exact ⟨le_trans (path.sojournStart_nonneg hstrict hpos (path.jumpCount T)) htC.1,
      htC.2⟩

/-- The completed sojourn intervals before `T`, together with the current
partial sojourn, are exactly `[0,T]`. -/
theorem CTMCPath.completed_union_current_sojourn_eq_Icc
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) {T : ℝ}
    (hfuture : ∃ n, T < path.times n) :
    (⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k) ∪
        Set.Icc (path.sojournStart (path.jumpCount T)) T =
      Set.Icc (0 : ℝ) T := by
  exact Set.Subset.antisymm
    (path.completed_union_current_sojourn_subset_Icc hstrict hpos hfuture)
    (path.Icc_subset_completed_union_current_sojourn hstrict hfuture)

/-- On the partial current sojourn interval ending at `T`, `stateAt` is
constant with value `stateSeq (jumpCount T)`. -/
theorem CTMCPath.stateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    {T t : ℝ} (hfuture : ∃ n, T < path.times n)
    (ht : t ∈ Set.Icc (path.sojournStart (path.jumpCount T)) T) :
    path.stateAt t = path.stateSeq (path.jumpCount T) := by
  cases hcount : path.jumpCount T with
  | zero =>
      have hTlt : T < path.times 0 :=
        path.lt_times_zero_of_jumpCount_eq_zero hfuture hcount
      exact path.stateAt_before_first t (lt_of_le_of_lt ht.2 hTlt)
  | succ n =>
      have hTlt : T < path.times (n + 1) := by
        simpa [hcount] using path.lt_times_jumpCount_of_exists hfuture
      have htlo : path.times n ≤ t := by
        simpa [hcount] using ht.1
      have hthi : t < path.times (n + 1) := lt_of_le_of_lt ht.2 hTlt
      simpa [hcount] using path.stateAt_between hstrict n t htlo hthi

/-- Integral over the partial current sojourn interval ending at `T`. -/
theorem CTMCPath.setIntegral_currentSojourn_stateAt
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (f : S → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n) :
    ∫ t in Set.Icc (path.sojournStart (path.jumpCount T)) T,
        f (path.stateAt t) =
      f (path.stateSeq (path.jumpCount T)) * path.currentSojournElapsed T := by
  have hconst : Set.EqOn (fun t => f (path.stateAt t))
      (fun _ : ℝ => f (path.stateSeq (path.jumpCount T)))
      (Set.Icc (path.sojournStart (path.jumpCount T)) T) := by
    intro t ht
    simpa using congrArg f
      (path.stateAt_eq_stateSeq_jumpCount_of_mem_currentSojourn hstrict hfuture ht)
  have hstart_le : path.sojournStart (path.jumpCount T) ≤ T :=
    path.sojournStart_jumpCount_le_of_exists hT hfuture
  calc
    ∫ t in Set.Icc (path.sojournStart (path.jumpCount T)) T, f (path.stateAt t)
        = ∫ t in Set.Icc (path.sojournStart (path.jumpCount T)) T,
            f (path.stateSeq (path.jumpCount T)) := by
            exact setIntegral_congr_fun measurableSet_Icc hconst
    _ = volume.real (Set.Icc (path.sojournStart (path.jumpCount T)) T) *
          f (path.stateSeq (path.jumpCount T)) := by
          rw [setIntegral_const, smul_eq_mul]
    _ = f (path.stateSeq (path.jumpCount T)) * path.currentSojournElapsed T := by
          rw [Real.volume_real_Icc_of_le hstart_le]
          simp [currentSojournElapsed]
          ring

/-- The completed sojourns plus the current partial sojourn contribution are
bounded by the full clock-time integral over `[0,T]`. -/
theorem CTMCPath.sum_sojournTime_mul_add_currentSojourn_le_setIntegral_Icc
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : S → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : IntegrableOn (fun t => f (path.stateAt t))
      (Set.Icc (0 : ℝ) T) volume) :
    (∑ k ∈ Finset.range (path.jumpCount T),
      f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T ≤
      ∫ t in Set.Icc (0 : ℝ) T, f (path.stateAt t) := by
  let U : Set ℝ := ⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k
  let C : Set ℝ := Set.Icc (path.sojournStart (path.jumpCount T)) T
  have hU_subset : U ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    simp only [U, Set.mem_iUnion, exists_prop] at ht
    obtain ⟨k, hk, htk⟩ := ht
    exact path.sojournInterval_subset_Icc_of_lt_jumpCount hstrict hpos hfuture
      (Finset.mem_range.mp hk) htk
  have hC_subset : C ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    constructor
    · exact le_trans
        (path.sojournStart_nonneg hstrict hpos (path.jumpCount T)) ht.1
    · exact ht.2
  have hUC_subset : Set.union U C ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    exact ht.elim (fun h => hU_subset h) (fun h => hC_subset h)
  have hUC_ae : Set.union U C ≤ᵐ[volume] Set.Icc (0 : ℝ) T :=
    Filter.Eventually.of_forall fun t ht => hUC_subset ht
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)]
        fun t => f (path.stateAt t) :=
    Filter.Eventually.of_forall fun t => hf_nonneg (path.stateAt t)
  have hmono :
      ∫ t in Set.union U C, f (path.stateAt t) ≤
        ∫ t in Set.Icc (0 : ℝ) T, f (path.stateAt t) :=
    setIntegral_mono_set hf_int hnonneg hUC_ae
  have hU_int : IntegrableOn (fun t => f (path.stateAt t)) U volume :=
    hf_int.mono_set hU_subset
  have hC_int : IntegrableOn (fun t => f (path.stateAt t)) C volume :=
    hf_int.mono_set hC_subset
  have hdisj : Disjoint U C := by
    rw [Set.disjoint_left]
    intro t htU htC
    simp only [U, Set.mem_iUnion, exists_prop] at htU
    obtain ⟨k, hk, htk⟩ := htU
    have hend_start :
        path.sojournEnd k ≤ path.sojournStart (path.jumpCount T) :=
      path.sojournEnd_le_sojournStart_of_lt hstrict (Finset.mem_range.mp hk)
    exact not_lt_of_ge (le_trans hend_start htC.1) htk.2
  have hsplitU :
      ∫ t in U, f (path.stateAt t) =
        ∑ k ∈ Finset.range (path.jumpCount T),
          f (path.stateSeq k) * path.sojournTime k := by
    simpa [U] using
      path.setIntegral_biUnion_sojournInterval_stateAt hstrict hpos f
        (path.jumpCount T)
  have hsplitC :
      ∫ t in C, f (path.stateAt t) =
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
    simpa [C] using
      path.setIntegral_currentSojourn_stateAt hstrict f hT hfuture
  have hsplit :
      ∫ t in Set.union U C, f (path.stateAt t) =
        (∑ k ∈ Finset.range (path.jumpCount T),
          f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
    change
      ∫ t in U ∪ C, f (path.stateAt t) =
        (∑ k ∈ Finset.range (path.jumpCount T),
          f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T
    rw [setIntegral_union hdisj measurableSet_Icc hU_int hC_int]
    rw [hsplitU, hsplitC]
  rw [hsplit] at hmono
  exact hmono

/-- The completed sojourns plus the current partial sojourn contribution are
exactly the clock-time integral over `[0,T]`. -/
theorem CTMCPath.sum_sojournTime_mul_add_currentSojourn_eq_setIntegral_Icc
    (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0) (f : S → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hfuture : ∃ n, T < path.times n)
    (hf_int : IntegrableOn (fun t => f (path.stateAt t))
      (Set.Icc (0 : ℝ) T) volume) :
    (∑ k ∈ Finset.range (path.jumpCount T),
      f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T =
      ∫ t in Set.Icc (0 : ℝ) T, f (path.stateAt t) := by
  let U : Set ℝ := ⋃ k ∈ Finset.range (path.jumpCount T), path.sojournInterval k
  let C : Set ℝ := Set.Icc (path.sojournStart (path.jumpCount T)) T
  have hUC_eq : Set.union U C = Set.Icc (0 : ℝ) T := by
    simpa [U, C] using
      path.completed_union_current_sojourn_eq_Icc hstrict hpos hfuture
  have hU_subset : U ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    have htUC : t ∈ Set.union U C := Or.inl ht
    simpa [hUC_eq] using htUC
  have hC_subset : C ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    have htUC : t ∈ Set.union U C := Or.inr ht
    simpa [hUC_eq] using htUC
  have hU_int : IntegrableOn (fun t => f (path.stateAt t)) U volume :=
    hf_int.mono_set hU_subset
  have hC_int : IntegrableOn (fun t => f (path.stateAt t)) C volume :=
    hf_int.mono_set hC_subset
  have hdisj : Disjoint U C := by
    rw [Set.disjoint_left]
    intro t htU htC
    simp only [U, Set.mem_iUnion, exists_prop] at htU
    obtain ⟨k, hk, htk⟩ := htU
    have hend_start :
        path.sojournEnd k ≤ path.sojournStart (path.jumpCount T) :=
      path.sojournEnd_le_sojournStart_of_lt hstrict (Finset.mem_range.mp hk)
    exact not_lt_of_ge (le_trans hend_start htC.1) htk.2
  have hsplitU :
      ∫ t in U, f (path.stateAt t) =
        ∑ k ∈ Finset.range (path.jumpCount T),
          f (path.stateSeq k) * path.sojournTime k := by
    simpa [U] using
      path.setIntegral_biUnion_sojournInterval_stateAt hstrict hpos f
        (path.jumpCount T)
  have hsplitC :
      ∫ t in C, f (path.stateAt t) =
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
    simpa [C] using
      path.setIntegral_currentSojourn_stateAt hstrict f hT hfuture
  have hsplit :
      ∫ t in Set.union U C, f (path.stateAt t) =
        (∑ k ∈ Finset.range (path.jumpCount T),
          f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T := by
    change
      ∫ t in U ∪ C, f (path.stateAt t) =
        (∑ k ∈ Finset.range (path.jumpCount T),
          f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T
    rw [setIntegral_union hdisj measurableSet_Icc hU_int hC_int]
    rw [hsplitU, hsplitC]
  calc
    (∑ k ∈ Finset.range (path.jumpCount T),
      f (path.stateSeq k) * path.sojournTime k) +
        f (path.stateSeq (path.jumpCount T)) *
          path.currentSojournElapsed T
        = ∫ t in Set.union U C, f (path.stateAt t) := by
            exact hsplit.symm
    _ = ∫ t in Set.Icc (0 : ℝ) T, f (path.stateAt t) := by
            rw [hUC_eq]

/-- The state changes at each jump: stateSeq(n) is the state just before
the n-th jump, stateSeq(n+1) is the state just after. -/
theorem CTMCPath.stateAt_jump_transition (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (n : ℕ) : path.stateAt (path.times n) = path.stateSeq (n + 1) :=
  path.stateAt_eq_stateSeq_succ hstrict n

/-- Sum over jumps telescope: for any function f on pairs of states,
the contribution from the first N jumps is a finite sum over stateSeq. -/
noncomputable def CTMCPath.jumpSum (path : CTMCPath S) (f : S → S → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, f (path.stateSeq k) (path.stateSeq (k + 1))

/-- The jump sum is additive: jumpSum N = jumpSum M + jumpSum(M..N). -/
theorem CTMCPath.jumpSum_add (path : CTMCPath S)
    (f : S → S → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    path.jumpSum f N = path.jumpSum f M +
      ∑ k ∈ Finset.Ico M N,
        f (path.stateSeq k) (path.stateSeq (k + 1)) := by
  simp only [jumpSum]
  exact (Finset.sum_range_add_sum_Ico
    (f := fun k => f (path.stateSeq k)
      (path.stateSeq (k + 1))) hMN).symm

/-- Jump sum with 0 jumps is 0. -/
@[simp]
theorem CTMCPath.jumpSum_zero (path : CTMCPath S) (f : S → S → ℝ) :
    path.jumpSum f 0 = 0 := by
  simp [jumpSum]

/-- Jump sum is monotone for non-negative f. -/
theorem CTMCPath.jumpSum_mono (path : CTMCPath S) (f : S → S → ℝ)
    (hf : ∀ s u, 0 ≤ f s u) {M N : ℕ} (hMN : M ≤ N) :
    path.jumpSum f M ≤ path.jumpSum f N := by
  rw [path.jumpSum_add f hMN]
  have : 0 ≤ ∑ k ∈ Finset.Ico M N, f (path.stateSeq k) (path.stateSeq (k + 1)) :=
    Finset.sum_nonneg (fun k _ => hf (path.stateSeq k) (path.stateSeq (k + 1)))
  linarith

/-- On a path with strictly increasing times and positive first time,
`stateAt` is locally constant to the right: for every `t ≥ 0` there exists
`δ > 0` such that `stateAt` is constant on `[t, t + δ)`. -/
theorem CTMCPath.stateAt_locallyConstant_right (path : CTMCPath S)
    (_hstrict : ∀ n, path.times n < path.times (n + 1))
    (_hpos : 0 < path.times 0)
    (t : ℝ) :
    ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → path.stateAt s = path.stateAt t := by
  by_cases hex : ∃ n, t < path.times n
  · let n := Nat.find hex
    have hn : t < path.times n := Nat.find_spec hex
    have hmin : ∀ k, k < n → ¬ t < path.times k := fun k hk => Nat.find_min hex hk
    refine ⟨path.times n - t, by linarith, ?_⟩
    intro s hts hst
    have hst' : s < path.times n := by linarith
    have hfind_s : ∃ m, s < path.times m := ⟨n, hst'⟩
    have hfind_eq : Nat.find hfind_s = n := by
      apply le_antisymm
      · exact Nat.find_min' hfind_s hst'
      · by_contra hle
        push Not at hle
        have hlt : Nat.find hfind_s < n := hle
        have := Nat.find_spec hfind_s
        have := hmin (Nat.find hfind_s) hlt
        have : ¬ t < path.times (Nat.find hfind_s) := this
        have : s < path.times (Nat.find hfind_s) := Nat.find_spec hfind_s
        linarith
    simp only [stateAt]
    rw [dif_pos hex, dif_pos hfind_s, hfind_eq]
  · refine ⟨1, one_pos, ?_⟩
    intro s hts _
    simp only [stateAt]
    have hex_s : ¬ ∃ n, s < path.times n := by
      push Not at hex ⊢
      intro n
      exact le_trans (hex n) hts
    rw [dif_neg hex, dif_neg hex_s]

/-- Filter form of right local constancy.  This is the path-regularity
statement used by later rational-time supremum arguments: immediately to the
right of any time, the path state is eventually equal to its current value. -/
theorem CTMCPath.eventually_stateAt_eq_nhdsWithin_Ici (path : CTMCPath S)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0)
    (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t), path.stateAt s = path.stateAt t := by
  obtain ⟨δ, hδ_pos, hδ⟩ := path.stateAt_locallyConstant_right hstrict hpos t
  rw [Filter.eventually_iff]
  rw [Metric.mem_nhdsWithin_iff]
  refine ⟨δ, hδ_pos, ?_⟩
  intro s hs
  rcases hs with ⟨hball, hsIci⟩
  have hts : t ≤ s := hsIci
  have hdist : dist s t < δ := by
    simpa [Metric.mem_ball] using hball
  have hst : s < t + δ := by
    rw [Real.dist_eq] at hdist
    have habs : |s - t| < δ := by simpa [abs_sub_comm] using hdist
    have hsub : s - t < δ := lt_of_le_of_lt (le_abs_self (s - t)) habs
    linarith
  exact hδ s hts hst

/-- Any state observable is eventually constant immediately to the right of
`t` along a compatible jump-and-hold path. -/
theorem CTMCPath.eventually_observable_stateAt_eq_nhdsWithin_Ici
    (path : CTMCPath S) {β : Type*} (f : S → β)
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0)
    (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t),
      f (path.stateAt s) = f (path.stateAt t) :=
  (path.eventually_stateAt_eq_nhdsWithin_Ici hstrict hpos t).mono fun _ hs => by
    rw [hs]

/-- Right-continuity of `stateAt` when the state space is given the discrete
topology.  The theorem is deliberately stated via `ContinuousWithinAt` on
`Ici t`, matching the right-continuous CTMC convention. -/
theorem CTMCPath.stateAt_continuousWithinAt_Ici (path : CTMCPath S)
    [TopologicalSpace S] [DiscreteTopology S]
    (hstrict : ∀ n, path.times n < path.times (n + 1))
    (hpos : 0 < path.times 0)
    (t : ℝ) :
    ContinuousWithinAt path.stateAt (Set.Ici t) t :=
  tendsto_nhds_of_eventually_eq
    (path.eventually_stateAt_eq_nhdsWithin_Ici hstrict hpos t)

end Ripple.CTMC
