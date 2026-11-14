import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBudget

/-!
# The §11 row split of the virtual-core tail (N12, steps 3–4 interface)

`PhaseThreeClockBudget.asynchronous_clock_estimate_of_tails` needs the virtual-core
tail `hcore` with budget `6 / n ^ 5`. PHASE3 §11 charges that tail row by row. This
file splits `PhaseThreeClockCore.ClockCore` into the §11 rows, evaluated at the
canonical first-hit witness `canonicalTimes` (every clause of the core that names a
time is a genuine first hit, so the witness is a function of the path), and proves:

* `clockCore_of_rows`: the conjunction of the rows is the core at the canonical witness;
* `virtualGoodAt_of_rows`: hence `VirtualGoodAt`;
* `virtual_core_tail_of_rows`: `hcore` from the per-row tails with the budgets
  `n^{-8}` (activation and height), `n^{-8}` (P3a passages), `2 n^{-10}` (shape,
  widths, hours, thinning), `n^{-29}` (Main credits), `3 n^{-5}` (all-cap deadline),
  `n^{-6} + n^{-21}` (local cap spread and contact budget), which sum to at most
  `6 / n ^ 5`; the regime row and the counter-reserve row are deterministic and enter as
  implications (`hreg`, `hres`), the latter proved in `PhaseThreeClockReserve`.

The row events are `rowFailure init R`: a finite first seed `s`, an entry `T` within
the early horizon, and the failure of the row `R` on the virtual path at `(s, T)`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRows

open TimeTheorem PairLog StageEventSpec PhaseThreeClockVirtual PhaseThreeClockCore
  PhaseThreeClockProducer PhaseThreeClockAssembly PhaseThreeClockExit

variable {n : ℕ} (init : InputCfg n)

/-! ## Canonical first-hit witnesses -/

theorem firstAfter_unique {P : ℕ → Prop} {S t t' : ℕ} (h : firstAfter P S t)
    (h' : firstAfter P S t') : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2.2 t h.1 hlt h.2.1
  · exact h.2.2 t' h'.1 hlt h'.2.1

theorem firstHit_unique {α : Type*} {P : α → Prop} {tr : ℕ → α} {t t' : ℕ}
    (h : firstHit P tr t) (h' : firstHit P tr t') : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2 t hlt h.1
  · exact h.2 t' hlt h'.1

open Classical in
/-- The first time at or after `S` satisfying `P`, if any; `S` otherwise. -/
def firstAfterTime (P : ℕ → Prop) (S : ℕ) : ℕ :=
  if h : ∃ t, firstAfter P S t then Nat.find h else S

theorem firstAfterTime_eq {P : ℕ → Prop} {S t : ℕ} (h : firstAfter P S t) :
    firstAfterTime P S = t := by
  classical
  unfold firstAfterTime
  rw [dif_pos ⟨t, h⟩]
  exact firstAfter_unique (Nat.find_spec (⟨t, h⟩ : ∃ t, firstAfter P S t)) h

open Classical in
/-- The first hitting time of `P` along `tr`, if any; `0` otherwise. -/
def firstHitTime {α : Type*} (P : α → Prop) (tr : ℕ → α) : ℕ :=
  if h : ∃ t, firstHit P tr t then Nat.find h else 0

theorem firstHitTime_eq {α : Type*} {P : α → Prop} {tr : ℕ → α} {t : ℕ}
    (h : firstHit P tr t) : firstHitTime P tr = t := by
  classical
  unfold firstHitTime
  rw [dif_pos ⟨t, h⟩]
  exact firstHit_unique (Nat.find_spec (⟨t, h⟩ : ∃ t, firstHit P tr t)) h

/-- The activation predicate of the core (99 % of the agents active). -/
def activationPred (lab : ℕ → Lab init) (v : ℕ) : Prop :=
  Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤ activeCountL init (lab v)

/-- The canonical witness: every clock time is the genuine first hit of its clause. -/
def canonicalTimes (lab : ℕ → Lab init) (cfg : ℕ → InputCfg n) (S : ℕ) : ClockTimes init where
  activation := firstAfterTime (activationPred init lab) S
  cap := firstAfterTime
    (fun v => frontCountL init (lab S) (lab v) (clockTop n) = clockCount (cfg S)) S
  first := fun ell => if ell = 0 then S else
    firstAfterTime (fun v => 1 ≤ frontCountL init (lab S) (lab v) ell) S
  bulk := fun ell => if ell = 0 then S else
    firstAfterTime
      (fun v => bulkThreshold (clockCount (cfg S)) ≤ frontCountL init (lab S) (lab v) ell) S
  start := fun h => if h = 0 then firstAfterTime (activationPred init lab) S else
    firstAfterTime
      (fun v => highThreshold (clockCount (cfg S)) ≤ frontCountL init (lab S) (lab v) (256 * h))
      S
  finish := fun h => firstAfterTime
    (fun v => smallThreshold (clockCount (cfg S)) ≤
      frontCountL init (lab S) (lab v) (256 * (h + 1))) S
  initialized := fun i => firstHitTime
    (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 => 3 ≤ a.phase.val)
    (fun v => lab v i)

theorem canonicalTimes_first_zero (lab : ℕ → Lab init) (cfg : ℕ → InputCfg n) (S : ℕ) :
    (canonicalTimes init lab cfg S).first 0 = S := by
  simp [canonicalTimes]

theorem canonicalTimes_bulk_zero (lab : ℕ → Lab init) (cfg : ℕ → InputCfg n) (S : ℕ) :
    (canonicalTimes init lab cfg S).bulk 0 = S := by
  simp [canonicalTimes]

theorem canonicalTimes_start_zero (lab : ℕ → Lab init) (cfg : ℕ → InputCfg n) (S : ℕ) :
    (canonicalTimes init lab cfg S).start 0 = (canonicalTimes init lab cfg S).activation := by
  simp [canonicalTimes]

/-! ## The §11 rows -/

section Rows

variable (lab : ℕ → Lab init) (cfg : ℕ → InputCfg n) (draws : Draws init)
  (S T : ℕ) (w : ClockTimes init)

/-- The regime clauses (PHASE3 §2, P2): roles, counts, phases and density on the
window. Deterministic from the entry and the homogeneous Phase-3 invariance. -/
structure RowRegime : Prop where
  roles_fixed : ∀ v, S ≤ v → v ≤ w.cap + logWindow n 400 → ∀ i : Fin init.card,
    (lab v i).role = (lab S i).role
  main_count : ∀ v, S ≤ v → v ≤ w.cap + logWindow n 400 →
    timeMainCount (cfg v) = timeMainCount (cfg S)
  clock_count : ∀ v, S ≤ v → v ≤ w.cap + logWindow n 400 →
    clockCount (cfg v) = clockCount (cfg S)
  reserve_count : ∀ v, S ≤ v → v ≤ w.cap + logWindow n 400 →
    reserveCount (cfg v) = reserveCount (cfg S)
  phase_range : ∀ v, S ≤ v → v ≤ w.cap + logWindow n 400 →
    ∀ a ∈ cfg v, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3
  all_three : ∀ v, T ≤ v → v ≤ w.cap + logWindow n 400 →
    ∀ a ∈ cfg v, a.phase.val = 3
  density : ∀ v, S ≤ v → v ≤ w.cap + logWindow n 400 →
    12 * n ≤ 25 * timeMainCount (cfg v) ∧
    25 * timeMainCount (cfg v) ≤ 13 * n ∧
    6 * n ≤ 25 * clockCount (cfg v) ∧
    25 * clockCount (cfg v) ≤ 7 * n ∧
    6 * n ≤ 25 * reserveCount (cfg v)

/-- §11 rows 1–2 and P5/P9a: activation, the height bound through the activation
allowance, the Clock initializations, and activation before minute twenty. -/
structure RowActivation : Prop where
  activation_first : firstAfter (activationPred init lab) S w.activation
  all_before_cap : T ≤ w.cap
  activation_before_twenty : w.activation ≤ w.bulk 20
  initialized_first : ∀ i, fixedRoleL init (lab S) .clock i →
    firstHit (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 =>
      3 ≤ a.phase.val) (fun v => lab v i) (w.initialized i)
  initialized_by_all : ∀ i, fixedRoleL init (lab S) .clock i → w.initialized i ≤ T
  counter_reset : ∀ i, fixedRoleL init (lab S) .clock i →
    (lab (w.initialized i) i).counter.val = 50 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  initialized_before_first_cap : ∀ i, fixedRoleL init (lab S) .clock i →
    w.initialized i < w.first (clockTop n)

/-- §11 row 3 (P3a): the finite first-hit passages and their local lengths. -/
structure RowPassage : Prop where
  level_first : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter (fun v => 1 ≤ frontCountL init (lab S) (lab v) ell) S (w.first ell)
  level_bulk : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter (fun v =>
      bulkThreshold (clockCount (cfg S)) ≤ frontCountL init (lab S) (lab v) ell) S (w.bulk ell)
  start_positive : ∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
    firstAfter (fun v =>
      highThreshold (clockCount (cfg S)) ≤ frontCountL init (lab S) (lab v) (256 * h))
      S (w.start h)
  finish_first : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    firstAfter (fun v =>
      smallThreshold (clockCount (cfg S)) ≤ frontCountL init (lab S) (lab v) (256 * (h + 1)))
      S (w.finish h)
  cap_first :
    firstAfter (fun v =>
      frontCountL init (lab S) (lab v) (clockTop n) = clockCount (cfg S)) S w.cap
  activation_before_cap : w.activation ≤ w.cap
  level_before_cap : ∀ ell, ell ≤ clockTop n →
    w.first ell ≤ w.cap ∧ w.bulk ell ≤ w.cap
  hour_before_cap : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.start h ≤ w.cap ∧ w.finish h ≤ w.cap
  raw_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell - w.first ell ≤ logWindow n 30
  fine_raw_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell ≤ max (w.first ell) w.activation +
      2000 * n * frontWidth (clockCount (cfg S))

/-- §11 row 4 (P4–P10): front shape, widths, hour windows, thinning and the active
floors. -/
structure RowShape : Prop where
  bulk_width :
    let C := clockCount (cfg S)
    ∀ v, S ≤ v → v ≤ w.cap →
      frontHeightL init (lab S) (lab v) -
        frontQuantileL init (lab S) (lab v) (bulkThreshold C) ≤ 2 * frontWidth C
  high_width :
    let C := clockCount (cfg S)
    ∀ v, S ≤ v → v ≤ w.cap →
      frontHeightL init (lab S) (lab v) -
        frontQuantileL init (lab S) (lab v) (highThreshold C) ≤ 2 * frontWidth C + 20
  front_shape :
    let C := clockCount (cfg S)
    ∀ ell v, 1 ≤ ell → ell < clockTop n →
      S ≤ v → v ≤ w.bulk ell →
      frontCutoff C ≤ frontCountL init (lab S) (lab v) ell →
      frontCountL init (lab S) (lab v) ell ≤ bulkThreshold C →
      C * frontCountL init (lab S) (lab v) (ell + 1) ≤
        frontCountL init (lab S) (lab v) ell ^ 2
  tick_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    clockContactsL init (lab S) draws (max (w.first ell) w.activation) (w.bulk ell) ≤
      localTickBudget (clockCount (cfg S))
  previous_end : ∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.finish (h - 1) < w.start h
  raw_width : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    70 * n ^ 2 < clockCount (cfg S) * (w.finish h - w.start h)
  exact_hour : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, w.start h ≤ v → v ≤ w.finish h →
      899 * clockCount (cfg S) ≤ 1000 * exactHourClocksL init (lab S) (lab v) h
  first_work_allowance : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((2 : ℝ) * (n : ℝ) ^ 2 / (clockCount (cfg S) : ℝ)) +
      Nat.ceil ((47 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (cfg S) : ℝ)) + 1 ≤
      w.finish h - w.start h
  second_work_allowance : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((51 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (cfg S) : ℝ)) ≤ w.finish h - w.start h
  active_main_floor : ∀ v, w.activation ≤ v → v ≤ w.cap + logWindow n 400 →
    47 * timeMainCount (cfg S) ≤ 48 * activeRoleCountL init (lab S) (lab v) .main
  active_clock_floor : ∀ v, w.activation ≤ v → v ≤ w.cap + logWindow n 400 →
    23 * clockCount (cfg S) ≤ 24 * activeRoleCountL init (lab S) (lab v) .clock

/-- §11 row 5 (P11–P12): the Main hour and deep-bias tails. -/
structure RowMain : Prop where
  main_hour_tail : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, S ≤ v → v ≤ w.finish h →
      2500 * highHourMainsL init (lab S) (lab v) h ≤ 3 * timeMainCount (cfg S)
  main_deep_tail : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, S ≤ v → v ≤ w.finish h →
      1250 * (highHourZeroMainsL init (lab S) (lab v) h +
        deepBiasedMainsL init (lab S) (lab v) h) ≤ 3 * timeMainCount (cfg S)

/-- §11 row 6 (P13): the all-cap deadline. -/
structure RowCap : Prop where
  cap_from_activation : w.cap ≤ T + logWindow n 16000
  cap_deadline : w.cap ≤ S + logWindow n 20000

/-- §11 rows 7–8 (P14): the local cap spread and the eligible-contact budget. -/
structure RowContact : Prop where
  eligible_budget : ∀ i, fixedRoleL init (lab S) .clock i →
    eligibleContactsL init lab draws S i (w.initialized i) (w.cap + logWindow n 16) <
      40 * (PhaseThreeModel.Numeric.hourIndex n + 1)

/-- The counter reserve (P14, transfer part): deterministic from the contact budget,
the counter reset and the virtual counter ledger. -/
structure RowReserve : Prop where
  counter_reserve : ∀ i, fixedRoleL init (lab S) .clock i →
    ∀ v, w.initialized i ≤ v → v ≤ w.cap + logWindow n 16 →
      10 * (PhaseThreeModel.Numeric.hourIndex n + 1) + 1 ≤ (lab v i).counter.val

/-- The conjunction of the rows at the canonical witness is the core. -/
theorem clockCore_of_rows
    (hreg : RowRegime init lab cfg S T (canonicalTimes init lab cfg S))
    (hact : RowActivation init lab S T (canonicalTimes init lab cfg S))
    (hpass : RowPassage init lab cfg S (canonicalTimes init lab cfg S))
    (hshape : RowShape init lab cfg draws S (canonicalTimes init lab cfg S))
    (hmain : RowMain init lab cfg S (canonicalTimes init lab cfg S))
    (hcap : RowCap init S T (canonicalTimes init lab cfg S))
    (hcontact : RowContact init lab draws S (canonicalTimes init lab cfg S))
    (hres : RowReserve init lab S (canonicalTimes init lab cfg S)) :
    ClockCore init lab cfg draws S T (canonicalTimes init lab cfg S) where
  roles_fixed := hreg.roles_fixed
  main_count := hreg.main_count
  clock_count := hreg.clock_count
  reserve_count := hreg.reserve_count
  phase_range := hreg.phase_range
  all_three := hreg.all_three
  density := hreg.density
  activation_first := hact.activation_first
  first_zero := canonicalTimes_first_zero init lab cfg S
  bulk_zero := canonicalTimes_bulk_zero init lab cfg S
  level_first := hpass.level_first
  level_bulk := hpass.level_bulk
  start_zero := canonicalTimes_start_zero init lab cfg S
  start_positive := hpass.start_positive
  finish_first := hpass.finish_first
  cap_first := hpass.cap_first
  activation_before_cap := hpass.activation_before_cap
  all_before_cap := hact.all_before_cap
  level_before_cap := hpass.level_before_cap
  hour_before_cap := hpass.hour_before_cap
  cap_deadline := hcap.cap_deadline
  bulk_width := hshape.bulk_width
  high_width := hshape.high_width
  front_shape := hshape.front_shape
  raw_local := hpass.raw_local
  tick_local := hshape.tick_local
  fine_raw_local := hpass.fine_raw_local
  activation_before_twenty := hact.activation_before_twenty
  previous_end := hshape.previous_end
  raw_width := hshape.raw_width
  exact_hour := hshape.exact_hour
  active_main_floor := hshape.active_main_floor
  active_clock_floor := hshape.active_clock_floor
  first_work_allowance := hshape.first_work_allowance
  second_work_allowance := hshape.second_work_allowance
  main_hour_tail := hmain.main_hour_tail
  main_deep_tail := hmain.main_deep_tail
  cap_from_activation := hcap.cap_from_activation
  initialized_first := hact.initialized_first
  initialized_by_all := hact.initialized_by_all
  counter_reset := hact.counter_reset
  initialized_before_first_cap := hact.initialized_before_first_cap
  eligible_budget := hcontact.eligible_budget
  counter_reserve := hres.counter_reserve

end Rows

/-! ## The rows on the virtual path and the row-failure events -/

/-- The canonical witness on the virtual continuation from the seed `S`. -/
def virtualTimes (ω : InputLog n) (S : ℕ) : ClockTimes init :=
  canonicalTimes init (virtualLabels init ω) (virtualCfg init ω) S

/-- The row-failure event of a row predicate `R ω S T`: a finite genuine first seed
`S`, an entry `T` within the early horizon, and the failure of the row. -/
def rowFailure (R : InputLog n → ℕ → ℕ → Prop) : Set (InputLog n) :=
  {ω | ∃ S T : ℕ, seedTime init 3 ω = (S : WithTop ℕ) ∧ T ≤ earlyHorizon n ∧
    AsyncEntry init ω S T ∧ ¬ R ω S T}

def regimeRow (ω : InputLog n) (S T : ℕ) : Prop :=
  RowRegime init (virtualLabels init ω) (virtualCfg init ω) S T (virtualTimes init ω S)

def activationRow (ω : InputLog n) (S T : ℕ) : Prop :=
  RowActivation init (virtualLabels init ω) S T (virtualTimes init ω S)

def passageRow (ω : InputLog n) (S : ℕ) (_T : ℕ) : Prop :=
  RowPassage init (virtualLabels init ω) (virtualCfg init ω) S (virtualTimes init ω S)

def shapeRow (ω : InputLog n) (S : ℕ) (_T : ℕ) : Prop :=
  RowShape init (virtualLabels init ω) (virtualCfg init ω) (drawLabels init ω) S
    (virtualTimes init ω S)

def mainRow (ω : InputLog n) (S : ℕ) (_T : ℕ) : Prop :=
  RowMain init (virtualLabels init ω) (virtualCfg init ω) S (virtualTimes init ω S)

def capRow (ω : InputLog n) (S T : ℕ) : Prop :=
  RowCap init S T (virtualTimes init ω S)

def contactRow (ω : InputLog n) (S : ℕ) (_T : ℕ) : Prop :=
  RowContact init (virtualLabels init ω) (drawLabels init ω) S (virtualTimes init ω S)

def reserveRow (ω : InputLog n) (S : ℕ) (_T : ℕ) : Prop :=
  RowReserve init (virtualLabels init ω) S (virtualTimes init ω S)

/-- All rows at the entry `(S, T)` give `VirtualGoodAt`. -/
theorem virtualGoodAt_of_rows {ω : InputLog n} {S T : ℕ} (hT : T ≤ earlyHorizon n)
    (hentry : AsyncEntry init ω S T)
    (hreg : regimeRow init ω S T) (hact : activationRow init ω S T)
    (hpass : passageRow init ω S T) (hshape : shapeRow init ω S T)
    (hmain : mainRow init ω S T) (hcap : capRow init ω S T)
    (hcontact : contactRow init ω S T) (hres : reserveRow init ω S T) :
    VirtualGoodAt init S ω :=
  ⟨T, virtualTimes init ω S, hT, hentry,
    clockCore_of_rows init _ _ _ S T hreg hact hpass hshape hmain hcap hcontact hres⟩

/-- The virtual-core failure is covered by the six probabilistic row failures, given the
two deterministic rows (regime from the entry; counter reserve from activation and
contact budget). -/
theorem virtual_core_bad_subset
    (hreg : ∀ ω S T, AsyncEntry init ω S T → regimeRow init ω S T)
    (hres : ∀ ω S T, AsyncEntry init ω S T → activationRow init ω S T →
      contactRow init ω S T → reserveRow init ω S T) :
    {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ⊆
    rowFailure init (activationRow init) ∪ (rowFailure init (passageRow init) ∪
      (rowFailure init (shapeRow init) ∪ (rowFailure init (mainRow init) ∪
      (rowFailure init (capRow init) ∪ rowFailure init (contactRow init))))) := by
  rintro ω ⟨s, hs, -, ⟨T, hT, hentry⟩, hbad⟩
  by_cases h2 : activationRow init ω s T
  · by_cases h3 : passageRow init ω s T
    · by_cases h4 : shapeRow init ω s T
      · by_cases h5 : mainRow init ω s T
        · by_cases h6 : capRow init ω s T
          · by_cases h7 : contactRow init ω s T
            · exact absurd (virtualGoodAt_of_rows init hT hentry (hreg ω s T hentry) h2 h3 h4
                h5 h6 h7 (hres ω s T hentry h2 h7)) hbad
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, T, hs, hT, hentry, h7⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, T, hs, hT, hentry, h6⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, T, hs, hT, hentry, h5⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨s, T, hs, hT, hentry, h4⟩))
    · exact Or.inr (Or.inl ⟨s, T, hs, hT, hentry, h3⟩)
  · exact Or.inl ⟨s, T, hs, hT, hentry, h2⟩

/-- The §11 row tails of the six probabilistic rows with their individual budgets. -/
structure RowTails : Prop where
  activation : law init (rowFailure init (activationRow init)) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  passage : law init (rowFailure init (passageRow init)) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8)
  shape : law init (rowFailure init (shapeRow init)) ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 10)
  main : law init (rowFailure init (mainRow init)) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 29)
  cap : law init (rowFailure init (capRow init)) ≤ ENNReal.ofReal (3 / (n : ℝ) ^ 5)
  contact : law init (rowFailure init (contactRow init)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21)

/-- The §11 budgets of the virtual-core rows sum to at most `6 / n ^ 5` for `n ≥ 2`. -/
theorem row_budget (hn : 2 ≤ n) :
    ENNReal.ofReal (1 / (n : ℝ) ^ 8) + (ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
      (ENNReal.ofReal (2 / (n : ℝ) ^ 10) + (ENNReal.ofReal (1 / (n : ℝ) ^ 29) +
      (ENNReal.ofReal (3 / (n : ℝ) ^ 5) +
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21))))) ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := by linarith
  have h8 : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 8 := by positivity
  have h10 : (0 : ℝ) ≤ 2 / (n : ℝ) ^ 10 := by positivity
  have h29 : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 29 := by positivity
  have h5 : (0 : ℝ) ≤ 3 / (n : ℝ) ^ 5 := by positivity
  have h621 : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21 := by positivity
  rw [← ENNReal.ofReal_add h5 h621, ← ENNReal.ofReal_add h29 (by positivity),
    ← ENNReal.ofReal_add h10 (by positivity), ← ENNReal.ofReal_add h8 (by positivity),
    ← ENNReal.ofReal_add h8 (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hp5 : (0 : ℝ) < (n : ℝ) ^ 5 := by positivity
  have hterm : ∀ k : ℕ, 5 ≤ k → (1 : ℝ) / (n : ℝ) ^ k ≤ 1 / (n : ℝ) ^ 5 / 2 ^ (k - 5) := by
    intro k hk
    have hsplit : (n : ℝ) ^ k = (n : ℝ) ^ 5 * (n : ℝ) ^ (k - 5) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, div_div]
    apply one_div_le_one_div_of_le (by positivity)
    apply mul_le_mul_of_nonneg_left _ hp5.le
    exact pow_le_pow_left₀ (by norm_num) hnR _
  have e8 : (1 : ℝ) / (n : ℝ) ^ 8 ≤ 1 / (n : ℝ) ^ 5 / 8 := by
    have := hterm 8 (by norm_num)
    rwa [show (2 : ℝ) ^ (8 - 5) = 8 by norm_num] at this
  have e10 : (1 : ℝ) / (n : ℝ) ^ 10 ≤ 1 / (n : ℝ) ^ 5 / 32 := by
    have := hterm 10 (by norm_num)
    rwa [show (2 : ℝ) ^ (10 - 5) = 32 by norm_num] at this
  have e29 : (1 : ℝ) / (n : ℝ) ^ 29 ≤ 1 / (n : ℝ) ^ 5 / 16777216 := by
    have := hterm 29 (by norm_num)
    rwa [show (2 : ℝ) ^ (29 - 5) = 16777216 by norm_num] at this
  have e6 : (1 : ℝ) / (n : ℝ) ^ 6 ≤ 1 / (n : ℝ) ^ 5 / 2 := by
    have := hterm 6 (by norm_num)
    rwa [show (2 : ℝ) ^ (6 - 5) = 2 by norm_num] at this
  have e21 : (1 : ℝ) / (n : ℝ) ^ 21 ≤ 1 / (n : ℝ) ^ 5 / 65536 := by
    have := hterm 21 (by norm_num)
    rwa [show (2 : ℝ) ^ (21 - 5) = 65536 by norm_num] at this
  have h2 : (2 : ℝ) / (n : ℝ) ^ 10 = 2 * (1 / (n : ℝ) ^ 10) := by ring
  have h3 : (3 : ℝ) / (n : ℝ) ^ 5 = 3 * (1 / (n : ℝ) ^ 5) := by ring
  have h6 : (6 : ℝ) / (n : ℝ) ^ 5 = 6 * (1 / (n : ℝ) ^ 5) := by ring
  rw [h2, h3, h6]
  have hq : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 5 := by positivity
  linarith

/-- `hcore` from the six row tails and the two deterministic rows. -/
theorem virtual_core_tail_of_rows (hn : 2 ≤ n)
    (hreg : ∀ ω S T, AsyncEntry init ω S T → regimeRow init ω S T)
    (hres : ∀ ω S T, AsyncEntry init ω S T → activationRow init ω S T →
      contactRow init ω S T → reserveRow init ω S T)
    (h : RowTails init) :
    law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω} ≤
      ENNReal.ofReal (6 / (n : ℝ) ^ 5) := by
  calc law init {ω | ∃ s : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
        SeedProfile n init (trace init ω s) ∧
        (∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T) ∧ ¬ VirtualGoodAt init s ω}
      ≤ law init _ := measure_mono (virtual_core_bad_subset init hreg hres)
    _ ≤ law init _ + (law init _ + (law init _ + (law init _ + (law init _ + law init _)))) := by
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 8) + (ENNReal.ofReal (1 / (n : ℝ) ^ 8) +
          (ENNReal.ofReal (2 / (n : ℝ) ^ 10) + (ENNReal.ofReal (1 / (n : ℝ) ^ 29) +
          (ENNReal.ofReal (3 / (n : ℝ) ^ 5) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21))))) :=
        add_le_add h.activation (add_le_add h.passage (add_le_add h.shape
          (add_le_add h.main (add_le_add h.cap h.contact))))
    _ ≤ ENNReal.ofReal (6 / (n : ℝ) ^ 5) := row_budget hn

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRows

end
