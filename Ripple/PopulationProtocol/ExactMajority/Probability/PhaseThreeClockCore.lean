import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockVirtual

/-!
# The clock-history core on an arbitrary labelled path (N12, steps 3–5 interface)

`StageEventSpec.ClockHistory` is stated on the actual labelled process
`PairLog.labelsAt init ω`. The clock estimates of PHASE3 P2–P14 are proved on the
virtual continuation `PhaseThreeClockVirtual.virtualLabels init ω`, and transferred to
the actual process before the first counter exit. To make the transfer a statement
about one predicate evaluated on two paths, this file restates the reviewed clauses
G3'.1–G3'.6 on an arbitrary labelled path `lab`, configuration path `cfg` and draw
record `draws`:

* the per-time counting functions `*L` are the `StageEventSpec` functions with the
  path abstracted; at the actual path they are the originals by `rfl`
  (`frontCount_eq_L`, ...);
* `ClockCore init lab cfg draws S T w` is G3'.1–G3'.6 without the actual-exit clauses
  (`first_exit`, `exit_deadline`, `protected_settling`, `exit_after_cap`,
  `final_spread`), with the clauses quantified up to the actual exit `ρ` quantified
  instead up to the exit deadline `w.cap + logWindow n 400`.

`VirtualClockCore init ω S T w` is `ClockCore` on the virtual path; it is the event
that the step-3 and step-4 producers estimate.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCore

open TimeTheorem PairLog StageEventSpec PhaseThreeClockVirtual

variable {n : ℕ} (init : InputCfg n)

/-- A labelling of the `init.card` physical labels. -/
abbrev Lab (init : InputCfg n) := Fin init.card → AgentState (PhaseThreeModel.Numeric.hourIndex n) 256

/-- A draw record on labels. -/
abbrev Draws (init : InputCfg n) := ℕ → Option (Fin init.card × Fin init.card)

/-! ## Counting functions on labellings -/

def activeL (fv : Lab init) (i : Fin init.card) : Prop := 3 ≤ (fv i).phase.val

def fixedRoleL (fS : Lab init) (r : Role) (i : Fin init.card) : Prop := (fS i).role = r

def activeCountL (fv : Lab init) : ℕ := labelCount init (activeL init fv)

def activeRoleCountL (fS fv : Lab init) (r : Role) : ℕ :=
  labelCount init (fun i => fixedRoleL init fS r i ∧ activeL init fv i)

open Classical in
def effectiveMinuteL (fv : Lab init) (i : Fin init.card) : ℕ :=
  if activeL init fv i then (fv i).minute.val else 0

def frontCountL (fS fv : Lab init) (ell : ℕ) : ℕ :=
  labelCount init (fun i => fixedRoleL init fS .clock i ∧ ell ≤ effectiveMinuteL init fv i)

open Classical in
def frontHeightL (fS fv : Lab init) : ℕ :=
  (Finset.univ.filter (fixedRoleL init fS .clock)).sup (effectiveMinuteL init fv)

open Classical in
def frontQuantileL (fS fv : Lab init) (b : ℕ) : ℕ :=
  ((Finset.range (clockTop n + 1)).filter
    (fun ell => b ≤ frontCountL init fS fv ell)).sup id

def clockContactL (fS : Lab init) (draws : Draws init) (k : ℕ) : Prop :=
  ∃ i j, draws k = some (i, j) ∧ fixedRoleL init fS .clock i ∧ fixedRoleL init fS .clock j

open Classical in
def clockContactsL (fS : Lab init) (draws : Draws init) (u v : ℕ) : ℕ :=
  ((Finset.Ioc u v).filter (clockContactL init fS draws)).card

def exactHourClocksL (fS fv : Lab init) (h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRoleL init fS .clock i ∧ activeL init fv i ∧ (fv i).minute.val / 256 = h)

def highHourMainsL (fS fv : Lab init) (h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRoleL init fS .main i ∧ activeL init fv i ∧ h < (fv i).hour.val)

def highHourZeroMainsL (fS fv : Lab init) (h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRoleL init fS .main i ∧ activeL init fv i ∧ (fv i).bias = Bias.zero ∧
      h < (fv i).hour.val)

def deepBiasedMainsL (fS fv : Lab init) (h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRoleL init fS .main i ∧ activeL init fv i ∧
      ∃ σ j, (fv i).bias = Bias.dyadic σ j ∧ h < j.val)

def eligibleContactL (lab : ℕ → Lab init) (draws : Draws init) (S : ℕ) (i : Fin init.card)
    (k : ℕ) : Prop :=
  0 < k ∧ ∃ j l,
    draws k = some (j, l) ∧
    (i = j ∨ i = l) ∧
    fixedRoleL init (lab S) .clock j ∧ fixedRoleL init (lab S) .clock l ∧
    (lab (k - 1) j).phase.val = 3 ∧
    (lab (k - 1) l).phase.val = 3 ∧
    (lab (k - 1) j).minute.val = clockTop n ∧
    (lab (k - 1) l).minute.val = clockTop n

open Classical in
def eligibleContactsL (lab : ℕ → Lab init) (draws : Draws init) (S : ℕ) (i : Fin init.card)
    (u v : ℕ) : ℕ :=
  ((Finset.Ioc u v).filter (eligibleContactL init lab draws S i)).card

/-! ## At the actual path these are the reviewed functions -/

variable (ω : InputLog n)

theorem activeCount_eq_L (v : ℕ) :
    StageEventSpec.activeCount init ω v = activeCountL init (labelsAt init ω v) := rfl

theorem activeRoleCount_eq_L (S v : ℕ) (r : Role) :
    StageEventSpec.activeRoleCount init ω S v r =
      activeRoleCountL init (labelsAt init ω S) (labelsAt init ω v) r := rfl

theorem effectiveMinute_eq_L (v : ℕ) (i : Fin init.card) :
    StageEventSpec.effectiveMinute init ω v i = effectiveMinuteL init (labelsAt init ω v) i := rfl

theorem frontCount_eq_L (S v ell : ℕ) :
    StageEventSpec.frontCount init ω S v ell = frontCountL init (labelsAt init ω S) (labelsAt init ω v) ell :=
  rfl

theorem frontHeight_eq_L (S v : ℕ) :
    StageEventSpec.frontHeight init ω S v = frontHeightL init (labelsAt init ω S) (labelsAt init ω v) := rfl

theorem frontQuantile_eq_L (S v b : ℕ) :
    StageEventSpec.frontQuantile init ω S v b =
      frontQuantileL init (labelsAt init ω S) (labelsAt init ω v) b := rfl

theorem clockContacts_eq_L (S u v : ℕ) :
    StageEventSpec.clockContacts init ω S u v = clockContactsL init (labelsAt init ω S) (drawLabels init ω) u v :=
  rfl

theorem exactHourClocks_eq_L (S v h : ℕ) :
    StageEventSpec.exactHourClocks init ω S v h =
      exactHourClocksL init (labelsAt init ω S) (labelsAt init ω v) h := rfl

theorem highHourMains_eq_L (S v h : ℕ) :
    StageEventSpec.highHourMains init ω S v h =
      highHourMainsL init (labelsAt init ω S) (labelsAt init ω v) h := rfl

theorem highHourZeroMains_eq_L (S v h : ℕ) :
    StageEventSpec.highHourZeroMains init ω S v h =
      highHourZeroMainsL init (labelsAt init ω S) (labelsAt init ω v) h := rfl

theorem deepBiasedMains_eq_L (S v h : ℕ) :
    StageEventSpec.deepBiasedMains init ω S v h =
      deepBiasedMainsL init (labelsAt init ω S) (labelsAt init ω v) h := rfl

theorem eligibleContacts_eq_L (S : ℕ) (i : Fin init.card) (u v : ℕ) :
    StageEventSpec.eligibleContacts init ω S i u v =
      eligibleContactsL init (labelsAt init ω) (drawLabels init ω) S i u v := rfl

/-! ## The core clauses on an arbitrary path -/

/-- G3'.1–G3'.6 of `StageEventSpec.ClockHistory` on the path `(lab, cfg, draws)`, with
the exit-related clauses removed and the clauses quantified up to the actual exit `ρ`
quantified instead up to the exit deadline `w.cap + logWindow n 400`. The entry clause
is not included: it is an event of the actual process supplied by the fibre. -/
structure ClockCore (lab : ℕ → Lab init) (cfg : ℕ → InputCfg n) (draws : Draws init)
    (S T : ℕ) (w : ClockTimes init) : Prop where
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
  activation_first :
    firstAfter (fun v =>
      Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤ activeCountL init (lab v)) S w.activation
  first_zero : w.first 0 = S
  bulk_zero : w.bulk 0 = S
  level_first : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter (fun v => 1 ≤ frontCountL init (lab S) (lab v) ell) S (w.first ell)
  level_bulk : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter (fun v =>
      bulkThreshold (clockCount (cfg S)) ≤ frontCountL init (lab S) (lab v) ell) S (w.bulk ell)
  start_zero : w.start 0 = w.activation
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
  all_before_cap : T ≤ w.cap
  level_before_cap : ∀ ell, ell ≤ clockTop n →
    w.first ell ≤ w.cap ∧ w.bulk ell ≤ w.cap
  hour_before_cap : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.start h ≤ w.cap ∧ w.finish h ≤ w.cap
  cap_deadline : w.cap ≤ S + logWindow n 20000
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
  raw_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell - w.first ell ≤ logWindow n 30
  tick_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    clockContactsL init (lab S) draws (max (w.first ell) w.activation) (w.bulk ell) ≤
      localTickBudget (clockCount (cfg S))
  fine_raw_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell ≤ max (w.first ell) w.activation +
      2000 * n * frontWidth (clockCount (cfg S))
  activation_before_twenty : w.activation ≤ w.bulk 20
  previous_end : ∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.finish (h - 1) < w.start h
  raw_width : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    70 * n ^ 2 < clockCount (cfg S) * (w.finish h - w.start h)
  exact_hour : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, w.start h ≤ v → v ≤ w.finish h →
      899 * clockCount (cfg S) ≤ 1000 * exactHourClocksL init (lab S) (lab v) h
  active_main_floor : ∀ v, w.activation ≤ v → v ≤ w.cap + logWindow n 400 →
    47 * timeMainCount (cfg S) ≤ 48 * activeRoleCountL init (lab S) (lab v) .main
  active_clock_floor : ∀ v, w.activation ≤ v → v ≤ w.cap + logWindow n 400 →
    23 * clockCount (cfg S) ≤ 24 * activeRoleCountL init (lab S) (lab v) .clock
  first_work_allowance : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((2 : ℝ) * (n : ℝ) ^ 2 / (clockCount (cfg S) : ℝ)) +
      Nat.ceil ((47 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (cfg S) : ℝ)) + 1 ≤
      w.finish h - w.start h
  second_work_allowance : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((51 : ℝ) * (n : ℝ) ^ 2 / (timeMainCount (cfg S) : ℝ)) ≤ w.finish h - w.start h
  main_hour_tail : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, S ≤ v → v ≤ w.finish h →
      2500 * highHourMainsL init (lab S) (lab v) h ≤ 3 * timeMainCount (cfg S)
  main_deep_tail : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, S ≤ v → v ≤ w.finish h →
      1250 * (highHourZeroMainsL init (lab S) (lab v) h +
        deepBiasedMainsL init (lab S) (lab v) h) ≤ 3 * timeMainCount (cfg S)
  cap_from_activation : w.cap ≤ T + logWindow n 16000
  initialized_first : ∀ i, fixedRoleL init (lab S) .clock i →
    firstHit (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 =>
      3 ≤ a.phase.val) (fun v => lab v i) (w.initialized i)
  initialized_by_all : ∀ i, fixedRoleL init (lab S) .clock i → w.initialized i ≤ T
  counter_reset : ∀ i, fixedRoleL init (lab S) .clock i →
    (lab (w.initialized i) i).counter.val = 50 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  initialized_before_first_cap : ∀ i, fixedRoleL init (lab S) .clock i →
    w.initialized i < w.first (clockTop n)
  eligible_budget : ∀ i, fixedRoleL init (lab S) .clock i →
    eligibleContactsL init lab draws S i (w.initialized i) (w.cap + logWindow n 16) <
      40 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  counter_reserve : ∀ i, fixedRoleL init (lab S) .clock i →
    ∀ v, w.initialized i ≤ v → v ≤ w.cap + logWindow n 16 →
      10 * (PhaseThreeModel.Numeric.hourIndex n + 1) + 1 ≤ (lab v i).counter.val

/-- The core on the virtual continuation: the event estimated by the step-3 and
step-4 producers. -/
def VirtualClockCore (ω : InputLog n) (S T : ℕ) (w : ClockTimes init) : Prop :=
  ClockCore init (virtualLabels init ω) (virtualCfg init ω) (drawLabels init ω) S T w

/-- The core on the actual path together with the actual-exit clauses gives the
reviewed clock history. -/
theorem clockHistory_of_core (S T ρ : ℕ) (w : ClockTimes init)
    (hentry : AsyncEntry init ω S T)
    (hcore : ClockCore init (labelsAt init ω) (trace init ω) (drawLabels init ω) S T w)
    (hexit : firstPhaseSeed init 4 ρ ω)
    (hρdead : ρ ≤ S + logWindow n 20000)
    (hprot : w.cap + logWindow n 16 < ρ)
    (hafter : ρ ≤ w.cap + logWindow n 400)
    (hspread : allGE 4 (trace init ω (S + logWindow n 20000))) :
    ClockHistory init ω S T ρ w where
  entry := hentry
  roles_fixed := fun v hS hv i => hcore.roles_fixed v hS (by omega) i
  main_count := fun v hS hv => hcore.main_count v hS (by omega)
  clock_count := fun v hS hv => hcore.clock_count v hS (by omega)
  reserve_count := fun v hS hv => hcore.reserve_count v hS (by omega)
  phase_range := fun v hS hv => hcore.phase_range v hS (by omega)
  all_three := fun v hT hv => hcore.all_three v hT (by omega)
  density := fun v hS hv => hcore.density v hS (by omega)
  activation_first := hcore.activation_first
  first_zero := hcore.first_zero
  bulk_zero := hcore.bulk_zero
  level_first := hcore.level_first
  level_bulk := hcore.level_bulk
  start_zero := hcore.start_zero
  start_positive := hcore.start_positive
  finish_first := hcore.finish_first
  cap_first := hcore.cap_first
  activation_before_cap := hcore.activation_before_cap
  all_before_cap := hcore.all_before_cap
  level_before_cap := hcore.level_before_cap
  hour_before_cap := hcore.hour_before_cap
  first_exit := hexit
  cap_deadline := hcore.cap_deadline
  exit_deadline := hρdead
  bulk_width := hcore.bulk_width
  high_width := hcore.high_width
  front_shape := hcore.front_shape
  raw_local := hcore.raw_local
  tick_local := hcore.tick_local
  fine_raw_local := hcore.fine_raw_local
  activation_before_twenty := hcore.activation_before_twenty
  previous_end := hcore.previous_end
  raw_width := hcore.raw_width
  exact_hour := hcore.exact_hour
  active_main_floor := fun v hα hv => hcore.active_main_floor v hα (by omega)
  active_clock_floor := fun v hα hv => hcore.active_clock_floor v hα (by omega)
  first_work_allowance := hcore.first_work_allowance
  second_work_allowance := hcore.second_work_allowance
  main_hour_tail := hcore.main_hour_tail
  main_deep_tail := hcore.main_deep_tail
  cap_from_activation := hcore.cap_from_activation
  protected_settling := hprot
  initialized_first := hcore.initialized_first
  initialized_by_all := hcore.initialized_by_all
  counter_reset := hcore.counter_reset
  initialized_before_first_cap := hcore.initialized_before_first_cap
  eligible_budget := hcore.eligible_budget
  counter_reserve := hcore.counter_reserve
  exit_after_cap := hafter
  final_spread := hspread

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCore

end
