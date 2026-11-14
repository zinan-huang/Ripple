import Ripple.PopulationProtocol.ExactMajority.Probability.PairLog
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Pre3
import Ripple.PopulationProtocol.ExactMajority.Analysis.Invariants
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The reviewed Phase-3 history and readout events

This is node N10 of DOTY-LEAN-PLAN. The execution variable is a recorded
pair log, and all contact counts use its persistent physical labels.
The entry history is PHASE02 section 10. The clock history retains all
seven clauses of PHASE3 section 3, with its finite-hour and activation
conventions. No probability is conditioned on this future good event.

The event specification makes no probabilistic producer claim.
-/

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.StageEventSpec

open TimeTheorem

attribute [local instance] Classical.propDecidable

def oppositeSign : Sign → Sign
  | .pos => .neg
  | .neg => .pos

def winningSign {n : ℕ} (init : InputCfg n) (σ : Sign) : Prop :=
  match σ with
  | .pos => 0 < initialGap init
  | .neg => initialGap init < 0

noncomputable def bandCount {n : ℕ}
    (σ : Sign) (ell width : ℕ) (c : InputCfg n) : ℕ :=
  c.countP (fun a =>
    a.role = .main ∧
    ∃ j, a.bias = Bias.dyadic σ j ∧
      ell ≤ j.val ∧ j.val ≤ ell + width)

noncomputable def signMass {n : ℕ}
    (σ : Sign) (c : InputCfg n) : ℚ :=
  (c.map (fun a =>
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic σ' j =>
          if σ' = σ then (2 : ℚ) ^ (-(j.val : ℤ)) else 0
    else 0)).sum

noncomputable def shallowMass {n : ℕ}
    (ell : ℕ) (c : InputCfg n) : ℚ :=
  (c.map (fun a =>
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic _ j =>
          if j.val < ell then (2 : ℚ) ^ (-(j.val : ℤ)) else 0
    else 0)).sum

noncomputable def shallowPotential {n : ℕ}
    (ell : ℕ) (c : InputCfg n) : ℕ :=
  (c.map (fun a =>
    if a.role = .main then
      match a.bias with
      | .zero => 0
      | .dyadic _ j =>
          if j.val < ell then 4 ^ (ell - j.val - 1) else 0
    else 0)).sum

def tieReadout {n : ℕ} (init c : InputCfg n) : Prop :=
  initialGap init = 0 ∧
    (∀ a ∈ c, a.role ≠ .main → a.bias = Bias.zero) ∧
    (∀ a ∈ c, a.role = .main →
      ∀ σ j, a.bias = Bias.dyadic σ j →
        j.val = PhaseThreeModel.Numeric.hourIndex n)

structure SmallReadout {n : ℕ}
    (init : InputCfg n) (M ell : ℕ) (σ : Sign)
    (c : InputCfg n) : Prop where
  winning : winningSign init σ
  nonzero : 0 < gapMagnitude init
  strictGap : 40 * gapMagnitude init < M
  levelLower : 5 ≤ ell
  levelUpper : ell + 2 ≤ PhaseThreeModel.Numeric.hourIndex n
  scaleLower : 2 * M ≤ 5 * 2 ^ ell * gapMagnitude init
  scaleUpper : 5 * 2 ^ ell * gapMagnitude init < 4 * M
  majorityBand : 92 * M ≤ 100 * bandCount σ ell 2 c
  minority :
    250 * (2 : ℚ) ^ ell * signMass (oppositeSign σ) c ≤ (M : ℚ)
  shallow :
    500 * (2 : ℚ) ^ ell * shallowMass ell c ≤ (M : ℚ)
  potential : 1000 * shallowPotential ell c ≤ M

structure StrongReadout {n : ℕ}
    (init : InputCfg n) (M : ℕ) (c : InputCfg n) : Prop where
  lowerGap : M ≤ 40 * gapMagnitude init
  upperGap : gapMagnitude init ≤ M
  reachable :
    (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
      init c
  phaseLower : ∀ a ∈ c, 3 ≤ a.phase.val
  phaseFourSeed : ∃ a ∈ c, a.phase.val = 4
  hasClock : ∃ a ∈ c, a.role = .clock
  usefulGap : n ≤ 120 * gapMagnitude init

def averageReadout {n : ℕ}
    (init : InputCfg n) (M : ℕ) (c : InputCfg n) : Prop :=
  tieReadout init c ∨
    (∃ ell σ, SmallReadout init M ell σ c) ∨
    StrongReadout init M c

/-! ## The retained asynchronous entry history -/

def finalRoles {n : ℕ} (c : InputCfg n) : Prop :=
  ∀ a ∈ c, a.role = .main ∨ a.role = .clock ∨ a.role = .reserve

def allGE {n : ℕ} (p : ℕ) (c : InputCfg n) : Prop :=
  ∀ a ∈ c, p ≤ a.phase.val

def someGE {n : ℕ} (p : ℕ) (c : InputCfg n) : Prop :=
  ∃ a ∈ c, p ≤ a.phase.val

def safeSmall {n : ℕ}
    (a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) : Prop :=
  2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4

def firstHit {α : Type*} (P : α → Prop) (tr : ℕ → α)
    (t : ℕ) : Prop :=
  P (tr t) ∧ ∀ u < t, ¬ P (tr u)

def firstAfter (P : ℕ → Prop) (S t : ℕ) : Prop :=
  S ≤ t ∧ P t ∧ ∀ u, S ≤ u → u < t → ¬ P u

noncomputable def clockCount {n : ℕ} (c : InputCfg n) : ℕ :=
  c.countP (fun a => a.role = .clock)

noncomputable def reserveCount {n : ℕ} (c : InputCfg n) : ℕ :=
  c.countP (fun a => a.role = .reserve)

noncomputable def mixedAbsMass {n : ℕ} (c : InputCfg n) : ℚ :=
  (c.map (fun a => |prePhase4Mass a|)).sum

def sparse {n : ℕ} (c : InputCfg n) : Prop :=
  100 * mixedAbsMass c ≤ 3 * (timeMainCount c : ℚ)

noncomputable def activationHorizon (n : ℕ) : ℕ :=
  2 * logWindow n 6

structure SeedProfile (n : ℕ) (init c : InputCfg n) : Prop where
  card_eq : c.card = n
  final_roles : finalRoles c
  role_good :
    RoleSplitConcentration.RoleSplitGood
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      (1 / 25 : ℝ) n c
  phase_range : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3
  exactly_two : c.countP (fun a => a.phase.val = 3) = 2
  fresh : ∀ a ∈ c, a.phase.val = 3 →
    Phase3Pre3.Phase3EntryAgent a
  fresh_clock_counter : ∀ a ∈ c, a.phase.val = 3 → a.role = .clock →
    a.counter.val = 50 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  already_initialized_safe : ∀ a ∈ c, 2 ≤ a.phase.val → safeSmall a
  nonmain_zero : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3
  mass_eq : prePhase4MassSum c = (initialGap init : ℚ)

structure AdvancedProfile (n : ℕ) (init c : InputCfg n) : Prop where
  card_eq : c.card = n
  final_roles : finalRoles c
  role_good :
    RoleSplitConcentration.RoleSplitGood
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
      (1 / 25 : ℝ) n c
  all_three : ∀ a ∈ c, a.phase.val = 3
  safe_small : ∀ a ∈ c, safeSmall a
  nonmain_small : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3
  nonmain_bias : ∀ a ∈ c, a.role ≠ .main → a.bias = Bias.zero
  clock_counter : ∀ a ∈ c, a.role = .clock →
    a.counter.val = 50 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  clock_height : ∀ a ∈ c, a.role = .clock →
    a.minute.val < 16 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  main_hour : ∀ a ∈ c, a.role = .main →
    a.hour.val ≤ PhaseThreeModel.Numeric.hourIndex n / 16
  main_index : ∀ a ∈ c, a.role = .main →
    ∀ σ j, a.bias = Bias.dyadic σ j →
      j.val ≤ PhaseThreeModel.Numeric.hourIndex n / 16
  mass_eq : prePhase4MassSum c = (initialGap init : ℚ)

/-- The two genuine first hits and the complete intervening history. -/
structure AsyncEntry {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S T : ℕ) : Prop where
  seed_first : firstHit (someGE 3) (trace init ω) S
  all_first : firstHit (allGE 3) (trace init ω) T
  order : S ≤ T
  deadline : T ≤ S + activationHorizon n
  seed_profile : SeedProfile n init (trace init ω S)
  advanced_profile : AdvancedProfile n init (trace init ω T)
  roles : ∀ u, S ≤ u → u ≤ T → finalRoles (trace init ω u)
  phases : ∀ u, S ≤ u → u ≤ T →
    ∀ a ∈ trace init ω u, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3
  main_count : ∀ u, S ≤ u → u ≤ T →
    timeMainCount (trace init ω u) = timeMainCount (trace init ω S)
  clock_count : ∀ u, S ≤ u → u ≤ T →
    clockCount (trace init ω u) = clockCount (trace init ω S)
  reserve_count : ∀ u, S ≤ u → u ≤ T →
    reserveCount (trace init ω u) = reserveCount (trace init ω S)
  mixed_mass : ∀ u, S ≤ u → u ≤ T →
    prePhase4MassSum (trace init ω u) = (initialGap init : ℚ)

def sparseAsyncEntry {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S T : ℕ) : Prop :=
  AsyncEntry init ω S T ∧
    ∀ u, S ≤ u → u ≤ T → sparse (trace init ω u)

theorem AsyncEntry.first_phase_seed {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {S T : ℕ} (h : AsyncEntry init ω S T) :
    firstPhaseSeed init 3 S ω := by
  constructor
  · obtain ⟨a, ha, hpa⟩ := h.seed_first.1
    refine ⟨a, ha, le_antisymm (h.seed_profile.phase_range a ha).2 hpa⟩
  · intro u hu a ha
    exact Nat.lt_of_not_ge (fun hpa => h.seed_first.2 u hu ⟨a, ha, hpa⟩)

/-! ## The deterministic mass cap; this is not a premise of clockGood -/

private theorem bias_abs_le_one {L : ℕ} (b : Bias L) :
    |Bias.toRat b| ≤ (1 : ℚ) := by
  cases b with
  | zero => simp [Bias.toRat]
  | dyadic σ j =>
    have hpos : (0 : ℚ) < 2 ^ j.val := by positivity
    have hden : (1 : ℚ) ≤ 2 ^ j.val := one_le_pow₀ (by norm_num)
    have hfrac : (1 : ℚ) / 2 ^ j.val ≤ 1 := (div_le_one hpos).2 hden
    cases σ <;>
      simpa only [Bias.toRat, abs_div, abs_neg, abs_one, abs_of_pos hpos]
        using hfrac

private theorem dyadic_mass_le_main_count {L K : ℕ}
    (c : Cfg L K)
    (hnonmain : ∀ a ∈ c, a.role ≠ .main → a.bias = Bias.zero) :
    |dyadicBiasSum c| ≤ (timeMainCount c : ℚ) := by
  induction c using Multiset.induction_on with
  | empty =>
    simp [dyadicBiasSum, timeMainCount]
  | cons a c ih =>
    have htail : |dyadicBiasSum c| ≤ (timeMainCount c : ℚ) :=
      ih (fun x hx => hnonmain x (Multiset.mem_cons_of_mem hx))
    by_cases hm : a.role = .main
    · have hbound :=
        (abs_add_le (Bias.toRat a.bias) (dyadicBiasSum c)).trans
          (add_le_add (bias_abs_le_one a.bias) htail)
      simpa [dyadicBiasSum, timeMainCount, Multiset.countP_cons, hm, add_comm]
        using hbound
    · have hb : a.bias = Bias.zero :=
        hnonmain a (Multiset.mem_cons_self a c) hm
      simpa [dyadicBiasSum, timeMainCount, Multiset.countP_cons, hm, hb, Bias.toRat]
        using htail

private theorem gapMagnitude_cast {L K : ℕ} (init : Cfg L K) :
    (gapMagnitude init : ℚ) = |(initialGap init : ℚ)| := by
  unfold gapMagnitude
  calc
    ((initialGap init).natAbs : ℚ) =
        (((initialGap init).natAbs : ℤ) : ℚ) := by
          simp only [Int.cast_natCast]
    _ = ((|initialGap init| : ℤ) : ℚ) := by
      rw [Int.natCast_natAbs]
    _ = |(initialGap init : ℚ)| := by
      rw [Int.cast_abs]

theorem AsyncEntry.mass_cap {n : ℕ} {init : InputCfg n}
    {ω : InputLog n} {S T : ℕ} (h : AsyncEntry init ω S T) :
    gapMagnitude init ≤ timeMainCount (trace init ω S) := by
  have hconvert :=
    prePhase4MassSum_eq_dyadicBiasSum_of_phase_ge_three (trace init ω T)
      (by intro a ha; exact (h.advanced_profile.all_three a ha).ge)
  have hbound := dyadic_mass_le_main_count (trace init ω T)
    h.advanced_profile.nonmain_bias
  rw [← hconvert, h.advanced_profile.mass_eq, ← gapMagnitude_cast init] at hbound
  have hnat : gapMagnitude init ≤ timeMainCount (trace init ω T) := by
    exact_mod_cast hbound
  simpa only [h.main_count T h.order le_rfl] using hnat

/-! ## Persistent-label observables

Coordinate k is the interaction taking configuration k-1 to k. Thus
the two contact counters below use Ioc u v, not Icc u v.
-/

def clockTop (n : ℕ) : ℕ :=
  256 * (PhaseThreeModel.Numeric.hourIndex n + 1)

def active {n : ℕ} (init : InputCfg n) (ω : InputLog n)
    (v : ℕ) (i : Fin init.card) : Prop :=
  3 ≤ (PairLog.labelsAt init ω v i).phase.val

def fixedRole {n : ℕ} (init : InputCfg n) (ω : InputLog n)
    (S : ℕ) (r : Role) (i : Fin init.card) : Prop :=
  (PairLog.labelsAt init ω S i).role = r

noncomputable def labelCount {n : ℕ} (init : InputCfg n)
    (P : Fin init.card → Prop) : ℕ :=
  (Finset.univ.filter P).card

noncomputable def activeCount {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (v : ℕ) : ℕ :=
  labelCount init (active init ω v)

noncomputable def activeRoleCount {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v : ℕ) (r : Role) : ℕ :=
  labelCount init (fun i => fixedRole init ω S r i ∧ active init ω v i)

noncomputable def effectiveMinute {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (v : ℕ) (i : Fin init.card) : ℕ :=
  if active init ω v i then (PairLog.labelsAt init ω v i).minute.val else 0

noncomputable def frontCount {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v ell : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRole init ω S .clock i ∧ ell ≤ effectiveMinute init ω v i)

noncomputable def frontHeight {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v : ℕ) : ℕ :=
  (Finset.univ.filter (fixedRole init ω S .clock)).sup
    (effectiveMinute init ω v)

noncomputable def bulkThreshold (C : ℕ) : ℕ :=
  Nat.ceil ((C : ℝ) / 10)

noncomputable def highThreshold (C : ℕ) : ℕ :=
  Nat.ceil (9 * (C : ℝ) / 10)

def smallThreshold (C : ℕ) : ℕ := C / 1000

noncomputable def frontQuantile {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v b : ℕ) : ℕ :=
  ((Finset.range (clockTop n + 1)).filter
    (fun ell => b ≤ frontCount init ω S v ell)).sup id

noncomputable def frontWidth (C : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (Real.log (C : ℝ))) + 16

noncomputable def frontCutoff (C : ℕ) : ℕ :=
  Nat.ceil (Real.rpow (C : ℝ) ((17 : ℝ) / 25))

noncomputable def localTickBudget (C : ℕ) : ℕ :=
  200 * frontWidth C * C

/-- Both orientations of the recorded physical Clock pair are counted. -/
def clockContact {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S k : ℕ) : Prop :=
  ∃ i j, PairLog.drawLabels init ω k = some (i, j) ∧
    fixedRole init ω S .clock i ∧ fixedRole init ω S .clock j

noncomputable def clockContacts {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S u v : ℕ) : ℕ :=
  ((Finset.Ioc u v).filter (clockContact init ω S)).card

/-- Exact Clock hour is minute/256. Main dragging, separately, clips at L. -/
noncomputable def exactHourClocks {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRole init ω S .clock i ∧ active init ω v i ∧
      (PairLog.labelsAt init ω v i).minute.val / 256 = h)

noncomputable def highHourMains {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRole init ω S .main i ∧ active init ω v i ∧
      h < (PairLog.labelsAt init ω v i).hour.val)

noncomputable def highHourZeroMains {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRole init ω S .main i ∧ active init ω v i ∧
      (PairLog.labelsAt init ω v i).bias = Bias.zero ∧
      h < (PairLog.labelsAt init ω v i).hour.val)

noncomputable def deepBiasedMains {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S v h : ℕ) : ℕ :=
  labelCount init (fun i =>
    fixedRole init ω S .main i ∧ active init ω v i ∧
      ∃ σ j, (PairLog.labelsAt init ω v i).bias = Bias.dyadic σ j ∧ h < j.val)

/-- Eligibility is tested in the actual preinteraction state of both endpoints.
The terminal coordinate is positive; no truncated predecessor is used at zero. -/
def eligibleContact {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S : ℕ) (i : Fin init.card) (k : ℕ) : Prop :=
  0 < k ∧ ∃ j l,
    PairLog.drawLabels init ω k = some (j, l) ∧
    (i = j ∨ i = l) ∧
    fixedRole init ω S .clock j ∧ fixedRole init ω S .clock l ∧
    (PairLog.labelsAt init ω (k - 1) j).phase.val = 3 ∧
    (PairLog.labelsAt init ω (k - 1) l).phase.val = 3 ∧
    (PairLog.labelsAt init ω (k - 1) j).minute.val = clockTop n ∧
    (PairLog.labelsAt init ω (k - 1) l).minute.val = clockTop n

noncomputable def eligibleContacts {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S : ℕ) (i : Fin init.card) (u v : ℕ) : ℕ :=
  ((Finset.Ioc u v).filter (eligibleContact init ω S i)).card

/-- Finite witnesses only; the producer must prove their genuine first-hit
properties. Unused values above the specified finite ranges are irrelevant. -/
structure ClockTimes {n : ℕ} (init : InputCfg n) where
  activation : ℕ
  cap : ℕ
  first : ℕ → ℕ
  bulk : ℕ → ℕ
  start : ℕ → ℕ
  finish : ℕ → ℕ
  initialized : Fin init.card → ℕ

/-- The auxiliary P14 local cap-spread event, equation (59).
It is deliberately separate from the seven defining clauses of G'_3. -/
def localCapSpread {n : ℕ} (init : InputCfg n) (ω : InputLog n)
    (S : ℕ) (w : ClockTimes init) : Prop :=
  let C := clockCount (trace init ω S)
  clockContacts init ω S (w.first (clockTop n)) w.cap ≤
    localTickBudget C + 8 * C +
      Nat.ceil (4 * (C : ℝ) * Real.log (n : ℝ))

/-! ## The seven reviewed clock clauses -/

/-- This is G'_3 with all finite first-hit witnesses retained.

The exact first Phase-4 seed is the successful first counter exit used by
PHASE3 P14--P15: no earlier phase is at least four, and the exiting Clock
enters Phase 4. Later phases at the final dissemination deadline are allowed.
-/
structure ClockHistory {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S T ρ : ℕ) (w : ClockTimes init) : Prop where
  /- G3'.1: the original history, not a later replacement snapshot. -/
  entry : AsyncEntry init ω S T
  roles_fixed : ∀ v, S ≤ v → v < ρ → ∀ i : Fin init.card,
    (PairLog.labelsAt init ω v i).role =
      (PairLog.labelsAt init ω S i).role
  main_count : ∀ v, S ≤ v → v < ρ →
    timeMainCount (trace init ω v) = timeMainCount (trace init ω S)
  clock_count : ∀ v, S ≤ v → v < ρ →
    clockCount (trace init ω v) = clockCount (trace init ω S)
  reserve_count : ∀ v, S ≤ v → v < ρ →
    reserveCount (trace init ω v) = reserveCount (trace init ω S)
  phase_range : ∀ v, S ≤ v → v < ρ →
    ∀ a ∈ trace init ω v, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3
  all_three : ∀ v, T ≤ v → v < ρ →
    ∀ a ∈ trace init ω v, a.phase.val = 3
  density : ∀ v, S ≤ v → v < ρ →
    12 * n ≤ 25 * timeMainCount (trace init ω v) ∧
    25 * timeMainCount (trace init ω v) ≤ 13 * n ∧
    6 * n ≤ 25 * clockCount (trace init ω v) ∧
    25 * clockCount (trace init ω v) ≤ 7 * n ∧
    6 * n ≤ 25 * reserveCount (trace init ω v)
  activation_first :
    firstAfter (fun v =>
      Nat.ceil ((99 : ℝ) * (n : ℝ) / 100) ≤ activeCount init ω v)
      S w.activation
  first_zero : w.first 0 = S
  bulk_zero : w.bulk 0 = S
  level_first : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter (fun v => 1 ≤ frontCount init ω S v ell) S (w.first ell)
  level_bulk : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    firstAfter (fun v =>
      bulkThreshold (clockCount (trace init ω S)) ≤
        frontCount init ω S v ell) S (w.bulk ell)
  start_zero : w.start 0 = w.activation
  start_positive : ∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
    firstAfter (fun v =>
      highThreshold (clockCount (trace init ω S)) ≤
        frontCount init ω S v (256 * h)) S (w.start h)
  finish_first : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    firstAfter (fun v =>
      smallThreshold (clockCount (trace init ω S)) ≤
        frontCount init ω S v (256 * (h + 1))) S (w.finish h)
  cap_first :
    firstAfter (fun v =>
      frontCount init ω S v (clockTop n) = clockCount (trace init ω S))
      S w.cap
  activation_before_cap : w.activation ≤ w.cap
  all_before_cap : T ≤ w.cap
  level_before_cap : ∀ ell, ell ≤ clockTop n →
    w.first ell ≤ w.cap ∧ w.bulk ell ≤ w.cap
  hour_before_cap : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.start h ≤ w.cap ∧ w.finish h ≤ w.cap
  first_exit : firstPhaseSeed init 4 ρ ω
  cap_deadline : w.cap ≤ S + logWindow n 20000
  exit_deadline : ρ ≤ S + logWindow n 20000

  /- G3'.2: both effective front widths and the first-passage shape bound. -/
  bulk_width :
    let C := clockCount (trace init ω S)
    ∀ v, S ≤ v → v ≤ w.cap →
      frontHeight init ω S v -
        frontQuantile init ω S v (bulkThreshold C) ≤ 2 * frontWidth C
  high_width :
    let C := clockCount (trace init ω S)
    ∀ v, S ≤ v → v ≤ w.cap →
      frontHeight init ω S v -
        frontQuantile init ω S v (highThreshold C) ≤ 2 * frontWidth C + 20
  front_shape :
    let C := clockCount (trace init ω S)
    ∀ ell v, 1 ≤ ell → ell < clockTop n →
      S ≤ v → v ≤ w.bulk ell →
      frontCutoff C ≤ frontCount init ω S v ell →
      frontCount init ω S v ell ≤ bulkThreshold C →
      C * frontCount init ω S v (ell + 1) ≤
        frontCount init ω S v ell ^ 2

  /- G3'.3: all three distinct local horizons. -/
  raw_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell - w.first ell ≤ logWindow n 30
  tick_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    clockContacts init ω S (max (w.first ell) w.activation) (w.bulk ell) ≤
      localTickBudget (clockCount (trace init ω S))
  fine_raw_local : ∀ ell, 1 ≤ ell → ell ≤ clockTop n →
    w.bulk ell ≤ max (w.first ell) w.activation +
      2000 * n * frontWidth (clockCount (trace init ω S))

  /- G3'.4: hour zero is activation, and all occupancy windows are closed. -/
  activation_before_twenty : w.activation ≤ w.bulk 20
  previous_end : ∀ h, 1 ≤ h → h ≤ PhaseThreeModel.Numeric.hourIndex n →
    w.finish (h - 1) < w.start h
  raw_width : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    70 * n ^ 2 <
      clockCount (trace init ω S) * (w.finish h - w.start h)
  exact_hour : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, w.start h ≤ v → v ≤ w.finish h →
      899 * clockCount (trace init ω S) ≤
        1000 * exactHourClocks init ω S v h
  active_main_floor : ∀ v, w.activation ≤ v → v < ρ →
    47 * timeMainCount (trace init ω S) ≤
      48 * activeRoleCount init ω S v .main
  active_clock_floor : ∀ v, w.activation ≤ v → v < ρ →
    23 * clockCount (trace init ω S) ≤
      24 * activeRoleCount init ω S v .clock
  first_work_allowance : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((2 : ℝ) * (n : ℝ) ^ 2 /
        (clockCount (trace init ω S) : ℝ)) +
      Nat.ceil ((47 : ℝ) * (n : ℝ) ^ 2 /
        (timeMainCount (trace init ω S) : ℝ)) + 1 ≤
      w.finish h - w.start h
  second_work_allowance : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    Nat.ceil ((51 : ℝ) * (n : ℝ) ^ 2 /
      (timeMainCount (trace init ω S) : ℝ)) ≤ w.finish h - w.start h

  /- G3'.5: inactive raw Main fields are not counted. -/
  main_hour_tail : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, S ≤ v → v ≤ w.finish h →
      2500 * highHourMains init ω S v h ≤
        3 * timeMainCount (trace init ω S)
  main_deep_tail : ∀ h, h ≤ PhaseThreeModel.Numeric.hourIndex n →
    ∀ v, S ≤ v → v ≤ w.finish h →
      1250 * (highHourZeroMains init ω S v h +
        deepBiasedMains init ω S v h) ≤ 3 * timeMainCount (trace init ω S)

  /- G3'.6: actual per-label Init-3 times and protected counters. -/
  cap_from_activation : w.cap ≤ T + logWindow n 16000
  protected_settling : w.cap + logWindow n 16 < ρ
  initialized_first : ∀ i, fixedRole init ω S .clock i →
    firstHit (fun a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 =>
      3 ≤ a.phase.val) (fun v => PairLog.labelsAt init ω v i) (w.initialized i)
  initialized_by_all : ∀ i, fixedRole init ω S .clock i →
    w.initialized i ≤ T
  counter_reset : ∀ i, fixedRole init ω S .clock i →
    (PairLog.labelsAt init ω (w.initialized i) i).counter.val =
      50 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  initialized_before_first_cap : ∀ i, fixedRole init ω S .clock i →
    w.initialized i < w.first (clockTop n)
  eligible_budget : ∀ i, fixedRole init ω S .clock i →
    eligibleContacts init ω S i (w.initialized i)
      (w.cap + logWindow n 16) <
      40 * (PhaseThreeModel.Numeric.hourIndex n + 1)
  counter_reserve : ∀ i, fixedRole init ω S .clock i →
    ∀ v, w.initialized i ≤ v → v ≤ w.cap + logWindow n 16 →
      10 * (PhaseThreeModel.Numeric.hourIndex n + 1) + 1 ≤
        (PairLog.labelsAt init ω v i).counter.val

  /- G3'.7: actual exit and threshold dissemination. -/
  exit_after_cap : ρ ≤ w.cap + logWindow n 400
  final_spread : allGE 4 (trace init ω (S + logWindow n 20000))

def reviewedClockGood {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S T ρ : ℕ) : Prop :=
  ∃ w : ClockTimes init, ClockHistory init ω S T ρ w

/-! ## First-barrier priority for a localized height argument

The successful crossing is frozen before the backup test. In particular,
backup at a later time cannot erase an earlier height witness. This auxiliary
process is for the entry/clock producer; it is not a scheduler conditioning
event and is not an additional premise of the entry predicate.
-/

def frozenFirstBarrierValue (Y : ℕ → ℝ) (σ β t : ℕ) : ℝ :=
  if σ ≤ t ∧ σ < β then Y σ else if β ≤ t then 0 else Y t

theorem frozenFirstBarrierValue_of_first (Y : ℕ → ℝ)
    {σ β t : ℕ} (hfirst : σ < β) (ht : σ ≤ t) :
    frozenFirstBarrierValue Y σ β t = Y σ := by
  unfold frozenFirstBarrierValue
  rw [if_pos (And.intro ht hfirst)]

theorem frozenFirstBarrierValue_after_backup (Y : ℕ → ℝ)
    {σ β t : ℕ} (hfirst : σ < β) (ht : β ≤ t) :
    frozenFirstBarrierValue Y σ β t = Y σ :=
  frozenFirstBarrierValue_of_first Y hfirst
    (le_trans (Nat.le_of_lt hfirst) ht)

/-! ## The canonical StageEvents constructor -/

noncomputable def reviewedStageEvents
    (n : ℕ) (init : InputCfg n) :
    StageEvents n init where
  entry := AsyncEntry init
  clockGood := reviewedClockGood init
  averageGood := fun ω S ρ =>
    averageReadout init (timeMainCount (trace init ω S)) (trace init ω ρ)
  entry_seed := by
    intro ω S T h
    exact h.first_phase_seed
  entry_order := by
    intro ω S T h
    exact h.order
  clock_seed := by
    intro ω S T ρ h
    obtain ⟨w, hw⟩ := h
    exact hw.first_exit
  clock_deadline := by
    intro ω S T ρ h
    obtain ⟨w, hw⟩ := h
    exact hw.exit_deadline
  clock_mass := by
    intro ω S T ρ h
    obtain ⟨w, hw⟩ := h
    exact hw.entry.mass_cap

theorem reviewedStageEvents_entry_iff {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S T : ℕ) :
    (reviewedStageEvents n init).entry ω S T ↔ AsyncEntry init ω S T :=
  Iff.rfl

theorem reviewedStageEvents_clockGood_iff {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S T ρ : ℕ) :
    (reviewedStageEvents n init).clockGood ω S T ρ ↔
      ∃ w : ClockTimes init, ClockHistory init ω S T ρ w :=
  Iff.rfl

theorem reviewedStageEvents_averageGood_iff {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (S ρ : ℕ) :
    (reviewedStageEvents n init).averageGood ω S ρ ↔
      averageReadout init (timeMainCount (trace init ω S)) (trace init ω ρ) :=
  Iff.rfl

end Ripple.PopulationProtocol.ExactMajority.StageEventSpec

end
