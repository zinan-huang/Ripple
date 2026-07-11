import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3GoodClock
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedKillNow
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma610StoppedAzuma
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Lemma615MassAboveDefs
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Real

namespace Phase3Core

open P3DeterministicAlgebra

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
Slot-3 piece 5: the thin Core(h) scaffold.

This file fixes only the stopped contracts and the strong-induction threading.
The H13/H14/H15/H16 producers are explicit assumptions for the later bridge and
engine pieces.  In particular, H14 is a stopped checkpoint hit and is vacuous for
`h < q`; none of these contracts is a global invariant over all reachable states.
-/

/-- Configurations for the concrete nonuniform exact-majority protocol. -/
abbrev Omega (L K : ℕ) := Config (AgentState L K)

/-! ## Mode/domain: the tie-vs-majority `ell` surface -/

/-- Domain object for the Core(h) induction.

The mode reuses `Phase3Pre3.Pre3Mode`, so the Phase-3 entry bundle and the Core
induction cannot silently disagree about tie/majority.  The "early" side is
always written as `h + 5 <= ell`; the domain carries `5 <= ell` explicitly.
-/
structure Phase3ModeDomain (L : ℕ) where
  mode : Phase3Pre3.Pre3Mode
  ell : ℕ
  lastCoreHour : ℕ
  five_le_ell : 5 ≤ ell
  lastCore_le_L : lastCoreHour ≤ L
  lastCore_le_ell : lastCoreHour ≤ ell
  tie_ell : mode = Phase3Pre3.Pre3Mode.tie → ell = L + 5
  tie_lastCore : mode = Phase3Pre3.Pre3Mode.tie → lastCoreHour = L
  tie_all_hours_early :
    mode = Phase3Pre3.Pre3Mode.tie → ∀ h, h ≤ lastCoreHour → h + 5 ≤ ell
  majority_lastCore : (∃ σ, mode = Phase3Pre3.Pre3Mode.majority σ) → lastCoreHour = ell
  /-- Carried for the later Lemma 6.18 readout; Core itself does not use it. -/
  majority_l_plus_two_le_L :
    (∃ σ, mode = Phase3Pre3.Pre3Mode.majority σ) → ell + 2 ≤ L
  /-- Doty's `q = floor(log_3 n)`; only positivity belongs in this scaffold. -/
  q : ℕ
  q_pos : 0 < q
  /-- Main count `|M|`, as a natural threshold scale. -/
  M : ℕ
  M_pos : 0 < M
  /-- Doty's total-mass constants `rho_h`. -/
  rho : ℕ → ℝ
  /-- Doty's O-fuel constants `tau_h`. -/
  tau : ℕ → ℝ
  rho_nonneg : ∀ h, 0 ≤ rho h
  tau_nonneg : ∀ h, 0 ≤ tau h

/-- Early hours, stated without Nat subtraction. -/
def Early (D : Phase3ModeDomain L) (h : ℕ) : Prop :=
  h + 5 ≤ D.ell

/-- The final-five table region, also subtraction-free. -/
def FinalFive (D : Phase3ModeDomain L) (h : ℕ) : Prop :=
  h ≤ D.ell ∧ D.ell ≤ h + 4

/-! ## Main-above tiny threshold -/

/-- Doty's Main-side Lemma-6.10 confinement threshold:
`floor((12/10000) * |M|)`, represented over naturals. -/
def mainAboveTinyThreshold (M : ℕ) : ℕ :=
  12 * M / 10000

/-- The integer Main-side threshold plus one dominates the real
`(12/10000) * |M|` cutoff. -/
theorem mainAboveTinyThreshold_real_le_succ (M : ℕ) :
    (12 / 10000 : ℝ) * (M : ℝ) ≤
      (((mainAboveTinyThreshold M + 1 : ℕ) : ℝ)) := by
  have hlt_nat : 12 * M < 10000 * (12 * M / 10000 + 1) := by
    exact Nat.lt_mul_div_succ (12 * M) (by norm_num : 0 < 10000)
  have hlt_real :
      ((12 * M : ℕ) : ℝ) <
        ((10000 * (12 * M / 10000 + 1) : ℕ) : ℝ) := by
    exact_mod_cast hlt_nat
  have hlt_scaled :
      ((12 * M : ℕ) : ℝ) <
        (10000 : ℝ) * (((12 * M / 10000 + 1 : ℕ) : ℝ)) := by
    simpa [Nat.cast_mul] using hlt_real
  have hlt_div :
      ((12 * M : ℕ) : ℝ) / 10000 <
        (((12 * M / 10000 + 1 : ℕ) : ℝ)) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 10000)]
    simpa [mul_comm] using hlt_scaled
  have hrewrite :
      (12 / 10000 : ℝ) * (M : ℝ) =
        ((12 * M : ℕ) : ℝ) / 10000 := by
    norm_num [Nat.cast_mul]
    ring
  simpa [mainAboveTinyThreshold, hrewrite] using le_of_lt hlt_div

/-- Failure of the M-scale Main tiny threshold gives the normalized Main
fraction used by Lemma 6.10.  This is a definitional theorem, not a residual
numeric assumption. -/
theorem main_not_tiny_frac
    {D : Phase3ModeDomain L} {h : ℕ} {c : Omega L K}
    (hnot_tiny :
      ¬ HourCoupling.mAbove (L := L) (K := K) h c ≤
        mainAboveTinyThreshold D.M) :
    (12 / 10000 : ℝ) ≤
      (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / (D.M : ℝ) := by
  have hM_pos : (0 : ℝ) < (D.M : ℝ) := by
    exact_mod_cast D.M_pos
  have hthreshold_lt_m :
      mainAboveTinyThreshold D.M <
        HourCoupling.mAbove (L := L) (K := K) h c :=
    Nat.lt_of_not_ge hnot_tiny
  have hthreshold_succ_le_m :
      mainAboveTinyThreshold D.M + 1 ≤
        HourCoupling.mAbove (L := L) (K := K) h c :=
    Nat.succ_le_of_lt hthreshold_lt_m
  have hthreshold_succ_le_m_real :
      (((mainAboveTinyThreshold D.M + 1 : ℕ) : ℝ)) ≤
        (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) := by
    exact_mod_cast hthreshold_succ_le_m
  have hthreshold_frac :
      (12 / 10000 : ℝ) ≤
        (((mainAboveTinyThreshold D.M + 1 : ℕ) : ℝ)) / (D.M : ℝ) := by
    rw [le_div_iff₀ hM_pos]
    exact mainAboveTinyThreshold_real_le_succ D.M
  have hfrac_mono :
      (((mainAboveTinyThreshold D.M + 1 : ℕ) : ℝ)) / (D.M : ℝ) ≤
        (HourCoupling.mAbove (L := L) (K := K) h c : ℝ) / (D.M : ℝ) :=
    div_le_div_of_nonneg_right hthreshold_succ_le_m_real hM_pos.le
  exact hthreshold_frac.trans hfrac_mono

/-! ## Stopped thread surface -/

/-- Named checkpoints inside hour `h`. -/
inductive Cut where
  | hourStart
  | afterO
  | afterPhi
  | afterMass
  | hourEnd
  deriving DecidableEq, Repr

/-- The run-local stopped surface shared by all Core(h) rows.

The gates and checkpoints are intentionally one thread of stopped kernels.  Later
producer proofs may show that concrete trace checkpoints lie in these sets, but
Core never asks for a fresh global entry invariant per hour.
-/
structure CoreRunSurface (D : Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) where
  hourGate : ℕ → Set (Omega L K)
  spanGate : ℕ → ℕ → Set (Omega L K)
  checkpoint : Cut → ℕ → Set (Omega L K)
  /-- Fixed clock population denominator for the hour-coupling potential. -/
  leakageC : ℝ
  leakageC_pos : 0 < leakageC
  /-- Phase-3 uses a positive minutes-per-hour scale. -/
  leakageK_pos : 0 < K
  /-- Hour-local gates sit inside the synchronous-hour regime used by stopped
  Lemma 6.10.  This is the satisfiable Regime/GoodClock handoff, not a global
  invariant over arbitrary configurations. -/
  hourGate_le_regime : ∀ h, h ≤ D.lastCoreHour →
    hourGate h ⊆
      Lemma610StoppedAzuma.regimeSet (L := L) (K := K) (D.M : ℝ) leakageC h
  /-- Checkpoint starts are actual starts for the stopped hour gate. -/
  hourStart_mem_gate : ∀ h, h ≤ D.lastCoreHour →
    checkpoint .hourStart h ⊆ hourGate h
  /-- Every named checkpoint used by the stopped row contracts is structurally
  inside the immediate-kill hour gate.  Thus alive killed-kernel mass is
  automatically eligible for checkpoint-indexed row tails; no trace-membership
  fact is needed as a distributional premise. -/
  checkpoint_mem_gate : ∀ cut h, h ≤ D.lastCoreHour →
    checkpoint cut h ⊆ hourGate h
  /-- The concrete full-kernel trace reaches the `afterO` checkpoint cut. -/
  trace_afterO_mem_checkpoint :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC) ∈ checkpoint .afterO h
  /-- The concrete full-kernel trace reaches the `afterPhi` checkpoint cut. -/
  trace_afterPhi_mem_checkpoint :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortyOneOverM) ∈
        checkpoint .afterPhi h
  /-- The concrete full-kernel trace reaches the `afterMass` checkpoint cut. -/
  trace_afterMass_mem_checkpoint :
    ∀ (G : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr)
      (h : ℕ), h ≤ D.lastCoreHour →
      let I := Phase3GoodClock.CoreClockInputs.ofGoodClock
        (L := L) (K := K) D.M h G
      tr (I.start + θ.twoOverC + θ.fortySevenOverM) ∈
        checkpoint .afterMass h
  /-- Synchronized start for the Lemma-6.10 potential. -/
  hourStart_phi_zero : ∀ h, h ≤ D.lastCoreHour →
    ∀ c, c ∈ checkpoint .hourStart h →
      HourCouplingAzuma.Phi (L := L) (K := K) (D.M : ℝ) leakageC h c = 0
  /-- The constrained hour gate is clock-leakage-good throughout the stopped
  hour.  The later GoodClock/Regime proof supplies this field. -/
  hourGate_clock_tiny : ∀ h, h ≤ D.lastCoreHour →
    ∀ c, c ∈ hourGate h →
      Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c
  /-- The constrained start is already Main-leakage-good, closing the `dt = 0`
  Dirac case. -/
  hourStart_main_tiny : ∀ h, h ≤ D.lastCoreHour →
    ∀ c, c ∈ checkpoint .hourStart h →
      HourCoupling.mAbove (L := L) (K := K) h c ≤
        mainAboveTinyThreshold D.M
  /-- Clock tiny implies the normalized clock premise of Lemma 6.10. -/
  clockTiny_frac : ∀ h c,
    Phase3GoodClock.TinyBeforeEnd (L := L) (K := K) θ h c →
      (HourCoupling.cAbove (L := L) (K := K) h c : ℝ) / leakageC ≤
        (1 / 1000 : ℝ)
  eps13 : ℕ → ℝ≥0∞
  eps14 : ℕ → ℝ≥0∞
  eps15 : ℕ → ℝ≥0∞
  eps16 : ℕ → ℝ≥0∞

/-- One Core proof thread: a single GoodClock trace plus the stopped gates used by
all H_i contracts. -/
structure CoreThread (D : Phase3ModeDomain L)
    (θ : Phase3GoodClock.ClockTimingParams)
    (tr : Phase3GoodClock.Trace L K) where
  good : Phase3GoodClock.GoodClock (L := L) (K := K) D.M θ tr
  surface : CoreRunSurface (L := L) (K := K) D θ tr

namespace CoreThread

noncomputable def clockInput {D : Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (T : CoreThread (L := L) (K := K) D θ tr) (h : ℕ) :
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h :=
  Phase3GoodClock.CoreClockInputs.ofGoodClock (L := L) (K := K) D.M h T.good

end CoreThread

namespace ClockCut

noncomputable def start {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (I : Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h) : ℕ :=
  I.start

noncomputable def afterO {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (I : Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h) : ℕ :=
  I.start + θ.twoOverC

noncomputable def afterPhi {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (I : Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h) : ℕ :=
  I.start + θ.twoOverC + θ.fortyOneOverM

noncomputable def afterMass {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (I : Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h) : ℕ :=
  I.start + θ.twoOverC + θ.fortySevenOverM

noncomputable def finish {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K} {h : ℕ}
    (I : Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h) : ℕ :=
  I.finish

end ClockCut

namespace CoreThread

/-- The run trace at Doty's `2/c` cut is a member of the stopped `afterO`
checkpoint. -/
theorem trace_afterO_mem_checkpoint {D : Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (T : CoreThread (L := L) (K := K) D θ tr) (h : ℕ)
    (hh : h ≤ D.lastCoreHour) :
    tr (ClockCut.afterO (L := L) (K := K) (T.clockInput h)) ∈
      T.surface.checkpoint .afterO h := by
  simpa [clockInput, ClockCut.afterO] using
    T.surface.trace_afterO_mem_checkpoint T.good h hh

/-- The run trace at Doty's `2/c + 41/m` cut is a member of the stopped
`afterPhi` checkpoint. -/
theorem trace_afterPhi_mem_checkpoint {D : Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (T : CoreThread (L := L) (K := K) D θ tr) (h : ℕ)
    (hh : h ≤ D.lastCoreHour) :
    tr (ClockCut.afterPhi (L := L) (K := K) (T.clockInput h)) ∈
      T.surface.checkpoint .afterPhi h := by
  simpa [clockInput, ClockCut.afterPhi] using
    T.surface.trace_afterPhi_mem_checkpoint T.good h hh

/-- The run trace at Doty's `2/c + 47/m` cut is a member of the stopped
`afterMass` checkpoint. -/
theorem trace_afterMass_mem_checkpoint {D : Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (T : CoreThread (L := L) (K := K) D θ tr) (h : ℕ)
    (hh : h ≤ D.lastCoreHour) :
    tr (ClockCut.afterMass (L := L) (K := K) (T.clockInput h)) ∈
      T.surface.checkpoint .afterMass h := by
  simpa [clockInput, ClockCut.afterMass] using
    T.surface.trace_afterMass_mem_checkpoint T.good h hh

/-- The GoodClock hour handoff used by the Core induction: previous stopped hour
closes before the next hour starts. -/
theorem previous_finish_lt_start {D : Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (T : CoreThread (L := L) (K := K) D θ tr) (h : ℕ) (hh : 0 < h) :
    ClockCut.finish (L := L) (K := K) (T.clockInput (h - 1)) <
      ClockCut.start (L := L) (K := K) (T.clockInput h) := by
  simpa [ClockCut.finish, ClockCut.start, clockInput] using
    Phase3GoodClock.GoodClock.previous_hour_finished
      (L := L) (K := K) (G := T.good) h hh

/-- The same handoff in the common `h -> h+1` form. -/
theorem finish_lt_next_start {D : Phase3ModeDomain L}
    {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (T : CoreThread (L := L) (K := K) D θ tr) (h : ℕ) :
    ClockCut.finish (L := L) (K := K) (T.clockInput h) <
      ClockCut.start (L := L) (K := K) (T.clockInput (h + 1)) := by
  simpa [Nat.add_sub_cancel, ClockCut.finish, ClockCut.start, clockInput] using
    Phase3GoodClock.GoodClock.previous_hour_finished
      (L := L) (K := K) (G := T.good) (h + 1) (by omega)

end CoreThread

/-! ## Immediate-kill stopped tails -/

noncomputable abbrev phase3Kernel (L K : ℕ) :
    Kernel (Omega L K) (Omega L K) :=
  (NonuniformMajority L K).transitionKernel

/-- Cemetery plus a lifted bad set. -/
def killedBad {α : Type*} (Bad : α → Prop) : Set (Option α) :=
  {o | o = none ∨ ∃ x, o = some x ∧ Bad x}

/-- The common stopped-tail shape: the real kernel is immediately killed when it
exits the local gate, and `none` is charged as failure. -/
noncomputable def stoppedTail
    (G : Set (Omega L K)) (t : ℕ) (x : Omega L K)
    (Bad : Omega L K → Prop) (ε : ℝ≥0∞) : Prop :=
  (GatedDrift.killK_now (phase3Kernel L K) G ^ t) (some x)
    (killedBad Bad) ≤ ε

/-- A killed immediate-stop tail controls the corresponding full-kernel segment
tail from the same start.  The cemetery event is charged in `killedBad`, so the
ordinary endpoint bad event is dominated by `GatedDrift.real_le_killed_now`. -/
theorem real_tail_of_stoppedTail
    {G : Set (Omega L K)} {t : ℕ} {x : Omega L K}
    {Bad : Omega L K → Prop} {ε : ℝ≥0∞}
    (h : stoppedTail (L := L) (K := K) G t x Bad ε) :
    (phase3Kernel L K ^ t) x {y | Bad y} ≤ ε := by
  exact
    (GatedDrift.real_le_killed_now
      (K := phase3Kernel L K) (G := G) (bad := Bad) t x).trans h

/-! ## Weighted observables and Core targets -/

noncomputable def WeightedBias (c : Omega L K) : ℚ :=
  biasSumQ (L := L) (K := K) c

noncomputable def WeightedMass (c : Omega L K) : ℚ :=
  totalMassQ (L := L) (K := K) c

noncomputable def WeightedMassAbove (level : ℕ) (c : Omega L K) : ℚ :=
  massAboveQ (L := L) (K := K) level c

noncomputable def PhiAbove (level : ℕ) (c : Omega L K) : ℚ :=
  phiAboveQ (L := L) (K := K) level c

/-- H13 target: many `O_h` agents after the `2/c` warm-up. -/
def OFuelFloor (D : Phase3ModeDomain L) (h : ℕ) (c : Omega L K) : Prop :=
  D.tau h * (D.M : ℝ) ≤
    (Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) h c : ℝ)

/-- H14 target: `phi(> -level) = 0`. -/
def PhiZero (level : ℕ) (c : Omega L K) : Prop :=
  PhiAbove (L := L) (K := K) level c = 0

/-- The Doty Lemma-6.15 upper-tail threshold
`0.001 |M| 2^{-h+1} = (1/500) |M| 2^{-h}`. -/
noncomputable def H15MassThreshold (D : Phase3ModeDomain L) (h : ℕ) : ℝ :=
  (1 / 500 : ℝ) * (D.M : ℝ) * (2 : ℝ) ^ (-(h : ℤ))

/-- H15 potential readout, aligned with the landed Lemma-6.15 engine.  The
probabilistic engine exposes the Doty mass-above consequence, so the Core API
uses that exact readout for the potential-drop surface. -/
def PhiSmall (D : Phase3ModeDomain L) (h : ℕ) (c : Omega L K) : Prop :=
  Lemma615MassAbove.muAbove (L := L) (K := K) h c ≤
    H15MassThreshold (L := L) D h

/-- H15 mass-above readout, using Doty's Lemma-6.15 constant
`(1/500)|M|2^{-h}`. -/
def MassAboveSmall (D : Phase3ModeDomain L) (h : ℕ) (c : Omega L K) : Prop :=
  Lemma615MassAbove.muAbove (L := L) (K := K) h c ≤
    H15MassThreshold (L := L) D h

/-- H15 exposes both the phi drop and the mass-above surface needed downstream. -/
def PhiPotentialDrop (D : Phase3ModeDomain L) (h : ℕ) (c : Omega L K) : Prop :=
  PhiSmall (L := L) (K := K) D h c ∧
    MassAboveSmall (L := L) (K := K) D h c

/-- H16 target: weighted mass is on the `rho_h |M| 2^{-h}` line. -/
def TotalMassBound (D : Phase3ModeDomain L) (h : ℕ) (c : Omega L K) : Prop :=
  ((WeightedMass (L := L) (K := K) c : ℚ) : ℝ) ≤
    D.rho h * (D.M : ℝ) * (2 : ℝ) ^ (-(h : ℤ))

/-! ## H13/H14/H15/H16 stopped contracts -/

/-- H13: from the `afterO` checkpoint through `end_h`, the stopped hour-local
chain has enough `O_h` fuel. -/
structure H13 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : Prop where
  h_in_range : h ≤ D.lastCoreHour
  tail : ∀ cO, cO ∈ T.surface.checkpoint .afterO h →
    ∀ dt, dt ≤
        ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          ClockCut.afterO (L := L) (K := K) (T.clockInput h) →
      stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cO
        (fun c => ¬ OFuelFloor (L := L) (K := K) D h c)
        (T.surface.eps13 h)

/-- H14: far-above potential is zero by the `afterO h` checkpoint.

For `h < q` the statement is intentionally vacuous.  For `q <= h`, the level is
`h - q`, i.e. Doty's `phi(> -h + q)` surface. -/
inductive H14 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : Prop where
  | vacuous (h_in_range : h ≤ D.lastCoreHour) (hlt : h < D.q) : H14 D T h
  | hit (h_in_range : h ≤ D.lastCoreHour) (hq : D.q ≤ h)
      (base_in_range : h - D.q ≤ D.lastCoreHour)
      (tail : ∀ cStart, cStart ∈ T.surface.checkpoint .afterPhi (h - D.q) →
        stoppedTail (L := L) (K := K)
          (T.surface.spanGate (h - D.q) h)
          (ClockCut.afterO (L := L) (K := K) (T.clockInput h) -
            ClockCut.afterPhi (L := L) (K := K) (T.clockInput (h - D.q)))
          cStart
          (fun c => ¬ PhiZero (L := L) (K := K) (h - D.q) c)
          (T.surface.eps14 h)) : H14 D T h

/-- H15: from the `afterO` checkpoint to `afterPhi h`, the stopped local chain
achieves the phi/mass-above drop. -/
structure H15 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : Prop where
  h_in_range : h ≤ D.lastCoreHour
  tail : ∀ cO, cO ∈ T.surface.checkpoint .afterO h →
    stoppedTail (L := L) (K := K) (T.surface.hourGate h)
      (ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) -
        ClockCut.afterO (L := L) (K := K) (T.clockInput h))
      cO
      (fun c => ¬ PhiPotentialDrop (L := L) (K := K) D h c)
      (T.surface.eps15 h)

/-- H16: from the cancellation-complete checkpoint through `end_h`, the stopped
chain exposes the total-mass halving bound for the next hour. -/
structure H16 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : Prop where
  h_in_range : h ≤ D.lastCoreHour
  tail : ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      stoppedTail (L := L) (K := K) (T.surface.hourGate h) dt cPhi
        (fun c => ¬ TotalMassBound (L := L) (K := K) D h c)
        (T.surface.eps16 h)

/-- The Core(h) bundle. -/
def Core {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : Prop :=
  H13 (L := L) (K := K) D T h ∧
    H14 (L := L) (K := K) D T h ∧
    H15 (L := L) (K := K) D T h ∧
    H16 (L := L) (K := K) D T h

namespace Core

theorem h13 {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr} {h : ℕ}
    (hc : Core (L := L) (K := K) D T h) :
    H13 (L := L) (K := K) D T h := hc.1

theorem h14 {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr} {h : ℕ}
    (hc : Core (L := L) (K := K) D T h) :
    H14 (L := L) (K := K) D T h := hc.2.1

theorem h15 {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr} {h : ℕ}
    (hc : Core (L := L) (K := K) D T h) :
    H15 (L := L) (K := K) D T h := hc.2.2.1

theorem h16 {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr} {h : ℕ}
    (hc : Core (L := L) (K := K) D T h) :
    H16 (L := L) (K := K) D T h := hc.2.2.2

end Core

/-! ## Previous-hour extractor -/

/-- The exact history slice consumed by the H_i producers.

Lemma 6.14 gets `H15 (h-q)` and the finite H13 window
`h-q <= k`, `k+5 <= h`.  Lemmas 6.15/6.16 consume the immediate
previous-hour rows. -/
structure PrevCore {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : Prop where
  prevH15 : 0 < h → H15 (L := L) (K := K) D T (h - 1)
  prevH16 : 0 < h → H16 (L := L) (K := K) D T (h - 1)
  hqH15 : D.q ≤ h → H15 (L := L) (K := K) D T (h - D.q)
  hqH13Window : D.q ≤ h → ∀ k,
    h - D.q ≤ k → k + 5 ≤ h → H13 (L := L) (K := K) D T k

namespace PrevCore

/-- Arithmetic extraction of the previous rows from a strong-induction history. -/
def ofHistory {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr} {h : ℕ}
    (hist : ∀ k, k < h → Core (L := L) (K := K) D T k) :
    PrevCore (L := L) (K := K) D T h := by
  classical
  refine
    { prevH15 := ?_
      prevH16 := ?_
      hqH15 := ?_
      hqH13Window := ?_ }
  · intro hp
    have hk : h - 1 < h := by omega
    exact Core.h15 (hist (h - 1) hk)
  · intro hp
    have hk : h - 1 < h := by omega
    exact Core.h16 (hist (h - 1) hk)
  · intro hq
    have hqpos : 0 < D.q := D.q_pos
    have hk : h - D.q < h := by omega
    exact Core.h15 (hist (h - D.q) hk)
  · intro hq k hklo hkle
    have hk : k < h := by omega
    exact Core.h13 (hist k hk)

end PrevCore

/-! ## Producer assumptions and induction wiring -/

/-- Phase-3 entry/base package consumed by Core.

The `pre3` field is the landed `Phase3Pre3.Pre3` surface.  H13/H15 are allowed
to use the trivial `h < 5` bases; H16 has the substantive `h = 0` mass base.
-/
structure Pre3Seed {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr) where
  η : ℝ
  n : ℕ
  entry : Omega L K
  pre3 : Phase3Pre3.Pre3 (L := L) (K := K) η n D.mode D.ell entry
  entry_checkpoint : entry ∈ T.surface.checkpoint .hourStart 0
  earlyH13 : ∀ h, h ≤ D.lastCoreHour → h < 5 →
    H13 (L := L) (K := K) D T h
  earlyH15 : ∀ h, h ≤ D.lastCoreHour → h < 5 →
    H15 (L := L) (K := K) D T h
  baseH16 : H16 (L := L) (K := K) D T 0

/-- Producer contracts for the four Core rows.

These are the named assumptions discharged by the later bridge/engine pieces.
They are phrased against the same `CoreThread`, so the step consumes the previous
hour's closed stopped result instead of re-demanding a fresh fixed-time entry.
-/
structure CoreProducers {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr) where
  pre3 : Pre3Seed (L := L) (K := K) D T
  mkH13 : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    PrevCore (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    H13 (L := L) (K := K) D T h
  /-- Non-vacuous H14 producer; the scaffold handles `h < q` directly. -/
  mkH14 : ∀ h, h ≤ D.lastCoreHour → D.q ≤ h →
    PrevCore (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    H14 (L := L) (K := K) D T h
  mkH15 : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    PrevCore (L := L) (K := K) D T h →
    H13 (L := L) (K := K) D T h →
    H14 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    H15 (L := L) (K := K) D T h
  mkH16 : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    PrevCore (L := L) (K := K) D T h →
    H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    H16 (L := L) (K := K) D T h

namespace CoreProducers

noncomputable def buildH13 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    (P : CoreProducers (L := L) (K := K) D T)
    (h : ℕ) (hle : h ≤ D.lastCoreHour)
    (prev : PrevCore (L := L) (K := K) D T h) :
    H13 (L := L) (K := K) D T h := by
  by_cases hlt : h < 5
  · exact P.pre3.earlyH13 h hle hlt
  · exact P.mkH13 h hle (Nat.le_of_not_gt hlt) prev (T.clockInput h)

noncomputable def buildH14 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    (P : CoreProducers (L := L) (K := K) D T)
    (h : ℕ) (hle : h ≤ D.lastCoreHour)
    (prev : PrevCore (L := L) (K := K) D T h) :
    H14 (L := L) (K := K) D T h := by
  by_cases hlt : h < D.q
  · exact H14.vacuous (D := D) (T := T) (h := h) hle hlt
  · exact P.mkH14 h hle (Nat.le_of_not_gt hlt) prev (T.clockInput h)

noncomputable def buildH15 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    (P : CoreProducers (L := L) (K := K) D T)
    (h : ℕ) (hle : h ≤ D.lastCoreHour)
    (prev : PrevCore (L := L) (K := K) D T h)
    (h13 : H13 (L := L) (K := K) D T h)
    (h14 : H14 (L := L) (K := K) D T h) :
    H15 (L := L) (K := K) D T h := by
  by_cases hlt : h < 5
  · exact P.pre3.earlyH15 h hle hlt
  · exact P.mkH15 h hle (Nat.le_of_not_gt hlt) prev h13 h14 (T.clockInput h)

noncomputable def buildH16 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    (P : CoreProducers (L := L) (K := K) D T)
    (h : ℕ) (hle : h ≤ D.lastCoreHour)
    (prev : PrevCore (L := L) (K := K) D T h)
    (h15 : H15 (L := L) (K := K) D T h) :
    H16 (L := L) (K := K) D T h := by
  by_cases hzero : h = 0
  · simpa [hzero] using P.pre3.baseH16
  · exact P.mkH16 h hle (Nat.pos_of_ne_zero hzero) prev h15 (T.clockInput h)

end CoreProducers

/-- One strong-induction row, pure wiring. -/
noncomputable def core_step {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    (P : CoreProducers (L := L) (K := K) D T)
    (h : ℕ) (hle : h ≤ D.lastCoreHour)
    (prev : PrevCore (L := L) (K := K) D T h) :
    Core (L := L) (K := K) D T h := by
  let h13 : H13 (L := L) (K := K) D T h :=
    P.buildH13 h hle prev
  let h14 : H14 (L := L) (K := K) D T h :=
    P.buildH14 h hle prev
  let h15 : H15 (L := L) (K := K) D T h :=
    P.buildH15 h hle prev h13 h14
  let h16 : H16 (L := L) (K := K) D T h :=
    P.buildH16 h hle prev h15
  exact ⟨h13, h14, h15, h16⟩

/-- Strong induction over the actual Core hours. -/
theorem core_all {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    (P : CoreProducers (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour → Core (L := L) (K := K) D T h := by
  intro h
  refine Nat.strong_induction_on h ?step
  intro h hist hle
  exact core_step (L := L) (K := K) P h hle
    (PrevCore.ofHistory (L := L) (K := K) (D := D) (T := T) (h := h)
      (fun k hk => hist k hk (by omega)))

/-! ## Doty Theorem 6.12 surface -/

/-- The public 6.12-facing state: 6.13, 6.15, and 6.16.  H14 remains inside
`Core` as a dependency of 6.15. -/
def Lemma612 {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    (D : Phase3ModeDomain L) (T : CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : Prop :=
  H13 (L := L) (K := K) D T h ∧
    H15 (L := L) (K := K) D T h ∧
    H16 (L := L) (K := K) D T h

theorem lemma612_of_core {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    {h : ℕ} (hc : Core (L := L) (K := K) D T h) :
    Lemma612 (L := L) (K := K) D T h :=
  ⟨Core.h13 hc, Core.h15 hc, Core.h16 hc⟩

/-- Doty's Theorem 6.12 shape, obtained by the Core(h) induction. -/
theorem lemma612_all {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3ModeDomain L} {T : CoreThread (L := L) (K := K) D θ tr}
    (P : CoreProducers (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour → Lemma612 (L := L) (K := K) D T h := by
  intro h hle
  exact lemma612_of_core (core_all (L := L) (K := K) P h hle)

#print axioms CoreThread.finish_lt_next_start
#print axioms PrevCore.ofHistory
#print axioms real_tail_of_stoppedTail
#print axioms mainAboveTinyThreshold_real_le_succ
#print axioms main_not_tiny_frac
#print axioms core_all
#print axioms lemma612_all

end Phase3Core

end ExactMajority
