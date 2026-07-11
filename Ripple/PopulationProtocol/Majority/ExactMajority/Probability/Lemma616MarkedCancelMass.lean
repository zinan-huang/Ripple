import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Engines
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Real

namespace Lemma616MarkedCancelMass

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
Marked/ghost lift for Lemma 6.16.

The raw same-exponent cancellation counter is not monotone in the Phase-3 hour
window: later split reactions may create new cancellable agents at the same
exponent.  The ghost lift below tracks only a start cohort.  Cohort agents have
a set-once `consumed` bit, so the ghost cancellation counter is monotone; split
births are not inserted into the cohort and are paid for by an explicit
correction ledger.
-/

/-- Ghost state for one H16 cancellation row.

`minority = true` means the tracked start-cohort agent belongs to the row's
minority side; `minority = false` means it belongs to the row's majority side.
The side bit is immutable, while `consumed` is set once when the tracked agent
leaves its row side. -/
structure CancelGhost where
  st : AgentState L K
  cohort : Bool
  active : Bool
  consumed : Bool
  minority : Bool
  deriving DecidableEq, Fintype

abbrev GhostConfig := Config (CancelGhost (L := L) (K := K))

local instance instOptionMSCancelGhost :
    MeasurableSpace (Option (GhostConfig (L := L) (K := K))) := ⊤

local instance instOptionDMSCancelGhost :
    DiscreteMeasurableSpace (Option (GhostConfig (L := L) (K := K))) :=
  ⟨fun _ => trivial⟩

/-- Forget the H16 ghost marks. -/
def forgetGhost (C : GhostConfig (L := L) (K := K)) :
    Config (AgentState L K) :=
  C.map CancelGhost.st

/-- Majority-side Main agents at one same-exponent row, with `σ` carried
explicitly as the minority sign. -/
def rowMajorityAgent (σ : Sign) (idx : Fin (L + 1))
    (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ∃ ss : Sign, ss ≠ σ ∧ a.bias = Bias.dyadic ss idx

/-- Minority-side Main agents at one same-exponent row. -/
def rowMinorityAgent (σ : Sign) (idx : Fin (L + 1))
    (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.dyadic σ idx

instance (σ : Sign) (idx : Fin (L + 1)) (a : AgentState L K) :
    Decidable (rowMajorityAgent (L := L) (K := K) σ idx a) := by
  unfold rowMajorityAgent
  infer_instance

instance (σ : Sign) (idx : Fin (L + 1)) (a : AgentState L K) :
    Decidable (rowMinorityAgent (L := L) (K := K) σ idx a) := by
  unfold rowMinorityAgent
  infer_instance

def rowSideAgent (σ : Sign) (idx : Fin (L + 1)) (minority : Bool)
    (a : AgentState L K) : Prop :=
  if minority then
    rowMinorityAgent (L := L) (K := K) σ idx a
  else
    rowMajorityAgent (L := L) (K := K) σ idx a

instance (σ : Sign) (idx : Fin (L + 1)) (minority : Bool)
    (a : AgentState L K) :
    Decidable (rowSideAgent (L := L) (K := K) σ idx minority a) := by
  unfold rowSideAgent
  infer_instance

def ghostActiveSideAgent (σ : Sign) (idx : Fin (L + 1)) (minority : Bool)
    (a : CancelGhost (L := L) (K := K)) : Prop :=
  a.cohort = true ∧ a.active = true ∧ a.consumed = false ∧
    a.minority = minority ∧
      rowSideAgent (L := L) (K := K) σ idx minority a.st

def ghostConsumedMinorityAgent
    (a : CancelGhost (L := L) (K := K)) : Prop :=
  a.cohort = true ∧ a.consumed = true ∧ a.minority = true

instance (σ : Sign) (idx : Fin (L + 1)) (minority : Bool)
    (a : CancelGhost (L := L) (K := K)) :
    Decidable (ghostActiveSideAgent (L := L) (K := K) σ idx minority a) := by
  unfold ghostActiveSideAgent
  infer_instance

instance (a : CancelGhost (L := L) (K := K)) :
    Decidable (ghostConsumedMinorityAgent (L := L) (K := K) a) := by
  unfold ghostConsumedMinorityAgent
  infer_instance

/-- Tracked active majority-side count. -/
def ghostMajorityCount (σ : Sign) (idx : Fin (L + 1))
    (C : GhostConfig (L := L) (K := K)) : ℕ :=
  Multiset.countP
    (ghostActiveSideAgent (L := L) (K := K) σ idx false) C

/-- Tracked active minority-side count. -/
def ghostMinorityCount (σ : Sign) (idx : Fin (L + 1))
    (C : GhostConfig (L := L) (K := K)) : ℕ :=
  Multiset.countP
    (ghostActiveSideAgent (L := L) (K := K) σ idx true) C

/-- Ghost cancellation counter: consumed start-cohort minority agents.  A
same-exponent cancellation consumes exactly one minority-side input, so this is
the row counter used by the H16 clock. -/
def ghostCancelCount (_σ : Sign) (_idx : Fin (L + 1))
    (C : GhostConfig (L := L) (K := K)) : ℕ :=
  Multiset.countP (ghostConsumedMinorityAgent (L := L) (K := K)) C

/-- Capped ghost counter for the stopped clock.  The cap makes the cemetery and
post-target states inactive for `{C < D}`. -/
def ghostCancelClock (σ : Sign) (idx : Fin (L + 1)) (D : ℕ)
    (C : GhostConfig (L := L) (K := K)) : ℕ :=
  min (ghostCancelCount (L := L) (K := K) σ idx C) D

def liftGhostCancelClock (σ : Sign) (idx : Fin (L + 1)) (D : ℕ) :
    Option (GhostConfig (L := L) (K := K)) → ℕ
  | none => D
  | some C => ghostCancelClock (L := L) (K := K) σ idx D C

theorem ghostCancelClock_lt_iff
    (σ : Sign) (idx : Fin (L + 1)) (D : ℕ)
    (C : GhostConfig (L := L) (K := K)) :
    ghostCancelClock (L := L) (K := K) σ idx D C < D ↔
      ghostCancelCount (L := L) (K := K) σ idx C < D := by
  unfold ghostCancelClock
  constructor <;> intro h
  · by_contra hnot
    have hD : D ≤ ghostCancelCount (L := L) (K := K) σ idx C :=
      le_of_not_gt hnot
    have hmin : min (ghostCancelCount (L := L) (K := K) σ idx C) D = D :=
      Nat.min_eq_right hD
    omega
  · exact lt_of_le_of_lt (Nat.min_le_left _ _) h

@[simp] theorem liftGhostCancelClock_none
    (σ : Sign) (idx : Fin (L + 1)) (D : ℕ) :
    liftGhostCancelClock (L := L) (K := K) σ idx D none = D := rfl

@[simp] theorem liftGhostCancelClock_some
    (σ : Sign) (idx : Fin (L + 1)) (D : ℕ)
    (C : GhostConfig (L := L) (K := K)) :
    liftGhostCancelClock (L := L) (K := K) σ idx D (some C) =
      ghostCancelClock (L := L) (K := K) σ idx D C := rfl

/-- Positional ghost update for one output of the real transition.  A tracked
agent is consumed once it stops matching its immutable row side; split-born
row agents are untracked because they have no cohort bit. -/
noncomputable def advanceCancelGhost (σ : Sign) (idx : Fin (L + 1))
    (old : CancelGhost (L := L) (K := K)) (out : AgentState L K) :
    CancelGhost (L := L) (K := K) :=
  let trackable := old.cohort && old.active && !old.consumed
  let sideOk := decide (rowSideAgent (L := L) (K := K) σ idx old.minority out)
  let consumed' := old.consumed || (trackable && !sideOk)
  let active' := trackable && !consumed' && sideOk
  { st := out
    cohort := old.cohort
    active := active'
    consumed := consumed'
    minority := old.minority }

noncomputable def cancelGhostTransition (σ : Sign) (idx : Fin (L + 1))
    (a b : CancelGhost (L := L) (K := K)) :
    CancelGhost (L := L) (K := K) × CancelGhost (L := L) (K := K) :=
  let out := Transition L K a.st b.st
  (advanceCancelGhost (L := L) (K := K) σ idx a out.1,
   advanceCancelGhost (L := L) (K := K) σ idx b out.2)

noncomputable def cancelGhostProtocol (σ : Sign) (idx : Fin (L + 1)) :
    Protocol (CancelGhost (L := L) (K := K)) where
  δ := cancelGhostTransition (L := L) (K := K) σ idx

noncomputable abbrev cancelGhostKernel (σ : Sign) (idx : Fin (L + 1)) :
    Kernel (GhostConfig (L := L) (K := K))
      (GhostConfig (L := L) (K := K)) :=
  (cancelGhostProtocol (L := L) (K := K) σ idx).transitionKernel

@[simp] theorem advanceCancelGhost_st
    (σ : Sign) (idx : Fin (L + 1))
    (old : CancelGhost (L := L) (K := K)) (out : AgentState L K) :
    (advanceCancelGhost (L := L) (K := K) σ idx old out).st = out := rfl

theorem forgetGhost_cancelGhostTransition
    (σ : Sign) (idx : Fin (L + 1))
    (a b : CancelGhost (L := L) (K := K)) :
    ((cancelGhostTransition (L := L) (K := K) σ idx a b).1.st,
        (cancelGhostTransition (L := L) (K := K) σ idx a b).2.st) =
      Transition L K a.st b.st := by
  rfl

private theorem countP_singleton_ite {α : Type*} (P : α → Prop)
    [DecidablePred P] (x : α) :
    Multiset.countP P ({x} : Multiset α) = if P x then 1 else 0 := by
  change Multiset.countP P (x ::ₘ (0 : Multiset α)) = if P x then 1 else 0
  rw [Multiset.countP_cons, Multiset.countP_zero, zero_add]

private theorem countP_pair_ite {α : Type*} (P : α → Prop)
    [DecidablePred P] (x y : α) :
    Multiset.countP P ({x, y} : Multiset α) =
      (if P x then 1 else 0) + (if P y then 1 else 0) := by
  change Multiset.countP P (x ::ₘ ({y} : Multiset α)) =
    (if P x then 1 else 0) + (if P y then 1 else 0)
  rw [Multiset.countP_cons, countP_singleton_ite]
  omega

theorem ghostConsumedMinorityAgent_advance_of_old
    (σ : Sign) (idx : Fin (L + 1))
    (old : CancelGhost (L := L) (K := K)) (out : AgentState L K)
    (hold : ghostConsumedMinorityAgent (L := L) (K := K) old) :
    ghostConsumedMinorityAgent (L := L) (K := K)
      (advanceCancelGhost (L := L) (K := K) σ idx old out) := by
  rcases hold with ⟨hcohort, hconsumed, hminority⟩
  unfold ghostConsumedMinorityAgent advanceCancelGhost
  simp [hcohort, hconsumed, hminority]

theorem ghostConsumed_pair_update_mono
    (σ : Sign) (idx : Fin (L + 1))
    (a b : CancelGhost (L := L) (K := K)) :
    Multiset.countP (ghostConsumedMinorityAgent (L := L) (K := K))
        ({a, b} : Multiset (CancelGhost (L := L) (K := K)))
      ≤
    Multiset.countP (ghostConsumedMinorityAgent (L := L) (K := K))
        ({(cancelGhostTransition (L := L) (K := K) σ idx a b).1,
          (cancelGhostTransition (L := L) (K := K) σ idx a b).2}
          : Multiset (CancelGhost (L := L) (K := K))) := by
  classical
  rw [countP_pair_ite, countP_pair_ite]
  have haLe :
      (if ghostConsumedMinorityAgent (L := L) (K := K) a then 1 else 0)
        ≤
      (if ghostConsumedMinorityAgent (L := L) (K := K)
            (cancelGhostTransition (L := L) (K := K) σ idx a b).1 then 1 else 0) := by
    by_cases ha :
        ghostConsumedMinorityAgent (L := L) (K := K) a
    · have haNew :
          ghostConsumedMinorityAgent (L := L) (K := K)
            (cancelGhostTransition (L := L) (K := K) σ idx a b).1 := by
        simpa [cancelGhostTransition] using
          ghostConsumedMinorityAgent_advance_of_old
            (L := L) (K := K) σ idx a (Transition L K a.st b.st).1 ha
      simp [ha, haNew]
    · simp [ha]
  have hbLe :
      (if ghostConsumedMinorityAgent (L := L) (K := K) b then 1 else 0)
        ≤
      (if ghostConsumedMinorityAgent (L := L) (K := K)
            (cancelGhostTransition (L := L) (K := K) σ idx a b).2 then 1 else 0) := by
    by_cases hb :
        ghostConsumedMinorityAgent (L := L) (K := K) b
    · have hbNew :
          ghostConsumedMinorityAgent (L := L) (K := K)
            (cancelGhostTransition (L := L) (K := K) σ idx a b).2 := by
        simpa [cancelGhostTransition] using
          ghostConsumedMinorityAgent_advance_of_old
            (L := L) (K := K) σ idx b (Transition L K a.st b.st).2 hb
      simp [hb, hbNew]
    · simp [hb]
  exact Nat.add_le_add haLe hbLe

theorem ghostCancelCount_scheduledStep_mono
    (σ : Sign) (idx : Fin (L + 1))
    (C : GhostConfig (L := L) (K := K))
    (pr : CancelGhost (L := L) (K := K) ×
        CancelGhost (L := L) (K := K)) :
    ghostCancelCount (L := L) (K := K) σ idx C ≤
      ghostCancelCount (L := L) (K := K) σ idx
        (Protocol.scheduledStep
          (cancelGhostProtocol (L := L) (K := K) σ idx) C pr) := by
  classical
  unfold Protocol.scheduledStep Protocol.stepOrSelf
  by_cases happ : Protocol.Applicable C pr.1 pr.2
  · rw [if_pos happ]
    obtain ⟨rest, hrest⟩ : ∃ rest, C = rest + ({pr.1, pr.2}
        : Multiset (CancelGhost (L := L) (K := K))) :=
      ⟨C - {pr.1, pr.2}, (tsub_add_cancel_of_le happ).symm⟩
    rw [hrest, add_tsub_cancel_right]
    dsimp [cancelGhostProtocol]
    unfold ghostCancelCount
    rw [Multiset.countP_add, Multiset.countP_add]
    exact Nat.add_le_add_left
      (ghostConsumed_pair_update_mono (L := L) (K := K) σ idx pr.1 pr.2) _
  · rw [if_neg happ]

theorem ghostCancelCount_stepDistOrSelf_support_mono
    (σ : Sign) (idx : Fin (L + 1))
    (C C' : GhostConfig (L := L) (K := K))
    (hsupp : C' ∈
      ((cancelGhostProtocol (L := L) (K := K) σ idx).stepDistOrSelf C).support) :
    ghostCancelCount (L := L) (K := K) σ idx C ≤
      ghostCancelCount (L := L) (K := K) σ idx C' := by
  classical
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hcard : 2 ≤ C.card
  · rw [dif_pos hcard] at hsupp
    unfold Protocol.stepDist at hsupp
    rw [PMF.support_map] at hsupp
    rcases hsupp with ⟨pr, _, hpr⟩
    rw [← hpr]
    exact ghostCancelCount_scheduledStep_mono
      (L := L) (K := K) σ idx C pr
  · rw [dif_neg hcard] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp
    subst C'
    exact le_rfl

theorem ghostCancelCount_transitionKernel_mono
    (σ : Sign) (idx : Fin (L + 1))
    (C C' : GhostConfig (L := L) (K := K))
    (hsupp : 0 < cancelGhostKernel (L := L) (K := K) σ idx C {C'}) :
    ghostCancelCount (L := L) (K := K) σ idx C ≤
      ghostCancelCount (L := L) (K := K) σ idx C' := by
  classical
  have hmem :
      C' ∈ ((cancelGhostProtocol (L := L) (K := K) σ idx).stepDistOrSelf C).support := by
    change 0 <
      ((cancelGhostProtocol (L := L) (K := K) σ idx).stepDistOrSelf C).toMeasure {C'} at hsupp
    rw [PMF.toMeasure_apply_singleton _ _
      (DiscreteMeasurableSpace.forall_measurableSet _)] at hsupp
    exact (PMF.mem_support_iff _ _).2 (ne_of_gt hsupp)
  exact ghostCancelCount_stepDistOrSelf_support_mono
    (L := L) (K := K) σ idx C C' hmem

theorem ghostCancelClock_transitionKernel_mono
    (σ : Sign) (idx : Fin (L + 1)) (D : ℕ)
    (C C' : GhostConfig (L := L) (K := K))
    (hsupp : 0 < cancelGhostKernel (L := L) (K := K) σ idx C {C'}) :
    ghostCancelClock (L := L) (K := K) σ idx D C ≤
      ghostCancelClock (L := L) (K := K) σ idx D C' := by
  unfold ghostCancelClock
  exact min_le_min
    (ghostCancelCount_transitionKernel_mono (L := L) (K := K) σ idx C C' hsupp)
    le_rfl

/-! ## Split-birth correction and row readout -/

/-- Named H16 split-birth correction budget.  Split-born same-exponent agents
enter the real row unmarked, so their cumulative contribution is charged to the
mass-above/phi budget supplied by H15. -/
structure SplitBirthCorrectionBudget
    (D : Phase3Core.Phase3ModeDomain L) (h correction : ℕ) where
  cumulativeSplitBirths : ℕ
  massAboveCharge : ℕ
  correction_le_cumulative : correction ≤ cumulativeSplitBirths
  cumulative_le_massAboveCharge : cumulativeSplitBirths ≤ massAboveCharge
  massAboveCharge_bound :
    (massAboveCharge : ℝ) ≤ (1 / 1000 : ℝ) * (D.M : ℝ)

theorem correction_le_massAbove_budget
    (D : Phase3Core.Phase3ModeDomain L) (h correction : ℕ)
    (B : SplitBirthCorrectionBudget (L := L) D h correction) :
    (correction : ℝ) ≤ (1 / 1000 : ℝ) * (D.M : ℝ) := by
  have hnat : correction ≤ B.massAboveCharge :=
    B.correction_le_cumulative.trans B.cumulative_le_massAboveCharge
  have hreal : (correction : ℝ) ≤ (B.massAboveCharge : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans B.massAboveCharge_bound

/-- Readout with a split-birth correction.  The row target `Drow` must buy the
ordinary `d*M` cancellations plus half of the charged split-birth units; this is
the deterministic absorption used by the marked row. -/
theorem totalMass_readout_of_cancel_drop_with_correction
    (mu : Ω → ℝ) (C : Ω → ℕ) (Drow h : ℕ)
    (startCoeff d rho M : ℝ) (correction : ℕ)
    (hM : 0 ≤ M)
    (hDmass_corr : d * M + (correction : ℝ) / 2 ≤ (Drow : ℝ))
    (hcoeff : startCoeff - 2 * d ≤ rho)
    (hdrop :
      ∀ x,
        mu x ≤ startCoeff * M * (2 : ℝ) ^ (-(h : ℤ)) -
          2 * (C x : ℝ) * (2 : ℝ) ^ (-(h : ℤ)) +
            (correction : ℝ) * (2 : ℝ) ^ (-(h : ℤ))) :
    ∀ x, Drow ≤ C x →
      mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ)) := by
  intro x hDle
  let scale : ℝ := (2 : ℝ) ^ (-(h : ℤ))
  have hscale : 0 ≤ scale := by
    unfold scale
    positivity
  have hprod : 0 ≤ M * scale := mul_nonneg hM hscale
  have hcoeff_scaled :
      (startCoeff - 2 * d) * M * scale ≤ rho * M * scale := by
    have h := mul_le_mul_of_nonneg_right hcoeff hprod
    simpa [mul_assoc] using h
  have hDleR : (Drow : ℝ) ≤ C x := by
    exact_mod_cast hDle
  have hbudgetC :
      d * M + (correction : ℝ) / 2 ≤ (C x : ℝ) :=
    hDmass_corr.trans hDleR
  have hcancel :
      2 * (d * M) * scale ≤
        2 * (C x : ℝ) * scale - (correction : ℝ) * scale := by
    have htwice :
        2 * (d * M) + (correction : ℝ) ≤ 2 * (C x : ℝ) := by
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_right htwice hscale
    nlinarith
  have htarget :
      startCoeff * M * scale - 2 * (C x : ℝ) * scale +
          (correction : ℝ) * scale
        ≤ (startCoeff - 2 * d) * M * scale := by
    calc
      startCoeff * M * scale - 2 * (C x : ℝ) * scale +
          (correction : ℝ) * scale
          ≤ startCoeff * M * scale - 2 * (d * M) * scale := by
            linarith
      _ = (startCoeff - 2 * d) * M * scale := by ring
  exact (hdrop x).trans (htarget.trans hcoeff_scaled)

section PerRowCorrection

variable [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
variable [DiscreteMeasurableSpace (ℕ × Ω)]

/-- Protocol-free per-row total-mass tail with the split-birth correction
absorbed into the row cancellation target. -/
theorem perRow_totalMassBad_tail_of_cancel_drop_with_correction
    (K : Kernel Ω Ω) [IsMarkovKernel K]
    (mu : Ω → ℝ) (C A B : Ω → ℕ)
    (A0 B0 n Drow T h : ℕ) (prevRho d rho M : ℝ)
    (correction : ℕ) (x0 : Ω)
    (hC0 : C x0 = 0)
    (hn : 2 ≤ n) (hD : Drow < B0) (hBA : B0 ≤ A0)
    (hqle :
      ∀ i : Fin Drow, CancelClockConcentration.twoSidedQ A0 B0 n Drow i ≤ 1)
    (hstep :
      ∀ x, C x < Drow → ∀ᵐ y ∂(K x), C y = C x ∨ C y = C x + 1)
    (hAfloor :
      ∀ x (_ : C x < Drow), ((A0 - C x : ℕ) : ℝ) ≤ A x)
    (hBfloor :
      ∀ x (_ : C x < Drow), ((B0 - C x : ℕ) : ℝ) ≤ B x)
    (hpair : ∀ x (_ : C x < Drow),
      (2 * (A x : ℝ) * (B x : ℝ)) / ((n : ℝ) * (n - 1 : ℕ))
        ≤ (K x).real {y | C y = C x + 1})
    (hT :
      CancelClockConcentration.integratedInvRateClock Drow
        (CancelClockConcentration.twoSidedQ A0 B0 n Drow) Drow ≤ (T : ℝ))
    (hM : 0 ≤ M)
    (hDmass_corr : d * M + (correction : ℝ) / 2 ≤ (Drow : ℝ))
    (hcoeff : 2 * prevRho - 2 * d ≤ rho)
    (hdrop :
      ∀ x,
        mu x ≤ (2 * prevRho) * M * (2 : ℝ) ^ (-(h : ℤ)) -
          2 * (C x : ℝ) * (2 : ℝ) ^ (-(h : ℤ)) +
            (correction : ℝ) * (2 : ℝ) ^ (-(h : ℤ))) :
    (CancelClockConcentration.stoppedKernel K C Drow ^ T) x0
        (Lemma616TotalMass.totalMassBad mu h rho M)
      ≤ ENNReal.ofReal (Real.exp
          (-(((T : ℝ) -
              CancelClockConcentration.integratedInvRateClock Drow
                (CancelClockConcentration.twoSidedQ A0 B0 n Drow) Drow) ^ 2)
            / (2 * (T : ℝ) *
                (CancelClockConcentration.invRateSlack Drow
                  (CancelClockConcentration.twoSidedQ A0 B0 n Drow)) ^ 2))) := by
  have hreadout :
      ∀ x, Drow ≤ C x →
        mu x ≤ rho * M * (2 : ℝ) ^ (-(h : ℤ)) :=
    totalMass_readout_of_cancel_drop_with_correction
      (mu := mu) (C := C) (Drow := Drow) (h := h)
      (startCoeff := 2 * prevRho) (d := d) (rho := rho)
      (M := M) (correction := correction)
      hM hDmass_corr hcoeff hdrop
  exact Lemma616TotalMass.perRow_totalMassBad_tail
    (K := K) (mu := mu) (C := C) (A := A) (B := B)
    (A0 := A0) (B0 := B0) (n := n) (D := Drow) (T := T)
    (h := h) (rho := rho) (M := M) (x0 := x0)
    hC0 hn hD hBA hqle hstep hAfloor hBfloor hpair hT hreadout

end PerRowCorrection

/-! ## Rho table binding for the final six rows -/

/-- The H16 table binding between the mode-domain `D.rho` and the landed
Lemma-6.16 constants. -/
structure RhoTable (D : Phase3Core.Phase3ModeDomain L) : Prop where
  rho_early : ∀ h, Phase3Core.Early (L := L) D h →
    D.rho h = Lemma616TotalMass.Constants.rho_early
  rho_lm5 : D.rho (D.ell - 5) = Lemma616TotalMass.Constants.rho_lm5
  rho_lm4 : D.rho (D.ell - 4) = Lemma616TotalMass.Constants.rho_lm4
  rho_lm3 : D.rho (D.ell - 3) = Lemma616TotalMass.Constants.rho_lm3
  rho_lm2 : D.rho (D.ell - 2) = Lemma616TotalMass.Constants.rho_lm2
  rho_lm1 : D.rho (D.ell - 1) = Lemma616TotalMass.Constants.rho_lm1
  rho_l : D.rho D.ell = Lemma616TotalMass.Constants.rho_l

namespace RhoTable

theorem row_lm5_closes {D : Phase3Core.Phase3ModeDomain L}
    (R : RhoTable (L := L) D) :
    2 * Lemma616TotalMass.Constants.rho_early -
        2 * Lemma616TotalMass.Constants.d_lm5 =
      D.rho (D.ell - 5) := by
  rw [R.rho_lm5, Lemma616TotalMass.Constants.row_lm5_table_closes]

theorem row_lm4_closes {D : Phase3Core.Phase3ModeDomain L}
    (R : RhoTable (L := L) D) :
    2 * D.rho (D.ell - 5) -
        2 * Lemma616TotalMass.Constants.d_lm4 =
      D.rho (D.ell - 4) := by
  rw [R.rho_lm5, R.rho_lm4,
    Lemma616TotalMass.Constants.row_lm4_table_closes]

theorem row_lm3_closes {D : Phase3Core.Phase3ModeDomain L}
    (R : RhoTable (L := L) D) :
    2 * D.rho (D.ell - 4) -
        2 * Lemma616TotalMass.Constants.d_lm3 =
      D.rho (D.ell - 3) := by
  rw [R.rho_lm4, R.rho_lm3,
    Lemma616TotalMass.Constants.row_lm3_table_closes]

theorem row_lm2_closes {D : Phase3Core.Phase3ModeDomain L}
    (R : RhoTable (L := L) D) :
    2 * D.rho (D.ell - 3) -
        2 * Lemma616TotalMass.Constants.d_lm2 =
      D.rho (D.ell - 2) := by
  rw [R.rho_lm3, R.rho_lm2,
    Lemma616TotalMass.Constants.row_lm2_table_closes]

theorem row_lm1_closes {D : Phase3Core.Phase3ModeDomain L}
    (R : RhoTable (L := L) D) :
    2 * D.rho (D.ell - 2) -
        2 * Lemma616TotalMass.Constants.d_lm1 =
      D.rho (D.ell - 1) := by
  rw [R.rho_lm2, R.rho_lm1,
    Lemma616TotalMass.Constants.row_lm1_table_closes]

theorem row_l_closes {D : Phase3Core.Phase3ModeDomain L}
    (R : RhoTable (L := L) D) :
    2 * D.rho (D.ell - 1) -
        2 * Lemma616TotalMass.Constants.d_l =
      D.rho D.ell := by
  rw [R.rho_lm1, R.rho_l,
    Lemma616TotalMass.Constants.row_l_table_closes]

end RhoTable

/-! ## Marked row runs and H16 engine packaging -/

/-- A stopped ghost row tail plus its projection back to the real H16 killed
hour gate.  The `σ` field keeps the orientation explicit. -/
structure MarkedCancelRowRun
    (D : Phase3Core.Phase3ModeDomain L) (h t : ℕ)
    (realGate : Set (Phase3Core.Omega L K))
    (c₀ : Phase3Core.Omega L K)
    (Row : Set (Phase3Core.Omega L K)) (ε : ℝ≥0∞) where
  σ : Sign
  idx : Fin (L + 1)
  target : ℕ
  C₀ : GhostConfig (L := L) (K := K)
  forget_C₀ : forgetGhost (L := L) (K := K) C₀ = c₀
  Q : Kernel (GhostConfig (L := L) (K := K))
        (GhostConfig (L := L) (K := K))
  G : Set (GhostConfig (L := L) (K := K))
  epsCounter : ℝ≥0∞
  epsSplitBirth : ℝ≥0∞
  counter_tail :
    (CancelClockConcentration.stoppedKernel
        (GatedDrift.killK_now Q G)
        (liftGhostCancelClock (L := L) (K := K) σ idx target) target ^ t)
        (some C₀)
        (Phase3Core.killedBad
          (fun C =>
            Row (forgetGhost (L := L) (K := K) C))) ≤ epsCounter
  projection_le :
    (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) realGate ^ t) (some c₀)
        (Phase3Core.killedBad Row)
      ≤
        (CancelClockConcentration.stoppedKernel
          (GatedDrift.killK_now Q G)
          (liftGhostCancelClock (L := L) (K := K) σ idx target) target ^ t)
          (some C₀)
          (Phase3Core.killedBad
            (fun C =>
              Row (forgetGhost (L := L) (K := K) C))) +
        epsSplitBirth
  eps_budget : epsCounter + epsSplitBirth ≤ ε

theorem stoppedTail_of_markedCancelRowRun
    (D : Phase3Core.Phase3ModeDomain L) (h t : ℕ)
    (realGate : Set (Phase3Core.Omega L K))
    (c₀ : Phase3Core.Omega L K)
    (Row : Set (Phase3Core.Omega L K)) (ε : ℝ≥0∞)
    (R : MarkedCancelRowRun (L := L) (K := K) D h t realGate c₀ Row ε) :
    Phase3Core.stoppedTail (L := L) (K := K) realGate t c₀ Row ε := by
  unfold Phase3Core.stoppedTail
  calc
    (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) realGate ^ t) (some c₀)
        (Phase3Core.killedBad Row)
        ≤
        (CancelClockConcentration.stoppedKernel
          (GatedDrift.killK_now R.Q R.G)
          (liftGhostCancelClock (L := L) (K := K) R.σ R.idx R.target) R.target ^ t)
          (some R.C₀)
          (Phase3Core.killedBad
            (fun C =>
              Row (forgetGhost (L := L) (K := K) C))) +
        R.epsSplitBirth := R.projection_le
    _ ≤ R.epsCounter + R.epsSplitBirth :=
        add_le_add R.counter_tail le_rfl
    _ ≤ ε := R.eps_budget

/-- Hour-local H16 data whose six rows are produced by marked cancellation
runs rather than naked stopped-tail assumptions. -/
structure H16MarkedCancelData {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  rhoTable : RhoTable (L := L) D
  Row0 : ℕ → Set (Phase3Core.Omega L K)
  Row1 : ℕ → Set (Phase3Core.Omega L K)
  Row2 : ℕ → Set (Phase3Core.Omega L K)
  Row3 : ℕ → Set (Phase3Core.Omega L K)
  Row4 : ℕ → Set (Phase3Core.Omega L K)
  Row5 : ℕ → Set (Phase3Core.Omega L K)
  eps0 : ℕ → ℝ≥0∞
  eps1 : ℕ → ℝ≥0∞
  eps2 : ℕ → ℝ≥0∞
  eps3 : ℕ → ℝ≥0∞
  eps4 : ℕ → ℝ≥0∞
  eps5 : ℕ → ℝ≥0∞
  cover : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ c, ¬ Phase3Core.TotalMassBound (L := L) (K := K) D h c →
      Lemma617Minority.sixUnion (Row0 h) (Row1 h) (Row2 h)
        (Row3 h) (Row4 h) (Row5 h) c
  eps_budget : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Lemma617Minority.sixSum
      (eps0 h) (eps1 h) (eps2 h) (eps3 h) (eps4 h) (eps5 h) ≤
        T.surface.eps16 h
  row0Run : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      MarkedCancelRowRun (L := L) (K := K) D h dt (T.surface.hourGate h)
        cPhi (Row0 h) (eps0 h)
  row1Run : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      MarkedCancelRowRun (L := L) (K := K) D h dt (T.surface.hourGate h)
        cPhi (Row1 h) (eps1 h)
  row2Run : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      MarkedCancelRowRun (L := L) (K := K) D h dt (T.surface.hourGate h)
        cPhi (Row2 h) (eps2 h)
  row3Run : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      MarkedCancelRowRun (L := L) (K := K) D h dt (T.surface.hourGate h)
        cPhi (Row3 h) (eps3 h)
  row4Run : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      MarkedCancelRowRun (L := L) (K := K) D h dt (T.surface.hourGate h)
        cPhi (Row4 h) (eps4 h)
  row5Run : ∀ h, h ≤ D.lastCoreHour → 0 < h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3Core.H15 (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cPhi, cPhi ∈ T.surface.checkpoint .afterPhi h →
    ∀ dt,
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) ≤ dt →
      dt ≤
          Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
            Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) →
      MarkedCancelRowRun (L := L) (K := K) D h dt (T.surface.hourGate h)
        cPhi (Row5 h) (eps5 h)

namespace H16MarkedCancelData

/-- Package marked H16 row runs into the existing `H16Engine`. -/
noncomputable def toH16Engine {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (E : H16MarkedCancelData (L := L) (K := K) D T) :
    Phase3Engines.H16Engine (L := L) (K := K) D T where
  Row0 := E.Row0
  Row1 := E.Row1
  Row2 := E.Row2
  Row3 := E.Row3
  Row4 := E.Row4
  Row5 := E.Row5
  eps0 := E.eps0
  eps1 := E.eps1
  eps2 := E.eps2
  eps3 := E.eps3
  eps4 := E.eps4
  eps5 := E.eps5
  cover := E.cover
  eps_budget := E.eps_budget
  tail0 := by
    intro h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi
    exact stoppedTail_of_markedCancelRowRun (L := L) (K := K) D h dt
      (T.surface.hourGate h) cPhi (E.Row0 h) (E.eps0 h)
      (E.row0Run h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
  tail1 := by
    intro h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi
    exact stoppedTail_of_markedCancelRowRun (L := L) (K := K) D h dt
      (T.surface.hourGate h) cPhi (E.Row1 h) (E.eps1 h)
      (E.row1Run h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
  tail2 := by
    intro h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi
    exact stoppedTail_of_markedCancelRowRun (L := L) (K := K) D h dt
      (T.surface.hourGate h) cPhi (E.Row2 h) (E.eps2 h)
      (E.row2Run h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
  tail3 := by
    intro h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi
    exact stoppedTail_of_markedCancelRowRun (L := L) (K := K) D h dt
      (T.surface.hourGate h) cPhi (E.Row3 h) (E.eps3 h)
      (E.row3Run h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
  tail4 := by
    intro h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi
    exact stoppedTail_of_markedCancelRowRun (L := L) (K := K) D h dt
      (T.surface.hourGate h) cPhi (E.Row4 h) (E.eps4 h)
      (E.row4Run h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)
  tail5 := by
    intro h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi
    exact stoppedTail_of_markedCancelRowRun (L := L) (K := K) D h dt
      (T.surface.hourGate h) cPhi (E.Row5 h) (E.eps5 h)
      (E.row5Run h hle hpos prev h15 I cPhi hcPhi dt hdtlo hdthi)

/-- Direct H16 producer obtained from marked cancellation rows. -/
noncomputable def mkH16 {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (E : H16MarkedCancelData (L := L) (K := K) D T) :
    ∀ h, h ≤ D.lastCoreHour → 0 < h →
      Phase3Core.PrevCore (L := L) (K := K) D T h →
      Phase3Core.H15 (L := L) (K := K) D T h →
      Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
      Phase3Core.H16 (L := L) (K := K) D T h :=
  E.toH16Engine.mkH16

end H16MarkedCancelData

#print axioms ghostCancelCount_transitionKernel_mono
#print axioms ghostCancelClock_transitionKernel_mono
#print axioms correction_le_massAbove_budget
#print axioms totalMass_readout_of_cancel_drop_with_correction
#print axioms perRow_totalMassBad_tail_of_cancel_drop_with_correction
#print axioms RhoTable.row_lm5_closes
#print axioms RhoTable.row_lm4_closes
#print axioms RhoTable.row_lm3_closes
#print axioms RhoTable.row_lm2_closes
#print axioms RhoTable.row_lm1_closes
#print axioms RhoTable.row_l_closes
#print axioms stoppedTail_of_markedCancelRowRun
#print axioms H16MarkedCancelData.toH16Engine
#print axioms H16MarkedCancelData.mkH16

end Lemma616MarkedCancelMass

end ExactMajority
