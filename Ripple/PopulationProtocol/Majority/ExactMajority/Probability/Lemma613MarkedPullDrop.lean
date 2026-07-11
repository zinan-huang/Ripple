import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Bridges
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ZeroSupplyCoupling
import Mathlib.Tactic

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Real

namespace Lemma613MarkedPullDrop

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-!
Marked/ghost lift for the Lemma-6.13 H13 pull.

The raw current counter of lagging zero Mains is not a monotone counter: a
Phase-3 cancel at a lower exponent can create fresh zero Mains below the current
hour.  The engine below therefore runs Doty's monotone Lemma-4.7 pull on a
tracked start cohort and exposes the cancel-birth accounting as an explicit
readout ledger.
-/

/-- Ghost lift for one H13 pull window.

`cohort` marks the original start-window O cohort.  `active` is the mutable
"still charged to the monotone pull" bit: an unreached cohort agent that stops
being a zero Main is retired from the monotone B counter and is paid for by the
correction ledger.  This extra bit is necessary because a split cohort agent can
later cancel back to zero below `h`; if immutable cohort membership alone were
used, that cancel-birth would re-enter B and monotonicity would again be false. -/
structure OReachGhost where
  st : AgentState L K
  cohort : Bool
  active : Bool
  reached : Bool
  deriving DecidableEq, Fintype

abbrev GhostConfig := Config (OReachGhost (L := L) (K := K))

local instance instOptionMSGhost :
    MeasurableSpace (Option (GhostConfig (L := L) (K := K))) := ⊤

local instance instOptionDMSGhost :
    DiscreteMeasurableSpace (Option (GhostConfig (L := L) (K := K))) :=
  ⟨fun _ => trivial⟩

/-- Forget the ghost marks. -/
def forgetGhost (C : GhostConfig (L := L) (K := K)) : Config (AgentState L K) :=
  C.map OReachGhost.st

/-- Monotone B population: tracked start-cohort zero Mains not yet marked as
having reached hour `h`.  Cancel-born zeros are not in the tracked cohort; their
effect is paid by the correction ledger. -/
def ghostUnpulledO (_h : ℕ) (C : GhostConfig (L := L) (K := K)) : ℕ :=
  Multiset.countP
    (fun a : OReachGhost (L := L) (K := K) =>
      a.cohort = true ∧ a.active = true ∧ a.reached = false ∧
        a.st.role = Role.main ∧ a.st.bias = Bias.zero)
    C

/-- Tracked cohort agents already marked as pulled to hour `h`. -/
def ghostReachedO (_h : ℕ) (C : GhostConfig (L := L) (K := K)) : ℕ :=
  Multiset.countP
    (fun a : OReachGhost (L := L) (K := K) =>
      a.cohort = true ∧ a.reached = true)
    C

/-- Current real `O_h` fuel count. -/
def currentOFuel (h : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Lemma615MassAbove.phase3OFuelCount (L := L) (K := K) h c

def ghostZeroMain (a : OReachGhost (L := L) (K := K)) : Prop :=
  a.st.role = Role.main ∧ a.st.bias = Bias.zero

def ghostUnpulledAgent (_h : ℕ) (a : OReachGhost (L := L) (K := K)) : Prop :=
  a.cohort = true ∧ a.active = true ∧ a.reached = false ∧
    ghostZeroMain (L := L) (K := K) a

theorem ghostUnpulledO_eq_countP (h : ℕ) (C : GhostConfig (L := L) (K := K)) :
    ghostUnpulledO (L := L) (K := K) h C =
      Multiset.countP (ghostUnpulledAgent (L := L) (K := K) h) C := by
  simp [ghostUnpulledO, ghostUnpulledAgent, ghostZeroMain]

def ghostReachedNow (h : ℕ) (out : AgentState L K) : Prop :=
  out.role = Role.main ∧ out.bias = Bias.zero ∧ h ≤ out.hour.val

/-- Positional ghost update for one output of the real transition.  The reached bit
is set once.  An unreached active cohort agent remains active only while it is
still a zero Main and has not just reached `h`; otherwise it is retired and must
be paid by the correction ledger. -/
noncomputable def advanceGhost (h : ℕ) (old : OReachGhost (L := L) (K := K))
    (out : AgentState L K) : OReachGhost (L := L) (K := K) :=
  let trackable :=
    old.cohort && old.active && !old.reached &&
      decide (ghostZeroMain (L := L) (K := K) old)
  let reached' :=
    old.reached || (trackable && decide (ghostReachedNow (L := L) (K := K) h out))
  let active' :=
    trackable && !reached' && decide (out.role = Role.main ∧ out.bias = Bias.zero)
  { st := out, cohort := old.cohort, active := active', reached := reached' }

noncomputable def ghostTransition (h : ℕ)
    (a b : OReachGhost (L := L) (K := K)) :
    OReachGhost (L := L) (K := K) × OReachGhost (L := L) (K := K) :=
  let out := Transition L K a.st b.st
  (advanceGhost (L := L) (K := K) h a out.1,
   advanceGhost (L := L) (K := K) h b out.2)

noncomputable def ghostProtocol (h : ℕ) :
    Protocol (OReachGhost (L := L) (K := K)) where
  δ := ghostTransition (L := L) (K := K) h

noncomputable abbrev ghostKernel (h : ℕ) :
    Kernel (GhostConfig (L := L) (K := K))
      (GhostConfig (L := L) (K := K)) :=
  (ghostProtocol (L := L) (K := K) h).transitionKernel

@[simp] theorem advanceGhost_st (h : ℕ) (old : OReachGhost (L := L) (K := K))
    (out : AgentState L K) :
    (advanceGhost (L := L) (K := K) h old out).st = out := rfl

theorem forgetGhost_ghostTransition (h : ℕ)
    (a b : OReachGhost (L := L) (K := K)) :
    ((ghostTransition (L := L) (K := K) h a b).1.st,
        (ghostTransition (L := L) (K := K) h a b).2.st) =
      Transition L K a.st b.st := by
  rfl

theorem ghostUnpulledAgent_advance_imp
    (h : ℕ) (old : OReachGhost (L := L) (K := K)) (out : AgentState L K)
    (hnew :
      ghostUnpulledAgent (L := L) (K := K) h
        (advanceGhost (L := L) (K := K) h old out)) :
    ghostUnpulledAgent (L := L) (K := K) h old := by
  simp [ghostUnpulledAgent, ghostZeroMain, advanceGhost] at hnew ⊢
  rcases hnew with ⟨hcohort, hactive, hreached, hrole, hbias⟩
  rcases hactive with ⟨⟨⟨hcohortOld, hactiveOld⟩, hnotReachedOld⟩, hzeroOld⟩
  exact ⟨hcohortOld.1.1, hcohortOld.1.2, hcohortOld.2,
    hactiveOld.1, hactiveOld.2⟩

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

/-! ## Below-front cancel-birth accounting -/

/-- Biased Main agents at exponent indices strictly below the H13 front `h`.

This is the count side of the birth-correction budget: a below-`h` Rule-3
cancel can only be charged to biased Main inputs from this predicate. -/
def belowHBiasedMain (h : ℕ) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ∃ (sgn : Sign) (i : Fin (L + 1)),
    a.bias = Bias.dyadic sgn i ∧ i.val < h

instance (h : ℕ) (a : AgentState L K) :
    Decidable (belowHBiasedMain (L := L) (K := K) h a) := by
  unfold belowHBiasedMain
  infer_instance

/-- The exact below-front cancel-birth event for a scheduled Main/Main pair. -/
def belowHCancelBirthPair (h : ℕ) (s t : AgentState L K) : Prop :=
  s.role = Role.main ∧ t.role = Role.main ∧
    ((∃ i : Fin (L + 1),
        s.bias = Bias.dyadic Sign.pos i ∧
          t.bias = Bias.dyadic Sign.neg i ∧ i.val < h) ∨
      (∃ i : Fin (L + 1),
        s.bias = Bias.dyadic Sign.neg i ∧
          t.bias = Bias.dyadic Sign.pos i ∧ i.val < h))

instance (h : ℕ) (s t : AgentState L K) :
    Decidable (belowHCancelBirthPair (L := L) (K := K) h s t) := by
  unfold belowHCancelBirthPair
  infer_instance

/-- Exact per-pair indicator for below-`h` cancel births in the Phase-3 Main/Main
cancel-split helper.  The value is `2` precisely when the scheduled pair is a
Main/Main opposite-sign same-exponent cancel whose cancel level is `< h`, since
that firing emits two zero-bias Main agents stamped with that below-front hour. -/
def belowHCancelBirthInd (h : ℕ) (s t : AgentState L K) : ℕ :=
  if belowHCancelBirthPair (L := L) (K := K) h s t then 2 else 0

/-- The exact below-front birth indicator is paid by the two biased Main inputs
it consumes.  The window-cumulative version sums this inequality along the
scheduled path; the remaining probabilistic content is the named H13 budget
below. -/
theorem belowHCancelBirthInd_le_belowHBiasedPair
    (h : ℕ) (s t : AgentState L K) :
    belowHCancelBirthInd (L := L) (K := K) h s t ≤
      Multiset.countP (belowHBiasedMain (L := L) (K := K) h)
        ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_pair_ite]
  unfold belowHCancelBirthInd
  by_cases hbirth : belowHCancelBirthPair (L := L) (K := K) h s t
  · rw [if_pos hbirth]
    rcases hbirth with ⟨hsRole, htRole, hcase | hcase⟩
    · rcases hcase with ⟨i, hsBias, htBias, hi⟩
      have hsBelow : belowHBiasedMain (L := L) (K := K) h s :=
        ⟨hsRole, Sign.pos, i, hsBias, hi⟩
      have htBelow : belowHBiasedMain (L := L) (K := K) h t :=
        ⟨htRole, Sign.neg, i, htBias, hi⟩
      simp [hsBelow, htBelow]
    · rcases hcase with ⟨i, hsBias, htBias, hi⟩
      have hsBelow : belowHBiasedMain (L := L) (K := K) h s :=
        ⟨hsRole, Sign.neg, i, hsBias, hi⟩
      have htBelow : belowHBiasedMain (L := L) (K := K) h t :=
        ⟨htRole, Sign.pos, i, htBias, hi⟩
      simp [hsBelow, htBelow]
  · rw [if_neg hbirth]
    omega

theorem ghostUnpulled_pair_update_le
    (h : ℕ) (a b : OReachGhost (L := L) (K := K)) :
    Multiset.countP (ghostUnpulledAgent (L := L) (K := K) h)
        ({(ghostTransition (L := L) (K := K) h a b).1,
          (ghostTransition (L := L) (K := K) h a b).2}
          : Multiset (OReachGhost (L := L) (K := K)))
      ≤
    Multiset.countP (ghostUnpulledAgent (L := L) (K := K) h)
        ({a, b} : Multiset (OReachGhost (L := L) (K := K))) := by
  classical
  rw [countP_pair_ite, countP_pair_ite]
  have haLe :
      (if ghostUnpulledAgent (L := L) (K := K) h
            (ghostTransition (L := L) (K := K) h a b).1 then 1 else 0)
        ≤ (if ghostUnpulledAgent (L := L) (K := K) h a then 1 else 0) := by
    by_cases haNew :
      ghostUnpulledAgent (L := L) (K := K) h
        (ghostTransition (L := L) (K := K) h a b).1
    · have haOld : ghostUnpulledAgent (L := L) (K := K) h a := by
        simpa [ghostTransition] using
          ghostUnpulledAgent_advance_imp (L := L) (K := K) h a
            (Transition L K a.st b.st).1 haNew
      simp [haNew, haOld]
    · simp [haNew]
  have hbLe :
      (if ghostUnpulledAgent (L := L) (K := K) h
            (ghostTransition (L := L) (K := K) h a b).2 then 1 else 0)
        ≤ (if ghostUnpulledAgent (L := L) (K := K) h b then 1 else 0) := by
    by_cases hbNew :
        ghostUnpulledAgent (L := L) (K := K) h
          (ghostTransition (L := L) (K := K) h a b).2
    · have hbOld : ghostUnpulledAgent (L := L) (K := K) h b := by
        simpa [ghostTransition] using
          ghostUnpulledAgent_advance_imp (L := L) (K := K) h b
            (Transition L K a.st b.st).2 hbNew
      simp [hbNew, hbOld]
    · simp [hbNew]
  exact Nat.add_le_add haLe hbLe

theorem ghostUnpulled_scheduledStep_le
    (h : ℕ) (C : GhostConfig (L := L) (K := K))
    (pr : OReachGhost (L := L) (K := K) × OReachGhost (L := L) (K := K)) :
    ghostUnpulledO (L := L) (K := K) h
        (Protocol.scheduledStep (ghostProtocol (L := L) (K := K) h) C pr)
      ≤ ghostUnpulledO (L := L) (K := K) h C := by
  classical
  unfold Protocol.scheduledStep Protocol.stepOrSelf
  by_cases happ : Protocol.Applicable C pr.1 pr.2
  · rw [if_pos happ]
    obtain ⟨rest, hrest⟩ : ∃ rest, C = rest + ({pr.1, pr.2}
        : Multiset (OReachGhost (L := L) (K := K))) :=
      ⟨C - {pr.1, pr.2}, (tsub_add_cancel_of_le happ).symm⟩
    rw [hrest, add_tsub_cancel_right]
    dsimp [ghostProtocol]
    repeat rw [ghostUnpulledO_eq_countP]
    rw [Multiset.countP_add, Multiset.countP_add]
    exact Nat.add_le_add_left
      (ghostUnpulled_pair_update_le (L := L) (K := K) h pr.1 pr.2) _
  · rw [if_neg happ]

theorem ghostUnpulled_stepDistOrSelf_support_mono
    (h : ℕ) (C C' : GhostConfig (L := L) (K := K))
    (hsupp : C' ∈ ((ghostProtocol (L := L) (K := K) h).stepDistOrSelf C).support) :
    ghostUnpulledO (L := L) (K := K) h C' ≤
      ghostUnpulledO (L := L) (K := K) h C := by
  classical
  unfold Protocol.stepDistOrSelf at hsupp
  by_cases hcard : 2 ≤ C.card
  · rw [dif_pos hcard] at hsupp
    unfold Protocol.stepDist at hsupp
    rw [PMF.support_map] at hsupp
    rcases hsupp with ⟨pr, _, hpr⟩
    rw [← hpr]
    exact ghostUnpulled_scheduledStep_le (L := L) (K := K) h C pr
  · rw [dif_neg hcard] at hsupp
    rw [PMF.mem_support_pure_iff] at hsupp
    subst C'
    exact le_rfl

theorem ghostUnpulled_transitionKernel_mono
    (h : ℕ) (C C' : GhostConfig (L := L) (K := K))
    (hsupp : 0 < ghostKernel (L := L) (K := K) h C {C'}) :
    ghostUnpulledO (L := L) (K := K) h C' ≤
      ghostUnpulledO (L := L) (K := K) h C := by
  classical
  have hmem :
      C' ∈ ((ghostProtocol (L := L) (K := K) h).stepDistOrSelf C).support := by
    change 0 < ((ghostProtocol (L := L) (K := K) h).stepDistOrSelf C).toMeasure {C'} at hsupp
    rw [PMF.toMeasure_apply_singleton _ _
      (DiscreteMeasurableSpace.forall_measurableSet _)] at hsupp
    exact (PMF.mem_support_iff _ _).2 (ne_of_gt hsupp)
  exact ghostUnpulled_stepDistOrSelf_support_mono (L := L) (K := K) h C C' hmem

/-- Lift a ghost counter to the cemetery state used by killed kernels. -/
def liftGhostCounter (B : GhostConfig (L := L) (K := K) → ℕ) :
    Option (GhostConfig (L := L) (K := K)) → ℕ
  | none => 0
  | some C => B C

/-- The explicit correction ledger for projecting marked reach back to current
reached Main count.

`revertCorrection = 0` is the Rule-2 max-fix consequence.  The remaining
birth term is the cumulative below-`h` cancel-birth count over the H13 window.
The only upstream probabilistic content kept here is the named b₂ budget below:
it is the precise 6.15/6.16 handoff that the cumulative below-front cancel
births consume at most `0.0276 |M|` biased-input units. -/
structure H13BelowCancelBirthBudget (D : Phase3Core.Phase3ModeDomain L)
    (h correction : ℕ) where
  /-- Window-cumulative below-`h` cancel births, in agent units. -/
  cumulativeBelowHCancelBirths : ℕ
  /-- The cumulative `ZeroSupplyCoupling.cancelInd` charge over the same window.
  This is in the same agent-unit convention as `cancelInd`, which returns `2`
  on a firing cancel pair. -/
  cumulativeCancelIndUnits : ℕ
  /-- Biased Main input units at exponent levels below the H13 front consumed by
  those cancellations.  The 6.15/6.16 leaves supply the numerical bound. -/
  biasedConsumedBelowH : ℕ
  correction_le_cumulative : correction ≤ cumulativeBelowHCancelBirths
  cumulative_le_cancelInd : cumulativeBelowHCancelBirths ≤ cumulativeCancelIndUnits
  cancelInd_le_biasedConsumed : cumulativeCancelIndUnits ≤ biasedConsumedBelowH
  biasedConsumed_bound_b2 :
    (biasedConsumedBelowH : ℝ) ≤ (276 / 10000 : ℝ) * (D.M : ℝ)

theorem correction_le_b2_of_belowCancelBirthBudget
    (D : Phase3Core.Phase3ModeDomain L) (h correction : ℕ)
    (B : H13BelowCancelBirthBudget (L := L) D h correction) :
    (correction : ℝ) ≤ (276 / 10000 : ℝ) * (D.M : ℝ) := by
  have hnat : correction ≤ B.biasedConsumedBelowH :=
    B.correction_le_cumulative.trans
      (B.cumulative_le_cancelInd.trans B.cancelInd_le_biasedConsumed)
  have hreal : (correction : ℝ) ≤ (B.biasedConsumedBelowH : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans B.biasedConsumed_bound_b2

/-- Raw ghost target before the b₂ birth correction is subtracted.  Doty's H13
pull reaches the stronger `0.9976 |M|` marked-reach floor; the birth budget
below spends at most `0.0276 |M|`, yielding the `0.97 |M|` intermediate floor
consumed by `Lemma613OFloor.ofuel_floor`. -/
def GhostRawMarkedTarget (D : Phase3Core.Phase3ModeDomain L)
    (h : ℕ) (C : GhostConfig (L := L) (K := K)) : Prop :=
  (9976 / 10000 : ℝ) * (D.M : ℝ) ≤
    (ghostReachedO (L := L) (K := K) h C : ℝ)

/-- Arithmetic absorption of the H13 birth budget into Doty's `b₂ = 0.0276m`
slack. -/
theorem marked_target_of_rawTarget_belowCancelBirthBudget
    (D : Phase3Core.Phase3ModeDomain L) (h correction : ℕ)
    (C : GhostConfig (L := L) (K := K))
    (hraw : GhostRawMarkedTarget (L := L) (K := K) D h C)
    (B : H13BelowCancelBirthBudget (L := L) D h correction) :
    (97 / 100 : ℝ) * (D.M : ℝ) + (correction : ℝ) ≤
      (ghostReachedO (L := L) (K := K) h C : ℝ) := by
  have hcorr := correction_le_b2_of_belowCancelBirthBudget
    (L := L) D h correction B
  unfold GhostRawMarkedTarget at hraw
  nlinarith [hcorr, hraw]

/-- Deterministic readout ledger for projecting marked reach back to the
current reached-Main count.  The raw marked target plus the named
`H13BelowCancelBirthBudget` derive the old `marked_target` field; it is no
longer a free residual assumption. -/
structure BirthCorrectionLedger (D : Phase3Core.Phase3ModeDomain L)
    (h : ℕ) (rho : ℝ) (C : GhostConfig (L := L) (K := K)) where
  correction : ℕ
  revertCorrection : ℕ
  cancelBirthCorrection : ℕ
  splitCorrection : ℕ
  cancelCount : ℕ
  biasedConsumed : ℕ
  correction_def :
    correction = revertCorrection + cancelBirthCorrection + splitCorrection
  revert_zero : revertCorrection = 0
  cancel_birth_le_cancel_count : cancelBirthCorrection ≤ cancelCount
  cancel_count_consumes_biased : 2 * cancelCount ≤ biasedConsumed
  split_zero : splitCorrection = 0
  raw_marked_target :
    GhostRawMarkedTarget (L := L) (K := K) D h C
  below_cancel_birth_budget :
    H13BelowCancelBirthBudget (L := L) D h cancelBirthCorrection
  marked_to_current :
    (ghostReachedO (L := L) (K := K) h C : ℝ) ≤
      (Lemma613OFloor.phase3ReachedMainCount (L := L) (K := K) h (forgetGhost C) : ℝ) +
        (correction : ℝ)
  biased_bound :
    Phase3Bridges.BiasedMainBound (L := L) (K := K) D rho (forgetGhost C)

theorem correction_le_b2_of_birthCorrectionLedger
    (D : Phase3Core.Phase3ModeDomain L) (h : ℕ) (rho : ℝ)
    (C : GhostConfig (L := L) (K := K))
    (R : BirthCorrectionLedger (L := L) (K := K) D h rho C) :
    (R.correction : ℝ) ≤ (276 / 10000 : ℝ) * (D.M : ℝ) := by
  have hbirth := correction_le_b2_of_belowCancelBirthBudget
    (L := L) D h R.cancelBirthCorrection R.below_cancel_birth_budget
  have hnat : R.correction = R.cancelBirthCorrection := by
    rw [R.correction_def, R.revert_zero, R.split_zero]
    omega
  rw [hnat]
  exact hbirth

theorem marked_target_of_birthCorrectionLedger
    (D : Phase3Core.Phase3ModeDomain L) (h : ℕ) (rho : ℝ)
    (C : GhostConfig (L := L) (K := K))
    (R : BirthCorrectionLedger (L := L) (K := K) D h rho C) :
    (97 / 100 : ℝ) * (D.M : ℝ) + (R.correction : ℝ) ≤
      (ghostReachedO (L := L) (K := K) h C : ℝ) := by
  have hcorr := correction_le_b2_of_birthCorrectionLedger
    (L := L) (K := K) D h rho C R
  have hraw := R.raw_marked_target
  unfold GhostRawMarkedTarget at hraw
  nlinarith [hcorr, hraw]

/-- The correction ledger first recovers the reached-Main intermediate floor. -/
theorem reachedMainFloor_of_birthCorrectionLedger
    (D : Phase3Core.Phase3ModeDomain L) (h : ℕ) (rho : ℝ)
    (C : GhostConfig (L := L) (K := K))
    (R : BirthCorrectionLedger (L := L) (K := K) D h rho C) :
    Phase3Bridges.ReachedMainFloor (L := L) (K := K) D h (forgetGhost C) := by
  unfold Phase3Bridges.ReachedMainFloor
  nlinarith [marked_target_of_birthCorrectionLedger
    (L := L) (K := K) D h rho C R, R.marked_to_current]

/-- Projection readout: marked reach plus the charged birth/split correction and
the biased-Main mass-to-count bound gives the current `O_h` fuel floor. -/
theorem ofuelFloor_of_birthCorrectionLedger
    (D : Phase3Core.Phase3ModeDomain L) (h : ℕ) (rho : ℝ)
    (C : GhostConfig (L := L) (K := K))
    (hcoef : D.tau h ≤ 97 / 100 - 2 * rho)
    (R : BirthCorrectionLedger (L := L) (K := K) D h rho C) :
    Phase3Core.OFuelFloor (L := L) (K := K) D h (forgetGhost C) := by
  exact Phase3Bridges.ofuelFloor_of_reached_biased
    (L := L) (K := K) D h rho (forgetGhost C) hcoef
    (reachedMainFloor_of_birthCorrectionLedger
      (L := L) (K := K) D h rho C R)
    R.biased_bound

def BirthCorrectedGhostGood (D : Phase3Core.Phase3ModeDomain L)
    (h : ℕ) (rho : ℝ) (C : GhostConfig (L := L) (K := K)) : Prop :=
  Nonempty (BirthCorrectionLedger (L := L) (K := K) D h rho C)

theorem ofuelFloor_of_birthCorrectedGhostGood
    (D : Phase3Core.Phase3ModeDomain L) (h : ℕ) (rho : ℝ)
    (C : GhostConfig (L := L) (K := K))
    (hcoef : D.tau h ≤ 97 / 100 - 2 * rho)
    (hgood : BirthCorrectedGhostGood (L := L) (K := K) D h rho C) :
    Phase3Core.OFuelFloor (L := L) (K := K) D h (forgetGhost C) := by
  rcases hgood with ⟨R⟩
  exact ofuelFloor_of_birthCorrectionLedger (L := L) (K := K) D h rho C hcoef R

/-- Ghost transition obligations needed to instantiate the existing catalytic
pull milestone.  The monotonicity obligation is now on the marked start cohort,
not on the raw current lagging-O population. -/
structure MarkedPullStepObligations
    (h bHi bLo n a₀ : ℕ)
    (Q : Kernel (GhostConfig (L := L) (K := K))
        (GhostConfig (L := L) (K := K))) : Prop where
  hB_hi : ∀ C, ghostUnpulledO (L := L) (K := K) h C ≤ bHi
  hB_mono : ∀ C C', 0 < Q C {C'} →
    ghostUnpulledO (L := L) (K := K) h C' ≤
      ghostUnpulledO (L := L) (K := K) h C
  hprogress : ∀ (i : Fin (bHi - bLo)) C,
    ghostUnpulledO (L := L) (K := K) h C = bHi - i.val →
      Q C {C' | ghostUnpulledO (L := L) (K := K) h C' <
        ghostUnpulledO (L := L) (K := K) h C} ≥
        ENNReal.ofReal
          (Phase3Bridges.CatalyticPull.catalyticPullRate n a₀ (bHi - i.val))

/-- Instantiate the repo catalytic-pull milestone on the marked ghost chain. -/
noncomputable def ghostPullMilestone
    {h bHi bLo n a₀ : ℕ}
    {Q : Kernel (GhostConfig (L := L) (K := K))
        (GhostConfig (L := L) (K := K))}
    (hlo : bLo < bHi) (hn : 2 ≤ n) (ha₀ : 1 ≤ a₀)
    (hbHi_le_n : bHi ≤ n) (h2a₀ : 2 * a₀ ≤ n - 1)
    (O : MarkedPullStepObligations (L := L) (K := K) h bHi bLo n a₀ Q) :
    RoleSplitConcentration.KernelMilestone Q :=
  Phase3Bridges.CatalyticPull.catalyticPullKernelMilestone
    (Q := Q) (B := ghostUnpulledO (L := L) (K := K) h)
    (bHi := bHi) (bLo := bLo) (n := n) (a₀ := a₀)
    hlo hn ha₀ hbHi_le_n h2a₀ O.hB_hi O.hB_mono O.hprogress

/-- Killed-kernel version of the marked pull milestone. -/
noncomputable def ghostKilledPullMilestone
    {h bHi bLo n a₀ : ℕ}
    {Q : Kernel (GhostConfig (L := L) (K := K))
        (GhostConfig (L := L) (K := K))}
    (G : Set (GhostConfig (L := L) (K := K)))
    (hlo : bLo < bHi) (hn : 2 ≤ n) (ha₀ : 1 ≤ a₀)
    (hbHi_le_n : bHi ≤ n) (h2a₀ : 2 * a₀ ≤ n - 1)
    (hB_hi : ∀ o,
      liftGhostCounter (L := L) (K := K)
          (ghostUnpulledO (L := L) (K := K) h) o ≤ bHi)
    (hB_mono : ∀ o o',
      0 < (GatedDrift.killK_now Q G) o {o'} →
        liftGhostCounter (L := L) (K := K)
            (ghostUnpulledO (L := L) (K := K) h) o' ≤
          liftGhostCounter (L := L) (K := K)
            (ghostUnpulledO (L := L) (K := K) h) o)
    (hprogress : ∀ (i : Fin (bHi - bLo)) o,
      liftGhostCounter (L := L) (K := K)
          (ghostUnpulledO (L := L) (K := K) h) o = bHi - i.val →
        (GatedDrift.killK_now Q G) o {o' |
            liftGhostCounter (L := L) (K := K)
                (ghostUnpulledO (L := L) (K := K) h) o' <
              liftGhostCounter (L := L) (K := K)
                (ghostUnpulledO (L := L) (K := K) h) o} ≥
          ENNReal.ofReal
            (Phase3Bridges.CatalyticPull.catalyticPullRate n a₀ (bHi - i.val))) :
    RoleSplitConcentration.KernelMilestone (GatedDrift.killK_now Q G) :=
  Phase3Bridges.CatalyticPull.catalyticPullKernelMilestone
    (Q := GatedDrift.killK_now Q G)
    (B := liftGhostCounter (L := L) (K := K)
      (ghostUnpulledO (L := L) (K := K) h))
    (bHi := bHi) (bLo := bLo) (n := n) (a₀ := a₀)
    hlo hn ha₀ hbHi_le_n h2a₀
    hB_hi
    hB_mono
    hprogress

/-- Ghost stopped-tail shape used before projection to the real stopped chain. -/
noncomputable def ghostStoppedTail
    (Q : Kernel (GhostConfig (L := L) (K := K))
        (GhostConfig (L := L) (K := K)))
    (G : Set (GhostConfig (L := L) (K := K))) (t : ℕ)
    (C₀ : GhostConfig (L := L) (K := K))
    (Bad : GhostConfig (L := L) (K := K) → Prop) (ε : ℝ≥0∞) : Prop :=
  (GatedDrift.killK_now Q G ^ t) (some C₀) (Phase3Core.killedBad Bad) ≤ ε

/-- Generic ghost stopped-tail theorem from the marked catalytic milestone. -/
theorem ghost_stoppedTail_of_kernelMilestone_noPre
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    [Countable (GhostConfig (L := L) (K := K))]
    (Q : Kernel (GhostConfig (L := L) (K := K))
        (GhostConfig (L := L) (K := K))) [IsMarkovKernel Q]
    (G S : Set (GhostConfig (L := L) (K := K)))
    (good : GhostConfig (L := L) (K := K) → Prop)
    (q ε : ℝ≥0∞)
    (mp : RoleSplitConcentration.KernelMilestone (GatedDrift.killK_now Q G))
    (P : Protocol Λ)
    (post_sound : ∀ C, mp.Post (some C) → good C)
    (hstep : ∀ C ∈ G, C ∈ S → Q C Gᶜ ≤ q)
    (C₀ : GhostConfig (L := L) (K := K)) (hC₀ : C₀ ∈ G)
    (lam : ℝ) (hlam : 1 ≤ lam) (t : ℕ)
    (ht : lam * mp.meanTime ≤ (t : ℝ))
    (hbudget :
      ENNReal.ofReal
          (Real.exp (-mp.pMin * mp.meanTime * (lam - 1 - Real.log lam))) +
        ((t : ℝ≥0∞) * q + ∑ τ ∈ Finset.range t, (Q ^ τ) C₀ Sᶜ)
        ≤ ε) :
    ghostStoppedTail (L := L) (K := K) Q G t C₀ (fun C => ¬ good C) ε := by
  unfold ghostStoppedTail
  unfold Phase3Core.killedBad
  exact (Phase3Bridges.killedBad_notGood_le_janson_add_escape_noPre
    (K := Q) G S good q mp P post_sound hstep C₀ hC₀ lam hlam t ht).trans hbudget

/-- A per-run marked-pull certificate.  The last field is the concrete coupling
from the ghost stopped chain back to the real stopped Phase-3 chain; it is the
place where a production instantiation proves the ghost kernel projects to the
real stopped kernel. -/
structure MarkedPullRun
    (D : Phase3Core.Phase3ModeDomain L) (h t : ℕ)
    (realGate : Set (Phase3Core.Omega L K))
    (c₀ : Phase3Core.Omega L K) (ε : ℝ≥0∞) where
  rho : ℝ
  hcoef : D.tau h ≤ 97 / 100 - 2 * rho
  C₀ : GhostConfig (L := L) (K := K)
  forget_C₀ : forgetGhost C₀ = c₀
  Q : Kernel (GhostConfig (L := L) (K := K)) (GhostConfig (L := L) (K := K))
  G : Set (GhostConfig (L := L) (K := K))
  ghost_tail :
    ghostStoppedTail (L := L) (K := K) Q G t C₀
      (fun C => ¬ BirthCorrectedGhostGood (L := L) (K := K) D h rho C) ε
  projection_le :
    (GatedDrift.killK_now (Phase3Core.phase3Kernel L K) realGate ^ t) (some c₀)
        (Phase3Core.killedBad
          (fun c => ¬ Phase3Core.OFuelFloor (L := L) (K := K) D h c))
      ≤ (GatedDrift.killK_now Q G ^ t) (some C₀)
        (Phase3Core.killedBad
          (fun C => ¬ BirthCorrectedGhostGood (L := L) (K := K) D h rho C))

/-- Read a real stopped H13 tail from a completed marked-pull run.  This theorem
keeps the real projection obligation explicit; no raw lagging-O monotonicity is
used. -/
theorem stoppedTail_of_markedPullRun
    (D : Phase3Core.Phase3ModeDomain L) (h t : ℕ)
    (realGate : Set (Phase3Core.Omega L K))
    (c₀ : Phase3Core.Omega L K) (ε : ℝ≥0∞)
    (R : MarkedPullRun (L := L) (K := K) D h t realGate c₀ ε) :
    Phase3Core.stoppedTail (L := L) (K := K) realGate t c₀
      (fun c => ¬ Phase3Core.OFuelFloor (L := L) (K := K) D h c) ε :=
  R.projection_le.trans R.ghost_tail

/-- Hour-local data producing the H13 bridge field from marked-pull runs. -/
structure H13MarkedPullData {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr) where
  eps : ℕ → ℝ≥0∞
  eps_budget : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h → eps h ≤ T.surface.eps13 h
  markedRun : ∀ h, h ≤ D.lastCoreHour → 5 ≤ h →
    Phase3Core.PrevCore (L := L) (K := K) D T h →
    Phase3GoodClock.CoreClockInputs (L := L) (K := K) θ tr h →
    ∀ cO, cO ∈ T.surface.checkpoint .afterO h →
    ∀ dt, dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h) →
      MarkedPullRun (L := L) (K := K) D h dt (T.surface.hourGate h) cO (eps h)

/-- Package marked-pull H13 data into the public bridge. -/
noncomputable def H13MarkedPullData.toH13Bridge
    {θ : Phase3GoodClock.ClockTimingParams} {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    (E : H13MarkedPullData (L := L) (K := K) D T) :
    Phase3Bridges.H13Bridge (L := L) (K := K) D T where
  epsReach := E.eps
  eps_budget := E.eps_budget
  reached_tail := by
    intro h hle h5 prev I cO hcO dt hdt
    exact stoppedTail_of_markedPullRun (L := L) (K := K) D h dt
      (T.surface.hourGate h) cO (E.eps h)
      (E.markedRun h hle h5 prev I cO hcO dt hdt)

#print axioms reachedMainFloor_of_birthCorrectionLedger
#print axioms ofuelFloor_of_birthCorrectionLedger
#print axioms ghostPullMilestone
#print axioms ghostKilledPullMilestone
#print axioms ghost_stoppedTail_of_kernelMilestone_noPre
#print axioms H13MarkedPullData.toH13Bridge

end Lemma613MarkedPullDrop

end ExactMajority
