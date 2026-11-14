-- Ripple/Kurtz/StrongApprox/RegenerativePoissonRecord.lean
import Mathlib
import Ripple.Kurtz.StrongApprox.PositiveRaceKernel
import Ripple.Kurtz.StrongApprox.RecordPastFreshness
import Ripple.sCRNUniversality.CTMCIdentification

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Finset Filter Preorder
open scoped ENNReal BigOperators
open Ripple.CTMC
open Ripple.sCRNUniversality.CTMCBridge
open Ripple.sCRNUniversality.CTMCIdentification
open ExponentialRace

universe u

namespace RegenerativeRace

variable {S : Type u} [Fintype S] [DecidableEq S] [Countable S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Positive off-diagonal destinations available from `x`. -/
abbrev ActiveTarget (Q : QMatrix S) (x : S) :=
  {y : S // y ≠ x ∧ Q.rate x y ≠ 0}

/-- A fixed finite channel name remembers both its source and target state. -/
abbrev RaceToken (Q : QMatrix S) :=
  Σ x : S, ActiveTarget Q x

/-- One fresh iid exponential row. -/
abbrev RaceRow (Q : QMatrix S) := RaceToken Q → ℝ

/-- Countably many fresh race rows. -/
abbrev PoissonRaceΩ (Q : QMatrix S) := ℕ → RaceRow Q

/-- The fixed countable `(channel, cell, slot)` index of the regenerative
source. The slot is unique because one gap is used per channel and record cell. -/
abbrev FixedRaceToken (Q : QMatrix S) := RaceToken Q × (ℕ × Unit)

/-- Currying equivalence between row samples and the fixed token sample. -/
def rowsEquivFixedTokens (Q : QMatrix S) :
    PoissonRaceΩ Q ≃ (FixedRaceToken Q → ℝ) where
  toFun rows q := rows q.2.1 q.1
  invFun f n l := f (l, n, ())
  left_inv rows := by funext n l; rfl
  right_inv f := by funext q; rcases q with ⟨l, n, u⟩; cases u; rfl

/-- Positive real rate attached to an active target. -/
def targetRate (Q : QMatrix S) (x : S) (a : ActiveTarget Q x) : ℝ :=
  Q.rate x a.1

theorem targetRate_pos (Q : QMatrix S) (x : S) (a : ActiveTarget Q x) :
    0 < targetRate Q x a := by
  have hnonneg := Q.rate_nonneg x a.1 a.2.1.symm
  exact lt_of_le_of_ne hnonneg (Ne.symm a.2.2)

/-- Removing zero off-diagonal entries does not change the exit-rate sum. -/
theorem targetRate_total (Q : QMatrix S) (x : S) :
    rateTotal (targetRate Q x) = Q.exitRate x := by
  classical
  unfold rateTotal targetRate QMatrix.exitRate
  calc
    (∑ a : ActiveTarget Q x, Q.rate x a.1) =
        ∑ y ∈ Finset.univ.filter (fun y => y ≠ x ∧ Q.rate x y ≠ 0),
          Q.rate x y := by
      simpa only [ActiveTarget] using
        (Finset.sum_subtype
          (Finset.univ.filter (fun y => y ≠ x ∧ Q.rate x y ≠ 0))
          (p := fun y => y ≠ x ∧ Q.rate x y ≠ 0)
          (by simp) (fun y => Q.rate x y)).symm
    _ = ∑ y ∈ Finset.univ.filter (· ≠ x), Q.rate x y := by
      rw [Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases hyx : y ≠ x
      · by_cases hyr : Q.rate x y ≠ 0
        · simp [hyx, hyr]
        · have hz : Q.rate x y = 0 := not_not.mp hyr
          simp [hyx, hz]
      · simp [hyx]

/-- A nonabsorbing state has at least one active target. -/
theorem activeTarget_nonempty (Q : QMatrix S) {x : S}
    (h : ¬Q.IsAbsorbing x) : Nonempty (ActiveTarget Q x) := by
  classical
  by_contra hempty
  have hz : ∀ y : S, y ≠ x → Q.rate x y = 0 := by
    intro y hyx
    by_contra hyr
    exact hempty ⟨⟨y, hyx, hyr⟩⟩
  apply h
  unfold QMatrix.IsAbsorbing QMatrix.exitRate
  apply Finset.sum_eq_zero
  intro y hy
  exact hz y (Finset.mem_filter.mp hy).2

/-- Restrict a global row to the channels available at one source state. -/
def stateClocks (Q : QMatrix S) (x : S) (E : RaceRow Q) :
    ActiveTarget Q x → ℝ :=
  fun a => E ⟨x, a⟩

@[fun_prop]
theorem measurable_stateClocks (Q : QMatrix S) (x : S) :
    Measurable (stateClocks Q x) := by
  apply measurable_pi_lambda
  intro a
  exact measurable_pi_apply (Sigma.mk x a)

/-- A state fibre of the global row is an iid unit exponential vector. -/
theorem stateClocks_law (Q : QMatrix S) (x : S) :
    (clockLaw (RaceToken Q)).map (stateClocks Q x) =
      clockLaw (ActiveTarget Q x) := by
  exact clockSubfamily_law (fun a : ActiveTarget Q x => Sigma.mk x a)
    (by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- The winner PMF of the active-target race maps to the embedded jump row. -/
theorem activeWinnerPMF_map (Q : QMatrix S) {x : S}
    (h : ¬Q.IsAbsorbing x) :
    letI : Nonempty (ActiveTarget Q x) := activeTarget_nonempty Q h
    (winnerPMF (targetRate Q x) (targetRate_pos Q x)).map Subtype.val =
      Q.embeddedDTMC.step x := by
  classical
  letI : Nonempty (ActiveTarget Q x) := activeTarget_nonempty Q h
  ext y
  rw [PMF.map_apply, tsum_fintype,
    Q.embeddedDTMC_step_of_nonabsorbing h y]
  by_cases hyx : y = x
  · subst y
    rw [Q.jumpProb_self]
    apply Finset.sum_eq_zero
    intro a _ha
    have h1 : x ≠ a.1 := a.2.1.symm
    simp [h1]
  · rw [QMatrix.jumpProb, if_neg (Ne.symm hyx)]
    by_cases hyr : Q.rate x y = 0
    · rw [hyr, zero_div, ENNReal.ofReal_zero]
      apply Finset.sum_eq_zero
      intro a _ha
      have hval : a.1 ≠ y := by
        intro hay
        apply a.2.2
        simpa [hay] using hyr
      simp [hval, hval.symm]
    · let a : ActiveTarget Q x := ⟨y, hyx, hyr⟩
      rw [Finset.sum_eq_single a]
      · rw [if_pos (rfl : y = a.1), winnerPMF_apply, targetRate_total]
        rfl
      · intro b _hb hba
        have hval : b.1 ≠ y := by
          intro hby
          apply hba
          exact Subtype.ext hby
        simp [hval, hval.symm]
      · intro ha
        exact False.elim (ha (Finset.mem_univ a))

/-- Measure form of `activeWinnerPMF_map`. -/
theorem activeWinnerMeasure_map (Q : QMatrix S) {x : S}
    (h : ¬Q.IsAbsorbing x) :
    letI : Nonempty (ActiveTarget Q x) := activeTarget_nonempty Q h
    Measure.map Subtype.val
        (winnerPMF (targetRate Q x) (targetRate_pos Q x)).toMeasure =
      Q.embeddedStepMeasure x := by
  letI : Nonempty (ActiveTarget Q x) := activeTarget_nonempty Q h
  rw [PMF.toMeasure_map Subtype.val
    (winnerPMF (targetRate Q x) (targetRate_pos Q x)) (by fun_prop),
    activeWinnerPMF_map Q h]
  rfl

/-- Live one-step race output. -/
noncomputable def liveRaceStep (Q : QMatrix S) (x : S)
    (h : ¬Q.IsAbsorbing x) (E : RaceRow Q) : ℝ × S := by
  letI : Nonempty (ActiveTarget Q x) := activeTarget_nonempty Q h
  let p := racePair (targetRate Q x) (stateClocks Q x E)
  exact (p.1, p.2.1)

@[fun_prop]
theorem measurable_liveRaceStep (Q : QMatrix S) (x : S)
    (h : ¬Q.IsAbsorbing x) : Measurable (liveRaceStep Q x h) := by
  letI : Nonempty (ActiveTarget Q x) := activeTarget_nonempty Q h
  unfold liveRaceStep
  exact (measurable_fst.comp
      ((measurable_racePair (targetRate Q x)).comp
        (measurable_stateClocks Q x))).prodMk
    (measurable_subtype_coe.comp (measurable_snd.comp
      ((measurable_racePair (targetRate Q x)).comp
        (measurable_stateClocks Q x))))

/-- A regenerative row has exactly the nonabsorbing jump-and-hold law. -/
theorem liveRaceStep_law (Q : QMatrix S) (x : S)
    (h : ¬Q.IsAbsorbing x) :
    Measure.map (liveRaceStep Q x h) (clockLaw (RaceToken Q)) =
      Q.jumpHoldStepMeasure h := by
  letI : Nonempty (ActiveTarget Q x) := activeTarget_nonempty Q h
  let r := targetRate Q x
  have hr : ∀ a, 0 < r a := targetRate_pos Q x
  letI : IsProbabilityMeasure (expMeasure (rateTotal r)) :=
    isProbabilityMeasure_expMeasure (rateTotal_pos r hr)
  have hclocks := stateClocks_law Q x
  have hpair := racePair_law r hr
  change Measure.map
      (((Prod.map id Subtype.val) ∘ racePair r) ∘ stateClocks Q x)
      (clockLaw (RaceToken Q)) = _
  rw [← Measure.map_map
      ((measurable_id.prodMap measurable_subtype_coe).comp
        (measurable_racePair r))
      (measurable_stateClocks Q x), hclocks,
    ← Measure.map_map (measurable_id.prodMap measurable_subtype_coe)
      (measurable_racePair r), hpair,
    ← Measure.map_prod_map (expMeasure (rateTotal r))
      (winnerPMF r hr).toMeasure measurable_id (by fun_prop),
    Measure.map_id, activeWinnerMeasure_map Q h,
    targetRate_total]
  rfl

open Classical in
/-- Total one-step race, with the canonical terminal marker at absorption. -/
noncomputable def raceStep (Q : QMatrix S) (x : S)
    (E : RaceRow Q) : ℝ × S :=
  if h : Q.IsAbsorbing x then (0, x) else liveRaceStep Q x h E

theorem raceStep_eq_of_absorbing (Q : QMatrix S) {x : S}
    (h : Q.IsAbsorbing x) : raceStep Q x = fun _ => (0, x) := by
  funext E
  unfold raceStep
  rw [dif_pos h]

theorem raceStep_eq_of_nonabsorbing (Q : QMatrix S) {x : S}
    (h : ¬Q.IsAbsorbing x) : raceStep Q x = liveRaceStep Q x h := by
  funext E
  unfold raceStep
  rw [dif_neg h]

@[fun_prop]
theorem measurable_raceStep_row (Q : QMatrix S) (x : S) :
    Measurable (raceStep Q x) := by
  by_cases h : Q.IsAbsorbing x
  · rw [raceStep_eq_of_absorbing Q h]
    exact measurable_const
  · rw [raceStep_eq_of_nonabsorbing Q h]
    exact measurable_liveRaceStep Q x h

@[fun_prop]
theorem measurable_raceStep (Q : QMatrix S) :
    Measurable (fun p : S × RaceRow Q => raceStep Q p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro x
  exact measurable_raceStep_row Q x

/-- The total race row is the canonical total jump-and-hold measure. -/
theorem raceStep_law (Q : QMatrix S) (x : S) :
    Measure.map (raceStep Q x) (clockLaw (RaceToken Q)) =
      Q.jumpHoldStepMeasureTotal x := by
  by_cases h : Q.IsAbsorbing x
  · rw [Q.jumpHoldStepMeasureTotal_of_absorbing h]
    rw [raceStep_eq_of_absorbing Q h, Measure.map_const]
    simp
  · rw [Q.jumpHoldStepMeasureTotal_of_nonabsorbing h,
      raceStep_eq_of_nonabsorbing Q h]
    exact liveRaceStep_law Q x h

/-- Product law of countably many fresh iid race rows. -/
noncomputable def poissonRaceMeasure (Q : QMatrix S) :
    Measure (PoissonRaceΩ Q) :=
  Measure.infinitePi (fun _ : ℕ => clockLaw (RaceToken Q))

instance poissonRaceMeasure_isProbabilityMeasure (Q : QMatrix S) :
    IsProbabilityMeasure (poissonRaceMeasure Q) := by
  unfold poissonRaceMeasure
  infer_instance

/-- The first `n` race rows. -/
def raceRowPrefix (Q : QMatrix S) (n : ℕ)
    (rows : PoissonRaceΩ Q) : Fin n → RaceRow Q :=
  fun j => rows j

@[fun_prop]
theorem measurable_raceRowPrefix (Q : QMatrix S) (n : ℕ) :
    Measurable (raceRowPrefix Q n) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_pi_apply j.1

/-- Finite row-prefix law. -/
theorem raceRowPrefix_law (Q : QMatrix S) (n : ℕ) :
    (poissonRaceMeasure Q).map (raceRowPrefix Q n) =
      Measure.pi (fun _ : Fin n => clockLaw (RaceToken Q)) := by
  simpa only [poissonRaceMeasure, raceRowPrefix,
    Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => clockLaw (RaceToken Q))
      (f := fun j : Fin n => j.val) Fin.val_injective)

/-- Earlier rows are independent of row `n`. -/
theorem raceRowPrefix_indep_next (Q : QMatrix S) (n : ℕ) :
    IndepFun (raceRowPrefix Q n) (fun rows : PoissonRaceΩ Q => rows n)
      (poissonRaceMeasure Q) := by
  have hi : iIndepFun
      (fun i : ℕ => fun rows : PoissonRaceΩ Q => rows i)
      (poissonRaceMeasure Q) := by
    exact iIndepFun_infinitePi
      (P := fun _ : ℕ => clockLaw (RaceToken Q))
      (X := fun (_ : ℕ) (x : RaceRow Q) => x)
      (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
  have h := iIndepFun.indepFun_finset (Finset.range n) ({n} : Finset ℕ)
    hd hi (fun i => measurable_pi_apply i)
  have hc := h.comp
    (φ := fun p : (i : Finset.range n) → RaceRow Q =>
      fun j : Fin n => p ⟨j.val, Finset.mem_range.mpr j.isLt⟩)
    (ψ := fun p : (i : ({n} : Finset ℕ)) → RaceRow Q =>
      p ⟨n, Finset.mem_singleton_self n⟩)
    (measurable_pi_lambda _ fun j => measurable_pi_apply _)
    (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ)) :
      Measurable fun p : ({n} : Finset ℕ) → RaceRow Q =>
        p ⟨n, Finset.mem_singleton_self n⟩)
  simpa only [Function.comp_def, raceRowPrefix] using hc

/-- Joint finite-prefix/next-row product law. -/
theorem raceRowPrefix_next_law (Q : QMatrix S) (n : ℕ) :
    (poissonRaceMeasure Q).map
        (fun rows => (raceRowPrefix Q n rows, rows n)) =
      (Measure.pi (fun _ : Fin n => clockLaw (RaceToken Q))).prod
        (clockLaw (RaceToken Q)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map
      (measurable_raceRowPrefix Q n).aemeasurable
      (measurable_pi_apply n).aemeasurable).mp
    (raceRowPrefix_indep_next Q n),
    raceRowPrefix_law]
  rw [poissonRaceMeasure, Measure.infinitePi_map_eval]

/-- State recursion driven by successive fresh race rows. -/
noncomputable def poissonState (Q : QMatrix S) (x₀ : S)
    (rows : PoissonRaceΩ Q) : ℕ → S
  | 0 => x₀
  | n + 1 => (raceStep Q (poissonState Q x₀ rows n) (rows n)).2

/-- Jump-and-hold record recursion. -/
noncomputable def poissonRecord (Q : QMatrix S) (x₀ : S)
    (rows : PoissonRaceΩ Q) : ℕ → ℝ × S
  | 0 => (0, x₀)
  | n + 1 => raceStep Q (poissonState Q x₀ rows n) (rows n)

@[simp]
theorem poissonRecord_zero (Q : QMatrix S) (x₀ : S)
    (rows : PoissonRaceΩ Q) :
    poissonRecord Q x₀ rows 0 = (0, x₀) := rfl

@[simp]
theorem poissonRecord_state (Q : QMatrix S) (x₀ : S)
    (rows : PoissonRaceΩ Q) (n : ℕ) :
    (poissonRecord Q x₀ rows n).2 = poissonState Q x₀ rows n := by
  cases n <;> rfl

@[fun_prop]
theorem measurable_poissonState (Q : QMatrix S) (x₀ : S) (n : ℕ) :
    Measurable (fun rows => poissonState Q x₀ rows n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact (measurable_snd.comp ((measurable_raceStep Q).comp
        (ih.prodMk (measurable_pi_apply n))))

@[fun_prop]
theorem measurable_poissonRecord (Q : QMatrix S) (x₀ : S) :
    Measurable (poissonRecord Q x₀) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_const
  | succ n =>
      exact (measurable_raceStep Q).comp
        ((measurable_poissonState Q x₀ n).prodMk
          (measurable_pi_apply n))

/-- State at time `n` only uses rows with index `< n`. -/
theorem poissonState_congr_before (Q : QMatrix S) (x₀ : S)
    {rows rows' : PoissonRaceΩ Q} (n : ℕ)
    (hrows : ∀ j, j < n → rows j = rows' j) :
    poissonState Q x₀ rows n = poissonState Q x₀ rows' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [poissonState, poissonState,
        ih (fun j hj => hrows j (hj.trans (Nat.lt_succ_self n))),
        hrows n (Nat.lt_succ_self n)]

/-- Record `n` only uses rows with index `< n`. -/
theorem poissonRecord_congr_before (Q : QMatrix S) (x₀ : S)
    {rows rows' : PoissonRaceΩ Q} (n : ℕ)
    (hrows : ∀ j, j < n → rows j = rows' j) :
    poissonRecord Q x₀ rows n = poissonRecord Q x₀ rows' n := by
  cases n with
  | zero => rfl
  | succ n =>
      rw [poissonRecord, poissonRecord,
        poissonState_congr_before Q x₀ n
          (fun j hj => hrows j (hj.trans (Nat.lt_succ_self n))),
        hrows n (Nat.lt_succ_self n)]

/-- Extend a finite row prefix by an irrelevant zero tail. -/
def extendRaceRows (Q : QMatrix S) (n : ℕ)
    (p : Fin n → RaceRow Q) : PoissonRaceΩ Q :=
  fun j => if h : j < n then p ⟨j, h⟩ else fun _ => 0

@[fun_prop]
theorem measurable_extendRaceRows (Q : QMatrix S) (n : ℕ) :
    Measurable (extendRaceRows Q n) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j < n
  · simpa [extendRaceRows, hj] using
      (measurable_pi_apply (⟨j, hj⟩ : Fin n))
  · simpa [extendRaceRows, hj] using
      (measurable_const : Measurable (fun _ : Fin n → RaceRow Q =>
        (fun _ => 0 : RaceRow Q)))

@[simp]
theorem extendRaceRows_prefix_apply (Q : QMatrix S) (n j : ℕ)
    (rows : PoissonRaceΩ Q) (hj : j < n) :
    extendRaceRows Q n (raceRowPrefix Q n rows) j = rows j := by
  simp [extendRaceRows, raceRowPrefix, hj]

/-- Record history computed from exactly the finite row prefix. -/
noncomputable def recordHistory (Q : QMatrix S) (x₀ : S) (n : ℕ)
    (p : Fin n → RaceRow Q) :
    (i : Finset.Iic n) → ℝ × S :=
  frestrictLe (π := fun _ : ℕ => ℝ × S) n
    (poissonRecord Q x₀ (extendRaceRows Q n p))

@[fun_prop]
theorem measurable_recordHistory (Q : QMatrix S) (x₀ : S) (n : ℕ) :
    Measurable (recordHistory Q x₀ n) :=
  (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n).comp
    ((measurable_poissonRecord Q x₀).comp
      (measurable_extendRaceRows Q n))

/-- Restricting the full sample and then rebuilding the history changes
nothing through record index `n`. -/
theorem recordHistory_restrict (Q : QMatrix S) (x₀ : S) (n : ℕ)
    (rows : PoissonRaceΩ Q) :
    recordHistory Q x₀ n (raceRowPrefix Q n rows) =
      recordPrefix (poissonRecord Q x₀) n rows := by
  funext i
  apply poissonRecord_congr_before Q x₀ i.1
  intro j hj
  exact extendRaceRows_prefix_apply Q n j rows
    (hj.trans_le (Finset.mem_Iic.mp i.2))

/-- Current state read from a finite record history. -/
theorem recordHistory_currentState (Q : QMatrix S) (x₀ : S) (n : ℕ)
    (p : Fin n → RaceRow Q) :
    QMatrix.currentStateFromHistory n (recordHistory Q x₀ n p) =
      poissonState Q x₀ (extendRaceRows Q n p) n := by
  exact poissonRecord_state Q x₀ _ n

/-- Next record as a measurable function of the finite history and one fresh row. -/
noncomputable def nextRecord (Q : QMatrix S) (x₀ : S) (n : ℕ)
    (pr : (Fin n → RaceRow Q) × RaceRow Q) : ℝ × S :=
  raceStep Q (poissonState Q x₀ (extendRaceRows Q n pr.1) n) pr.2

@[fun_prop]
theorem measurable_nextRecord (Q : QMatrix S) (x₀ : S) (n : ℕ) :
    Measurable (nextRecord Q x₀ n) :=
  (measurable_raceStep Q).comp
    (((measurable_poissonState Q x₀ n).comp
      ((measurable_extendRaceRows Q n).comp measurable_fst)).prodMk
        measurable_snd)

/-- Rebuilding the finite prefix and supplying row `n` gives record `n+1`. -/
theorem nextRecord_restrict (Q : QMatrix S) (x₀ : S) (n : ℕ)
    (rows : PoissonRaceΩ Q) :
    nextRecord Q x₀ n (raceRowPrefix Q n rows, rows n) =
      poissonRecord Q x₀ rows (n + 1) := by
  unfold nextRecord poissonRecord
  rw [poissonState_congr_before Q x₀ n
    (fun j hj => extendRaceRows_prefix_apply Q n j rows hj)]

/-- Marginal law of the finite record prefix. -/
theorem poissonRaceMeasure_map_recordPrefix
    (Q : QMatrix S) (x₀ : S) (n : ℕ) :
    (poissonRaceMeasure Q).map
        (recordPrefix (poissonRecord Q x₀) n) =
      (Measure.pi (fun _ : Fin n => clockLaw (RaceToken Q))).map
        (recordHistory Q x₀ n) := by
  rw [← raceRowPrefix_law Q n,
    Measure.map_map (measurable_recordHistory Q x₀ n)
      (measurable_raceRowPrefix Q n)]
  apply Measure.map_congr
  filter_upwards [] with rows
  exact (recordHistory_restrict Q x₀ n rows).symm

/-- **Requested source theorem.** At every recursively generated record index,
the fresh race row is iid unit exponential and independent of the complete
finite record past. -/
theorem poissonRecord_freshResidualsAt
    (Q : QMatrix S) (x₀ : S) (n : ℕ) :
    FreshResidualsAt (poissonRaceMeasure Q) (poissonRecord Q x₀)
      (fun rows => rows n) n := by
  refine
    { measurable_history :=
        (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n).comp
          (measurable_poissonRecord Q x₀)
      measurable_residual := measurable_pi_apply n
      joint_law := ?_ }
  let ν := Measure.pi (fun _ : Fin n => clockLaw (RaceToken Q))
  let ρ := clockLaw (RaceToken Q)
  calc
    (poissonRaceMeasure Q).map
        (fun rows =>
          (recordPrefix (poissonRecord Q x₀) n rows, rows n)) =
        (poissonRaceMeasure Q).map
          (fun rows =>
            (recordHistory Q x₀ n (raceRowPrefix Q n rows), rows n)) := by
      apply Measure.map_congr
      filter_upwards [] with rows
      rw [recordHistory_restrict Q x₀ n rows]
    _ = (ν.prod ρ).map (Prod.map (recordHistory Q x₀ n) id) := by
      rw [← raceRowPrefix_next_law Q n,
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (ν.map (recordHistory Q x₀ n)).prod ρ := by
      simpa only [Measure.map_id] using
        (Measure.map_prod_map ν ρ
          (measurable_recordHistory Q x₀ n) measurable_id).symm
    _ = ((poissonRaceMeasure Q).map
          (recordPrefix (poissonRecord Q x₀) n)).prod ρ := by
      rw [poissonRaceMeasure_map_recordPrefix Q x₀ n]

/-- Initial record-prefix law. -/
theorem poissonRecord_initial (Q : QMatrix S) (x₀ : S) :
    ((poissonRaceMeasure Q).map (poissonRecord Q x₀)).map
        (frestrictLe (π := fun _ => ℝ × S) 0) =
      (Measure.dirac (0, x₀)).map
        (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => ℝ × S)).symm := by
  rw [Measure.map_map
    (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) 0)
    (measurable_poissonRecord Q x₀)]
  have hconst :
      (frestrictLe (π := fun _ : ℕ => ℝ × S) 0) ∘
          poissonRecord Q x₀ =
        fun _ => (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => ℝ × S)).symm (0, x₀) := by
    funext rows i
    rcases i with ⟨i, hi⟩
    have : i = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp hi)
    subst i
    rfl
  rw [hconst]
  simp

/-- Product-history transport for an iid next row. -/
theorem map_prod_history_next
    {A B H Y : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace H] [MeasurableSpace Y]
    (μ : Measure A) [SFinite μ] (ρ : Measure B) [SFinite ρ]
    (θ : Kernel H Y) [IsSFiniteKernel θ]
    (history : A → H) (hHistory : Measurable history)
    (next : A × B → Y) (hNext : Measurable next)
    (hrow : ∀ᵐ a ∂μ,
      ρ.map (fun b => next (a, b)) = θ (history a)) :
    (μ.prod ρ).map (fun ab => (history ab.1, next ab)) =
      (μ.map history) ⊗ₘ θ := by
  have hpair : Measurable
      (fun ab : A × B => (history ab.1, next ab)) :=
    (hHistory.comp measurable_fst).prodMk hNext
  refine Measure.ext_of_lintegral _ (fun f hf => ?_)
  calc
    ∫⁻ z, f z ∂((μ.prod ρ).map
        (fun ab => (history ab.1, next ab))) =
        ∫⁻ a, ∫⁻ b, f (history a, next (a, b)) ∂ρ ∂μ := by
      rw [lintegral_map hf hpair, lintegral_prod (fun ab : A × B => f (history ab.1, next ab))
        (hf.comp hpair).aemeasurable]
    _ = ∫⁻ a, ∫⁻ y, f (history a, y) ∂θ (history a) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hrow] with a ha
      rw [← ha]
      exact (lintegral_map (hf.comp (measurable_const.prodMk measurable_id))
        (hNext.comp (measurable_const.prodMk measurable_id))).symm
    _ = ∫⁻ h, ∫⁻ y, f (h, y) ∂θ h ∂μ.map history := by
      rw [lintegral_map hf.lintegral_kernel_prod_right' hHistory]
    _ = ∫⁻ z, f z ∂((μ.map history) ⊗ₘ θ) := by
      rw [Measure.lintegral_compProd hf]

/-- History/next-record kernel identity for the regenerative source. -/
theorem poissonRecord_history_next
    (Q : QMatrix S) (x₀ : S) (n : ℕ) :
    let μ := (poissonRaceMeasure Q).map (poissonRecord Q x₀)
    μ.map (fun records =>
        (frestrictLe (π := fun _ : ℕ => ℝ × S) n records,
          records (n + 1))) =
      μ.map (frestrictLe (π := fun _ : ℕ => ℝ × S) n) ⊗ₘ
        Q.jumpHoldTrajectoryStepKernel n := by
  let ν := Measure.pi (fun _ : Fin n => clockLaw (RaceToken Q))
  let ρ := clockLaw (RaceToken Q)
  let θ := Q.jumpHoldTrajectoryStepKernel n
  letI : IsMarkovKernel θ := Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  have hrow : ∀ p : Fin n → RaceRow Q,
      ρ.map (fun E => nextRecord Q x₀ n (p, E)) =
        θ (recordHistory Q x₀ n p) := by
    intro p
    rw [Q.jumpHoldTrajectoryStepKernel_apply,
      recordHistory_currentState Q x₀ n p,
      Q.jumpHoldStepKernel_apply]
    exact raceStep_law Q (poissonState Q x₀ (extendRaceRows Q n p) n)
  have htransport := map_prod_history_next ν ρ θ
    (recordHistory Q x₀ n) (measurable_recordHistory Q x₀ n)
    (nextRecord Q x₀ n) (measurable_nextRecord Q x₀ n)
    (ae_of_all ν hrow)
  dsimp only
  calc
    (((poissonRaceMeasure Q).map (poissonRecord Q x₀)).map
        (fun records =>
          (frestrictLe (π := fun _ : ℕ => ℝ × S) n records,
            records (n + 1)))) =
        (poissonRaceMeasure Q).map
          (fun rows =>
            (recordHistory Q x₀ n (raceRowPrefix Q n rows),
              nextRecord Q x₀ n (raceRowPrefix Q n rows, rows n))) := by
      rw [Measure.map_map (by fun_prop) (measurable_poissonRecord Q x₀)]
      apply Measure.map_congr
      filter_upwards [] with rows
      apply Prod.ext
      · exact (recordHistory_restrict Q x₀ n rows).symm
      · exact (nextRecord_restrict Q x₀ n rows).symm
    _ = (ν.prod ρ).map
        (fun pr =>
          (recordHistory Q x₀ n pr.1,
            nextRecord Q x₀ n pr)) := by
      rw [← raceRowPrefix_next_law Q n,
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (ν.map (recordHistory Q x₀ n)) ⊗ₘ θ := htransport
    _ = (((poissonRaceMeasure Q).map (poissonRecord Q x₀)).map
          (frestrictLe (π := fun _ : ℕ => ℝ × S) n)) ⊗ₘ θ := by
      have h1 : ((poissonRaceMeasure Q).map (poissonRecord Q x₀)).map
          (frestrictLe (π := fun _ : ℕ => ℝ × S) n) =
          ν.map (recordHistory Q x₀ n) := by
        rw [Measure.map_map
          (measurable_frestrictLe (X := fun _ : ℕ => ℝ × S) n)
          (measurable_poissonRecord Q x₀)]
        exact poissonRaceMeasure_map_recordPrefix Q x₀ n
      rw [h1]

/-- **Unconditional source-to-canonical equality.** -/
theorem poissonRecord_map_eq_canonicalRecordMeasure
    (Q : QMatrix S) (x₀ : S) :
    (poissonRaceMeasure Q).map (poissonRecord Q x₀) =
      Q.canonicalRecordMeasure x₀ := by
  let μ := (poissonRaceMeasure Q).map (poissonRecord Q x₀)
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map
      (measurable_poissonRecord Q x₀).aemeasurable
  change μ = Q.canonicalRecordMeasure x₀
  apply eq_canonicalRecordMeasure_of_history_next Q x₀ μ
  · exact poissonRecord_initial Q x₀
  · intro n
    exact poissonRecord_history_next Q x₀ n

end RegenerativeRace

end Ripple.Kurtz.StrongApprox

end
