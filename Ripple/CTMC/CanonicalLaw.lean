/-
  Ripple.CTMC.CanonicalLaw — canonical finite-state CTMC path law skeleton

  This file packages the one-step jump-hold kernel from `CTMC.lean` into an
  Ionescu-Tulcea trajectory measure.  A trajectory is represented as a sequence
  of records `(holding time, state)`, with record 0 equal to `(0, initialState)`.
-/

import Ripple.CTMC.CTMCProcess
import Mathlib.Probability.Martingale.BorelCantelli
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

namespace Ripple.CTMC

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {S : Type*}

/-- One jump-hold record: the holding time just sampled and the state reached
after that hold.  Record 0 is used as the deterministic initial marker. -/
abbrev QMatrix.JumpHoldRecord (S : Type*) := ℝ × S

/-- Ionescu-Tulcea state space for the record trajectory. -/
abbrev QMatrix.JumpHoldTrajectorySpace (S : Type*) (_n : ℕ) :=
  QMatrix.JumpHoldRecord S

/-- The current state encoded by a finite record history is the state component
of the last record. -/
noncomputable def QMatrix.currentStateFromHistory
    (n : ℕ) (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) : S :=
  (hist ⟨n, mem_Iic.mpr le_rfl⟩).2

/-- Reading the current state from the final coordinate of a finite history is
measurable. -/
theorem QMatrix.measurable_currentStateFromHistory [MeasurableSpace S] (n : ℕ) :
    Measurable (fun hist : ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) =>
      QMatrix.currentStateFromHistory (S := S) n hist) := by
  unfold QMatrix.currentStateFromHistory QMatrix.JumpHoldTrajectorySpace QMatrix.JumpHoldRecord
  fun_prop

variable [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S]

/-- The history-dependent kernel required by Mathlib's Ionescu-Tulcea theorem:
look at the last state in the history and sample the next jump-hold record from
the total one-step CTMC kernel. -/
noncomputable def QMatrix.jumpHoldTrajectoryStepKernel (Q : QMatrix S) (n : ℕ) :
    Kernel ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
      (QMatrix.JumpHoldTrajectorySpace S (n + 1)) :=
  Q.jumpHoldStepKernel.comap
    (fun hist => QMatrix.currentStateFromHistory (S := S) n hist)
    (QMatrix.measurable_currentStateFromHistory (S := S) n)

/-- Applying the history-dependent trajectory kernel just applies the one-step
jump-hold kernel to the current state encoded in the last history record. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_apply
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :
    Q.jumpHoldTrajectoryStepKernel n hist =
      Q.jumpHoldStepKernel (QMatrix.currentStateFromHistory (S := S) n hist) :=
  rfl

/-- For a non-absorbing current state, the history-dependent trajectory step
kernel is exactly the product jump-hold law at that current state. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    Q.jumpHoldTrajectoryStepKernel n hist = Q.jumpHoldStepMeasure h := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]

/-- For an absorbing current state, the history-dependent trajectory step
kernel is the terminal record marker. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_of_absorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    Q.jumpHoldTrajectoryStepKernel n hist =
      Measure.dirac (0, QMatrix.currentStateFromHistory (S := S) n hist) := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_absorbing h]

/-- Each history-dependent record kernel is Markov. -/
theorem QMatrix.isMarkovKernel_jumpHoldTrajectoryStepKernel
    (Q : QMatrix S) (n : ℕ) :
    IsMarkovKernel (Q.jumpHoldTrajectoryStepKernel n) := by
  unfold QMatrix.jumpHoldTrajectoryStepKernel
  haveI : IsMarkovKernel Q.jumpHoldStepKernel := Q.isMarkovKernel_jumpHoldStepKernel
  exact Kernel.IsMarkovKernel.comap Q.jumpHoldStepKernel
    (QMatrix.measurable_currentStateFromHistory (S := S) n)

/-- For a non-absorbing current state, the holding-time marginal of the
history-dependent trajectory step kernel is the exponential holding-time law. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_map_fst_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    (Q.jumpHoldTrajectoryStepKernel n hist).map Prod.fst =
      Q.holdingTimeMeasure h := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h,
    Q.jumpHoldStepMeasure_map_fst]

/-- For a non-absorbing current state, the next-state marginal of the
history-dependent trajectory step kernel is the embedded jump-chain row. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_map_snd_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    (Q.jumpHoldTrajectoryStepKernel n hist).map Prod.snd =
      Q.embeddedStepMeasure (QMatrix.currentStateFromHistory (S := S) n hist) := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h,
    Q.jumpHoldStepMeasure_map_snd]

/-- For an absorbing current state, the holding-time marginal of the trajectory
step kernel is the terminal holding-time marker `0`. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_map_fst_of_absorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    (Q.jumpHoldTrajectoryStepKernel n hist).map Prod.fst =
      Measure.dirac 0 := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_absorbing h]
  simp

/-- For an absorbing current state, the next-state marginal of the trajectory
step kernel is the terminal state marker. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_map_snd_of_absorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    (Q.jumpHoldTrajectoryStepKernel n hist).map Prod.snd =
      Measure.dirac (QMatrix.currentStateFromHistory (S := S) n hist) := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_absorbing h]
  simp

/-- For a non-absorbing current state, the trajectory step samples a positive
holding time almost surely. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_holdingTime_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, 0 < r.1 := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]
  exact Q.jumpHoldStepMeasure_holdingTime_pos_ae h

/-- For a non-absorbing current state, the trajectory step samples a next state
different from the current state almost surely. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_next_ne_current_ae_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist,
      r.2 ≠ QMatrix.currentStateFromHistory (S := S) n hist := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]
  exact Q.jumpHoldStepMeasure_next_ne_self_ae h

/-- For a non-absorbing current state, the trajectory step samples a next
state with positive generator rate almost surely. -/
theorem QMatrix.jumpHoldTrajectoryStepKernel_next_rate_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (n : ℕ)
    (hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)
    (h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)) :
    ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist,
      0 < Q.rate (QMatrix.currentStateFromHistory (S := S) n hist) r.2 := by
  rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
    Q.jumpHoldStepMeasureTotal_of_nonabsorbing h]
  exact Q.jumpHoldStepMeasure_next_rate_pos_ae h

/-- Canonical record trajectory measure started from `s₀`.
Record 0 is deterministically `(0, s₀)`, and subsequent records are generated
by the history-dependent jump-hold kernels. -/
noncomputable def QMatrix.canonicalRecordMeasure (Q : QMatrix S) (s₀ : S) :
    Measure ((n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) := by
  let κ := Q.jumpHoldTrajectoryStepKernel
  letI : ∀ n, IsMarkovKernel (κ n) :=
    fun n => Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  exact Kernel.trajMeasure (Measure.dirac (0, s₀)) κ

/-- The canonical record trajectory measure is a probability measure. -/
theorem QMatrix.isProbabilityMeasure_canonicalRecordMeasure
    (Q : QMatrix S) (s₀ : S) :
    IsProbabilityMeasure (Q.canonicalRecordMeasure s₀) := by
  unfold QMatrix.canonicalRecordMeasure
  infer_instance

instance QMatrix.instIsProbabilityMeasureCanonicalRecordMeasure
    (Q : QMatrix S) (s₀ : S) :
    IsProbabilityMeasure (Q.canonicalRecordMeasure s₀) :=
  Q.isProbabilityMeasure_canonicalRecordMeasure s₀

/-- The initial one-coordinate history under the canonical record law is
deterministically `(0, s₀)`. -/
theorem QMatrix.canonicalRecordMeasure_map_frestrictLe_zero
    (Q : QMatrix S) (s₀ : S) :
    (Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe 0) =
      (Measure.dirac (0, s₀)).map
        (MeasurableEquiv.piUnique
          (fun i : Iic 0 => QMatrix.JumpHoldTrajectorySpace S i)).symm := by
  unfold QMatrix.canonicalRecordMeasure
  let κ := Q.jumpHoldTrajectoryStepKernel
  letI : ∀ n, IsMarkovKernel (κ n) :=
    fun n => Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  rw [Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe]
  simp

/-- Under the canonical record law, record `0` is almost surely the
deterministic initial marker `(0, s₀)`. -/
theorem QMatrix.canonicalRecordMeasure_record_zero_eq_init_ae
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, records 0 = (0, s₀) := by
  let e := (MeasurableEquiv.piUnique
    (fun i : Iic 0 => QMatrix.JumpHoldTrajectorySpace S i)).symm
  have hhist :
      ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe 0),
        hist = e (0, s₀) := by
    rw [Q.canonicalRecordMeasure_map_frestrictLe_zero s₀]
    simp [e]
  have hrecords :
      ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
        Preorder.frestrictLe 0 records = e (0, s₀) :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe 0).aemeasurable hhist
  filter_upwards [hrecords] with records hrecords
  have hcoord := congrFun hrecords ⟨0, mem_Iic.mpr le_rfl⟩
  simpa [e] using hcoord

/-- The joint law of the history through step `n` and the next record is the
history marginal composed with the history-dependent jump-hold step kernel.
This is the main Ionescu-Tulcea identity used to derive conditional and
marginal path laws. -/
theorem QMatrix.canonicalRecordMeasure_history_next
    (Q : QMatrix S) (s₀ : S) (n : ℕ) :
    (Q.canonicalRecordMeasure s₀).map
        (fun records => (Preorder.frestrictLe n records, records (n + 1))) =
      (Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n) ⊗ₘ
        Q.jumpHoldTrajectoryStepKernel n := by
  unfold QMatrix.canonicalRecordMeasure
  let κ := Q.jumpHoldTrajectoryStepKernel
  letI : ∀ n, IsMarkovKernel (κ n) :=
    fun n => Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  exact (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (μ₀ := Measure.dirac (0, s₀)) (κ := κ) (a := n)).symm

/-- Under the canonical record law, conditional on a non-absorbing history
through step `n`, the next sampled holding time is positive almost surely. -/
theorem QMatrix.canonicalRecordMeasure_next_holdingTime_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1 := by
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z =>
      ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) → 0 < z.2.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_pos : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) | 0 < z.2.1} := by
      exact (measurable_fst.comp measurable_snd) measurableSet_Ioi
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) | 0 < z.2.1} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.union h_pos
  have hkernel :
      ∀ᵐ hist ∂μ.map X,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · filter_upwards with r
      intro hnon
      exact (hnon h).elim
    · exact (Q.jumpHoldTrajectoryStepKernel_holdingTime_pos_ae_of_nonabsorbing n hist h).mono
        (fun r hr _hnon => hr)
  have hpair : ∀ᵐ z ∂(μ.map fun records => (X records, Y records)), p z := by
    rw [show μ.map (fun records => (X records, Y records)) =
        μ.map (fun records => (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map X = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show Q.jumpHoldTrajectoryStepKernel n = Q.jumpHoldTrajectoryStepKernel n by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (X records, Y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, X, Y, p] using hrecords

/-- Countable-intersection version of
`canonicalRecordMeasure_next_holdingTime_pos_ae_of_nonabsorbing`: under the
canonical record law, all next sampled holding times are positive whenever the
corresponding finite history is non-absorbing. -/
theorem QMatrix.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        0 < (records (n + 1)).1 := by
  exact ae_all_iff.mpr fun n =>
    Q.canonicalRecordMeasure_next_holdingTime_pos_ae_of_nonabsorbing s₀ n

/-- Under the canonical record law, conditional on a non-absorbing history
through step `n`, the next sampled state differs from the current state almost
surely. -/
theorem QMatrix.canonicalRecordMeasure_next_state_ne_current_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z =>
      ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.2 ≠ QMatrix.currentStateFromHistory (S := S) n z.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_ne : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 ≠ QMatrix.currentStateFromHistory (S := S) n z.1} := by
      have h_eq : MeasurableSet
          {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
              QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
            z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1} :=
        measurableSet_eq_fun (measurable_snd.comp measurable_snd)
          ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
      convert h_eq.compl using 1
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 ≠ QMatrix.currentStateFromHistory (S := S) n z.1} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.union h_ne
  have hkernel :
      ∀ᵐ hist ∂μ.map X,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · filter_upwards with r
      intro hnon
      exact (hnon h).elim
    · exact (Q.jumpHoldTrajectoryStepKernel_next_ne_current_ae_of_nonabsorbing n hist h).mono
        (fun r hr _hnon => hr)
  have hpair : ∀ᵐ z ∂(μ.map fun records => (X records, Y records)), p z := by
    rw [show μ.map (fun records => (X records, Y records)) =
        μ.map (fun records => (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map X = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (X records, Y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, X, Y, p] using hrecords

/-- Countable-intersection version of
`canonicalRecordMeasure_next_state_ne_current_ae_of_nonabsorbing`. -/
theorem QMatrix.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 ≠
          QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  exact ae_all_iff.mpr fun n =>
    Q.canonicalRecordMeasure_next_state_ne_current_ae_of_nonabsorbing s₀ n

/-- Under the canonical record law, once a history is in an absorbing state,
the next sampled state is the same state almost surely. -/
theorem QMatrix.canonicalRecordMeasure_all_next_state_eq_current_ae_of_absorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).2 =
          QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) := by
  refine ae_all_iff.mpr ?_
  intro n
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z =>
      Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_eq : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_snd)
        ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          ¬ Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.2 = QMatrix.currentStateFromHistory (S := S) n z.1} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.compl.union h_eq
  have hkernel :
      ∀ᵐ hist ∂μ.map X,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · have hdirac :
          Q.jumpHoldTrajectoryStepKernel n hist =
            Measure.dirac
              (0, QMatrix.currentStateFromHistory (S := S) n hist) := by
        rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
          Q.jumpHoldStepMeasureTotal_of_absorbing h]
      rw [hdirac]
      simp [p, h]
    · filter_upwards with r
      intro hAbs
      exact (h hAbs).elim
  have hpair : ∀ᵐ z ∂(μ.map fun records => (X records, Y records)), p z := by
    rw [show μ.map (fun records => (X records, Y records)) =
        μ.map (fun records => (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map X = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (X records, Y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, X, Y, p] using hrecords

/-- Under the canonical record law, once a history is absorbing, the next
sampled holding time is the terminal marker `0` almost surely. -/
theorem QMatrix.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        (records (n + 1)).1 = 0 := by
  refine ae_all_iff.mpr ?_
  intro n
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z =>
      Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) →
        z.2.1 = 0
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_eq : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.1 = (0 : ℝ)} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          ¬ Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          z.2.1 = (0 : ℝ)} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.compl.union h_eq
  have hkernel :
      ∀ᵐ hist ∂μ.map X,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · have hdirac :
          Q.jumpHoldTrajectoryStepKernel n hist =
            Measure.dirac
              (0, QMatrix.currentStateFromHistory (S := S) n hist) := by
        rw [Q.jumpHoldTrajectoryStepKernel_apply, Q.jumpHoldStepKernel_apply,
          Q.jumpHoldStepMeasureTotal_of_absorbing h]
      rw [hdirac]
      simp [p, h]
    · filter_upwards with r
      intro hAbs
      exact (h hAbs).elim
  have hpair : ∀ᵐ z ∂(μ.map fun records => (X records, Y records)), p z := by
    rw [show μ.map (fun records => (X records, Y records)) =
        μ.map (fun records => (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map X = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (X records, Y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, X, Y, p] using hrecords

/-- Under the canonical record law, every sampled next holding time is
nonnegative.  Non-absorbing histories sample a positive holding time, while
absorbing histories use the terminal marker `0`. -/
theorem QMatrix.canonicalRecordMeasure_all_next_holdingTime_nonneg_ae
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      0 ≤ (records (n + 1)).1 := by
  filter_upwards
    [Q.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing s₀,
      Q.canonicalRecordMeasure_all_next_holdingTime_eq_zero_ae_of_absorbing s₀]
    with records hpos hzero n
  by_cases h :
      Q.IsAbsorbing
        (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records))
  · exact le_of_eq (hzero n h).symm
  · exact le_of_lt (hpos n h)

/-- Under the canonical record law, conditional on a non-absorbing history
through step `n`, the next sampled state has positive generator rate almost
surely. -/
theorem QMatrix.canonicalRecordMeasure_next_rate_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        0 < Q.rate
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records))
          (records (n + 1)).2 := by
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  let p :
      (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
        QMatrix.JumpHoldTrajectorySpace S (n + 1)) → Prop :=
    fun z =>
      ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1) →
        0 < Q.rate (QMatrix.currentStateFromHistory (S := S) n z.1) z.2.2
  have hp : MeasurableSet {z | p z} := by
    have h_abs : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} := by
      exact ((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
        ((Set.to_countable {s : S | Q.IsAbsorbing s}).measurableSet)
    have h_rate_pos : MeasurableSet
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          0 < Q.rate (QMatrix.currentStateFromHistory (S := S) n z.1) z.2.2} := by
      let E : Finset (S × S) := Finset.univ.filter fun st => 0 < Q.rate st.1 st.2
      have h_single : ∀ st : S × S, MeasurableSet
          {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
              QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
            QMatrix.currentStateFromHistory (S := S) n z.1 = st.1 ∧
              z.2.2 = st.2} := by
        intro st
        exact
          (((QMatrix.measurable_currentStateFromHistory (S := S) n).comp measurable_fst)
            (measurableSet_singleton st.1)).inter
            ((measurable_snd.comp measurable_snd) (measurableSet_singleton st.2))
      rw [show {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          0 < Q.rate (QMatrix.currentStateFromHistory (S := S) n z.1) z.2.2} =
          ⋃ st ∈ E,
            {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
                QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
              QMatrix.currentStateFromHistory (S := S) n z.1 = st.1 ∧
                z.2.2 = st.2} by
        ext z
        simp [E]]
      exact Finset.measurableSet_biUnion E fun st _ => h_single st
    rw [show {z | p z} =
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)} ∪
        {z : (((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) ×
            QMatrix.JumpHoldTrajectorySpace S (n + 1)) |
          0 < Q.rate (QMatrix.currentStateFromHistory (S := S) n z.1) z.2.2} by
      ext z
      by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n z.1)
      · simp [p, h]
      · simp [p, h]]
    exact h_abs.union h_rate_pos
  have hkernel :
      ∀ᵐ hist ∂μ.map X,
        ∀ᵐ r ∂Q.jumpHoldTrajectoryStepKernel n hist, p (hist, r) := by
    refine Filter.Eventually.of_forall ?_
    intro hist
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · filter_upwards with r
      intro hnon
      exact (hnon h).elim
    · exact (Q.jumpHoldTrajectoryStepKernel_next_rate_pos_ae_of_nonabsorbing n hist h).mono
        (fun r hr _hnon => hr)
  have hpair : ∀ᵐ z ∂(μ.map fun records => (X records, Y records)), p z := by
    rw [show μ.map (fun records => (X records, Y records)) =
        μ.map (fun records => (Preorder.frestrictLe n records, records (n + 1))) by
          rfl]
    rw [show μ.map X = μ.map (Preorder.frestrictLe n) by rfl] at hkernel
    rw [show μ = Q.canonicalRecordMeasure s₀ by rfl]
    rw [Q.canonicalRecordMeasure_history_next s₀ n]
    exact Measure.ae_compProd_of_ae_ae hp hkernel
  have hrecords : ∀ᵐ records ∂μ, p (X records, Y records) :=
    MeasureTheory.ae_of_ae_map (by fun_prop) hpair
  simpa [μ, X, Y, p] using hrecords

/-- Countable-intersection version of
`canonicalRecordMeasure_next_rate_pos_ae_of_nonabsorbing`. -/
theorem QMatrix.canonicalRecordMeasure_all_next_rate_pos_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀, ∀ n,
      ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records)) →
        0 < Q.rate
          (QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records))
          (records (n + 1)).2 := by
  exact ae_all_iff.mpr fun n =>
    Q.canonicalRecordMeasure_next_rate_pos_ae_of_nonabsorbing s₀ n

/-- Conditional distribution of the next record given the history through
step `n`, specialized from Mathlib's Ionescu-Tulcea conditional distribution
theorem. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    condDistrib
        (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
          records (n + 1))
        (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀)
      =ᵐ[(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n)]
        Q.jumpHoldTrajectoryStepKernel n := by
  unfold QMatrix.canonicalRecordMeasure
  let κ := Q.jumpHoldTrajectoryStepKernel
  letI : ∀ n, IsMarkovKernel (κ n) :=
    fun n => Q.isMarkovKernel_jumpHoldTrajectoryStepKernel n
  exact Kernel.condDistrib_trajMeasure (μ₀ := Measure.dirac (0, s₀)) (κ := κ) (a := n)

/-- Almost every non-absorbing history has next-record conditional law equal
to the one-step product jump-hold law at the current state. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      ∀ h : ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) n hist),
        condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              records (n + 1))
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist =
          Q.jumpHoldStepMeasure h := by
  filter_upwards [Q.condDistrib_canonicalRecordMeasure_next s₀ n] with hist hhist h
  rw [hhist, Q.jumpHoldTrajectoryStepKernel_of_nonabsorbing n hist h]

/-- Almost every absorbing history has next-record conditional law equal to
the terminal record marker. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_of_absorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist) →
        condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              records (n + 1))
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist =
          Measure.dirac
            (0, QMatrix.currentStateFromHistory (S := S) n hist) := by
  filter_upwards [Q.condDistrib_canonicalRecordMeasure_next s₀ n] with hist hhist h
  rw [hhist, Q.jumpHoldTrajectoryStepKernel_of_absorbing n hist h]

/-- Conditional distribution of the next holding time given the record history
through step `n`, expressed as the first-coordinate marginal of the canonical
next-record kernel. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    condDistrib
        (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
          (records (n + 1)).1)
        (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀)
      =ᵐ[(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n)]
        (Q.jumpHoldTrajectoryStepKernel n).map Prod.fst := by
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  have hcomp :
      condDistrib (Prod.fst ∘ Y) (Preorder.frestrictLe n)
          (Q.canonicalRecordMeasure s₀)
        =ᵐ[(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n)]
          (condDistrib Y (Preorder.frestrictLe n)
            (Q.canonicalRecordMeasure s₀)).map Prod.fst :=
    condDistrib_comp (X := Preorder.frestrictLe n) (Y := Y)
      (μ := Q.canonicalRecordMeasure s₀) (f := Prod.fst) (by fun_prop) measurable_fst
  have hnext := Q.condDistrib_canonicalRecordMeasure_next s₀ n
  have hmap :
      (condDistrib Y (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀)).map Prod.fst
        =ᵐ[(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n)]
          (Q.jumpHoldTrajectoryStepKernel n).map Prod.fst := by
    filter_upwards [hnext] with hist hhist
    ext A hA
    rw [Kernel.map_apply' _ measurable_fst _ hA,
      Kernel.map_apply' _ measurable_fst _ hA, hhist]
  simpa [Y, Function.comp_def] using hcomp.trans hmap

/-- Conditional distribution of the next state given the record history through
step `n`, expressed as the second-coordinate marginal of the canonical
next-record kernel. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_state
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace S] [Nonempty S] :
    condDistrib
        (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
          (records (n + 1)).2)
        (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀)
      =ᵐ[(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n)]
        (Q.jumpHoldTrajectoryStepKernel n).map Prod.snd := by
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      QMatrix.JumpHoldTrajectorySpace S (n + 1) :=
    fun records => records (n + 1)
  have hcomp :
      condDistrib (Prod.snd ∘ Y) (Preorder.frestrictLe n)
          (Q.canonicalRecordMeasure s₀)
        =ᵐ[(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n)]
          (condDistrib Y (Preorder.frestrictLe n)
            (Q.canonicalRecordMeasure s₀)).map Prod.snd :=
    condDistrib_comp (X := Preorder.frestrictLe n) (Y := Y)
      (μ := Q.canonicalRecordMeasure s₀) (f := Prod.snd) (by fun_prop) measurable_snd
  have hnext := Q.condDistrib_canonicalRecordMeasure_next s₀ n
  have hmap :
      (condDistrib Y (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀)).map Prod.snd
        =ᵐ[(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n)]
          (Q.jumpHoldTrajectoryStepKernel n).map Prod.snd := by
    filter_upwards [hnext] with hist hhist
    ext A hA
    rw [Kernel.map_apply' _ measurable_snd _ hA,
      Kernel.map_apply' _ measurable_snd _ hA, hhist]
  simpa [Y, Function.comp_def] using hcomp.trans hmap

/-- Almost every non-absorbing history has next holding-time conditional law
equal to the exponential holding-time law of its current state. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      ∀ h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist),
        condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).1)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist =
          Q.holdingTimeMeasure h := by
  filter_upwards [Q.condDistrib_canonicalRecordMeasure_next_holdingTime s₀ n] with hist hhist h
  rw [hhist, Kernel.map_apply _ measurable_fst,
    Q.jumpHoldTrajectoryStepKernel_map_fst_of_nonabsorbing n hist h]

/-- Almost every non-absorbing history has next-holding-time conditional mean
equal to the reciprocal of its current exit rate. -/
theorem QMatrix.integral_condDistrib_next_holdingTime_eq_inv_exitRate_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      ∀ _h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist),
        (∫ t : ℝ,
            t ∂condDistrib
              (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
                (records (n + 1)).1)
              (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist) =
          (Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist))⁻¹ := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
    with hist hhist h
  rw [hhist h]
  exact Q.integral_holdingTimeMeasure_eq_inv_exitRate h

/-- Almost every non-absorbing history has next-holding-time conditional
second moment equal to `2 / exitRate^2`. -/
theorem QMatrix.integral_condDistrib_next_holdingTime_sq_eq_two_div_exitRate_sq_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      ∀ _h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist),
        (∫ t : ℝ,
            t ^ 2 ∂condDistrib
              (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
                (records (n + 1)).1)
              (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist) =
          2 * (1 / Q.exitRate
            (QMatrix.currentStateFromHistory (S := S) n hist)) ^ 2 := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
    with hist hhist h
  rw [hhist h]
  exact Q.integral_holdingTimeMeasure_sq_eq_two_mul_inv_sq h

/-- Almost every non-absorbing history assigns positive conditional
probability to every nonnegative holding-time tail for the next step. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_Ioi_pos_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      ∀ _h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist),
        0 <
          condDistrib
              (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
                (records (n + 1)).1)
              (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist
            (Set.Ioi δ) := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
    with hist hhist h
  rw [hhist h]
  exact Q.holdingTimeMeasure_Ioi_pos h hδ

/-- Almost every non-absorbing history has the state-uniform exponential
tail lower bound for the next holding-time conditional law. -/
theorem QMatrix.condDistrib_next_holdingTime_Ioi_ge_uniformRate_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    [Nonempty S]
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      ∀ _h : ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist),
        Real.exp (-(Q.uniformRate * δ)) ≤
          (condDistrib
              (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
                (records (n + 1)).1)
              (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist).real
            (Set.Ioi δ) := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
    with hist hhist h
  rw [hhist h]
  exact Q.holdingTimeMeasure_real_Ioi_ge_uniformRate h hδ

/-- Under a no-absorbing-state hypothesis, the conditional expectation of the
next raw holding-time tail indicator, given the record history through `n`, is
bounded below by the uniform exponential tail. -/
theorem QMatrix.condExp_next_holdingTime_Ioi_ge_uniformRate_of_no_absorbing
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s)
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    [Nonempty S]
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      Real.exp (-(Q.uniformRate * δ)) ≤
        MeasureTheory.condExp
          (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
          (Q.canonicalRecordMeasure s₀)
          (((fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
            (records (n + 1)).1) ⁻¹' Set.Ioi δ).indicator fun _ => (1 : ℝ))
          records := by
  let μ := Q.canonicalRecordMeasure s₀
  let X : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
      ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have htail_hist :
      ∀ᵐ hist ∂μ.map X,
        Real.exp (-(Q.uniformRate * δ)) ≤
          (ProbabilityTheory.condDistrib Y X μ hist).real (Set.Ioi δ) := by
    unfold μ X Y
    filter_upwards
      [Q.condDistrib_next_holdingTime_Ioi_ge_uniformRate_of_nonabsorbing s₀ n hδ]
      with hist hhist
    exact hhist (h_no_abs _)
  have htail_records :
      ∀ᵐ records ∂μ,
        Real.exp (-(Q.uniformRate * δ)) ≤
          (ProbabilityTheory.condDistrib Y X μ (X records)).real (Set.Ioi δ) :=
    MeasureTheory.ae_of_ae_map (Preorder.measurable_frestrictLe n).aemeasurable htail_hist
  have hcond :
      (fun records =>
        (ProbabilityTheory.condDistrib Y X μ (X records)).real (Set.Ioi δ))
        =ᵐ[μ]
        MeasureTheory.condExp (MeasurableSpace.comap X inferInstance) μ
          ((Y ⁻¹' Set.Ioi δ).indicator fun _ => (1 : ℝ)) :=
    ProbabilityTheory.condDistrib_ae_eq_condExp
      (X := X) (Y := Y) (μ := μ) (s := Set.Ioi δ)
      (Preorder.measurable_frestrictLe n) (by fun_prop) measurableSet_Ioi
  filter_upwards [htail_records, hcond] with records htail hcond_eq
  simpa [μ, X, Y, Function.comp_def, hcond_eq] using htail

/-- Almost every absorbing history has next holding-time conditional law equal
to the terminal marker `0`. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist) →
        condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).1)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist =
          Measure.dirac 0 := by
  filter_upwards [Q.condDistrib_canonicalRecordMeasure_next_holdingTime s₀ n] with hist hhist h
  rw [hhist, Kernel.map_apply _ measurable_fst,
    Q.jumpHoldTrajectoryStepKernel_map_fst_of_absorbing n hist h]

/-- Almost every non-absorbing history has next-state conditional law equal to
the embedded jump-chain row of its current state. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_state_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace S] [Nonempty S] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      ¬Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist) →
        condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).2)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist =
          Q.embeddedStepMeasure (QMatrix.currentStateFromHistory (S := S) n hist) := by
  filter_upwards [Q.condDistrib_canonicalRecordMeasure_next_state s₀ n] with hist hhist h
  rw [hhist, Kernel.map_apply _ measurable_snd,
    Q.jumpHoldTrajectoryStepKernel_map_snd_of_nonabsorbing n hist h]

/-- Almost every absorbing history has next-state conditional law equal to the
terminal current-state marker. -/
theorem QMatrix.condDistrib_canonicalRecordMeasure_next_state_of_absorbing
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace S] [Nonempty S] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist) →
        condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).2)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist =
          Measure.dirac (QMatrix.currentStateFromHistory (S := S) n hist) := by
  filter_upwards [Q.condDistrib_canonicalRecordMeasure_next_state s₀ n] with hist hhist h
  rw [hhist, Kernel.map_apply _ measurable_snd,
    Q.jumpHoldTrajectoryStepKernel_map_snd_of_absorbing n hist h]

theorem QMatrix.integral_condDistrib_next_holdingTime_eq_inv_exitRate
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      (∫ t : ℝ,
          t ∂condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).1)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist) =
        (Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist))⁻¹ := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
      Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n]
    with hist hnonabs habs
  by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
  · rw [habs h]
    have hzero : Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist) = 0 :=
      h
    simp [hzero]
  · rw [hnonabs h]
    exact Q.integral_holdingTimeMeasure_eq_inv_exitRate h

theorem QMatrix.integral_condDistrib_next_holdingTime_sq_eq_two_div_exitRate_sq
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ hist ∂(Q.canonicalRecordMeasure s₀).map (Preorder.frestrictLe n),
      (∫ t : ℝ,
          t ^ 2 ∂condDistrib
            (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
              (records (n + 1)).1)
            (Preorder.frestrictLe n) (Q.canonicalRecordMeasure s₀) hist) =
        2 * (1 / Q.exitRate
          (QMatrix.currentStateFromHistory (S := S) n hist)) ^ 2 := by
  filter_upwards
    [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
      Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n]
    with hist hnonabs habs
  by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
  · rw [habs h]
    have hzero : Q.exitRate (QMatrix.currentStateFromHistory (S := S) n hist) = 0 :=
      h
    simp [hzero]
  · rw [hnonabs h]
    exact Q.integral_holdingTimeMeasure_sq_eq_two_mul_inv_sq h

set_option maxHeartbeats 800000 in
theorem QMatrix.integrable_next_holdingTime_canonicalRecordMeasure_guarded
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    Integrable
      (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
        (records (n + 1)).1)
      (Q.canonicalRecordMeasure s₀) := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hY_meas : AEMeasurable Y μ := by fun_prop
  have hX_meas : Measurable X := Preorder.measurable_frestrictLe n
  suffices h : Integrable (Prod.snd : _ × ℝ → ℝ)
      (μ.map fun records => (X records, Y records)) from
    (integrable_map_measure measurable_snd.aestronglyMeasurable
      (hX_meas.aemeasurable.prodMk hY_meas)).mp h
  rw [← MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    hY_meas measurable_snd.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards
      [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
        Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n]
      with hist hnonabs habs
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · rw [habs h]
      exact MeasureTheory.integrable_dirac (by simp :
        ‖((fun t : ℝ => t) (0 : ℝ))‖ₑ < ∞)
    · rw [hnonabs h]
      exact Q.integrable_holdingTimeMeasure_id h
  · obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ s : S, (Q.exitRate s)⁻¹ ≤ C :=
      ⟨Finset.univ.sup' ⟨s₀, Finset.mem_univ s₀⟩ (fun s => (Q.exitRate s)⁻¹),
       fun s => by
        exact Finset.le_sup'
          (s := (Finset.univ : Finset S))
          (f := fun s => (Q.exitRate s)⁻¹)
          (Finset.mem_univ s)⟩
    have hC_nonneg : 0 ≤ C :=
      (inv_nonneg.mpr (Q.exitRate_nonneg s₀)).trans (hC s₀)
    exact Integrable.of_bound
      (measurable_snd.norm.aestronglyMeasurable.integral_condDistrib_map hY_meas)
      C
      (by filter_upwards
            [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
              Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n]
            with hist hnonabs habs
          by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
          · rw [habs h]
            simp [hC_nonneg]
          · rw [hnonabs h, Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg t))]
            calc ∫ t : ℝ, ‖t‖ ∂Q.holdingTimeMeasure h
                  = ∫ t : ℝ, t ∂Q.holdingTimeMeasure h := by
                    apply integral_congr_ae
                    filter_upwards [Q.holdingTimeMeasure_pos_ae h] with t ht
                    exact Real.norm_of_nonneg (le_of_lt ht)
                _ = (Q.exitRate (QMatrix.currentStateFromHistory n hist))⁻¹ :=
                    Q.integral_holdingTimeMeasure_eq_inv_exitRate h
                _ ≤ C := hC _)

set_option maxHeartbeats 800000 in
theorem QMatrix.integrable_next_holdingTime_sq_canonicalRecordMeasure_guarded
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    Integrable
      (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
        (records (n + 1)).1 ^ 2)
      (Q.canonicalRecordMeasure s₀) := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hY_meas : AEMeasurable Y μ := by fun_prop
  have hX_meas : Measurable X := Preorder.measurable_frestrictLe n
  have hf_sm : StronglyMeasurable (fun t : ℝ => t ^ 2) := by fun_prop
  suffices h : Integrable ((fun t : ℝ => t ^ 2) ∘ (Prod.snd : _ × ℝ → ℝ))
      (μ.map fun records => (X records, Y records)) from
    (integrable_map_measure
      (hf_sm.comp_measurable measurable_snd).aestronglyMeasurable
      (hX_meas.aemeasurable.prodMk hY_meas)).mp h
  rw [← MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    hY_meas (hf_sm.comp_measurable measurable_snd).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards
      [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
        Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n]
      with hist hnonabs habs
    by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
    · rw [habs h]
      exact MeasureTheory.integrable_dirac (by simp :
        ‖((fun t : ℝ => t ^ 2) (0 : ℝ))‖ₑ < ∞)
    · rw [hnonabs h]
      exact Q.integrable_holdingTimeMeasure_sq h
  · obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ s : S, 2 * (1 / Q.exitRate s) ^ 2 ≤ C :=
      ⟨Finset.univ.sup' ⟨s₀, Finset.mem_univ s₀⟩
        (fun s => 2 * (1 / Q.exitRate s) ^ 2),
       fun s => by
        exact Finset.le_sup'
          (s := (Finset.univ : Finset S))
          (f := fun s => 2 * (1 / Q.exitRate s) ^ 2)
          (Finset.mem_univ s)⟩
    have hC_nonneg : 0 ≤ C := by
      have hbase : 0 ≤ 2 * (1 / Q.exitRate s₀) ^ 2 := by positivity
      exact hbase.trans (hC s₀)
    exact Integrable.of_bound
      ((hf_sm.comp_measurable measurable_snd).norm.aestronglyMeasurable.integral_condDistrib_map
        hY_meas)
      C
      (by filter_upwards
            [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n,
              Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_absorbing s₀ n]
            with hist hnonabs habs
          by_cases h : Q.IsAbsorbing (QMatrix.currentStateFromHistory (S := S) n hist)
          · rw [habs h]
            simp [hC_nonneg]
          · rw [hnonabs h]
            rw [Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg _))]
            calc ∫ t : ℝ, ‖t ^ 2‖ ∂Q.holdingTimeMeasure h
                  = ∫ t : ℝ, t ^ 2 ∂Q.holdingTimeMeasure h := by
                    apply integral_congr_ae
                    filter_upwards [Q.holdingTimeMeasure_pos_ae h] with t ht
                    exact Real.norm_of_nonneg (sq_nonneg t)
                _ = 2 * (1 / Q.exitRate (QMatrix.currentStateFromHistory n hist)) ^ 2 :=
                    Q.integral_holdingTimeMeasure_sq_eq_two_mul_inv_sq h
                _ ≤ C := hC _)

theorem QMatrix.condExp_next_holdingTime_eq_inv_exitRate
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      MeasureTheory.condExp
        (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
        (Q.canonicalRecordMeasure s₀)
        (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
          (records (n + 1)).1)
        records =
      (Q.exitRate (QMatrix.currentStateFromHistory (S := S) n
        (Preorder.frestrictLe n records)))⁻¹ := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hinteg := Q.integrable_next_holdingTime_canonicalRecordMeasure_guarded s₀ n
  have hcondExp := condExp_ae_eq_integral_condDistrib'
    (Preorder.measurable_frestrictLe n) hinteg
  have hcondDist :=
    Q.integral_condDistrib_next_holdingTime_eq_inv_exitRate s₀ n
  filter_upwards [hcondExp,
    MeasureTheory.ae_of_ae_map
      (Preorder.measurable_frestrictLe n).aemeasurable hcondDist]
    with records hce hcd
  rw [hce]
  exact hcd

theorem QMatrix.condExp_next_holdingTime_sq_eq_two_div_exitRate_sq
    (Q : QMatrix S) (s₀ : S) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      MeasureTheory.condExp
        (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
        (Q.canonicalRecordMeasure s₀)
        (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
          (records (n + 1)).1 ^ 2)
        records =
      2 * (1 / Q.exitRate (QMatrix.currentStateFromHistory (S := S) n
        (Preorder.frestrictLe n records))) ^ 2 := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hinteg := Q.integrable_next_holdingTime_sq_canonicalRecordMeasure_guarded s₀ n
  have hf_sm : StronglyMeasurable (fun t : ℝ => t ^ 2) := by fun_prop
  have hcondExp := condExp_ae_eq_integral_condDistrib
    (Preorder.measurable_frestrictLe n)
    (by fun_prop : AEMeasurable Y μ) hf_sm hinteg
  have hcondDist :=
    Q.integral_condDistrib_next_holdingTime_sq_eq_two_div_exitRate_sq s₀ n
  filter_upwards [hcondExp,
    MeasureTheory.ae_of_ae_map
      (Preorder.measurable_frestrictLe n).aemeasurable hcondDist]
    with records hce hcd
  rw [hce]
  exact hcd

set_option maxHeartbeats 800000 in
-- The disintegration/integrability bridge elaborates several dependent product
-- spaces and conditional-distribution kernels.
/-- The next holding time is integrable under the canonical record law
when all states are non-absorbing.  Proved via the tower property:
conditionally (given history through step n), the holding time has
exponential law with finite mean, and the conditional mean is bounded
over all states. -/
theorem QMatrix.integrable_next_holdingTime_canonicalRecordMeasure
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    Integrable
      (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
        (records (n + 1)).1)
      (Q.canonicalRecordMeasure s₀) := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hY_meas : AEMeasurable Y μ := by fun_prop
  have hX_meas : Measurable X := Preorder.measurable_frestrictLe n
  suffices h : Integrable (Prod.snd : _ × ℝ → ℝ)
      (μ.map fun records => (X records, Y records)) from
    (integrable_map_measure measurable_snd.aestronglyMeasurable
      (hX_meas.aemeasurable.prodMk hY_meas)).mp h
  rw [← MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    hY_meas measurable_snd.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards
      [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
      with hist hhist
    rw [hhist (h_no_abs _)]
    exact Q.integrable_holdingTimeMeasure_id (h_no_abs _)
  · obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ s : S, (Q.exitRate s)⁻¹ ≤ C :=
      ⟨Finset.univ.sup' ⟨s₀, Finset.mem_univ s₀⟩ (fun s => (Q.exitRate s)⁻¹),
       fun s => by
        exact Finset.le_sup'
          (s := (Finset.univ : Finset S))
          (f := fun s => (Q.exitRate s)⁻¹)
          (Finset.mem_univ s)⟩
    exact Integrable.of_bound
      (measurable_snd.norm.aestronglyMeasurable.integral_condDistrib_map hY_meas)
      C
      (by filter_upwards
            [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
            with hist hhist
          have h_na := h_no_abs (QMatrix.currentStateFromHistory n hist)
          rw [hhist h_na, Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg t))]
          calc ∫ t : ℝ, ‖t‖ ∂Q.holdingTimeMeasure h_na
                = ∫ t : ℝ, t ∂Q.holdingTimeMeasure h_na := by
                  apply integral_congr_ae
                  filter_upwards [Q.holdingTimeMeasure_pos_ae h_na] with t ht
                  exact Real.norm_of_nonneg (le_of_lt ht)
              _ = (Q.exitRate (QMatrix.currentStateFromHistory n hist))⁻¹ :=
                  Q.integral_holdingTimeMeasure_eq_inv_exitRate h_na
              _ ≤ C := hC _)

set_option maxHeartbeats 800000 in
-- Same disintegration bridge as above, with an extra square/norm composition.
/-- The squared next holding time is integrable under the canonical record law
when all states are non-absorbing. -/
theorem QMatrix.integrable_next_holdingTime_sq_canonicalRecordMeasure
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    Integrable
      (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
        (records (n + 1)).1 ^ 2)
      (Q.canonicalRecordMeasure s₀) := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hY_meas : AEMeasurable Y μ := by fun_prop
  have hX_meas : Measurable X := Preorder.measurable_frestrictLe n
  have hf_sm : StronglyMeasurable (fun t : ℝ => t ^ 2) := by fun_prop
  suffices h : Integrable ((fun t : ℝ => t ^ 2) ∘ (Prod.snd : _ × ℝ → ℝ))
      (μ.map fun records => (X records, Y records)) from
    (integrable_map_measure
      (hf_sm.comp_measurable measurable_snd).aestronglyMeasurable
      (hX_meas.aemeasurable.prodMk hY_meas)).mp h
  rw [← MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
    hY_meas (hf_sm.comp_measurable measurable_snd).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards
      [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
      with hist hhist
    rw [hhist (h_no_abs _)]
    exact Q.integrable_holdingTimeMeasure_sq (h_no_abs _)
  · obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ s : S, 2 * (1 / Q.exitRate s) ^ 2 ≤ C :=
      ⟨Finset.univ.sup' ⟨s₀, Finset.mem_univ s₀⟩
        (fun s => 2 * (1 / Q.exitRate s) ^ 2),
       fun s => by
        exact Finset.le_sup'
          (s := (Finset.univ : Finset S))
          (f := fun s => 2 * (1 / Q.exitRate s) ^ 2)
          (Finset.mem_univ s)⟩
    exact Integrable.of_bound
      ((hf_sm.comp_measurable measurable_snd).norm.aestronglyMeasurable.integral_condDistrib_map
        hY_meas)
      C
      (by filter_upwards
            [Q.condDistrib_canonicalRecordMeasure_next_holdingTime_of_nonabsorbing s₀ n]
            with hist hhist
          have h_na := h_no_abs (QMatrix.currentStateFromHistory n hist)
          rw [hhist h_na]
          rw [Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg _))]
          calc ∫ t : ℝ, ‖t ^ 2‖ ∂Q.holdingTimeMeasure h_na
                = ∫ t : ℝ, t ^ 2 ∂Q.holdingTimeMeasure h_na := by
                  apply integral_congr_ae
                  filter_upwards [Q.holdingTimeMeasure_pos_ae h_na] with t ht
                  exact Real.norm_of_nonneg (sq_nonneg t)
              _ = 2 * (1 / Q.exitRate (QMatrix.currentStateFromHistory n hist)) ^ 2 :=
                  Q.integral_holdingTimeMeasure_sq_eq_two_mul_inv_sq h_na
              _ ≤ C := hC _)

/-- Under a no-absorbing-state hypothesis, the conditional expectation of the
next holding time given the history through step n equals the reciprocal exit
rate of the current state, almost surely under the canonical record law. -/
theorem QMatrix.condExp_next_holdingTime_eq_inv_exitRate_of_no_absorbing
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      MeasureTheory.condExp
        (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
        (Q.canonicalRecordMeasure s₀)
        (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
          (records (n + 1)).1)
        records =
      (Q.exitRate (QMatrix.currentStateFromHistory (S := S) n
        (Preorder.frestrictLe n records)))⁻¹ := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hinteg := Q.integrable_next_holdingTime_canonicalRecordMeasure s₀ h_no_abs n
  have hcondExp := condExp_ae_eq_integral_condDistrib'
    (Preorder.measurable_frestrictLe n) hinteg
  have hcondDist :=
    Q.integral_condDistrib_next_holdingTime_eq_inv_exitRate_of_nonabsorbing s₀ n
  filter_upwards [hcondExp,
    MeasureTheory.ae_of_ae_map
      (Preorder.measurable_frestrictLe n).aemeasurable hcondDist]
    with records hce hcd
  rw [hce]
  exact hcd (h_no_abs _)

/-- Under a no-absorbing-state hypothesis, the conditional expectation of the
squared next holding time given the history through step n equals
`2 / exitRate^2` of the current state, almost surely. -/
theorem QMatrix.condExp_next_holdingTime_sq_eq_two_div_exitRate_sq_of_no_absorbing
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s) (n : ℕ)
    [StandardBorelSpace (QMatrix.JumpHoldTrajectorySpace S (n + 1))]
    [Nonempty (QMatrix.JumpHoldTrajectorySpace S (n + 1))] :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      MeasureTheory.condExp
        (MeasurableSpace.comap (Preorder.frestrictLe n) inferInstance)
        (Q.canonicalRecordMeasure s₀)
        (fun records : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
          (records (n + 1)).1 ^ 2)
        records =
      2 * (1 / Q.exitRate (QMatrix.currentStateFromHistory (S := S) n
        (Preorder.frestrictLe n records))) ^ 2 := by
  let μ := Q.canonicalRecordMeasure s₀
  let X :
      ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
        ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) :=
    Preorder.frestrictLe n
  let Y : ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) → ℝ :=
    fun records => (records (n + 1)).1
  have hinteg := Q.integrable_next_holdingTime_sq_canonicalRecordMeasure s₀ h_no_abs n
  have hf_sm : StronglyMeasurable (fun t : ℝ => t ^ 2) := by fun_prop
  have hcondExp := condExp_ae_eq_integral_condDistrib
    (Preorder.measurable_frestrictLe n)
    (by fun_prop : AEMeasurable Y μ) hf_sm hinteg
  have hcondDist :=
    Q.integral_condDistrib_next_holdingTime_sq_eq_two_div_exitRate_sq_of_nonabsorbing s₀ n
  filter_upwards [hcondExp,
    MeasureTheory.ae_of_ae_map
      (Preorder.measurable_frestrictLe n).aemeasurable hcondDist]
    with records hce hcd
  rw [hce]
  exact hcd (h_no_abs _)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- Deterministically read a `CTMCPath` from an infinite record trajectory. -/
noncomputable def QMatrix.recordTrajectoryToPath
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) : CTMCPath S where
  init := (records 0).2
  jumps n := (records (n + 1)).2
  times n := ∑ k ∈ Finset.range (n + 1), (records (k + 1)).1

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
@[simp]
theorem QMatrix.recordTrajectoryToPath_init
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) :
    (QMatrix.recordTrajectoryToPath records).init = (records 0).2 :=
  rfl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
@[simp]
theorem QMatrix.recordTrajectoryToPath_jumps
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) (n : ℕ) :
    (QMatrix.recordTrajectoryToPath records).jumps n = (records (n + 1)).2 :=
  rfl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
@[simp]
theorem QMatrix.recordTrajectoryToPath_times
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) (n : ℕ) :
    (QMatrix.recordTrajectoryToPath records).times n =
      ∑ k ∈ Finset.range (n + 1), (records (k + 1)).1 :=
  rfl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- The first jump time read from a record trajectory is the first sampled
holding time. -/
theorem QMatrix.recordTrajectoryToPath_times_zero
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) :
    (QMatrix.recordTrajectoryToPath records).times 0 = (records 1).1 := by
  simp [QMatrix.recordTrajectoryToPath]

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
@[simp]
theorem QMatrix.recordTrajectoryToPath_stateSeq
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) (n : ℕ) :
    (QMatrix.recordTrajectoryToPath records).stateSeq n = (records n).2 := by
  cases n <;> simp [QMatrix.recordTrajectoryToPath, CTMCPath.stateSeq]

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
@[simp]
theorem QMatrix.currentStateFromHistory_frestrictLe
    (records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) (n : ℕ) :
    QMatrix.currentStateFromHistory (S := S) n (Preorder.frestrictLe n records) =
      (QMatrix.recordTrajectoryToPath records).stateSeq n := by
  simp [QMatrix.currentStateFromHistory, QMatrix.recordTrajectoryToPath_stateSeq]

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- The next jump time is obtained by adding the next sampled holding time. -/
theorem QMatrix.recordTrajectoryToPath_times_succ
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) (n : ℕ) :
    (QMatrix.recordTrajectoryToPath records).times (n + 1) =
      (QMatrix.recordTrajectoryToPath records).times n + (records (n + 2)).1 := by
  simp [QMatrix.recordTrajectoryToPath, Finset.sum_range_succ, add_assoc]

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- The CTMCPath holding time after jump `n` is the sampled holding time in
record `n+2`.  The initial holding time is `times 0`, handled by
`recordTrajectoryToPath_times_zero`. -/
theorem QMatrix.recordTrajectoryToPath_holdingTime
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) (n : ℕ) :
    (QMatrix.recordTrajectoryToPath records).holdingTime n = (records (n + 2)).1 := by
  rw [CTMCPath.holdingTime_eq, QMatrix.recordTrajectoryToPath_times_succ]
  ring

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- The sojourn time spent in `stateSeq n` is the raw holding time stored in
record `n+1`.  This includes the initial sojourn, unlike
`recordTrajectoryToPath_holdingTime`, which is shifted by one jump. -/
theorem QMatrix.recordTrajectoryToPath_sojournTime
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n) (n : ℕ) :
    (QMatrix.recordTrajectoryToPath records).sojournTime n = (records (n + 1)).1 := by
  cases n with
  | zero =>
      simp [CTMCPath.sojournTime]
  | succ n =>
      rw [CTMCPath.sojournTime_succ, QMatrix.recordTrajectoryToPath_times_succ]
      ring

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The read-out state sequence at a fixed index is measurable as a function
of the record trajectory. -/
theorem QMatrix.measurable_recordTrajectoryToPath_stateSeq
    (n : ℕ) :
    Measurable (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
      (QMatrix.recordTrajectoryToPath records).stateSeq n) := by
  cases n with
  | zero =>
      simp only [CTMCPath.stateSeq_zero, QMatrix.recordTrajectoryToPath_init]
      fun_prop
  | succ n =>
      simp only [CTMCPath.stateSeq_succ, QMatrix.recordTrajectoryToPath_jumps]
      fun_prop

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The read-out jump time at a fixed index is measurable as a function of the
record trajectory. -/
theorem QMatrix.measurable_recordTrajectoryToPath_times
    (n : ℕ) :
    Measurable (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
      (QMatrix.recordTrajectoryToPath records).times n) := by
  simp only [QMatrix.recordTrajectoryToPath_times]
  fun_prop

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The read-out holding time at a fixed index is measurable as a function of
the record trajectory. -/
theorem QMatrix.measurable_recordTrajectoryToPath_holdingTime
    (n : ℕ) :
    Measurable (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
      (QMatrix.recordTrajectoryToPath records).holdingTime n) := by
  rw [show (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
      (QMatrix.recordTrajectoryToPath records).holdingTime n) =
      fun records => (records (n + 2)).1 from by
        funext records
        exact QMatrix.recordTrajectoryToPath_holdingTime records n]
  fun_prop

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The natural filtration on the canonical record trajectory space: at time
`n` it contains exactly the events depending on records up to index `n`. -/
def QMatrix.canonicalRecordFiltration :
    MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace
        ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m)) :=
  MeasureTheory.Filtration.piLE
    (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
@[simp]
theorem QMatrix.canonicalRecordFiltration_eq_piLE :
    QMatrix.canonicalRecordFiltration (S := S) =
      MeasureTheory.Filtration.piLE
        (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n) :=
  rfl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
theorem QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe
    (n : ℕ) :
    QMatrix.canonicalRecordFiltration (S := S) n =
      MeasurableSpace.pi.comap
        (Preorder.frestrictLe n :
          ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) →
            ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i)) := by
  simpa [QMatrix.canonicalRecordFiltration] using
    (MeasureTheory.Filtration.piLE_eq_comap_frestrictLe
      (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n) n)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The canonical record filtration shifted by one index.  This is the natural
filtration for clock-horizon jump-time events, because `times n` uses holding
records through index `n+1`. -/
def QMatrix.shiftedCanonicalRecordFiltration :
    MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace
        ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m)) where
  seq n := QMatrix.canonicalRecordFiltration (S := S) (n + 1)
  mono' := by
    intro n m hnm
    exact (QMatrix.canonicalRecordFiltration (S := S)).mono
      (Nat.succ_le_succ hnm)
  le' n := (QMatrix.canonicalRecordFiltration (S := S)).le (n + 1)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- A function of the record trajectory that factors through the finite history
up to `n` is measurable with respect to the canonical record filtration at
`n`. -/
theorem QMatrix.measurable_canonicalRecordFiltration_of_frestrictLe
    {E : Type*} [MeasurableSpace E] (n : ℕ)
    {g : ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) → E}
    (hg : Measurable g) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
        g (Preorder.frestrictLe n records)) := by
  rw [QMatrix.canonicalRecordFiltration_apply_eq_comap_frestrictLe (S := S) n]
  exact hg.comp (comap_measurable _)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The raw record at index `n` is measurable with respect to the canonical
history through `n`. -/
theorem QMatrix.measurable_record_canonicalRecordFiltration (n : ℕ) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
        records n) := by
  simpa using
    (QMatrix.measurable_canonicalRecordFiltration_of_frestrictLe
      (S := S) n
      (g := fun hist : ((i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i) =>
        hist ⟨n, mem_Iic.mpr le_rfl⟩)
      (by fun_prop))

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- Earlier raw records remain measurable with respect to later canonical
histories. -/
theorem QMatrix.measurable_record_canonicalRecordFiltration_le
    {k n : ℕ} (hkn : k ≤ n) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
        records k) :=
  (QMatrix.measurable_record_canonicalRecordFiltration (S := S) k).mono
    ((QMatrix.canonicalRecordFiltration (S := S)).mono hkn) le_rfl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The read-out `n`-th jump time depends only on raw records through
index `n+1`, since it is the sum of holding times in records `1, ..., n+1`. -/
theorem QMatrix.measurable_recordTrajectoryToPath_times_canonicalRecordFiltration
    (n : ℕ) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) (n + 1)]
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
        (QMatrix.recordTrajectoryToPath records).times n) := by
  simp only [QMatrix.recordTrajectoryToPath_times]
  refine Finset.measurable_sum _ ?_
  intro k hk
  have hk_le : k + 1 ≤ n + 1 := by
    exact Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  exact (QMatrix.measurable_record_canonicalRecordFiltration_le
    (S := S) hk_le).fst

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The read-out state sequence at index `n` is adapted to the canonical record
filtration through `n`. -/
theorem QMatrix.measurable_recordTrajectoryToPath_stateSeq_canonicalRecordFiltration
    (n : ℕ) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
        (QMatrix.recordTrajectoryToPath records).stateSeq n) := by
  simpa [QMatrix.recordTrajectoryToPath_stateSeq] using
    ((QMatrix.measurable_record_canonicalRecordFiltration (S := S) n).snd)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- Earlier read-out states remain measurable with respect to later canonical
histories. -/
theorem QMatrix.measurable_recordTrajectoryToPath_stateSeq_canonicalRecordFiltration_le
    {k n : ℕ} (hkn : k ≤ n) :
    Measurable[QMatrix.canonicalRecordFiltration (S := S) n]
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
        (QMatrix.recordTrajectoryToPath records).stateSeq k) := by
  simpa [QMatrix.recordTrajectoryToPath_stateSeq] using
    ((QMatrix.measurable_record_canonicalRecordFiltration_le
      (S := S) hkn).snd)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The event that the `n`-th raw record holding time is larger than `ε`
is measurable with respect to the canonical history filtration through `n`. -/
theorem QMatrix.measurableSet_record_holdingTime_Ioi_piLE
    (ε : ℝ) (n : ℕ) :
    MeasurableSet[MeasureTheory.Filtration.piLE
        (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n) n]
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        ε < (records n).1} := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe
    (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n) n]
  refine ⟨{hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i |
      ε < (hist ⟨n, mem_Iic.mpr le_rfl⟩).1}, ?_, ?_⟩
  · exact (show Measurable
        (fun hist : (i : Iic n) → QMatrix.JumpHoldTrajectorySpace S i =>
          (hist ⟨n, mem_Iic.mpr le_rfl⟩).1) by
        fun_prop) measurableSet_Ioi
  · ext records
    rfl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- Named-filtration version of
`QMatrix.measurableSet_record_holdingTime_Ioi_piLE`. -/
theorem QMatrix.measurableSet_record_holdingTime_Ioi_canonicalRecordFiltration
    (ε : ℝ) (n : ℕ) :
    MeasurableSet[QMatrix.canonicalRecordFiltration (S := S) n]
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        ε < (records n).1} := by
  simpa [QMatrix.canonicalRecordFiltration] using
    QMatrix.measurableSet_record_holdingTime_Ioi_piLE (S := S) ε n

/-- Under a no-absorbing-state hypothesis, raw record holding times exceed
any fixed positive threshold infinitely often in the strong count sense.  This
is the Lévy generalized Borel-Cantelli input for canonical non-explosion. -/
theorem QMatrix.canonicalRecordMeasure_raw_holdingTime_Ioi_count_tendsto_ae
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s)
    [StandardBorelSpace S] [Nonempty S] {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter fun k => ε < (records (k + 1)).1).card : ℝ))
        Filter.atTop Filter.atTop := by
  let μ := Q.canonicalRecordMeasure s₀
  let ℱ : MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace
        ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m)) :=
    MeasureTheory.Filtration.piLE
      (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n)
  let A : ℕ → Set ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) :=
    fun n => {records | ε < (records n).1}
  have hA_meas : ∀ n, MeasurableSet[ℱ n] (A n) := by
    intro n
    simpa [ℱ, A] using
      QMatrix.measurableSet_record_holdingTime_Ioi_piLE (S := S) ε n
  have hBC := MeasureTheory.tendsto_sum_indicator_atTop_iff'
    (μ := μ) (ℱ := ℱ) (s := A) hA_meas
  have htail : ∀ᵐ records ∂μ, ∀ k : ℕ,
      Real.exp (-(Q.uniformRate * ε)) ≤
        MeasureTheory.condExp (ℱ k) μ
          ((A (k + 1)).indicator fun _ => (1 : ℝ)) records := by
    rw [ae_all_iff]
    intro k
    have hk :=
      Q.condExp_next_holdingTime_Ioi_ge_uniformRate_of_no_absorbing
        s₀ h_no_abs k (le_of_lt hε)
    simpa [μ, ℱ, A, MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
      using hk
  filter_upwards [hBC, htail] with records hBC_records htail_records
  have hp : 0 < Real.exp (-(Q.uniformRate * ε)) := Real.exp_pos _
  have hpred : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        MeasureTheory.condExp (ℱ k) μ
          ((A (k + 1)).indicator fun _ => (1 : ℝ)) records)
      Filter.atTop Filter.atTop := by
    have hconst : Filter.Tendsto
        (fun n : ℕ => (n : ℝ) * Real.exp (-(Q.uniformRate * ε)))
        Filter.atTop Filter.atTop :=
      by simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop hp
    refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hconst
    filter_upwards with n
    calc
      (n : ℝ) * Real.exp (-(Q.uniformRate * ε))
          = ∑ k ∈ Finset.range n, Real.exp (-(Q.uniformRate * ε)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range n,
            MeasureTheory.condExp (ℱ k) μ
              ((A (k + 1)).indicator fun _ => (1 : ℝ)) records := by
            exact Finset.sum_le_sum fun k _ => htail_records k
  have hindicator : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        (A (k + 1)).indicator (fun _ => (1 : ℝ)) records)
      Filter.atTop Filter.atTop :=
    hBC_records.2 hpred
  refine hindicator.congr' ?_
  filter_upwards with n
  rw [Finset.sum_indicator_eq_sum_filter]
  simp [A]

/-- Under a no-absorbing-state hypothesis, the holding times in the read-out
`CTMCPath` exceed any fixed positive threshold unboundedly often, almost
surely. -/
theorem QMatrix.canonicalRecordMeasure_holdingTime_Ioi_count_tendsto_ae
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s)
    [StandardBorelSpace S] [Nonempty S] {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter fun k =>
            ε < (QMatrix.recordTrajectoryToPath records).holdingTime k).card : ℝ))
        Filter.atTop Filter.atTop := by
  let μ := Q.canonicalRecordMeasure s₀
  let ℱ : MeasureTheory.Filtration ℕ
      (inferInstance : MeasurableSpace
        ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m)) :=
    { seq := fun n => MeasureTheory.Filtration.piLE
        (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n) (n + 1)
      mono' := by
        intro i j hij
        exact (MeasureTheory.Filtration.piLE
          (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n)).mono
            (Nat.succ_le_succ hij)
      le' := by
        intro i
        exact (MeasureTheory.Filtration.piLE
          (X := fun n : ℕ => QMatrix.JumpHoldTrajectorySpace S n)).le (i + 1) }
  let A : ℕ → Set ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) :=
    fun n => {records | ε < (records (n + 1)).1}
  have hA_meas : ∀ n, MeasurableSet[ℱ n] (A n) := by
    intro n
    simpa [ℱ, A] using
      QMatrix.measurableSet_record_holdingTime_Ioi_piLE (S := S) ε (n + 1)
  have hBC := MeasureTheory.tendsto_sum_indicator_atTop_iff'
    (μ := μ) (ℱ := ℱ) (s := A) hA_meas
  have htail : ∀ᵐ records ∂μ, ∀ k : ℕ,
      Real.exp (-(Q.uniformRate * ε)) ≤
        MeasureTheory.condExp (ℱ k) μ
          ((A (k + 1)).indicator fun _ => (1 : ℝ)) records := by
    rw [ae_all_iff]
    intro k
    have hk :=
      Q.condExp_next_holdingTime_Ioi_ge_uniformRate_of_no_absorbing
        s₀ h_no_abs (k + 1) (le_of_lt hε)
    simpa [μ, ℱ, A, MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
      using hk
  filter_upwards [hBC, htail] with records hBC_records htail_records
  have hp : 0 < Real.exp (-(Q.uniformRate * ε)) := Real.exp_pos _
  have hpred : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        MeasureTheory.condExp (ℱ k) μ
          ((A (k + 1)).indicator fun _ => (1 : ℝ)) records)
      Filter.atTop Filter.atTop := by
    have hconst : Filter.Tendsto
        (fun n : ℕ => (n : ℝ) * Real.exp (-(Q.uniformRate * ε)))
        Filter.atTop Filter.atTop :=
      by simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop hp
    refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hconst
    filter_upwards with n
    calc
      (n : ℝ) * Real.exp (-(Q.uniformRate * ε))
          = ∑ k ∈ Finset.range n, Real.exp (-(Q.uniformRate * ε)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range n,
            MeasureTheory.condExp (ℱ k) μ
              ((A (k + 1)).indicator fun _ => (1 : ℝ)) records := by
            exact Finset.sum_le_sum fun k _ => htail_records k
  have hindicator : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        (A (k + 1)).indicator (fun _ => (1 : ℝ)) records)
      Filter.atTop Filter.atTop :=
    hBC_records.2 hpred
  refine hindicator.congr' ?_
  filter_upwards with n
  rw [Finset.sum_indicator_eq_sum_filter]
  simp [A, QMatrix.recordTrajectoryToPath_holdingTime]

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- For fixed `t` and `n`, the event that the `n`-th read-out jump time is
after `t` is measurable. -/
theorem QMatrix.measurableSet_recordTrajectoryToPath_time_gt
    (t : ℝ) (n : ℕ) :
    MeasurableSet
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        t < (QMatrix.recordTrajectoryToPath records).times n} :=
  (QMatrix.measurable_recordTrajectoryToPath_times (S := S) n) measurableSet_Ioi

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- Filtration-level version of
`QMatrix.measurableSet_recordTrajectoryToPath_time_gt`. -/
theorem QMatrix.measurableSet_recordTrajectoryToPath_time_gt_canonicalRecordFiltration
    (t : ℝ) (n : ℕ) :
    MeasurableSet[QMatrix.canonicalRecordFiltration (S := S) (n + 1)]
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        t < (QMatrix.recordTrajectoryToPath records).times n} :=
  (QMatrix.measurable_recordTrajectoryToPath_times_canonicalRecordFiltration
    (S := S) n) measurableSet_Ioi

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The WithTop-valued clock-horizon jump index has finite-level stopping
events in the shifted record filtration. -/
theorem QMatrix.measurableSet_recordTrajectoryToPath_jumpCountTop_le_canonicalRecordFiltration
    (t : ℝ) (n : ℕ) :
    MeasurableSet[QMatrix.canonicalRecordFiltration (S := S) (n + 1)]
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        (QMatrix.recordTrajectoryToPath records).jumpCountTop t ≤ (n : WithTop ℕ)} := by
  rw [show {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        (QMatrix.recordTrajectoryToPath records).jumpCountTop t ≤ (n : WithTop ℕ)} =
      ⋃ k ∈ Finset.range (n + 1),
        {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
          t < (QMatrix.recordTrajectoryToPath records).times k} by
    ext records
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, Finset.mem_range]
    constructor
    · intro hle
      obtain ⟨k, hk, htk⟩ :=
        (QMatrix.recordTrajectoryToPath records).jumpCountTop_le_coe_iff_exists_le
          t n |>.mp hle
      exact ⟨k, Nat.lt_succ_of_le hk, htk⟩
    · rintro ⟨k, hk, htk⟩
      exact
        (QMatrix.recordTrajectoryToPath records).jumpCountTop_le_coe_iff_exists_le
          t n |>.mpr ⟨k, Nat.le_of_lt_succ hk, htk⟩]
  exact Finset.measurableSet_biUnion (Finset.range (n + 1)) fun k hk =>
    (QMatrix.canonicalRecordFiltration (S := S)).mono
      (Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) _
      (QMatrix.measurableSet_recordTrajectoryToPath_time_gt_canonicalRecordFiltration
        (S := S) t k)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- The WithTop-valued clock-horizon jump index is a stopping time for the
shifted canonical record filtration. -/
theorem QMatrix.isStoppingTime_recordTrajectoryToPath_jumpCountTop_shifted
    (t : ℝ) :
    MeasureTheory.IsStoppingTime
      (QMatrix.shiftedCanonicalRecordFiltration (S := S))
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
        (QMatrix.recordTrajectoryToPath records).jumpCountTop t) := by
  intro n
  exact
    QMatrix.measurableSet_recordTrajectoryToPath_jumpCountTop_le_canonicalRecordFiltration
      (S := S) t n

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- For fixed `t` and `n`, the event that `n` is the first index whose
read-out jump time is after `t` is measurable.  The finite-history form avoids
using `Nat.find` directly. -/
theorem QMatrix.measurableSet_recordTrajectoryToPath_first_time_gt
    (t : ℝ) (n : ℕ) :
    MeasurableSet
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        t < (QMatrix.recordTrajectoryToPath records).times n ∧
          ∀ k ∈ Finset.range n,
            ¬ t < (QMatrix.recordTrajectoryToPath records).times k} := by
  have h_after := QMatrix.measurableSet_recordTrajectoryToPath_time_gt (S := S) t n
  have h_before : MeasurableSet
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        ∀ k ∈ Finset.range n,
          ¬ t < (QMatrix.recordTrajectoryToPath records).times k} := by
    rw [show {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        ∀ k ∈ Finset.range n,
          ¬ t < (QMatrix.recordTrajectoryToPath records).times k} =
        ⋂ k ∈ Finset.range n,
          {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
            ¬ t < (QMatrix.recordTrajectoryToPath records).times k} by
      ext records
      simp]
    exact Finset.measurableSet_biInter (Finset.range n) fun k _ =>
      (QMatrix.measurableSet_recordTrajectoryToPath_time_gt (S := S) t k).compl
  exact h_after.inter h_before

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- For fixed `t`, the event that no read-out jump time is after `t` is
measurable.  This is the fallback branch in the current `CTMCPath.stateAt`
definition. -/
theorem QMatrix.measurableSet_recordTrajectoryToPath_no_time_gt
    (t : ℝ) :
    MeasurableSet
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        ∀ n, ¬ t < (QMatrix.recordTrajectoryToPath records).times n} := by
  rw [show {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        ∀ n, ¬ t < (QMatrix.recordTrajectoryToPath records).times n} =
      ⋂ n,
        {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
          ¬ t < (QMatrix.recordTrajectoryToPath records).times n} by
    ext records
    simp]
  exact MeasurableSet.iInter fun n =>
    (QMatrix.measurableSet_recordTrajectoryToPath_time_gt (S := S) t n).compl

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- For fixed `t` and `n`, the event that the read-out jump count at clock
time `t` is exactly `n` is measurable. -/
theorem QMatrix.measurableSet_recordTrajectoryToPath_jumpCount_eq
    (t : ℝ) (n : ℕ) :
    MeasurableSet
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        (QMatrix.recordTrajectoryToPath records).jumpCount t = n} := by
  let first : Set ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) :=
    {records | t < (QMatrix.recordTrajectoryToPath records).times n ∧
      ∀ k < n, ¬ t < (QMatrix.recordTrajectoryToPath records).times k}
  let none : Set ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) :=
    {records | n = 0 ∧
      ∀ k, ¬ t < (QMatrix.recordTrajectoryToPath records).times k}
  have hfirst : MeasurableSet first := by
    simpa [first, Finset.mem_range] using
      QMatrix.measurableSet_recordTrajectoryToPath_first_time_gt (S := S) t n
  have hnone : MeasurableSet none := by
    by_cases hn : n = 0
    · simpa [none, hn] using
        QMatrix.measurableSet_recordTrajectoryToPath_no_time_gt (S := S) t
    · simp [none, hn]
  rw [show {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
      (QMatrix.recordTrajectoryToPath records).jumpCount t = n} = first ∪ none by
    ext records
    simp only [Set.mem_setOf_eq, Set.mem_union, first, none]
    exact (QMatrix.recordTrajectoryToPath records).jumpCount_eq_iff t n]
  exact hfirst.union hnone

omit [Fintype S] [DecidableEq S] [Countable S] in
/-- For fixed `t` and state `a`, the canonical read-out event
`stateAt t = a` is measurable. -/
theorem QMatrix.measurableSet_recordTrajectoryToPath_stateAt_eq
    (t : ℝ) (a : S) :
    MeasurableSet
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        (QMatrix.recordTrajectoryToPath records).stateAt t = a} := by
  have h_init : MeasurableSet
      {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        (QMatrix.recordTrajectoryToPath records).init = a} := by
    rw [show {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        (QMatrix.recordTrajectoryToPath records).init = a} =
        {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
          (records 0).2 = a} by
      ext records
      simp [QMatrix.recordTrajectoryToPath_init]]
    exact (show Measurable
      (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m => (records 0).2) by
        fun_prop) (measurableSet_singleton a)
  rw [show {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
        (QMatrix.recordTrajectoryToPath records).stateAt t = a} =
      ({records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
          (∀ n, ¬ t < (QMatrix.recordTrajectoryToPath records).times n) ∧
            (QMatrix.recordTrajectoryToPath records).init = a} ∪
        ⋃ n,
          {records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m |
            (t < (QMatrix.recordTrajectoryToPath records).times n ∧
              ∀ k ∈ Finset.range n,
                ¬ t < (QMatrix.recordTrajectoryToPath records).times k) ∧
              (QMatrix.recordTrajectoryToPath records).stateSeq n = a}) by
    ext records
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
    let path := QMatrix.recordTrajectoryToPath records
    change path.stateAt t = a ↔
      ((∀ n, ¬ t < path.times n) ∧ path.init = a) ∨
        ∃ n, (t < path.times n ∧
          ∀ k ∈ Finset.range n, ¬ t < path.times k) ∧
          path.stateSeq n = a
    constructor
    · intro hstate
      by_cases hex : ∃ n, t < path.times n
      · right
        let n := Nat.find hex
        have hmin : ∀ k ∈ Finset.range n, ¬ t < path.times k := by
          intro k hk
          exact Nat.find_min hex (Finset.mem_range.mp hk)
        refine ⟨n, ⟨Nat.find_spec hex, hmin⟩, ?_⟩
        have hpath :=
          path.stateAt_eq_stateSeq_of_first_time_gt t (Nat.find_spec hex) hmin
        rw [← hpath]
        exact hstate
      · left
        have hno : ∀ n, ¬ t < path.times n := by
          intro n hn
          exact hex ⟨n, hn⟩
        refine ⟨hno, ?_⟩
        have hstate_init : path.stateAt t = path.init := by
          simp [CTMCPath.stateAt, hex]
        rw [hstate_init] at hstate
        exact hstate
    · intro h
      rcases h with hno | hsome
      · rcases hno with ⟨hno, hinit⟩
        have hex : ¬ ∃ n, t < path.times n := by
          rintro ⟨n, hn⟩
          exact hno n hn
        have hstate_init : path.stateAt t = path.init := by
          simp [CTMCPath.stateAt, hex]
        rw [hstate_init, hinit]
      · rcases hsome with ⟨n, ⟨hn, hmin⟩, hseq⟩
        have hpath := path.stateAt_eq_stateSeq_of_first_time_gt t hn hmin
        rw [hpath, hseq]]
  exact
    ((QMatrix.measurableSet_recordTrajectoryToPath_no_time_gt (S := S) t).inter h_init).union
      (MeasurableSet.iUnion fun n =>
        (QMatrix.measurableSet_recordTrajectoryToPath_first_time_gt (S := S) t n).inter
          ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) n)
            (measurableSet_singleton a)))

omit [Fintype S] [DecidableEq S] in
/-- For fixed `t`, the canonical read-out state at time `t` is measurable. -/
theorem QMatrix.measurable_recordTrajectoryToPath_stateAt
    (t : ℝ) :
    Measurable (fun records : (m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m =>
      (QMatrix.recordTrajectoryToPath records).stateAt t) :=
  measurable_to_countable' fun a =>
    QMatrix.measurableSet_recordTrajectoryToPath_stateAt_eq (S := S) t a

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- In the product space of clock time and record trajectory, the event that
the `n`-th read-out jump time is after the clock time is measurable. -/
theorem QMatrix.measurableSet_prod_recordTrajectoryToPath_time_gt
    (n : ℕ) :
    MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        p.1 < (QMatrix.recordTrajectoryToPath p.2).times n} :=
  measurableSet_lt measurable_fst
    ((QMatrix.measurable_recordTrajectoryToPath_times (S := S) n).comp measurable_snd)

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- In the product space of clock time and record trajectory, the event that
`n` is the first read-out jump index after the clock time is measurable. -/
theorem QMatrix.measurableSet_prod_recordTrajectoryToPath_first_time_gt
    (n : ℕ) :
    MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        p.1 < (QMatrix.recordTrajectoryToPath p.2).times n ∧
          ∀ k ∈ Finset.range n,
            ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times k} := by
  have h_after := QMatrix.measurableSet_prod_recordTrajectoryToPath_time_gt (S := S) n
  have h_before : MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ k ∈ Finset.range n,
          ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times k} := by
    rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ k ∈ Finset.range n,
          ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times k} =
        ⋂ k ∈ Finset.range n,
          {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
            ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times k} by
      ext p
      simp]
    exact Finset.measurableSet_biInter (Finset.range n) fun k _ =>
      (QMatrix.measurableSet_prod_recordTrajectoryToPath_time_gt (S := S) k).compl
  exact h_after.inter h_before

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSingletonClass S] in
/-- In the product space of clock time and record trajectory, the event that
no read-out jump time is after the clock time is measurable. -/
theorem QMatrix.measurableSet_prod_recordTrajectoryToPath_no_time_gt :
    MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ n, ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times n} := by
  rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ n, ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times n} =
      ⋂ n,
        {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
          ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times n} by
    ext p
    simp]
  exact MeasurableSet.iInter fun n =>
    (QMatrix.measurableSet_prod_recordTrajectoryToPath_time_gt (S := S) n).compl

omit [Fintype S] [DecidableEq S] [Countable S] in
/-- In the product space of clock time and record trajectory, the event
`stateAt clock = a` is measurable. -/
theorem QMatrix.measurableSet_prod_recordTrajectoryToPath_stateAt_eq
    (a : S) :
    MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).stateAt p.1 = a} := by
  have h_init : MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).init = a} := by
    rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).init = a} =
        {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
          (p.2 0).2 = a} by
      ext p
      simp [QMatrix.recordTrajectoryToPath_init]]
    exact (show Measurable
      (fun p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) => (p.2 0).2) by
        fun_prop) (measurableSet_singleton a)
  rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).stateAt p.1 = a} =
      ({p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
          (∀ n, ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times n) ∧
            (QMatrix.recordTrajectoryToPath p.2).init = a} ∪
        ⋃ n,
          {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
            (p.1 < (QMatrix.recordTrajectoryToPath p.2).times n ∧
              ∀ k ∈ Finset.range n,
                ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times k) ∧
              (QMatrix.recordTrajectoryToPath p.2).stateSeq n = a}) by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
    let path := QMatrix.recordTrajectoryToPath p.2
    let t := p.1
    change path.stateAt t = a ↔
      ((∀ n, ¬ t < path.times n) ∧ path.init = a) ∨
        ∃ n, (t < path.times n ∧
          ∀ k ∈ Finset.range n, ¬ t < path.times k) ∧
          path.stateSeq n = a
    constructor
    · intro hstate
      by_cases hex : ∃ n, t < path.times n
      · right
        let n := Nat.find hex
        have hmin : ∀ k ∈ Finset.range n, ¬ t < path.times k := by
          intro k hk
          exact Nat.find_min hex (Finset.mem_range.mp hk)
        refine ⟨n, ⟨Nat.find_spec hex, hmin⟩, ?_⟩
        have hpath :=
          path.stateAt_eq_stateSeq_of_first_time_gt t (Nat.find_spec hex) hmin
        rw [← hpath]
        exact hstate
      · left
        have hno : ∀ n, ¬ t < path.times n := by
          intro n hn
          exact hex ⟨n, hn⟩
        refine ⟨hno, ?_⟩
        have hstate_init : path.stateAt t = path.init := by
          simp [CTMCPath.stateAt, hex]
        rw [hstate_init] at hstate
        exact hstate
    · intro h
      rcases h with hno | hsome
      · rcases hno with ⟨hno, hinit⟩
        have hex : ¬ ∃ n, t < path.times n := by
          rintro ⟨n, hn⟩
          exact hno n hn
        have hstate_init : path.stateAt t = path.init := by
          simp [CTMCPath.stateAt, hex]
        rw [hstate_init, hinit]
      · rcases hsome with ⟨n, ⟨hn, hmin⟩, hseq⟩
        have hpath := path.stateAt_eq_stateSeq_of_first_time_gt t hn hmin
        rw [hpath, hseq]]
  exact
    (QMatrix.measurableSet_prod_recordTrajectoryToPath_no_time_gt (S := S)).inter h_init
      |>.union
        (MeasurableSet.iUnion fun n =>
          (QMatrix.measurableSet_prod_recordTrajectoryToPath_first_time_gt (S := S) n).inter
            (((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) n).comp measurable_snd)
              (measurableSet_singleton a)))

omit [Fintype S] [DecidableEq S] in
/-- The canonical read-out state is jointly measurable in clock time and
record trajectory. -/
theorem QMatrix.measurable_prod_recordTrajectoryToPath_stateAt :
    Measurable
      (fun p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
        (QMatrix.recordTrajectoryToPath p.2).stateAt p.1) :=
  measurable_to_countable' fun a =>
    QMatrix.measurableSet_prod_recordTrajectoryToPath_stateAt_eq (S := S) a

omit [Fintype S] [DecidableEq S] [Countable S] [MeasurableSpace S]
  [MeasurableSingletonClass S] in
/-- Positive sampled holding times make the read-out jump times strictly
increasing. -/
theorem QMatrix.recordTrajectoryToPath_times_strict
    (records : (n : ℕ) → QMatrix.JumpHoldTrajectorySpace S n)
    (hpos : ∀ n, 0 < (records (n + 2)).1) :
    ∀ n, (QMatrix.recordTrajectoryToPath records).times n <
      (QMatrix.recordTrajectoryToPath records).times (n + 1) := by
  intro n
  rw [QMatrix.recordTrajectoryToPath_times_succ]
  linarith [hpos n]

/-- Under the canonical record law, if all finite histories relevant to
successive jump-time increments are non-absorbing, then the read-out CTMCPath
has strictly increasing jump times.  This statement is deliberately conditional:
absorbing histories use terminal `(0,current)` markers, so strict increase is
not asserted after absorption. -/
theorem QMatrix.canonicalRecordMeasure_recordTrajectoryToPath_times_strict_ae_of_nonabsorbing
    (Q : QMatrix S) (s₀ : S) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      (∀ n,
        ¬Q.IsAbsorbing
          (QMatrix.currentStateFromHistory (S := S) (n + 1)
            (Preorder.frestrictLe (n + 1) records))) →
        ∀ n, (QMatrix.recordTrajectoryToPath records).times n <
          (QMatrix.recordTrajectoryToPath records).times (n + 1) := by
  filter_upwards [Q.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing s₀]
    with records hpos h_nonabsorbing
  exact QMatrix.recordTrajectoryToPath_times_strict records
    (fun n => hpos (n + 1) (h_nonabsorbing n))

/-- If the Q-matrix has no absorbing states, then all holding times in the
canonical read-out path are nonnegative almost surely. -/
theorem QMatrix.canonicalRecordMeasure_recordTrajectoryToPath_holdingTime_nonneg_ae_of_no_absorbing
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      ∀ n, 0 ≤ (QMatrix.recordTrajectoryToPath records).holdingTime n := by
  filter_upwards [Q.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing s₀]
    with records hpos n
  rw [QMatrix.recordTrajectoryToPath_holdingTime]
  exact le_of_lt (hpos (n + 1) (h_no_abs _))

/-- Canonical non-explosion bridge: after the large-holding-time count has
been proved to diverge almost surely, non-explosion follows from the
deterministic `CTMCPath` criterion. -/
theorem QMatrix.canonicalRecordMeasure_nonExplosive_ae_of_large_count_tendsto
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s)
    {ε : ℝ} (hε : 0 < ε)
    (hcount : ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter fun k =>
            ε ≤ (QMatrix.recordTrajectoryToPath records).holdingTime k).card : ℝ))
        Filter.atTop Filter.atTop) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      (QMatrix.recordTrajectoryToPath records).NonExplosive := by
  filter_upwards
    [Q.canonicalRecordMeasure_recordTrajectoryToPath_holdingTime_nonneg_ae_of_no_absorbing
      s₀ h_no_abs, hcount]
    with records hnonneg hcount_records
  exact (QMatrix.recordTrajectoryToPath records).nonExplosive_of_large_holdingTime_count_tendsto
    hnonneg hε hcount_records

/-- Strict-threshold canonical non-explosion bridge, matching `Set.Ioi ε`
Borel-Cantelli events. -/
theorem QMatrix.canonicalRecordMeasure_nonExplosive_ae_of_large_strict_count_tendsto
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s)
    {ε : ℝ} (hε : 0 < ε)
    (hcount : ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter fun k =>
            ε < (QMatrix.recordTrajectoryToPath records).holdingTime k).card : ℝ))
        Filter.atTop Filter.atTop) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      (QMatrix.recordTrajectoryToPath records).NonExplosive := by
  filter_upwards
    [Q.canonicalRecordMeasure_recordTrajectoryToPath_holdingTime_nonneg_ae_of_no_absorbing
      s₀ h_no_abs, hcount]
    with records hnonneg hcount_records
  exact (QMatrix.recordTrajectoryToPath records)
    |>.nonExplosive_of_large_holdingTime_strict_count_tendsto
      hnonneg hε hcount_records

/-- If the Q-matrix has no absorbing states, then canonical record trajectories
read out as non-explosive CTMC paths almost surely. -/
theorem QMatrix.canonicalRecordMeasure_recordTrajectoryToPath_nonExplosive_ae_of_no_absorbing
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s)
    [StandardBorelSpace S] [Nonempty S] :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      (QMatrix.recordTrajectoryToPath records).NonExplosive := by
  have hcount :=
    Q.canonicalRecordMeasure_holdingTime_Ioi_count_tendsto_ae
      s₀ h_no_abs (by norm_num : (0 : ℝ) < 1)
  exact Q.canonicalRecordMeasure_nonExplosive_ae_of_large_strict_count_tendsto
    s₀ h_no_abs (by norm_num : (0 : ℝ) < 1) hcount

/-- If the Q-matrix has no absorbing states, then canonical record trajectories
read out as `CTMCPath`s are compatible with `Q` almost surely. -/
theorem QMatrix.canonicalRecordMeasure_recordTrajectoryToPath_isCompatible_ae_of_no_absorbing
    (Q : QMatrix S) (s₀ : S) (h_no_abs : ∀ s, ¬Q.IsAbsorbing s) :
    ∀ᵐ records ∂Q.canonicalRecordMeasure s₀,
      (QMatrix.recordTrajectoryToPath records).IsCompatible Q := by
  filter_upwards
    [Q.canonicalRecordMeasure_all_next_holdingTime_pos_ae_of_nonabsorbing s₀,
      Q.canonicalRecordMeasure_all_next_state_ne_current_ae_of_nonabsorbing s₀,
      Q.canonicalRecordMeasure_recordTrajectoryToPath_times_strict_ae_of_nonabsorbing s₀]
    with records hpos hne hstrict_cond
  have hfirst : 0 < (QMatrix.recordTrajectoryToPath records).times 0 := by
    have hfirst_record : 0 < (records 1).1 := hpos 0 (h_no_abs _)
    simpa [QMatrix.recordTrajectoryToPath_times_zero] using hfirst_record
  have hstrict : ∀ n, (QMatrix.recordTrajectoryToPath records).times n <
      (QMatrix.recordTrajectoryToPath records).times (n + 1) :=
    hstrict_cond (fun n => h_no_abs _)
  have hjump : (QMatrix.recordTrajectoryToPath records).init ≠
      (QMatrix.recordTrajectoryToPath records).jumps 0 ∨
      Q.IsAbsorbing (QMatrix.recordTrajectoryToPath records).init := by
    left
    intro heq
    have hne0 := hne 0 (h_no_abs _)
    exact hne0 (by
      simpa [QMatrix.currentStateFromHistory] using heq.symm)
  exact ⟨hfirst, hstrict, hjump⟩

end Ripple.CTMC
