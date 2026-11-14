-- Ripple/Kurtz/StrongApprox/CellActiveRaceRecordKernel.lean
import Ripple.Kurtz.StrongApprox.CellDensityChannelAlignment
import Ripple.Kurtz.StrongApprox.RegenerativePoissonRecord
import Ripple.Kurtz.StrongApprox.CellExtendedRecordLawInterface

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellActiveRaceRecordKernel

open MeasureTheory ProbabilityTheory Set Filter Preorder
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open CellStoppingLineFreshness CellExtendedStoppingLine
open ExponentialRace
open CellDensityChannelAlignment

variable {ι S : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable [Fintype S] [DecidableEq S] [Countable S]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Embed every positive off-diagonal target at a state into the fixed cell
coordinates.  Extra cell coordinates are allowed and are ignored by this
canonical race row. -/
structure ActiveTargetClockEmbedding
    (Q : QMatrix S) (ι : Type*) where
  channel : ∀ x, RegenerativeRace.ActiveTarget Q x → ι
  injective : ∀ x, Function.Injective (channel x)

/-- Restrict a fixed cell residual vector to the currently active targets. -/
def cellStateClocks
    {Q : QMatrix S}
    (A : ActiveTargetClockEmbedding Q ι)
    (x : S) (E : ι → ℝ) :
    RegenerativeRace.ActiveTarget Q x → ℝ :=
  fun a => E (A.channel x a)

@[fun_prop]
theorem measurable_cellStateClocks
    {Q : QMatrix S}
    (A : ActiveTargetClockEmbedding Q ι) (x : S) :
    Measurable (cellStateClocks A x) := by
  apply measurable_pi_lambda
  intro a
  exact measurable_pi_apply (A.channel x a)

/-- An injective active subfamily of the cell residuals is again iid Exp(1). -/
theorem cellStateClocks_law
    {Q : QMatrix S}
    (A : ActiveTargetClockEmbedding Q ι) (x : S) :
    (clockLaw ι).map (cellStateClocks A x) =
      clockLaw (RegenerativeRace.ActiveTarget Q x) := by
  exact clockSubfamily_law (A.channel x) (A.injective x)

/-- Nonabsorbing one-step race read directly from the active cell subfamily. -/
noncomputable def liveCellRaceStep
    {Q : QMatrix S}
    (A : ActiveTargetClockEmbedding Q ι)
    (x : S) (h : ¬ Q.IsAbsorbing x)
    (E : ι → ℝ) : ℝ × S := by
  letI : Nonempty (RegenerativeRace.ActiveTarget Q x) :=
    RegenerativeRace.activeTarget_nonempty Q h
  let p := racePair (RegenerativeRace.targetRate Q x)
    (cellStateClocks A x E)
  exact (p.1, p.2.1)

@[fun_prop]
theorem measurable_liveCellRaceStep
    {Q : QMatrix S}
    (A : ActiveTargetClockEmbedding Q ι)
    (x : S) (h : ¬ Q.IsAbsorbing x) :
    Measurable (liveCellRaceStep A x h) := by
  letI : Nonempty (RegenerativeRace.ActiveTarget Q x) :=
    RegenerativeRace.activeTarget_nonempty Q h
  unfold liveCellRaceStep
  exact (measurable_fst.comp
      ((measurable_racePair (RegenerativeRace.targetRate Q x)).comp
        (measurable_cellStateClocks A x))).prodMk
    (measurable_subtype_coe.comp (measurable_snd.comp
      ((measurable_racePair (RegenerativeRace.targetRate Q x)).comp
        (measurable_cellStateClocks A x))))

/-- The active cell race is the canonical nonabsorbing jump-hold law. -/
theorem liveCellRaceStep_law
    {Q : QMatrix S}
    (A : ActiveTargetClockEmbedding Q ι)
    (x : S) (h : ¬ Q.IsAbsorbing x) :
    Measure.map (liveCellRaceStep A x h) (clockLaw ι) =
      Q.jumpHoldStepMeasure h := by
  letI : Nonempty (RegenerativeRace.ActiveTarget Q x) :=
    RegenerativeRace.activeTarget_nonempty Q h
  let r := RegenerativeRace.targetRate Q x
  have hr : ∀ a, 0 < r a := RegenerativeRace.targetRate_pos Q x
  letI : IsProbabilityMeasure (expMeasure (rateTotal r)) :=
    isProbabilityMeasure_expMeasure (rateTotal_pos r hr)
  have hclocks := cellStateClocks_law A x
  have hpair := racePair_law r hr
  change Measure.map
      (((Prod.map id Subtype.val) ∘ racePair r) ∘
        cellStateClocks A x) (clockLaw ι) = _
  rw [← Measure.map_map
      ((measurable_id.prodMap measurable_subtype_coe).comp
        (measurable_racePair r))
      (measurable_cellStateClocks A x),
    hclocks,
    ← Measure.map_map (measurable_id.prodMap measurable_subtype_coe)
      (measurable_racePair r),
    hpair,
    ← Measure.map_prod_map (expMeasure (rateTotal r))
      (winnerPMF r hr).toMeasure measurable_id (by fun_prop),
    Measure.map_id,
    RegenerativeRace.activeWinnerMeasure_map Q h,
    RegenerativeRace.targetRate_total]
  rfl

open Classical in
/-- Zero-aware total race: absorption appends the canonical terminal marker. -/
noncomputable def cellRaceStep
    (Q : QMatrix S) (A : ActiveTargetClockEmbedding Q ι)
    (x : S) (E : ι → ℝ) : ℝ × S :=
  if h : Q.IsAbsorbing x then (0, x) else liveCellRaceStep A x h E

theorem cellRaceStep_eq_of_absorbing
    (Q : QMatrix S) (A : ActiveTargetClockEmbedding Q ι) {x : S} (h : Q.IsAbsorbing x) :
    cellRaceStep Q A x = fun _ => (0, x) := by
  funext E
  unfold cellRaceStep
  rw [dif_pos h]

theorem cellRaceStep_eq_of_nonabsorbing
    (Q : QMatrix S) (A : ActiveTargetClockEmbedding Q ι) {x : S} (h : ¬ Q.IsAbsorbing x) :
    cellRaceStep Q A x = liveCellRaceStep A x h := by
  funext E
  unfold cellRaceStep
  rw [dif_neg h]

@[fun_prop]
theorem measurable_cellRaceStep_row
    (Q : QMatrix S) (A : ActiveTargetClockEmbedding Q ι) (x : S) :
    Measurable (cellRaceStep Q A x) := by
  by_cases h : Q.IsAbsorbing x
  · rw [cellRaceStep_eq_of_absorbing Q A h]
    exact measurable_const
  · rw [cellRaceStep_eq_of_nonabsorbing Q A h]
    exact measurable_liveCellRaceStep A x h

@[fun_prop]
theorem measurable_cellRaceStep
    (Q : QMatrix S) (A : ActiveTargetClockEmbedding Q ι) :
    Measurable (fun p : S × (ι → ℝ) =>
      cellRaceStep Q A p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro x
  exact measurable_cellRaceStep_row Q A x

/-- Complete active-cell row law, including the absorbing state. -/
theorem cellRaceStep_law
    (Q : QMatrix S) (A : ActiveTargetClockEmbedding Q ι) (x : S) :
    Measure.map (cellRaceStep Q A x) (clockLaw ι) =
      Q.jumpHoldStepMeasureTotal x := by
  by_cases h : Q.IsAbsorbing x
  · rw [Q.jumpHoldStepMeasureTotal_of_absorbing h]
    rw [cellRaceStep_eq_of_absorbing Q A h, Measure.map_const]
    simp
  · rw [Q.jumpHoldStepMeasureTotal_of_nonabsorbing h,
      cellRaceStep_eq_of_nonabsorbing Q A h]
    exact liveCellRaceStep_law A x h

/-! ## Proof-ready form of the Γ/β/v alignment -/

variable {d : ℕ}
variable {Gamma : Ripple.Kurtz.RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {xDensity : Fin d → ℝ}
variable {latticeStart : ∀ n : ℕ, 0 < n → Fin d → Fin (n + 1)}

/-- Finite combinatorial consequences of `DensityChannelAlignment` needed by
the active race.  These are intended to be derived from the channel
equivalence, boundary compatibility, and the definition of `offDiagRate`.
They are exposed separately so no kernel identity is hidden in the alignment. -/
structure KernelReadyDensityChannelAlignment
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n) : Type _ where
  embedding : ActiveTargetClockEmbedding
    (DensityDepCTMC.mk n hn Gamma).toQMatrix ι
  rate_eq : ∀ x, ∀ a : RegenerativeRace.ActiveTarget
      (DensityDepCTMC.mk n hn Gamma).toQMatrix x,
    (DensityDepCTMC.mk n hn Gamma).toQMatrix.rate x a.1 =
      A.densityRate n hn x (embedding.channel x a)
  jump_eq : ∀ x, ∀ a : RegenerativeRace.ActiveTarget
      (DensityDepCTMC.mk n hn Gamma).toQMatrix x, ∀ i,
    (a.1 i : ℤ) - (x i : ℤ) =
      A.jump (embedding.channel x a) i
  complete : ∀ x l,
    0 < A.latticeRate n hn x l →
      ∃ a : RegenerativeRace.ActiveTarget
        (DensityDepCTMC.mk n hn Gamma).toQMatrix x,
        embedding.channel x a = l

/-! ## Fresh residuals imply the history-next kernel identity -/

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Generic measure-theoretic assembly.  It is independent of how the
stopping lines were constructed. -/
theorem historyNext_of_freshResidualsAt
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {record : Omega → ℕ → ℝ × S}
    {residual : Omega → ι → ℝ} {k : ℕ}
    (H : FreshResidualsAt mu record residual k)
    (next :
      (((i : Finset.Iic k) → ℝ × S) × (ι → ℝ)) → ℝ × S)
    (hnext : Measurable next)
    (theta : Kernel ((i : Finset.Iic k) → ℝ × S) (ℝ × S))
    [IsMarkovKernel theta]
    (hrow : ∀ hist,
      (clockLaw ι).map (fun E => next (hist, E)) = theta hist)
    (hpath : ∀ᵐ omega ∂mu,
      record omega (k + 1) =
        next (recordPrefix record k omega, residual omega)) :
    mu.map (fun omega =>
        (recordPrefix record k omega, record omega (k + 1))) =
      (mu.map (recordPrefix record k)) ⊗ₘ theta := by
  let history := recordPrefix record k
  let joint : Omega →
      (((i : Finset.Iic k) → ℝ × S) × (ι → ℝ)) :=
    fun omega => (history omega, residual omega)
  let out :
      (((i : Finset.Iic k) → ℝ × S) × (ι → ℝ)) →
        (((i : Finset.Iic k) → ℝ × S) × (ℝ × S)) :=
    fun p => (p.1, next p)
  have hjoint : Measurable joint := by
    exact H.measurable_history.prodMk H.measurable_residual
  have hout : Measurable out := measurable_fst.prodMk hnext
  letI : IsProbabilityMeasure (mu.map history) :=
    Measure.isProbabilityMeasure_map H.measurable_history.aemeasurable
  have htransport :=
    RegenerativeRace.map_prod_history_next
      (mu.map history) (clockLaw ι) theta
      id measurable_id next hnext
      (ae_of_all _ fun hist => by simpa using hrow hist)
  calc
    mu.map (fun omega =>
        (recordPrefix record k omega, record omega (k + 1))) =
        mu.map (out ∘ joint) := by
          apply Measure.map_congr
          filter_upwards [hpath] with omega homega
          simp [out, joint, history, homega]
    _ = (mu.map joint).map out :=
      (Measure.map_map hout hjoint).symm
    _ = ((mu.map history).prod (clockLaw ι)).map out := by
      rw [show mu.map joint =
          (mu.map history).prod (clockLaw ι) by
        simpa [joint, history] using H.joint_law]
    _ = (mu.map history) ⊗ₘ theta := by
      simpa [out] using htransport
    _ = (mu.map (recordPrefix record k)) ⊗ₘ theta := rfl

/-! ## Corrected record-recursion interface -/

/-- What the zero-aware stopping-line recursion must produce.

The `step` field is pathwise on the original cell space.  Its active row is
not a new source of randomness: it is a measurable function of the fresh
residual vector at the current extended stopping line. -/
structure ZeroAwareCellRecordRecursion
    (Q : QMatrix S) (x0 : S)
    (record : CellFamily ι → ℕ → ℝ × S)
    (internal : ℕ → ExtendedCellLine ι)
    (A : ActiveTargetClockEmbedding Q ι) : Prop where
  filtration : ExtendedCellRecordFiltrationRealization record internal
  initial :
    ((cellFamilyLaw ι).map record).map
        (frestrictLe (π := fun _ : ℕ => ℝ × S) 0) =
      (Measure.dirac (0, x0)).map
        (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => ℝ × S)).symm
  step : ∀ k,
    ∀ᵐ c ∂cellFamilyLaw ι,
      record c (k + 1) =
        cellRaceStep Q A (record c k).2
          (extendedStoppingResidual (internal k) c)

namespace ZeroAwareCellRecordRecursion

/-- The corrected cell recursion has the canonical history-next kernel. -/
theorem history_next
    {Q : QMatrix S} {x0 : S}
    {record : CellFamily ι → ℕ → ℝ × S}
    {internal : ℕ → ExtendedCellLine ι}
    {A : ActiveTargetClockEmbedding Q ι}
    (h : ZeroAwareCellRecordRecursion Q x0 record internal A)
    (k : ℕ) :
    ((cellFamilyLaw ι).map record).map (fun omega =>
        (frestrictLe (π := fun _ : ℕ => ℝ × S) k omega,
          omega (k + 1))) =
      ((cellFamilyLaw ι).map record).map
          (frestrictLe (π := fun _ : ℕ => ℝ × S) k) ⊗ₘ
        Q.jumpHoldTrajectoryStepKernel k := by
  let theta := Q.jumpHoldTrajectoryStepKernel k
  letI : IsMarkovKernel theta :=
    Q.isMarkovKernel_jumpHoldTrajectoryStepKernel k
  let next :
      (((i : Finset.Iic k) → ℝ × S) × (ι → ℝ)) → ℝ × S :=
    fun p => cellRaceStep Q A
      (QMatrix.currentStateFromHistory k p.1) p.2
  have hcurrent : Measurable
      (QMatrix.currentStateFromHistory (S := S) k) := by
    exact measurable_snd.comp
      (measurable_pi_apply
        (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k))
  have hnext : Measurable next := by
    exact (measurable_cellRaceStep Q A).comp
      ((hcurrent.comp measurable_fst).prodMk measurable_snd)
  have hrow : ∀ hist,
      (clockLaw ι).map (fun E => next (hist, E)) = theta hist := by
    intro hist
    dsimp only [next, theta]
    rw [Q.jumpHoldTrajectoryStepKernel_apply,
      Q.jumpHoldStepKernel_apply]
    exact cellRaceStep_law Q A
      (QMatrix.currentStateFromHistory k hist)
  have hpath : ∀ᵐ c ∂cellFamilyLaw ι,
      record c (k + 1) =
        next (recordPrefix record k c,
          extendedStoppingResidual (internal k) c) := by
    filter_upwards [h.step k] with c hc
    simpa only [next, QMatrix.currentStateFromHistory,
      recordPrefix, frestrictLe_apply] using hc
  have H := h.filtration.freshResidualsAt
    (fun _ => (0, x0)) k
  have key := historyNext_of_freshResidualsAt
    H next hnext theta hrow hpath
  have hrec : Measurable record := h.filtration.measurable_record
  have hpair : Measurable (fun omega : ℕ → ℝ × S =>
      (frestrictLe (π := fun _ : ℕ => ℝ × S) k omega, omega (k + 1))) :=
    (measurable_frestrictLe k).prodMk (measurable_pi_apply (k + 1))
  rw [Measure.map_map hpair hrec,
    Measure.map_map (measurable_frestrictLe k) hrec]
  exact key

/-- The corrected recursion supplies the unchanged density-record-law field. -/
theorem toExtendedCellDensityRecordRealization
    {d : ℕ} {M : DensityDepCTMC d}
    {x0 : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → ExtendedCellLine ι}
    {A : ActiveTargetClockEmbedding M.toQMatrix ι}
    (h : ZeroAwareCellRecordRecursion
      M.toQMatrix x0 record internal A) :
    ExtendedCellDensityRecordRealization M x0 record internal :=
  { filtration := h.filtration
    density :=
      { measurable_record := h.filtration.measurable_record
        initial := h.initial
        history_next := h.history_next } }

/-- Canonical record law of the corrected cell-built density record. -/
theorem record_law
    {d : ℕ} {M : DensityDepCTMC d}
    {x0 : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → ExtendedCellLine ι}
    {A : ActiveTargetClockEmbedding M.toQMatrix ι}
    (h : ZeroAwareCellRecordRecursion
      M.toQMatrix x0 record internal A) :
    (cellFamilyLaw ι).map record =
      M.toQMatrix.canonicalRecordMeasure x0 :=
  (h.toExtendedCellDensityRecordRealization).record_law

/-- Canonical nonnegative-path readout law of the corrected cell record. -/
theorem readout_law
    {d : ℕ} {M : DensityDepCTMC d}
    {x0 : Fin d → Fin (M.N + 1)}
    {record : CellFamily ι → ℕ →
      ℝ × (Fin d → Fin (M.N + 1))}
    {internal : ℕ → ExtendedCellLine ι}
    {A : ActiveTargetClockEmbedding M.toQMatrix ι}
    (h : ZeroAwareCellRecordRecursion
      M.toQMatrix x0 record internal A) :
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative M ∘ record) =
      (M.toQMatrix.canonicalRecordMeasure x0).map
        (AlignedCellCoupling.canonicalDensityNonnegative M) :=
  (h.toExtendedCellDensityRecordRealization).readout_law

end ZeroAwareCellRecordRecursion

/-!
THEOREM LIST
* `cellStateClocks_law`
* `liveCellRaceStep_law`
* `cellRaceStep_law`
* `historyNext_of_freshResidualsAt`
* `ZeroAwareCellRecordRecursion.history_next`
* `ZeroAwareCellRecordRecursion.toExtendedCellDensityRecordRealization`
* `ZeroAwareCellRecordRecursion.record_law`
* `ZeroAwareCellRecordRecursion.readout_law`

CLOSES
* Exact active-subtype race law on the fixed cell space.
* Zero-rate channels are omitted from the race without changing the sample
  space.
* Canonical `(0,x)` padding after absorption.
* The full measure-theoretic passage from `FreshResidualsAt` to the
  history-next kernel.
* `IsDensityRecordRealization`, canonical record law, and canonical readout law
  for any corrected zero-aware cell recursion.

UNFINISHED
* Generalize the one-step stopping-line theorem from globally positive
  rates to: the current active subtype on each state fibre, and the identity
  internal line on an absorbing fibre.
* Iterate that generalized theorem to construct an actual
  `ZeroAwareCellRecordRecursion`.
* Derive `KernelReadyDensityChannelAlignment` from
  `DensityChannelAlignment`; the proof is finite aggregation of Γ's unique
  jump vectors, boundary-zero channels, and `density_offdiag_rate_aggregation`.
* Prove the corrected record readout equals `cellTimeChangeNonnegative` under
  `beta_eq`, `vector_eq`, and `initial_alignment`.
* The old `recursiveRecord` remains valid only for the special globally
  positive, everywhere-valid, nonabsorbing channel system.
END
-/

end Ripple.Kurtz.StrongApprox.CellActiveRaceRecordKernel

end
