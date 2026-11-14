-- Ripple/Kurtz/StrongApprox/CellPerScaleDensityAlignment.lean
import Ripple.Kurtz.StrongApprox.CellKernelReadyAlignment
import Ripple.Kurtz.StrongApprox.PoissonCellTimeChangeFactor

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellPerScaleDensityAlignment

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
open Ripple.CTMC
open Ripple.Kurtz
open CellDensityChannelAlignment
open CellActiveRaceRecordKernel
open CellZeroAwareRecordSequence

variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι]

private abbrev DensityState (d n : ℕ) :=
  Fin d → Fin (n + 1)

private abbrev DensityModel
    (Gamma : RateSpec d) (n : ℕ) (hn : 0 < n) :=
  DensityDepCTMC.mk n hn Gamma

/-- A channel alignment at one lattice scale.  In contrast with the legacy
`DensityChannelAlignment`, the initial equality has exactly one scale in its
type. -/
structure PerScaleDensityChannelAlignment
    (Gamma : RateSpec d)
    (beta : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ)
    (n : ℕ) (hn : 0 < n) : Type _ where
  channelEquiv : ι ≃ ListedNonzeroJump Gamma
  beta_eq : ∀ l y,
    beta l y = Gamma.rate (channelEquiv l).1 y
  vector_eq : ∀ l i,
    v l i = ((channelEquiv l).1 i : ℝ)
  boundary : (DensityModel Gamma n hn).BoundaryCompatible
  zero_jump_rate : Gamma.rate (0 : Fin d → ℤ) = 0
  latticeStart : DensityState d n
  xStart : Fin d → ℝ
  initial_alignment :
    (DensityModel Gamma n hn).scaledState latticeStart = xStart

namespace PerScaleDensityChannelAlignment

variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {n : ℕ} {hn : 0 < n}

/-- Canonical constructor: the scale start is definitionally the scaled
lattice start. -/
def ofLatticeStart
    (channelEquiv : ι ≃ ListedNonzeroJump Gamma)
    (beta_eq : ∀ l y,
      beta l y = Gamma.rate (channelEquiv l).1 y)
    (vector_eq : ∀ l i,
      v l i = ((channelEquiv l).1 i : ℝ))
    (boundary : (DensityModel Gamma n hn).BoundaryCompatible)
    (zero_jump_rate : Gamma.rate (0 : Fin d → ℤ) = 0)
    (latticeStart : DensityState d n) :
    PerScaleDensityChannelAlignment Gamma beta v n hn :=
  { channelEquiv := channelEquiv
    beta_eq := beta_eq
    vector_eq := vector_eq
    boundary := boundary
    zero_jump_rate := zero_jump_rate
    latticeStart := latticeStart
    xStart := (DensityModel Gamma n hn).scaledState latticeStart
    initial_alignment := rfl }

/-- Integer jump carried by a channel. -/
def jump
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (l : ι) : Fin d → ℤ :=
  (A.channelEquiv l).1

@[simp]
theorem jump_mem
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (l : ι) : A.jump l ∈ Gamma.jumps :=
  (A.channelEquiv l).2.1

@[simp]
theorem jump_ne_zero
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (l : ι) : A.jump l ≠ 0 :=
  (A.channelEquiv l).2.2

/-- Scale-`n` density rate. -/
noncomputable def densityRate
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι) : ℝ :=
  (n : ℝ) * beta l ((DensityModel Gamma n hn).scaledState x)

/-- Nonnegative rate used by the cell recursion. -/
noncomputable def latticeRate
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι) : ℝ≥0 :=
  Real.toNNReal (A.densityRate x l)

/-- The advertised jump has a target in the scale-`n` cube. -/
def hasLatticeTarget
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι) : Prop :=
  ∃ y : DensityState d n,
    ∀ i, (y i : ℤ) - (x i : ℤ) = A.jump l i

/-- Total scale-`n` lattice step. -/
noncomputable def latticeStep
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι) : DensityState d n :=
  if h : A.hasLatticeTarget x l then Classical.choose h else x

/-- Boundary compatibility kills an invalid channel. -/
theorem latticeRate_eq_zero_of_no_target
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι)
    (hno : ¬ A.hasLatticeTarget x l) :
    A.latticeRate x l = 0 := by
  have hz :
      Gamma.rate (A.jump l)
          ((DensityModel Gamma n hn).scaledState x) = 0 :=
    A.boundary x (A.jump l) (A.jump_mem l) hno
  have hz' :
      Gamma.rate (A.channelEquiv l).1
          ((DensityModel Gamma n hn).scaledState x) = 0 := hz
  simp [latticeRate, densityRate, A.beta_eq, hz']

/-- A positive local channel realizes its advertised jump. -/
theorem latticeStep_spec_of_positive
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι)
    (hpositive : 0 < A.latticeRate x l) :
    ∀ i,
      (A.latticeStep x l i : ℤ) - (x i : ℤ) = A.jump l i := by
  by_cases htarget : A.hasLatticeTarget x l
  · intro i
    simp only [latticeStep, dif_pos htarget]
    exact Classical.choose_spec htarget i
  · have hz := A.latticeRate_eq_zero_of_no_target x l htarget
    rw [hz] at hpositive
    exact (lt_irrefl 0 hpositive).elim

end PerScaleDensityChannelAlignment

/-! ## Scale-local form of `CellKernelReadyAlignment` -/

/-- The same four finite consequences as in `CellKernelReadyAlignment`, but indexed by a genuinely
single-scale alignment. -/
structure KernelReadyPerScaleDensityChannelAlignment
    {Gamma : RateSpec d}
    {beta : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ}
    {n : ℕ} {hn : 0 < n}
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) : Type _ where
  embedding : ActiveTargetClockEmbedding
    (DensityModel Gamma n hn).toQMatrix ι
  rate_eq : ∀ x, ∀ a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x,
    (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
      A.densityRate x (embedding.channel x a)
  jump_eq : ∀ x, ∀ a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x, ∀ i,
    (a.1 i : ℤ) - (x i : ℤ) =
      A.jump (embedding.channel x a) i
  complete : ∀ x l,
    0 < A.latticeRate x l →
      ∃ a : RegenerativeRace.ActiveTarget
        (DensityModel Gamma n hn).toQMatrix x,
        embedding.channel x a = l

private theorem matchingJumpFilter_eq_singleton
    (M : DensityDepCTMC d)
    (x y : Fin d → Fin (M.N + 1))
    (j : Fin d → ℤ)
    (hj : j ∈ M.rateSpec.jumps)
    (hmatch : ∀ i, (y i : ℤ) - (x i : ℤ) = j i) :
    M.rateSpec.jumps.filter
        (fun q => ∀ i, (y i : ℤ) - (x i : ℤ) = q i) = {j} := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_hq, hqmatch⟩
    funext i
    exact (hqmatch i).symm.trans (hmatch i)
  · intro hq
    subst q
    exact ⟨hj, hmatch⟩

private theorem offDiagRate_eq_of_matching
    (M : DensityDepCTMC d)
    (x y : Fin d → Fin (M.N + 1))
    (hyx : y ≠ x)
    (j : Fin d → ℤ)
    (hj : j ∈ M.rateSpec.jumps)
    (hmatch : ∀ i, (y i : ℤ) - (x i : ℤ) = j i) :
    M.offDiagRate x y =
      (M.N : ℝ) * M.rateSpec.rate j (M.scaledState x) := by
  have hfilter :=
    matchingJumpFilter_eq_singleton M x y j hj hmatch
  rw [DensityDepCTMC.offDiagRate, if_neg hyx.symm, hfilter]
  simp only [Finset.sum_singleton]
  rfl

private theorem existsActiveJump
    (Gamma : RateSpec d) (n : ℕ) (hn : 0 < n)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) :
    ∃ j : ListedNonzeroJump Gamma,
      ∀ i, (a.1 i : ℤ) - (x i : ℤ) = j.1 i := by
  have hq :
      0 < (DensityModel Gamma n hn).toQMatrix.rate x a.1 := by
    simpa only [RegenerativeRace.targetRate] using
      RegenerativeRace.targetRate_pos
        (DensityModel Gamma n hn).toQMatrix x a
  have hoff :
      0 < (DensityModel Gamma n hn).offDiagRate x a.1 :=
    (DensityModel Gamma n hn).offDiagRate_pos_of_toQMatrix_rate_pos hq
  obtain ⟨j, hj, hmatch⟩ :=
    (DensityModel Gamma n hn).exists_jump_of_offDiagRate_pos hoff
  have hjzero : j ≠ 0 := by
    intro hzero
    subst j
    exact
      (density_zero_jump_not_offdiag
        (DensityModel Gamma n hn) x a.1 a.2.1.symm) hmatch
  exact ⟨⟨j, hj, hjzero⟩, hmatch⟩

private noncomputable def activeJump
    (Gamma : RateSpec d) (n : ℕ) (hn : 0 < n)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) :
    ListedNonzeroJump Gamma :=
  Classical.choose (existsActiveJump Gamma n hn x a)

private theorem activeJump_spec
    (Gamma : RateSpec d) (n : ℕ) (hn : 0 < n)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x)
    (i : Fin d) :
    (a.1 i : ℤ) - (x i : ℤ) =
      (activeJump Gamma n hn x a).1 i := by
  exact Classical.choose_spec
    (existsActiveJump Gamma n hn x a) i

variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {n : ℕ} {hn : 0 < n}

private noncomputable def activeChannel
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) : ι :=
  A.channelEquiv.symm (activeJump Gamma n hn x a)

private theorem activeChannel_injective
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) :
    Function.Injective (activeChannel A x) := by
  intro a b hab
  have hj :
      activeJump Gamma n hn x a = activeJump Gamma n hn x b := by
    apply A.channelEquiv.symm.injective
    simpa only [activeChannel] using hab
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hdiff :
      (a.1 i : ℤ) - (x i : ℤ) =
        (b.1 i : ℤ) - (x i : ℤ) := by
    calc
      (a.1 i : ℤ) - (x i : ℤ) =
          (activeJump Gamma n hn x a).1 i :=
        activeJump_spec Gamma n hn x a i
      _ = (activeJump Gamma n hn x b).1 i := by rw [hj]
      _ = (b.1 i : ℤ) - (x i : ℤ) :=
        (activeJump_spec Gamma n hn x b i).symm
  have hval : (a.1 i : ℤ) = (b.1 i : ℤ) := by
    linarith
  exact Int.ofNat.inj hval

private noncomputable def activeEmbedding
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    ActiveTargetClockEmbedding
      (DensityModel Gamma n hn).toQMatrix ι where
  channel := activeChannel A
  injective := activeChannel_injective A

private theorem activeTargetRate_eq_jumpRate
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) :
    (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
      (n : ℝ) * Gamma.rate
        (activeJump Gamma n hn x a).1
        ((DensityModel Gamma n hn).scaledState x) := by
  have hoff :=
    offDiagRate_eq_of_matching
      (DensityModel Gamma n hn) x a.1 a.2.1
      (activeJump Gamma n hn x a).1
      (activeJump Gamma n hn x a).2.1
      (fun i => activeJump_spec Gamma n hn x a i)
  simpa only [DensityDepCTMC.toQMatrix,
    DensityDepCTMC.qMatrixRate, if_neg a.2.1.symm] using hoff

private theorem activeTargetRate_eq_densityRate
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) :
    (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
      A.densityRate x (activeChannel A x a) := by
  calc
    (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
        (n : ℝ) * Gamma.rate
          (activeJump Gamma n hn x a).1
          ((DensityModel Gamma n hn).scaledState x) :=
      activeTargetRate_eq_jumpRate x a
    _ = A.densityRate x (activeChannel A x a) := by
      unfold PerScaleDensityChannelAlignment.densityRate
      rw [A.beta_eq]
      simp only [activeChannel, Equiv.apply_symm_apply]

private theorem activeChannel_jump
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) :
    A.jump (activeChannel A x a) =
      (activeJump Gamma n hn x a).1 := by
  unfold PerScaleDensityChannelAlignment.jump activeChannel
  simp only [Equiv.apply_symm_apply]

private theorem activeChannel_eq_of_match
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x)
    (l : ι)
    (hmatch : ∀ i,
      (a.1 i : ℤ) - (x i : ℤ) = A.jump l i) :
    activeChannel A x a = l := by
  apply A.channelEquiv.injective
  simp only [activeChannel, Equiv.apply_symm_apply]
  apply Subtype.ext
  funext i
  calc
    (activeJump Gamma n hn x a).1 i =
        (a.1 i : ℤ) - (x i : ℤ) :=
      (activeJump_spec Gamma n hn x a i).symm
    _ = A.jump l i := hmatch i
    _ = (A.channelEquiv l).1 i := rfl

private theorem densityRate_nonneg
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι) :
    0 ≤ A.densityRate x l := by
  unfold PerScaleDensityChannelAlignment.densityRate
  rw [A.beta_eq]
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Gamma.rate_nonneg
    (A.channelEquiv l).1 (A.channelEquiv l).2.1
  intro i
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem densityRate_pos_of_latticeRate_pos
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι)
    (hpositive : 0 < A.latticeRate x l) :
    0 < A.densityRate x l := by
  have hnonneg := densityRate_nonneg A x l
  have hcoe : 0 < ((A.latticeRate x l : ℝ≥0) : ℝ) :=
    (NNReal.coe_pos).2 hpositive
  change 0 < ((Real.toNNReal (A.densityRate x l)) : ℝ) at hcoe
  rw [Real.coe_toNNReal _ hnonneg] at hcoe
  exact hcoe

private theorem activeChannel_complete
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (x : DensityState d n) (l : ι)
    (hpositive : 0 < A.latticeRate x l) :
    ∃ a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x,
      activeChannel A x a = l := by
  let y := A.latticeStep x l
  have hmatch : ∀ i,
      (y i : ℤ) - (x i : ℤ) = A.jump l i := by
    intro i
    exact A.latticeStep_spec_of_positive x l hpositive i
  have hyx : y ≠ x := by
    intro heq
    apply A.jump_ne_zero l
    funext i
    have hi := hmatch i
    rw [heq] at hi
    simpa only [Pi.zero_apply, sub_self] using hi.symm
  have hdensity : 0 < A.densityRate x l :=
    densityRate_pos_of_latticeRate_pos A x l hpositive
  have hoff :
      (DensityModel Gamma n hn).offDiagRate x y =
        A.densityRate x l := by
    calc
      (DensityModel Gamma n hn).offDiagRate x y =
          (n : ℝ) * Gamma.rate (A.jump l)
            ((DensityModel Gamma n hn).scaledState x) :=
        offDiagRate_eq_of_matching
          (DensityModel Gamma n hn) x y hyx
          (A.jump l) (A.jump_mem l) hmatch
      _ = A.densityRate x l := by
        unfold PerScaleDensityChannelAlignment.densityRate
        rw [A.beta_eq]
        rfl
  have hoffPositive :
      0 < (DensityModel Gamma n hn).offDiagRate x y := by
    rw [hoff]
    exact hdensity
  have hq :
      0 < (DensityModel Gamma n hn).toQMatrix.rate x y := by
    simpa only [DensityDepCTMC.toQMatrix,
      DensityDepCTMC.qMatrixRate, if_neg hyx.symm] using hoffPositive
  let a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x :=
    ⟨y, hyx, hq.ne'⟩
  refine ⟨a, ?_⟩
  apply activeChannel_eq_of_match A x a l
  intro i
  change (y i : ℤ) - (x i : ℤ) = A.jump l i
  exact hmatch i

/-- The finite channel aggregation of `CellKernelReadyAlignment`, now with no all-scale initial premise. -/
noncomputable def kernelReady
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    KernelReadyPerScaleDensityChannelAlignment A := by
  classical
  refine
    { embedding := activeEmbedding A
      rate_eq := ?_
      jump_eq := ?_
      complete := ?_ }
  · intro x a
    change (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
      A.densityRate x (activeChannel A x a)
    exact activeTargetRate_eq_densityRate A x a
  · intro x a i
    change (a.1 i : ℤ) - (x i : ℤ) =
      A.jump (activeChannel A x a) i
    calc
      (a.1 i : ℤ) - (x i : ℤ) =
          (activeJump Gamma n hn x a).1 i :=
        activeJump_spec Gamma n hn x a i
      _ = A.jump (activeChannel A x a) i :=
        (congrFun (activeChannel_jump A x a) i).symm
  · intro x l hpositive
    exact activeChannel_complete A x l hpositive

/-! ## Per-scale record, readout, and path laws -/

section Records

variable [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {b : ι → ℝ}
variable {hbetaZero : ∀ l y, 0 ≤ beta l y}
variable {hbetaBound : ∀ l y, beta l y ≤ b l}
variable {hbetaMeasurable : ∀ l, Measurable (beta l)}

/-- Exact one-scale package.  The `recursion` field is the scale-local form of
the constructed zero-aware recursion of `CellZeroAwareRecordSequence`; once supplied, its record/readout
laws are the generic theorems already in the library. -/
structure PerScaleDensityCellSystem
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) : Type _ where
  recursion :
    ZeroAwareCellRecordRecursion
      (DensityModel Gamma n hn).toQMatrix A.latticeStart
      (recursiveRecord A.latticeStart A.latticeRate A.latticeStep)
      (recursiveInternal A.latticeStart A.latticeRate A.latticeStep)
      (kernelReady A).embedding
  coupling :
    AlignedCellCoupling (v := v)
      (DensityModel Gamma n hn) A.latticeStart
      hbetaZero hbetaBound hbetaMeasurable A.xStart

namespace PerScaleDensityCellSystem

/-- The canonical record law at exactly this scale. -/
theorem record_law
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (D : PerScaleDensityCellSystem
      (b := b) (hbetaZero := hbetaZero)
      (hbetaBound := hbetaBound)
      (hbetaMeasurable := hbetaMeasurable) A) :
    (cellFamilyLaw ι).map
        (recursiveRecord A.latticeStart A.latticeRate A.latticeStep) =
      (DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        A.latticeStart :=
  D.recursion.record_law

/-- The canonical density readout law at exactly this scale. -/
theorem readout_law
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (D : PerScaleDensityCellSystem
      (b := b) (hbetaZero := hbetaZero)
      (hbetaBound := hbetaBound)
      (hbetaMeasurable := hbetaMeasurable) A) :
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative
          (DensityModel Gamma n hn) ∘
          recursiveRecord A.latticeStart A.latticeRate A.latticeStep) =
      ((DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        A.latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityModel Gamma n hn)) :=
  D.recursion.readout_law

variable {Omega : Type*} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {N : ℕ → Omega → ℕ}

/-- The original Poisson time-change path at this scale has the same canonical
CTMC law, now started at `A.xStart`. -/
theorem poisson_path_law
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn)
    (D : PerScaleDensityCellSystem
      (b := b) (hbetaZero := hbetaZero)
      (hbetaBound := hbetaBound)
      (hbetaMeasurable := hbetaMeasurable) A)
    (hNm : ∀ i, Measurable (N i))
    (hN : iIndepFun N P)
    (hNl : ∀ i k,
      P {omega | N i omega = k} = ENNReal.ofReal (poisTerm k 1)) :
    (familyMeasure ι P).map
        (globalNonnegativePath (N := N)
          (β := beta) (v := v) (b := b)
          hn hbetaZero hbetaBound hbetaMeasurable A.xStart) =
      ((DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        A.latticeStart).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityModel Gamma n hn)) := by
  exact sipGlobalPoissonPath_canonical_law
    (N := N) (P := P) (β := beta) (v := v) (b := b)
    (M := DensityModel Gamma n hn) (xLattice := A.latticeStart)
    hNm hN hNl hbetaZero hbetaBound hbetaMeasurable
    A.xStart D.coupling

end PerScaleDensityCellSystem

end Records

/-!
THEOREM LIST
* `PerScaleDensityChannelAlignment`
* `PerScaleDensityChannelAlignment.ofLatticeStart`
* `PerScaleDensityChannelAlignment.latticeRate_eq_zero_of_no_target`
* `PerScaleDensityChannelAlignment.latticeStep_spec_of_positive`
* `KernelReadyPerScaleDensityChannelAlignment`
* `kernelReady`
* `PerScaleDensityCellSystem`
* `PerScaleDensityCellSystem.record_law`
* `PerScaleDensityCellSystem.readout_law`
* `PerScaleDensityCellSystem.poisson_path_law`

CLOSES
* A density-channel alignment whose initial equality mentions one scale only.
* The scale-local version of all four kernel-ready fields.
* The generic record/readout laws at the local lattice start.
* The original Poisson time-change law at the local density start.

EXPLICIT INPUT
* `PerScaleDensityCellSystem.recursion` is the scale-local retyping of the
  concrete zero-aware recursion of `CellZeroAwareRecordSequence`, which proves the same recursion for the
  legacy alignment type; its proof is independent of any second scale, but
  its present declaration cannot accept this new alignment type without
  editing an existing file.  The generic record/readout consequences are
  fully discharged here.

UNFINISHED
* A later compatibility-only file may re-export the concrete recursion
  constructor for `PerScaleDensityChannelAlignment`; no probability or
  initial-value argument remains in that adapter.
END
-/

end Ripple.Kurtz.StrongApprox.CellPerScaleDensityAlignment

end
