-- Ripple/Kurtz/StrongApprox/CellKernelReadyAlignment.lean
import Ripple.Kurtz.StrongApprox.CellZeroAwareRecordSequence

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellKernelReadyAlignment

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open CellStoppingLineFreshness
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

/-- For a fixed source and target, the matching listed jump is unique. -/
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

/-- Hence one realizable listed jump contributes exactly one summand to the
canonical off-diagonal rate. -/
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

/-- Every active Q-matrix target determines a listed nonzero jump. -/
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

/-- The unique listed nonzero jump of an active target. -/
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
variable {xDensity : Fin d → ℝ}
variable {latticeStart : ∀ n : ℕ, 0 < n → Fin d → Fin (n + 1)}

/-- Name an active target by the channel corresponding to its unique jump. -/
private noncomputable def activeChannel
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) : ι :=
  A.channelEquiv.symm (activeJump Gamma n hn x a)

/-- Two active targets with the same channel have the same difference from the
source, hence are the same target. -/
private theorem activeChannel_injective
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n) :
    Function.Injective (activeChannel A n hn x) := by
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
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n) :
    ActiveTargetClockEmbedding
      (DensityModel Gamma n hn).toQMatrix ι where
  channel := activeChannel A n hn
  injective := fun x => activeChannel_injective A n hn x

/-- The Q-matrix rate of an active target is the single rate attached to its
unique listed jump. -/
private theorem activeTargetRate_eq_jumpRate
    (n : ℕ) (hn : 0 < n)
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

/-- This is exactly the aligned density rate; there is no normalization
mismatch. -/
private theorem activeTargetRate_eq_densityRate
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) :
    (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
      A.densityRate n hn x (activeChannel A n hn x a) := by
  calc
    (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
        (n : ℝ) * Gamma.rate
          (activeJump Gamma n hn x a).1
          ((DensityModel Gamma n hn).scaledState x) :=
      activeTargetRate_eq_jumpRate n hn x a
    _ = A.densityRate n hn x (activeChannel A n hn x a) := by
      unfold DensityChannelAlignment.densityRate
      rw [A.beta_eq]
      simp only [activeChannel, Equiv.apply_symm_apply]

private theorem activeChannel_jump
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x) :
    A.jump (activeChannel A n hn x a) =
      (activeJump Gamma n hn x a).1 := by
  unfold DensityChannelAlignment.jump activeChannel
  simp only [Equiv.apply_symm_apply]

/-- Any channel whose advertised jump is the target difference is the channel
chosen by `activeChannel`. -/
private theorem activeChannel_eq_of_match
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n)
    (a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x)
    (l : ι)
    (hmatch : ∀ i,
      (a.1 i : ℤ) - (x i : ℤ) = A.jump l i) :
    activeChannel A n hn x a = l := by
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
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n) (l : ι) :
    0 ≤ A.densityRate n hn x l := by
  unfold DensityChannelAlignment.densityRate
  rw [A.beta_eq]
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Gamma.rate_nonneg
    (A.channelEquiv l).1 (A.channelEquiv l).2.1
  intro i
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem densityRate_pos_of_latticeRate_pos
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n) (l : ι)
    (hpositive : 0 < A.latticeRate n hn x l) :
    0 < A.densityRate n hn x l := by
  have hnonneg := densityRate_nonneg A n hn x l
  have hcoe :
      0 < ((A.latticeRate n hn x l : ℝ≥0) : ℝ) :=
    (NNReal.coe_pos).2 hpositive
  change 0 < ((Real.toNNReal
    (A.densityRate n hn x l)) : ℝ) at hcoe
  rw [Real.coe_toNNReal _ hnonneg] at hcoe
  exact hcoe

/-- Every positive aligned lattice channel produces an active target, and the
active-target embedding maps that target back to the original channel. -/
private theorem activeChannel_complete
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : DensityState d n) (l : ι)
    (hpositive : 0 < A.latticeRate n hn x l) :
    ∃ a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x,
      activeChannel A n hn x a = l := by
  let y := A.latticeStep n hn x l
  have hmatch : ∀ i,
      (y i : ℤ) - (x i : ℤ) = A.jump l i := by
    intro i
    exact A.latticeStep_spec_of_positive n hn x l hpositive i
  have hyx : y ≠ x := by
    intro heq
    apply A.jump_ne_zero l
    funext i
    have hi := hmatch i
    rw [heq] at hi
    simpa only [Pi.zero_apply, sub_self] using hi.symm
  have hdensity : 0 < A.densityRate n hn x l :=
    densityRate_pos_of_latticeRate_pos A n hn x l hpositive
  have hoff :
      (DensityModel Gamma n hn).offDiagRate x y =
        A.densityRate n hn x l := by
    calc
      (DensityModel Gamma n hn).offDiagRate x y =
          (n : ℝ) * Gamma.rate (A.jump l)
            ((DensityModel Gamma n hn).scaledState x) :=
        offDiagRate_eq_of_matching
          (DensityModel Gamma n hn) x y hyx
          (A.jump l) (A.jump_mem l) hmatch
      _ = A.densityRate n hn x l := by
        unfold DensityChannelAlignment.densityRate
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
  apply activeChannel_eq_of_match A n hn x a l
  intro i
  change (y i : ℤ) - (x i : ℤ) = A.jump l i
  exact hmatch i

/-- The alignment itself canonically supplies the remaining
kernel-ready input of `CellZeroAwareRecordSequence`. -/
noncomputable def kernelReady
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n) :
    KernelReadyDensityChannelAlignment A n hn := by
  classical
  refine
    { embedding := activeEmbedding A n hn
      rate_eq := ?_
      jump_eq := ?_
      complete := ?_ }
  · intro x a
    change (DensityModel Gamma n hn).toQMatrix.rate x a.1 =
      A.densityRate n hn x (activeChannel A n hn x a)
    exact activeTargetRate_eq_densityRate A n hn x a
  · intro x a i
    change (a.1 i : ℤ) - (x i : ℤ) =
      A.jump (activeChannel A n hn x a) i
    calc
      (a.1 i : ℤ) - (x i : ℤ) =
          (activeJump Gamma n hn x a).1 i :=
        activeJump_spec Gamma n hn x a i
      _ = A.jump (activeChannel A n hn x a) i :=
        (congrFun (activeChannel_jump A n hn x a) i).symm
  · intro x l hpositive
    change ∃ a : RegenerativeRace.ActiveTarget
      (DensityModel Gamma n hn).toQMatrix x,
      activeChannel A n hn x a = l
    exact activeChannel_complete A n hn x l hpositive

section CanonicalLaws

variable [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {n : ℕ}

/-- The canonical record law with the explicit kernel-ready argument
eliminated. -/
theorem densityCellRecord_law
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (hn : 0 < n) :
    (cellFamilyLaw ι).map
        (recursiveRecord (latticeStart n hn)
          (A.latticeRate n hn) (A.latticeStep n hn)) =
      (DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        (latticeStart n hn) :=
  CellZeroAwareRecordSequence.densityCellRecord_law
    A hn (kernelReady A n hn)

/-- The canonical density readout law with the explicit kernel-ready
argument eliminated. -/
theorem densityCellReadout_law
    (A : DensityChannelAlignment
      Gamma beta v xDensity latticeStart)
    (hn : 0 < n) :
    (cellFamilyLaw ι).map
        (AlignedCellCoupling.canonicalDensityNonnegative
          (DensityModel Gamma n hn) ∘
          recursiveRecord (latticeStart n hn)
            (A.latticeRate n hn) (A.latticeStep n hn)) =
      ((DensityModel Gamma n hn).toQMatrix.canonicalRecordMeasure
        (latticeStart n hn)).map
          (AlignedCellCoupling.canonicalDensityNonnegative
            (DensityModel Gamma n hn)) :=
  CellZeroAwareRecordSequence.densityCellReadout_law
    A hn (kernelReady A n hn)

end CanonicalLaws

/-!
THEOREM LIST
* `kernelReady`
* `densityCellRecord_law`
* `densityCellReadout_law`

CLOSES
* Derivation of all four fields of
  `KernelReadyDensityChannelAlignment A n hn` from the original alignment.
* Exact singleton reduction of the target-aggregated Q-matrix rate.
* Active-target/channel injectivity.
* Boundary-compatible completeness of every positive lattice channel.
* The canonical record and readout laws with `K` removed; their public
  call shape is now `densityCellRecord_law A hn` and
  `densityCellReadout_law A hn`.

UNFINISHED
* The separate pathwise identification between this canonical record readout
  and the original Poisson time-change process remains a later item.
END
-/

end Ripple.Kurtz.StrongApprox.CellKernelReadyAlignment

end
