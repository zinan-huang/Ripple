/-
  Ripple.LPP.SynPPKurtz

  Boundary-safe stochastic backend for syntactic population protocols.
  A diagonal input pair must be the identity transition; every nontrivial
  transition then consumes two distinct states, so the unguarded mass-action
  RateSpec is compatible with the finite population simplex.
-/

import Ripple.LPP.WeightedReactions
import Ripple.LPP.Stochastic
import Ripple.Kurtz.FiniteHorizonGeneric
import Ripple.CTMC.FrozenRandomIndexDoob

namespace Ripple

open Kurtz CTMC

namespace PLPPTransitions

variable {n : ℕ} (tr : PLPPTransitions n)

/-- Repeated-input interactions are necessarily identity interactions. -/
def DiagonalIdentity : Prop :=
  ∀ i k l, tr.α i i k l ≠ 0 → k = i ∧ l = i

/-- The PLPP RateSpec only lists conservative jumps. -/
theorem toDensityDepCTMC_conservativeJumps (N : ℕ) (hN : 0 < N) :
    (DensityDepCTMC.mk N hN tr.toRateSpec).ConservativeJumps := by
  intro ell hell
  exact tr.rateSpecJumps_conservative ell hell

/-- Off-diagonal inputs are realizable whenever both input counts are
positive. Diagonal inputs are harmless because `DiagonalIdentity` forces
their net change to be zero. -/
theorem toDensityDepCTMC_boundaryCompatibleOnSimplex
    (hdiag : tr.DiagonalIdentity) (N : ℕ) (hN : 0 < N) :
    (DensityDepCTMC.mk N hN tr.toRateSpec).BoundaryCompatibleOnSimplex := by
  let M : DensityDepCTMC n := DensityDepCTMC.mk N hN tr.toRateSpec
  intro x hx ell _hell himpossible
  change (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
    if netChange i j k l = ell then
      (tr.α i j k l : ℝ) * M.scaledState x i * M.scaledState x j
    else 0) = 0
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  by_cases hnet : netChange i j k l = ell
  · rw [if_pos hnet]
    by_cases halpha : tr.α i j k l = 0
    · simp [halpha]
    by_cases hij : i = j
    · subst j
      obtain ⟨rfl, rfl⟩ := hdiag i k l halpha
      exfalso
      apply himpossible
      refine ⟨x, fun r => ?_⟩
      rw [← hnet]
      simp [netChange]
    · have hsum : ∑ r, (x r : ℕ) = N := by
        simpa [M, DensityDepCTMC.InSimplex, DensityDepCTMC.totalCount] using hx
      by_cases hxi : (x i : ℕ) = 0
      · simp [M, DensityDepCTMC.scaledState, hxi]
      by_cases hxj : (x j : ℕ) = 0
      · simp [M, DensityDepCTMC.scaledState, hxj]
      · let reaction : Kurtz.PPReaction n :=
          { in1 := i, in2 := j, out1 := k, out2 := l }
        have hreal := reaction.exists_realizing_state_of_inputsDistinct_of_input_counts_pos
          (by simpa [reaction, Kurtz.PPReaction.InputsDistinct] using hij)
          x hsum (Nat.pos_of_ne_zero hxi) (Nat.pos_of_ne_zero hxj)
        exfalso
        apply himpossible
        obtain ⟨y, hy⟩ := hreal
        refine ⟨y, fun r => ?_⟩
        rw [← hnet]
        simpa [reaction, Kurtz.PPReaction.netChange, netChange, eq_comm] using hy r
  · rw [if_neg hnet]

/-- Simplex boundary compatibility makes the abstract drift vanish at every
absorbing lattice state. -/
theorem toDensityDepCTMC_driftZeroAtAbsorbingOnSimplex
    (hdiag : tr.DiagonalIdentity) (N : ℕ) (hN : 0 < N) :
    (DensityDepCTMC.mk N hN tr.toRateSpec).DriftZeroAtAbsorbingOnSimplex := by
  let M : DensityDepCTMC n := DensityDepCTMC.mk N hN tr.toRateSpec
  have hBC : M.BoundaryCompatibleOnSimplex := by
    simpa [M] using tr.toDensityDepCTMC_boundaryCompatibleOnSimplex hdiag N hN
  intro x hx hexit
  change M.rateSpec.drift (M.scaledState x) = 0
  rw [← M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex hBC hx]
  funext i
  exact M.generatorDrift_eq_zero_of_exitRateAt_zero
    (by simpa [DensityDepCTMC.exitRateAt] using hexit) i

end PLPPTransitions

namespace SynPPBalance

variable {n : ℕ} (eq : SynPPBalance n)

/-- Coefficient form of a harmless repeated-input interaction. -/
def DiagonalIdentity : Prop :=
  ∀ i r, eq.coeff r i i = if r = i then 2 else 0

theorem toPLPPTransitions_diagonalIdentity (hdiag : eq.DiagonalIdentity) :
    eq.toPLPPTransitions.DiagonalIdentity := by
  intro i k l halpha
  have hk0 : eq.coeff k i i ≠ 0 := by
    intro hk
    apply halpha
    simp [SynPPBalance.toPLPPTransitions, hk]
  have hl0 : eq.coeff l i i ≠ 0 := by
    intro hl
    apply halpha
    simp [SynPPBalance.toPLPPTransitions, hl]
  constructor
  · by_contra hki
    exact hk0 (by rw [hdiag i k]; simp [hki])
  · by_contra hli
    exact hl0 (by rw [hdiag i l]; simp [hli])

end SynPPBalance

namespace WeightedReactions

variable {n m : ℕ} (R : WeightedReactions n m)

/-- Input-distinct weighted reactions leave every diagonal input pair for the
identity filler in `QuadField.toSynPPBalance`. -/
theorem toSynPPBalance_diagonalIdentity (hR : R.InputsDistinct) :
    R.toSynPPBalance.DiagonalIdentity := by
  intro i r
  change ((if r = i then 1 else 0) + if r = i then 1 else 0) +
      R.toQuadField.normalization * R.coeff r i i = if r = i then 2 else 0
  rw [R.coeff_diag_eq_zero hR r i]
  by_cases hri : r = i
  · subst r
    norm_num
  · simp [hri]

/-- Zero-rate padding may use repeated inputs without changing the compiled
field; active input distinctness is therefore the natural compiler invariant. -/
theorem toSynPPBalance_diagonalIdentity_of_active
    (hR : R.ActiveInputsDistinct) :
    R.toSynPPBalance.DiagonalIdentity := by
  intro i r
  change ((if r = i then 1 else 0) + if r = i then 1 else 0) +
      R.toQuadField.normalization * R.coeff r i i = if r = i then 2 else 0
  rw [R.coeff_diag_eq_zero_of_active hR r i]
  by_cases hri : r = i
  · subst r
    norm_num
  · simp [hri]

/-- The normalized weighted-reaction compiler supplies the two structural
hypotheses consumed by the generic frozen Kurtz engine. -/
theorem toRateSpec_kurtzStructural (hR : R.InputsDistinct) (N : ℕ) (hN : 0 < N) :
    let tr := R.toSynPPBalance.toPLPPTransitions
    (DensityDepCTMC.mk N hN tr.toRateSpec).DriftZeroAtAbsorbingOnSimplex ∧
      (DensityDepCTMC.mk N hN tr.toRateSpec).ConservativeJumps := by
  let tr := R.toSynPPBalance.toPLPPTransitions
  have hsyn : R.toSynPPBalance.DiagonalIdentity :=
    R.toSynPPBalance_diagonalIdentity hR
  have hdiag : tr.DiagonalIdentity :=
    R.toSynPPBalance.toPLPPTransitions_diagonalIdentity hsyn
  exact ⟨tr.toDensityDepCTMC_driftZeroAtAbsorbingOnSimplex hdiag N hN,
    tr.toDensityDepCTMC_conservativeJumps N hN⟩

/-- Structural hypotheses for a reaction table whose zero-rate padding may
contain repeated inputs. -/
theorem toRateSpec_kurtzStructural_of_active
    (hR : R.ActiveInputsDistinct) (N : ℕ) (hN : 0 < N) :
    let tr := R.toSynPPBalance.toPLPPTransitions
    (DensityDepCTMC.mk N hN tr.toRateSpec).DriftZeroAtAbsorbingOnSimplex ∧
      (DensityDepCTMC.mk N hN tr.toRateSpec).ConservativeJumps := by
  let tr := R.toSynPPBalance.toPLPPTransitions
  have hsyn : R.toSynPPBalance.DiagonalIdentity :=
    R.toSynPPBalance_diagonalIdentity_of_active hR
  have hdiag : tr.DiagonalIdentity :=
    R.toSynPPBalance.toPLPPTransitions_diagonalIdentity hsyn
  exact ⟨tr.toDensityDepCTMC_driftZeroAtAbsorbingOnSimplex hdiag N hN,
    tr.toDensityDepCTMC_conservativeJumps N hN⟩

end WeightedReactions

namespace CTMC.DensityDepCTMC

variable {d : ℕ}

/-- If every state in a frozen path's state sequence is in the population
simplex, then every frozen clock-time state is in the simplex as well. -/
theorem frozenStateAt_inSimplex_of_forall_stateSeq
    (M : DensityDepCTMC d)
    (path : CTMCPath (Fin d → Fin (M.N + 1)))
    (hseq : ∀ n, M.InSimplex (path.stateSeq n)) (t : ℝ) :
    M.InSimplex (path.frozenStateAt t) := by
  by_cases hex : ∃ n, t < path.times n
  · let n := Nat.find hex
    have hmin : ∀ k ∈ Finset.range n, ¬ t < path.times k := by
      intro k hk
      exact Nat.find_min hex (Finset.mem_range.mp hk)
    rw [path.frozenStateAt_eq_stateSeq_of_first_time_gt t n
      (Nat.find_spec hex) hmin]
    exact hseq n
  · have hno : ∀ m, ¬ t < path.times m := by
      intro m hm
      exact hex ⟨m, hm⟩
    by_cases hstable : ∃ n, path.stateSeq n = path.stateSeq (n + 1)
    · let n := Nat.find hstable
      have hmin : ∀ k ∈ Finset.range n,
          path.stateSeq k ≠ path.stateSeq (k + 1) := by
        intro k hk
        exact Nat.find_min hstable (Finset.mem_range.mp hk)
      rw [path.frozenStateAt_eq_stateSeq_of_first_stable t n hno
        (Nat.find_spec hstable) hmin]
      exact hseq n
    · have hnostable : ∀ n, path.stateSeq n ≠ path.stateSeq (n + 1) := by
        intro n hn
        exact hstable ⟨n, hn⟩
      rw [path.frozenStateAt_eq_init_of_no_time_gt_of_no_stable t hno hnostable]
      simpa only [CTMCPath.stateSeq_zero] using hseq 0

/-- Conservative canonical paths remain in the population simplex at every
frozen clock time, including their absorbing/explosive frozen tails. -/
theorem canonicalPathMap_frozenStateAt_inSimplex_ae_of_conservative
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hcons : M.ConservativeJumps) (hinit : M.InSimplex x₀) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
      M.InSimplex ((M.canonicalPathMap records).frozenStateAt t) := by
  filter_upwards
    [M.canonicalPathMap_stateSeq_inSimplex_ae_of_conservative x₀ hcons hinit]
    with records hseq t
  exact M.frozenStateAt_inSimplex_of_forall_stateSeq
    (M.canonicalPathMap records) hseq t

/-- On a conservative simplex path, simplex-local boundary compatibility
identifies the residual martingale used by Kurtz with the generator-centered
martingale controlled by the finite-clock Doob construction. -/
theorem canonical_frozenMartingalePart_eq_frozenGeneratorMartingalePart_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (hcons : M.ConservativeJumps) (hinit : M.InSimplex x₀)
    (hBC : M.BoundaryCompatibleOnSimplex) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀, ∀ t : ℝ,
      M.frozenMartingalePart M.canonicalPathMap t records =
        M.frozenGeneratorMartingalePart M.canonicalPathMap t records := by
  filter_upwards
    [M.canonicalPathMap_frozenStateAt_inSimplex_ae_of_conservative
      x₀ hcons hinit]
    with records hsimp t
  ext i
  apply sub_eq_zero.mp
  rw [M.frozenMartingalePart_sub_frozenGeneratorMP M.canonicalPathMap t records i]
  have hintegral :
      (∫ s in Set.Icc (0 : ℝ) t,
        (M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s)) i) =
      ∫ s in Set.Icc (0 : ℝ) t,
        (M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap s records)) i := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro s _hs
    have h := M.generatorDrift_eq_rateSpec_drift_of_boundaryCompatibleOnSimplex
      hBC (hsimp s)
    simpa [DensityDepCTMC.frozenDensityProcess, DensityDepCTMC.scaledState]
      using congrFun h i
  rw [hintegral, sub_self]

end CTMC.DensityDepCTMC

end Ripple
