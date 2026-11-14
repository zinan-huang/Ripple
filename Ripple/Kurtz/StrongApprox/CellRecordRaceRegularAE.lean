-- Ripple/Kurtz/StrongApprox/CellRecordRaceRegularAE.lean
import Ripple.Kurtz.StrongApprox.CellRecursiveClockLedger

/-!
# `RecordRaceRegular` holds almost surely

The three probability-one events already on main are intersected over the
countably many record indices:

* `ExtendedCellRecordFiltrationRealization.finite` (every recursive internal
  line is finite);
* `residualWaitE_finite_ae` (every scaled residual wait is finite);
* `currentStateStrictWinner_ae` (the current record state is absorbing or has
  a strict active target winner).

The only new content is the deterministic translation from the strict
target winner to the channel-level statement in `RecordRaceRegular`.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellRecordRaceRegularAE

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
open Ripple.CTMC
open Ripple.Kurtz
open ExponentialRace
open CellPerScaleDensityAlignment
open CellPerScaleRecordPathAE
open CellExtendedStoppingLine
open CellExtendedRaceRecursion
open CellZeroAwareExtendedRace
open CellActiveRaceRecordKernel
open CellPerScaleRecordRecursion
open CellRecursiveClockLedger

variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {n : ℕ} {hn : 0 < n}

private theorem activeRaceTerm_toReal'
    {σ : ExtendedCellLine ι} {rate : ι → ℝ≥0}
    {c : CellFamily ι} {l : ι} (hl : 0 < rate l) :
    (activeRaceTermE σ rate c l).toReal =
      extendedStoppingResidual σ c l / (rate l : ℝ) := by
  simp [activeRaceTermE, hl, extendedStoppingResidual,
    CellRandomTimeEvaluation.residualVector,
    CellRandomTimeEvaluation.residualWait,
    extendedResidualWaitE, ENNReal.toReal_div]

/-- **Almost surely, every record of the recursion is race-regular.** -/
theorem recordRaceRegular_ae
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    ∀ᵐ c ∂cellFamilyLaw ι, RecordRaceRegular A c := by
  let R := activeRaceDataOf A
  let hfilt := (extendedRealization A).filtration
  have hfresh : ∀ k, FreshResidualsAt (cellFamilyLaw ι) (recordMap A)
      (extendedStoppingResidual (internalMap A k)) k :=
    fun k => hfilt.freshResidualsAt (fun _ => (0, A.latticeStart)) k
  have hline : ∀ᵐ c ∂cellFamilyLaw ι,
      ∀ k l, internalMap A k c l ≠ ∞ := by
    rw [ae_all_iff]
    intro k
    exact hfilt.finite k
  have hres : ∀ᵐ c ∂cellFamilyLaw ι,
      ∀ k l, extendedResidualWaitE (internalMap A k) c l ≠ ∞ := by
    rw [ae_all_iff]
    intro k
    exact residualWaitE_finite_ae (hfresh k)
  have hwin : ∀ᵐ c ∂cellFamilyLaw ι, ∀ k,
      (DensityDepCTMC.mk n hn Gamma).toQMatrix.IsAbsorbing
          (recordMap A c k).2 ∨
        ∃ a : RegenerativeRace.ActiveTarget
          (DensityDepCTMC.mk n hn Gamma).toQMatrix (recordMap A c k).2,
          strictClockWin
            (RegenerativeRace.targetRate
              (DensityDepCTMC.mk n hn Gamma).toQMatrix
              (recordMap A c k).2) a
            (cellStateClocks R.embedding (recordMap A c k).2
              (extendedStoppingResidual (internalMap A k) c)) := by
    rw [ae_all_iff]
    intro k
    exact currentStateStrictWinner_ae R (hfresh k)
  filter_upwards [hline, hres, hwin] with c h1 h2 h3
  refine ⟨h1, h2, ?_⟩
  intro k hactive
  have hactive' : HasActiveRate (A.latticeRate (recordMap A c k).2) :=
    hactive
  have habs : ¬ (DensityDepCTMC.mk n hn Gamma).toQMatrix.IsAbsorbing
      (recordMap A c k).2 :=
    (aligned_has_active_iff R (recordMap A c k).2).1 hactive'
  obtain ⟨a, ha⟩ := (h3 k).resolve_left habs
  have hwaitEq := alignedRaceWait_eq_winner R (recordMap A c k).2
    (h2 k) a ha
  have hwinnerFinite :
      activeRaceTermE (internalMap A k) (A.latticeRate (recordMap A c k).2) c
        (R.embedding.channel (recordMap A c k).2 a) ≠ ∞ := by
    have hp := aligned_channel_rate_pos R (recordMap A c k).2 a
    simp only [activeRaceTermE, if_pos hp]
    exact ENNReal.div_ne_top (h2 k _) (by exact_mod_cast hp.ne')
  refine ⟨R.embedding.channel (recordMap A c k).2 a,
    aligned_channel_rate_pos R (recordMap A c k).2 a, hwaitEq, ?_⟩
  intro l hl
  by_cases hpos : 0 < A.latticeRate (recordMap A c k).2 l
  · obtain ⟨b, hb⟩ := R.complete (recordMap A c k).2 l hpos
    have hba : b ≠ a := by
      intro h
      subst h
      exact hl hb.symm
    have hlt := ha b hba
    subst hb
    have hpa := aligned_channel_rate_pos R (recordMap A c k).2 a
    have hpb := aligned_channel_rate_pos R (recordMap A c k).2 b
    have hlFinite :
        activeRaceTermE (internalMap A k)
            (A.latticeRate (recordMap A c k).2) c
          (R.embedding.channel (recordMap A c k).2 b) ≠ ∞ := by
      simp only [activeRaceTermE, if_pos hpb]
      exact ENNReal.div_ne_top (h2 k _) (by exact_mod_cast hpb.ne')
    show activeRaceWaitE (internalMap A k)
        (A.latticeRate (recordMap A c k).2) c <
      activeRaceTermE (internalMap A k)
        (A.latticeRate (recordMap A c k).2) c
        (R.embedding.channel (recordMap A c k).2 b)
    rw [hwaitEq]
    apply (ENNReal.toReal_lt_toReal hwinnerFinite hlFinite).1
    rw [activeRaceTerm_toReal' hpa, activeRaceTerm_toReal' hpb,
      R.rate_coe (recordMap A c k).2 a, R.rate_coe (recordMap A c k).2 b]
    simpa [cellStateClocks, RegenerativeRace.targetRate] using hlt
  · have hzero : activeRaceTermE (internalMap A k)
        (A.latticeRate (recordMap A c k).2) c l = ∞ := by
      simp [activeRaceTermE, hpos]
    show activeRaceWaitE (internalMap A k)
        (A.latticeRate (recordMap A c k).2) c <
      activeRaceTermE (internalMap A k)
        (A.latticeRate (recordMap A c k).2) c l
    rw [hwaitEq, hzero]
    exact lt_top_iff_ne_top.2 hwinnerFinite

/-- Hence a regular simple cell family exists. -/
theorem exists_recordRaceRegular
    (A : PerScaleDensityChannelAlignment Gamma beta v n hn) :
    ∃ c : CellFamily ι, RecordRaceRegular A c :=
  (recordRaceRegular_ae A).exists

/-!
THEOREM LIST
* `recordRaceRegular_ae`
* `exists_recordRaceRegular`

CLOSES
* The a.s. `RecordRaceRegular A c` from three existing a.s. events.

UNFINISHED
* Nothing in this file.
END
-/

end Ripple.Kurtz.StrongApprox.CellRecordRaceRegularAE

end
