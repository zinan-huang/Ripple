-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingOldBlocks.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingObservedBlocks
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingNumerics

/-!
# Calibrated old-index extinction over completed observed blocks

The work length is ceil(100 n^2 / M), the conservative ready-zero drift is
.77 M / n^2, and the number of blocks is floor(log n / 3) - 6.
The result is a joint bound under the original law. Constructing the clock's
specific starts and proving their completion is intentionally a separate
obligation from this probability theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingOldBlocks

open TimeTheorem PhaseOneDrain AveragingIntegerPotential AveragingWorkCounter
open AveragingObservedBlocks AveragingNumerics

variable {L : ℕ}

def oldWorkRate (n M : ℕ) : ℝ := (77 / 100 : ℝ) * M / (n : ℝ) ^ 2

def oldWorkTrials (n M : ℕ) : ℕ := Nat.ceil ((100 : ℝ) * (n : ℝ) ^ 2 / M)

theorem oldWorkRate_nonneg (n M : ℕ) : 0 ≤ oldWorkRate n M := by
  unfold oldWorkRate
  positivity

theorem oldWorkRate_lt_one (n M : ℕ) (hn : 1 ≤ n) (hM : M ≤ n) :
    oldWorkRate n M < 1 := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hMr : (M : ℝ) ≤ n := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by linarith
  have hsquare : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  unfold oldWorkRate
  apply (div_lt_iff₀ (sq_pos_of_pos hnpos)).2
  nlinarith

theorem oldWorkRate_trials (n M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    (77 : ℝ) ≤ oldWorkRate n M * oldWorkTrials n M := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hceil := Nat.le_ceil ((100 : ℝ) * (n : ℝ) ^ 2 / M)
  have hmul := mul_le_mul_of_nonneg_left hceil (oldWorkRate_nonneg n M)
  have heq : oldWorkRate n M * ((100 : ℝ) * (n : ℝ) ^ 2 / M) = 77 := by
    unfold oldWorkRate
    field_simp [ne_of_gt hMr, ne_of_gt hnr]
    <;> ring
  simpa only [oldWorkTrials, heq] using hmul

theorem geometric_blocks_le_exp (r : ℝ) (hrnonneg : 0 ≤ r) (hrlt : r < 1)
    (B N : ℕ) (hwork : (77 : ℝ) ≤ r * N) :
    (1 - ENNReal.ofReal r) ^ (B * N) ≤
      ENNReal.ofReal (Real.exp (-77 * (B : ℝ))) := by
  have hbase : 1 - r ≤ Real.exp (-r) := by
    linarith only [Real.add_one_le_exp (-r)]
  have hreal :
      (1 - r) ^ (B * N) ≤ Real.exp (-77 * (B : ℝ)) := by
    calc
      (1 - r) ^ (B * N) ≤ (Real.exp (-r)) ^ (B * N) :=
        pow_le_pow_left₀ (sub_nonneg.mpr hrlt.le) hbase _
      _ = Real.exp (-r * ((B * N : ℕ) : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (-77 * (B : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hwork (Nat.cast_nonneg B)
        push_cast
        nlinarith only [hmul]
  have heq :
      ENNReal.ofReal ((1 - r) ^ (B * N)) =
        (1 - ENNReal.ofReal r) ^ (B * N) := by
    rw [ENNReal.ofReal_pow (sub_nonneg.mpr hrlt.le),
      ENNReal.ofReal_sub 1 hrnonneg, ENNReal.ofReal_one]
  rw [← heq]
  exact ENNReal.ofReal_le_ofReal hreal

theorem old_blocks_constant (n M Ψ : ℕ) (hn : timePopulationThreshold ≤ n)
    (hMpos : 0 < M) (hMle : M ≤ n) (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n) :
    (1 - ENNReal.ofReal (oldWorkRate n M)) ^
        ((oldCutoff n - 6) * oldWorkTrials n M) * Ψ ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) := by
  have hnpos : 0 < n := by exact_mod_cast (population_log_lower hn).1
  have hgeom := geometric_blocks_le_exp (oldWorkRate n M)
    (oldWorkRate_nonneg n M) (oldWorkRate_lt_one n M (by omega) hMle)
    (oldCutoff n - 6) (oldWorkTrials n M) (oldWorkRate_trials n M hnpos hMpos)
  have hmass : (Ψ : ℝ) * Real.exp (-77 * ((oldCutoff n - 6 : ℕ) : ℝ)) ≤
      1 / (n : ℝ) ^ 20 :=
    (mul_le_mul_of_nonneg_right hΨ (Real.exp_pos _).le).trans
      (old_blocks_natural_exponent hn)
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-77 * ((oldCutoff n - 6 : ℕ) : ℝ))) * Ψ :=
      mul_le_mul_right' hgeom _
    _ = ENNReal.ofReal
        ((Ψ : ℝ) * Real.exp (-77 * ((oldCutoff n - 6 : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg Ψ), ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal hmass

/-- The calibrated n^-20 old-index tail for q-6 completed observed blocks. -/
theorem old_blocks_extinction_tail
    (n M : ℕ) (hn : timePopulationThreshold ≤ n) (hMpos : 0 < M) (hMle : M ≤ n)
    (init : Cfg L 256) (s h : ℕ) (hh : 1 ≤ h)
    (A : Set ((i : Finset.Iic s) → Draw L 256)) (Ψ : ℕ)
    (hΨ : (Ψ : ℝ) ≤ (1 / 1000 : ℝ) * n)
    (σ : Fin (oldCutoff n - 6) → Ω L 256 → WithTop ℕ)
    (hσ : ∀ j, PairLogPastTime (σ j)) (T : ℕ) :
    law init {ω |
        WorkLive init s h (ENNReal.ofReal (oldWorkRate n M)) A Ψ
          (blockWork s (oldWorkTrials n M) σ) T ω ∧
        BlocksComplete s (oldWorkTrials n M) σ T ω ∧
        1 ≤ augmentedPhiNat h (trace init ω (s + T))} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} := by
  refine (observed_blocks_extinction_tail init s h hh
    (ENNReal.ofReal (oldWorkRate n M))
    (ENNReal.ofReal_lt_one.mpr
      (oldWorkRate_lt_one n M (by
        have hnp : 0 < n := by exact_mod_cast (population_log_lower hn).1
        omega) hMle))
    A Ψ (oldWorkTrials n M) σ hσ T).trans ?_
  exact mul_le_mul_right' (old_blocks_constant n M Ψ hn hMpos hMle hΨ) _

end Ripple.PopulationProtocol.ExactMajority.AveragingOldBlocks

end
