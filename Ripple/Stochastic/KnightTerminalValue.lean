import Ripple.Stochastic.KnightStoppedClock
import Ripple.Stochastic.DoobContinuous
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Measurable terminal values and the finite-clock localization step

The terminal variable is the measurable limsup of integer observations. On
convergent paths it equals the physical-time limit. Integer martingale
convergence is proved from the installed discrete convergence theorem.
An explicit block-oscillation criterion upgrades this to convergence along
all nonnegative times. The final localization step uses actual inverse-clock
stopped paths and does not evaluate an infinite inverse at zero.

For a stochastic integral, the random-stopping martingale/isometry producer
and the summable block-square estimate must still instantiate these criteria.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory
open Ripple.Analysis

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A total measurable candidate; on a convergent path it has the usual limit.
Its value on nonconvergent paths carries no probabilistic assertion. -/
noncomputable def knightTerminalValue (M : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  limsup (fun n : ℕ => M (n : ℝ≥0) ω) atTop

theorem measurable_knightTerminalValue {M : ℝ≥0 → Ω → ℝ}
    (hM : ∀ n : ℕ, Measurable (M (n : ℝ≥0))) : Measurable (knightTerminalValue M) :=
  Measurable.limsup hM

/-- Natural physical times tend to infinity on the nonnegative time axis. -/
theorem tendsto_nnreal_natCast : Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨n, hn⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop n] with k hk
  exact hn.trans (by exact_mod_cast hk)

theorem knightTerminalValue_eq_of_tendsto {M : ℝ≥0 → Ω → ℝ} {ω : Ω} {l : ℝ}
    (hlim : Tendsto (fun t => M t ω) atTop (𝓝 l)) : knightTerminalValue M ω = l :=
  (hlim.comp tendsto_nnreal_natCast).limsup_eq

/-- Monotonicity reduces the uncountable terminal-clock supremum to integers. -/
theorem terminalClock_eq_iSup_nat {A : ℝ≥0 → ℝ≥0} (hm : Monotone A) :
    terminalClock A = ⨆ n : ℕ, (A n : ℝ≥0∞) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact (show (A t : ℝ≥0∞) ≤ (A n : ℝ≥0∞) by exact_mod_cast hm hn).trans
      (le_iSup (fun k : ℕ => (A k : ℝ≥0∞)) n)
  · exact iSup_le fun n => le_iSup (fun t : ℝ≥0 => (A t : ℝ≥0∞)) (n : ℝ≥0)

/-- Terminal-clock measurability uses only integer evaluations and pathwise
monotonicity; no uncountable supremum measurability is assumed. -/
theorem measurable_terminalClock {A : ℝ≥0 → Ω → ℝ≥0}
    (hA : ∀ n : ℕ, Measurable (A n)) (hm : ∀ ω, Monotone (fun t => A t ω)) :
    Measurable (fun ω => terminalClock (fun t => A t ω)) := by
  have heq : (fun ω => terminalClock (fun t => A t ω)) =
      fun ω => ⨆ n : ℕ, (A n ω : ℝ≥0∞) := funext fun ω => terminalClock_eq_iSup_nat (hm ω)
  rw [heq]
  exact Measurable.iSup fun n => ENNReal.continuous_coe.measurable.comp (hA n)

/-- The finite-clock event is measurable for an everywhere monotone clock. -/
theorem measurableSet_finite_terminalClock {A : ℝ≥0 → Ω → ℝ≥0}
    (hA : ∀ n : ℕ, Measurable (A n)) (hm : ∀ ω, Monotone (fun t => A t ω)) :
    MeasurableSet {ω | terminalClock (fun t => A t ω) ≠ ⊤} :=
  ((measurable_terminalClock hA hm) (measurableSet_singleton ⊤)).compl

/-- The canonical integer-skeleton limit is measurable and agrees with the
limsup candidate, for a martingale uniformly bounded in first moment. -/
theorem ae_integer_tendsto_knightTerminalValue
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) {R : ℝ≥0}
    (hbound : ∀ n : ℕ, eLpNorm (M n) 1 P ≤ R) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => M (n : ℝ≥0) ω) atTop
      (𝓝 (knightTerminalValue M ω)) := by
  have hmono : Monotone (fun n : ℕ => (n : ℝ≥0)) := Nat.mono_cast
  have hN := Ripple.Stochastic.Doob.martingale_compMono hM (fun n : ℕ => (n : ℝ≥0)) hmono
  have hlim := hN.submartingale.ae_tendsto_limitProcess hbound
  filter_upwards [hlim] with ω hω
  have heq : knightTerminalValue M ω = _ := hω.limsup_eq
  rw [heq]
  exact hω

/-- Deterministic block control upgrades integer convergence to full-time
convergence. Continuity alone does not provide the block control. -/
theorem tendsto_of_integer_limit_and_block_control
    {M : ℝ≥0 → ℝ} {l : ℝ} {b : ℕ → ℝ}
    (hN : Tendsto (fun n : ℕ => M n) atTop (𝓝 l))
    (hb : Tendsto b atTop (𝓝 0))
    (hblock : ∀ (n : ℕ) (t : ℝ≥0), (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      dist (M t) (M n) ≤ b n) : Tendsto M atTop (𝓝 l) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hNbound⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hN) (ε / 2) (by positivity))
  obtain ⟨K, hKbound⟩ := eventually_atTop.mp (hb.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
  filter_upwards [eventually_ge_atTop ((max N K : ℕ) : ℝ≥0)] with t ht
  let n : ℕ := ⌊(t : ℝ)⌋₊
  have hnlo : (n : ℝ≥0) ≤ t := by exact_mod_cast (Nat.floor_le t.coe_nonneg)
  have hnhi : t ≤ (n : ℝ≥0) + 1 := by exact_mod_cast (Nat.lt_floor_add_one (t : ℝ)).le
  have hnk : max N K ≤ n := Nat.le_floor (by exact_mod_cast ht)
  calc dist (M t) l ≤ dist (M t) (M n) + dist (M n) l := dist_triangle _ _ _
       _ ≤ b n + dist (M n) l := add_le_add (hblock n t hnlo hnhi) le_rfl
       _ < ε / 2 + ε / 2 := add_lt_add (hKbound n ((le_max_right N K).trans hnk))
         (hNbound n ((le_max_left N K).trans hnk))
       _ = ε := by ring

/-- Summable expected squares of block bounds imply almost-sure vanishing of
the block bounds. This is the measure-theoretic endpoint of the Doob-on-blocks
argument; no independence of blocks is needed. -/
theorem ae_tendsto_zero_of_summable_block_squares
    {P : Measure Ω} {b : ℕ → Ω → ℝ}
    (hb : ∀ n, Measurable (b n))
    (hsum : (∑' n, ∫⁻ ω, (‖b n ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n => |b n ω|) atTop (𝓝 0) := by
  let q : ℕ → Ω → ℝ≥0 := fun n ω => ‖b n ω‖₊ ^ 2
  have hq : ∀ n, Measurable (fun ω => (q n ω : ℝ≥0∞)) := by
    intro n
    exact ENNReal.continuous_coe.measurable.comp ((hb n).nnnorm.pow_const 2)
  have hsum' : (∫⁻ ω, ∑' n, (q n ω : ℝ≥0∞) ∂P) ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (hq n).aemeasurable)]
    simpa [q] using hsum
  have hfinite := ae_lt_top' (Measurable.aemeasurable (Measurable.tsum hq)) hsum'
  filter_upwards [hfinite] with ω hω
  have hs : Summable (fun n => (q n ω : ℝ)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hω.ne
  have hz := hs.tendsto_atTop_zero
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  have hs2 : Tendsto (fun n => |b n ω|) atTop (𝓝 (Real.sqrt 0)) :=
    hsqrt.congr (fun n => by simp [q, Real.sqrt_sq_eq_abs])
  simpa using hs2

/-- A summable block-square estimate and discrete martingale convergence give
the full half-line limit, with a measurable terminal value already fixed. -/
theorem ae_tendsto_knightTerminalValue_of_blocks
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P) {R : ℝ≥0}
    (hbound : ∀ n : ℕ, eLpNorm (M n) 1 P ≤ R)
    (b : ℕ → Ω → ℝ) (hb : ∀ n, Measurable (b n))
    (hsum : (∑' n, ∫⁻ ω, (‖b n ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤)
    (hblock : ∀ᵐ ω ∂P, ∀ (n : ℕ) (t : ℝ≥0), (n : ℝ≥0) ≤ t → t ≤ (n : ℝ≥0) + 1 →
      dist (M t ω) (M n ω) ≤ |b n ω|) :
    ∀ᵐ ω ∂P, Tendsto (fun t => M t ω) atTop (𝓝 (knightTerminalValue M ω)) := by
  filter_upwards [ae_integer_tendsto_knightTerminalValue hM hbound,
    ae_tendsto_zero_of_summable_block_squares hb hsum, hblock] with ω hN hbω hblockω
  exact tendsto_of_integer_limit_and_block_control hN hbω hblockω

/-- A finite terminal clock lies strictly below some integer level. -/
theorem exists_nat_gt_terminalClock {A : ℝ≥0 → ℝ≥0} (h : terminalClock A ≠ ⊤) :
    ∃ n : ℕ, terminalClock A < ((n : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (terminalClock A).toNNReal
  refine ⟨n, ?_⟩
  rw [← ENNReal.coe_toNNReal h]
  exact_mod_cast hn

/-- Countable localization removes the bracket cap. The input is convergence
of the concrete clock-stopped processes; arbitrary replacement processes are
not accepted. The output has one exceptional set and a measurable candidate. -/
theorem ae_tendsto_on_finite_terminalClock_of_stopped
    {P : Measure Ω} {M : ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ≥0}
    (hStoppedConvergence : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ l : ℝ,
      Tendsto (clockStoppedPath (fun t => M t ω) (fun t => A t ω) n) atTop (𝓝 l)) :
    ∀ᵐ ω ∂P, terminalClock (fun t => A t ω) ≠ ⊤ →
      Tendsto (fun t => M t ω) atTop (𝓝 (knightTerminalValue M ω)) := by
  have hall := ae_all_iff.mpr hStoppedConvergence
  filter_upwards [hall] with ω hω hfinite
  obtain ⟨n, hn⟩ := exists_nat_gt_terminalClock hfinite
  obtain ⟨l, hl⟩ := hω n
  rw [clockStoppedPath_eq_of_terminal_le hn.le] at hl
  rw [knightTerminalValue_eq_of_tendsto hl]
  exact hl

end Ripple.ProbabilityTheory
