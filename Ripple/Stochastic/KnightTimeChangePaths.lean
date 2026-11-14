import Ripple.Analysis.ClockInverse

/-!
# Deterministic paths for the completed Knight time change

The strict inverse and terminal clock are the installed definitions in
`Ripple.Analysis`. Evaluation of the raw path is useful only below the terminal
clock; above it the extended inverse is infinite and `toNNReal` is only a default.
The completed path uses a terminal value and an auxiliary path there instead.

These are deterministic statements. The stochastic bracket-flat lemma must
produce constancy on clock fibres simultaneously for every pair of physical
times. Finite-bracket martingale convergence must produce the terminal value
and its convergence hypothesis. Neither stochastic producer is proved here.
Continuity of the raw path and its left limit at a finite terminal clock are
also separate obligations; the results here prove the composition identity,
including terminal plateaux and the identically zero clock.
-/

open Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory

open Ripple.Analysis

/-- A path cannot change while its clock has the same value. The stochastic
producer must establish this for all times on a single full-measure set. -/
def ConstantOnClockFibres (A : ℝ≥0 → ℝ≥0) (M : ℝ≥0 → ℝ) : Prop :=
  ∀ s t, A s = A t → M s = M t

/-- The raw inverse-clock path. Its mathematical branch is `u < terminalClock A`.
The definition remains total by using the installed `ENNReal.toNNReal`. -/
noncomputable def rawTimeChangePath (M : ℝ≥0 → ℝ) (A : ℝ≥0 → ℝ≥0)
    (u : ℝ≥0) : ℝ :=
  M (clockInverse A u).toNNReal

/-- Complete an inverse-clock path after its finite terminal clock by an
auxiliary path starting at zero. For an infinite terminal clock only the first
branch is used. The terminal value is supplied by martingale convergence. -/
noncomputable def completedTimeChangePath (M : ℝ≥0 → ℝ) (A : ℝ≥0 → ℝ≥0)
    (terminalValue : ℝ) (W : ℝ≥0 → ℝ) (u : ℝ≥0) : ℝ :=
  if (u : ℝ≥0∞) < terminalClock A then rawTimeChangePath M A u
  else terminalValue + W (u - (terminalClock A).toNNReal)

/-- Below the terminal clock the completed path is the actual inverse-clock path. -/
theorem completedTimeChangePath_of_lt_terminal
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0} {terminalValue : ℝ} {W : ℝ≥0 → ℝ}
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < terminalClock A) :
    completedTimeChangePath M A terminalValue W u = rawTimeChangePath M A u := by
  simp only [completedTimeChangePath, if_pos hu]

/-- On and after a finite terminal clock the auxiliary path gives the formula. -/
theorem completedTimeChangePath_of_terminal_le
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0} {terminalValue : ℝ} {W : ℝ≥0 → ℝ}
    {u : ℝ≥0} (hu : terminalClock A ≤ (u : ℝ≥0∞)) :
    completedTimeChangePath M A terminalValue W u =
      terminalValue + W (u - (terminalClock A).toNNReal) := by
  simp only [completedTimeChangePath, if_neg (not_lt_of_ge hu)]

/-- Flat clock fibres remove the plateau ambiguity in the strict inverse. -/
theorem rawTimeChangePath_comp
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hflat : ConstantOnClockFibres A M) (t : ℝ≥0)
    (ht : (A t : ℝ≥0∞) < terminalClock A) :
    rawTimeChangePath M A (A t) = M t := by
  exact hflat _ t (clock_at_clockInverse hc hm hz ht)

/-- With an infinite terminal clock, the raw composition identity holds at every
physical time and needs no terminal convergence assumption. -/
theorem rawTimeChangePath_comp_of_terminal_eq_top
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hflat : ConstantOnClockFibres A M) (hterminal : terminalClock A = ⊤)
    (t : ℝ≥0) : rawTimeChangePath M A (A t) = M t := by
  apply rawTimeChangePath_comp hc hm hz hflat t
  rw [hterminal]
  exact ENNReal.coe_lt_top

/-- If the clock attains its terminal level, its monotonicity makes it constant
from that physical time onward. -/
theorem clock_eventually_eq_of_terminal_attained
    {A : ℝ≥0 → ℝ≥0} (hm : Monotone A) {t : ℝ≥0}
    (ht : (A t : ℝ≥0∞) = terminalClock A) :
    ∀ᶠ s in atTop, A s = A t := by
  filter_upwards [eventually_ge_atTop t] with s hs
  apply le_antisymm ?_ (hm hs)
  have hle : (A s : ℝ≥0∞) ≤ (A t : ℝ≥0∞) := by
    rw [ht]
    exact le_iSup (fun r : ℝ≥0 => (A r : ℝ≥0∞)) s
  exact_mod_cast hle

/-- Fibre constancy and convergence force an attained terminal level to have
the terminal path value. The desired identity is derived, not assumed. -/
theorem eq_terminalValue_of_terminal_attained
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0} {terminalValue : ℝ}
    (hm : Monotone A) (hflat : ConstantOnClockFibres A M)
    (hlim : Tendsto M atTop (𝓝 terminalValue)) {t : ℝ≥0}
    (ht : (A t : ℝ≥0∞) = terminalClock A) : M t = terminalValue := by
  have heq : ∀ᶠ s in atTop, M s = M t := by
    filter_upwards [clock_eventually_eq_of_terminal_attained hm ht] with s hs
    exact hflat s t hs
  have hconstant : Tendsto M atTop (𝓝 (M t)) := by
    apply tendsto_const_nhds.congr'
    exact (show M =ᶠ[atTop] fun _ => M t from heq).symm
  exact tendsto_nhds_unique hconstant hlim

/-- At a finite terminal clock, the completed path has the supplied terminal
value because the auxiliary path starts at zero. -/
theorem completedTimeChangePath_at_terminal
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0} {terminalValue : ℝ} {W : ℝ≥0 → ℝ}
    (hfinite : terminalClock A ≠ ⊤) (hW : W 0 = 0) :
    completedTimeChangePath M A terminalValue W (terminalClock A).toNNReal =
      terminalValue := by
  have hcoe := ENNReal.coe_toNNReal hfinite
  rw [completedTimeChangePath_of_terminal_le (le_of_eq hcoe.symm)]
  simp [hW]

/-- The completed composition identity handles both finite and infinite clocks.
Terminal convergence is required only when the terminal clock is finite. -/
theorem completedTimeChangePath_comp
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0} {terminalValue : ℝ} {W : ℝ≥0 → ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hflat : ConstantOnClockFibres A M)
    (hlim : terminalClock A ≠ ⊤ → Tendsto M atTop (𝓝 terminalValue))
    (hW : W 0 = 0) (t : ℝ≥0) :
    completedTimeChangePath M A terminalValue W (A t) = M t := by
  by_cases ht : (A t : ℝ≥0∞) < terminalClock A
  · rw [completedTimeChangePath_of_lt_terminal ht]
    exact rawTimeChangePath_comp hc hm hz hflat t ht
  · have hlevel : (A t : ℝ≥0∞) = terminalClock A :=
      le_antisymm (le_iSup (fun s : ℝ≥0 => (A s : ℝ≥0∞)) t) (le_of_not_gt ht)
    have hfinite : terminalClock A ≠ ⊤ := by
      rw [← hlevel]
      exact ENNReal.coe_ne_top
    have hto : (terminalClock A).toNNReal = A t := by
      rw [← hlevel]
      simp
    rw [← hto, completedTimeChangePath_at_terminal hfinite hW]
    exact (eq_terminalValue_of_terminal_attained hm hflat (hlim hfinite) hlevel).symm

/-- A zero terminal clock forces the entire nonnegative clock to vanish. -/
theorem clock_eq_zero_of_terminal_eq_zero
    {A : ℝ≥0 → ℝ≥0} (hzero : terminalClock A = 0) (t : ℝ≥0) : A t = 0 := by
  have hle : (A t : ℝ≥0∞) ≤ 0 := by
    rw [← hzero]
    exact le_iSup (fun s : ℝ≥0 => (A s : ℝ≥0∞)) t
  have heq : (A t : ℝ≥0∞) = 0 := le_antisymm hle bot_le
  exact_mod_cast heq

/-- In the zero-clock case fibre constancy forces the original path to be
constant. This covers a vanishing stochastic-integral channel. -/
theorem path_eq_initial_of_terminal_eq_zero
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0}
    (hflat : ConstantOnClockFibres A M) (hzero : terminalClock A = 0)
    (t : ℝ≥0) : M t = M 0 := by
  apply hflat
  rw [clock_eq_zero_of_terminal_eq_zero hzero t,
    clock_eq_zero_of_terminal_eq_zero hzero 0]

/-- With a zero clock, completion begins at internal time zero and uses the
whole auxiliary path, shifted by the supplied terminal value. -/
theorem completedTimeChangePath_of_terminal_eq_zero
    {M : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0} {terminalValue : ℝ} {W : ℝ≥0 → ℝ}
    (hzero : terminalClock A = 0) (u : ℝ≥0) :
    completedTimeChangePath M A terminalValue W u = terminalValue + W u := by
  rw [completedTimeChangePath_of_terminal_le (by rw [hzero]; exact bot_le)]
  simp [hzero]

end Ripple.ProbabilityTheory
