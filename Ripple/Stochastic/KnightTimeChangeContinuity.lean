import Ripple.Stochastic.KnightTimeChangePaths
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Continuity after collapsing clock fibres

A compact set of physical times whose path values stay away from a prescribed
value has a compact clock image. If the whole clock fibre has the prescribed
value, this image misses the clock level. This proves continuity without
asserting continuity of the strict inverse, which can jump across plateaux.
The same argument, with a small tail supplied by convergence in physical time,
proves the finite terminal left limit, including clocks that attain their limit.
-/

open Set Filter
open scoped NNReal ENNReal Topology

namespace Ripple.ProbabilityTheory
open Ripple.Analysis

/-- Near a clock level, all bounded physical preimages have nearby path values.
The fibre condition is required only at the single level under consideration. -/
theorem eventually_close_of_clock_fibre
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ} (hc : Continuous A) (hM : Continuous M)
    {u : ℝ≥0} {m : ℝ} (hf : ∀ t, A t = u → M t = m)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v in 𝓝 u, ∀ t, t ≤ T → A t = v → dist (M t) m < ε := by
  let K : Set ℝ≥0 := Icc 0 T ∩ {t | ε ≤ dist (M t) m}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const (hM.dist continuous_const))
  have hu : u ∉ A '' K := by
    rintro ⟨t, ht, htu⟩
    have hbad : ε ≤ dist (M t) m := ht.2
    rw [hf t htu, dist_self] at hbad
    exact (not_le_of_gt hε) hbad
  have hev : (A '' K)ᶜ ∈ 𝓝 u := (hK.image hc).isClosed.isOpen_compl.mem_nhds hu
  filter_upwards [hev] with v hv t ht htv
  apply lt_of_not_ge
  intro hbad
  exact hv ⟨t, ⟨⟨bot_le, ht⟩, hbad⟩, htv⟩

/-- The raw time-changed path is continuous at every subterminal level.
The inverse need not be continuous. -/
theorem continuousAt_rawTimeChangePath
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hM : Continuous M) (hf : ConstantOnClockFibres A M)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < terminalClock A) :
    ContinuousAt (rawTimeChangePath M A) u := by
  obtain ⟨T, hT⟩ := lt_iSup_iff.mp hu
  have huT : u < A T := by exact_mod_cast hT
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hfibre : ∀ t, A t = u → M t = rawTimeChangePath M A u := by
    intro t ht
    exact hf t _ (ht.trans (clock_at_clockInverse hc hm hz hu).symm)
  filter_upwards [eventually_close_of_clock_fibre hc hM hfibre T hε,
    eventually_lt_nhds huT] with v hv hvT
  have hvterm : (v : ℝ≥0∞) < terminalClock A :=
    (show (v : ℝ≥0∞) < (A T : ℝ≥0∞) by exact_mod_cast hvT).trans_le
      (le_iSup (fun t : ℝ≥0 => (A t : ℝ≥0∞)) T)
  have hfin := clockInverse_ne_top_of_lt_terminal hvterm
  have hbound : (clockInverse A v).toNNReal ≤ T := by
    have h := clockInverse_le_of_lt hvT
    rw [← ENNReal.coe_toNNReal hfin] at h
    exact_mod_cast h
  exact hv _ hbound (clock_at_clockInverse hc hm hz hvterm)

/-- The natural domain of the raw path includes internal time zero whenever
the terminal clock is positive. -/
theorem continuousOn_rawTimeChangePath
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hM : Continuous M) (hf : ConstantOnClockFibres A M) :
    ContinuousOn (rawTimeChangePath M A) {u | (u : ℝ≥0∞) < terminalClock A} :=
  fun _ hu => (continuousAt_rawTimeChangePath hc hm hz hM hf hu).continuousWithinAt

/-- The limit as internal time approaches a finite terminal clock from below.
For terminal clock zero the source filter is empty, as it should be. -/
theorem tendsto_rawTimeChangePath_terminal
    {A : ℝ≥0 → ℝ≥0} {M : ℝ≥0 → ℝ} {m : ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hM : Continuous M) (hf : ConstantOnClockFibres A M)
    (hfinite : terminalClock A ≠ ⊤) (hlim : Tendsto M atTop (𝓝 m)) :
    Tendsto (rawTimeChangePath M A) (𝓝[<] (terminalClock A).toNNReal) (𝓝 m) := by
  let a := (terminalClock A).toNNReal
  have ha : (a : ℝ≥0∞) = terminalClock A := ENNReal.coe_toNNReal hfinite
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hlim) ε hε)
  have hfibre : ∀ t, A t = a → M t = m := by
    intro t ht
    apply eq_terminalValue_of_terminal_attained hm hf hlim
    exact (congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) ht).trans ha
  have hnear := (eventually_close_of_clock_fibre hc hM hfibre T hε).filter_mono
    (nhdsWithin_le_nhds (s := Set.Iio a))
  filter_upwards [hnear, self_mem_nhdsWithin] with v hv hva
  have hvterm : (v : ℝ≥0∞) < terminalClock A := by
    rw [← ha]
    exact_mod_cast (show v < a from hva)
  by_cases ht : (clockInverse A v).toNNReal ≤ T
  · exact hv _ ht (clock_at_clockInverse hc hm hz hvterm)
  · exact hT _ (le_of_not_ge ht)

/-- Joining two one-sided limits gives continuity at a seam with a non-strict
right branch. This also works at the left endpoint of the nonnegative axis. -/
theorem continuousAt_if_lt_seam
    {E : Type*} [TopologicalSpace E] {f g : ℝ≥0 → E} {a : ℝ≥0}
    (hl : Tendsto f (𝓝[<] a) (𝓝 (g a))) (hr : ContinuousAt g a) :
    ContinuousAt (fun u => if u < a then f u else g u) a := by
  have hleft : Tendsto (fun u => if u < a then f u else g u)
      (𝓝[<] a) (𝓝 (g a)) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp [show u < a from hu]
  have hright : Tendsto (fun u => if u < a then f u else g u)
      (𝓝[≥] a) (𝓝 (g a)) := by
    apply (hr.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp [not_lt_of_ge (show a ≤ u from hu)]
  have hunion : Iio a ∪ Ici a = (univ : Set ℝ≥0) := by ext u; simp
  have h := hleft.sup hright
  rw [← nhdsWithin_union, hunion, nhdsWithin_univ] at h
  simpa [ContinuousAt] using h

/-- Continuity at the completed-clock seam follows from physical terminal
convergence and an auxiliary path continuous at zero and starting at zero. -/
theorem continuousAt_completedTimeChangePath_terminal
    {A : ℝ≥0 → ℝ≥0} {M W : ℝ≥0 → ℝ} {m : ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hM : Continuous M) (hf : ConstantOnClockFibres A M)
    (hfinite : terminalClock A ≠ ⊤) (hlim : Tendsto M atTop (𝓝 m))
    (hW : Continuous W) (hzero : W 0 = 0) :
    ContinuousAt (completedTimeChangePath M A m W) (terminalClock A).toNNReal := by
  let a := (terminalClock A).toNNReal
  have ha : (a : ℝ≥0∞) = terminalClock A := ENNReal.coe_toNNReal hfinite
  have heq : completedTimeChangePath M A m W =
      fun u => if u < a then rawTimeChangePath M A u else m + W (u - a) := by
    funext u
    simp only [completedTimeChangePath, ← ha, ENNReal.coe_lt_coe, ENNReal.toNNReal_coe]
  rw [heq]
  apply continuousAt_if_lt_seam
  · simpa [hzero] using tendsto_rawTimeChangePath_terminal hc hm hz hM hf hfinite hlim
  · exact (continuous_const.add (hW.comp (continuous_id.sub continuous_const))).continuousAt

/-- The completed inverse-clock path is continuous on the entire internal
time axis, with the finite terminal convergence hypothesis used only at its
seam. The auxiliary path is used only for finite terminal clocks. -/
theorem continuous_completedTimeChangePath
    {A : ℝ≥0 → ℝ≥0} {M W : ℝ≥0 → ℝ} {m : ℝ}
    (hc : Continuous A) (hm : Monotone A) (hz : A 0 = 0)
    (hM : Continuous M) (hf : ConstantOnClockFibres A M)
    (hlim : terminalClock A ≠ ⊤ → Tendsto M atTop (𝓝 m))
    (hW : Continuous W) (hzero : W 0 = 0) :
    Continuous (completedTimeChangePath M A m W) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : (u : ℝ≥0∞) < terminalClock A
  · change Tendsto (completedTimeChangePath M A m W) (𝓝 u)
      (𝓝 (completedTimeChangePath M A m W u))
    rw [completedTimeChangePath_of_lt_terminal hu]
    apply (continuousAt_rawTimeChangePath hc hm hz hM hf hu).tendsto.congr'
    have hev : ∀ᶠ v : ℝ≥0 in 𝓝 u, (v : ℝ≥0∞) < terminalClock A :=
      ENNReal.continuous_coe.continuousAt.eventually (gt_mem_nhds hu)
    filter_upwards [hev] with v hv
    exact (completedTimeChangePath_of_lt_terminal hv).symm
  · have hle := le_of_not_gt hu
    have hfinite : terminalClock A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    let a := (terminalClock A).toNNReal
    have ha : (a : ℝ≥0∞) = terminalClock A := ENNReal.coe_toNNReal hfinite
    have hau : a ≤ u := by
      rw [← ha] at hle
      exact_mod_cast hle
    rcases eq_or_lt_of_le hau with heq | hlt
    · rw [← heq]
      exact continuousAt_completedTimeChangePath_terminal hc hm hz hM hf hfinite
        (hlim hfinite) hW hzero
    · have happ : Continuous (fun v : ℝ≥0 => m + W (v - a)) :=
        continuous_const.add (hW.comp (continuous_id.sub continuous_const))
      change Tendsto (completedTimeChangePath M A m W) (𝓝 u)
        (𝓝 (completedTimeChangePath M A m W u))
      rw [completedTimeChangePath_of_terminal_le (le_of_not_gt hu)]
      apply happ.continuousAt.tendsto.congr'
      filter_upwards [eventually_gt_nhds hlt] with v hv
      have hlevel : terminalClock A ≤ (v : ℝ≥0∞) := by
        rw [← ha]
        exact_mod_cast hv.le
      exact (completedTimeChangePath_of_terminal_le hlevel).symm

end Ripple.ProbabilityTheory
