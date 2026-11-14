-- Ripple/Analysis/PeanoBoundedExistence.lean
import Mathlib

/-!
# Peano existence for a globally bounded finite-dimensional vector field

The approximation is a delayed Picard scheme. For mesh `h`, the `k`-th
iterate has stabilized on `[0, k*h]`; choosing `h = T/(n+1)` therefore gives
an exact delayed integral equation on `[0,T]`. Uniform boundedness of the
vector field gives a common Lipschitz constant, so Arzelà–Ascoli applies.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped BigOperators Topology NNReal Interval UniformConvergence BoundedContinuousFunction

namespace Ripple.Analysis.PeanoBoundedExistence

variable {ι : Type*} [Fintype ι]

local notation "V" => (ι → ℝ)

private def peanoDelay (h t : ℝ) : ℝ :=
  max 0 (t - h)

@[fun_prop]
private theorem continuous_peanoDelay (h : ℝ) :
    Continuous (peanoDelay h) := by
  unfold peanoDelay
  fun_prop

private theorem peanoDelay_mem
    {h T s : ℝ} (hh : 0 ≤ h) (hs : s ∈ Icc (0 : ℝ) T) :
    peanoDelay h s ∈ Icc (0 : ℝ) T := by
  unfold peanoDelay
  constructor
  · exact le_max_left _ _
  · exact max_le (hs.1.trans hs.2) ((sub_le_self s hh).trans hs.2)

private theorem dist_peanoDelay_self_le
    {h s : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) :
    dist (peanoDelay h s) s ≤ h := by
  have hle : peanoDelay h s ≤ s := by
    unfold peanoDelay
    exact max_le hs (sub_le_self s hh)
  have hlo : s - h ≤ peanoDelay h s := by
    unfold peanoDelay
    exact le_max_right _ _
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith

private noncomputable def peanoStep
    (G : V → V) (xZero : V) (h : ℝ) (f : ℝ → V) (t : ℝ) : V :=
  xZero + ∫ s in (0 : ℝ)..t, G (f (peanoDelay h s))

private theorem continuous_peanoStep
    {G : V → V} {xZero : V} {h : ℝ} {f : ℝ → V}
    (hG : Continuous G) (hf : Continuous f) :
    Continuous (peanoStep G xZero h f) := by
  have hc : Continuous (fun s => G (f (peanoDelay h s))) :=
    hG.comp (hf.comp (continuous_peanoDelay h))
  exact continuous_const.add
    (intervalIntegral.continuous_primitive
      (fun a b => hc.intervalIntegrable a b) 0)

private theorem lipschitzWith_peanoStep
    {G : V → V} {xZero : V} {h Bnd : ℝ} {f : ℝ → V}
    (hG : Continuous G) (hBnd0 : 0 ≤ Bnd)
    (hBnd : ∀ y, ‖G y‖ ≤ Bnd) (hf : Continuous f) :
    LipschitzWith (⟨Bnd, hBnd0⟩ : ℝ≥0) (peanoStep G xZero h f) := by
  have hc : Continuous (fun s => G (f (peanoDelay h s))) :=
    hG.comp (hf.comp (continuous_peanoDelay h))
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [dist_eq_norm, peanoStep, peanoStep, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 s) (hc.intervalIntegrable 0 t),
    Real.dist_eq]
  simpa using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := s) (C := Bnd)
      (fun r _ => hBnd (f (peanoDelay h r))))

private noncomputable def peanoIterate
    (G : V → V) (xZero : V) (h : ℝ) : ℕ → ℝ → V
  | 0 => fun _ => xZero
  | k + 1 => peanoStep G xZero h (peanoIterate G xZero h k)

@[simp]
private theorem peanoIterate_zero
    (G : V → V) (xZero : V) (h t : ℝ) :
    peanoIterate G xZero h 0 t = xZero := rfl

@[simp]
private theorem peanoIterate_succ
    (G : V → V) (xZero : V) (h : ℝ) (k : ℕ) :
    peanoIterate G xZero h (k + 1) =
      peanoStep G xZero h (peanoIterate G xZero h k) := rfl

private theorem continuous_peanoIterate
    (G : V → V) (hG : Continuous G) (xZero : V) (h : ℝ) :
    ∀ k, Continuous (peanoIterate G xZero h k)
  | 0 => continuous_const
  | k + 1 =>
      continuous_peanoStep hG
        (continuous_peanoIterate G hG xZero h k)

private theorem peanoIterate_at_zero
    (G : V → V) (xZero : V) (h : ℝ) :
    ∀ k, peanoIterate G xZero h k 0 = xZero
  | 0 => rfl
  | k + 1 => by
      rw [peanoIterate_succ]
      simp [peanoStep]

private theorem lipschitzWith_peanoIterate_succ
    (G : V → V) (hG : Continuous G) (xZero : V)
    {h Bnd : ℝ} (hBnd0 : 0 ≤ Bnd)
    (hBnd : ∀ y, ‖G y‖ ≤ Bnd) (k : ℕ) :
    LipschitzWith (⟨Bnd, hBnd0⟩ : ℝ≥0)
      (peanoIterate G xZero h (k + 1)) := by
  simpa only [peanoIterate_succ] using
    lipschitzWith_peanoStep hG hBnd0 hBnd
      (continuous_peanoIterate G hG xZero h k)

private theorem peanoIterate_stable
    (G : V → V) (xZero : V) {h : ℝ} (hh : 0 ≤ h) :
    ∀ (k : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) ((k : ℝ) * h) →
      peanoIterate G xZero h (k + 1) t =
        peanoIterate G xZero h k t
  | 0, t, ht => by
      have ht0 : t = 0 := by
        simp only [Nat.cast_zero, zero_mul, mem_Icc] at ht
        linarith
      subst t
      simp [peanoIterate_at_zero]
  | k + 1, t, ht => by
      rw [peanoIterate_succ, peanoIterate_succ]
      unfold peanoStep
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      apply congrArg G
      apply peanoIterate_stable G xZero hh k
      constructor
      · exact le_max_left _ _
      · unfold peanoDelay
        apply max_le
        · exact mul_nonneg (Nat.cast_nonneg k) hh
        · have htUpper := ht.2
          push_cast at htUpper
          nlinarith [hs.2]

private def peanoMesh (T : ℝ) (n : ℕ) : ℝ :=
  T / ((n + 1 : ℕ) : ℝ)

private theorem peanoMesh_nonneg
    {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ peanoMesh T n := by
  unfold peanoMesh
  positivity

private theorem peanoMesh_mul (T : ℝ) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * peanoMesh T n = T := by
  have hne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold peanoMesh
  field_simp [hne]

private noncomputable def peanoApprox
    (G : V → V) (xZero : V) (T : ℝ) (n : ℕ) : ℝ → V :=
  peanoIterate G xZero (peanoMesh T n) (n + 1)

private theorem continuous_peanoApprox
    (G : V → V) (hG : Continuous G) (xZero : V)
    (T : ℝ) (n : ℕ) :
    Continuous (peanoApprox G xZero T n) := by
  unfold peanoApprox
  exact continuous_peanoIterate G hG xZero _ _

private theorem peanoApprox_at_zero
    (G : V → V) (xZero : V) (T : ℝ) (n : ℕ) :
    peanoApprox G xZero T n 0 = xZero := by
  unfold peanoApprox
  exact peanoIterate_at_zero G xZero _ _

private theorem lipschitzWith_peanoApprox
    (G : V → V) (hG : Continuous G) (xZero : V)
    {T Bnd : ℝ} (hBnd0 : 0 ≤ Bnd)
    (hBnd : ∀ y, ‖G y‖ ≤ Bnd) (n : ℕ) :
    LipschitzWith (⟨Bnd, hBnd0⟩ : ℝ≥0)
      (peanoApprox G xZero T n) := by
  unfold peanoApprox
  exact lipschitzWith_peanoIterate_succ
    G hG xZero hBnd0 hBnd n

private theorem peanoApprox_eq_delayed
    (G : V → V) (xZero : V) {T : ℝ} (hT : 0 ≤ T)
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    peanoApprox G xZero T n t =
      xZero + ∫ s in (0 : ℝ)..t,
        G (peanoApprox G xZero T n (peanoDelay (peanoMesh T n) s)) := by
  have hinterval :
      t ∈ Icc (0 : ℝ) (((n + 1 : ℕ) : ℝ) * peanoMesh T n) := by
    rw [peanoMesh_mul]
    exact ht
  change
    peanoIterate G xZero (peanoMesh T n) (n + 1) t =
      peanoIterate G xZero (peanoMesh T n) ((n + 1) + 1) t
  exact (peanoIterate_stable G xZero
    (peanoMesh_nonneg hT n) (n + 1) t hinterval).symm

private noncomputable def peanoApproxBCF
    (G : V → V) (hG : Continuous G) (xZero : V)
    (T : ℝ) (n : ℕ) : Icc (0 : ℝ) T →ᵇ V :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => peanoApprox G xZero T n t.1,
      (continuous_peanoApprox G hG xZero T n).comp continuous_subtype_val⟩

private theorem lipschitzWith_peanoApproxBCF
    (G : V → V) (hG : Continuous G) (xZero : V)
    {T Bnd : ℝ} (hBnd0 : 0 ≤ Bnd)
    (hBnd : ∀ y, ‖G y‖ ≤ Bnd) (n : ℕ) :
    LipschitzWith (⟨Bnd, hBnd0⟩ : ℝ≥0)
      (peanoApproxBCF G hG xZero T n) := by
  change LipschitzWith (⟨Bnd, hBnd0⟩ : ℝ≥0)
    (fun t : Icc (0 : ℝ) T => peanoApprox G xZero T n t.1)
  simpa using
    (lipschitzWith_peanoApprox G hG xZero hBnd0 hBnd n).comp
      (LipschitzWith.subtype_val (Icc (0 : ℝ) T))

private theorem peanoApproxBCF_mem_closedBall
    (G : V → V) (hG : Continuous G) (xZero : V)
    {T Bnd : ℝ} (hT : 0 ≤ T) (hBnd0 : 0 ≤ Bnd)
    (hBnd : ∀ y, ‖G y‖ ≤ Bnd) (n : ℕ)
    (t : Icc (0 : ℝ) T) :
    peanoApproxBCF G hG xZero T n t ∈
      closedBall xZero (Bnd * T) := by
  let z : Icc (0 : ℝ) T := ⟨0, ⟨le_rfl, hT⟩⟩
  have hz : peanoApproxBCF G hG xZero T n z = xZero := by
    change peanoApprox G xZero T n 0 = xZero
    exact peanoApprox_at_zero G xZero T n
  have hlip :=
    (lipschitzWith_peanoApproxBCF G hG xZero hBnd0 hBnd n).dist_le_mul t z
  rw [mem_closedBall]
  calc
    dist (peanoApproxBCF G hG xZero T n t) xZero =
        dist (peanoApproxBCF G hG xZero T n t)
          (peanoApproxBCF G hG xZero T n z) := by rw [hz]
    _ ≤ ((⟨Bnd, hBnd0⟩ : ℝ≥0) : ℝ) * dist t z := hlip
    _ = Bnd * t.1 := by
      simp [z, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg t.2.1]
    _ ≤ Bnd * T := mul_le_mul_of_nonneg_left t.2.2 hBnd0

private noncomputable def peanoExtension
    {T : ℝ} (hT : 0 ≤ T) (f : Icc (0 : ℝ) T →ᵇ V) (t : ℝ) : V :=
  f (projIcc 0 T hT t)

@[simp]
private theorem peanoExtension_of_mem
    {T : ℝ} (hT : 0 ≤ T) (f : Icc (0 : ℝ) T →ᵇ V)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    peanoExtension hT f t = f ⟨t, ht⟩ := by
  unfold peanoExtension
  rw [projIcc_of_mem hT ht]

@[fun_prop]
private theorem continuous_peanoExtension
    {T : ℝ} (hT : 0 ≤ T) (f : Icc (0 : ℝ) T →ᵇ V) :
    Continuous (peanoExtension hT f) := by
  unfold peanoExtension
  exact f.continuous.comp continuous_projIcc

private theorem exists_peano_fixedPoint
    (G : V → V) (hG : Continuous G) (Bnd : ℝ)
    (hBnd0 : 0 ≤ Bnd) (hBnd : ∀ y, ‖G y‖ ≤ Bnd)
    (xZero : V) {T : ℝ} (hT : 0 ≤ T) :
    ∃ f : Icc (0 : ℝ) T →ᵇ V,
      ∀ t, f t = xZero + ∫ s in (0 : ℝ)..t.1,
        G (peanoExtension hT f s) := by
  let a : ℕ → Icc (0 : ℝ) T →ᵇ V :=
    fun n => peanoApproxBCF G hG xZero T n
  let A : Set (Icc (0 : ℝ) T →ᵇ V) := Set.range a
  have haLip (n : ℕ) :
      LipschitzWith (⟨Bnd, hBnd0⟩ : ℝ≥0) (a n) := by
    dsimp [a]
    exact lipschitzWith_peanoApproxBCF G hG xZero hBnd0 hBnd n
  have haRange (n : ℕ) (t : Icc (0 : ℝ) T) :
      a n t ∈ closedBall xZero (Bnd * T) := by
    dsimp [a]
    exact peanoApproxBCF_mem_closedBall
      G hG xZero hT hBnd0 hBnd n t
  have hcompact : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli
      (closedBall xZero (Bnd * T)) (isCompact_closedBall xZero (Bnd * T)) A
    · intro f t hf
      rcases hf with ⟨n, rfl⟩
      exact haRange n t
    · refine (LipschitzWith.uniformEquicontinuous
        ((↑) : A → Icc (0 : ℝ) T → V)
        (⟨Bnd, hBnd0⟩ : ℝ≥0) ?_).equicontinuous
      rintro ⟨f, hf⟩
      rcases hf with ⟨n, rfl⟩
      exact haLip n
  have ha (n : ℕ) : a n ∈ closure A :=
    subset_closure ⟨n, rfl⟩
  obtain ⟨f, _hf, phi, hphi, hlim⟩ :=
    hcompact.isSeqCompact ha
  have hlimUniform :
      TendstoUniformly (fun n t => a (phi n) t) f atTop := by
    simpa only [Function.comp_apply] using
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim)
  have hfRange (t : Icc (0 : ℝ) T) :
      f t ∈ closedBall xZero (Bnd * T) :=
    isClosed_closedBall.mem_of_tendsto
      (hlimUniform.tendsto_at t)
      (Eventually.of_forall fun n => haRange (phi n) t)
  have hdenNat :
      Tendsto (fun n => phi n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ _) hphi.tendsto_atTop
  have hden :
      Tendsto (fun n : ℕ => ((phi n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdenNat
  have hmeshZero :
      Tendsto (fun n => peanoMesh T (phi n)) atTop (𝓝 0) := by
    simpa [peanoMesh] using tendsto_const_nhds.div_atTop hden
  have hmeshScaled :
      Tendsto (fun n => Bnd * peanoMesh T (phi n)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hmeshZero
  let delayed : ℕ → ℝ → V := fun n s =>
    peanoExtension hT (a (phi n))
      (peanoDelay (peanoMesh T (phi n)) s)
  let limitPath : ℝ → V := peanoExtension hT f
  have hpath :
      TendstoUniformlyOn delayed limitPath atTop (Icc (0 : ℝ) T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hshift :
        ∀ᶠ n in atTop, Bnd * peanoMesh T (phi n) < ε / 2 :=
      (tendsto_order.1 hmeshScaled).2 _ hhalf
    have hfun :
        ∀ᶠ n in atTop, ∀ t,
          dist (a (phi n) t) (f t) < ε / 2 :=
      (Metric.tendstoUniformly_iff.mp hlimUniform _ hhalf).mono
        fun n hn t => by rw [dist_comm]; exact hn t
    filter_upwards [hshift, hfun] with n hn hfn
    intro s hs
    have hh := peanoMesh_nonneg hT (phi n)
    have hd := peanoDelay_mem hh hs
    have hnear :
        dist (a (phi n) ⟨peanoDelay (peanoMesh T (phi n)) s, hd⟩)
            (a (phi n) ⟨s, hs⟩) ≤
          Bnd * peanoMesh T (phi n) := by
      calc
        dist (a (phi n) ⟨peanoDelay (peanoMesh T (phi n)) s, hd⟩)
            (a (phi n) ⟨s, hs⟩) ≤
          ((⟨Bnd, hBnd0⟩ : ℝ≥0) : ℝ) *
            dist (⟨peanoDelay (peanoMesh T (phi n)) s, hd⟩ :
              Icc (0 : ℝ) T) ⟨s, hs⟩ :=
            (haLip (phi n)).dist_le_mul _ _
        _ = Bnd * dist (peanoDelay (peanoMesh T (phi n)) s) s := by
          simp [Subtype.dist_eq]
        _ ≤ Bnd * peanoMesh T (phi n) :=
          mul_le_mul_of_nonneg_left
            (dist_peanoDelay_self_le hh hs.1) hBnd0
    dsimp [delayed, limitPath]
    rw [peanoExtension_of_mem hT f hs,
      peanoExtension_of_mem hT (a (phi n)) hd, dist_comm]
    calc
      dist (a (phi n) ⟨peanoDelay (peanoMesh T (phi n)) s, hd⟩)
          (f ⟨s, hs⟩) ≤
        dist (a (phi n) ⟨peanoDelay (peanoMesh T (phi n)) s, hd⟩)
            (a (phi n) ⟨s, hs⟩) +
          dist (a (phi n) ⟨s, hs⟩) (f ⟨s, hs⟩) :=
            dist_triangle _ _ _
      _ < ε / 2 + ε / 2 :=
        add_lt_add (hnear.trans_lt hn) (hfn ⟨s, hs⟩)
      _ = ε := add_halves ε
  have hdelayedRange :
      ∀ n s, s ∈ Icc (0 : ℝ) T →
        delayed n s ∈ closedBall xZero (Bnd * T) := by
    intro n s hs
    have hd := peanoDelay_mem (peanoMesh_nonneg hT (phi n)) hs
    dsimp [delayed]
    rw [peanoExtension_of_mem hT (a (phi n)) hd]
    exact haRange (phi n) _
  have hlimitRange :
      ∀ s, s ∈ Icc (0 : ℝ) T →
        limitPath s ∈ closedBall xZero (Bnd * T) := by
    intro s hs
    dsimp [limitPath]
    rw [peanoExtension_of_mem hT f hs]
    exact hfRange _
  have hGunif : UniformContinuousOn G (closedBall xZero (Bnd * T)) :=
    (isCompact_closedBall xZero (Bnd * T)).uniformContinuousOn_of_continuous hG.continuousOn
  have hGpath :
      TendstoUniformlyOn (fun n s => G (delayed n s))
        (fun s => G (limitPath s)) atTop (Icc (0 : ℝ) T) :=
    hGunif.comp_tendstoUniformlyOn_eventually
      (Eventually.of_forall fun n s hs => hdelayedRange n s hs)
      hlimitRange hpath
  refine ⟨f, ?_⟩
  intro t
  have hsub : [[(0 : ℝ), t.1]] ⊆ Icc (0 : ℝ) T := by
    intro s hs
    rw [uIcc_of_le t.2.1] at hs
    exact ⟨hs.1, hs.2.trans t.2.2⟩
  have hcont (n : ℕ) :
      ContinuousOn (fun s => G (delayed n s)) [[(0 : ℝ), t.1]] := by
    dsimp [delayed]
    exact (hG.comp
      ((continuous_peanoExtension hT (a (phi n))).comp
        (continuous_peanoDelay _))).continuousOn
  have heq (n : ℕ) :
      a (phi n) t = xZero + ∫ s in (0 : ℝ)..t.1,
        G (delayed n s) := by
    change peanoApprox G xZero T (phi n) t.1 = _
    rw [peanoApprox_eq_delayed G xZero hT (phi n) t.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.2.1] at hs
    have hsT : s ∈ Icc (0 : ℝ) T :=
      ⟨hs.1, hs.2.trans t.2.2⟩
    have hd := peanoDelay_mem (peanoMesh_nonneg hT (phi n)) hsT
    dsimp [delayed]
    rw [peanoExtension_of_mem hT (a (phi n)) hd]
    rfl
  have hInt :
      Tendsto (fun n => ∫ s in (0 : ℝ)..t.1, G (delayed n s))
        atTop (𝓝 (∫ s in (0 : ℝ)..t.1, G (limitPath s))) :=
    (hGpath.mono hsub).tendsto_intervalIntegral_of_continuousOn
      (Eventually.of_forall hcont)
  have hleft : Tendsto (fun n => a (phi n) t) atTop (𝓝 (f t)) :=
    hlimUniform.tendsto_at t
  have hright :
      Tendsto (fun n => xZero + ∫ s in (0 : ℝ)..t.1,
        G (delayed n s)) atTop
        (𝓝 (xZero + ∫ s in (0 : ℝ)..t.1, G (limitPath s))) :=
    tendsto_const_nhds.add hInt
  have hevent :
      (fun n => a (phi n) t) =ᶠ[atTop]
        (fun n => xZero + ∫ s in (0 : ℝ)..t.1, G (delayed n s)) :=
    Eventually.of_forall heq
  have hright' :
      Tendsto (fun n => a (phi n) t) atTop
        (𝓝 (xZero + ∫ s in (0 : ℝ)..t.1, G (limitPath s))) :=
    Tendsto.congr' hevent.symm hright
  exact tendsto_nhds_unique hleft hright'

/-- Peano existence on a finite interval for a continuous globally bounded
finite-dimensional vector field. -/
theorem exists_peanoBounded_solution
    (G : V → V) (hG : Continuous G) (Bnd : ℝ)
    (hBnd : ∀ y, ‖G y‖ ≤ Bnd) (xZero : V)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ tau : ℝ → V,
      Continuous tau ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        tau t = xZero + ∫ s in (0 : ℝ)..t, G (tau s)) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt tau (G (tau t)) (Icc (0 : ℝ) T) t) := by
  have hBnd0 : 0 ≤ Bnd :=
    (norm_nonneg (G xZero)).trans (hBnd xZero)
  obtain ⟨f, hfixed⟩ :=
    exists_peano_fixedPoint G hG Bnd hBnd0 hBnd xZero hT
  let tau : ℝ → V := peanoExtension hT f
  have htau : Continuous tau := by
    dsimp [tau]
    exact continuous_peanoExtension hT f
  have heq : ∀ t ∈ Icc (0 : ℝ) T,
      tau t = xZero + ∫ s in (0 : ℝ)..t, G (tau s) := by
    intro t ht
    have h := hfixed ⟨t, ht⟩
    show peanoExtension hT f t = _
    rw [peanoExtension_of_mem hT f ht]
    exact h
  refine ⟨tau, htau, heq, ?_⟩
  intro t ht
  letI : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hc : Continuous (fun s => G (tau s)) := hG.comp htau
  have hprim :
      HasDerivWithinAt
        (fun u => xZero + ∫ s in (0 : ℝ)..u, G (tau s))
        (G (tau t)) (Icc (0 : ℝ) T) t := by
    apply HasDerivWithinAt.const_add
    apply intervalIntegral.integral_hasDerivWithinAt_right
      (hc.intervalIntegrable 0 t)
      (hc.continuousOn.stronglyMeasurableAtFilter_nhdsWithin
        measurableSet_Icc t)
      (hc.continuousOn t ht)
  apply hprim.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact heq u hu
  · exact ht

/-!
THEOREM LIST
* `exists_peanoBounded_solution`

CLOSES
* Item 1: continuous bounded Peano existence, integral equation, continuity,
  and `HasDerivWithinAt` on `[0,T]`.

UNFINISHED
* Nothing is intentionally omitted from item 1.
END
-/

end Ripple.Analysis.PeanoBoundedExistence

end
