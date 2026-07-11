/-
Ripple.BoundedUniversality.BGP.Existence
--------------------
P10 layer, restated (post-R3 author defect finding, logged in
notes/bgp-adversarial-rounds.md round-3 addendum):

The v1 P10 (`iterator_solution_exists` in LatchAssembly, unconditional
global existence for every A, M, w) is LIKELY FALSE: `F = S.evalF` is
a polynomial, hence superlinear in general, and the z↔u feedback
(`ż ~ q(F(u) − z)`, `u̇ ~ r(z − u)`) admits a finite-time blowup
scenario outside the tracking regime.  Global existence and tracking
must be proved TOGETHER: clip `F` outside the working volume to a
globally bounded Lipschitz continuation, get a global solution by
Picard–Lindelöf, run the tracking invariant to show the solution never
leaves the region where the clip is inactive, conclude it solves the
TRUE system — and satisfies `MovingBox`.  This is exactly the supplier
shape that `assembled_euclidean_simulation`'s `hsupply` hypothesis
needs (R3#8), so proving `boxed_iterator_exists` below discharges it.

The old unconditional statement in LatchAssembly will be DELETED at
the next merge (it is unused by the assembled chain after R3#8).
-/

import Ripple.BoundedUniversality.BGP.TrackingGeneral
import Ripple.Core.ODEGlobal
import Mathlib

namespace Ripple.BoundedUniversality.BGP

open Real
open Filter

/-- Forward monotonicity: `f(0) ≥ 0` and `f' ≥ 0` on `[0, t]` give
`f(t) ≥ 0` (derivative hypotheses only needed forward). -/
private theorem fwd_nonneg_of_deriv_nonneg
    (f : ℝ → ℝ) (f' : ℝ → ℝ)
    (hderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt f (f' s) s)
    (hpos : ∀ s : ℝ, 0 ≤ s → 0 ≤ f' s)
    (h0 : 0 ≤ f 0) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · intro s hs
      exact (hderiv s hs.1).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact ((hderiv s hs.1.le).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hderiv s hs.1.le).deriv]
      exact hpos s hs.1.le
  have := hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  linarith

/-- **Scalar barrier** (the dissipativity lemma D-4 was missing; the
"coupled time-gated barrier" decouples: the z-drive `Ftil(u)` is
bounded independently of `u` by the clip, and the u-drive is `z`,
sequentially).  For `y' = g(t)(w(t) - y)` with `g ≥ 0` and `|w| ≤ Cb`
on `[0, ∞)`: `|y(0)| ≤ Cb` propagates to `|y(t)| ≤ Cb` for all
`t ≥ 0`.  Integrating-factor monotonicity, the `latch_mem_unitInterval`
pattern with `[−Cb, Cb]` in place of `[0, 1]`. -/
theorem scalar_barrier (y g w : ℝ → ℝ) (Cb : ℝ)
    (hgc : Continuous g)
    (hg0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t)
    (hw : ∀ t : ℝ, 0 ≤ t → |w t| ≤ Cb)
    (hy : ∀ t : ℝ, 0 ≤ t → HasDerivAt y (g t * (w t - y t)) t)
    (h0 : |y 0| ≤ Cb) :
    ∀ t : ℝ, 0 ≤ t → |y t| ≤ Cb := by
  intro t ht
  set Φ : ℝ → ℝ := fun s => ∫ τ in (0:ℝ)..s, g τ with hΦdef
  have hΦderiv : ∀ s : ℝ, HasDerivAt Φ (g s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hgc.intervalIntegrable 0 s)
      (hgc.stronglyMeasurableAtFilter _ _)
      hgc.continuousAt
  set E : ℝ → ℝ := fun s => Real.exp (Φ s) with hEdef
  have hEderiv : ∀ s : ℝ, HasDerivAt E (g s * E s) s := by
    intro s
    have := (hΦderiv s).exp
    convert this using 1
    simp only [hEdef]
    ring
  have hEpos : ∀ s, 0 < E s := fun s => Real.exp_pos _
  have hE0 : E 0 = 1 := by simp [hEdef, hΦdef]
  have habs := abs_le.mp h0
  rw [abs_le]
  constructor
  · -- -Cb ≤ y: (y + Cb)·E nondecreasing from ≥ 0
    have hfderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => (y τ + Cb) * E τ)
        (g s * (w s + Cb) * E s) s := by
      intro s hs
      have h1 := ((hy s hs).add_const Cb).mul (hEderiv s)
      convert h1 using 1
      ring
    have h := fwd_nonneg_of_deriv_nonneg (fun τ => (y τ + Cb) * E τ) _
      hfderiv
      (fun s hs => by
        have hws := abs_le.mp (hw s hs)
        have := (hEpos s).le
        have := hg0 s hs
        have hwc : 0 ≤ w s + Cb := by linarith [hws.1]
        positivity)
      (by simp only [hE0, mul_one]; linarith) t ht
    nlinarith [hEpos t, h]
  · -- y ≤ Cb: (Cb - y)·E nondecreasing from ≥ 0
    have hfderiv : ∀ s : ℝ, 0 ≤ s → HasDerivAt (fun τ => (Cb - y τ) * E τ)
        (g s * (Cb - w s) * E s) s := by
      intro s hs
      have h0' : HasDerivAt (fun τ => Cb - y τ)
          (-(g s * (w s - y s))) s := (hy s hs).const_sub Cb
      have h1 := h0'.mul (hEderiv s)
      convert h1 using 1
      ring
    have h := fwd_nonneg_of_deriv_nonneg (fun τ => (Cb - y τ) * E τ) _
      hfderiv
      (fun s hs => by
        have hws := abs_le.mp (hw s hs)
        have := (hEpos s).le
        have := hg0 s hs
        have hwc : 0 ≤ Cb - w s := by linarith [hws.2]
        positivity)
      (by simp only [hE0, mul_one]; linarith) t ht
    nlinarith [hEpos t, h]

/-- Local half-open variant of `scalar_barrier`, tailored to the invariant
hypothesis in `Ripple.locally_lipschitz_bounded_global_ode_proved_continuous`.
Only the derivative and bounds on `[0,T)` are needed to control a fixed
`t < T`. -/
private theorem scalar_barrier_Ico (y g w : ℝ → ℝ) (Cb T : ℝ)
    (hgc : Continuous g)
    (hg0 : ∀ s : ℝ, s ∈ Set.Ico (0 : ℝ) T → 0 ≤ g s)
    (hw : ∀ s : ℝ, s ∈ Set.Ico (0 : ℝ) T → |w s| ≤ Cb)
    (hy : ∀ s : ℝ, s ∈ Set.Ico (0 : ℝ) T →
      HasDerivAt y (g s * (w s - y s)) s)
    (h0 : |y 0| ≤ Cb) :
    ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) T → |y t| ≤ Cb := by
  intro t ht
  set Φ : ℝ → ℝ := fun s => ∫ τ in (0:ℝ)..s, g τ with hΦdef
  have hΦderiv : ∀ s : ℝ, HasDerivAt Φ (g s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hgc.intervalIntegrable 0 s)
      (hgc.stronglyMeasurableAtFilter _ _)
      hgc.continuousAt
  set E : ℝ → ℝ := fun s => Real.exp (Φ s) with hEdef
  have hEderiv : ∀ s : ℝ, HasDerivAt E (g s * E s) s := by
    intro s
    have := (hΦderiv s).exp
    convert this using 1
    simp only [hEdef]
    ring
  have hEpos : ∀ s, 0 < E s := fun s => Real.exp_pos _
  have hE0 : E 0 = 1 := by simp [hEdef, hΦdef]
  have habs := abs_le.mp h0
  have ht0 : 0 ≤ t := ht.1
  rw [abs_le]
  constructor
  · have hfderiv : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) t →
        HasDerivAt (fun τ => (y τ + Cb) * E τ)
          (g s * (w s + Cb) * E s) s := by
      intro s hs
      have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      have h1 := ((hy s hsI).add_const Cb).mul (hEderiv s)
      convert h1 using 1
      ring
    have hmono : MonotoneOn (fun τ => (y τ + Cb) * E τ) (Set.Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · intro s hs
        exact (hfderiv s hs).continuousAt.continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact ((hfderiv s ⟨hs.1.le, hs.2.le⟩).differentiableAt).differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hfderiv s ⟨hs.1.le, hs.2.le⟩).deriv]
        have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1.le, lt_of_lt_of_le hs.2 ht.2.le⟩
        have hws := abs_le.mp (hw s hsI)
        have hgt := hg0 s hsI
        have hwc : 0 ≤ w s + Cb := by linarith [hws.1]
        positivity
    have h := hmono (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
    have hstart : 0 ≤ (y 0 + Cb) * E 0 := by
      simp only [hE0, mul_one]
      linarith
    nlinarith [hEpos t, h, hstart]
  · have hfderiv : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) t →
        HasDerivAt (fun τ => (Cb - y τ) * E τ)
          (g s * (Cb - w s) * E s) s := by
      intro s hs
      have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      have h0' : HasDerivAt (fun τ => Cb - y τ)
          (-(g s * (w s - y s))) s := (hy s hsI).const_sub Cb
      have h1 := h0'.mul (hEderiv s)
      convert h1 using 1
      ring
    have hmono : MonotoneOn (fun τ => (Cb - y τ) * E τ) (Set.Icc 0 t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      · intro s hs
        exact (hfderiv s hs).continuousAt.continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact ((hfderiv s ⟨hs.1.le, hs.2.le⟩).differentiableAt).differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hfderiv s ⟨hs.1.le, hs.2.le⟩).deriv]
        have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1.le, lt_of_lt_of_le hs.2 ht.2.le⟩
        have hws := abs_le.mp (hw s hsI)
        have hgt := hg0 s hsI
        have hwc : 0 ≤ Cb - w s := by linarith [hws.2]
        positivity
    have h := hmono (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
    have hstart : 0 ≤ (Cb - y 0) * E 0 := by
      simp only [hE0, mul_one]
      linarith
    nlinarith [hEpos t, h, hstart]

private theorem locallyLipschitz_pi_lip_on_closedBall {n : ℕ}
    (f : (Fin n → ℝ) → Fin n → ℝ)
    (hcoord : ∀ k : Fin n, LocallyLipschitz fun x : Fin n → ℝ => f x k) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin n → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  intro R hR
  let s : Set (Fin n → ℝ) := Metric.closedBall 0 R
  have hs : IsCompact s := isCompact_closedBall _ _
  have hloc : ∀ k : Fin n, LocallyLipschitzOn s (fun x : Fin n → ℝ => f x k) :=
    fun k => (hcoord k).locallyLipschitzOn
  have hK : ∀ k : Fin n, ∃ K : NNReal,
      LipschitzOnWith K (fun x : Fin n → ℝ => f x k) s :=
    fun k => LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs (hloc k)
  choose K hKlip using hK
  refine ⟨(∑ k : Fin n, (K k : ℝ)), ?_⟩
  intro x y hx hy
  have hxmem : x ∈ s := by simpa [s, Metric.mem_closedBall, dist_zero_right] using hx
  have hymem : y ∈ s := by simpa [s, Metric.mem_closedBall, dist_zero_right] using hy
  rw [← dist_eq_norm]
  have hnonneg : 0 ≤ (∑ k : Fin n, (K k : ℝ)) * ‖x - y‖ := by
    exact mul_nonneg (Finset.sum_nonneg fun k _ => (K k).2) (norm_nonneg _)
  apply (dist_pi_le_iff hnonneg).2
  intro k
  have hk := (hKlip k).dist_le_mul x hxmem y hymem
  rw [dist_eq_norm] at hk
  calc
    dist (f x k) (f y k) ≤ (K k : ℝ) * ‖x - y‖ := by
      simpa [dist_eq_norm] using hk
    _ ≤ (∑ j : Fin n, (K j : ℝ)) * ‖x - y‖ := by
      have hle : (K k : ℝ) ≤ ∑ j : Fin n, (K j : ℝ) :=
        Finset.single_le_sum (fun j _ => (K j).2) (Finset.mem_univ k)
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

private noncomputable def clamp (C x : ℝ) : ℝ := max (-C) (min C x)

private theorem abs_clamp_le {C x : ℝ} (hC : 0 ≤ C) : |clamp C x| ≤ C := by
  rw [abs_le]
  constructor
  · unfold clamp
    exact le_max_left _ _
  · unfold clamp
    exact max_le (by linarith) (min_le_left C x)

private theorem clamp_eq_self_of_abs_le {C x : ℝ} (hx : |x| ≤ C) :
    clamp C x = x := by
  have h := abs_le.mp hx
  unfold clamp
  rw [min_eq_right h.2, max_eq_right h.1]

private theorem locallyLipschitz_clamp {α : Type*} [PseudoEMetricSpace α]
    {f : α → ℝ} (C : ℝ) (hf : LocallyLipschitz f) :
    LocallyLipschitz fun x => clamp C (f x) := by
  unfold clamp
  exact (hf.const_min C).const_max (-C)

private theorem locallyLipschitz_const_real {α : Type*} [PseudoMetricSpace α]
    (c : ℝ) : LocallyLipschitz fun _ : α => c := by
  intro x
  refine ⟨0, Set.univ, Filter.univ_mem, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro a _ b _
  simp

private theorem locallyLipschitz_mul_real {α : Type*} [PseudoMetricSpace α]
    {f g : α → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => f x * g x := by
  intro x
  rcases hf x with ⟨Kf, sf, hsf, hlf⟩
  rcases hg x with ⟨Kg, sg, hsg, hlg⟩
  have hfbd : {y : α | |f y| ≤ |f x| + 1} ∈ nhds x := by
    have hcont := hf.continuous.continuousAt (x := x)
    filter_upwards [Metric.tendsto_nhds.mp hcont 1 (by norm_num)] with y hy
    rw [Real.dist_eq] at hy
    calc
      |f y| = |(f y - f x) + f x| := by ring_nf
      _ ≤ |f y - f x| + |f x| := abs_add_le _ _
      _ ≤ |f x| + 1 := by linarith [le_of_lt hy]
  have hgbd : {y : α | |g y| ≤ |g x| + 1} ∈ nhds x := by
    have hcont := hg.continuous.continuousAt (x := x)
    filter_upwards [Metric.tendsto_nhds.mp hcont 1 (by norm_num)] with y hy
    rw [Real.dist_eq] at hy
    calc
      |g y| = |(g y - g x) + g x| := by ring_nf
      _ ≤ |g y - g x| + |g x| := abs_add_le _ _
      _ ≤ |g x| + 1 := by linarith [le_of_lt hy]
  let t : Set α := sf ∩ sg ∩ {y | |f y| ≤ |f x| + 1} ∩ {y | |g y| ≤ |g x| + 1}
  let L : ℝ := (|f x| + 1) * (Kg : ℝ) + (|g x| + 1) * (Kf : ℝ)
  have hL0 : 0 ≤ L := by
    unfold L
    positivity
  refine ⟨Real.toNNReal L, t, ?_, ?_⟩
  · exact Filter.inter_mem
      (Filter.inter_mem (Filter.inter_mem hsf hsg) hfbd) hgbd
  · apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have haf : a ∈ sf := ha.1.1.1
    have hag : a ∈ sg := ha.1.1.2
    have hbf : b ∈ sf := hb.1.1.1
    have hbg : b ∈ sg := hb.1.1.2
    have hafbd : |f a| ≤ |f x| + 1 := ha.1.2
    have hgbbd : |g b| ≤ |g x| + 1 := hb.2
    have hgd : |g a - g b| ≤ (Kg : ℝ) * dist a b := by
      simpa [Real.dist_eq] using hlg.dist_le_mul a hag b hbg
    have hfd : |f a - f b| ≤ (Kf : ℝ) * dist a b := by
      simpa [Real.dist_eq] using hlf.dist_le_mul a haf b hbf
    rw [Real.dist_eq]
    have hmain :
        |f a * g a - f b * g b| ≤
          ((|f x| + 1) * (Kg : ℝ) + (|g x| + 1) * (Kf : ℝ)) * dist a b := by
      calc
        |f a * g a - f b * g b|
            = |f a * (g a - g b) + g b * (f a - f b)| := by ring_nf
        _ ≤ |f a * (g a - g b)| + |g b * (f a - f b)| := abs_add_le _ _
        _ = |f a| * |g a - g b| + |g b| * |f a - f b| := by
          rw [abs_mul, abs_mul]
        _ ≤ (|f x| + 1) * ((Kg : ℝ) * dist a b) +
              (|g x| + 1) * ((Kf : ℝ) * dist a b) := by
          exact add_le_add
            (mul_le_mul hafbd hgd (abs_nonneg _) (by positivity))
            (mul_le_mul hgbbd hfd (abs_nonneg _) (by positivity))
        _ = ((|f x| + 1) * (Kg : ℝ) + (|g x| + 1) * (Kf : ℝ)) * dist a b := by
          ring
    simpa [L, Real.coe_toNNReal _ hL0] using hmain

private theorem locallyLipschitz_const_mul_real {α : Type*} [PseudoMetricSpace α]
    (c : ℝ) {f : α → ℝ} (hf : LocallyLipschitz f) :
    LocallyLipschitz fun x => c * f x :=
  locallyLipschitz_mul_real (locallyLipschitz_const_real c) hf

private theorem mvPolynomial_eval₂_contDiff
    {K : Type*} [Field K] [Algebra K ℝ]
    {d : ℕ} (p : MvPolynomial (Fin d) K) :
    ContDiff ℝ ⊤ (fun x : Fin d → ℝ => p.eval₂ (algebraMap K ℝ) x) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂_C]
      exact contDiff_const
  | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add]
      exact hp.add hq
  | mul_X p i hp =>
      have h_eval : ∀ x : Fin d → ℝ,
          (p * MvPolynomial.X i).eval₂ (algebraMap K ℝ) x
            = p.eval₂ (algebraMap K ℝ) x * x i := by
        intro x
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      simp only [h_eval]
      exact hp.mul (contDiff_apply ℝ ℝ i)

private noncomputable def idxS (d : ℕ) : Fin (2 + (d + d)) :=
  Fin.castAdd (d + d) (0 : Fin 2)

private noncomputable def idxC (d : ℕ) : Fin (2 + (d + d)) :=
  Fin.castAdd (d + d) (1 : Fin 2)

private noncomputable def idxZ {d : ℕ} (i : Fin d) : Fin (2 + (d + d)) :=
  Fin.natAdd 2 (Fin.castAdd d i)

private noncomputable def idxU {d : ℕ} (i : Fin d) : Fin (2 + (d + d)) :=
  Fin.natAdd 2 (Fin.natAdd d i)

private noncomputable def zPart {d : ℕ} (y : Fin (2 + (d + d)) → ℝ) : Fin d → ℝ :=
  fun i => y (idxZ i)

private noncomputable def uPart {d : ℕ} (y : Fin (2 + (d + d)) → ℝ) : Fin d → ℝ :=
  fun i => y (idxU i)

private noncomputable def clippedF {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C : ℝ) :
    (Fin d → ℝ) → Fin d → ℝ :=
  fun x i => clamp C (S.evalF x i)

private noncomputable def clippedField {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C A : ℝ) (M : ℕ) :
    (Fin (2 + (d + d)) → ℝ) → Fin (2 + (d + d)) → ℝ :=
  fun y =>
    Fin.append
      (fun k : Fin 2 =>
        if k = 0 then y (idxC d) else -(y (idxS d)))
      (Fin.append
        (fun i : Fin d =>
          A * ((1 + y (idxS d)) / 2) ^ M *
            (clippedF S C (uPart y) i - zPart y i))
        (fun i : Fin d =>
          A * ((1 - y (idxS d)) / 2) ^ M *
            (zPart y i - uPart y i)))

private theorem clippedField_s {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C A : ℝ) (M : ℕ)
    (y : Fin (2 + (d + d)) → ℝ) :
    clippedField S C A M y (idxS d) = y (idxC d) := by
  simp [clippedField, idxS, idxC]

private theorem clippedField_c {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C A : ℝ) (M : ℕ)
    (y : Fin (2 + (d + d)) → ℝ) :
    clippedField S C A M y (idxC d) = -y (idxS d) := by
  simp [clippedField, idxS, idxC]

private theorem clippedField_z {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C A : ℝ) (M : ℕ)
    (y : Fin (2 + (d + d)) → ℝ) (i : Fin d) :
    clippedField S C A M y (idxZ i) =
      A * ((1 + y (idxS d)) / 2) ^ M *
        (clippedF S C (uPart y) i - zPart y i) := by
  simp [clippedField, idxZ]

private theorem clippedField_u {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C A : ℝ) (M : ℕ)
    (y : Fin (2 + (d + d)) → ℝ) (i : Fin d) :
    clippedField S C A M y (idxU i) =
      A * ((1 - y (idxS d)) / 2) ^ M *
        (zPart y i - uPart y i) := by
  rw [clippedField, idxU, Fin.append_right, Fin.append_right]

private theorem zPart_coord_locallyLipschitz {d : ℕ} (i : Fin d) :
    LocallyLipschitz fun y : Fin (2 + (d + d)) → ℝ => zPart y i := by
  change LocallyLipschitz fun y : Fin (2 + (d + d)) → ℝ => y (idxZ i)
  exact (contDiff_apply ℝ ℝ (idxZ i) :
    ContDiff ℝ 1 (fun y : Fin (2 + (d + d)) → ℝ => y (idxZ i))).locallyLipschitz

private theorem uPart_coord_locallyLipschitz {d : ℕ} (i : Fin d) :
    LocallyLipschitz fun y : Fin (2 + (d + d)) → ℝ => uPart y i := by
  change LocallyLipschitz fun y : Fin (2 + (d + d)) → ℝ => y (idxU i)
  exact (contDiff_apply ℝ ℝ (idxU i) :
    ContDiff ℝ 1 (fun y : Fin (2 + (d + d)) → ℝ => y (idxU i))).locallyLipschitz

private theorem uPart_contDiff {d : ℕ} :
    ContDiff ℝ 1 (fun y : Fin (2 + (d + d)) → ℝ => uPart y) := by
  apply contDiff_pi'
  intro i
  change ContDiff ℝ 1 (fun y : Fin (2 + (d + d)) → ℝ => y (idxU i))
  exact contDiff_apply ℝ ℝ (idxU i)

private theorem qGate_locallyLipschitz {d : ℕ} (M : ℕ) :
    LocallyLipschitz
      (fun y : Fin (2 + (d + d)) → ℝ => ((1 + y (idxS d)) / 2) ^ M) := by
  have hcd : ContDiff ℝ 1
      (fun y : Fin (2 + (d + d)) → ℝ => ((1 + y (idxS d)) / 2) ^ M) := by
    fun_prop
  exact hcd.locallyLipschitz

private theorem rGate_locallyLipschitz {d : ℕ} (M : ℕ) :
    LocallyLipschitz
      (fun y : Fin (2 + (d + d)) → ℝ => ((1 - y (idxS d)) / 2) ^ M) := by
  have hcd : ContDiff ℝ 1
      (fun y : Fin (2 + (d + d)) → ℝ => ((1 - y (idxS d)) / 2) ^ M) := by
    fun_prop
  exact hcd.locallyLipschitz

private theorem evalF_uPart_coord_locallyLipschitz
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (i : Fin d) :
    LocallyLipschitz
      (fun y : Fin (2 + (d + d)) → ℝ => S.evalF (uPart y) i) := by
  have hp : ContDiff ℝ 1 (fun x : Fin d → ℝ => S.evalF x i) := by
    unfold RobustRealExtension.evalF
    exact (mvPolynomial_eval₂_contDiff (K := ℚ) (S.F i)).of_le (by simp)
  have hcomp := hp.comp uPart_contDiff
  exact hcomp.locallyLipschitz

private theorem clippedF_uPart_coord_locallyLipschitz
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C : ℝ) (i : Fin d) :
    LocallyLipschitz
      (fun y : Fin (2 + (d + d)) → ℝ => clippedF S C (uPart y) i) := by
  simpa [clippedF] using
    locallyLipschitz_clamp C (evalF_uPart_coord_locallyLipschitz S i)

private theorem clippedField_coord_locallyLipschitz
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C A : ℝ) (M : ℕ) :
    ∀ k : Fin (2 + (d + d)),
      LocallyLipschitz fun y : Fin (2 + (d + d)) → ℝ =>
        clippedField S C A M y k := by
  intro k
  cases h : (finSumFinEquiv.symm k : Fin 2 ⊕ Fin (d + d)) with
  | inl kc =>
      have hk : k = finSumFinEquiv (Sum.inl kc) := by
        rw [← h]
        simp
      subst k
      fin_cases kc
      · simpa [clippedField, idxC] using
          (contDiff_apply ℝ ℝ (idxC d) :
            ContDiff ℝ 1 (fun y : Fin (2 + (d + d)) → ℝ => y (idxC d))).locallyLipschitz
      · have hs : LocallyLipschitz
            (fun y : Fin (2 + (d + d)) → ℝ => y (idxS d)) :=
          (contDiff_apply ℝ ℝ (idxS d) :
            ContDiff ℝ 1 (fun y : Fin (2 + (d + d)) → ℝ => y (idxS d))).locallyLipschitz
        have hneg : LocallyLipschitz
            (fun y : Fin (2 + (d + d)) → ℝ => -y (idxS d)) := by
          have hcd : ContDiff ℝ 1
              (fun y : Fin (2 + (d + d)) → ℝ => -y (idxS d)) := by
            fun_prop
          exact hcd.locallyLipschitz
        simpa [clippedField, idxS] using hneg
  | inr kr =>
      have hk : k = finSumFinEquiv (Sum.inr kr) := by
        rw [← h]
        simp
      subst k
      cases hr : (finSumFinEquiv.symm kr : Fin d ⊕ Fin d) with
      | inl i =>
          have hkr : kr = finSumFinEquiv (Sum.inl i) := by
            rw [← hr]
            simp
          subst kr
          have hAconst : LocallyLipschitz
              (fun _ : Fin (2 + (d + d)) → ℝ => A) :=
            (contDiff_const : ContDiff ℝ 1
              (fun _ : Fin (2 + (d + d)) → ℝ => A)).locallyLipschitz
          have hdiff :=
            (clippedF_uPart_coord_locallyLipschitz S C i).sub
              (zPart_coord_locallyLipschitz i)
          have hprod :=
            locallyLipschitz_const_mul_real A
              (locallyLipschitz_mul_real (qGate_locallyLipschitz (d := d) M) hdiff)
          convert hprod using 1
          ext y
          simp [clippedField, clippedF, zPart, idxZ, Fin.append_right]
          ring
      | inr i =>
          have hkr : kr = finSumFinEquiv (Sum.inr i) := by
            rw [← hr]
            simp
          subst kr
          have hAconst : LocallyLipschitz
              (fun _ : Fin (2 + (d + d)) → ℝ => A) :=
            (contDiff_const : ContDiff ℝ 1
              (fun _ : Fin (2 + (d + d)) → ℝ => A)).locallyLipschitz
          have hdiff :=
            (zPart_coord_locallyLipschitz i).sub
              (uPart_coord_locallyLipschitz i)
          have hprod :=
            locallyLipschitz_const_mul_real A
              (locallyLipschitz_mul_real (rGate_locallyLipschitz (d := d) M) hdiff)
          convert hprod using 1
          ext y
          dsimp [clippedField, zPart, uPart]
          rw [Fin.append_right]
          rw [idxU]
          rw [Fin.append_right]
          rw [idxU]
          ring_nf

private theorem clippedField_lip
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (C A : ℝ) (M : ℕ) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin (2 + (d + d)) → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖clippedField S C A M x - clippedField S C A M y‖ ≤ L * ‖x - y‖ :=
  locallyLipschitz_pi_lip_on_closedBall (clippedField S C A M)
    (clippedField_coord_locallyLipschitz S C A M)

private noncomputable def clippedInit {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (x₀ : Fin d → ℝ) : Fin (2 + (d + d)) → ℝ :=
  Fin.append (fun k : Fin 2 => if k = 0 then 0 else 1)
    (Fin.append x₀ x₀)

private theorem clippedInit_s {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (x₀ : Fin d → ℝ) :
    clippedInit (Mch := Mch) (E := E) x₀ (idxS d) = 0 := by
  simp [clippedInit, idxS]

private theorem clippedInit_c {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (x₀ : Fin d → ℝ) :
    clippedInit (Mch := Mch) (E := E) x₀ (idxC d) = 1 := by
  simp [clippedInit, idxC]

private theorem clippedInit_z {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (x₀ : Fin d → ℝ) (i : Fin d) :
    zPart (clippedInit (Mch := Mch) (E := E) x₀) i = x₀ i := by
  simp [zPart, clippedInit, idxZ]

private theorem clippedInit_u {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (x₀ : Fin d → ℝ) (i : Fin d) :
    uPart (clippedInit (Mch := Mch) (E := E) x₀) i = x₀ i := by
  rw [uPart, clippedInit, idxU, Fin.append_right, Fin.append_right]

private theorem clipped_local_bounds
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E)
    (B_orb C A : ℝ) (M : ℕ) (w : ℕ)
    (hBorb : 0 < B_orb)
    (hA : 0 < A)
    (horb0 : ∀ i : Fin d, |orbitPoint Mch E w 0 i| ≤ B_orb)
    (hC : B_orb + (S.ηstep : ℝ) + 1 ≤ C)
    (T : ℝ) (hT : 0 < T)
    (y : ℝ → Fin (2 + (d + d)) → ℝ)
    (hy0 : y 0 = clippedInit (Mch := Mch) (E := E) (orbitPoint Mch E w 0))
    (hy : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt y (clippedField S C A M (y t)) t) :
    (∀ t ∈ Set.Ico (0 : ℝ) T, |y t (idxS d)| ≤ 1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, |y t (idxC d)| ≤ 1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d, |zPart (y t) i| ≤ C) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d, |uPart (y t) i| ≤ C) := by
  have hCpos : 0 < C := by
    have hη : 0 ≤ (S.ηstep : ℝ) := by exact_mod_cast S.ηstep_pos.le
    nlinarith [hC, hη, hBorb]
  have hCnonneg : 0 ≤ C := hCpos.le
  have henergy :
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        y t (idxS d) ^ 2 + y t (idxC d) ^ 2 = 1 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hderivE : ∀ s ∈ Set.Icc (0 : ℝ) t,
        HasDerivAt
          (fun τ => y τ (idxS d) ^ 2 + y τ (idxC d) ^ 2)
          0 s := by
      intro s hs
      have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      have hsode := hy s hsI
      have hds : HasDerivAt (fun τ => y τ (idxS d))
          (clippedField S C A M (y s) (idxS d)) s :=
        (hasDerivAt_pi.mp hsode) (idxS d)
      have hdc : HasDerivAt (fun τ => y τ (idxC d))
          (clippedField S C A M (y s) (idxC d)) s :=
        (hasDerivAt_pi.mp hsode) (idxC d)
      have hsq := (hds.pow 2).add (hdc.pow 2)
      convert hsq using 1
      rw [clippedField_s, clippedField_c]
      ring
    have hhold := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := 0)
      (fun s hs => (hderivE s hs).hasDerivWithinAt)
      (fun s hs => by norm_num)
      (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0)
    have hzero :
        ‖(y t (idxS d) ^ 2 + y t (idxC d) ^ 2) -
          (y 0 (idxS d) ^ 2 + y 0 (idxC d) ^ 2)‖ = 0 := by
      have : ‖(y t (idxS d) ^ 2 + y t (idxC d) ^ 2) -
          (y 0 (idxS d) ^ 2 + y 0 (idxC d) ^ 2)‖ ≤ 0 := by
        simpa using hhold
      exact le_antisymm this (norm_nonneg _)
    have hinit :
        y 0 (idxS d) ^ 2 + y 0 (idxC d) ^ 2 = 1 := by
      rw [hy0, clippedInit_s, clippedInit_c]
      norm_num
    have habs : |(y t (idxS d) ^ 2 + y t (idxC d) ^ 2) -
          (y 0 (idxS d) ^ 2 + y 0 (idxC d) ^ 2)| = 0 := by
      simpa [Real.norm_eq_abs] using hzero
    have heq :
        y t (idxS d) ^ 2 + y t (idxC d) ^ 2 =
          y 0 (idxS d) ^ 2 + y 0 (idxC d) ^ 2 := by
      exact sub_eq_zero.mp (abs_eq_zero.mp habs)
    linarith
  have hs_bound : ∀ t ∈ Set.Ico (0 : ℝ) T, |y t (idxS d)| ≤ 1 := by
    intro t ht
    have hE := henergy t ht
    have hs_sq_nonneg : 0 ≤ y t (idxS d) ^ 2 := sq_nonneg _
    have hc_sq_nonneg : 0 ≤ y t (idxC d) ^ 2 := sq_nonneg _
    have hs_sq_le : y t (idxS d) ^ 2 ≤ 1 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y t (idxS d) + 1),
      sq_nonneg (y t (idxS d) - 1), hs_sq_le]
  have hc_bound : ∀ t ∈ Set.Ico (0 : ℝ) T, |y t (idxC d)| ≤ 1 := by
    intro t ht
    have hE := henergy t ht
    have hc_sq_le : y t (idxC d) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y t (idxS d))]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (y t (idxC d) + 1),
      sq_nonneg (y t (idxC d) - 1), hc_sq_le]
  have hgate_q_nonneg : ∀ t ∈ Set.Ico (0 : ℝ) T,
      0 ≤ A * ((1 + y t (idxS d)) / 2) ^ M := by
    intro t ht
    have hs := abs_le.mp (hs_bound t ht)
    have hbase : 0 ≤ (1 + y t (idxS d)) / 2 := by linarith
    positivity
  have hgate_r_nonneg : ∀ t ∈ Set.Ico (0 : ℝ) T,
      0 ≤ A * ((1 - y t (idxS d)) / 2) ^ M := by
    intro t ht
    have hs := abs_le.mp (hs_bound t ht)
    have hbase : 0 ≤ (1 - y t (idxS d)) / 2 := by linarith
    positivity
  have hy_cont : ContinuousOn y (Set.Ico (0 : ℝ) T) := by
    intro t ht
    exact (hy t ht).continuousAt.continuousWithinAt
  have hz_bounds : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d,
      |zPart (y t) i| ≤ C := by
    intro t ht i
    let T' : ℝ := (t + T) / 2
    have hT'pos : 0 < T' := by dsimp [T']; nlinarith [ht.1, hT]
    have htT' : t < T' := by dsimp [T']; nlinarith [ht.2]
    have hT'T : T' < T := by dsimp [T']; nlinarith [ht.2]
    let sExt : ℝ → ℝ :=
      Set.IccExtend (show (0 : ℝ) ≤ T' by linarith)
        (fun x : Set.Icc (0 : ℝ) T' => y x.1 (idxS d))
    let g : ℝ → ℝ := fun s => A * ((1 + sExt s) / 2) ^ M
    let ww : ℝ → ℝ := fun s => clippedF S C (uPart (y s)) i
    have hsExt_eq : ∀ s ∈ Set.Icc (0 : ℝ) T', sExt s = y s (idxS d) := by
      intro s hs
      simpa [sExt] using
        (Set.IccExtend_of_mem (show (0 : ℝ) ≤ T' by linarith)
          (fun x : Set.Icc (0 : ℝ) T' => y x.1 (idxS d)) hs)
    have hgc : Continuous g := by
      have hcont_restrict :
          Continuous (fun x : Set.Icc (0 : ℝ) T' => y x.1 (idxS d)) := by
        change Continuous ((Set.Icc (0 : ℝ) T').restrict
          (fun s => y s (idxS d)))
        apply ContinuousOn.restrict
        intro s hs
        have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 hT'T⟩
        exact ((hasDerivAt_pi.mp (hy s hsI)) (idxS d)).continuousAt.continuousWithinAt
      have hscont : Continuous sExt :=
        hcont_restrict.Icc_extend'
      unfold g
      fun_prop
    have hw : ∀ s ∈ Set.Ico (0 : ℝ) T', |ww s| ≤ C := by
      intro s hs
      exact abs_clamp_le hCnonneg
    have hder : ∀ s ∈ Set.Ico (0 : ℝ) T',
        HasDerivAt (fun τ => zPart (y τ) i)
          (g s * (ww s - zPart (y s) i)) s := by
      intro s hs
      have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 hT'T⟩
      have hsode := hy s hsI
      have hdz : HasDerivAt (fun τ => y τ (idxZ i))
          (clippedField S C A M (y s) (idxZ i)) s :=
        (hasDerivAt_pi.mp hsode) (idxZ i)
      have hse : sExt s = y s (idxS d) := hsExt_eq s ⟨hs.1, hs.2.le⟩
      simpa [g, ww, zPart, clippedField_z, hse] using hdz
    have h0 : |(fun τ => zPart (y τ) i) 0| ≤ C := by
      change |zPart (y 0) i| ≤ C
      rw [hy0, clippedInit_z]
      have hη : 0 ≤ (S.ηstep : ℝ) := by exact_mod_cast S.ηstep_pos.le
      have := horb0 i
      nlinarith [hC, hη]
    have hg0 : ∀ s ∈ Set.Ico (0 : ℝ) T', 0 ≤ g s := by
      intro s hs
      have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 hT'T⟩
      have hse : sExt s = y s (idxS d) := hsExt_eq s ⟨hs.1, hs.2.le⟩
      simpa [g, hse] using hgate_q_nonneg s hsI
    exact scalar_barrier_Ico (fun τ => zPart (y τ) i) g ww C T' hgc
      hg0 hw hder h0 t ⟨ht.1, htT'⟩
  have hu_bounds : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d,
      |uPart (y t) i| ≤ C := by
    intro t ht i
    let T' : ℝ := (t + T) / 2
    have hT'pos : 0 < T' := by dsimp [T']; nlinarith [ht.1, hT]
    have htT' : t < T' := by dsimp [T']; nlinarith [ht.2]
    have hT'T : T' < T := by dsimp [T']; nlinarith [ht.2]
    let sExt : ℝ → ℝ :=
      Set.IccExtend (show (0 : ℝ) ≤ T' by linarith)
        (fun x : Set.Icc (0 : ℝ) T' => y x.1 (idxS d))
    let g : ℝ → ℝ := fun s => A * ((1 - sExt s) / 2) ^ M
    let ww : ℝ → ℝ := fun s => zPart (y s) i
    have hsExt_eq : ∀ s ∈ Set.Icc (0 : ℝ) T', sExt s = y s (idxS d) := by
      intro s hs
      simpa [sExt] using
        (Set.IccExtend_of_mem (show (0 : ℝ) ≤ T' by linarith)
          (fun x : Set.Icc (0 : ℝ) T' => y x.1 (idxS d)) hs)
    have hgc : Continuous g := by
      have hcont_restrict :
          Continuous (fun x : Set.Icc (0 : ℝ) T' => y x.1 (idxS d)) := by
        change Continuous ((Set.Icc (0 : ℝ) T').restrict
          (fun s => y s (idxS d)))
        apply ContinuousOn.restrict
        intro s hs
        have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_of_le_of_lt hs.2 hT'T⟩
        exact ((hasDerivAt_pi.mp (hy s hsI)) (idxS d)).continuousAt.continuousWithinAt
      have hscont : Continuous sExt :=
        hcont_restrict.Icc_extend'
      unfold g
      fun_prop
    have hw : ∀ s ∈ Set.Ico (0 : ℝ) T', |ww s| ≤ C := by
      intro s hs
      exact hz_bounds s ⟨hs.1, lt_trans hs.2 hT'T⟩ i
    have hder : ∀ s ∈ Set.Ico (0 : ℝ) T',
        HasDerivAt (fun τ => uPart (y τ) i)
          (g s * (ww s - uPart (y s) i)) s := by
      intro s hs
      have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 hT'T⟩
      have hsode := hy s hsI
      have hdu : HasDerivAt (fun τ => y τ (idxU i))
          (clippedField S C A M (y s) (idxU i)) s :=
        (hasDerivAt_pi.mp hsode) (idxU i)
      have hse : sExt s = y s (idxS d) := hsExt_eq s ⟨hs.1, hs.2.le⟩
      simpa [g, ww, uPart, clippedField_u, hse] using hdu
    have h0 : |(fun τ => uPart (y τ) i) 0| ≤ C := by
      change |uPart (y 0) i| ≤ C
      rw [hy0, clippedInit_u]
      have hη : 0 ≤ (S.ηstep : ℝ) := by exact_mod_cast S.ηstep_pos.le
      have := horb0 i
      nlinarith [hC, hη]
    have hg0 : ∀ s ∈ Set.Ico (0 : ℝ) T', 0 ≤ g s := by
      intro s hs
      have hsI : s ∈ Set.Ico (0 : ℝ) T := ⟨hs.1, lt_trans hs.2 hT'T⟩
      have hse : sExt s = y s (idxS d) := hsExt_eq s ⟨hs.1, hs.2.le⟩
      simpa [g, hse] using hgate_r_nonneg s hsI
    exact scalar_barrier_Ico (fun τ => uPart (y τ) i) g ww C T' hgc
      hg0 hw hder h0 t ⟨ht.1, htT'⟩
  exact ⟨hs_bound, hc_bound, hz_bounds, hu_bounds⟩

private theorem clipped_global_solution
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E)
    (B_orb C A : ℝ) (M : ℕ) (w : ℕ)
    (hBorb : 0 < B_orb) (hA : 0 < A)
    (horb0 : ∀ i : Fin d, |orbitPoint Mch E w 0 i| ≤ B_orb)
    (hC : B_orb + (S.ηstep : ℝ) + 1 ≤ C) :
    ∃ y : ℝ → Fin (2 + (d + d)) → ℝ,
      y 0 = clippedInit (Mch := Mch) (E := E) (orbitPoint Mch E w 0) ∧
      (∀ t : ℝ, 0 ≤ t → HasDerivAt y (clippedField S C A M (y t)) t) ∧
      (∀ t : ℝ, 0 ≤ t → |y t (idxS d)| ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → |y t (idxC d)| ≤ 1) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, |zPart (y t) i| ≤ C) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, |uPart (y t) i| ≤ C) := by
  have hηnonneg : 0 ≤ (S.ηstep : ℝ) := by exact_mod_cast S.ηstep_pos.le
  have hCpos : 0 < C := by nlinarith [hC, hηnonneg, hBorb]
  have hCp1pos : 0 < C + 1 := by nlinarith
  obtain ⟨y, hy0, hyode⟩ :=
    Ripple.locally_lipschitz_bounded_global_ode_proved
      (clippedField S C A M)
      (clippedInit (Mch := Mch) (E := E) (orbitPoint Mch E w 0))
      (clippedField_lip S C A M)
      (C + 1) hCp1pos
      (by
        intro T hT y hy0 hy t ht
        obtain ⟨hsb, hcb, hzb, hub⟩ :=
          clipped_local_bounds S B_orb C A M w hBorb hA horb0 hC T hT y hy0 hy
        rw [pi_norm_le_iff_of_nonneg hCp1pos.le]
        intro k
        cases h : (finSumFinEquiv.symm k : Fin 2 ⊕ Fin (d + d)) with
        | inl kc =>
            have hk : k = finSumFinEquiv (Sum.inl kc) := by
              rw [← h]
              simp
            subst k
            fin_cases kc
            · have := hsb t ht
              simpa [idxS, Real.norm_eq_abs] using le_trans this (by linarith : (1 : ℝ) ≤ C + 1)
            · have := hcb t ht
              simpa [idxC, Real.norm_eq_abs] using le_trans this (by linarith : (1 : ℝ) ≤ C + 1)
        | inr kr =>
            have hk : k = finSumFinEquiv (Sum.inr kr) := by
              rw [← h]
              simp
            subst k
            cases hr : (finSumFinEquiv.symm kr : Fin d ⊕ Fin d) with
            | inl i =>
                have hkr : kr = finSumFinEquiv (Sum.inl i) := by
                  rw [← hr]
                  simp
                subst kr
                have := hzb t ht i
                have hle : C ≤ C + 1 := by linarith
                simpa [zPart, idxZ, Real.norm_eq_abs] using le_trans this hle
            | inr i =>
                have hkr : kr = finSumFinEquiv (Sum.inr i) := by
                  rw [← hr]
                  simp
                subst kr
                have := hub t ht i
                have hle : C ≤ C + 1 := by linarith
                simpa [uPart, idxU, Real.norm_eq_abs] using le_trans this hle)
  have hbounds_at : ∀ t : ℝ, 0 ≤ t →
      |y t (idxS d)| ≤ 1 ∧ |y t (idxC d)| ≤ 1 ∧
      (∀ i : Fin d, |zPart (y t) i| ≤ C) ∧
      (∀ i : Fin d, |uPart (y t) i| ≤ C) := by
    intro t ht
    obtain ⟨hsb, hcb, hzb, hub⟩ :=
      clipped_local_bounds S B_orb C A M w hBorb hA horb0 hC
        (t + 1) (by linarith) y hy0
        (fun s hs => hyode s hs.1)
    exact ⟨hsb t ⟨ht, by linarith⟩, hcb t ⟨ht, by linarith⟩,
      hzb t ⟨ht, by linarith⟩, hub t ⟨ht, by linarith⟩⟩
  refine ⟨y, hy0, hyode, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hbounds_at t ht).1
  · intro t ht
    exact (hbounds_at t ht).2.1
  · intro t ht
    exact (hbounds_at t ht).2.2.1
  · intro t ht
    exact (hbounds_at t ht).2.2.2

private noncomputable def forwardExtend (h : ℝ → ℝ) (v0 : ℝ) : ℝ → ℝ :=
  fun t => if 0 ≤ t then h t else h 0 + t * v0

private theorem forwardExtend_eq_of_nonneg (h : ℝ → ℝ) (v0 : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    forwardExtend h v0 t = h t := by
  simp [forwardExtend, ht]

private theorem forwardExtend_continuous (h : ℝ → ℝ) (v v0 : ℝ → ℝ)
    (hder : ∀ t : ℝ, 0 ≤ t → HasDerivAt h (v t) t) :
    Continuous (forwardExtend h (v0 0)) := by
  have hleft : ContinuousOn (forwardExtend h (v0 0)) (Set.Iic (0 : ℝ)) := by
    refine (by fun_prop : Continuous fun t : ℝ => h 0 + t * v0 0).continuousOn.congr ?_
    intro t ht
    rcases lt_or_eq_of_le (show t ≤ 0 from ht) with htneg | rfl
    · simp [forwardExtend, not_le_of_gt htneg]
    · simp [forwardExtend]
  have hright : ContinuousOn (forwardExtend h (v0 0)) (Set.Ici (0 : ℝ)) := by
    have hh : ContinuousOn h (Set.Ici (0 : ℝ)) := by
      intro t ht
      exact (hder t ht).continuousAt.continuousWithinAt
    refine hh.congr ?_
    intro t ht
    have ht0 : 0 ≤ t := ht
    simp [forwardExtend, ht0]
  have huniv : Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ) = Set.univ := by
    ext t
    simp
  have hcontOn : ContinuousOn (forwardExtend h (v0 0)) Set.univ := by
    simpa [huniv] using
      hleft.union_of_isClosed hright isClosed_Iic isClosed_Ici
  simpa using hcontOn

private theorem forwardExtend_hasDerivAt_zero (h : ℝ → ℝ) (v0 : ℝ)
    (hder0 : HasDerivAt h v0 0) :
    HasDerivAt (forwardExtend h v0) v0 0 := by
  have haff : HasDerivAt (fun t : ℝ => h 0 + t * v0) v0 0 := by
    exact (hasDerivAt_mul_const v0).const_add (h 0)
  have hleft : HasDerivWithinAt (forwardExtend h v0) v0 (Set.Iic (0 : ℝ)) 0 := by
    refine haff.hasDerivWithinAt.congr ?_ ?_
    intro t ht
    rcases lt_or_eq_of_le (show t ≤ 0 from ht) with htneg | rfl
    · simp [forwardExtend, not_le_of_gt htneg]
    · simp [forwardExtend]
    simp [forwardExtend]
  have hright : HasDerivWithinAt (forwardExtend h v0) v0 (Set.Ici (0 : ℝ)) 0 := by
    refine hder0.hasDerivWithinAt.congr ?_ ?_
    intro t ht
    have ht0 : 0 ≤ t := ht
    simp [forwardExtend, ht0]
    change (if (0 : ℝ) ≤ 0 then h 0 else h 0 + 0 * v0) = h 0
    simp
  have huniv : Set.Iic (0 : ℝ) ∪ Set.Ici (0 : ℝ) = Set.univ := by
    ext t
    simp
  have hboth := hleft.union hright
  simpa [huniv] using hboth

private theorem forwardExtend_hasDerivAt_of_pos (h : ℝ → ℝ) (v0 v t : ℝ)
    (ht : 0 < t) (hder : HasDerivAt h v t) :
    HasDerivAt (forwardExtend h v0) v t := by
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hs0 : 0 ≤ s := (show 0 < s from hs).le
  simp [forwardExtend, hs0]

private theorem forwardExtend_hasDerivAt_nonneg (h : ℝ → ℝ) (v : ℝ → ℝ)
    (hder : ∀ t : ℝ, 0 ≤ t → HasDerivAt h (v t) t) :
    ∀ t : ℝ, 0 ≤ t → HasDerivAt (forwardExtend h (v 0)) (v t) t := by
  intro t ht
  rcases lt_or_eq_of_le ht with htpos | rfl
  · exact forwardExtend_hasDerivAt_of_pos h (v 0) (v t) t htpos (hder t ht)
  · exact forwardExtend_hasDerivAt_zero h (v 0) (hder 0 le_rfl)

private theorem clipped_clock_eq
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E)
    (C A : ℝ) (M : ℕ) (x₀ : Fin d → ℝ)
    (y : ℝ → Fin (2 + (d + d)) → ℝ)
    (hy0 : y 0 = clippedInit (Mch := Mch) (E := E) x₀)
    (hyode : ∀ t : ℝ, 0 ≤ t → HasDerivAt y (clippedField S C A M (y t)) t)
    (hsb : ∀ t : ℝ, 0 ≤ t → |y t (idxS d)| ≤ 1)
    (hcb : ∀ t : ℝ, 0 ≤ t → |y t (idxC d)| ≤ 1) :
    ∀ t : ℝ, 0 ≤ t → y t (idxS d) = Real.sin t ∧
      y t (idxC d) = Real.cos t := by
  classical
  let f : (Fin 2 → ℝ) → Fin 2 → ℝ :=
    fun x k => if k = 0 then x 1 else -x 0
  let α : ℝ → Fin 2 → ℝ :=
    fun t k => if k = 0 then y t (idxS d) else y t (idxC d)
  let β : ℝ → Fin 2 → ℝ :=
    fun t k => if k = 0 then Real.sin t else Real.cos t
  have hα0 : α 0 = (fun k : Fin 2 => if k = 0 then 0 else 1) := by
    ext k
    fin_cases k <;> simp [α, hy0, clippedInit_s, clippedInit_c]
  have hβ0 : β 0 = (fun k : Fin 2 => if k = 0 then 0 else 1) := by
    ext k
    fin_cases k <;> simp [β]
  have hlip : ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin 2 → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖ := by
    intro R hR
    refine ⟨1, ?_⟩
    intro x y _ _
    rw [one_mul]
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    have hcoord : ∀ i : Fin 2, ‖(x - y) i‖ ≤ ‖x - y‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).mp le_rfl
    fin_cases k
    · simpa [f, Pi.sub_apply] using hcoord (1 : Fin 2)
    · calc
        ‖(f x - f y) 1‖ = ‖(x - y) 0‖ := by
          simp [f, Pi.sub_apply, sub_eq_add_neg]
          rw [show -x 0 + y 0 = -(x 0 + -y 0) by ring, abs_neg]
        _ ≤ ‖x - y‖ := hcoord (0 : Fin 2)
  have hα_deriv : ∀ T : ℝ, 0 < T → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt α (f (α t)) (Set.Icc 0 T) t := by
    intro T hT t ht
    have hpi : HasDerivAt α (f (α t)) t := by
      apply hasDerivAt_pi.mpr
      intro k
      have hyt := hyode t ht.1
      fin_cases k
      · have hs := (hasDerivAt_pi.mp hyt) (idxS d)
        simpa [α, f, clippedField_s] using hs
      · have hc := (hasDerivAt_pi.mp hyt) (idxC d)
        simpa [α, f, clippedField_c] using hc
    exact hpi.hasDerivWithinAt
  have hβ_deriv : ∀ T : ℝ, 0 < T → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt β (f (β t)) (Set.Icc 0 T) t := by
    intro T hT t ht
    have hpi : HasDerivAt β (f (β t)) t := by
      apply hasDerivAt_pi.mpr
      intro k
      fin_cases k
      · simpa [β, f] using Real.hasDerivAt_sin t
      · simpa [β, f] using Real.hasDerivAt_cos t
    exact hpi.hasDerivWithinAt
  have hα_bound : ∀ T : ℝ, 0 < T → ∀ t ∈ Set.Icc (0 : ℝ) T, ‖α t‖ ≤ 1 := by
    intro T hT t ht
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    fin_cases k
    · simpa [α, Real.norm_eq_abs] using hsb t ht.1
    · simpa [α, Real.norm_eq_abs] using hcb t ht.1
  have hβ_bound : ∀ T : ℝ, 0 < T → ∀ t ∈ Set.Icc (0 : ℝ) T, ‖β t‖ ≤ 1 := by
    intro T hT t ht
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    fin_cases k
    · simpa [β, Real.norm_eq_abs] using Real.abs_sin_le_one t
    · simpa [β, Real.norm_eq_abs] using Real.abs_cos_le_one t
  intro t ht
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t ∈ Set.Icc (0 : ℝ) T := by dsimp [T]; constructor <;> linarith
  have hagree := Ripple.solutions_agree_on_Icc (f := f)
    (y₀ := fun k : Fin 2 => if k = 0 then 0 else 1)
    (M := (1 : ℝ)) hT zero_le_one hlip hα0 hβ0
    (hα_deriv T hT) (hβ_deriv T hT) (hα_bound T hT) (hβ_bound T hT)
  have heq := hagree htT
  constructor
  · have := congr_fun heq (0 : Fin 2)
    simpa [α, β] using this
  · have := congr_fun heq (1 : Fin 2)
    simpa [α, β] using this

private theorem cycle_cover {t : ℝ} (ht : 0 ≤ t) :
    ∃ j : ℕ, t ∈ Set.Icc (2 * π * (j : ℝ)) (2 * π * ((j : ℝ) + 1)) := by
  let p : ℝ := 2 * π
  have hp : 0 < p := by dsimp [p]; positivity
  let x : ℝ := t / p
  have hx0 : 0 ≤ x := by exact div_nonneg ht hp.le
  refine ⟨Nat.floor x, ?_, ?_⟩
  · have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hmul := mul_le_mul_of_nonneg_left hfloor hp.le
    have hpx : p * x = t := by dsimp [x]; field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith
  · have hlt : x < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hpx : p * x = t := by dsimp [x]; field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith
/-- **P10′, boxed iterator existence (the `hsupply` provider).**
Under the same data as `all_time_tracking` — a robust real extension
whose encoded orbit has uniformly `D_K/4`-bounded steps, Lipschitz
modulus `LF` and bound `BF` for `evalF` on the `2 D_K`-enlargement of
the orbit tube, and cascade-satisfying parameters `A, M` — the
iterator has a global solution from every encoded input, and that
solution satisfies the moving-box certificate.

Proof route (verified design):
1. CLIP: replace `S.evalF` by the componentwise clamp
   `F̃ x i := max (lo w i) (min (hi w i) (S.evalF x i))`-style bounded
   Lipschitz continuation agreeing with `evalF` on the working tube.
2. GLOBAL EXISTENCE for the clipped non-autonomous system: RHS is
   globally Lipschitz in the state, continuous in `t` (gates are
   `qPulse/rPulse`), so Picard–Lindelöf iterates converge on every
   compact time interval (Mathlib `IsPicardLindelof` /
   `exists_forall_hasDerivAt...`; chain local solutions).
3. BOOTSTRAP: let `T* := sup {T : the clipped solution satisfies the
   moving-box bounds on [0, T]}`.  On `[0, T*)` the clip is inactive,
   so the tracking analysis (`perturbation_recurrence` /
   `all_time_tracking`, already PROVED) applies verbatim and yields
   STRICTLY interior bounds at `T*`; continuity extends them past
   `T*` — clopen argument forces `T* = ∞`.
4. The clipped solution on the box solves the true ODE — package as
   `IteratorSol` + `MovingBox`. -/
theorem boxed_iterator_exists
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    -- bounded encoded orbit (v3 fractional architecture)
    (B_orb : ℝ) (hBorb : 0 < B_orb)
    (horb : ∀ (w j : ℕ) (i : Fin d), |orbitPoint Mch E w j i| ≤ B_orb)
    -- clip level C and crude radius Dc, with their defining inequalities
    -- (D-3 round-3 finding: the cascade must be quantified at the SAME
    -- radius the dissipative bound supplies; single-radius narrative)
    (C Dc : ℝ)
    (hC : B_orb + (S.ηstep : ℝ) + 1 ≤ C)
    (hDc : C + B_orb ≤ Dc)
    -- F-data on the Dc-tubes (where the solution provably lives):
    (hFbound : ∀ (w j : ℕ) (x : Fin d → ℝ),
      (∀ i, |x i - orbitPoint Mch E w j i| ≤ Dc) →
      ∀ i, |S.evalF x i| ≤ C)
    (LF : ℝ) (hLF : 0 ≤ LF)
    (hFlip : ∀ (w j : ℕ) (x y : Fin d → ℝ),
      (∀ i, |x i - orbitPoint Mch E w j i| ≤ Dc) →
      (∀ i, |y i - orbitPoint Mch E w j i| ≤ Dc) →
      ∀ r : ℝ, 0 ≤ r → (∀ i, |x i - y i| ≤ r) →
      ∀ i, |S.evalF x i - S.evalF y i| ≤ LF * r)
    (A : ℝ) (hA : 0 < A) (M : ℕ)
    (η : ℝ) (hη : 0 < η)
    -- cascade at the crude radius Dc:
    (hcasc₀ : 2 * trackingKappa A M < 1)
    (hcasc₁ : 2 * trackingKappa A M * Dc + 2 * trackingChi A M * Dc
        + (S.ηstep : ℝ) ≤ η * (1 - 2 * trackingKappa A M))
    (hcasc₂ : η + trackingChi A M * Dc ≤ (S.r₀ : ℝ)) :
    ∀ w : ℕ,
      ∃ sol : IteratorSol d S.evalF A M (orbitPoint Mch E w 0),
        MovingBox S sol Dc := by
  intro w
  have hηstep_nonneg : 0 ≤ (S.ηstep : ℝ) := by exact_mod_cast S.ηstep_pos.le
  have hCpos : 0 < C := by nlinarith [hC, hBorb, hηstep_nonneg]
  have hCnonneg : 0 ≤ C := hCpos.le
  have hDcpos : 0 < Dc := by nlinarith [hDc, hCpos, hBorb]
  obtain ⟨y, hy0, hyode, hsb, hcb, hzb, hub⟩ :=
    clipped_global_solution S B_orb C A M w hBorb hA (horb w 0) hC
  let vz : Fin d → ℝ := fun i => clippedField S C A M (y 0) (idxZ i)
  let vu : Fin d → ℝ := fun i => clippedField S C A M (y 0) (idxU i)
  let z : ℝ → Fin d → ℝ :=
    fun t i => forwardExtend (fun τ => zPart (y τ) i) (vz i) t
  let u : ℝ → Fin d → ℝ :=
    fun t i => forwardExtend (fun τ => uPart (y τ) i) (vu i) t
  have hz_nonneg : ∀ t : ℝ, 0 ≤ t → z t = zPart (y t) := by
    intro t ht
    ext i
    simp [z, forwardExtend, ht]
  have hu_nonneg : ∀ t : ℝ, 0 ≤ t → u t = uPart (y t) := by
    intro t ht
    ext i
    simp [u, forwardExtend, ht]
  have hclock := clipped_clock_eq S C A M (orbitPoint Mch E w 0) y
    hy0 hyode hsb hcb
  have hclip_inactive : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d,
      clippedF S C (u t) i = S.evalF (u t) i := by
    intro t ht i
    obtain ⟨j, hj⟩ := cycle_cover ht
    have huclose : ∀ l : Fin d, |u t l - orbitPoint Mch E w j l| ≤ Dc := by
      intro l
      have hut : u t l = uPart (y t) l := congr_fun (hu_nonneg t ht) l
      calc
        |u t l - orbitPoint Mch E w j l|
            = |uPart (y t) l - orbitPoint Mch E w j l| := by rw [hut]
        _ ≤ |uPart (y t) l| + |orbitPoint Mch E w j l| := by
            simpa [abs_sub_comm] using
              abs_sub_le (uPart (y t) l) 0 (orbitPoint Mch E w j l)
        _ ≤ C + B_orb := add_le_add (hub t ht l) (horb w j l)
        _ ≤ Dc := hDc
    exact clamp_eq_self_of_abs_le (hFbound w j (u t) huclose i)
  let sol : IteratorSol d S.evalF A M (orbitPoint Mch E w 0) :=
    { z := z
      u := u
      init_z := by
        ext i
        simp [z, vz, forwardExtend, hy0, clippedInit_z]
      init_u := by
        ext i
        simp [u, vu, forwardExtend, hy0, clippedInit_u]
      cont_z := by
        intro i
        exact forwardExtend_continuous
          (fun τ => zPart (y τ) i)
          (fun τ => clippedField S C A M (y τ) (idxZ i))
          (fun τ => clippedField S C A M (y τ) (idxZ i))
          (by
            intro t ht
            exact (hasDerivAt_pi.mp (hyode t ht)) (idxZ i))
      cont_u := by
        intro i
        exact forwardExtend_continuous
          (fun τ => uPart (y τ) i)
          (fun τ => clippedField S C A M (y τ) (idxU i))
          (fun τ => clippedField S C A M (y τ) (idxU i))
          (by
            intro t ht
            exact (hasDerivAt_pi.mp (hyode t ht)) (idxU i))
      ode_z := by
        intro t ht i
        have hraw : HasDerivAt (fun τ => z τ i)
            (clippedField S C A M (y t) (idxZ i)) t := by
          exact forwardExtend_hasDerivAt_nonneg
            (fun τ => zPart (y τ) i)
            (fun τ => clippedField S C A M (y τ) (idxZ i))
            (by
              intro s hs
              exact (hasDerivAt_pi.mp (hyode s hs)) (idxZ i))
            t ht
        convert hraw using 1
        have hzfun := hz_nonneg t ht
        have hufun := hu_nonneg t ht
        have hsine := (hclock t ht).1
        rw [clippedField_z, hsine, qPulse]
        rw [← hufun, hclip_inactive t ht i]
        rw [← congr_fun hzfun i]
      ode_u := by
        intro t ht i
        have hraw : HasDerivAt (fun τ => u τ i)
            (clippedField S C A M (y t) (idxU i)) t := by
          exact forwardExtend_hasDerivAt_nonneg
            (fun τ => uPart (y τ) i)
            (fun τ => clippedField S C A M (y τ) (idxU i))
            (by
              intro s hs
              exact (hasDerivAt_pi.mp (hyode s hs)) (idxU i))
            t ht
        convert hraw using 1
        have hzfun := hz_nonneg t ht
        have hufun := hu_nonneg t ht
        have hsine := (hclock t ht).1
        rw [clippedField_u, hsine, rPulse]
        rw [← congr_fun hzfun i, ← congr_fun hufun i] }
  refine ⟨sol, ?_⟩
  intro j t htcycle
  have ht_nonneg : 0 ≤ t := by
    have hjnonneg : 0 ≤ 2 * π * (j : ℝ) := by positivity
    exact le_trans hjnonneg htcycle.1
  have hzfun := hz_nonneg t ht_nonneg
  have hufun := hu_nonneg t ht_nonneg
  constructor
  · intro i
    calc
      |orbitPoint Mch E w (j + 1) i - orbitPoint Mch E w j i|
          ≤ |orbitPoint Mch E w (j + 1) i| + |orbitPoint Mch E w j i| := by
          simpa using abs_sub_le (orbitPoint Mch E w (j + 1) i) 0
            (orbitPoint Mch E w j i)
      _ ≤ B_orb + B_orb := add_le_add (horb w (j + 1) i) (horb w j i)
      _ ≤ C + B_orb := by nlinarith [hC, hηstep_nonneg]
      _ ≤ Dc := hDc
  constructor
  · intro i
    calc
      |sol.z t i - orbitPoint Mch E w j i|
          = |zPart (y t) i - orbitPoint Mch E w j i| := by
          change |z t i - orbitPoint Mch E w j i| =
            |zPart (y t) i - orbitPoint Mch E w j i|
          rw [congr_fun hzfun i]
      _ ≤ |zPart (y t) i| + |orbitPoint Mch E w j i| := by
          simpa [abs_sub_comm] using
            abs_sub_le (zPart (y t) i) 0 (orbitPoint Mch E w j i)
      _ ≤ C + B_orb := add_le_add (hzb t ht_nonneg i) (horb w j i)
      _ ≤ Dc := hDc
  constructor
  · intro i
    calc
      |sol.u t i - orbitPoint Mch E w j i|
          = |uPart (y t) i - orbitPoint Mch E w j i| := by
          change |u t i - orbitPoint Mch E w j i| =
            |uPart (y t) i - orbitPoint Mch E w j i|
          rw [congr_fun hufun i]
      _ ≤ |uPart (y t) i| + |orbitPoint Mch E w j i| := by
          simpa [abs_sub_comm] using
            abs_sub_le (uPart (y t) i) 0 (orbitPoint Mch E w j i)
      _ ≤ C + B_orb := add_le_add (hub t ht_nonneg i) (horb w j i)
      _ ≤ Dc := hDc
  · intro i
    have huclose : ∀ l : Fin d, |sol.u t l - orbitPoint Mch E w j l| ≤ Dc := by
      intro l
      calc
        |sol.u t l - orbitPoint Mch E w j l|
            = |uPart (y t) l - orbitPoint Mch E w j l| := by
            change |u t l - orbitPoint Mch E w j l| =
              |uPart (y t) l - orbitPoint Mch E w j l|
            rw [congr_fun hufun l]
        _ ≤ |uPart (y t) l| + |orbitPoint Mch E w j l| := by
            simpa [abs_sub_comm] using
              abs_sub_le (uPart (y t) l) 0 (orbitPoint Mch E w j l)
        _ ≤ C + B_orb := add_le_add (hub t ht_nonneg l) (horb w j l)
        _ ≤ Dc := hDc
    calc
      |S.evalF (sol.u t) i - orbitPoint Mch E w j i|
          ≤ |S.evalF (sol.u t) i| + |orbitPoint Mch E w j i| := by
          simpa [abs_sub_comm] using
            abs_sub_le (S.evalF (sol.u t) i) 0 (orbitPoint Mch E w j i)
      _ ≤ C + B_orb := add_le_add (hFbound w j (sol.u t) huclose i) (horb w j i)
      _ ≤ Dc := hDc

end Ripple.BoundedUniversality.BGP
