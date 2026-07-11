/-
Ripple.BoundedUniversality.GPAC.RationalRounding
----------------------------
The rational rounding obstruction and its bounded-encoding resolution.

Bournez–Graça–Pouly's TM-by-polynomial-ODE simulation uses an
error-correcting ROUNDING helper, realized in the published work by the
trigonometric macro `(1/2π)·arccos(cos 2πx)` — which forces `π` into the
coefficients.  Can it be replaced by a RATIONAL polynomial?

This file proves the dichotomy (ChatGPT-pro RB1 verdict, independently
re-derived):

* `no_global_rational_rounder` — NO single polynomial (rational or even
  real) can contract neighborhoods of *every* integer toward their
  centers.  So a global rounder on the unbounded lattice ℤ is impossible;
  the published periodic helper genuinely uses periodicity.

* `finite_symbol_rounder` (next) — but on a BOUNDED/finite symbol set
  `{0,…,B}` an explicit rational polynomial contraction exists (Hermite
  interpolation).  Hence "bounded + rational" is synergistic: compact
  encoding is exactly what makes rational rounding possible.
-/

import Mathlib

namespace Ripple.BoundedUniversality.GPAC.RationalRounding

open Polynomial

/-- **Obstruction.** No real polynomial can act as a rounding contraction
near every integer: if `|P(n+e) − n| ≤ λ|e|` for all integers `n` and all
small `e`, with contraction factor `λ < 1`, then no such `P` exists.

In particular no *rational* polynomial gives a global integer rounder —
the published BGP periodic helper cannot be replaced by one fixed
polynomial on the unbounded lattice. -/
theorem no_global_rational_rounder
    (P : ℝ[X]) (lam ρ : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hρ : 0 < ρ)
    (h : ∀ (n : ℤ) (e : ℝ), |e| ≤ ρ → |P.eval ((n : ℝ) + e) - (n : ℝ)| ≤ lam * |e|) :
    False := by
  -- Step 1: at e = 0, P fixes every integer.
  have hfix : ∀ n : ℤ, P.eval (n : ℝ) = (n : ℝ) := by
    intro n
    have h0 := h n 0 (by simpa using le_of_lt hρ)
    simp only [add_zero, abs_zero, mul_zero] at h0
    have : |P.eval (n : ℝ) - (n : ℝ)| = 0 := le_antisymm h0 (abs_nonneg _)
    have := abs_eq_zero.mp this
    linarith [sub_eq_zero.mp this]
  -- Step 2: P − X has infinitely many roots (all integers), hence is 0.
  have hroots : Set.Infinite {x : ℝ | (P - X).IsRoot x} := by
    apply Set.Infinite.mono (s := Set.range (fun n : ℤ => (n : ℝ)))
    · rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, eval_X, hfix n, sub_self]
    · exact Set.infinite_range_of_injective (fun a b hab => by exact_mod_cast hab)
  have hPX : P - X = 0 := Polynomial.eq_zero_of_infinite_isRoot _ hroots
  have hP : P = X := by linear_combination hPX
  -- Step 3: then P(n+e) = n+e exactly, so |e| ≤ λ|e|; take e = ρ > 0.
  have hcontr := h 0 ρ (by rw [abs_of_pos hρ])
  rw [hP] at hcontr
  simp only [eval_X, Int.cast_zero, add_zero, zero_add, sub_zero] at hcontr
  rw [abs_of_pos hρ] at hcontr
  nlinarith

/-! ### Obstruction inside the robust-step layer (F2)

The compactness obstruction strikes the *unbounded* fuel register machine
at the level of the robust polynomial step itself: no single polynomial can
robustly track "increment the fuel until the halt time `k₀`, then freeze"
(the absorbing-halt behaviour) with a separation/error radius below `1/2`.
Same mechanism as `no_global_rational_rounder` (a polynomial bounded on an
unbounded ℕ-tail is constant). This is why the robust-step interface must be
re-typed over a space bound `S` rather than over the unbounded `ℕ`. -/
theorem no_robust_increment_freeze
    (q : ℝ[X]) (k0 : ℕ) (hk0 : 1 ≤ k0) (ε : ℝ) (hε : ε < 1/2)
    (hinc : ∀ k : ℕ, k < k0 → |q.eval (k : ℝ) - ((k : ℝ) + 1)| ≤ ε)
    (hfreeze : ∀ k : ℕ, k0 ≤ k → |q.eval (k : ℝ) - (k : ℝ)| ≤ ε) : False := by
  set r : ℝ[X] := q - X with hr
  have hreval : ∀ x : ℝ, r.eval x = q.eval x - x := fun x => by rw [hr]; simp
  -- r is constant: degree ≤ 0, else |r| → ∞ contradicts the ε-bound on the tail
  have hdeg : r.degree ≤ 0 := by
    by_contra h
    push_neg at h
    have htend : Filter.Tendsto (fun k : ℕ => |r.eval (k : ℝ)|) Filter.atTop Filter.atTop :=
      (Polynomial.abs_tendsto_atTop r h).comp tendsto_natCast_atTop_atTop
    have hbd : ∀ᶠ k : ℕ in Filter.atTop, |r.eval (k : ℝ)| ≤ ε := by
      filter_upwards [Filter.eventually_ge_atTop k0] with k hk
      rw [hreval]; exact hfreeze k hk
    obtain ⟨k, hgt, hle⟩ := ((htend.eventually_gt_atTop ε).and hbd).exists
    linarith
  have hc : r = C (r.coeff 0) := Polynomial.degree_le_zero_iff.mp hdeg
  set c := r.coeff 0 with hcdef
  have hrc : ∀ x : ℝ, r.eval x = c := fun x => by rw [hc, eval_C]
  -- c = q(k0) - k0 (freeze) and c = q(0) (increment at 0)
  have hcf : |c| ≤ ε := by
    have e : c = q.eval (k0 : ℝ) - (k0 : ℝ) := by
      have h1 : r.eval (k0 : ℝ) = c := hrc _
      have h2 : r.eval (k0 : ℝ) = q.eval (k0 : ℝ) - (k0 : ℝ) := hreval _
      linarith
    rw [e]; exact hfreeze k0 (le_refl k0)
  have hci : |c - 1| ≤ ε := by
    have e : c = q.eval (0 : ℝ) := by
      have h1 : r.eval (0 : ℝ) = c := hrc _
      have h2 : r.eval (0 : ℝ) = q.eval (0 : ℝ) - 0 := hreval _
      simp only [sub_zero] at h2; linarith
    have h := hinc 0 (by omega)
    rw [e]; simpa using h
  have b1 := abs_le.mp hcf; have b2 := abs_le.mp hci
  linarith [b1.1, b1.2, b2.1, b2.2]

/-! ### The bounded / finite-symbol rational rounder

On a finite symbol set `{0,…,B}` an explicit RATIONAL polynomial with
the rounding fixed points and contraction slope exists, via
`R = X + W·S` where `W` is the nodal polynomial `∏(X−i)` and `S` is the
Lagrange interpolant chosen so that `R'(i) = 1/4` at every symbol.
This is the algebraic core of the bounded rational rounder; combined
with the mean value theorem it gives a genuine contraction on a
neighborhood of each symbol (next step).  Establishing it makes precise
that *bounded encoding is what enables rational rounding*. -/

open Lagrange in
/-- Algebraic core: over ℚ there is a polynomial fixing every symbol
`0,…,B` with derivative `1/4` there (a contraction slope). -/
theorem finite_symbol_rounder_algebraic (B : ℕ) :
    ∃ R : ℚ[X],
      (∀ i ∈ Finset.Icc 0 B, R.eval (i : ℚ) = (i : ℚ)) ∧
      (∀ i ∈ Finset.Icc 0 B, (derivative R).eval (i : ℚ) = 1/4) := by
  classical
  let s : Finset ℕ := Finset.Icc 0 B
  let c : ℕ → ℚ := fun n => (n : ℚ)
  have hinj : Set.InjOn c ↑s := by
    intro a _ b _ hab
    have hab' : (a : ℚ) = (b : ℚ) := hab
    exact_mod_cast hab'
  let W : ℚ[X] := Lagrange.nodal s c
  let D : ℕ → ℚ := fun j => (derivative W).eval (c j)
  have hWnode : ∀ j ∈ s, W.eval (c j) = 0 := by
    intro j hj
    show (Lagrange.nodal s c).eval (c j) = 0
    rw [Lagrange.eval_nodal]
    exact Finset.prod_eq_zero hj (by simp)
  have hDdiag : ∀ j ∈ s, D j = ∏ k ∈ s.erase j, (c j - c k) := by
    intro j hj
    show (derivative (Lagrange.nodal s c)).eval (c j) = _
    rw [Lagrange.derivative_nodal, eval_finset_sum, Finset.sum_eq_single j]
    · rw [Lagrange.eval_nodal]
    · intro i _ hij
      rw [Lagrange.eval_nodal]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hij h.symm, hj⟩) (by simp)
    · intro hjs; exact absurd hj hjs
  have hDne : ∀ j ∈ s, D j ≠ 0 := by
    intro j hj
    rw [hDdiag j hj]
    refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    refine sub_ne_zero.mpr (fun h => hkj ?_)
    have h' : (j : ℚ) = (k : ℚ) := h
    exact (by exact_mod_cast h'.symm : k = j)
  let S : ℚ[X] := Lagrange.interpolate s c (fun j => -3 / (4 * D j))
  refine ⟨X + W * S, ?_, ?_⟩
  · intro i hi
    show (X + W * S).eval (c i) = c i
    simp only [eval_add, eval_X, eval_mul, hWnode i hi, zero_mul, add_zero]
  · intro i hi
    show (derivative (X + W * S)).eval (c i) = 1/4
    rw [derivative_add, derivative_X, derivative_mul]
    simp only [eval_add, eval_one, eval_mul, hWnode i hi, zero_mul, add_zero]
    have hSi : S.eval (c i) = -3 / (4 * D i) :=
      Lagrange.eval_interpolate_at_node _ hinj hi
    have hDi : (derivative W).eval (c i) = D i := rfl
    rw [hDi, hSi]
    have hne := hDne i hi
    field_simp
    ring

/-- **Bounded rational rounder (full contraction).** The rational
polynomial of `finite_symbol_rounder_algebraic`, viewed as a real
function, is a genuine contraction toward each symbol on a neighborhood:
`|R(i+e) − i| ≤ (1/2)|e|`.  Proved by upgrading the contraction slope
`R'(i)=1/4` via the mean value inequality (the derivative stays `≤ 1/2`
near each symbol by continuity).  Combined with `no_global_rational_rounder`,
this is the rounding error-corrector realized with rational coefficients
on a bounded symbol set — the gadget BGP needed `π` for. -/
theorem finite_symbol_rounder (B : ℕ) :
    ∃ R : ℚ[X], ∀ i ∈ Finset.Icc 0 B, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ e : ℝ, |e| ≤ ρ →
        |(R.map (algebraMap ℚ ℝ)).eval ((i : ℝ) + e) - (i : ℝ)| ≤ (1/2) * |e| := by
  obtain ⟨R, hfix, hderiv⟩ := finite_symbol_rounder_algebraic B
  refine ⟨R, fun i hi => ?_⟩
  set Rℝ : ℝ[X] := R.map (algebraMap ℚ ℝ) with hRℝ
  have hcast : ((i : ℕ) : ℝ) = algebraMap ℚ ℝ ((i : ℕ) : ℚ) :=
    (map_natCast (algebraMap ℚ ℝ) i).symm
  -- Rℝ(i) = i
  have hfixℝ : Rℝ.eval (i : ℝ) = (i : ℝ) := by
    rw [hRℝ, hcast, eval_map, eval₂_at_apply, hfix i hi]
  -- Rℝ'(i) = 1/4
  have hderivℝ : (Rℝ.derivative).eval (i : ℝ) = 1/4 := by
    rw [hRℝ, derivative_map, hcast, eval_map, eval₂_at_apply, hderiv i hi]
    rw [eq_ratCast (algebraMap ℚ ℝ) (1/4)]; norm_num
  -- |Rℝ'| ≤ 1/2 on an open neighborhood of i
  have hcont : Continuous (fun x : ℝ => |(Rℝ.derivative).eval x|) :=
    (Rℝ.derivative.continuous).abs
  have hopen : IsOpen {x : ℝ | |(Rℝ.derivative).eval x| < 1/2} :=
    isOpen_lt hcont continuous_const
  have hmem : (i : ℝ) ∈ {x : ℝ | |(Rℝ.derivative).eval x| < 1/2} := by
    simp only [Set.mem_setOf_eq, hderivℝ]; norm_num
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hopen (i : ℝ) hmem
  refine ⟨ρ₀ / 2, by linarith, fun e he => ?_⟩
  -- mean value inequality on the closed ball of radius ρ₀/2
  set s : Set ℝ := Metric.closedBall (i : ℝ) (ρ₀ / 2) with hs
  have hconv : Convex ℝ s := convex_closedBall _ _
  have hbound : ∀ x ∈ s, ‖deriv (fun y => Rℝ.eval y) x‖ ≤ (1/2 : ℝ) := by
    intro x hx
    rw [Polynomial.deriv, Real.norm_eq_abs]
    have hxb : x ∈ Metric.ball (i : ℝ) ρ₀ := by
      rw [Metric.mem_closedBall] at hx; rw [Metric.mem_ball]; linarith
    exact le_of_lt (hball hxb)
  have hdiff : ∀ x ∈ s, DifferentiableAt ℝ (fun y => Rℝ.eval y) x :=
    fun x _ => Rℝ.differentiable.differentiableAt
  have hi_s : (i : ℝ) ∈ s := Metric.mem_closedBall_self (by linarith)
  have hy_s : (i : ℝ) + e ∈ s := by
    rw [hs, Metric.mem_closedBall, Real.dist_eq]; simpa using he
  have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hi_s hy_s
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hfixℝ] at hmvt
  have : ((i : ℝ) + e) - (i : ℝ) = e := by ring
  rw [this] at hmvt
  exact hmvt

/-- Uniform-radius version: a single `ρ > 0` works for every symbol
(finite minimum of the per-symbol radii). -/
theorem finite_symbol_rounder_uniform (B : ℕ) :
    ∃ R : ℚ[X], ∃ ρ : ℝ, 0 < ρ ∧ ∀ i ∈ Finset.Icc 0 B, ∀ e : ℝ, |e| ≤ ρ →
      |(R.map (algebraMap ℚ ℝ)).eval ((i : ℝ) + e) - (i : ℝ)| ≤ (1/2) * |e| := by
  classical
  obtain ⟨R, hR⟩ := finite_symbol_rounder B
  refine ⟨R, ?_⟩
  set s := Finset.Icc 0 B with hsdef
  have hne : s.Nonempty := ⟨0, by rw [hsdef]; exact Finset.mem_Icc.mpr ⟨le_refl 0, Nat.zero_le B⟩⟩
  let f : ℕ → ℝ := fun i => if h : i ∈ s then Classical.choose (hR i h) else 1
  have hfspec : ∀ i (hi : i ∈ s), 0 < f i ∧
      ∀ e, |e| ≤ f i →
        |(R.map (algebraMap ℚ ℝ)).eval ((i : ℝ) + e) - (i : ℝ)| ≤ (1/2) * |e| := by
    intro i hi
    rw [show f i = Classical.choose (hR i hi) from dif_pos hi]
    exact Classical.choose_spec (hR i hi)
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image s f hne
  exact ⟨f i₀, (hfspec i₀ hi₀).1, fun i hi e he => (hfspec i hi).2 e (le_trans he (hmin i hi))⟩

/-- **Coordinatewise rounder contracts in sup-norm.** Applying the rational
rounder to each coordinate gives a `½`-contraction (in the `ℓ∞` metric on
`Fin N → ℝ`) toward any grid point whose coordinates are symbols in
`{0,…,B}`.  This is the map `C` consumed by `step_contracts`: it instantiates
the abstract robustness mechanism with the concrete rational rounder. -/
theorem coordinatewise_rounder_contracts (B N : ℕ) :
    ∃ R : ℚ[X], ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (g : Fin N → ℝ), (∀ j, ∃ i ∈ Finset.Icc 0 B, g j = (i : ℝ)) →
        ∀ (x : Fin N → ℝ), dist x g ≤ ρ →
          dist (fun j => (R.map (algebraMap ℚ ℝ)).eval (x j)) g ≤ (1/2) * dist x g := by
  obtain ⟨R, ρ, hρ, hunif⟩ := finite_symbol_rounder_uniform B
  refine ⟨R, ρ, hρ, fun g hg x hx => ?_⟩
  rw [dist_pi_le_iff (by positivity)]
  intro j
  obtain ⟨i, hi, hgj⟩ := hg j
  have hdj : dist (x j) (g j) ≤ ρ := le_trans (dist_le_pi_dist x g j) hx
  have he : |x j - (i : ℝ)| ≤ ρ := by
    rw [← Real.dist_eq, ← hgj]; exact hdj
  have hb := hunif i hi (x j - (i : ℝ)) he
  rw [show (i : ℝ) + (x j - (i : ℝ)) = x j from by ring] at hb
  rw [hgj, Real.dist_eq]
  refine le_trans hb ?_
  have : |x j - (i : ℝ)| = dist (x j) (g j) := by rw [hgj, Real.dist_eq]
  rw [this]
  gcongr
  exact dist_le_pi_dist x g j

end Ripple.BoundedUniversality.GPAC.RationalRounding
