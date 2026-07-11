/-
Ripple.BoundedUniversality.HenonSelector.RotationCounterexample
--------------------------------------------
F3: The rotation R(u,v) = (3u/5 - 4v/5, 4u/5 + 3v/5) preserves S¹,
all orbit points are Q-algebraic (in fact rational), and the orbit
is infinite. This refutes the general principle "algebraic point in
compact rational dynamics ⇒ eventually periodic orbit" (Claim B).

The key tool: z = (3+4i)/5 is NOT a root of unity, proved by the
algebraic-integer trace argument (z + z⁻¹ = 6/5, which would need
to be an algebraic integer if z were a root of unity, contradicting
6/5 ∉ ℤ).
-/

import Ripple.BoundedUniversality.HenonSelector.Henon

namespace Ripple.BoundedUniversality.HenonSelector

noncomputable def rot (p : Point2) : Point2 :=
  (((3 : ℝ) / 5) * p.1 - ((4 : ℝ) / 5) * p.2,
   ((4 : ℝ) / 5) * p.1 + ((3 : ℝ) / 5) * p.2)

def rotQ (p : ℚ × ℚ) : ℚ × ℚ :=
  (((3 : ℚ) / 5) * p.1 - ((4 : ℚ) / 5) * p.2,
   ((4 : ℚ) / 5) * p.1 + ((3 : ℚ) / 5) * p.2)

def coeQPoint (p : ℚ × ℚ) : Point2 :=
  ((p.1 : ℝ), (p.2 : ℝ))

theorem rot_preserves_circle_expr (p : Point2) :
    (rot p).1 ^ 2 + (rot p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  simp only [rot]; ring

theorem rot_preserves_unit_circle
    {p : Point2} (hp : p.1 ^ 2 + p.2 ^ 2 = 1) :
    (rot p).1 ^ 2 + (rot p).2 ^ 2 = 1 := by
  rw [rot_preserves_circle_expr]; exact hp

theorem rotQ_commutes_with_coe (p : ℚ × ℚ) :
    coeQPoint (rotQ p) = rot (coeQPoint p) := by
  unfold coeQPoint rotQ rot
  simp only [Prod.mk.injEq]
  constructor <;> push_cast <;> ring

theorem rot_orbit_rational (n : ℕ) :
    ∃ q : ℚ × ℚ,
      Nat.iterate rot n ((1 : ℝ), (0 : ℝ)) = coeQPoint q := by
  induction n with
  | zero =>
    exact ⟨(1, 0), by unfold coeQPoint; simp⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨rotQ q, by
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [hq, ← rotQ_commutes_with_coe]⟩

theorem rot_orbit_alg (n : ℕ) :
    IsAlgPoint (Nat.iterate rot n ((1 : ℝ), (0 : ℝ))) := by
  obtain ⟨q, hq⟩ := rot_orbit_rational n
  rw [hq]; unfold coeQPoint IsAlgPoint
  exact ⟨isAlgebraic_algebraMap q.1, isAlgebraic_algebraMap q.2⟩

noncomputable def ζ : ℂ :=
  ((3 : ℂ) / 5) + ((4 : ℂ) / 5) * Complex.I

private theorem ζ_ne_zero : ζ ≠ 0 := by
  intro h
  have : ζ.re = 0 := by rw [h]; simp
  simp [ζ, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im] at this

private theorem ζ_add_inv_eq : ζ + ζ⁻¹ = ((6 : ℂ) / 5) := by
  have hne := ζ_ne_zero
  apply Complex.ext
  · simp [ζ, Complex.add_re, Complex.inv_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.normSq]
    norm_num
  · simp [ζ, Complex.add_im, Complex.inv_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.normSq]
    norm_num

theorem ζ_not_rootOfUnity :
    ¬ ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1 := by
  rintro ⟨n, hn, hpow⟩
  -- ζ^n = 1 ⇒ ζ integral over ℤ
  have hζ_int : IsIntegral ℤ ζ := by
    apply IsIntegral.of_pow hn
    simpa [hpow] using isIntegral_one (R := ℤ) (B := ℂ)
  -- (ζ⁻¹)^n = 1 ⇒ ζ⁻¹ integral over ℤ
  have hζinv_int : IsIntegral ℤ ζ⁻¹ := by
    apply IsIntegral.of_pow hn
    rw [inv_pow, hpow, inv_one]
    exact isIntegral_one
  -- ζ + ζ⁻¹ = 6/5 integral over ℤ
  have hsum_int : IsIntegral ℤ ((6 : ℂ) / 5) := by
    rw [← ζ_add_inv_eq]
    exact hζ_int.add hζinv_int
  -- Pull back to ℚ: 6/5 ∈ ℚ is integral over ℤ
  have h65Q : IsIntegral ℤ ((6 : ℚ) / 5) := by
    have : (algebraMap ℚ ℂ) ((6 : ℚ) / 5) = (6 : ℂ) / 5 := by simp [map_div₀]
    rw [← this] at hsum_int
    rwa [isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hsum_int
  -- ℤ is integrally closed in ℚ: integral ⇒ ∃ m : ℤ, ↑m = 6/5
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h65Q
  -- Contradiction: no integer equals 6/5
  have : (m : ℚ) = 6 / 5 := hm
  have : (5 : ℚ) * m = 6 := by linarith
  have : (5 : ℤ) * m = 6 := by exact_mod_cast this
  omega

private noncomputable def toComplex (p : Point2) : ℂ := ⟨p.1, p.2⟩

private theorem toComplex_rot (p : Point2) :
    toComplex (rot p) = ζ * toComplex p := by
  unfold toComplex rot ζ
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im] <;> ring

private theorem toComplex_rot_iter (n : ℕ) :
    toComplex (Nat.iterate rot n (1, 0)) = ζ ^ n := by
  induction n with
  | zero => simp [toComplex, ζ]; apply Complex.ext <;> simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [toComplex_rot, ih, pow_succ, mul_comm]

private theorem toComplex_injective : Function.Injective toComplex := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  simp only [toComplex, Complex.mk.injEq] at h
  exact Prod.ext h.1 h.2

private theorem ζ_pow_injective : Function.Injective (fun n : ℕ => ζ ^ n) := by
  intro m n h
  by_contra hmn
  wlog hmn_lt : m < n with H
  · push_neg at hmn_lt
    exact H h.symm (Ne.symm hmn) (lt_of_le_of_ne hmn_lt (Ne.symm hmn))
  apply ζ_not_rootOfUnity
  refine ⟨n - m, Nat.sub_pos_of_lt hmn_lt, ?_⟩
  have hne : ζ ^ m ≠ 0 := pow_ne_zero _ ζ_ne_zero
  have : ζ ^ n = ζ ^ m := h.symm
  have hmle : m ≤ n := hmn_lt.le
  calc ζ ^ (n - m) = ζ ^ n / ζ ^ m := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
            ← zpow_sub₀ ζ_ne_zero]; congr 1; omega
    _ = ζ ^ m / ζ ^ m := by rw [this]
    _ = 1 := div_self (pow_ne_zero _ ζ_ne_zero)

private theorem rot_iter_injective :
    Function.Injective (fun n : ℕ => Nat.iterate rot n ((1 : ℝ), (0 : ℝ))) := by
  intro m n h
  apply ζ_pow_injective
  have : toComplex (rot ^[m] (1, 0)) = toComplex (rot ^[n] (1, 0)) := congr_arg toComplex h
  rwa [toComplex_rot_iter, toComplex_rot_iter] at this

theorem rot_orbit_infinite :
    Set.Infinite
      { p : Point2 | ∃ n : ℕ, p = Nat.iterate rot n ((1 : ℝ), (0 : ℝ)) } := by
  have : { p : Point2 | ∃ n : ℕ, p = rot ^[n] (1, 0) } =
      Set.range (fun n : ℕ => rot ^[n] ((1 : ℝ), (0 : ℝ))) := by
    ext p; simp [Set.mem_range, eq_comm]
  rw [this]
  exact Set.infinite_range_of_injective rot_iter_injective

end Ripple.BoundedUniversality.HenonSelector
