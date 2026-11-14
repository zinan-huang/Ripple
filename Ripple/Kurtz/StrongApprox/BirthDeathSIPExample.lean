import Ripple.Kurtz.StrongApprox.PoissonDriverFamily
import Ripple.Kurtz.StrongApprox.CellRecordTimeCoverage
import Ripple.Kurtz.StrongApprox.SIPDensityPerScaleStart

/-!
# End-to-end instance of the per-scale-start SIP theorem

One-dimensional birth/death chain on `[0,1]` with bounded clipped rates
`up(y) = clamp(1 - y)`, `down(y) = clamp(y)`, `clamp a = max 0 (min a 1)`.
The drift `F(y) = clamp(1-y) - clamp(y)` vanishes at `1/2`, so the constant
`x ≡ 1/2` solves the integral equation; `F` is `2`-Lipschitz.  The scale-`n`
lattice start is `⌊n/2⌋`.
-/

open Ripple.Kurtz
open Ripple.Kurtz.StrongApprox
open Ripple.Kurtz.StrongApprox.CellPerScaleDensityAlignment
open Ripple.Kurtz.StrongApprox.CellDensityChannelAlignment
open Ripple.CTMC
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

noncomputable section

namespace BirthDeathSIP

def up : Fin 1 → ℤ := fun _ => 1
def down : Fin 1 → ℤ := fun _ => -1

theorem up_ne_down : up ≠ down := by
  intro h
  have := congrFun h 0
  simp [up, down] at this

theorem up_ne_zero : up ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [up] at this

theorem down_ne_zero : down ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [down] at this

/-- clipping to `[0,1]` -/
def clamp (a : ℝ) : ℝ := max 0 (min a 1)

theorem clamp_nonneg (a : ℝ) : 0 ≤ clamp a := le_max_left _ _
theorem clamp_le_one (a : ℝ) : clamp a ≤ 1 :=
  max_le zero_le_one (min_le_right _ _)

theorem clamp_lip (a b : ℝ) : |clamp a - clamp b| ≤ |a - b| := by
  unfold clamp
  calc
    |max 0 (min a 1) - max 0 (min b 1)| ≤
        max |(0 : ℝ) - 0| |min a 1 - min b 1| := abs_max_sub_max_le_max _ _ _ _
    _ ≤ |a - b| := by
      refine max_le (by simp) ?_
      calc
        |min a 1 - min b 1| ≤ max |a - b| |(1 : ℝ) - 1| :=
          abs_min_sub_min_le_max _ _ _ _
        _ = |a - b| := by simp

def rateFn (ℓ : Fin 1 → ℤ) (y : Fin 1 → ℝ) : ℝ :=
  if ℓ = up then clamp (1 - y 0) else if ℓ = down then clamp (y 0) else 0

theorem rateFn_nonneg (ℓ : Fin 1 → ℤ) (y : Fin 1 → ℝ) : 0 ≤ rateFn ℓ y := by
  unfold rateFn
  split_ifs
  · exact clamp_nonneg _
  · exact clamp_nonneg _
  · exact le_rfl

theorem rateFn_le_one (ℓ : Fin 1 → ℤ) (y : Fin 1 → ℝ) : rateFn ℓ y ≤ 1 := by
  unfold rateFn
  split_ifs
  · exact clamp_le_one _
  · exact clamp_le_one _
  · exact zero_le_one

theorem rateFn_lip (ℓ : Fin 1 → ℤ) (x y : Fin 1 → ℝ) :
    |rateFn ℓ x - rateFn ℓ y| ≤ |x 0 - y 0| := by
  unfold rateFn
  split_ifs
  · have h := clamp_lip (1 - x 0) (1 - y 0)
    have h2 : |(1 - x 0) - (1 - y 0)| = |x 0 - y 0| := by
      rw [show (1 - x 0) - (1 - y 0) = -(x 0 - y 0) by ring, abs_neg]
    linarith
  · exact clamp_lip _ _
  · simp

def Gamma : RateSpec 1 where
  jumps := {up, down}
  rate := rateFn
  rate_nonneg := fun ℓ _ y _ => rateFn_nonneg ℓ y
  rate_support := by
    intro ℓ hℓ
    funext y
    have h1 : ℓ ≠ up := fun h => hℓ (by simp [h])
    have h2 : ℓ ≠ down := fun h => hℓ (by simp [h])
    simp [rateFn, h1, h2]
  rate_lipschitz := by
    intro ℓ _ R _
    refine ⟨1, one_pos, ?_⟩
    intro x y _ _
    have hx : ‖(x - y) 0‖ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) 0
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hx
    rw [one_mul, Real.norm_eq_abs]
    exact (rateFn_lip ℓ x y).trans hx

def jumpOf : Bool → (Fin 1 → ℤ) := fun b => if b then up else down

theorem jumpOf_mem (b : Bool) : jumpOf b ∈ Gamma.jumps ∧ jumpOf b ≠ 0 := by
  cases b
  · simp [jumpOf, Gamma, down_ne_zero]
  · simp [jumpOf, Gamma, up_ne_zero]

def channelEquiv : Bool ≃ ListedNonzeroJump Gamma where
  toFun b := ⟨jumpOf b, jumpOf_mem b⟩
  invFun ℓ := decide (ℓ.1 = up)
  left_inv b := by
    cases b
    · simp [jumpOf, up_ne_down.symm]
    · simp [jumpOf]
  right_inv ℓ := by
    obtain ⟨ℓ, hℓ, _⟩ := ℓ
    have h : ℓ = up ∨ ℓ = down := by simpa [Gamma] using hℓ
    apply Subtype.ext
    rcases h with rfl | rfl
    · simp [jumpOf]
    · simp [jumpOf, up_ne_down.symm]

theorem boundary (n : ℕ) (hn : 0 < n) :
    (DensityDepCTMC.mk n hn Gamma).BoundaryCompatible := by
  intro x ℓ hℓ hno
  have h : ℓ = up ∨ ℓ = down := by simpa [Gamma] using hℓ
  have hx : (x 0 : ℕ) ≤ n := Nat.lt_succ_iff.mp (x 0).isLt
  rcases h with rfl | rfl
  · by_cases hlt : (x 0 : ℕ) < n
    · exfalso
      apply hno
      refine ⟨fun _ => ⟨(x 0 : ℕ) + 1, by show (x 0 : ℕ) + 1 < n + 1; omega⟩, ?_⟩
      intro i
      fin_cases i
      simp [up]
    · have hxn : (x 0 : ℕ) = n := le_antisymm hx (not_lt.mp hlt)
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      show rateFn up _ = 0
      simp [rateFn, clamp, DensityDepCTMC.scaledState, hxn, hnR]
  · by_cases hpos : 0 < (x 0 : ℕ)
    · exfalso
      apply hno
      refine ⟨fun _ => ⟨(x 0 : ℕ) - 1, by show (x 0 : ℕ) - 1 < n + 1; omega⟩, ?_⟩
      intro i
      fin_cases i
      simp [down]
      omega
    · have hx0 : (x 0 : ℕ) = 0 := by omega
      show rateFn down _ = 0
      simp [rateFn, clamp, DensityDepCTMC.scaledState, hx0, up_ne_down.symm]

theorem zero_jump : Gamma.rate (0 : Fin 1 → ℤ) = 0 := by
  show rateFn 0 = 0
  funext y
  simp [rateFn, up_ne_zero.symm, down_ne_zero.symm]

/-- the rate functions and jump vectors of the two channels -/
def beta : Bool → (Fin 1 → ℝ) → ℝ := fun b y => Gamma.rate (jumpOf b) y
def vec : Bool → Fin 1 → ℝ := fun b i => ((jumpOf b i : ℤ) : ℝ)
def bnd : Bool → ℝ := fun _ => 1

theorem beta_nonneg : ∀ (b : Bool) (y : Fin 1 → ℝ), 0 ≤ beta b y :=
  fun b y => rateFn_nonneg _ _
theorem beta_le : ∀ (b : Bool) (y : Fin 1 → ℝ), beta b y ≤ bnd b :=
  fun b y => rateFn_le_one _ _
theorem beta_meas : ∀ b : Bool, Measurable (beta b) := by
  intro b
  cases b
  · show Measurable fun y : Fin 1 → ℝ => rateFn down y
    have : (fun y : Fin 1 → ℝ => rateFn down y) = fun y => clamp (y 0) := by
      funext y
      simp [rateFn, up_ne_down.symm]
    rw [this]
    unfold clamp
    fun_prop
  · show Measurable fun y : Fin 1 → ℝ => rateFn up y
    have : (fun y : Fin 1 → ℝ => rateFn up y) = fun y => clamp (1 - y 0) := by
      funext y
      simp [rateFn]
    rw [this]
    unfold clamp
    fun_prop

/-- scale-`n` alignment with lattice start `⌊n/2⌋` -/
def perScale (n : ℕ) (hn : 0 < n) :
    PerScaleDensityChannelAlignment Gamma beta vec n hn :=
  PerScaleDensityChannelAlignment.ofLatticeStart channelEquiv
    (fun _ _ => rfl) (fun _ _ => rfl) (boundary n hn) zero_jump
    (fun _ => ⟨n / 2, by omega⟩)

def x0 : Fin 1 → ℝ := fun _ => 1 / 2

theorem round (n : ℕ) (hn : 0 < n) :
    ‖(DensityDepCTMC.mk n hn Gamma).scaledState (perScale n hn).latticeStart - x0‖ ≤
      (1 / 2 : ℝ) / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n 2).symm
  have hr1 : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
    exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt n two_pos)
  have hr0 : (0 : ℝ) ≤ ((n % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => ?_)
  have h1 : ((n / 2 : ℕ) : ℝ) / n - 1 / 2 = -(((n % 2 : ℕ) : ℝ) / (2 * n)) := by
    field_simp
    linarith
  have hval : ((DensityDepCTMC.mk n hn Gamma).scaledState
      (perScale n hn).latticeStart - x0) i = ((n / 2 : ℕ) : ℝ) / n - 1 / 2 := rfl
  rw [hval, Real.norm_eq_abs, h1, abs_neg, abs_of_nonneg (by positivity)]
  rw [show (1 / 2 : ℝ) / n = 1 / (2 * n) by field_simp]
  exact div_le_div_of_nonneg_right hr1 (by positivity)

/-- the drift is `2`-Lipschitz -/
theorem drift_lip (y z : Fin 1 → ℝ) :
    ‖tcDrift beta vec y - tcDrift beta vec z‖ ≤ 2 * ‖y - z‖ := by
  have hd : ∀ w : Fin 1 → ℝ, tcDrift beta vec w 0 = clamp (1 - w 0) - clamp (w 0) := by
    intro w
    simp [tcDrift, beta, vec, jumpOf, Gamma, rateFn, up, down, up_ne_down.symm,
      Fintype.sum_bool, sub_eq_add_neg]
  have hx : ‖(y - z) 0‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) 0
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hx
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => ?_)
  fin_cases i
  simp only [Fin.zero_eta, Pi.sub_apply, Real.norm_eq_abs]
  rw [hd y, hd z]
  have h1 := clamp_lip (1 - y 0) (1 - z 0)
  have h2 := clamp_lip (y 0) (z 0)
  have h3 : |(1 - y 0) - (1 - z 0)| = |y 0 - z 0| := by
    rw [show (1 - y 0) - (1 - z 0) = -(y 0 - z 0) by ring, abs_neg]
  have h4 : |(clamp (1 - y 0) - clamp (y 0)) - (clamp (1 - z 0) - clamp (z 0))| ≤
      |clamp (1 - y 0) - clamp (1 - z 0)| + |clamp (y 0) - clamp (z 0)| := by
    calc _ = |(clamp (1 - y 0) - clamp (1 - z 0)) - (clamp (y 0) - clamp (z 0))| := by ring_nf
      _ ≤ _ := abs_sub _ _
  linarith

/-- the constant `1/2` solves the drift integral equation from `1/2` -/
theorem drift_zero : tcDrift beta vec x0 = 0 := by
  funext i
  fin_cases i
  simp [tcDrift, beta, vec, jumpOf, Gamma, rateFn, up, down, up_ne_down.symm,
    Fintype.sum_bool, x0, clamp]
  norm_num


/-- the LIL error term of this model -/
theorem lilError_eq (n : ℕ) :
    SIPDensityPerScaleStart.densityLILError vec bnd 1 n =
      2 * (n : ℝ)⁻¹ * envelope (n : ℝ) := by
  unfold SIPDensityPerScaleStart.densityLILError
  have hnorm : ∀ f : Fin 1 → ℝ, ‖f‖ = |f 0| := by
    intro f
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
        (fun i => by fin_cases i; simp)
    · simpa using norm_le_pi_norm f 0
  have hv : ∀ b : Bool, ‖vec b‖ = 1 := by
    intro b
    rw [hnorm]
    cases b <;> simp [vec, jumpOf, up, down]
  simp [hv, bnd] <;> ring

open PoissonDriverFamily CellRecordTimeCoverage SIPDensityCellRecordPerScaleAE in
/-- **End-to-end instance.**  Concrete driver, birth/death model, constant ODE
solution `x ≡ 1/2`, lattice starts `⌊n/2⌋`:  almost surely, for all large `n` and
all `t ∈ [0,1]`, the SIP time-change path is within
`exp 2 * (1/(2n) + (2/n) * envelope n)` of `1/2`. -/
theorem concrete_bound :
    ∀ᵐ omega ∂familyMeasure Bool driverMeasure,
      ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖namedPoissonTimeChange (N := canonicalCount)
            beta vec bnd beta_nonneg beta_le beta_meas
            ((familyOfAlignments beta_nonneg beta_le beta_meas
              (fun n hn => perScale n hn)).startDensity n) n omega t - x0‖ ≤
          Real.exp (2 * 1) * ((1 / 2 : ℝ) / n + 2 * (n : ℝ)⁻¹ * envelope (n : ℝ)) := by
  have hmain := sip_density_strong_approximation_of_alignments
    (Gamma := Gamma) (N := canonicalCount) (P := driverMeasure)
    beta_nonneg beta_le beta_meas (fun n hn => perScale n hn)
    driver_measurable driver_indep driver_law
    (L := 2) (by norm_num) drift_lip (T := 1) (by norm_num)
    (x := fun _ : ℝ => x0) (xZero := x0)
    continuousOn_const
    (by
      intro t _
      simp [drift_zero])
  filter_upwards [hmain.2] with omega homega
  filter_upwards [homega, Filter.eventually_gt_atTop 0] with n hn' hn
  intro t ht
  have hstart :
      ‖(familyOfAlignments beta_nonneg beta_le beta_meas
          (fun n hn => perScale n hn)).startDensity n - x0‖ ≤
        (1 / 2 : ℝ) / n := by
    rw [AEDensitySIPCellRecordFamily.startDensity_eq_scaledState _ hn]
    exact round n hn
  have hb := hn' t ht
  rw [lilError_eq] at hb
  have hsum := add_le_add_left hstart (2 * (n : ℝ)⁻¹ * envelope (n : ℝ))
  calc _ ≤ _ := hb
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      linarith

end BirthDeathSIP

#print axioms BirthDeathSIP.concrete_bound
#print axioms PoissonDriverFamily.driver_indep
#check @BirthDeathSIP.concrete_bound
