-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockSquaringCollapse.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkedShape

/-! Deterministic repeated-squaring step in P6, with its actual rounded width. -/
noncomputable section
open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSquaringCollapse

open PhaseThreeModel.Numeric PhaseThreeClockMarkedShape

theorem squaring_chain_bound (z : ℕ → ℝ) (r : ℝ) (d : ℕ)
    (hz : ∀ j, 0 ≤ z j) (hr : 0 ≤ r) (hstart : z 0 ≤ r)
    (hstep : ∀ j, j < d → z (j + 1) ≤ (z j) ^ 2) :
    z d ≤ r ^ (2 ^ d) := by
  have hbound : ∀ j, j ≤ d → z j ≤ r ^ (2 ^ j) := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa only [pow_zero, pow_one] using hstart
    | succ j ih =>
        intro hj
        calc
          z (j + 1) ≤ (z j) ^ 2 := hstep j (by omega)
          _ ≤ (r ^ (2 ^ j)) ^ 2 :=
            pow_le_pow_left₀ (hz j) (ih (by omega)) 2
          _ = r ^ (2 ^ (j + 1)) := by
            rw [← pow_mul, pow_succ]
  exact hbound d le_rfl

theorem frontWidth_exp_lower (C : ℕ)
    (hx : 4194304 ≤ Real.log (C : ℝ)) :
    Real.log (C : ℝ) ≤ (2 : ℝ) ^ frontWidth C := by
  have hxpos : 0 < Real.log (C : ℝ) := by linarith
  have hlpos : 0 < Real.log (2 : ℝ) := by
    linarith [log_two_bounds.1]
  have hceil := Nat.le_ceil (Real.logb 2 (Real.log (C : ℝ)))
  have hdiv : Real.log (Real.log (C : ℝ)) / Real.log 2 ≤ (frontWidth C : ℝ) := by
    change Real.log (Real.log (C : ℝ)) / Real.log 2 ≤
      ((Nat.ceil (Real.logb 2 (Real.log (C : ℝ))) + 16 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_ofNat]
    have hceil' : Real.log (Real.log (C : ℝ)) / Real.log 2 ≤
        (Nat.ceil (Real.logb 2 (Real.log (C : ℝ))) : ℝ) := hceil
    linarith
  have hlog : Real.log (Real.log (C : ℝ)) ≤
      Real.log ((2 : ℝ) ^ frontWidth C) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ hlpos).mp hdiv
  have he := Real.exp_le_exp.mpr hlog
  simpa only [Real.exp_log hxpos,
    Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) (frontWidth C))] using he

theorem repeated_square_below_cutoff (C : ℕ)
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ)) :
    (101 / 1000 : ℝ) ^ (2 ^ frontWidth C) <
      (C : ℝ) ^ (-(8 / 25 : ℝ)) := by
  let d := frontWidth C
  have hxpos : 0 < Real.log (C : ℝ) := by linarith
  have hsize : Real.log (C : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, d] using frontWidth_exp_lower C hx
  have hprod := mul_le_mul_of_nonneg_left log_two_bounds.1
    (show (0 : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) by positivity)
  have hexp : -((2 ^ d : ℕ) : ℝ) * Real.log 2 <
      Real.log (C : ℝ) * (-(8 / 25 : ℝ)) := by
    nlinarith only [hxpos, hsize, hprod]
  have hid : (1 / 2 : ℝ) ^ (2 ^ d) =
      Real.exp (-((2 ^ d : ℕ) : ℝ) * Real.log 2) := by
    calc
      _ = Real.exp (Real.log ((1 / 2 : ℝ) ^ (2 ^ d))) :=
        (Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)).symm
      _ = _ := by
        rw [Real.log_pow, Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
          (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
        congr 1
        ring
  calc
    (101 / 1000 : ℝ) ^ (2 ^ frontWidth C) ≤
        (1 / 2 : ℝ) ^ (2 ^ d) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = Real.exp (-((2 ^ d : ℕ) : ℝ) * Real.log 2) := hid
    _ < Real.exp (Real.log (C : ℝ) * (-(8 / 25 : ℝ))) :=
      Real.exp_lt_exp.mpr hexp
    _ = _ := (Real.rpow_def_of_pos hC _).symm

theorem shapeCutoff_ratio_lower (C : ℕ) (hC : 0 < (C : ℝ)) :
    (C : ℝ) ^ (-(8 / 25 : ℝ)) ≤ (shapeCutoff C : ℝ) / C := by
  have hc : (C : ℝ) ^ (17 / 25 : ℝ) ≤ (shapeCutoff C : ℝ) := Nat.le_ceil _
  have hid : (C : ℝ) ^ (17 / 25 : ℝ) / C =
      (C : ℝ) ^ (-(8 / 25 : ℝ)) := by
    calc
      _ = (C : ℝ) ^ ((-(8 / 25 : ℝ)) + 1) / C := by norm_num
      _ = ((C : ℝ) ^ (-(8 / 25 : ℝ)) * C) / C := by
        rw [Real.rpow_add hC, Real.rpow_one]
      _ = _ := mul_div_cancel_right₀ _ hC.ne'
  simpa only [hid] using div_le_div_of_nonneg_right hc hC.le

theorem normalized_shape (C X Y : ℕ) (hC : 0 < (C : ℝ))
    (hshape : C * Y ≤ X ^ 2) :
    (Y : ℝ) / C ≤ ((X : ℝ) / C) ^ 2 := by
  have hnat : (C : ℝ) * Y ≤ (X : ℝ) ^ 2 := by exact_mod_cast hshape
  have hY : (Y : ℝ) ≤ (X : ℝ) ^ 2 / C := by
    apply (le_div_iff₀ hC).mpr
    nlinarith only [hnat]
  calc
    (Y : ℝ) / C ≤ ((X : ℝ) ^ 2 / C) / C :=
      div_le_div_of_nonneg_right hY hC.le
    _ = ((X : ℝ) / C) ^ 2 := by field_simp [hC.ne'] <;> ring

/-- If all d intermediate earlier shape assertions hold, a w-sized
front at j+d forces the j-front to have reached the bulk threshold. -/
theorem bulk_of_sublinear_front_and_shapes (C j : ℕ) (X : ℕ → ℕ)
    (hC : 0 < (C : ℝ)) (hx : 4194304 ≤ Real.log (C : ℝ))
    (hanti : Antitone X)
    (hhigh : shapeCutoff C ≤ X (j + frontWidth C))
    (hshape : ∀ ell, j ≤ ell → ell < j + frontWidth C →
      shapeCutoff C ≤ X ell → X ell ≤ StageEventSpec.bulkThreshold C →
      C * X (ell + 1) ≤ X ell ^ 2) :
    StageEventSpec.bulkThreshold C ≤ X j := by
  by_contra hnot
  have hbelow : X j < StageEventSpec.bulkThreshold C := by omega
  have hbig : (1000 : ℝ) ≤ C := by
    have he := Real.add_one_le_exp (Real.log (C : ℝ))
    rw [Real.exp_log hC] at he
    linarith
  let z : ℕ → ℝ := fun t => (X (j + t) : ℝ) / C
  have hstart : z 0 ≤ (101 / 1000 : ℝ) := by
    simpa only [z, Nat.add_zero] using bulk_ratio_le_barrier C (X j) hbig hbelow.le
  have hstep : ∀ t, t < frontWidth C → z (t + 1) ≤ (z t) ^ 2 := by
    intro t ht
    have hlow : shapeCutoff C ≤ X (j + t) :=
      hhigh.trans (hanti (by omega : j + t ≤ j + frontWidth C))
    have hupp : X (j + t) ≤ StageEventSpec.bulkThreshold C :=
      (hanti (by omega : j ≤ j + t)).trans hbelow.le
    have hs := hshape (j + t) (by omega) (by omega) hlow hupp
    simpa only [z, Nat.add_assoc] using normalized_shape C (X (j + t))
      (X (j + t + 1)) hC hs
  have hbound := squaring_chain_bound z (101 / 1000 : ℝ) (frontWidth C)
    (fun t => div_nonneg (Nat.cast_nonneg _) hC.le) (by norm_num) hstart hstep
  have hlower : (C : ℝ) ^ (-(8 / 25 : ℝ)) ≤ z (frontWidth C) :=
    (shapeCutoff_ratio_lower C hC).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hhigh) hC.le)
  exact (not_lt_of_ge hlower)
    (hbound.trans_lt (repeated_square_below_cutoff C hC hx))

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockSquaringCollapse

end
