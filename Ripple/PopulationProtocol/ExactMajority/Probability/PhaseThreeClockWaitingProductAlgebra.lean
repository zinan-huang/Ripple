-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockWaitingProductAlgebra.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3Scalar
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

noncomputable section

open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockWaitingProductAlgebra

def waitingStep (delta p : ℝ) : ℝ := 1 - delta / p

def geometricFactor (delta p : ℝ) : ℝ := (waitingStep delta p)⁻¹

def waitingProduct (p : ℕ → ℝ) (delta : ℝ) (r K : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico r K, geometricFactor delta (p j)

def survivalProduct (p : ℕ → ℝ) (delta : ℝ) (r a : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico r a, waitingStep delta (p j)

def survivalWeight (p : ℕ → ℝ) (delta : ℝ) (r K a : ℕ) : ℝ :=
  if a < K then survivalProduct p delta r a else 0

theorem waitingStep_bounds (delta p : ℝ) (hd : 0 ≤ delta)
    (hp : 0 < p) (hsmall : delta < p) :
    0 < waitingStep delta p ∧ waitingStep delta p ≤ 1 := by
  have hdiv : 0 ≤ delta / p := div_nonneg hd hp.le
  have hlt : delta / p < 1 := (div_lt_one hp).mpr hsmall
  unfold waitingStep
  constructor <;> linarith

theorem geometricFactor_ge_one (delta p : ℝ) (hd : 0 ≤ delta)
    (hp : 0 < p) (hsmall : delta < p) :
    1 ≤ geometricFactor delta p := by
  have h := waitingStep_bounds delta p hd hp hsmall
  have hi : (1 : ℝ) ≤ 1 / waitingStep delta p :=
    (le_div_iff₀ h.1).mpr (by simpa using h.2)
  simpa only [geometricFactor, one_div] using hi

theorem geometricFactor_eq (delta p : ℝ) (hp : p ≠ 0) :
    geometricFactor delta p = p / (p - delta) := by
  have h : 1 - delta / p = (p - delta) / p := by
    field_simp [hp]
    <;> ring
  unfold geometricFactor waitingStep
  rw [h, inv_div]

theorem geometricFactor_waiting_equation (delta p : ℝ)
    (hp : 0 < p) (hsmall : delta < p) :
    (1 - delta) * geometricFactor delta p =
      p + (1 - p) * geometricFactor delta p := by
  rw [geometricFactor_eq delta p (ne_of_gt hp)]
  field_simp [ne_of_gt (sub_pos.mpr hsmall)]
  <;> ring

theorem waitingProduct_eq_inv (p : ℕ → ℝ) (delta : ℝ) (r K : ℕ) :
    waitingProduct p delta r K = (survivalProduct p delta r K)⁻¹ := by
  simp only [waitingProduct, survivalProduct, geometricFactor, Finset.prod_inv_distrib]

theorem waitingProduct_ge_one (p : ℕ → ℝ) (delta : ℝ) (r K : ℕ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j) :
    1 ≤ waitingProduct p delta r K :=
  Finset.one_le_prod (fun j hj => geometricFactor_ge_one delta (p j) hd (hp j hj) (hsmall j hj))

theorem survivalProduct_pos (p : ℕ → ℝ) (delta : ℝ) (r K : ℕ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j) :
    0 < survivalProduct p delta r K :=
  Finset.prod_pos (fun j hj => (waitingStep_bounds delta (p j) hd (hp j hj) (hsmall j hj)).1)

theorem survivalWeight_bounds (p : ℕ → ℝ) (delta : ℝ) (r K a : ℕ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j)
    (hra : r ≤ a) :
    0 ≤ survivalWeight p delta r K a ∧ survivalWeight p delta r K a ≤ 1 := by
  by_cases ha : a < K
  · have hf (j : ℕ) (hj : j ∈ Finset.Ico r a) :
        0 < waitingStep delta (p j) ∧ waitingStep delta (p j) ≤ 1 :=
      waitingStep_bounds delta (p j) hd
        (hp j (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
          (Finset.mem_Ico.mp hj).2.trans ha⟩))
        (hsmall j (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
          (Finset.mem_Ico.mp hj).2.trans ha⟩))
    simp only [survivalWeight, if_pos ha, survivalProduct]
    exact ⟨Finset.prod_nonneg (fun j hj => (hf j hj).1.le),
      Finset.prod_le_one (fun j hj => (hf j hj).1.le) (fun j hj => (hf j hj).2)⟩
  · simp only [survivalWeight, if_neg ha, le_refl, zero_le_one, and_self]

theorem survivalWeight_antitone (p : ℕ → ℝ) (delta : ℝ) (r K a b : ℕ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j)
    (hra : r ≤ a) (hab : a ≤ b) :
    survivalWeight p delta r K b ≤ survivalWeight p delta r K a := by
  by_cases hb : b < K
  · have ha : a < K := hab.trans_lt hb
    have hsub : Finset.Ico r a ⊆ Finset.Ico r b := by
      intro j hj
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
        (Finset.mem_Ico.mp hj).2.trans_le hab⟩
    have hf (j : ℕ) (hj : j ∈ Finset.Ico r b) :
        0 < waitingStep delta (p j) ∧ waitingStep delta (p j) ≤ 1 :=
      waitingStep_bounds delta (p j) hd
        (hp j (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
          (Finset.mem_Ico.mp hj).2.trans hb⟩))
        (hsmall j (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
          (Finset.mem_Ico.mp hj).2.trans hb⟩))
    simp only [survivalWeight, if_pos ha, if_pos hb, survivalProduct]
    exact Finset.prod_le_prod_of_subset_of_le_one hsub
      (fun j hj => (hf j hj).1.le) (fun j hj _ => (hf j hj).2)
  · rw [survivalWeight, if_neg hb]
    exact (survivalWeight_bounds p delta r K a hd hp hsmall hra).1

theorem survivalWeight_succ_le (p : ℕ → ℝ) (delta : ℝ) (r K a : ℕ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j)
    (hra : r ≤ a) (ha : a < K) :
    survivalWeight p delta r K (a + 1) ≤
      waitingStep delta (p a) * survivalWeight p delta r K a := by
  have haI : a ∈ Finset.Ico r K := Finset.mem_Ico.mpr ⟨hra, ha⟩
  by_cases hs : a + 1 < K
  · simp only [survivalWeight, if_pos ha, if_pos hs, survivalProduct,
      Finset.prod_Ico_succ_top hra]
    exact le_of_eq (mul_comm _ _)
  · rw [survivalWeight, if_neg hs]
    exact mul_nonneg (waitingStep_bounds delta (p a) hd (hp a haI) (hsmall a haI)).1.le
      (survivalWeight_bounds p delta r K a hd hp hsmall hra).1

theorem survivalWeight_loss_bounds (p : ℕ → ℝ) (delta : ℝ) (r K a : ℕ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j)
    (hra : r ≤ a) :
    0 ≤ (delta / p a) * survivalWeight p delta r K a ∧
      (delta / p a) * survivalWeight p delta r K a ≤ 1 := by
  by_cases ha : a < K
  · have haI : a ∈ Finset.Ico r K := Finset.mem_Ico.mpr ⟨hra, ha⟩
    have hq : 0 ≤ delta / p a := div_nonneg hd (hp a haI).le
    have hqone : delta / p a ≤ 1 := ((div_lt_one (hp a haI)).mpr (hsmall a haI)).le
    have hw := survivalWeight_bounds p delta r K a hd hp hsmall hra
    exact ⟨mul_nonneg hq hw.1, (mul_le_mul_of_nonneg_right hqone hw.1).trans (by simpa using hw.2)⟩
  · simp only [survivalWeight, if_neg ha, mul_zero, le_refl, zero_le_one, and_self]

theorem survivalWeight_step (p : ℕ → ℝ) (delta : ℝ) (r K a b : ℕ) (I : ℝ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j)
    (hra : r ≤ a) (hab : a ≤ b)
    (hI : I = 0 ∨ I = 1) (hinc : I ≤ (b : ℝ) - (a : ℝ)) :
    survivalWeight p delta r K b ≤
      survivalWeight p delta r K a -
        ((delta / p a) * survivalWeight p delta r K a) * I := by
  by_cases ha : a < K
  · rcases hI with rfl | rfl
    · simpa only [mul_zero, sub_zero] using
        survivalWeight_antitone p delta r K a b hd hp hsmall hra hab
    · have hab' : a + 1 ≤ b := by
        have hc : (a : ℝ) + 1 ≤ (b : ℝ) := by linarith
        exact_mod_cast hc
      calc
        survivalWeight p delta r K b ≤ survivalWeight p delta r K (a + 1) :=
          survivalWeight_antitone p delta r K (a + 1) b hd hp hsmall (by omega) hab'
        _ ≤ waitingStep delta (p a) * survivalWeight p delta r K a :=
          survivalWeight_succ_le p delta r K a hd hp hsmall hra ha
        _ = _ := by unfold waitingStep; ring
  · have hb : ¬ b < K := by omega
    simp only [survivalWeight, if_neg ha, if_neg hb, mul_zero, zero_mul, sub_zero, le_refl]

theorem survivalWeight_survival_lower (p : ℕ → ℝ) (delta : ℝ) (r K a : ℕ)
    (hd : 0 ≤ delta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, delta < p j)
    (hra : r ≤ a) (ha : a < K) :
    1 ≤ waitingProduct p delta r K * survivalWeight p delta r K a := by
  have hprod : 0 < survivalProduct p delta r K :=
    survivalProduct_pos p delta r K hd hp hsmall
  have hsub : Finset.Ico r a ⊆ Finset.Ico r K := by
    intro j hj
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
      (Finset.mem_Ico.mp hj).2.trans ha⟩
  have hle : survivalProduct p delta r K ≤ survivalProduct p delta r a :=
    Finset.prod_le_prod_of_subset_of_le_one hsub
      (fun j hj => (waitingStep_bounds delta (p j) hd (hp j hj) (hsmall j hj)).1.le)
      (fun j hj _ => (waitingStep_bounds delta (p j) hd (hp j hj) (hsmall j hj)).2)
  rw [waitingProduct_eq_inv, survivalWeight, if_pos ha]
  calc
    1 = (survivalProduct p delta r K)⁻¹ * survivalProduct p delta r K :=
      (inv_mul_cancel₀ (ne_of_gt hprod)).symm
    _ ≤ (survivalProduct p delta r K)⁻¹ * survivalProduct p delta r a :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hprod.le)

theorem exponential_delta_bounds (theta : ℝ) (htheta : 0 ≤ theta) :
    0 ≤ 1 - Real.exp (-theta) ∧ 1 - Real.exp (-theta) ≤ theta := by
  have he : Real.exp (-theta) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hl := Real.add_one_le_exp (-theta)
  constructor <;> linarith

theorem exponential_delta_lt_rate (theta p : ℝ)
    (htheta : 0 ≤ theta) (hp : 0 < p) (hsmall : theta / p ≤ 1 / 1000) :
    1 - Real.exp (-theta) < p := by
  have ht : theta ≤ (1 / 1000 : ℝ) * p := (div_le_iff₀ hp).mp hsmall
  have hd := (exponential_delta_bounds theta htheta).2
  linarith

theorem geometricFactor_le_exp (theta p : ℝ)
    (htheta : 0 ≤ theta) (hp : 0 < p) (hsmall : theta / p ≤ 1 / 1000) :
    geometricFactor (1 - Real.exp (-theta)) p ≤
      Real.exp ((1000 / 999 : ℝ) * (theta / p)) := by
  let x : ℝ := (1 - Real.exp (-theta)) / p
  have hx : 0 ≤ x := div_nonneg (exponential_delta_bounds theta htheta).1 hp.le
  have hxt : x ≤ theta / p :=
    div_le_div_of_nonneg_right (exponential_delta_bounds theta htheta).2 hp.le
  have hxsmall : x ≤ (1 / 1000 : ℝ) := hxt.trans hsmall
  have hden : 0 < 1 - x := by linarith
  have hdenlower : (999 / 1000 : ℝ) ≤ 1 - x := by linarith
  have hinv : 0 < (1 - x)⁻¹ := inv_pos.mpr hden
  have hlog := Real.log_le_sub_one_of_pos hinv
  have hid : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp [ne_of_gt hden]
    <;> ring
  have hfrac : x / (1 - x) ≤ (1000 / 999 : ℝ) * (theta / p) := by
    calc
      x / (1 - x) ≤ x / (999 / 1000 : ℝ) :=
        div_le_div_of_nonneg_left hx (by norm_num) hdenlower
      _ = (1000 / 999 : ℝ) * x := by ring
      _ ≤ (1000 / 999 : ℝ) * (theta / p) :=
        mul_le_mul_of_nonneg_left hxt (by norm_num)
  apply (Real.log_le_iff_le_exp hinv).mp
  exact hlog.trans (by rw [hid]; exact hfrac)

theorem waitingProduct_le_exp (p : ℕ → ℝ) (theta : ℝ) (r K : ℕ)
    (htheta : 0 ≤ theta)
    (hp : ∀ j ∈ Finset.Ico r K, 0 < p j)
    (hsmall : ∀ j ∈ Finset.Ico r K, theta / p j ≤ 1 / 1000) :
    waitingProduct p (1 - Real.exp (-theta)) r K ≤
      Real.exp ((1000 / 999 : ℝ) * theta *
        (∑ j ∈ Finset.Ico r K, 1 / p j)) := by
  have hd := (exponential_delta_bounds theta htheta).1
  have hlt (j : ℕ) (hj : j ∈ Finset.Ico r K) :
      1 - Real.exp (-theta) < p j :=
    exponential_delta_lt_rate theta (p j) htheta (hp j hj) (hsmall j hj)
  calc
    waitingProduct p (1 - Real.exp (-theta)) r K ≤
        ∏ j ∈ Finset.Ico r K, Real.exp ((1000 / 999 : ℝ) * (theta / p j)) :=
      Finset.prod_le_prod
        (fun j hj => (zero_le_one.trans (geometricFactor_ge_one _ _ hd (hp j hj) (hlt j hj))))
        (fun j hj => geometricFactor_le_exp theta (p j) htheta (hp j hj) (hsmall j hj))
    _ = Real.exp (∑ j ∈ Finset.Ico r K, (1000 / 999 : ℝ) * (theta / p j)) := by
      rw [Real.exp_sum]
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockWaitingProductAlgebra

end
