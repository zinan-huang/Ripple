/-
  Kernel-verified analytical coefficient majorant bound for the CRT proof.

  Architecture (zero native_decide):

  Layer 1: Majorant algebra — Maj f F closed under conv, pow, pullback, sparse sum
  Layer 2: Eisenstein/Δ bounds — |E4[n]| ≤ G4[n], |E6[n]| ≤ G6[n], |Δ[n]| ≤ DeltaBound[n]
  Layer 3: Row bridge — Q_j recurrence = Δ^(42-j) · E4^(3j) closed form, row bounds
  Layer 4: Final hbound — sparse L¹ convolution → B ≈ H · 10^1420

  Key insight: the recurrence for Q_j is NOT an arbitrary recurrence — it is the
  coefficient recurrence for Q_j(q) = Δ(q)^(42-j) · E4(q)^(3j). The derivative
  identity E4 · D Q_j = (42 E2E4 - j E6) · Q_j (already proved) establishes this.
  Bounding the closed form via majorants avoids the exponential blowup from
  taking absolute values in the recurrence.
-/
import Ripple.Number.Modular.ModularPolynomialSturmCertificate
import Ripple.Number.Modular.SturmCRTBoundCert
import Ripple.Number.Modular.LevelOneSturmGeneric
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace Ripple.Number.Modular

open scoped MatrixGroups
open scoped UpperHalfPlane
open CongruenceSubgroup

/-! ## Layer 1: Majorant Algebra -/

/-- Coefficientwise majorization: |f(n)| ≤ F(n) for all n. -/
def Maj (f : ℕ → ℤ) (F : ℕ → ℕ) : Prop :=
  ∀ n, |f n| ≤ (F n : ℤ)

/-- Convolution of nonneg sequences. -/
def convNat (F G : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum (fun k => F k * G (n - k))

theorem Maj.conv {f g : ℕ → ℤ} {F G : ℕ → ℕ}
    (hf : Maj f F) (hg : Maj g G) :
    Maj (fun n => (Finset.range (n + 1)).sum (fun k => f k * g (n - k)))
      (convNat F G) := by
  intro n; simp only [convNat]
  calc |∑ k ∈ Finset.range (n + 1), f k * g (n - k)|
      ≤ ∑ k ∈ Finset.range (n + 1), |f k * g (n - k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (F k * G (n - k) : ℤ) := by
        apply Finset.sum_le_sum; intro k _
        rw [abs_mul]
        exact mul_le_mul (hf k) (hg (n - k)) (abs_nonneg _) (Int.natCast_nonneg _)
    _ = ↑(∑ k ∈ Finset.range (n + 1), F k * G (n - k)) := by push_cast; ring_nf

/-- Majorant of n-fold convolution power. -/
def powConvNat (F : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  match k with
  | 0 => fun n => if n = 0 then 1 else 0
  | k + 1 => convNat F (powConvNat F k)

theorem Maj.powConv {f : ℕ → ℤ} {F : ℕ → ℕ} (hf : Maj f F)
    (k : ℕ) :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n ((PowerSeries.mk f) ^ k))
      (powConvNat F k) := by
  induction k with
  | zero =>
    intro n; simp only [pow_zero, PowerSeries.coeff_one, powConvNat]; split <;> simp
  | succ k ih =>
    show Maj _ (convNat F (powConvNat F k))
    intro n; dsimp only
    rw [pow_succ', PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp_rw [PowerSeries.coeff_mk]
    exact Maj.conv hf ih n

theorem Maj.add {f g : ℕ → ℤ} {F G : ℕ → ℕ}
    (hf : Maj f F) (hg : Maj g G) :
    Maj (fun n => f n + g n) (fun n => F n + G n) := by
  intro n; push_cast
  calc |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ ↑(F n) + ↑(G n) := add_le_add (hf n) (hg n)

theorem Maj.smul {f : ℕ → ℤ} {F : ℕ → ℕ} (c : ℤ)
    (hf : Maj f F) :
    Maj (fun n => c * f n) (fun n => c.natAbs * F n) := by
  intro n
  rw [abs_mul]
  push_cast
  rw [Int.abs_eq_natAbs]
  exact mul_le_mul_of_nonneg_left (hf n) (by positivity)

/-- Majorant for q-pullback by 41: f(q^41). -/
def pullback41Nat (F : ℕ → ℕ) (n : ℕ) : ℕ :=
  if 41 ∣ n then F (n / 41) else 0

theorem Maj.pullback41 {f : ℕ → ℤ} {F : ℕ → ℕ} (hf : Maj f F) :
    Maj (fun n => if 41 ∣ n then f (n / 41) else 0) (pullback41Nat F) := by
  intro n; simp only [pullback41Nat]
  split
  · exact hf _
  · simp

/-! ## Layer 2: Eisenstein and Δ coefficient bounds -/

/-- G4 majorant: |E4[n]| ≤ G4Bound n.
    Uses 2880 · C(n+2, 3) ≥ 480 n³ ≥ 240 σ₃(n). -/
def G4Bound (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2880 * Nat.choose (n + 2) 3

/-- G6 majorant: |E6[n]| ≤ G6Bound n.
    Uses 120960 · C(n+4, 5) ≥ 1008 n⁵ ≥ 504 σ₅(n). -/
def G6Bound (n : ℕ) : ℕ :=
  if n = 0 then 1 else 120960 * Nat.choose (n + 4) 5

/-! ### σ₃(n) ≤ 2n³: proof via ℚ telescoping

Strategy: cast to ℚ. Split σ₃(n) = n³ + Σ_{properDiv} d³.
For each d ∈ properDivisors, we have n/d ≥ 2 and d·(n/d) = n,
so (d:ℚ)³ = (n:ℚ)³/(n/d:ℚ)³. Bound 1/e³ ≤ 1/(e(e-1))
and use telescoping: Σ_{e ∈ S, e ≥ 2} 1/(e(e-1)) ≤ 1. -/

/-- Telescoping bound: Σ_{e=2}^{M} 1/(e(e-1)) = 1 - 1/M in ℚ. -/
private lemma sum_Icc_inv_pred_mul (M : ℕ) (hM : 2 ≤ M) :
    (Finset.Icc 2 M).sum (fun e => (1 : ℚ) / ((e : ℚ) * ((e : ℚ) - 1))) =
      1 - 1 / (M : ℚ) := by
  induction M with
  | zero => omega
  | succ M ih =>
    by_cases hM2 : M + 1 = 2
    · -- Base case: M+1 = 2, so M = 1
      have : M = 1 := by omega
      subst this; simp [Finset.Icc_self]; ring
    · -- Inductive step: M+1 ≥ 3, so M ≥ 2
      have hM1 : 2 ≤ M := by omega
      -- Icc 2 (M+1) = insert (M+1) (Icc 2 M)
      have hIcc : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
        ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc])]
      rw [ih hM1]
      -- Now goal: 1/((M+1)*((M+1)-1)) + (1 - 1/M) = 1 - 1/(M+1)
      have hMne : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hM1ne : ((M : ℚ) + 1) ≠ 0 := by positivity
      -- Simplify (M+1)-1 = M in ℚ
      have hsimp : ((M + 1 : ℕ) : ℚ) - 1 = (M : ℚ) := by push_cast; ring
      rw [hsimp]
      -- Now goal: 1/((M+1)*M) + (1 - 1/M) = 1 - 1/(M+1)
      -- i.e. 1/((M+1)*M) = 1/M - 1/(M+1) (partial fractions)
      -- The Nat.cast of (M+1) needs to be rewritten
      have hcast : ((M + 1 : ℕ) : ℚ) = (M : ℚ) + 1 := by push_cast; ring
      rw [hcast]
      rw [show (1 : ℚ) / (((M : ℚ) + 1) * (M : ℚ)) = 1 / (M : ℚ) - 1 / ((M : ℚ) + 1) from by
        rw [div_sub_div _ _ hMne hM1ne, mul_comm]; congr 1; ring]
      ring

/-- For each d ∈ properDivisors n: d³ ≤ n³ · 1/((n/d)(n/d - 1)) in ℚ. -/
private lemma proper_div_cube_le_inv_pred (n d : ℕ) (hn : 0 < n)
    (hd : d ∈ n.properDivisors) :
    (d : ℚ) ^ 3 ≤ (n : ℚ) ^ 3 * ((1 : ℚ) / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
  have hdvd := (Nat.mem_properDivisors.mp hd).1
  have hlt := (Nat.mem_properDivisors.mp hd).2
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hd)
  set e := n / d
  have he : 2 ≤ e := Nat.one_lt_div_of_mem_properDivisors hd
  have hde : d * e = n := by
    show d * (n / d) = n
    rw [mul_comm]; exact Nat.div_mul_cancel hdvd
  -- In ℚ: d = n/e, so d³ = n³/e³.
  -- We need: n³/e³ ≤ n³/(e(e-1)), i.e., e(e-1) ≤ e³, i.e., e-1 ≤ e², true.
  have he_pos : (0 : ℚ) < (e : ℚ) := by positivity
  have he1_pos : (0 : ℚ) < ((e : ℚ) - 1) := by
    have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
    linarith
  have hdQ : (d : ℚ) = (n : ℚ) / (e : ℚ) := by
    rw [eq_div_iff (ne_of_gt he_pos)]
    exact_mod_cast hde
  rw [hdQ, div_pow, mul_one_div]
  -- Goal: n^3 / e^3 ≤ n^3 / (e * (e - 1))
  -- Since e*(e-1) ≤ e^3 and e*(e-1) > 0:
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos he_pos he1_pos) (by nlinarith [sq_nonneg ((e : ℚ) - 1)])

/-- The Finset image of n/· on properDivisors maps into Icc 2 n. -/
private lemma div_properDivisors_subset_Icc (n : ℕ) (_hn : 0 < n) :
    (n.properDivisors.image (n / ·)) ⊆ Finset.Icc 2 n := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨d, hd, rfl⟩ := he
  rw [Finset.mem_Icc]
  exact ⟨Nat.one_lt_div_of_mem_properDivisors hd,
         Nat.div_le_self n d⟩

private lemma sigma3_le_two_mul_cube (n : ℕ) (hn : 0 < n) :
    ArithmeticFunction.sigma 3 n ≤ 2 * n ^ 3 := by
  -- Cast to ℚ
  suffices h : (ArithmeticFunction.sigma 3 n : ℚ) ≤ 2 * (n : ℚ) ^ 3 by exact_mod_cast h
  -- Rewrite sigma as a sum over divisors
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  -- Split: divisors n = {n} ∪ properDivisors n
  have hne : n ≠ 0 := by omega
  rw [← Nat.cons_self_properDivisors hne, Finset.sum_cons]
  -- Goal: n^3 + Σ_{d ∈ properDiv} d^3 ≤ 2*n^3
  -- Suffices: Σ_{d ∈ properDiv} d^3 ≤ n^3
  suffices hpd : (n.properDivisors.sum fun d => (d : ℚ) ^ 3) ≤ (n : ℚ) ^ 3 by linarith
  -- Bound each d^3 by n^3 * 1/(e*(e-1)) where e = n/d
  calc n.properDivisors.sum (fun d => (d : ℚ) ^ 3)
      ≤ n.properDivisors.sum (fun d =>
          (n : ℚ) ^ 3 * (1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1)))) := by
        apply Finset.sum_le_sum
        intro d hd
        exact proper_div_cube_le_inv_pred n d hn hd
    _ = (n : ℚ) ^ 3 * n.properDivisors.sum (fun d =>
          1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
        rw [← Finset.mul_sum]
    _ ≤ (n : ℚ) ^ 3 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- Step 1: The map d ↦ n/d is injective on properDivisors
        have hinj : ∀ a ∈ n.properDivisors, ∀ b ∈ n.properDivisors,
            n / a = n / b → a = b := by
          intro a ha b hb hab
          have ha' := (Nat.mem_properDivisors.mp ha).1
          have hb' := (Nat.mem_properDivisors.mp hb).1
          have ha_pos : 0 < a := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors ha)
          have hb_pos : 0 < b := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hb)
          calc a = n / (n / a) := (Nat.div_div_self ha' hne).symm
            _ = n / (n / b) := by rw [hab]
            _ = b := Nat.div_div_self hb' hne
        -- Handle n = 1 separately (properDivisors empty)
        by_cases hn1 : n = 1
        · subst hn1; simp [Nat.properDivisors_one]
        · have hn2 : 2 ≤ n := by omega
          -- Step 2: Rewrite sum over image
          set g : ℕ → ℚ := fun e => (1 : ℚ) / ((e : ℚ) * ((e : ℚ) - 1)) with hg_def
          have hsum_eq : n.properDivisors.sum (fun d => g (n / d)) =
              (n.properDivisors.image (n / ·)).sum g :=
            (Finset.sum_image hinj).symm
          rw [hsum_eq]
          -- Step 3: Bound image sum by Icc 2 n sum (all terms nonneg)
          have himg := div_properDivisors_subset_Icc n hn
          have hg_nn : ∀ e ∈ Finset.Icc 2 n, 0 ≤ g e := by
            intro e he
            have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
            apply div_nonneg one_pos.le
            apply mul_nonneg (Nat.cast_nonneg e)
            have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he2
            linarith
          calc (n.properDivisors.image (n / ·)).sum g
              ≤ (Finset.Icc 2 n).sum g :=
                Finset.sum_le_sum_of_subset_of_nonneg himg (fun e he _ => hg_nn e he)
            _ = 1 - 1 / (n : ℚ) := sum_Icc_inv_pred_mul n hn2
            _ ≤ 1 := sub_le_self _ (div_nonneg one_pos.le (Nat.cast_nonneg n))
    _ = (n : ℚ) ^ 3 := by ring

theorem maj_E4 :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n E4ZSeries) G4Bound := by
  intro n; dsimp only; rw [coeff_E4ZSeries]; unfold E4CoeffZ G4Bound
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    rw [show (240 : ℤ) * ↑(ArithmeticFunction.sigma 3 n) =
      ↑(240 * ArithmeticFunction.sigma 3 n) from by push_cast; ring]
    rw [abs_of_nonneg (by positivity)]
    push_cast
    calc (240 * ArithmeticFunction.sigma 3 n : ℤ)
        ≤ 240 * (2 * n ^ 3) := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast sigma3_le_two_mul_cube n hn_pos
          · norm_num
      _ = 480 * n ^ 3 := by ring
      _ ≤ 2880 * Nat.choose (n + 2) 3 := by
          have hchoose : 6 * Nat.choose (n + 2) 3 = n * (n + 1) * (n + 2) := by
            have h1 := Nat.succ_mul_choose_eq (n + 1) 2
            have h2 := Nat.succ_mul_choose_eq n 1
            rw [Nat.choose_one_right] at h2
            nlinarith
          have hcube : n ^ 3 ≤ n * (n + 1) * (n + 2) := by nlinarith
          nlinarith

/-- For each d ∈ properDivisors n: d^5 ≤ n^5 · 1/((n/d)(n/d - 1)) in ℚ. -/
private lemma proper_div_fifth_le_inv_pred (n d : ℕ) (hn : 0 < n)
    (hd : d ∈ n.properDivisors) :
    (d : ℚ) ^ 5 ≤ (n : ℚ) ^ 5 * ((1 : ℚ) / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
  have hdvd := (Nat.mem_properDivisors.mp hd).1
  have hlt := (Nat.mem_properDivisors.mp hd).2
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hd)
  set e := n / d
  have he : 2 ≤ e := Nat.one_lt_div_of_mem_properDivisors hd
  have hde : d * e = n := by
    show d * (n / d) = n
    rw [mul_comm]; exact Nat.div_mul_cancel hdvd
  have he_pos : (0 : ℚ) < (e : ℚ) := by positivity
  have he1_pos : (0 : ℚ) < ((e : ℚ) - 1) := by
    have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
    linarith
  have hdQ : (d : ℚ) = (n : ℚ) / (e : ℚ) := by
    rw [eq_div_iff (ne_of_gt he_pos)]
    exact_mod_cast hde
  rw [hdQ, div_pow, mul_one_div]
  -- Goal: n^5 / e^5 ≤ n^5 / (e * (e - 1))
  -- Since e*(e-1) ≤ e^5 and e*(e-1) > 0:
  apply div_le_div_of_nonneg_left (by positivity) (mul_pos he_pos he1_pos)
  -- Need: e * (e - 1) ≤ e ^ 5, i.e. e - 1 ≤ e ^ 4
  have he2 : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he
  nlinarith [sq_nonneg ((e : ℚ)), sq_nonneg ((e : ℚ) ^ 2 - 1)]

private lemma sigma5_le_two_mul_pow5 (n : ℕ) (hn : 0 < n) :
    ArithmeticFunction.sigma 5 n ≤ 2 * n ^ 5 := by
  -- Cast to ℚ
  suffices h : (ArithmeticFunction.sigma 5 n : ℚ) ≤ 2 * (n : ℚ) ^ 5 by exact_mod_cast h
  -- Rewrite sigma as a sum over divisors
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  -- Split: divisors n = {n} ∪ properDivisors n
  have hne : n ≠ 0 := by omega
  rw [← Nat.cons_self_properDivisors hne, Finset.sum_cons]
  -- Goal: n^5 + Σ_{d ∈ properDiv} d^5 ≤ 2*n^5
  -- Suffices: Σ_{d ∈ properDiv} d^5 ≤ n^5
  suffices hpd : (n.properDivisors.sum fun d => (d : ℚ) ^ 5) ≤ (n : ℚ) ^ 5 by linarith
  -- Bound each d^5 by n^5 * 1/(e*(e-1)) where e = n/d
  calc n.properDivisors.sum (fun d => (d : ℚ) ^ 5)
      ≤ n.properDivisors.sum (fun d =>
          (n : ℚ) ^ 5 * (1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1)))) := by
        apply Finset.sum_le_sum
        intro d hd
        exact proper_div_fifth_le_inv_pred n d hn hd
    _ = (n : ℚ) ^ 5 * n.properDivisors.sum (fun d =>
          1 / ((n / d : ℕ) * (((n / d : ℕ) : ℚ) - 1))) := by
        rw [← Finset.mul_sum]
    _ ≤ (n : ℚ) ^ 5 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        -- Step 1: The map d ↦ n/d is injective on properDivisors
        have hinj : ∀ a ∈ n.properDivisors, ∀ b ∈ n.properDivisors,
            n / a = n / b → a = b := by
          intro a ha b hb hab
          have ha' := (Nat.mem_properDivisors.mp ha).1
          have hb' := (Nat.mem_properDivisors.mp hb).1
          have ha_pos : 0 < a := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors ha)
          have hb_pos : 0 < b := Nat.pos_of_mem_divisors (Nat.properDivisors_subset_divisors hb)
          calc a = n / (n / a) := (Nat.div_div_self ha' hne).symm
            _ = n / (n / b) := by rw [hab]
            _ = b := Nat.div_div_self hb' hne
        -- Handle n = 1 separately (properDivisors empty)
        by_cases hn1 : n = 1
        · subst hn1; simp [Nat.properDivisors_one]
        · have hn2 : 2 ≤ n := by omega
          -- Step 2: Rewrite sum over image
          set g : ℕ → ℚ := fun e => (1 : ℚ) / ((e : ℚ) * ((e : ℚ) - 1)) with hg_def
          have hsum_eq : n.properDivisors.sum (fun d => g (n / d)) =
              (n.properDivisors.image (n / ·)).sum g :=
            (Finset.sum_image hinj).symm
          rw [hsum_eq]
          -- Step 3: Bound image sum by Icc 2 n sum (all terms nonneg)
          have himg := div_properDivisors_subset_Icc n hn
          have hg_nn : ∀ e ∈ Finset.Icc 2 n, 0 ≤ g e := by
            intro e he
            have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
            apply div_nonneg one_pos.le
            apply mul_nonneg (Nat.cast_nonneg e)
            have : (2 : ℚ) ≤ (e : ℚ) := by exact_mod_cast he2
            linarith
          calc (n.properDivisors.image (n / ·)).sum g
              ≤ (Finset.Icc 2 n).sum g :=
                Finset.sum_le_sum_of_subset_of_nonneg himg (fun e he _ => hg_nn e he)
            _ = 1 - 1 / (n : ℚ) := sum_Icc_inv_pred_mul n hn2
            _ ≤ 1 := sub_le_self _ (div_nonneg one_pos.le (Nat.cast_nonneg n))
    _ = (n : ℚ) ^ 5 := by ring

set_option maxHeartbeats 400000 in
theorem maj_E6 :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n E6ZSeries) G6Bound := by
  intro n; dsimp only; rw [coeff_E6ZSeries]; unfold E6CoeffZ G6Bound
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    rw [show (-504 : ℤ) * ↑(ArithmeticFunction.sigma 5 n) =
      -(↑(504 * ArithmeticFunction.sigma 5 n)) from by push_cast; ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    push_cast
    calc (504 * ArithmeticFunction.sigma 5 n : ℤ)
        ≤ 504 * (2 * n ^ 5) := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast sigma5_le_two_mul_pow5 n hn_pos
          · norm_num
      _ = 1008 * n ^ 5 := by ring
      _ ≤ 120960 * Nat.choose (n + 4) 5 := by
          -- 120 * C(n+4,5) = n*(n+1)*(n+2)*(n+3)*(n+4)
          -- Build up: C(n+1,2)*2 = n*(n+1), C(n+2,3)*3 = (n+2)*C(n+1,2), etc.
          have h4 := Nat.succ_mul_choose_eq n 1
          rw [Nat.choose_one_right] at h4
          -- h4: (n+1) * n = C(n+1,2) * 2
          have h3 := Nat.succ_mul_choose_eq (n + 1) 2
          -- h3: (n+2) * C(n+1,2) = C(n+2,3) * 3
          have h2 := Nat.succ_mul_choose_eq (n + 2) 3
          -- h2: (n+3) * C(n+2,3) = C(n+3,4) * 4
          have h1 := Nat.succ_mul_choose_eq (n + 3) 4
          -- h1: (n+4) * C(n+3,4) = C(n+4,5) * 5
          -- From these: 120 * C(n+4,5) = n*(n+1)*(n+2)*(n+3)*(n+4)
          -- Step by step: set intermediate variables
          set c2 := Nat.choose (n + 1) 2
          set c3 := Nat.choose (n + 2) 3
          set c4 := Nat.choose (n + 3) 4
          set c5 := Nat.choose (n + 4) 5
          -- From h4: n*(n+1) = 2*c2
          have eq2 : n * (n + 1) = 2 * c2 := by linarith
          -- From h3: (n+2)*c2 = 3*c3
          have eq3 : (n + 2) * c2 = 3 * c3 := by linarith
          -- From h2: (n+3)*c3 = 4*c4
          have eq4 : (n + 3) * c3 = 4 * c4 := by linarith
          -- From h1: (n+4)*c4 = 5*c5
          have eq5 : (n + 4) * c4 = 5 * c5 := by linarith
          -- Chain: 120*c5 = 24*(n+4)*c4 = 24*(n+4)*(n+3)*c3/4 = ...
          -- Easier: n*(n+1)*(n+2)*(n+3)*(n+4) = 2*c2*(n+2)*(n+3)*(n+4)
          --   = 2*3*c3*(n+3)*(n+4) = 6*c3*(n+3)*(n+4)
          --   = 6*4*c4*(n+4) = 24*c4*(n+4) = 24*5*c5 = 120*c5
          have step1 : n * (n + 1) * (n + 2) = 2 * c2 * (n + 2) := by nlinarith
          have step2 : 2 * c2 * (n + 2) = 2 * (3 * c3) := by nlinarith
          have step3 : n * (n + 1) * (n + 2) * (n + 3) = 6 * c3 * (n + 3) := by nlinarith
          have step4 : 6 * c3 * (n + 3) = 6 * (4 * c4) := by nlinarith
          have step5 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 24 * c4 * (n + 4) := by nlinarith
          have step6 : 24 * c4 * (n + 4) = 24 * (5 * c5) := by nlinarith
          have hchoose : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 120 * c5 := by nlinarith
          -- n^5 ≤ n*(n+1)*(n+2)*(n+3)*(n+4)
          have hpow5 : n ^ 5 ≤ n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
            have h0 : 0 < n := hn_pos
            nlinarith [sq_nonneg n, sq_nonneg (n * (n + 1) - n * n)]
          -- 1008 * n^5 ≤ 120960 * c5
          nlinarith

/-- Δ majorant from |1728 Δ| ≤ |E4³| + |E6²|, i.e. |Δ| ≤ (G4³ + G6²).
    We skip the 1728 denominator for simplicity. -/
def DeltaBound (n : ℕ) : ℕ :=
  convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n +
  convNat G6Bound G6Bound n

/-- Tighter Δ majorant keeping the 1/1728 factor: |Δ[n]| ≤ ⌈(G4³ + G6²)(n) / 1728⌉. -/
def DeltaBoundTight (n : ℕ) : ℕ :=
  (convNat G4Bound (convNat G4Bound G4Bound) n +
   convNat G6Bound G6Bound n) / 1728 + 1

/-- Classical identity: `1728 Δ = E₄³ − E₆²`, as a formal power series over `ℤ`.

**Proof route** (all ingredients exist in the codebase):

1. Form `G := E₄³ − E₆² − 1728 Δ` as a `CuspForm Γ(1) 12` in the complex setting.
   - E₄³ and E₆² are weight-12 modular forms; 1728 Δ is weight 12.
   - G[0] = 1 − 1 − 0 = 0, so G is a cusp form.

2. Apply `cuspForm_eq_zero_via` (from `LevelOneSturmGeneric.lean`) with
   `(k, a, b, n) = (12, 1, 1, 2)`:
   - `1 * 12 = 12 * 1` ✓
   - `1 * 2 ≥ 1 + 1` ✓
   - Need G's q-expansion coefficients at m = 0 and m = 1 to vanish.
   - G[0] = 0 ✓;  G[1] = 720 − (−1008) − 1728 = 0 ✓  (by `native_decide`).

3. From `G = 0` as functions ℍ → ℂ, use `qExpansion_coeff_unique` to get
   `∀ n, coeff n (map ℤ→ℂ) G_Z = 0`, then lift to ℤ by `Int.cast_injective`.

This requires bundling E₄³ − E₆² as a `ModularForm Γ(1) 12` and constructing the
corresponding `CuspForm`.  The generic Sturm machinery handles the rest. -/
-- Helper: weight cast lemmas
private lemma three_mul_four_eq_twelve : (3 : ℕ) * (4 : ℤ) = 12 := by norm_num
private lemma two_mul_six_eq_twelve : (2 : ℕ) * (6 : ℤ) = 12 := by norm_num

-- Helper: E4^3 as a weight-12 modular form at level 1.
private noncomputable def E4CubedMF : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast three_mul_four_eq_twelve
    (((DirectSum.of (ModularForm 𝒮ℒ) 4 E4) ^ 3) ((3 : ℕ) * (4 : ℤ)))

-- Helper: E6^2 as a weight-12 modular form at level 1.
private noncomputable def E6SquaredMF : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast two_mul_six_eq_twelve
    (((DirectSum.of (ModularForm 𝒮ℒ) 6 E6) ^ 2) ((2 : ℕ) * (6 : ℤ)))

-- Helper: E4^3 q-expansion = E4QExpansion^3
private lemma E4CubedMF_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (E4CubedMF : ℍ → ℂ) =
      E4QExpansion ^ 3 := by
  -- E4CubedMF = mcast (of E4 ^ 3), and mcast doesn't change the underlying function.
  -- qExpansion_of_pow gives qExpansion of (of E4)^3 = (qExpansion E4)^3.
  change ModularFormClass.qExpansion (1 : ℝ)
    ((ModularForm.mcast three_mul_four_eq_twelve
      (((DirectSum.of (ModularForm 𝒮ℒ) 4 E4) ^ 3) ((3 : ℕ) * (4 : ℤ))) : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = _
  -- mcast doesn't change the function
  show ModularFormClass.qExpansion (1 : ℝ)
    ((((DirectSum.of (ModularForm 𝒮ℒ) 4 E4) ^ 3) ((3 : ℕ) * (4 : ℤ)) : ModularForm 𝒮ℒ _) : ℍ → ℂ) = _
  exact ModularForm.qExpansion_of_pow one_pos ModularFormClass.one_mem_strictPeriods_SL2Z E4 3

-- Helper: E6^2 q-expansion = E6QExpansion^2
private lemma E6SquaredMF_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (E6SquaredMF : ℍ → ℂ) =
      E6QExpansion ^ 2 := by
  change ModularFormClass.qExpansion (1 : ℝ)
    ((ModularForm.mcast two_mul_six_eq_twelve
      (((DirectSum.of (ModularForm 𝒮ℒ) 6 E6) ^ 2) ((2 : ℕ) * (6 : ℤ))) : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = _
  show ModularFormClass.qExpansion (1 : ℝ)
    ((((DirectSum.of (ModularForm 𝒮ℒ) 6 E6) ^ 2) ((2 : ℕ) * (6 : ℤ)) : ModularForm 𝒮ℒ _) : ℍ → ℂ) = _
  exact ModularForm.qExpansion_of_pow one_pos ModularFormClass.one_mem_strictPeriods_SL2Z E6 2

-- Helper: Δ q-expansion of deltaLevelOneMF equals deltaEulerSeries
private lemma deltaLevelOneMF_qExpansion :
    ModularFormClass.qExpansion (1 : ℝ) (deltaLevelOneMF : ℍ → ℂ) =
      deltaEulerSeries := by
    ext d; symm
    refine ModularFormClass.qExpansion_coeff_unique
      (c := fun n => PowerSeries.coeff (R := ℂ) n deltaEulerSeries)
      (f := deltaLevelOneMF)
      one_pos ModularFormClass.one_mem_strictPeriods_SL2Z ?_ d
    intro τ; simpa [smul_eq_mul, deltaLevelOneMF] using deltaEulerSeries_hasSum τ

-- Helper: map ℤ → ℂ for E6ZSeries
private lemma map_E6ZSeries :
    PowerSeries.map (Int.castRingHom ℂ) E6ZSeries = E6QExpansion := by
  ext n; rw [PowerSeries.coeff_map, coeff_E6ZSeries, coeff_E6QExpansion]
  unfold E6CoeffZ; by_cases hn : n = 0 <;> simp [hn]

/-- The modular form `G = E₄³ − E₆² − 1728 Δ` of weight 12 and level 1,
whose vanishing is the core of the identity. -/
private noncomputable def deltaIdentityGMF : ModularForm 𝒮ℒ 12 :=
  E4CubedMF - E6SquaredMF - (1728 : ℂ) • deltaLevelOneMF

-- Coefficient of G's q-expansion at m equals the corresponding integer computation.
set_option maxHeartbeats 3200000 in
private lemma deltaIdentityGMF_qExpansion_coeff (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ)).coeff m =
      (PowerSeries.coeff (R := ℤ) m (E4ZSeries ^ 3) : ℂ) -
        (PowerSeries.coeff (R := ℤ) m (E6ZSeries ^ 2) : ℂ) -
        1728 * (PowerSeries.coeff (R := ℤ) m deltaEulerSeriesZ : ℂ) := by
  -- Use qExpansion_coeff_unique: G has HasSum equal to E4^3 - E6^2 - 1728*Δ.
  -- The ℤ power series mapped to ℂ give HasSum to E4, E6, Δ.
  -- G = E4CubedMF - E6SquaredMF - 1728 • deltaLevelOneMF
  -- The coefficients of qExpansion(G) equal the HasSum coefficients.
  -- We show HasSum for G using the individual HasSum for E4^3, E6^2, Δ.
  let c : ℕ → ℂ := fun m =>
    (PowerSeries.coeff (R := ℤ) m (E4ZSeries ^ 3) : ℂ) -
      (PowerSeries.coeff (R := ℤ) m (E6ZSeries ^ 2) : ℂ) -
      1728 * (PowerSeries.coeff (R := ℤ) m deltaEulerSeriesZ : ℂ)
  suffices hHS : ∀ τ : ℍ, HasSum (fun m => c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (deltaIdentityGMF τ) by
    exact (ModularFormClass.qExpansion_coeff_unique (f := deltaIdentityGMF)
      one_pos ModularFormClass.one_mem_strictPeriods_SL2Z hHS m).symm
  intro τ
  -- deltaIdentityGMF τ = E4CubedMF τ - E6SquaredMF τ - 1728 * deltaLevelOneMF τ
  -- = E4(τ)^3 - E6(τ)^2 - 1728 * delta(τ)  (by definition)
  -- HasSum for E4^3: from E4CubedMF
  have hE4cube : HasSum (fun m => PowerSeries.coeff (R := ℂ) m (E4QExpansion ^ 3) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E4CubedMF τ) := by
    rw [← E4CubedMF_qExpansion]
    exact ModularFormClass.hasSum_qExpansion (f := E4CubedMF) one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z τ
  have hE6sq : HasSum (fun m => PowerSeries.coeff (R := ℂ) m (E6QExpansion ^ 2) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E6SquaredMF τ) := by
    rw [← E6SquaredMF_qExpansion]
    exact ModularFormClass.hasSum_qExpansion (f := E6SquaredMF) one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z τ
  have hDelta : HasSum (fun m => PowerSeries.coeff (R := ℂ) m deltaEulerSeries *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (deltaLevelOneMF τ) := by
    rw [← deltaLevelOneMF_qExpansion]
    exact ModularFormClass.hasSum_qExpansion (f := deltaLevelOneMF) one_pos
      ModularFormClass.one_mem_strictPeriods_SL2Z τ
  -- Combine: G = E4³ - E6² - 1728*Δ
  have hcombine := ((hE4cube.sub hE6sq).sub (hDelta.mul_left 1728))
  -- Rewrite E4QExpansion etc. in terms of ℤ-series mapped to ℂ
  convert hcombine using 1
  · ext m
    simp only [c, smul_eq_mul, sub_mul]
    have hE4coeff :
        PowerSeries.coeff (R := ℂ) m (E4QExpansion ^ 3) =
          (PowerSeries.coeff (R := ℤ) m (E4ZSeries ^ 3) : ℂ) := by
      rw [← map_E4ZSeries, ← map_pow, PowerSeries.coeff_map]
      rfl
    have hE6coeff :
        PowerSeries.coeff (R := ℂ) m (E6QExpansion ^ 2) =
          (PowerSeries.coeff (R := ℤ) m (E6ZSeries ^ 2) : ℂ) := by
      rw [← map_E6ZSeries, ← map_pow, PowerSeries.coeff_map]
      rfl
    have hDcoeff :
        PowerSeries.coeff (R := ℂ) m deltaEulerSeries =
          (PowerSeries.coeff (R := ℤ) m deltaEulerSeriesZ : ℂ) := by
      rw [← map_deltaEulerSeriesZ, PowerSeries.coeff_map]
      rfl
    rw [hE4coeff, hE6coeff, hDcoeff]
    ring

set_option maxHeartbeats 1600000 in
/-- Coefficient check: the first two coefficients of `G = E₄³ − E₆² − 1728 Δ` vanish.
For `m = 0`: `1 − 1 − 1728 · 0 = 0`.
For `m = 1`: `720 − (−1008) − 1728 · 1 = 0`. -/
private theorem deltaIdentityGMF_low_coeffs_vanish (m : ℕ) (hm : m ≤ 1) :
    (ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ)).coeff m = 0 := by
  rw [deltaIdentityGMF_qExpansion_coeff]
  -- It suffices to show the ℤ expression is zero.
  suffices hZ : PowerSeries.coeff (R := ℤ) m (E4ZSeries ^ 3) -
      PowerSeries.coeff (R := ℤ) m (E6ZSeries ^ 2) -
      1728 * PowerSeries.coeff (R := ℤ) m deltaEulerSeriesZ = 0 by
    exact_mod_cast hZ
  interval_cases m
  · -- m = 0: E4Z^3[0] = 1^3 = 1, E6Z^2[0] = 1^2 = 1, Δ[0] = 0
    have hE4 : PowerSeries.coeff (R := ℤ) 0 (E4ZSeries ^ 3) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      have : PowerSeries.constantCoeff (R := ℤ) E4ZSeries = 1 := by
        simp [E4ZSeries, E4CoeffZ]
      simp [this]
    have hE6 : PowerSeries.coeff (R := ℤ) 0 (E6ZSeries ^ 2) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      have : PowerSeries.constantCoeff (R := ℤ) E6ZSeries = 1 := by
        simp [E6ZSeries, E6CoeffZ]
      simp [this]
    have hD : PowerSeries.coeff (R := ℤ) 0 deltaEulerSeriesZ = 0 := by
      rw [coeff_deltaEulerSeriesZ]; exact deltaEulerCoeffZ_zero
    simp [hE4, hE6, hD]
  · -- m = 1: use coeff_mul to expand convolutions
    -- E4Z^3 = E4Z * E4Z^2, and E4Z^2 = E4Z * E4Z
    -- coeff 1 (f * g) = f[0]*g[1] + f[1]*g[0]
    -- E4Z[0] = 1, E4Z[1] = 240, E6Z[0] = 1, E6Z[1] = -504, Δ[1] = 1
    have hE4_0 : PowerSeries.coeff (R := ℤ) 0 E4ZSeries = 1 := by
      simp [coeff_E4ZSeries, E4CoeffZ]
    have hE4_1 : PowerSeries.coeff (R := ℤ) 1 E4ZSeries = 240 := by
      simp [coeff_E4ZSeries, E4CoeffZ, ArithmeticFunction.sigma]
    have hE6_0 : PowerSeries.coeff (R := ℤ) 0 E6ZSeries = 1 := by
      simp [coeff_E6ZSeries, E6CoeffZ]
    have hE6_1 : PowerSeries.coeff (R := ℤ) 1 E6ZSeries = -504 := by
      simp [coeff_E6ZSeries, E6CoeffZ, ArithmeticFunction.sigma]
    have hD_1 : PowerSeries.coeff (R := ℤ) 1 deltaEulerSeriesZ = 1 :=
      coeff_deltaEulerSeriesZ_one
    -- E4Z^2[1] = E4Z[0]*E4Z[1] + E4Z[1]*E4Z[0] = 2*240 = 480
    have hE4sq_1 : PowerSeries.coeff (R := ℤ) 1 (E4ZSeries ^ 2) = 480 := by
      rw [pow_two, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton]
      simp [hE4_0, hE4_1]
    -- E4Z^3[1] = E4Z[0]*E4Z^2[1] + E4Z[1]*E4Z^2[0] = 480 + 240 = 720
    have hE4sq_0 : PowerSeries.coeff (R := ℤ) 0 (E4ZSeries ^ 2) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
      simp [E4ZSeries, E4CoeffZ]
    have hE4cube_1 : PowerSeries.coeff (R := ℤ) 1 (E4ZSeries ^ 3) = 720 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton]
      simp [hE4_0, hE4_1, hE4sq_0, hE4sq_1]
    -- E6Z^2[1] = E6Z[0]*E6Z[1] + E6Z[1]*E6Z[0] = 2*(-504) = -1008
    have hE6sq_1 : PowerSeries.coeff (R := ℤ) 1 (E6ZSeries ^ 2) = -1008 := by
      rw [pow_two, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton]
      simp [hE6_0, hE6_1]
    rw [hE4cube_1, hE6sq_1, hD_1]
    ring

set_option maxHeartbeats 800000 in
theorem delta_1728_identity :
    (1728 : ℤ) • deltaEulerSeriesZ = E4ZSeries ^ 3 - E6ZSeries ^ 2 := by
  -- Step 1: Show G = E4³ - E6² - 1728Δ = 0 as a weight-12 modular form via Sturm bound.
  have hG : deltaIdentityGMF = 0 :=
    levelOne_modularForm_eq_zero_of_low_coeffs_vanish
      (show (4 : ℕ) ≤ 12 by norm_num) ⟨6, rfl⟩
      deltaIdentityGMF
      (fun m hm => deltaIdentityGMF_low_coeffs_vanish m (by omega))
  -- Step 2: From G = 0, every q-expansion coefficient vanishes.
  have hqzero : ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ) = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos ModularFormClass.one_mem_strictPeriods_SL2Z
      deltaIdentityGMF).mpr hG
  have hzero_coeff : ∀ n, (ModularFormClass.qExpansion (1 : ℝ) (deltaIdentityGMF : ℍ → ℂ)).coeff n = 0 := by
    intro n; rw [hqzero]; simp
  -- Step 3: Each coefficient of G's q-expansion equals the ℤ computation.
  -- From deltaIdentityGMF_qExpansion_coeff + hzero_coeff, we get the ℤ identity.
  ext n
  have hcoeff := deltaIdentityGMF_qExpansion_coeff n
  rw [hzero_coeff] at hcoeff
  -- hcoeff: 0 = (E4Z^3[n] : ℂ) - (E6Z^2[n] : ℂ) - 1728 * (ΔZ[n] : ℂ)
  -- Goal: 1728 • ΔZ[n] = E4Z^3[n] - E6Z^2[n]
  -- The ℤ identity follows from the vanishing ℂ identity by injectivity of ℤ → ℂ.
  apply Int.cast_injective (α := ℂ)
  simp only [map_smul, map_sub, smul_eq_mul]
  push_cast
  set A : ℂ := (PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) : ℂ)
  set B : ℂ := (PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2) : ℂ)
  set D : ℂ := (PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ : ℂ)
  change (1728 : ℂ) * D = A - B
  have h0 : A - B - 1728 * D = 0 := by
    simpa [A, B, D] using hcoeff.symm
  exact (sub_eq_zero.mp h0).symm

/-- Convolution of a nonneg sequence with the constant-1 sequence is at least
    the original sequence pointwise. -/
private lemma le_convNat_one (F : ℕ → ℕ) (n : ℕ) :
    F n ≤ convNat F (fun _ => 1) n := by
  simp only [convNat, mul_one]
  exact Finset.single_le_sum (fun k _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl))

/-- `PowerSeries.mk (coeff · f) = f` — reconstruction from coefficients. -/
private lemma mk_coeff_eq (f : PowerSeries ℤ) :
    PowerSeries.mk (fun n => PowerSeries.coeff (R := ℤ) n f) = f :=
  PowerSeries.ext (fun n => PowerSeries.coeff_mk n _)

theorem maj_Delta :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ) DeltaBound := by
  -- From the 1728 identity: 1728 * Δ[n] = (E4³)[n] - (E6²)[n]
  -- So |Δ[n]| = |(E4³ - E6²)[n]| / 1728 ≤ (|(E4³)[n]| + |(E6²)[n]|) / 1728
  --          ≤ |(E4³)[n]| + |(E6²)[n]|
  have hident := delta_1728_identity
  -- E4³ majorant
  have hE4_mk : PowerSeries.mk (fun n => PowerSeries.coeff (R := ℤ) n E4ZSeries) =
      E4ZSeries := mk_coeff_eq _
  have hE6_mk : PowerSeries.mk (fun n => PowerSeries.coeff (R := ℤ) n E6ZSeries) =
      E6ZSeries := mk_coeff_eq _
  have maj_E4_cube : Maj (fun n =>
      PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3))
      (powConvNat G4Bound 3) := by
    have h := Maj.powConv maj_E4 3; rwa [hE4_mk] at h
  have maj_E6_sq : Maj (fun n =>
      PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))
      (powConvNat G6Bound 2) := by
    have h := Maj.powConv maj_E6 2; rwa [hE6_mk] at h
  -- powConvNat G4Bound 3 = convNat G4Bound (convNat G4Bound G4Bound)
  -- powConvNat G6Bound 2 = convNat G6Bound G6Bound
  -- We need to show these definitional equalities modulo convNat with delta_0
  -- powConvNat F 1 = convNat F δ₀ which equals F pointwise
  -- For now, unfold powConvNat and work with the definitions
  intro n
  -- From the identity: 1728 * Δ[n] = (E4³ - E6²)[n]
  have hcoeff : (1728 : ℤ) * PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ =
      PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3 - E6ZSeries ^ 2) := by
    have := congr_arg (PowerSeries.coeff (R := ℤ) n) hident
    simp only [map_smul, smul_eq_mul] at this
    exact this
  -- |Δ[n]| * 1728 = |1728 * Δ[n]| = |(E4³ - E6²)[n]| ≤ |E4³[n]| + |E6²[n]|
  have h1728_pos : (0 : ℤ) < 1728 := by norm_num
  rw [map_sub] at hcoeff
  have habs_ineq : (1728 : ℤ) * |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤
      |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
      |PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)| := by
    rw [← abs_of_pos h1728_pos, ← abs_mul, hcoeff]
    -- |a - b| ≤ |a| + |b|
    calc |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) -
            PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)|
        ≤ |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
          |-(PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))| := by
            rw [show PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) -
              PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2) =
              PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) +
              (-(PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))) from sub_eq_add_neg _ _]
            exact abs_add_le _ _
      _ = _ := by rw [abs_neg]
  -- Now bound |E4³[n]| and |E6²[n]|
  have hE4cube_bound := maj_E4_cube n
  have hE6sq_bound := maj_E6_sq n
  -- |Δ[n]| ≤ (|E4³[n]| + |E6²[n]|) / 1728
  --        ≤ |E4³[n]| + |E6²[n]|
  --        ≤ powConvNat G4Bound 3 n + powConvNat G6Bound 2 n
  have hdelta_bound : |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤
      ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) := by
    have h := habs_ineq
    have := add_le_add hE4cube_bound hE6sq_bound
    calc |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ|
        ≤ 1728 * |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| := by
          linarith [abs_nonneg (PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ)]
      _ ≤ |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
          |PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)| := habs_ineq
      _ ≤ ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) := this
  -- Now relate powConvNat to the DeltaBound definition
  -- DeltaBound n = convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n
  --             + convNat G6Bound G6Bound n
  -- powConvNat G4Bound 3 n ≤ convNat (powConvNat G4Bound 3) (fun _ => 1) n
  -- and powConvNat G4Bound 3 = convNat G4Bound (convNat G4Bound G4Bound) (need proof)
  -- powConvNat G6Bound 2 n = convNat G6Bound G6Bound (need proof)
  -- Step: show powConvNat G4Bound 3 n ≤ first term of DeltaBound
  -- and powConvNat G6Bound 2 n ≤ second term of DeltaBound
  show |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤ ↑(DeltaBound n)
  unfold DeltaBound
  push_cast
  calc |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ|
      ≤ ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) := hdelta_bound
    _ ≤ ↑(convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n) +
        ↑(convNat G6Bound G6Bound n) := by
        apply add_le_add
        · -- powConvNat G4Bound 3 n ≤ convNat (...) (fun _ => 1) n
          -- First: powConvNat G4Bound 3 = convNat G4Bound (convNat G4Bound G4Bound)
          -- as functions (need to unfold and show convNat F δ₀ = F)
          suffices h : powConvNat G4Bound 3 n ≤
              convNat (convNat G4Bound (convNat G4Bound G4Bound)) (fun _ => 1) n by
            exact_mod_cast h
          -- powConvNat G4Bound 3 n = convNat G4Bound (powConvNat G4Bound 2) n
          --   = convNat G4Bound (convNat G4Bound (powConvNat G4Bound 1)) n
          -- where powConvNat G4Bound 1 = convNat G4Bound (powConvNat G4Bound 0)
          --   = convNat G4Bound δ₀
          -- and convNat F δ₀ = F pointwise
          -- So powConvNat G4Bound 3 n = convNat G4Bound (convNat G4Bound G4Bound) n
          have hpow1 : ∀ m, powConvNat G4Bound 1 m = G4Bound m := by
            intro m; show convNat G4Bound (fun n => if n = 0 then 1 else 0) m = G4Bound m
            simp only [convNat]
            rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
              (fun k hk hkm => by
                have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
                have hklt : k < m := lt_of_le_of_ne hkle hkm
                simp [show m - k ≠ 0 from Nat.ne_of_gt (Nat.sub_pos_of_lt hklt)])]
            simp
          have hpow3_eq : powConvNat G4Bound 3 n =
              convNat G4Bound (convNat G4Bound G4Bound) n := by
            show convNat G4Bound (convNat G4Bound (powConvNat G4Bound 1)) n =
              convNat G4Bound (convNat G4Bound G4Bound) n
            congr 1; ext m; congr 1; ext m'; exact hpow1 m'
          rw [hpow3_eq]
          exact le_convNat_one _ n
        · -- powConvNat G6Bound 2 n = convNat G6Bound G6Bound n
          have hpow1 : ∀ m, powConvNat G6Bound 1 m = G6Bound m := by
            intro m; show convNat G6Bound (fun n => if n = 0 then 1 else 0) m = G6Bound m
            simp only [convNat]
            rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
              (fun k hk hkm => by
                have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
                have hklt : k < m := lt_of_le_of_ne hkle hkm
                simp [show m - k ≠ 0 from Nat.ne_of_gt (Nat.sub_pos_of_lt hklt)])]
            simp
          have hpow2_eq : powConvNat G6Bound 2 n = convNat G6Bound G6Bound n := by
            show convNat G6Bound (powConvNat G6Bound 1) n =
              convNat G6Bound G6Bound n
            congr 1; ext m; exact hpow1 m
          rw [hpow2_eq]

theorem maj_DeltaTight :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ) DeltaBoundTight := by
  have hident := delta_1728_identity
  have hE4_mk := mk_coeff_eq E4ZSeries
  have hE6_mk := mk_coeff_eq E6ZSeries
  have maj_E4_cube : Maj (fun n => PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3))
      (powConvNat G4Bound 3) := by
    have h := Maj.powConv maj_E4 3; rwa [hE4_mk] at h
  have maj_E6_sq : Maj (fun n => PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2))
      (powConvNat G6Bound 2) := by
    have h := Maj.powConv maj_E6 2; rwa [hE6_mk] at h
  intro n
  have hcoeff : (1728 : ℤ) * PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ =
      PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3 - E6ZSeries ^ 2) := by
    have := congr_arg (PowerSeries.coeff (R := ℤ) n) hident
    simp only [map_smul, smul_eq_mul] at this; exact this
  rw [map_sub] at hcoeff
  have hpow1_G4 : ∀ m, powConvNat G4Bound 1 m = G4Bound m := by
    intro m; show convNat G4Bound (fun n => if n = 0 then 1 else 0) m = G4Bound m
    simp only [convNat]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
      (fun k hk hkm => by
        have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hklt : k < m := lt_of_le_of_ne hkle hkm
        simp [show m - k ≠ 0 from Nat.ne_of_gt (Nat.sub_pos_of_lt hklt)])]
    simp
  have hpow3_eq : ∀ m, powConvNat G4Bound 3 m =
      convNat G4Bound (convNat G4Bound G4Bound) m := by
    intro m
    show convNat G4Bound (convNat G4Bound (powConvNat G4Bound 1)) m = _
    congr 1; ext m'; congr 1; ext m''; exact hpow1_G4 m''
  have hpow1_G6 : ∀ m, powConvNat G6Bound 1 m = G6Bound m := by
    intro m; show convNat G6Bound (fun n => if n = 0 then 1 else 0) m = G6Bound m
    simp only [convNat]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr (by omega))
      (fun k hk hkm => by
        have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hklt : k < m := lt_of_le_of_ne hkle hkm
        simp [show m - k ≠ 0 from Nat.ne_of_gt (Nat.sub_pos_of_lt hklt)])]
    simp
  have hpow2_eq : ∀ m, powConvNat G6Bound 2 m = convNat G6Bound G6Bound m := by
    intro m; show convNat G6Bound (powConvNat G6Bound 1) m = _
    congr 1; ext m'; exact hpow1_G6 m'
  set C := convNat G4Bound (convNat G4Bound G4Bound) n + convNat G6Bound G6Bound n
  have h1728_bound : 1728 * |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤ (C : ℤ) := by
    rw [← abs_of_pos (show (0 : ℤ) < 1728 from by norm_num), ← abs_mul, hcoeff]
    calc |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3) -
            PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)|
        ≤ |PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ 3)| +
          |PowerSeries.coeff (R := ℤ) n (E6ZSeries ^ 2)| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ ↑(powConvNat G4Bound 3 n) + ↑(powConvNat G6Bound 2 n) :=
          add_le_add (maj_E4_cube n) (maj_E6_sq n)
      _ = ↑C := by simp only [C, hpow3_eq, hpow2_eq]; push_cast; ring
  show |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| ≤ ↑(DeltaBoundTight n)
  unfold DeltaBoundTight
  push_cast
  have h_abs_nn : (0 : ℤ) ≤ |PowerSeries.coeff (R := ℤ) n deltaEulerSeriesZ| := abs_nonneg _
  omega

/-! ## Layer 3: Row bridge and row bounds

  The derivative identity (already proved):
    E4 · D Q_j = (42 E2E4 - j E6) · Q_j

  establishes that the recurrence rows Q_j are exactly the Fourier
  coefficients of Δ^(42-j) · E4^(3j). This is a symbolic proof
  using uniqueness of the recurrence solution.
-/

/-- The recurrence row Q_j equals the closed form Δ^(42-j) · (E4³)^j,
for any truncation length containing the requested coefficient. -/
theorem phi41_Qrow_eq_closed_form_of_lt (N j : ℕ) (hj : j ≤ 42) (n : ℕ)
    (hn : n < N) :
    truncCoeffArrayAt
      ((phi41QRecurrenceRowsArray N).getD j
        (zeroTruncCoeffArray N)) n =
      PowerSeries.coeff (R := ℤ) n
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)) := by
  -- Step 1: TruncRep connects the power series to the dense row list
  have hTR := TruncRep.phi41LevelOneDenseRowExpr N j
  -- Step 2: The dense row list satisfies the recurrence (from the derivative identity)
  have hderiv : E4ZSeries *
      (PowerSeries.X * PowerSeries.derivative ℤ
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
    (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
      PowerSeries.C (j : ℤ) * E6ZSeries) *
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)) :=
    phi41LevelOneDenseRow_derivative_identity_of_base j hj
      (E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity
        E4ZSeries_derivative_identity)
      deltaEulerSeriesZ_derivative_identity
  -- Step 3: ListArrayEq connects the dense row list to the recurrence row array
  have hLA : ListArrayEq N
      ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N))
      (phi41QRecurrenceRowArray N j
        (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N)) :=
    ListArrayEq.of_phi41QRecurrence
      (ListArrayEq.E4 N) (ListArrayEq.E6 N) (ListArrayEq.E2E4 N)
      (fun m hm hmv =>
        truncCoeffAt_phi41LevelOneDenseRowsList_eq_zero_of_lt_valuation hj hm hmv)
      (fun m hm hmv =>
        truncCoeffAt_phi41LevelOneDenseRowsList_eq_one_of_eq_valuation hj hm hmv)
      (fun m hm hmv =>
        truncCoeffAt_phi41LevelOneDenseRowsList_eq_recurrence_of_derivative_identity
          hj hm hmv hderiv)
  -- Step 4: Unwrap the array access
  rw [phi41QRecurrenceRowsArray_getD_of_le N hj]
  -- Step 5: Chain the equalities
  -- TruncRep gives: coeff n (...) = truncCoeffAt (dense_row) n
  have hcoeff := hTR n hn
  -- ListArrayEq gives: truncCoeffAt (dense_row) n = truncCoeffArrayAt (rec_row) n
  have hLA_n := hLA n hn
  -- Rewrite using phi41LevelOneDenseRowsList_getD_of_le
  rw [phi41LevelOneDenseRowsList_getD_of_le N hj] at hLA_n
  -- Now hLA_n : truncCoeffAt (mulTruncCoeffList ...) n = truncCoeffArrayAt (recRow) n
  -- hcoeff : coeff n (...) = truncCoeffAt (mulTruncCoeffList ...) n
  rw [← hLA_n, ← hcoeff]

/-- The recurrence row Q_j equals the closed form Δ^(42-j) · (E4³)^j. -/
theorem phi41_Qrow_eq_closed_form (j : ℕ) (hj : j ≤ 42) (n : ℕ)
    (hn : n < phi41Level41SturmBound) :
    truncCoeffArrayAt
      ((phi41QRecurrenceRowsArray phi41Level41SturmBound).getD j
        (zeroTruncCoeffArray phi41Level41SturmBound)) n =
      PowerSeries.coeff (R := ℤ) n
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)) :=
  phi41_Qrow_eq_closed_form_of_lt phi41Level41SturmBound j hj n hn

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
/-- Majorant chain: |(E4³)^j · Δ^(42-j) [n]| ≤ conv(G4^{3j}, DeltaTight^{42-j})(n). -/
theorem maj_Qrow (j : ℕ) (hj : j ≤ 42) :
    Maj (fun n => PowerSeries.coeff (R := ℤ) n
        ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)))
      (convNat (powConvNat G4Bound (3 * j)) (powConvNat DeltaBoundTight (42 - j))) := by
  have hE4_mk := mk_coeff_eq E4ZSeries
  have hD_mk := mk_coeff_eq deltaEulerSeriesZ
  have maj_E4_pow : Maj (fun n => PowerSeries.coeff (R := ℤ) n (E4ZSeries ^ (3 * j)))
      (powConvNat G4Bound (3 * j)) := by
    have h := Maj.powConv maj_E4 (3 * j); rwa [hE4_mk] at h
  have maj_D_pow : Maj (fun n => PowerSeries.coeff (R := ℤ) n (deltaEulerSeriesZ ^ (42 - j)))
      (powConvNat DeltaBoundTight (42 - j)) := by
    have h := Maj.powConv maj_DeltaTight (42 - j); rwa [hD_mk] at h
  have hpow : (E4ZSeries ^ 3) ^ j = E4ZSeries ^ (3 * j) := by rw [← pow_mul]
  intro n
  dsimp only
  rw [hpow]
  change |PowerSeries.coeff (R := ℤ) n
      (E4ZSeries ^ (3 * j) * deltaEulerSeriesZ ^ (42 - j))| ≤ _
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact Maj.conv maj_E4_pow maj_D_pow n

private lemma multichoose_pos_of_pos {r : ℕ} (hr : 0 < r) (n : ℕ) :
    0 < Nat.multichoose r n := by
  rw [Nat.multichoose_eq]
  exact Nat.choose_pos (by omega)

private lemma convNat_multichoose_zero_right (r n : ℕ) :
    convNat (Nat.multichoose r) (Nat.multichoose 0) n =
      Nat.multichoose r n := by
  unfold convNat
  rw [Finset.sum_eq_single n]
  · simp [Nat.multichoose_zero_right]
  · intro k hk hkn
    have hklt : k < n := by
      have hkle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      omega
    have hpos : 0 < n - k := by omega
    cases h : n - k with
    | zero => omega
    | succ t =>
        simp [h, Nat.multichoose_zero_succ]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self n)))

private lemma coeff_invOneSubPow_multichoose_int (r n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow ℤ r).val =
      (Nat.multichoose r n : ℤ) := by
  cases r with
  | zero =>
      cases n with
      | zero => simp [PowerSeries.invOneSubPow]
      | succ n => simp [PowerSeries.invOneSubPow, Nat.multichoose_zero_succ]
  | succ d =>
      rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
      rw [PowerSeries.coeff_mk, Nat.multichoose_eq]
      have htop : d + 1 + n - 1 = d + n := by omega
      rw [htop]
      norm_num
      have hsym := Nat.choose_symm (n := d + n) (k := d) (by omega : d ≤ d + n)
      simpa [Nat.add_sub_cancel_left] using hsym.symm

private lemma convNat_multichoose (r s n : ℕ) :
    convNat (Nat.multichoose r) (Nat.multichoose s) n =
      Nat.multichoose (r + s) n := by
  apply Nat.cast_injective (R := ℤ)
  have h := congrArg (fun u : PowerSeries ℤ => PowerSeries.coeff n u)
    (congrArg Units.val (PowerSeries.invOneSubPow_add (S := ℤ) (d := r) s))
  change PowerSeries.coeff n (PowerSeries.invOneSubPow ℤ (r + s)).val =
    PowerSeries.coeff n
      ((PowerSeries.invOneSubPow ℤ r).val * (PowerSeries.invOneSubPow ℤ s).val) at h
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  rw [← coeff_invOneSubPow_multichoose_int (r + s) n]
  rw [h]
  unfold convNat
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k _hk
  rw [coeff_invOneSubPow_multichoose_int r k,
    coeff_invOneSubPow_multichoose_int s (n - k)]

private lemma convNat_le_mul_multichoose {F G : ℕ → ℕ} {A B r s : ℕ}
    (hF : ∀ n, F n ≤ A * Nat.multichoose r n)
    (hG : ∀ n, G n ≤ B * Nat.multichoose s n) (n : ℕ) :
    convNat F G n ≤ A * B * Nat.multichoose (r + s) n := by
  unfold convNat
  calc
    (∑ k ∈ Finset.range (n + 1), F k * G (n - k))
        ≤ ∑ k ∈ Finset.range (n + 1),
            A * B * (Nat.multichoose r k * Nat.multichoose s (n - k)) := by
          refine Finset.sum_le_sum ?_
          intro k _hk
          calc
            F k * G (n - k)
                ≤ (A * Nat.multichoose r k) *
                    (B * Nat.multichoose s (n - k)) :=
                  Nat.mul_le_mul (hF k) (hG (n - k))
            _ = A * B *
                    (Nat.multichoose r k * Nat.multichoose s (n - k)) := by
                  ring
    _ = A * B *
          (∑ k ∈ Finset.range (n + 1),
            Nat.multichoose r k * Nat.multichoose s (n - k)) := by
          rw [Finset.mul_sum]
    _ = A * B * Nat.multichoose (r + s) n := by
          rw [← convNat, convNat_multichoose]

private lemma powConvNat_le_mul_multichoose {F : ℕ → ℕ} {A r : ℕ}
    (hF : ∀ n, F n ≤ A * Nat.multichoose r n) :
    ∀ k n, powConvNat F k n ≤ A ^ k * Nat.multichoose (r * k) n := by
  intro k
  induction k with
  | zero =>
      intro n
      cases n with
      | zero => simp [powConvNat, Nat.multichoose_zero_right]
      | succ n => simp [powConvNat, Nat.multichoose_zero_succ]
  | succ k ih =>
      intro n
      show convNat F (powConvNat F k) n ≤
        A ^ (k + 1) * Nat.multichoose (r * (k + 1)) n
      calc
        convNat F (powConvNat F k) n
            ≤ A * A ^ k * Nat.multichoose (r + r * k) n :=
              convNat_le_mul_multichoose hF ih n
        _ = A ^ (k + 1) * Nat.multichoose (r * (k + 1)) n := by
              have hr : r + r * k = r * (k + 1) := by ring
              rw [hr, pow_succ']

private lemma G4Bound_le_multichoose4 (n : ℕ) :
    G4Bound n ≤ 2880 * Nat.multichoose 4 n := by
  have hmc : Nat.multichoose 4 n = Nat.choose (n + 3) 3 := by
    rw [Nat.multichoose_eq]
    have htop : 4 + n - 1 = n + 3 := by omega
    rw [htop]
    simpa [Nat.add_sub_cancel] using
      (Nat.choose_symm (n := n + 3) (k := 3) (by omega : 3 ≤ n + 3))
  rw [hmc]
  unfold G4Bound
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]
    exact Nat.mul_le_mul_left 2880
      (Nat.choose_le_choose 3 (by omega : n + 2 ≤ n + 3))

private lemma G6Bound_le_multichoose6 (n : ℕ) :
    G6Bound n ≤ 120960 * Nat.multichoose 6 n := by
  have hmc : Nat.multichoose 6 n = Nat.choose (n + 5) 5 := by
    rw [Nat.multichoose_eq]
    have htop : 6 + n - 1 = n + 5 := by omega
    rw [htop]
    simpa [Nat.add_sub_cancel] using
      (Nat.choose_symm (n := n + 5) (k := 5) (by omega : 5 ≤ n + 5))
  rw [hmc]
  unfold G6Bound
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]
    exact Nat.mul_le_mul_left 120960
      (Nat.choose_le_choose 5 (by omega : n + 4 ≤ n + 5))

private lemma DeltaBoundTight_le_multichoose12 (n : ℕ) :
    DeltaBoundTight n ≤ 10 ^ 8 * Nat.multichoose 12 n := by
  have hG4sq : ∀ n, convNat G4Bound G4Bound n ≤
      (2880 * 2880) * Nat.multichoose (4 + 4) n := by
    intro n
    exact convNat_le_mul_multichoose G4Bound_le_multichoose4
      G4Bound_le_multichoose4 n
  have hG4cube :
      convNat G4Bound (convNat G4Bound G4Bound) n ≤
        2880 ^ 3 * Nat.multichoose 12 n := by
    have h := convNat_le_mul_multichoose G4Bound_le_multichoose4 hG4sq n
    calc
      convNat G4Bound (convNat G4Bound G4Bound) n
          ≤ 2880 * (2880 * 2880) * Nat.multichoose (4 + (4 + 4)) n := h
      _ = 2880 ^ 3 * Nat.multichoose 12 n := by norm_num [pow_succ]
  have hG6sq :
      convNat G6Bound G6Bound n ≤
        120960 ^ 2 * Nat.multichoose 12 n := by
    have h := convNat_le_mul_multichoose G6Bound_le_multichoose6
      G6Bound_le_multichoose6 n
    calc
      convNat G6Bound G6Bound n
          ≤ 120960 * 120960 * Nat.multichoose (6 + 6) n := h
      _ = 120960 ^ 2 * Nat.multichoose 12 n := by norm_num [pow_succ]
  unfold DeltaBoundTight
  set C := Nat.multichoose 12 n
  set S := convNat G4Bound (convNat G4Bound G4Bound) n +
    convNat G6Bound G6Bound n
  have hS : S ≤ (2880 ^ 3 + 120960 ^ 2) * C := by
    dsimp [S, C]
    calc
      convNat G4Bound (convNat G4Bound G4Bound) n +
          convNat G6Bound G6Bound n
          ≤ 2880 ^ 3 * Nat.multichoose 12 n +
              120960 ^ 2 * Nat.multichoose 12 n :=
            Nat.add_le_add hG4cube hG6sq
      _ = (2880 ^ 3 + 120960 ^ 2) * Nat.multichoose 12 n := by ring
  calc
    S / 1728 + 1
        ≤ ((2880 ^ 3 + 120960 ^ 2) * C) / 1728 + 1 :=
          Nat.add_le_add_right (Nat.div_le_div_right hS) 1
    _ ≤ 10 ^ 8 * C := by
          have hCpos : 0 < C := by
            dsimp [C]
            exact multichoose_pos_of_pos (by norm_num : 0 < 12) n
          have hA : 2880 ^ 3 + 120960 ^ 2 < 1728 * 10 ^ 8 := by norm_num
          have hmul :
              (2880 ^ 3 + 120960 ^ 2) * C < 1728 * (10 ^ 8 * C) := by
            calc
              (2880 ^ 3 + 120960 ^ 2) * C
                  < (1728 * 10 ^ 8) * C :=
                    Nat.mul_lt_mul_of_pos_right hA hCpos
              _ = 1728 * (10 ^ 8 * C) := by ring
          have hdiv : ((2880 ^ 3 + 120960 ^ 2) * C) / 1728 < 10 ^ 8 * C := by
            exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 1728)).2
              (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)
          omega

private lemma qrow_majorant_le_universal (j n : ℕ) (hj : j ≤ 42) :
    convNat (powConvNat G4Bound (3 * j))
      (powConvNat DeltaBoundTight (42 - j)) n ≤
        2880 ^ 126 * Nat.multichoose 504 n := by
  have hE4 := powConvNat_le_mul_multichoose G4Bound_le_multichoose4 (3 * j)
  have hDelta := powConvNat_le_mul_multichoose DeltaBoundTight_le_multichoose12 (42 - j)
  have h := convNat_le_mul_multichoose hE4 hDelta n
  have hconst :
      2880 ^ (3 * j) * (10 ^ 8) ^ (42 - j) ≤ 2880 ^ 126 := by
    have hbase : 10 ^ 8 ≤ 2880 ^ 3 := by norm_num
    have hpow := Nat.pow_le_pow_left hbase (42 - j)
    calc
      2880 ^ (3 * j) * (10 ^ 8) ^ (42 - j)
          ≤ 2880 ^ (3 * j) * (2880 ^ 3) ^ (42 - j) :=
            Nat.mul_le_mul_left _ hpow
      _ = 2880 ^ (3 * j + 3 * (42 - j)) := by
            rw [← pow_mul, ← pow_add]
      _ = 2880 ^ 126 := by
            congr 1
            omega
  calc
    convNat (powConvNat G4Bound (3 * j))
        (powConvNat DeltaBoundTight (42 - j)) n
        ≤ (2880 ^ (3 * j) * (10 ^ 8) ^ (42 - j)) *
            Nat.multichoose (4 * (3 * j) + 12 * (42 - j)) n := h
    _ = (2880 ^ (3 * j) * (10 ^ 8) ^ (42 - j)) *
            Nat.multichoose 504 n := by
          congr 2
          omega
    _ ≤ 2880 ^ 126 * Nat.multichoose 504 n :=
          Nat.mul_le_mul_right _ hconst

/-- A binomial coefficient times its largest binomial-distribution monomial is bounded by
    the full binomial expansion. -/
private lemma choose_mul_pow_mul_pow_le_pow (N K : ℕ) (hK : K ≤ N) :
    Nat.choose N K * K ^ K * (N - K) ^ (N - K) ≤ N ^ N := by
  have hsum := (add_pow K (N - K) N).symm
  have hterm :
      K ^ K * (N - K) ^ (N - K) * Nat.choose N K ≤
        (K + (N - K)) ^ N := by
    rw [← hsum]
    exact Finset.single_le_sum
      (s := Finset.range (N + 1))
      (f := fun m => K ^ m * (N - K) ^ (N - m) * Nat.choose N m)
      (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hK))
  have hKN : K + (N - K) = N := Nat.add_sub_of_le hK
  rw [hKN] at hterm
  calc
    Nat.choose N K * K ^ K * (N - K) ^ (N - K)
        = K ^ K * (N - K) ^ (N - K) * Nat.choose N K := by ring
    _ ≤ N ^ N := hterm

private lemma pow10_mul2 (a b : ℕ) :
    (10 : ℕ) ^ a * 10 ^ b = 10 ^ (a + b) := by
  rw [← pow_add]

private lemma pow10_mul3 (a b c : ℕ) :
    (10 : ℕ) ^ a * 10 ^ b * 10 ^ c = 10 ^ (a + b + c) := by
  rw [pow10_mul2, pow10_mul2]

set_option exponentiation.threshold 300 in
private lemma pow11426_51_le : (11426 : ℕ) ^ 51 ≤ 9 * 10 ^ 206 := by
  norm_num

set_option exponentiation.threshold 500 in
private lemma pow2880_126_le_pow10_436 : (2880 : ℕ) ^ 126 ≤ 10 ^ 436 := by
  norm_num

set_option exponentiation.threshold 2600 in
private lemma pow11426_627_le : (11426 : ℕ) ^ 627 ≤ 2 * 10 ^ 2544 := by
  norm_num

set_option exponentiation.threshold 3900 in
private lemma pow11426_950_le : (11426 : ℕ) ^ 950 ≤ 10 ^ 3855 := by
  norm_num

private lemma pow11426_3528_le :
    (11426 : ℕ) ^ 3528 ≤ 18 * 10 ^ 14315 := by
  have hsplit :
      (11426 : ℕ) ^ 3528 = 11426 ^ 51 * 11426 ^ 627 * (11426 ^ 950) ^ 3 := by
    rw [show 3528 = 51 + 627 + 950 * 3 by norm_num]
    rw [pow_add, pow_add, pow_mul]
  calc
    (11426 : ℕ) ^ 3528
        = 11426 ^ 51 * 11426 ^ 627 * (11426 ^ 950) ^ 3 := hsplit
    _ ≤ (9 * 10 ^ 206) * (2 * 10 ^ 2544) * (10 ^ 3855) ^ 3 :=
        Nat.mul_le_mul
          (Nat.mul_le_mul
            pow11426_51_le
            pow11426_627_le)
          (Nat.pow_le_pow_left pow11426_950_le 3)
    _ = 18 * 10 ^ 14315 := by
        rw [← pow_mul]
        rw [show 3855 * 3 = 11565 by norm_num]
        calc
          9 * 10 ^ 206 * (2 * 10 ^ 2544) * 10 ^ 11565
              = 18 * (10 ^ 206 * 10 ^ 2544 * 10 ^ 11565) := by
                  set A := 10 ^ 206
                  set B := 10 ^ 2544
                  set C := 10 ^ 11565
                  ring
          _ = 18 * 10 ^ 14315 := by
              rw [pow10_mul3]

set_option exponentiation.threshold 300 in
private lemma pow8014_11_le : (8014 : ℕ) ^ 11 ≤ 9 * 10 ^ 42 := by
  norm_num

set_option exponentiation.threshold 2000 in
private lemma pow8014_492_le : (8014 : ℕ) ^ 492 ≤ 5 * 10 ^ 1920 := by
  norm_num

private lemma pow8014_503_le : (8014 : ℕ) ^ 503 ≤ 45 * 10 ^ 1962 := by
  have hsplit : (8014 : ℕ) ^ 503 = 8014 ^ 11 * 8014 ^ 492 := by
    rw [show 503 = 11 + 492 by norm_num, pow_add]
  calc
    (8014 : ℕ) ^ 503 = 8014 ^ 11 * 8014 ^ 492 := hsplit
    _ ≤ (9 * 10 ^ 42) * (5 * 10 ^ 1920) :=
        Nat.mul_le_mul pow8014_11_le pow8014_492_le
    _ = 45 * 10 ^ 1962 := by
        calc
          9 * 10 ^ 42 * (5 * 10 ^ 1920)
              = 45 * (10 ^ 42 * 10 ^ 1920) := by
                  set A := 10 ^ 42
                  set B := 10 ^ 1920
                  ring
          _ = 45 * 10 ^ 1962 := by
              rw [pow10_mul2]

private lemma pow11426_3528_mul_pow8014_503_le :
    (11426 : ℕ) ^ 3528 * 8014 ^ 503 ≤ 10 ^ 16280 := by
  calc
    (11426 : ℕ) ^ 3528 * 8014 ^ 503
        ≤ (18 * 10 ^ 14315) * (45 * 10 ^ 1962) :=
          Nat.mul_le_mul pow11426_3528_le pow8014_503_le
    _ = 810 * 10 ^ 16277 := by
        calc
          18 * 10 ^ 14315 * (45 * 10 ^ 1962)
              = 810 * (10 ^ 14315 * 10 ^ 1962) := by
                  set A := 10 ^ 14315
                  set B := 10 ^ 1962
                  ring
          _ = 810 * 10 ^ 16277 := by
              rw [pow10_mul2]
    _ ≤ 10 ^ 16280 := by
        calc
          810 * 10 ^ 16277 ≤ 10 ^ 3 * 10 ^ 16277 :=
            Nat.mul_le_mul_right _ (by norm_num : 810 ≤ 10 ^ 3)
          _ = 10 ^ 16280 := by
            rw [pow10_mul2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma choose_4031_503_le_pow10_659 :
    Nat.choose 4031 503 ≤ 10 ^ 659 := by
  have hterm := choose_mul_pow_mul_pow_le_pow 4031 503 (by norm_num : 503 ≤ 4031)
  have hsub : 4031 - 503 = 3528 := by norm_num
  rw [hsub] at hterm
  have hA :
      10000 ^ 3528 * 4031 ^ 3528 ≤ 11426 ^ 3528 * 3528 ^ 3528 := by
    calc
      10000 ^ 3528 * 4031 ^ 3528
          = (10000 * 4031) ^ 3528 := by rw [mul_pow]
      _ ≤ (11426 * 3528) ^ 3528 :=
          Nat.pow_le_pow_left (by norm_num : 10000 * 4031 ≤ 11426 * 3528) 3528
      _ = 11426 ^ 3528 * 3528 ^ 3528 := by rw [mul_pow]
  have hB :
      1000 ^ 503 * 4031 ^ 503 ≤ 8014 ^ 503 * 503 ^ 503 := by
    calc
      1000 ^ 503 * 4031 ^ 503
          = (1000 * 4031) ^ 503 := by rw [mul_pow]
      _ ≤ (8014 * 503) ^ 503 :=
          Nat.pow_le_pow_left (by norm_num : 1000 * 4031 ≤ 8014 * 503) 503
      _ = 8014 ^ 503 * 503 ^ 503 := by rw [mul_pow]
  have hscaleEq : 10000 ^ 3528 * 1000 ^ 503 = 10 ^ 15621 := by
    rw [show (10000 : ℕ) = 10 ^ 4 by norm_num,
      show (1000 : ℕ) = 10 ^ 3 by norm_num]
    rw [← pow_mul, ← pow_mul, pow10_mul2]
  have hscaled :
      (10000 ^ 3528 * 1000 ^ 503) * 4031 ^ 4031 ≤
        (10000 ^ 3528 * 1000 ^ 503) *
          (10 ^ 659 * (503 ^ 503 * 3528 ^ 3528)) := by
    calc
      (10000 ^ 3528 * 1000 ^ 503) * 4031 ^ 4031
          = (10000 ^ 3528 * 4031 ^ 3528) *
              (1000 ^ 503 * 4031 ^ 503) := by
        rw [show 4031 = 3528 + 503 by norm_num, pow_add]
        set A := 10000 ^ 3528
        set B := 1000 ^ 503
        set C := 4031 ^ 3528
        set D := 4031 ^ 503
        change (A * B) * (C * D) = (A * C) * (B * D)
        ring
      _ ≤ (11426 ^ 3528 * 3528 ^ 3528) *
            (8014 ^ 503 * 503 ^ 503) :=
        Nat.mul_le_mul hA hB
      _ = (11426 ^ 3528 * 8014 ^ 503) * (503 ^ 503 * 3528 ^ 3528) := by
        set A := 11426 ^ 3528
        set B := 3528 ^ 3528
        set C := 8014 ^ 503
        set D := 503 ^ 503
        change (A * B) * (C * D) = (A * C) * (D * B)
        ring
      _ ≤ 10 ^ 16280 * (503 ^ 503 * 3528 ^ 3528) :=
        Nat.mul_le_mul_right _ pow11426_3528_mul_pow8014_503_le
      _ = 10 ^ 15621 * (10 ^ 659 * (503 ^ 503 * 3528 ^ 3528)) := by
        rw [show 16280 = 15621 + 659 by norm_num, pow_add]
        set D := 503 ^ 503 * 3528 ^ 3528
        change 10 ^ 15621 * 10 ^ 659 * D = 10 ^ 15621 * (10 ^ 659 * D)
        ring
      _ = (10000 ^ 3528 * 1000 ^ 503) *
            (10 ^ 659 * (503 ^ 503 * 3528 ^ 3528)) := by
        rw [hscaleEq]
  have hpow :
      4031 ^ 4031 ≤ 10 ^ 659 * (503 ^ 503 * 3528 ^ 3528) :=
    Nat.le_of_mul_le_mul_left hscaled (by positivity)
  have hdenpos : 0 < 503 ^ 503 * 3528 ^ 3528 := by positivity
  have hchooseScaled :
      Nat.choose 4031 503 * (503 ^ 503 * 3528 ^ 3528) ≤
        10 ^ 659 * (503 ^ 503 * 3528 ^ 3528) := by
    calc
      Nat.choose 4031 503 * (503 ^ 503 * 3528 ^ 3528)
          = Nat.choose 4031 503 * 503 ^ 503 * 3528 ^ 3528 := by
            rw [Nat.mul_assoc]
      _ ≤ 4031 ^ 4031 := hterm
      _ ≤ 10 ^ 659 * (503 ^ 503 * 3528 ^ 3528) := hpow
  exact Nat.le_of_mul_le_mul_right hchooseScaled hdenpos

set_option exponentiation.threshold 1700 in
private lemma pow1171_503_le : (1171 : ℕ) ^ 503 ≤ 4 * 10 ^ 1543 := by
  norm_num

set_option exponentiation.threshold 200 in
private lemma pow69_86_le : (69 : ℕ) ^ 86 ≤ 2 * 10 ^ 158 := by
  norm_num

set_option maxRecDepth 10000 in
private lemma pow1171_503_mul_pow69_86_le :
    (1171 : ℕ) ^ 503 * 69 ^ 86 ≤ 10 ^ 1702 := by
  calc
    (1171 : ℕ) ^ 503 * 69 ^ 86
        ≤ (4 * 10 ^ 1543) * (2 * 10 ^ 158) :=
      Nat.mul_le_mul pow1171_503_le pow69_86_le
    _ = 8 * (10 ^ 1543 * 10 ^ 158) := by
      set A := 10 ^ 1543
      set B := 10 ^ 158
      ring
    _ = 8 * 10 ^ 1701 := by
      rw [pow10_mul2]
    _ ≤ 10 ^ 1 * 10 ^ 1701 :=
      Nat.mul_le_mul_right _ (by norm_num : 8 ≤ 10 ^ 1)
    _ = 10 ^ 1702 := by
      rw [pow10_mul2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma choose_589_503_le_pow10_107 :
    Nat.choose 589 503 ≤ 10 ^ 107 := by
  have hterm := choose_mul_pow_mul_pow_le_pow 589 503 (by norm_num : 503 ≤ 589)
  have hsub : 589 - 503 = 86 := by norm_num
  rw [hsub] at hterm
  have hA :
      1000 ^ 503 * 589 ^ 503 ≤ 1171 ^ 503 * 503 ^ 503 := by
    calc
      1000 ^ 503 * 589 ^ 503
          = (1000 * 589) ^ 503 := by rw [mul_pow]
      _ ≤ (1171 * 503) ^ 503 :=
          Nat.pow_le_pow_left (by norm_num : 1000 * 589 ≤ 1171 * 503) 503
      _ = 1171 ^ 503 * 503 ^ 503 := by rw [mul_pow]
  have hB :
      10 ^ 86 * 589 ^ 86 ≤ 69 ^ 86 * 86 ^ 86 := by
    calc
      10 ^ 86 * 589 ^ 86
          = (10 * 589) ^ 86 := by rw [mul_pow]
      _ ≤ (69 * 86) ^ 86 :=
          Nat.pow_le_pow_left (by norm_num : 10 * 589 ≤ 69 * 86) 86
      _ = 69 ^ 86 * 86 ^ 86 := by rw [mul_pow]
  have hscaleEq : 1000 ^ 503 * 10 ^ 86 = 10 ^ 1595 := by
    rw [show (1000 : ℕ) = 10 ^ 3 by norm_num]
    rw [← pow_mul, pow10_mul2]
  have hscaled :
      (1000 ^ 503 * 10 ^ 86) * 589 ^ 589 ≤
        (1000 ^ 503 * 10 ^ 86) *
          (10 ^ 107 * (503 ^ 503 * 86 ^ 86)) := by
    calc
      (1000 ^ 503 * 10 ^ 86) * 589 ^ 589
          = (1000 ^ 503 * 589 ^ 503) * (10 ^ 86 * 589 ^ 86) := by
        rw [show 589 = 503 + 86 by norm_num, pow_add]
        set A := 1000 ^ 503
        set B := 10 ^ 86
        set C := 589 ^ 503
        set D := 589 ^ 86
        change (A * B) * (C * D) = (A * C) * (B * D)
        ring
      _ ≤ (1171 ^ 503 * 503 ^ 503) * (69 ^ 86 * 86 ^ 86) :=
        Nat.mul_le_mul hA hB
      _ = (1171 ^ 503 * 69 ^ 86) * (503 ^ 503 * 86 ^ 86) := by
        set A := 1171 ^ 503
        set B := 503 ^ 503
        set C := 69 ^ 86
        set D := 86 ^ 86
        change (A * B) * (C * D) = (A * C) * (B * D)
        ring
      _ ≤ 10 ^ 1702 * (503 ^ 503 * 86 ^ 86) :=
        Nat.mul_le_mul_right _ pow1171_503_mul_pow69_86_le
      _ = 10 ^ 1595 * (10 ^ 107 * (503 ^ 503 * 86 ^ 86)) := by
        rw [show 1702 = 1595 + 107 by norm_num, pow_add]
        set D := 503 ^ 503 * 86 ^ 86
        change 10 ^ 1595 * 10 ^ 107 * D = 10 ^ 1595 * (10 ^ 107 * D)
        ring
      _ = (1000 ^ 503 * 10 ^ 86) *
          (10 ^ 107 * (503 ^ 503 * 86 ^ 86)) := by
        rw [hscaleEq]
  have hpow :
      589 ^ 589 ≤ 10 ^ 107 * (503 ^ 503 * 86 ^ 86) :=
    Nat.le_of_mul_le_mul_left hscaled (by positivity)
  have hdenpos : 0 < 503 ^ 503 * 86 ^ 86 := by positivity
  have hchooseScaled :
      Nat.choose 589 503 * (503 ^ 503 * 86 ^ 86) ≤
        10 ^ 107 * (503 ^ 503 * 86 ^ 86) := by
    calc
      Nat.choose 589 503 * (503 ^ 503 * 86 ^ 86)
          = Nat.choose 589 503 * 503 ^ 503 * 86 ^ 86 := by
            rw [Nat.mul_assoc]
      _ ≤ 589 ^ 589 := hterm
      _ ≤ 10 ^ 107 * (503 ^ 503 * 86 ^ 86) := hpow
  exact Nat.le_of_mul_le_mul_right hchooseScaled hdenpos

private lemma multichoose504_big_bound {n : ℕ}
    (hn : n < phi41Level41SturmBound) :
    Nat.multichoose 504 n ≤ 10 ^ 659 := by
  have hmc : Nat.multichoose 504 n = Nat.choose (n + 503) 503 := by
    rw [Nat.multichoose_eq]
    have htop : 504 + n - 1 = n + 503 := by omega
    rw [htop]
    simpa [Nat.add_sub_cancel] using
      (Nat.choose_symm (n := n + 503) (k := 503) (by omega : 503 ≤ n + 503))
  rw [hmc]
  calc
    Nat.choose (n + 503) 503 ≤ Nat.choose 4031 503 :=
      Nat.choose_le_choose 503 (by
        unfold phi41Level41SturmBound at hn
        omega)
    _ ≤ 10 ^ 659 := choose_4031_503_le_pow10_659

private lemma multichoose504_pull_bound {n : ℕ}
    (hn : n < (phi41Level41SturmBound + 40) / 41) :
    Nat.multichoose 504 n ≤ 10 ^ 107 := by
  have hmc : Nat.multichoose 504 n = Nat.choose (n + 503) 503 := by
    rw [Nat.multichoose_eq]
    have htop : 504 + n - 1 = n + 503 := by omega
    rw [htop]
    simpa [Nat.add_sub_cancel] using
      (Nat.choose_symm (n := n + 503) (k := 503) (by omega : 503 ≤ n + 503))
  rw [hmc]
  calc
    Nat.choose (n + 503) 503 ≤ Nat.choose 589 503 :=
      Nat.choose_le_choose 503 (by
        unfold phi41Level41SturmBound at hn
        omega)
    _ ≤ 10 ^ 107 := choose_589_503_le_pow10_107

/-- Q_j row bound for the big side (n ≤ 3528). -/
def QrowBigBound : ℕ := 10 ^ 1095

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Qrow_bound_big (j n : ℕ) (hj : j ≤ 42) (hn : n < phi41Level41SturmBound) :
    |PowerSeries.coeff (R := ℤ) n
      ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))| ≤
        (QrowBigBound : ℤ) := by
  have hmaj := maj_Qrow j hj n
  have hnat :
      convNat (powConvNat G4Bound (3 * j))
        (powConvNat DeltaBoundTight (42 - j)) n ≤ QrowBigBound := by
    have hmajor := qrow_majorant_le_universal j n hj
    have hprod :
        2880 ^ 126 * Nat.multichoose 504 n ≤ 10 ^ 436 * 10 ^ 659 :=
      Nat.mul_le_mul
        pow2880_126_le_pow10_436
        (multichoose504_big_bound hn)
    have hpow : 10 ^ 436 * 10 ^ 659 = QrowBigBound := by
      unfold QrowBigBound
      rw [pow10_mul2]
    exact hmajor.trans (by simpa [hpow] using hprod)
  exact hmaj.trans (Int.ofNat_le.mpr hnat)

/-- Q_j row bound for the pullback side (n ≤ 86). -/
def QrowPullBound : ℕ := 10 ^ 545

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Qrow_bound_pull (j n : ℕ) (hj : j ≤ 42)
    (hn : n < (phi41Level41SturmBound + 40) / 41) :
    |PowerSeries.coeff (R := ℤ) n
      ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))| ≤
        (QrowPullBound : ℤ) := by
  have hmaj := maj_Qrow j hj n
  have hnat :
      convNat (powConvNat G4Bound (3 * j))
        (powConvNat DeltaBoundTight (42 - j)) n ≤ QrowPullBound := by
    have hmajor := qrow_majorant_le_universal j n hj
    have hprod :
        2880 ^ 126 * Nat.multichoose 504 n ≤ 10 ^ 436 * 10 ^ 107 :=
      Nat.mul_le_mul
        pow2880_126_le_pow10_436
        (multichoose504_pull_bound hn)
    have hslack : 10 ^ 436 * 10 ^ 107 ≤ QrowPullBound := by
      have hpow107 :
          (10 : ℕ) ^ 107 ≤ 10 ^ 109 :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num : 107 ≤ 109)
      have hmul : 10 ^ 436 * 10 ^ 107 ≤ 10 ^ 436 * 10 ^ 109 :=
        Nat.mul_le_mul_left _ hpow107
      have hpow : 10 ^ 436 * 10 ^ 109 = QrowPullBound := by
        unfold QrowPullBound
        rw [pow10_mul2]
      exact hmul.trans (le_of_eq hpow)
    exact (hmajor.trans hprod).trans hslack
  exact hmaj.trans (Int.ofNat_le.mpr hnat)

/-! ## Layer 4: Final hbound -/

/-- L¹ norm of the sparse polynomial coefficients. -/
def phi41SparseCoeffL1 : ℕ := 430214329162130934998014102783361653658762732413094968916550882973547953622830262212842588534662719039444865306033970385222128557480041050477161942460951747267724218572856686366457354033833183729895066298456075383665917627855402679807422318295127406075930386573946224224589581427869341548900894574793047751098726891135150527133456232175958143472802273850895591408228388096697078890752446780701243687850587368626490269011874194961146618896275452020396881788950421918688605914846416454068185912748488270029811530696637748568712369220658313129280786402819547027841719551741165076517643725037564882558190925529

private def phi41SparseCoeffRowL1 (x : ℕ) : ℕ :=
  (Finset.range 43).sum (fun y =>
    Int.natAbs
      ((phi41SparseCoeffMatrixArray.getD x (Array.replicate 43 0)).getD y 0))

private def phi41SparseCoeffMatrixL1 : ℕ :=
  (Finset.range 43).sum phi41SparseCoeffRowL1

private lemma linearCombinationFromCoeffMatrixArray_bound
    {N x n : ℕ} {Q : Array (Array ℤ)} (hn : n < N) (hx : x ≤ 42)
    {B : ℕ}
    (hQ : ∀ y : ℕ, y ≤ 42 →
      |truncCoeffArrayAt (Q.getD y (zeroTruncCoeffArray N)) n| ≤ (B : ℤ)) :
    |truncCoeffArrayAt
      (linearCombinationFromCoeffMatrixArray N x Q phi41SparseCoeffMatrixArray) n| ≤
        (phi41RowL1Cert x * B : ℤ) := by
  rw [truncCoeffArrayAt_linearCombinationFromCoeffMatrixArray hn]
  rw [sumRangeFromZ_zero_eq_finset_sum]
  calc
    |∑ y ∈ Finset.range 43,
        (phi41SparseCoeffMatrixArray.getD x (Array.replicate 43 0)).getD y 0 *
          truncCoeffArrayAt (Q.getD y (zeroTruncCoeffArray N)) n|
        ≤ ∑ y ∈ Finset.range 43,
            |(phi41SparseCoeffMatrixArray.getD x (Array.replicate 43 0)).getD y 0 *
              truncCoeffArrayAt (Q.getD y (zeroTruncCoeffArray N)) n| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ Finset.range 43,
          ((Int.natAbs
            ((phi41SparseCoeffMatrixArray.getD x (Array.replicate 43 0)).getD y 0) *
              B : ℕ) : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro y hy
          have hy42 : y ≤ 42 := by
            have hylt : y < 43 := Finset.mem_range.mp hy
            omega
          rw [abs_mul, Int.abs_eq_natAbs]
          exact mul_le_mul_of_nonneg_left (hQ y hy42) (by positivity)
      _ = (phi41RowL1Cert x * B : ℤ) := by
            have hnat :
                (∑ y ∈ Finset.range 43,
                  Int.natAbs
                    ((phi41SparseCoeffMatrixArray.getD x
                      (Array.replicate 43 0)).getD y 0) * B) =
                  phi41RowL1Cert x * B := by
              rw [← phi41RowL1Cert_correct x hx, Finset.sum_mul]
            exact_mod_cast hnat

private lemma phi41QrowArray_bound_big {j n : ℕ} (hj : j ≤ 42)
    (hn : n < phi41Level41SturmBound) :
    |truncCoeffArrayAt
      ((phi41QRecurrenceRowsArray phi41Level41SturmBound).getD j
        (zeroTruncCoeffArray phi41Level41SturmBound)) n| ≤
        (QrowBigBound : ℤ) := by
  rw [phi41_Qrow_eq_closed_form j hj n hn]
  exact Qrow_bound_big j n hj hn

private lemma phi41QrowArray_bound_pull {j n : ℕ} (hj : j ≤ 42)
    (hn : n < (phi41Level41SturmBound + 40) / 41) :
    |truncCoeffArrayAt
      ((phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41)).getD j
        (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))) n| ≤
        (QrowPullBound : ℤ) := by
  rw [phi41_Qrow_eq_closed_form_of_lt
    ((phi41Level41SturmBound + 40) / 41) j hj n hn]
  exact Qrow_bound_pull j n hj hn

-- Heavy computation: bounds each of 43 row contributions via the majorant chain
-- TODO: kernel computation too heavy (>5h on uisai2). Needs restructured proof
-- (e.g. precomputed certificate or mod-p approach). The Vandermonde majorant
-- chain (Qrow_bound_big/pull) is the mathematical content; this assembly is mechanical.
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private lemma phi41Contribution_bound (x n : ℕ)
    (hx : x ≤ 42) (hn : n < phi41Level41SturmBound) :
    |truncCoeffArrayAt
      (mulQPullback41CompressedTruncCoeffArray phi41Level41SturmBound
        (((phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41)).getD x
          (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))))
        (linearCombinationFromCoeffMatrixArray phi41Level41SturmBound x
          (phi41QRecurrenceRowsArray phi41Level41SturmBound)
          phi41SparseCoeffMatrixArray)) n| ≤
        (87 * phi41RowL1Cert x * QrowBigBound * QrowPullBound : ℤ) := by
  rw [truncCoeffArrayAt_mulQPullback41CompressedTruncCoeffArray hn]
  rw [sumRangeFromZ_zero_eq_finset_sum]
  have hM : (phi41Level41SturmBound + 40) / 41 = 87 := by
    unfold phi41Level41SturmBound
    norm_num
  have hcard : (Finset.range (n / 41 + 1)).card ≤ 87 := by
    simp
    have hndiv : n / 41 < 87 := by
      apply Nat.div_lt_of_lt_mul
      unfold phi41Level41SturmBound at hn
      omega
    omega
  calc
    |∑ m ∈ Finset.range (n / 41 + 1),
        truncCoeffArrayAt
          ((phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41)).getD x
            (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))) m *
          truncCoeffArrayAt
            (linearCombinationFromCoeffMatrixArray phi41Level41SturmBound x
              (phi41QRecurrenceRowsArray phi41Level41SturmBound)
              phi41SparseCoeffMatrixArray) (n - 41 * m)|
        ≤ ∑ m ∈ Finset.range (n / 41 + 1),
            |truncCoeffArrayAt
                ((phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41)).getD x
                  (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))) m *
              truncCoeffArrayAt
                (linearCombinationFromCoeffMatrixArray phi41Level41SturmBound x
                  (phi41QRecurrenceRowsArray phi41Level41SturmBound)
                  phi41SparseCoeffMatrixArray) (n - 41 * m)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.range (n / 41 + 1),
          (phi41RowL1Cert x * QrowBigBound * QrowPullBound : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          have hm_le : m ≤ n / 41 := by
            have hmlt : m < n / 41 + 1 := Finset.mem_range.mp hm
            omega
          have hmM : m < (phi41Level41SturmBound + 40) / 41 := by
            rw [hM]
            have hndiv : n / 41 < 87 := by
              apply Nat.div_lt_of_lt_mul
              unfold phi41Level41SturmBound at hn
              omega
            omega
          have hidx : n - 41 * m < phi41Level41SturmBound := by
            omega
          have hpull := phi41QrowArray_bound_pull (j := x) (n := m) hx hmM
          have hlin :
              |truncCoeffArrayAt
                (linearCombinationFromCoeffMatrixArray phi41Level41SturmBound x
                  (phi41QRecurrenceRowsArray phi41Level41SturmBound)
                  phi41SparseCoeffMatrixArray) (n - 41 * m)| ≤
                (phi41RowL1Cert x * QrowBigBound : ℤ) := by
            exact linearCombinationFromCoeffMatrixArray_bound hidx hx
              (B := QrowBigBound)
              (fun y hy => phi41QrowArray_bound_big (j := y) (n := n - 41 * m) hy hidx)
          rw [abs_mul]
          calc
            |truncCoeffArrayAt
                ((phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41)).getD x
                  (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))) m| *
              |truncCoeffArrayAt
                (linearCombinationFromCoeffMatrixArray phi41Level41SturmBound x
                  (phi41QRecurrenceRowsArray phi41Level41SturmBound)
                  phi41SparseCoeffMatrixArray) (n - 41 * m)|
                ≤ (QrowPullBound : ℤ) *
                    (phi41RowL1Cert x * QrowBigBound : ℤ) :=
                  mul_le_mul hpull hlin (abs_nonneg _) (by positivity)
            _ = (phi41RowL1Cert x * QrowBigBound * QrowPullBound : ℤ) := by ring
    _ ≤ (87 * phi41RowL1Cert x * QrowBigBound * QrowPullBound : ℤ) := by
          rw [Finset.sum_const]
          simp only [nsmul_eq_mul]
          have hcard_int : ((Finset.range (n / 41 + 1)).card : ℤ) ≤ (87 : ℤ) := by
            exact Int.ofNat_le.mpr hcard
          calc ((Finset.range (n / 41 + 1)).card : ℤ) *
                (↑(phi41RowL1Cert x) * ↑QrowBigBound * ↑QrowPullBound)
              ≤ 87 * (↑(phi41RowL1Cert x) * ↑QrowBigBound * ↑QrowPullBound) :=
                mul_le_mul_of_nonneg_right hcard_int (by positivity)
            _ = 87 * ↑(phi41RowL1Cert x) * ↑QrowBigBound * ↑QrowPullBound := by
                set a := (phi41RowL1Cert x : ℤ)
                set b := (QrowBigBound : ℤ)
                set c := (QrowPullBound : ℤ)
                ring

/-- Final height bound: 87 · H · QrowBigBound · QrowPullBound. -/
def phi41HeightBound : ℕ :=
  87 * phi41TotalL1Cert * QrowBigBound * QrowPullBound

set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
/-- The analytical hbound — zero native_decide. -/
theorem phi41_final_coeff_bound (n : ℕ) (hn : n < phi41Level41SturmBound) :
    |truncCoeffArrayAt
      (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
        (phi41HeightBound : ℤ) := by
  rw [show phi41Level41RecurrenceCoeffArray phi41Level41SturmBound =
      phi41Level41RecurrenceCoeffArrayFromRows phi41Level41SturmBound
        ((phi41Level41SturmBound + 40) / 41)
        (phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41))
        (phi41QRecurrenceRowsArray phi41Level41SturmBound) by rfl]
  rw [truncCoeffArrayAt_phi41Level41RecurrenceCoeffArrayFromRows hn]
  unfold phi41Level41RecurrenceCoeffArrayFromRowsCoeff
  rw [sumRangeFromZ_zero_eq_finset_sum]
  calc
    |∑ x ∈ Finset.range 43,
        truncCoeffArrayAt
          (mulQPullback41CompressedTruncCoeffArray phi41Level41SturmBound
            ((phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41)).getD x
              (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41)))
            (linearCombinationFromCoeffMatrixArray phi41Level41SturmBound x
              (phi41QRecurrenceRowsArray phi41Level41SturmBound)
              phi41SparseCoeffMatrixArray)) n|
        ≤ ∑ x ∈ Finset.range 43,
            |truncCoeffArrayAt
              (mulQPullback41CompressedTruncCoeffArray phi41Level41SturmBound
                ((phi41QRecurrenceRowsArray ((phi41Level41SturmBound + 40) / 41)).getD x
                  (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41)))
                (linearCombinationFromCoeffMatrixArray phi41Level41SturmBound x
                  (phi41QRecurrenceRowsArray phi41Level41SturmBound)
                  phi41SparseCoeffMatrixArray)) n| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ Finset.range 43,
          (87 * phi41RowL1Cert x * QrowBigBound * QrowPullBound : ℤ) := by
          refine Finset.sum_le_sum ?_
          intro x hxmem
          have hx : x ≤ 42 := by
            have hxlt : x < 43 := Finset.mem_range.mp hxmem
            omega
          exact phi41Contribution_bound x n hx hn
    _ = (87 * phi41TotalL1Cert * QrowBigBound * QrowPullBound : ℤ) := by
          have hrows :
              (∑ x ∈ Finset.range 43, phi41RowL1Cert x) =
                phi41TotalL1Cert := by
            rw [← phi41TotalL1Cert_correct]
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hx42 : x ≤ 42 := by
              have hxlt : x < 43 := Finset.mem_range.mp hx
              omega
            exact (phi41RowL1Cert_correct x hx42).symm
          have hnat :
              (∑ x ∈ Finset.range 43,
                  87 * phi41RowL1Cert x * QrowBigBound * QrowPullBound) =
                87 * phi41TotalL1Cert * QrowBigBound * QrowPullBound := by
            calc
              (∑ x ∈ Finset.range 43,
                  87 * phi41RowL1Cert x * QrowBigBound * QrowPullBound : ℕ)
                = (∑ x ∈ Finset.range 43, phi41RowL1Cert x) *
                    (87 * QrowBigBound * QrowPullBound) := by
                    rw [show (∑ x ∈ Finset.range 43,
                        87 * phi41RowL1Cert x * QrowBigBound * QrowPullBound : ℕ) =
                      (∑ x ∈ Finset.range 43, phi41RowL1Cert x * (87 * QrowBigBound * QrowPullBound)) from
                      Finset.sum_congr rfl (fun x _ => by ring),
                      Finset.sum_mul (f := phi41RowL1Cert)]
              _ = phi41TotalL1Cert * (87 * QrowBigBound * QrowPullBound) := by
                    rw [hrows]
              _ = 87 * phi41TotalL1Cert * QrowBigBound * QrowPullBound := by ring
          exact_mod_cast hnat
    _ = (phi41HeightBound : ℤ) := by
          unfold phi41HeightBound; push_cast; ring

end Ripple.Number.Modular
