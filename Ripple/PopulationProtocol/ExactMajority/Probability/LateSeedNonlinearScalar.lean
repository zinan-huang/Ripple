-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSeedNonlinearScalar.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingStoppedDebt

/-!
# An adapted nonlinear service tail

The exponentially transformed state is killed on reaching the target.
Its one-step estimate uses the conditional probability of an actual strict
decrease. No independent geometric variables, and no conditioning on future
gate survival, enter the proof.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

def nonlinearServiceRate (N : ℝ) (j : ℕ) : ℝ := 2 * (j : ℝ) ^ 2 / N

def nonlinearDiscount (N : ℝ) (b : ℕ) : ℝ := (b : ℝ) ^ 2 / (2 * N)

def nonlinearPotential (b j : ℕ) : ℝ :=
  if b < j then Real.exp ((b : ℝ) / 3 - (b : ℝ) ^ 2 / (3 * (j : ℝ))) else 0

theorem nonlinearPotential_nonneg (b j : ℕ) : 0 ≤ nonlinearPotential b j := by
  unfold nonlinearPotential
  split_ifs <;> positivity

theorem nonlinearPotential_upper (b j : ℕ) :
    nonlinearPotential b j ≤ Real.exp ((b : ℝ) / 3) := by
  unfold nonlinearPotential
  split_ifs with h
  · apply Real.exp_le_exp.mpr
    have : 0 ≤ (b : ℝ) ^ 2 / (3 * (j : ℝ)) := by positivity
    linarith
  · exact Real.exp_nonneg _

theorem nonlinearPotential_mono (b : ℕ) : Monotone (nonlinearPotential b) := by
  intro j k hjk
  by_cases hj : b < j
  · have hk : b < k := hj.trans_le hjk
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hjkr : (j : ℝ) ≤ k := by exact_mod_cast hjk
    have hquot :
        (b : ℝ) ^ 2 / (3 * (k : ℝ)) ≤ (b : ℝ) ^ 2 / (3 * (j : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_nonneg (sq_nonneg (b : ℝ)) (sub_nonneg.mpr hjkr)]
    simp only [nonlinearPotential, if_pos hj, if_pos hk]
    exact Real.exp_le_exp.mpr (by linarith)
  · simp only [nonlinearPotential, if_neg hj]
    exact nonlinearPotential_nonneg b k

theorem nonlinearPotential_one_le {b j : ℕ} (hj : b < j) :
    1 ≤ nonlinearPotential b j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hbcast : (b : ℝ) ≤ j := by exact_mod_cast hj.le
  have hquot : (b : ℝ) ^ 2 / (3 * (j : ℝ)) ≤ (b : ℝ) / 3 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (j : ℝ))).2
    nlinarith [mul_nonneg (Nat.cast_nonneg b) (sub_nonneg.mpr hbcast)]
  simp only [nonlinearPotential, if_pos hj]
  calc
    1 = Real.exp 0 := by rw [Real.exp_zero]
    _ ≤ Real.exp ((b : ℝ) / 3 - (b : ℝ) ^ 2 / (3 * (j : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith)

theorem nonlinearPotential_gap_nonneg (b j : ℕ) :
    0 ≤ nonlinearPotential b j - nonlinearPotential b (j - 1) :=
  sub_nonneg.mpr (nonlinearPotential_mono b (Nat.sub_le j 1))

private theorem reciprocal_exp_bound {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 / (1 + u) := by
  have he : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hi := one_div_le_one_div_of_le (by linarith : 0 < 1 + u) he
  simpa only [Real.exp_neg, one_div] using hi

/-- The state potential loses at least the required fixed fraction in one
step when the strict-decrease probability is the quadratic service rate. -/
theorem nonlinearPotential_service_loss (N : ℝ) (hN : 0 < N)
    (b j : ℕ) (hb : 0 < b) :
    nonlinearDiscount N b * nonlinearPotential b j ≤
      nonlinearServiceRate N j *
        (nonlinearPotential b j - nonlinearPotential b (j - 1)) := by
  by_cases hj : b < j
  · have hjone : 1 ≤ j := by omega
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hjpred : (0 : ℝ) < (j : ℝ) - 1 := by
      have : (2 : ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
      linarith
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub hjone, Nat.cast_one]
    let u : ℝ := (b : ℝ) ^ 2 / (3 * (j : ℝ) * ((j : ℝ) - 1))
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hupos : 0 < 1 + u := by linarith
    have hprev :
        nonlinearPotential b (j - 1) ≤ nonlinearPotential b j * Real.exp (-u) := by
      by_cases hp : b < j - 1
      · simp only [nonlinearPotential, if_pos hp, if_pos hj, hcast]
        rw [← Real.exp_add]
        apply le_of_eq
        congr 1
        dsimp [u]
        field_simp [hjpos.ne', hjpred.ne']
        <;> ring
      · rw [nonlinearPotential, if_neg hp]
        exact mul_nonneg (nonlinearPotential_nonneg b j) (Real.exp_nonneg _)
    have hprev' :
        nonlinearPotential b (j - 1) ≤ nonlinearPotential b j / (1 + u) := by
      calc
        nonlinearPotential b (j - 1) ≤
            nonlinearPotential b j * Real.exp (-u) := hprev
        _ ≤ nonlinearPotential b j * (1 / (1 + u)) :=
          mul_le_mul_of_nonneg_left (reciprocal_exp_bound hu)
            (nonlinearPotential_nonneg b j)
        _ = nonlinearPotential b j / (1 + u) := by ring
    have hgap :
        nonlinearPotential b j * (u / (1 + u)) ≤
          nonlinearPotential b j - nonlinearPotential b (j - 1) := by
      have hid :
          nonlinearPotential b j * (u / (1 + u)) =
            nonlinearPotential b j - nonlinearPotential b j / (1 + u) := by
        field_simp [hupos.ne']
        <;> ring
      rw [hid]
      linarith
    have hbcast : (b : ℝ) ≤ j := by exact_mod_cast hj.le
    have hsquare : (b : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg b) hbcast 2
    have hnum : 0 ≤ (j : ℝ) ^ 2 + 3 * (j : ℝ) - (b : ℝ) ^ 2 := by
      nlinarith
    have hid :
        nonlinearServiceRate N j * u - nonlinearDiscount N b * (1 + u) =
          (b : ℝ) ^ 2 * ((j : ℝ) ^ 2 + 3 * (j : ℝ) - (b : ℝ) ^ 2) /
            (6 * N * (j : ℝ) * ((j : ℝ) - 1)) := by
      dsimp [nonlinearServiceRate, nonlinearDiscount, u]
      field_simp [hN.ne', hjpos.ne', hjpred.ne']
      <;> ring
    have hrel :
        nonlinearDiscount N b ≤ nonlinearServiceRate N j * u / (1 + u) := by
      apply (le_div_iff₀ hupos).2
      have hnonneg :
          0 ≤ nonlinearServiceRate N j * u - nonlinearDiscount N b * (1 + u) := by
        rw [hid]
        exact div_nonneg (mul_nonneg (sq_nonneg (b : ℝ)) hnum) (by positivity)
      linarith
    have hrate : 0 ≤ nonlinearServiceRate N j := by
      unfold nonlinearServiceRate
      positivity
    calc
      nonlinearDiscount N b * nonlinearPotential b j ≤
          (nonlinearServiceRate N j * u / (1 + u)) * nonlinearPotential b j :=
        mul_le_mul_of_nonneg_right hrel (nonlinearPotential_nonneg b j)
      _ = nonlinearServiceRate N j * (nonlinearPotential b j * (u / (1 + u))) := by
        ring
      _ ≤ nonlinearServiceRate N j *
          (nonlinearPotential b j - nonlinearPotential b (j - 1)) :=
        mul_le_mul_of_nonneg_left hgap hrate
  · have hp : ¬ b < j - 1 := by omega
    simp only [nonlinearPotential, if_neg hj, if_neg hp, sub_self, mul_zero, le_refl]

private theorem nonlinearPotential_step {b j k : ℕ} (hkj : k ≤ j) :
    nonlinearPotential b k ≤ nonlinearPotential b j -
      (nonlinearPotential b j - nonlinearPotential b (j - 1)) *
        (if k < j then (1 : ℝ) else 0) := by
  by_cases hlt : k < j
  · rw [if_pos hlt, mul_one]
    have hprev := nonlinearPotential_mono b (show k ≤ j - 1 by omega)
    linarith
  · simp only [if_neg hlt, mul_zero, sub_zero]
    exact nonlinearPotential_mono b hkj

/-- The upper role-density gate ensures that every geometric comparison
parameter is a probability. This is deliberately retained in the interface. -/
theorem nonlinear_role_density_cap (n M : ℕ) (hn : 3 ≤ n)
    (hrole : 25 * M ≤ 13 * n) :
    2 * (M : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  have hncast : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hrolecast : 25 * (M : ℝ) ≤ 13 * (n : ℝ) := by exact_mod_cast hrole
  have hM : (M : ℝ) ≤ 13 * (n : ℝ) / 25 := by linarith
  have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg M) hM 2
  have hnprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 3) :=
    mul_nonneg (Nat.cast_nonneg n) (by linarith)
  nlinarith

theorem nonlinearServiceRate_le_one {N : ℝ} (hN : 0 < N)
    {M j : ℕ} (hcap : 2 * (M : ℝ) ^ 2 ≤ N) (hj : j ≤ M) :
    nonlinearServiceRate N j ≤ 1 := by
  have hsquare : (j : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg j) (by exact_mod_cast hj) 2
  unfold nonlinearServiceRate
  apply (div_le_iff₀ hN).2
  nlinarith

theorem nonlinearDiscount_le_one {N : ℝ} (hN : 0 < N)
    {M b : ℕ} (hcap : 2 * (M : ℝ) ^ 2 ≤ N) (hb : b ≤ M) :
    nonlinearDiscount N b ≤ 1 := by
  have hsquare : (b : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg b) (by exact_mod_cast hb) 2
  unfold nonlinearDiscount
  apply (div_le_iff₀ (by positivity : 0 < 2 * N)).2
  nlinarith [sq_nonneg (M : ℝ)]

section Adapted

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m}

private theorem nonlinear_nat_transform_integrable
    {X : Ω → ℕ} {M : ℕ} (hX : Measurable X)
    (hM : ∀ᵐ ω ∂μ, X ω ≤ M) (f : ℕ → ℝ) :
    Integrable (fun ω => f (X ω)) μ := by
  refine Integrable.of_bound
    (((measurable_of_countable f).comp hX).stronglyMeasurable.aestronglyMeasurable)
    (∑ j ∈ Finset.range (M + 1), ‖f j‖) ?_
  filter_upwards [hM] with ω hω
  exact Finset.single_le_sum (fun j _ => norm_nonneg (f j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hω))

private theorem nonlinear_moment_step
    (J : ℕ → Ω → ℕ) (M b : ℕ) (N : ℝ) (hN : 0 < N) (hb : 0 < b)
    (hJ : ∀ t, StronglyMeasurable[ℱ t] (J t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, J t ω ≤ M)
    (hmono : ∀ t, ∀ᵐ ω ∂μ, J (t + 1) ω ≤ J t ω)
    (hdeath : ∀ t, (fun ω => nonlinearServiceRate N (J t ω)) ≤ᵐ[μ]
      μ[fun ω => if J (t + 1) ω < J t ω then (1 : ℝ) else 0 | ℱ t])
    (t : ℕ) :
    (∫ ω, nonlinearPotential b (J (t + 1) ω) ∂μ) ≤
      (1 - nonlinearDiscount N b) * ∫ ω, nonlinearPotential b (J t ω) ∂μ := by
  let V : ℕ → Ω → ℝ := fun s ω => nonlinearPotential b (J s ω)
  let D : Ω → ℝ :=
    fun ω => nonlinearPotential b (J t ω) - nonlinearPotential b (J t ω - 1)
  let B : Ω → ℝ := fun ω => if J (t + 1) ω < J t ω then 1 else 0
  have hVsm (s : ℕ) : StronglyMeasurable[ℱ s] (V s) :=
    ((measurable_of_countable (nonlinearPotential b)).comp (hJ s).measurable).stronglyMeasurable
  have hVint (s : ℕ) : Integrable (V s) μ :=
    nonlinear_nat_transform_integrable ((hJ s).mono (ℱ.le s)).measurable
      (hbound s) (nonlinearPotential b)
  have hDsm : StronglyMeasurable[ℱ t] D :=
    ((measurable_of_countable (fun j : ℕ =>
      nonlinearPotential b j - nonlinearPotential b (j - 1))).comp
      (hJ t).measurable).stronglyMeasurable
  have hDint : Integrable D μ :=
    nonlinear_nat_transform_integrable ((hJ t).mono (ℱ.le t)).measurable
      (hbound t) (fun j => nonlinearPotential b j - nonlinearPotential b (j - 1))
  have hBsm : StronglyMeasurable[ℱ (t + 1)] B :=
    ((measurable_of_countable (fun p : ℕ × ℕ =>
      if p.1 < p.2 then (1 : ℝ) else 0)).comp
      ((hJ (t + 1)).measurable.prodMk
        ((hJ t).mono (ℱ.mono (Nat.le_succ t))).measurable)).stronglyMeasurable
  have hBnorm : ∀ ω, ‖B ω‖ ≤ 1 := by
    intro ω
    dsimp [B]
    split_ifs <;> norm_num
  have hBint : Integrable B μ :=
    Integrable.of_bound (hBsm.mono (ℱ.le (t + 1))).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hBnorm)
  have hDBint : Integrable (D * B) μ :=
    hDint.mul_bdd (hBsm.mono (ℱ.le (t + 1))).aestronglyMeasurable
      (Filter.Eventually.of_forall hBnorm)
  have hpoint : V (t + 1) ≤ᵐ[μ] V t - D * B := by
    filter_upwards [hmono t] with ω hω
    exact nonlinearPotential_step hω
  have hCE : μ[V (t + 1) | ℱ t] ≤ᵐ[μ] μ[V t - D * B | ℱ t] :=
    condExp_mono (hVint (t + 1)) ((hVint t).sub hDBint) hpoint
  have hlinear : μ[V t - D * B | ℱ t] =ᵐ[μ] V t - D * μ[B | ℱ t] := by
    have hsub := condExp_sub (hVint t) hDBint (ℱ t)
    have hpull := condExp_mul_of_stronglyMeasurable_left hDsm hDBint hBint
    have hfixed := condExp_of_stronglyMeasurable (ℱ.le t) (hVsm t) (hVint t)
    filter_upwards [hsub, hpull] with ω hs hp
    simp only [Pi.sub_apply, Pi.mul_apply] at hs hp ⊢
    rw [hs, hfixed, hp]
  have hcond : μ[V (t + 1) | ℱ t] ≤ᵐ[μ]
      (fun ω => (1 - nonlinearDiscount N b) * V t ω) := by
    filter_upwards [hCE, hlinear, hdeath t] with ω hc hl hd
    rw [hl] at hc
    have hDn : 0 ≤ D ω := nonlinearPotential_gap_nonneg b (J t ω)
    have hdrop := mul_le_mul_of_nonneg_left hd hDn
    have hloss := nonlinearPotential_service_loss N hN b (J t ω) hb
    change μ[V (t + 1) | ℱ t] ω ≤ (1 - nonlinearDiscount N b) * V t ω
    change D ω * nonlinearServiceRate N (J t ω) ≤ D ω * μ[B | ℱ t] ω at hdrop
    change nonlinearDiscount N b * V t ω ≤
      nonlinearServiceRate N (J t ω) * D ω at hloss
    change μ[V (t + 1) | ℱ t] ω ≤ V t ω - D ω * μ[B | ℱ t] ω at hc
    nlinarith
  calc
    (∫ ω, nonlinearPotential b (J (t + 1) ω) ∂μ) =
        ∫ ω, μ[V (t + 1) | ℱ t] ω ∂μ := (integral_condExp (ℱ.le t)).symm
    _ ≤ ∫ ω, (1 - nonlinearDiscount N b) * V t ω ∂μ :=
      integral_mono_ae integrable_condExp ((hVint t).const_mul _) hcond
    _ = (1 - nonlinearDiscount N b) * ∫ ω, nonlinearPotential b (J t ω) ∂μ :=
      integral_const_mul _ _

/-- The adapted exponential moment is derived from the nonlinear one-step
service law; it is not a premise of the tail theorem. -/
theorem nonlinear_death_moment
    (J : ℕ → Ω → ℕ) (M b : ℕ) (N : ℝ) (hN : 0 < N) (hb : 0 < b)
    (hdiscount : nonlinearDiscount N b ≤ 1)
    (hJ : ∀ t, StronglyMeasurable[ℱ t] (J t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, J t ω ≤ M)
    (hmono : ∀ t, ∀ᵐ ω ∂μ, J (t + 1) ω ≤ J t ω)
    (hdeath : ∀ t, (fun ω => nonlinearServiceRate N (J t ω)) ≤ᵐ[μ]
      μ[fun ω => if J (t + 1) ω < J t ω then (1 : ℝ) else 0 | ℱ t])
    (T : ℕ) :
    (∫ ω, nonlinearPotential b (J T ω) ∂μ) ≤
      (1 - nonlinearDiscount N b) ^ T * Real.exp ((b : ℝ) / 3) := by
  have hr : 0 ≤ 1 - nonlinearDiscount N b := sub_nonneg.mpr hdiscount
  induction T with
  | zero =>
      simp only [pow_zero, one_mul]
      calc
        (∫ ω, nonlinearPotential b (J 0 ω) ∂μ) ≤
            ∫ _ : Ω, Real.exp ((b : ℝ) / 3) ∂μ :=
          integral_mono
            (nonlinear_nat_transform_integrable ((hJ 0).mono (ℱ.le 0)).measurable
              (hbound 0) (nonlinearPotential b))
            (integrable_const _) (fun ω => nonlinearPotential_upper b (J 0 ω))
        _ = Real.exp ((b : ℝ) / 3) := by simp
  | succ T ih =>
      calc
        (∫ ω, nonlinearPotential b (J (T + 1) ω) ∂μ) ≤
            (1 - nonlinearDiscount N b) * ∫ ω, nonlinearPotential b (J T ω) ∂μ :=
          nonlinear_moment_step J M b N hN hb hJ hbound hmono hdeath T
        _ ≤ (1 - nonlinearDiscount N b) *
            ((1 - nonlinearDiscount N b) ^ T * Real.exp ((b : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left ih hr
        _ = (1 - nonlinearDiscount N b) ^ (T + 1) *
            Real.exp ((b : ℝ) / 3) := by rw [pow_succ]; ring

/-- The calibrated nonlinear service tail. Kills to zero and multi-label
decreases are allowed. The threshold is strict: the success conclusion is J≤b. -/
theorem adapted_nonlinear_death_tail
    (J : ℕ → Ω → ℕ) (M b : ℕ) (N : ℝ) (hN : 0 < N) (hb : 0 < b)
    (hbM : b ≤ M) (hcap : 2 * (M : ℝ) ^ 2 ≤ N)
    (hJ : ∀ t, StronglyMeasurable[ℱ t] (J t))
    (hbound : ∀ t, ∀ᵐ ω ∂μ, J t ω ≤ M)
    (hmono : ∀ t, ∀ᵐ ω ∂μ, J (t + 1) ω ≤ J t ω)
    (hdeath : ∀ t, (fun ω => nonlinearServiceRate N (J t ω)) ≤ᵐ[μ]
      μ[fun ω => if J (t + 1) ω < J t ω then (1 : ℝ) else 0 | ℱ t])
    (T : ℕ) (hT : N / (b : ℝ) ≤ T) :
    μ.real {ω | b < J T ω} ≤ Real.exp (-(b : ℝ) / 6) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hdiscount := nonlinearDiscount_le_one hN hcap hbM
  have hmoment := nonlinear_death_moment J M b N hN hb hdiscount
    hJ hbound hmono hdeath T
  have hgeom :
      (1 - nonlinearDiscount N b) ^ T ≤
        Real.exp (-nonlinearDiscount N b * (T : ℝ)) := by
    have hbase : 1 - nonlinearDiscount N b ≤ Real.exp (-nonlinearDiscount N b) := by
      linarith [Real.add_one_le_exp (-nonlinearDiscount N b)]
    calc
      (1 - nonlinearDiscount N b) ^ T ≤ (Real.exp (-nonlinearDiscount N b)) ^ T :=
        pow_le_pow_left₀ (sub_nonneg.mpr hdiscount) hbase T
      _ = Real.exp (-nonlinearDiscount N b * (T : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hTmul : N ≤ (T : ℝ) * (b : ℝ) := (div_le_iff₀ hbpos).mp hT
  have hdiscountT : (b : ℝ) / 2 ≤ nonlinearDiscount N b * (T : ℝ) := by
    unfold nonlinearDiscount
    have hmul := mul_le_mul_of_nonneg_left hTmul hbpos.le
    have hid : (b : ℝ) ^ 2 / (2 * N) * (T : ℝ) =
        ((b : ℝ) ^ 2 * (T : ℝ)) / (2 * N) := by ring
    rw [hid]
    apply (le_div_iff₀ (by positivity : 0 < 2 * N)).2
    nlinarith
  have hVint : Integrable (fun ω => nonlinearPotential b (J T ω)) μ :=
    nonlinear_nat_transform_integrable ((hJ T).mono (ℱ.le T)).measurable
      (hbound T) (nonlinearPotential b)
  have hsub : {ω | b < J T ω} ⊆ {ω | (1 : ℝ) ≤ nonlinearPotential b (J T ω)} :=
    fun ω hω => nonlinearPotential_one_le hω
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun ω => nonlinearPotential_nonneg b (J T ω)) hVint (1 : ℝ)
  have hprob : μ.real {ω | b < J T ω} ≤
      ∫ ω, nonlinearPotential b (J T ω) ∂μ :=
    (measureReal_mono hsub).trans (by simpa only [one_mul] using hmarkov)
  calc
    μ.real {ω | b < J T ω} ≤ ∫ ω, nonlinearPotential b (J T ω) ∂μ := hprob
    _ ≤ (1 - nonlinearDiscount N b) ^ T * Real.exp ((b : ℝ) / 3) := hmoment
    _ ≤ Real.exp (-nonlinearDiscount N b * (T : ℝ)) * Real.exp ((b : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hgeom (Real.exp_nonneg _)
    _ = Real.exp (-nonlinearDiscount N b * (T : ℝ) + (b : ℝ) / 3) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(b : ℝ) / 6) := Real.exp_le_exp.mpr (by linarith)

end Adapted

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
