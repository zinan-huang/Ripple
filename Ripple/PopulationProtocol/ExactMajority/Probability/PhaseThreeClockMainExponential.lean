import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProductTails
import Ripple.Probability.BennettLemma

/-!
# A relative Bernstein tail for a supermartingale with bounded increments (N12, P12 tool)

PHASE3 P12 bounds the probability that the discounted Main-credit potential rises by
`u_*` on its stopped horizon through a compensated Freedman estimate. On a prefix event
`E` (in the time-zero σ-algebra of the filtration in use) the same bound follows from the
product tool `PhaseThreeClockProductTails.prefix_product_tail_ennreal` applied to the
factors `exp (λ ΔY_t - ψ c²)`: for a supermartingale increment `ΔY` with `|ΔY| ≤ c`,
`exp (λ ΔY) ≤ 1 + λ ΔY + ψ ΔY²` (`bernstein_one_step`), so the factor has conditional
mean at most `exp (-ψ c²) (1 + ψ c²) ≤ 1`. The compensation of the drift is unnecessary:
the supermartingale inequality enters the one-step bound linearly.

`supermartingale_terminal_tail`: for `E` in `ℱ 0`,
`μ (E ∩ {u ≤ Y N - Y 0}) ≤ exp (N ψ c² - λ u) · μ E` with `ψ = bernstein_psi λ c`.
Applied to a process frozen at its first barrier hit, `{u ≤ Y N - Y 0}` is the event that
the barrier is hit by time `N`, which is the maximal form P12 uses. Nothing here
conditions on a future event.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainExponential

open PhaseThreeClockProductTails Ripple.Probability

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

/-- The exponential factor of one step. -/
def expFactor (Y : ℕ → Ω → ℝ) (lam ψc : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Real.exp (lam * (Y (t + 1) ω - Y t ω) - ψc)

theorem expFactor_stronglyMeasurable {Y : ℕ → Ω → ℝ}
    (hY : ∀ t, StronglyMeasurable[ℱ t] (Y t)) (lam ψc : ℝ) (t : ℕ) :
    StronglyMeasurable[ℱ (t + 1)] (expFactor Y lam ψc t) := by
  have h1 : StronglyMeasurable[ℱ (t + 1)] (Y (t + 1)) := hY (t + 1)
  have h0 : StronglyMeasurable[ℱ (t + 1)] (Y t) := (hY t).mono (ℱ.mono (Nat.le_succ t))
  have hd : StronglyMeasurable[ℱ (t + 1)] (fun ω => lam * (Y (t + 1) ω - Y t ω) - ψc) :=
    ((h1.sub h0).const_mul lam).sub stronglyMeasurable_const
  exact Real.continuous_exp.comp_stronglyMeasurable hd

theorem expFactor_nonneg (Y : ℕ → Ω → ℝ) (lam ψc : ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ expFactor Y lam ψc t ω := (Real.exp_pos _).le

theorem expFactor_le {Y : ℕ → Ω → ℝ} {c : ℝ} (hinc : ∀ t ω, |Y (t + 1) ω - Y t ω| ≤ c)
    {lam : ℝ} (hlam : 0 ≤ lam) {ψc : ℝ} (hψ : 0 ≤ ψc) (t : ℕ) (ω : Ω) :
    expFactor Y lam ψc t ω ≤ Real.exp (lam * c) := by
  unfold expFactor
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp (hinc t ω)).2
  nlinarith

/-- The product of the factors is the exponential of the total increment. -/
theorem prefixProduct_expFactor (Y : ℕ → Ω → ℝ) (lam ψc : ℝ) (N : ℕ) (ω : Ω) :
    prefixProduct (expFactor Y lam ψc) N ω =
      Real.exp (lam * (Y N ω - Y 0 ω) - N * ψc) := by
  induction N with
  | zero => simp [prefixProduct_zero]
  | succ N ih =>
      rw [prefixProduct_succ, ih]
      unfold expFactor
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

/-- The one-step conditional bound: a supermartingale increment bounded by `c` has
`E[exp (λ ΔY) | ℱ t] ≤ 1 + ψ c²`. -/
theorem condExp_exp_increment_le {Y : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hY : ∀ t, StronglyMeasurable[ℱ t] (Y t))
    (hinc : ∀ t ω, |Y (t + 1) ω - Y t ω| ≤ c)
    (hdrift : ∀ t, μ[fun ω => Y (t + 1) ω - Y t ω | ℱ t] ≤ᵐ[μ] fun _ => 0)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlc : lam * c < 3) (t : ℕ) :
    μ[fun ω => Real.exp (lam * (Y (t + 1) ω - Y t ω)) | ℱ t] ≤ᵐ[μ]
      fun _ => 1 + bernstein_psi lam c * c ^ 2 := by
  set ψ := bernstein_psi lam c with hψdef
  have hψ : 0 ≤ ψ := bernstein_psi_nonneg hlam hlc
  let d : Ω → ℝ := fun ω => Y (t + 1) ω - Y t ω
  have hdm : StronglyMeasurable[ℱ (t + 1)] d :=
    (hY (t + 1)).sub ((hY t).mono (ℱ.mono (Nat.le_succ t)))
  have hd_int : Integrable d μ := by
    refine Integrable.of_bound (hdm.mono (ℱ.le (t + 1))).aestronglyMeasurable c ?_
    exact ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hinc t ω
  have hexp_int : Integrable (fun ω => Real.exp (lam * d ω)) μ := by
    refine Integrable.of_bound
      ((Real.continuous_exp.comp_stronglyMeasurable (hdm.const_mul lam)).mono
        (ℱ.le (t + 1))).aestronglyMeasurable (Real.exp (lam * c)) ?_
    refine ae_of_all _ fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h := (abs_le.mp (hinc t ω)).2
    nlinarith
  have hpoly_int : Integrable (fun ω => 1 + (lam * d ω + ψ * c ^ 2)) μ :=
    (integrable_const (1 : ℝ)).add ((hd_int.const_mul lam).add (integrable_const _))
  have hbern : (fun ω => Real.exp (lam * d ω)) ≤ᵐ[μ] fun ω => 1 + (lam * d ω + ψ * c ^ 2) := by
    refine ae_of_all _ fun ω => ?_
    have h := bernstein_one_step (d := d ω) (c := c) (t := lam) (hinc t ω) hc hlam hlc
    have hsq : d ω ^ 2 ≤ c ^ 2 := by
      have := abs_le.mp (hinc t ω)
      nlinarith [this.1, this.2]
    have := mul_le_mul_of_nonneg_left hsq hψ
    rw [hψdef] at this
    linarith
  have hmono : μ[fun ω => Real.exp (lam * d ω) | ℱ t] ≤ᵐ[μ]
      μ[fun ω => 1 + (lam * d ω + ψ * c ^ 2) | ℱ t] :=
    condExp_mono hexp_int hpoly_int hbern
  have hpoly_ce : μ[fun ω => 1 + (lam * d ω + ψ * c ^ 2) | ℱ t] ≤ᵐ[μ]
      fun _ => 1 + ψ * c ^ 2 := by
    change μ[(fun _ : Ω => (1 : ℝ)) + ((fun ω => lam * d ω) + fun _ => ψ * c ^ 2) | ℱ t]
      ≤ᵐ[μ] fun _ => 1 + ψ * c ^ 2
    have hconst : μ[fun _ : Ω => (1 : ℝ) | ℱ t] = fun _ : Ω => (1 : ℝ) :=
      condExp_const (ℱ.le t) (1 : ℝ)
    have hconst' : μ[fun _ : Ω => ψ * c ^ 2 | ℱ t] = fun _ : Ω => ψ * c ^ 2 :=
      condExp_const (ℱ.le t) _
    have hsum := condExp_add ((integrable_const (1 : ℝ)) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
      ((hd_int.const_mul lam).add (integrable_const (ψ * c ^ 2))) (ℱ t)
    have hsum2 := condExp_add (hd_int.const_mul lam) (integrable_const (ψ * c ^ 2)) (ℱ t)
    have hl_d : μ[fun ω => lam * d ω | ℱ t] =ᵐ[μ] fun ω => lam * μ[d | ℱ t] ω := by
      simpa [Pi.smul_apply] using condExp_smul (μ := μ) lam d (ℱ t)
    filter_upwards [hsum, hsum2, hl_d, hdrift t] with ω hsumω hsum2ω hl_dω hdω
    have hdω' : μ[d | ℱ t] ω ≤ 0 := hdω
    calc μ[(fun _ : Ω => (1 : ℝ)) + ((fun ω => lam * d ω) + fun _ => ψ * c ^ 2) | ℱ t] ω
        = μ[fun _ : Ω => (1 : ℝ) | ℱ t] ω +
            μ[(fun ω => lam * d ω) + fun _ => ψ * c ^ 2 | ℱ t] ω := hsumω
      _ = μ[fun _ : Ω => (1 : ℝ) | ℱ t] ω +
            (μ[fun ω => lam * d ω | ℱ t] ω + μ[fun _ => ψ * c ^ 2 | ℱ t] ω) := by
            rw [hsum2ω]
            simp only [Pi.add_apply]
      _ = 1 + (lam * μ[d | ℱ t] ω + ψ * c ^ 2) := by
            rw [hconst, hl_dω, hconst']
      _ ≤ 1 + ψ * c ^ 2 := by nlinarith
  exact hmono.trans hpoly_ce

/-- The factor `exp (λ ΔY - ψ c²)` has conditional mean at most one. -/
theorem expFactor_condExp_le_one {Y : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hY : ∀ t, StronglyMeasurable[ℱ t] (Y t))
    (hinc : ∀ t ω, |Y (t + 1) ω - Y t ω| ≤ c)
    (hdrift : ∀ t, μ[fun ω => Y (t + 1) ω - Y t ω | ℱ t] ≤ᵐ[μ] fun _ => 0)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlc : lam * c < 3) (t : ℕ) :
    μ[expFactor Y lam (bernstein_psi lam c * c ^ 2) t | ℱ t] ≤ᵐ[μ] fun _ => 1 := by
  set ψc := bernstein_psi lam c * c ^ 2 with hψc
  have hψ : 0 ≤ ψc := mul_nonneg (bernstein_psi_nonneg hlam hlc) (sq_nonneg c)
  have hfun : expFactor Y lam ψc t =
      fun ω => Real.exp (-ψc) * Real.exp (lam * (Y (t + 1) ω - Y t ω)) := by
    funext ω
    unfold expFactor
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hfun]
  have hsm := condExp_smul (μ := μ) (Real.exp (-ψc))
    (fun ω => Real.exp (lam * (Y (t + 1) ω - Y t ω))) (ℱ t)
  have hce := condExp_exp_increment_le hc hY hinc hdrift hlam hlc t
  filter_upwards [hsm, hce] with ω hsmω hceω
  change μ[(Real.exp (-ψc)) • fun ω => Real.exp (lam * (Y (t + 1) ω - Y t ω)) | ℱ t] ω ≤ 1
  rw [hsmω]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hpos : 0 < Real.exp (-ψc) := Real.exp_pos _
  calc Real.exp (-ψc) * μ[fun ω => Real.exp (lam * (Y (t + 1) ω - Y t ω)) | ℱ t] ω
      ≤ Real.exp (-ψc) * (1 + ψc) := mul_le_mul_of_nonneg_left hceω hpos.le
    _ ≤ Real.exp (-ψc) * Real.exp ψc :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp ψc]) hpos.le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The relative Bernstein tail on a prefix event: a supermartingale with increments
bounded by `c` rises by `u` on `[0, N]` with probability at most
`exp (N ψ c² - λ u)` relative to the prefix event `E ∈ ℱ 0`, for every `0 ≤ λ` with
`λ c < 3` and `ψ = bernstein_psi λ c`. -/
theorem supermartingale_terminal_tail {Y : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hY : ∀ t, StronglyMeasurable[ℱ t] (Y t))
    (hinc : ∀ t ω, |Y (t + 1) ω - Y t ω| ≤ c)
    (hdrift : ∀ t, μ[fun ω => Y (t + 1) ω - Y t ω | ℱ t] ≤ᵐ[μ] fun _ => 0)
    (E : Set Ω) (hE : MeasurableSet[ℱ 0] E) (N : ℕ) (u : ℝ)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlc : lam * c < 3) :
    μ (E ∩ {ω | u ≤ Y N ω - Y 0 ω}) ≤
      ENNReal.ofReal (Real.exp (N * (bernstein_psi lam c * c ^ 2) - lam * u)) * μ E := by
  set ψc := bernstein_psi lam c * c ^ 2 with hψc
  have hψ : 0 ≤ ψc := mul_nonneg (bernstein_psi_nonneg hlam hlc) (sq_nonneg c)
  have hr : 0 < Real.exp (lam * u - N * ψc) := Real.exp_pos _
  have hA : ∀ ω ∈ E ∩ {ω | u ≤ Y N ω - Y 0 ω},
      Real.exp (lam * u - N * ψc) ≤ prefixProduct (expFactor Y lam ψc) N ω := by
    rintro ω ⟨-, hω⟩
    rw [prefixProduct_expFactor]
    apply Real.exp_le_exp.mpr
    have : lam * u ≤ lam * (Y N ω - Y 0 ω) := mul_le_mul_of_nonneg_left hω hlam
    linarith
  have h := prefix_product_tail_ennreal (μ := μ) (ℱ := ℱ)
    (expFactor_stronglyMeasurable hY lam ψc) (expFactor_nonneg Y lam ψc)
    (expFactor_le hinc hlam hψ) (expFactor_condExp_le_one hc hY hinc hdrift hlam hlc)
    E hE N {ω | u ≤ Y N ω - Y 0 ω} hr hA
  have hinv : 1 / Real.exp (lam * u - N * ψc) = Real.exp (N * ψc - lam * u) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rwa [hinv] at h

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainExponential

end
