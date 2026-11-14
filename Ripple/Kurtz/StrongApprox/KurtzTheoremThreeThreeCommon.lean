-- Ripple/Kurtz/StrongApprox/KurtzTheoremThreeThreeCommon.lean
import Ripple.Kurtz.StrongApprox.DyadicEntropyCommonLevel
import Ripple.Kurtz.StrongApprox.DyadicCoverBudget
import Ripple.Kurtz.StrongApprox.PerturbedDiffusionComparison
import Ripple.Kurtz.StrongApprox.ChannelProductTransport
import Mathlib.Probability.IdentDistrib

/-!
# Kurtz 1978, Theorem 3.3(a): one coefficient for every population size

The theorem (p. 232): if `f_l^N ≤ ε_l` (3.1), `|f_l - f_l^N| ≤ Γ ε_l / N`
(3.2), `|f_l(x) - f_l(y)| ≤ ε_l M ‖x - y‖` (3.19), the drift `F` is
`M`-Lipschitz, only finitely many `ε_l` are nonzero, and `Y_l`, `B_l` satisfy
the conclusion of Lemma 3.1 (p. 230), then for `N ≥ 2` there is a random
variable `β_N^T` with distribution independent of `N` and
`E exp(λ β_N^T) < ∞` such that
`sup_{t ≤ T} ‖X_N(t) - Z_N(t)‖ ≤ β_N^T log N / N` (3.20).

Here `FiniteChannelKurtzClaim` states this conclusion with one random variable
`β^T` for every `N` simultaneously (a stronger form), and the analytic
premises on the paths (`hPaths`) are carried as hypotheses of the abstract
theorem `finiteChannelKurtzClaim`, to be produced by the chain construction
and the diffusion existence results.  The coefficient is explicit
(`dyadicCoverBeta`).  The Lipschitz hypothesis on the drift is not needed:
the channel Lipschitz bounds (3.19) suffice, and nonnegativity of the limiting
rates follows from that of the chain rates and (3.2).
-/

noncomputable section
namespace Ripple.Kurtz.StrongApprox
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable def FiniteChannelKurtzClaim
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ι → (Fin d → ℝ) → ℝ)
    (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ)
    (Gamma M T : ℝ)
    (Y W : ι → ℝ → Ω → ℝ)
    (Xi : ι → Ω → ℝ)
    (X Z : ℕ → Ω → ℝ → Fin d → ℝ)
    (x0 : ℕ → Ω → Fin d → ℝ) : Prop :=
  ∀ (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y,
      |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ)))
    (hXiMeas : ∀ l, Measurable (Xi l))
    (hXi0 : ∀ l omega, 0 ≤ Xi l omega)
    (hXiExp : ∀ l, ∃ eta : ℝ, 0 < eta ∧
      Integrable (fun omega => Real.exp (eta * Xi l omega)) P)
    (hKMT : ∀ᵐ omega ∂P, ∀ l t, 0 ≤ t →
      |Y l t omega - t - W l t omega| ≤
        Xi l omega * Real.log (max 2 t))
    (hPaths : ∀ᵐ omega ∂P, ∀ N : ℕ, 2 ≤ N →
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => fN N l (X N omega s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (X N omega s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (Z N omega s)) volume 0 t) ∧
      IntegrableOn (fun s => ‖X N omega s - Z N omega s‖)
        (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Ico (0 : ℝ) T,
        ContinuousWithinAt (fun s => ‖X N omega s - Z N omega s‖)
          (Ioi t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        X N omega t = x0 N omega + ∑ l,
          (Y l (scaledTcClock (N : ℝ) (fN N) (X N omega) l t) omega /
            (N : ℝ)) • v l) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Z N omega t = x0 N omega +
          (∫ s in (0 : ℝ)..t, tcDrift f v (Z N omega s)) + ∑ l,
          (W l (scaledTcClock (N : ℝ) f (Z N omega) l t) omega /
            (N : ℝ)) • v l)),
    ∃ betaT : Ω → ℝ,
      Measurable betaT ∧
      (∀ omega, 0 ≤ betaT omega) ∧
      (∃ lam : ℝ, 0 < lam ∧
        Integrable (fun omega => Real.exp (lam * betaT omega)) P) ∧
      (∀ᵐ omega ∂P, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖X N omega t - Z N omega t‖ ≤
          betaT omega * Real.log (N : ℝ) / (N : ℝ))


/-- Having a finite exponential moment at some strictly positive parameter. -/
def HasPositiveExpMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Ω → ℝ) : Prop :=
  ∃ eta : ℝ, 0 < eta ∧ Integrable (fun ω => Real.exp (eta * U ω)) P

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Constants have a positive exponential moment on a probability space. -/
theorem positiveExpMoment_const (b : ℝ) :
    HasPositiveExpMoment P (fun _ : Ω => b) :=
  ⟨1, by norm_num, integrable_const _⟩

/-- Finite exponential moments are closed under addition without independence. -/
theorem positiveExpMoment_add {U V : Ω → ℝ}
    (hU : Measurable U) (hV : Measurable V)
    (hUn : ∀ ω, 0 ≤ U ω) (hVn : ∀ ω, 0 ≤ V ω)
    (hUm : HasPositiveExpMoment P U) (hVm : HasPositiveExpMoment P V) :
    HasPositiveExpMoment P (fun ω => U ω + V ω) := by
  obtain ⟨a, ha, hia⟩ := hUm
  obtain ⟨b, hb, hib⟩ := hVm
  let eta := min a b / 2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heA : 2 * eta ≤ a := by dsimp [eta]; linarith [min_le_left a b]
  have heB : 2 * eta ≤ b := by dsimp [eta]; linarith [min_le_right a b]
  refine ⟨eta, heta, (hia.add hib).mono' ?_ ?_⟩
  · exact (Real.measurable_exp.comp (measurable_const.mul (hU.add hV))).aestronglyMeasurable
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hu := mul_le_mul_of_nonneg_right heA (hUn ω)
    have hv := mul_le_mul_of_nonneg_right heB (hVn ω)
    rcases le_total (a * U ω) (b * V ω) with h | h
    · have hx : eta * (U ω + V ω) ≤ b * V ω := by linarith
      exact (Real.exp_le_exp.mpr hx).trans (le_add_of_nonneg_left (Real.exp_nonneg _))
    · have hx : eta * (U ω + V ω) ≤ a * U ω := by linarith
      exact (Real.exp_le_exp.mpr hx).trans (le_add_of_nonneg_right (Real.exp_nonneg _))

/-- Nonnegative scaling and a deterministic translation preserve a positive
exponential moment, with no independence assumption. -/
theorem positiveExpMoment_affine {U : Ω → ℝ}
    (hU : Measurable U) (hUn : ∀ ω, 0 ≤ U ω)
    (hUm : HasPositiveExpMoment P U) {c : ℝ} (hc : 0 ≤ c) (b : ℝ) :
    HasPositiveExpMoment P (fun ω => c * U ω + b) := by
  obtain ⟨a, ha, hia⟩ := hUm
  let eta := a / (c + 1)
  have hd : 0 < c + 1 := by linarith
  have heta : 0 < eta := div_pos ha hd
  have hec : eta * c ≤ a := by
    dsimp [eta]
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith
  refine ⟨eta, heta, (hia.const_mul (Real.exp (eta * b))).mono' ?_ ?_⟩
  · exact (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_const.mul hU).add measurable_const))).aestronglyMeasurable
  · filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (eta * (c * U ω + b)) =
          Real.exp (eta * b) * Real.exp ((eta * c) * U ω) := by
            rw [← Real.exp_add]; congr 1 <;> ring
      _ ≤ Real.exp (eta * b) * Real.exp (a * U ω) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hec (hUn ω)))
          (Real.exp_nonneg _)

/-- A finite sum of nonnegative variables with positive exponential moments
also has one, without assumptions on their joint law. -/
theorem positiveExpMoment_sum {ι : Type*} [Fintype ι] {U : ι → Ω → ℝ}
    (hU : ∀ l, Measurable (U l)) (hUn : ∀ l ω, 0 ≤ U l ω)
    (hUm : ∀ l, HasPositiveExpMoment P (U l)) :
    HasPositiveExpMoment P (fun ω => ∑ l, U l ω) := by
  classical
  have hfin : ∀ s : Finset ι,
      HasPositiveExpMoment P (fun ω => ∑ l ∈ s, U l ω) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (positiveExpMoment_const (P := P) 0)
    | @insert l s hl ih =>
        simpa only [Finset.sum_insert hl] using
          positiveExpMoment_add (hU l)
            (Finset.measurable_sum _ fun k _ => hU k)
            (hUn l) (fun ω => Finset.sum_nonneg fun k _ => hUn k ω) (hUm l) ih
  simpa using hfin Finset.univ

/-- Measurability of the explicit common coefficient. -/
theorem measurable_dyadicCoverBeta {K A : Ω → ℝ}
    (hK : Measurable K) (hA : Measurable A) (S D Gamma E M T : ℝ) :
    Measurable (fun ω => dyadicCoverBeta S (K ω) (A ω) D Gamma E M T) := by
  unfold dyadicCoverBeta
  fun_prop

/-- The explicit coefficient has a positive exponential moment. -/
theorem positiveExpMoment_dyadicCoverBeta {K A : Ω → ℝ}
    (hK : Measurable K) (hA : Measurable A)
    (hKn : ∀ ω, 0 ≤ K ω) (hAn : ∀ ω, 0 ≤ A ω)
    (hKm : HasPositiveExpMoment P K) (hAm : HasPositiveExpMoment P A)
    {S D Gamma E M T : ℝ} (hS : 0 ≤ S) (hD : 1 ≤ D)
    (hGamma : 0 ≤ Gamma) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    HasPositiveExpMoment P
      (fun ω => dyadicCoverBeta S (K ω) (A ω) D Gamma E M T) := by
  have ht : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : 0 ≤ dyadicCoverLogFactor D := by
    unfold dyadicCoverLogFactor
    have : 0 ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
    positivity
  have hoff : 0 ≤ dyadicCoverOffset D := by
    unfold dyadicCoverOffset
    have := Real.log_nonneg hD
    positivity
  let U := fun ω => S * dyadicCoverLogFactor D * K ω
  let V := fun ω => 1024 * S * (2 + (A ω + dyadicCoverOffset D) / Real.log 2)
  have hUm : HasPositiveExpMoment P U := by
    simpa [U] using positiveExpMoment_affine hK hKn hKm (mul_nonneg hS hlog) 0
  have hVm : HasPositiveExpMoment P V := by
    have hm := positiveExpMoment_affine hA hAn hAm
      (show 0 ≤ 1024 * S / Real.log 2 by positivity)
      (1024 * S * (2 + dyadicCoverOffset D / Real.log 2))
    have heq : (fun ω => (1024 * S / Real.log 2) * A ω +
        1024 * S * (2 + dyadicCoverOffset D / Real.log 2)) = V := by
      funext ω
      dsimp [V]
      ring
    rw [← heq]
    exact hm
  have hUn : ∀ ω, 0 ≤ U ω := fun ω => mul_nonneg (mul_nonneg hS hlog) (hKn ω)
  have hVn : ∀ ω, 0 ≤ V ω := fun ω => by
    have hnonneg := hAn ω
    dsimp [V]
    positivity
  have hsum := positiveExpMoment_add
    (show Measurable U by dsimp [U]; fun_prop)
    (show Measurable V by dsimp [V]; fun_prop) hUn hVn hUm hVm
  have hm := positiveExpMoment_affine
    (show Measurable (fun ω => U ω + V ω) by dsimp [U, V]; fun_prop)
    (fun ω => add_nonneg (hUn ω) (hVn ω)) hsum
    (Real.exp_nonneg (257 * M * E * T))
    (Real.exp (257 * M * E * T) * (257 * Gamma * E * T / Real.log 2))
  have heq : (fun ω => Real.exp (257 * M * E * T) * (U ω + V ω) +
      Real.exp (257 * M * E * T) * (257 * Gamma * E * T / Real.log 2)) =
      (fun ω => dyadicCoverBeta S (K ω) (A ω) D Gamma E M T) := by
    funext ω
    dsimp [dyadicCoverBeta, U, V]
    ring
  rw [← heq]
  exact hm


/-- Kurtz Theorem 3.3(a), strengthened to a single coefficient for every population
size on the given driver space. Carried hypotheses and intended producers:
`heps`, `hGamma`, `hM`, `hT`, `hfN0`, `h31`, `h32`, and `h319` are
rate-model assumptions (3.1), (3.2), and (3.19); nonnegativity of the limiting
rates follows from `hfN0` and `h32` (`rate_limit_nonneg`), and the paper's drift
Lipschitz assumption is not needed (channel Lipschitz bounds suffice). `hW` comes from the Brownian driver law;
`hXiMeas`, `hXi0`, `hXiExp`, and `hKMT` come from the common KMT coefficient
adapter, or its finite-product transport. `hPaths` carries interval integrability
of the three rate compositions, distance integrability and right continuity,
and the chain and diffusion equations with a shared initial condition. Their
intended producers are the chain construction and the diffusion existence and
regularity theorem. No solution existence or path regularity is asserted here.
The dyadic entropy event and exponential moment are produced in this proof. -/
theorem finiteChannelKurtzClaim
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ι → (Fin d → ℝ) → ℝ)
    (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ)
    (Gamma M T : ℝ)
    (Y W : ι → ℝ → Ω → ℝ)
    (Xi : ι → Ω → ℝ)
    (X Z : ℕ → Ω → ℝ → Fin d → ℝ)
    (x0 : ℕ → Ω → Fin d → ℝ) :
    FiniteChannelKurtzClaim P f fN v eps Gamma M T Y W Xi X Z x0 := by
  classical
  intro heps hGamma hM hT hfN0 h31 h32 h319 hW
    hXiMeas hXi0 hXiExp hKMT hPaths
  have hf0 : ∀ l x, 0 ≤ f l x := fun l x => rate_limit_nonneg hfN0 h32 l x
  let S := channelWeight (fun l => ‖v l‖)
  let E := channelClockLip (fun l => ‖v l‖) eps
  let D := 1 + ∑ l, eps l * T
  let K := fun ω => ∑ l, Xi l ω
  let A := dyadicEntropyCommonReal W
  let betaT := fun ω => dyadicCoverBeta S (K ω) (A ω) D Gamma E M T
  have hS : 0 ≤ S := channelWeight_nonneg (fun l => norm_nonneg (v l))
  have hE : 0 ≤ E := channelClockLip_nonneg (fun l => norm_nonneg (v l)) heps
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => mul_nonneg (heps l) hT)
  have hclockD : ∀ l, eps l * T ≤ D := by
    intro l
    have hle := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
      mul_nonneg (heps k) hT) (Finset.mem_univ l)
    dsimp [D]
    linarith
  have hKmeas : Measurable K := Finset.measurable_sum _ fun l _ => hXiMeas l
  have hKn : ∀ ω, 0 ≤ K ω := fun ω => Finset.sum_nonneg fun l _ => hXi0 l ω
  have hAmeas : Measurable A :=
    measurable_dyadicEntropyCommonReal fun l => (hW l 0).eval_measurable
  have hAn : ∀ ω, 0 ≤ A ω := dyadicEntropyCommonReal_nonneg W
  have hKm : HasPositiveExpMoment P K := positiveExpMoment_sum hXiMeas hXi0 hXiExp
  have hAm : HasPositiveExpMoment P A :=
    ⟨1 / 2, by norm_num, (integral_exp_dyadicEntropyCommonReal_le hW
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).1⟩
  refine ⟨betaT, measurable_dyadicCoverBeta hKmeas hAmeas S D Gamma E M T,
    fun ω => dyadicCoverBeta_nonneg hS (hKn ω) (hAn ω) hD hGamma hE hT,
    positiveExpMoment_dyadicCoverBeta hKmeas hAmeas hKn hAn hKm hAm
      hS hD hGamma hE hT, ?_⟩
  filter_upwards [hKMT, hPaths, brownianEntropyBound_of_commonLevel_ae hW]
    with ω hcoupling hpaths hentropy
  intro N hN t ht
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨j, hjlo, hjhi⟩ := exists_dyadic_cover_nat hN hD
  have hadm := dyadicCover_affineBudget_admissible hNr hD (hAn ω) hjlo
  have hHtwo : (2 : ℝ) ≤ (2 : ℝ) ^ j := by
    have hND : (N : ℝ) ≤ (N : ℝ) * D := by
      nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
    linarith
  have hHpos : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos (by norm_num) j
  have hR : 0 ≤ K ω * Real.log ((2 : ℝ) ^ j) :=
    mul_nonneg (hKn ω) (Real.log_nonneg (by linarith))
  have hq : 0 ≤ dyadicCoverAffineBudget ((2 : ℝ) ^ j) (A ω) j := by linarith [hadm.2.1]
  have hXiK : ∀ l, Xi l ω ≤ K ω := fun l =>
    Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hXi0 k ω) (Finset.mem_univ l)
  have hcouplingH : ∀ l u, u ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) →
      |Y l u ω - u - W l u ω| ≤ K ω * Real.log ((2 : ℝ) ^ j) := by
    intro l u hu
    have hmax : max (2 : ℝ) u ≤ (2 : ℝ) ^ j := max_le hHtwo hu.2
    have hlog : Real.log (max (2 : ℝ) u) ≤ Real.log ((2 : ℝ) ^ j) :=
      Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) hmax
    exact (hcoupling l u hu.1).trans
      ((mul_le_mul_of_nonneg_left hlog (hXi0 l ω)).trans
        (mul_le_mul_of_nonneg_right (hXiK l) (Real.log_nonneg (by linarith))))
  have hWaff : ∀ l u w, u ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) →
      w ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) →
      |W l u ω - W l w ω| ≤
        1024 * dyadicCoverAffineBudget ((2 : ℝ) ^ j) (A ω) j + 256 * |u - w| := by
    intro l u w hu hw
    have habs : |u - w| ∈ Icc (0 : ℝ) ((2 : ℝ) ^ j) :=
      ⟨abs_nonneg _, abs_sub_le_iff.mpr ⟨by linarith [hu.1, hu.2, hw.1, hw.2],
        by linarith [hu.1, hu.2, hw.1, hw.2]⟩⟩
    have hmod := hentropy.2.2.2 l j u hu w hw
    have hparam : 2 + A ω + dyadicEntropyPenalty j = dyadicCoverEntropy (A ω) j := by
      dsimp [dyadicEntropyPenalty, dyadicCoverEntropy]
      push_cast
      ring
    rw [hparam] at hmod
    exact hmod.trans (brownianEntropyBound_le_cover_affine hHpos hNr
      hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2 habs)
  obtain ⟨hfNX, hfX, hfZ, huint, hurc, hXeq, hZeq⟩ := hpaths N hN
  have hmain := perturbed_diffusion_comparison
    (f := f) (fN := fN) (v := v) (eps := eps)
    (Y := fun l u => Y l u ω) (W := fun l u => W l u ω)
    (X := X N ω) (Z := Z N ω) (xZero := x0 N ω)
    hN hGamma hM hT hR hq heps hf0 hfN0 h31 h32 h319
    hfNX hfX hfZ huint hurc
    (fun l => (mul_le_mul_of_nonneg_left (hclockD l)
      (Nat.cast_nonneg N)).trans hjlo)
    hXeq hZeq hcouplingH hWaff ht
  exact dyadicCover_comparison_le_beta hNr hD (hAn ω) (hKn ω) hS
    hGamma hE hT hjlo hjhi hmain


/-- Choosing the same coefficient at every population size gives the identical-law
conclusion of Theorem 3.3(a), with a common exponential moment parameter. -/
theorem finiteChannelKurtz_identicalLaw
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ι → (Fin d → ℝ) → ℝ)
    (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ)
    (Gamma M T : ℝ)
    (Y W : ι → ℝ → Ω → ℝ)
    (Xi : ι → Ω → ℝ)
    (X Z : ℕ → Ω → ℝ → Fin d → ℝ)
    (x0 : ℕ → Ω → Fin d → ℝ) :
  ∀ (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y,
      |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hW : ∀ l j, DyadicBrownianOn P (W l) ((2 : ℝ) ^ (j : ℕ)))
    (hXiMeas : ∀ l, Measurable (Xi l))
    (hXi0 : ∀ l omega, 0 ≤ Xi l omega)
    (hXiExp : ∀ l, ∃ eta : ℝ, 0 < eta ∧
      Integrable (fun omega => Real.exp (eta * Xi l omega)) P)
    (hKMT : ∀ᵐ omega ∂P, ∀ l t, 0 ≤ t →
      |Y l t omega - t - W l t omega| ≤
        Xi l omega * Real.log (max 2 t))
    (hPaths : ∀ᵐ omega ∂P, ∀ N : ℕ, 2 ≤ N →
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => fN N l (X N omega s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (X N omega s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (Z N omega s)) volume 0 t) ∧
      IntegrableOn (fun s => ‖X N omega s - Z N omega s‖)
        (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Ico (0 : ℝ) T,
        ContinuousWithinAt (fun s => ‖X N omega s - Z N omega s‖)
          (Ioi t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        X N omega t = x0 N omega + ∑ l,
          (Y l (scaledTcClock (N : ℝ) (fN N) (X N omega) l t) omega /
            (N : ℝ)) • v l) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Z N omega t = x0 N omega +
          (∫ s in (0 : ℝ)..t, tcDrift f v (Z N omega s)) + ∑ l,
          (W l (scaledTcClock (N : ℝ) f (Z N omega) l t) omega /
            (N : ℝ)) • v l)),
    ∃ beta : ℕ → Ω → ℝ,
      (∀ N, Measurable (beta N)) ∧
      (∀ N ω, 0 ≤ beta N ω) ∧
      (∃ lam : ℝ, 0 < lam ∧ ∀ N,
        Integrable (fun ω => Real.exp (lam * beta N ω)) P) ∧
      (∀ N n, IdentDistrib (beta N) (beta n) P P) ∧
      (∀ᵐ ω ∂P, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖X N ω t - Z N ω t‖ ≤ beta N ω * Real.log (N : ℝ) / (N : ℝ)) := by
  intro heps hGamma hM hT hfN0 h31 h32 h319 hW
    hXiMeas hXi0 hXiExp hKMT hPaths
  obtain ⟨betaT, hm, hn, ⟨lam, hlam, hi⟩, hbound⟩ :=
    finiteChannelKurtzClaim P f fN v eps Gamma M T Y W Xi X Z x0
      heps hGamma hM hT hfN0 h31 h32 h319 hW
      hXiMeas hXi0 hXiExp hKMT hPaths
  exact ⟨fun _ => betaT, fun _ => hm, fun _ => hn,
    ⟨lam, hlam, fun _ => hi⟩, fun _ _ => IdentDistrib.refl hm.aemeasurable, hbound⟩


/-- Concrete finite-channel theorem on the product of the all-time KMT spaces.
The product adapters discharge all driver hypotheses. The rate hypotheses and
`hPaths` are carried exactly as in `finiteChannelKurtzClaim`; the latter must be
supplied by the chain and diffusion construction and regularity producers. -/
theorem channelKMT_finiteChannelKurtz
    {ι : Type*} [Fintype ι] {d : ℕ}
    (f : ι → (Fin d → ℝ) → ℝ)
    (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ) (Gamma M T : ℝ)
    (X Z : ℕ → channelKMTSpace ι → ℝ → Fin d → ℝ)
    (x0 : ℕ → channelKMTSpace ι → Fin d → ℝ) :
  ∀ (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y,
      |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hPaths : ∀ᵐ omega ∂(channelKMTMeasure ι), ∀ N : ℕ, 2 ≤ N →
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => fN N l (X N omega s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (X N omega s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (Z N omega s)) volume 0 t) ∧
      IntegrableOn (fun s => ‖X N omega s - Z N omega s‖)
        (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Ico (0 : ℝ) T,
        ContinuousWithinAt (fun s => ‖X N omega s - Z N omega s‖)
          (Ioi t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        X N omega t = x0 N omega + ∑ l,
          ((channelKMTPoisson l (scaledTcClock (N : ℝ) (fN N) (X N omega) l t) omega : ℝ) /
            (N : ℝ)) • v l) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Z N omega t = x0 N omega +
          (∫ s in (0 : ℝ)..t, tcDrift f v (Z N omega s)) + ∑ l,
          (channelKMTBrownian l (scaledTcClock (N : ℝ) f (Z N omega) l t) omega /
            (N : ℝ)) • v l)),
    ∃ betaT : channelKMTSpace ι → ℝ,
      Measurable betaT ∧
      (∀ omega, 0 ≤ betaT omega) ∧
      (∃ lam : ℝ, 0 < lam ∧
        Integrable (fun omega => Real.exp (lam * betaT omega)) (channelKMTMeasure ι)) ∧
      (∀ᵐ omega ∂(channelKMTMeasure ι), ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖X N omega t - Z N omega t‖ ≤
          betaT omega * Real.log (N : ℝ) / (N : ℝ)) := by
  intro heps hGamma hM hT hfN0 h31 h32 h319 hPaths
  apply finiteChannelKurtzClaim (channelKMTMeasure ι) f fN v eps Gamma M T
    (fun l t ω => (channelKMTPoisson l t ω : ℝ)) channelKMTBrownian
    channelKMTCoefficient X Z x0
    heps hGamma hM hT hfN0 h31 h32 h319
    channelKMTBrownian_dyadicBrownianOn measurable_channelKMTCoefficient
    channelKMTCoefficient_nonneg
    (fun l => ⟨AllTimeKurtzMoment.allTimeKurtzGamma / 2,
      by linarith [AllTimeKurtzMoment.allTimeKurtzGamma_pos],
      integrable_exp_channelKMTCoefficient l
        (by linarith [AllTimeKurtzMoment.allTimeKurtzGamma_pos])
        (by linarith [AllTimeKurtzMoment.allTimeKurtzGamma_pos])⟩)
    channelKMT_bound_ae hPaths


end Ripple.Kurtz.StrongApprox
end
