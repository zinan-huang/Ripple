-- Ripple/Kurtz/StrongApprox/KurtzTheoremThreeThree.lean
import Ripple.Kurtz.StrongApprox.KurtzTheoremThreeThreeCommon
import Ripple.Kurtz.StrongApprox.AllTimeKMTChain

/-!
# Kurtz 1978, Theorem 3.3(a), with no path premise

T. G. Kurtz, "Strong approximation theorems for density dependent Markov
chains", Stochastic Process. Appl. 6 (1978), Theorem 3.3(a), p. 232: for the
chain `X_N` of (1.3) with rates `f_l^N` and the diffusion `Z_N` of (1.6) with
rates `f_l`, `Z_N(0) = X_N(0)`, under (3.1) `0 ≤ f_l^N ≤ ε_l`, (3.2)
`|f_l - f_l^N| ≤ Γ ε_l / N`, (3.19) `|f_l(x) - f_l(y)| ≤ ε_l M ‖x - y‖` and
finitely many active channels, and given Poisson/Brownian pairs `(Y_l, B_l)`
satisfying the conclusion of Lemma 3.1, there is a random variable `β_N^T`,
with distribution independent of `N` and an exponential moment, such that
`sup_{t ≤ T} ‖X_N(t) - Z_N(t)‖ ≤ β_N^T log N / N` (3.20).

Here everything is on the concrete probability space
`channelKMTMeasure ι = ⊗_l allTimeKMTMeasure`:

* the pairs are `Y_l = allTimeKMTPoisson · (ω l)`, `W_l = allTimeKMTBrownian ·
  (ω l)`, `B_l(t) = t + W_l(t)` (Lemma 3.1 holds for each: `KurtzLemmaThreeOne`),
  independent across `l`, and the same for every `N`;
* the chain `X_N` is `allTimeChain`, driven by these `Y_l`, for every `N ≥ 2`;
* `Z_N(ω)` is any family of continuous solutions of (1.6) driven by `W_l`
  (`exists_kurtz_diffusion_family`: they exist for every sample);
* the initial states `x0 N ω` are arbitrary (random, depending on `N` and on the
  sample): the comparison is pathwise.

No path regularity is assumed: it is proved (`allTimeChain_regularity`).  The
statement is stronger than the paper's in that one `β^T` serves all `N`.  The
drift-Lipschitz assumption of the paper is not needed, and nonnegativity of
`f_l` and `ε_l` follows from (3.1), (3.2).
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.KurtzTheoremThreeThree

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
open AllTimeKMT AllTimeKMTLaws AllTimeKMTChain

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The chain `X_N` of Theorem 3.3 on the product of all-time KMT spaces, for
`N ≥ 2` (the value for `N < 2` is a dummy). -/
def kurtzChain (v : ι → Fin d → ℝ) (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    {eps : ι → ℝ}
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N : ℕ, 2 ≤ N → ∀ l, Measurable (fN N l))
    (x0 : ℕ → channelKMTSpace ι → Fin d → ℝ)
    (N : ℕ) (ω : channelKMTSpace ι) : ℝ → Fin d → ℝ :=
  if h : 2 ≤ N then
    allTimeChain (n := N) (by omega) v (hfN0 N h) (h31 N h) (hfNm N h) (x0 N ω) ω
  else fun _ => 0

/-- `Z` is a continuous solution of the diffusion equation (1.6) driven by the
Brownian motions of the sample, from the initial state `xZero`. -/
def KurtzDiffusionEq (f : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ) (T : ℝ)
    (xZero : Fin d → ℝ) (N : ℕ) (ω : channelKMTSpace ι)
    (Z : ℝ → Fin d → ℝ) : Prop :=
  Continuous Z ∧
    ∀ t ∈ Icc (0 : ℝ) T,
      Z t = xZero + (∫ s in (0 : ℝ)..t, tcDrift f v (Z s)) +
        ∑ l, (channelKMTBrownian l (scaledTcClock (N : ℝ) f Z l t) ω /
          (N : ℝ)) • v l

/-- The limiting rates are continuous, from (3.19). -/
theorem continuous_of_lip {f : ι → (Fin d → ℝ) → ℝ} {eps : ι → ℝ} {M : ℝ}
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖) (l : ι) :
    Continuous (f l) := by
  have hK : 0 ≤ eps l * M := mul_nonneg (heps l) hM
  have : LipschitzWith ⟨eps l * M, hK⟩ (f l) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm]
    exact h319 l x y
  exact this.continuous

/-- (3.1) with nonnegative rates forces `0 ≤ ε_l`. -/
theorem eps_nonneg_of {fN : ℕ → ι → (Fin d → ℝ) → ℝ} {eps : ι → ℝ}
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l) (l : ι) : 0 ≤ eps l :=
  (hfN0 2 le_rfl l 0).trans (h31 2 le_rfl l 0)

/-- **Existence**: for every sample there are continuous solutions of (1.6),
for every `N ≥ 2` and every initial state. -/
theorem exists_kurtz_diffusion_family
    {f : ι → (Fin d → ℝ) → ℝ} {fN : ℕ → ι → (Fin d → ℝ) → ℝ}
    {eps : ι → ℝ} {Gamma M T : ℝ} (v : ι → Fin d → ℝ)
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (x0 : ℕ → channelKMTSpace ι → Fin d → ℝ) :
    ∃ Z : ℕ → channelKMTSpace ι → ℝ → Fin d → ℝ,
      ∀ N, 2 ≤ N → ∀ ω, KurtzDiffusionEq f v T (x0 N ω) N ω (Z N ω) := by
  classical
  have heps : ∀ l, 0 ≤ eps l := eps_nonneg_of hfN0 h31
  have hfc : ∀ l, Continuous (f l) := continuous_of_lip heps hM h319
  have hf0 : ∀ l x, 0 ≤ f l x := fun l x => rate_limit_nonneg hfN0 h32 l x
  have hfB : ∀ l x, f l x ≤ eps l := fun l x => rate_limit_le h31 h32 l x
  have key : ∀ (N : ℕ) (ω : channelKMTSpace ι), ∃ Z : ℝ → Fin d → ℝ,
      2 ≤ N → KurtzDiffusionEq f v T (x0 N ω) N ω Z := by
    intro N ω
    by_cases hN : 2 ≤ N
    · have hNr : (0 : ℝ) < (N : ℝ) := by
        have : (0 : ℕ) < N := by omega
        exact_mod_cast this
      obtain ⟨Z, hZc, _hint, hZeq⟩ := exists_diffusionTimeChange_solution
        (fun l t => allTimeKMTBrownian t (ω l))
        (fun l => allTimeKMTBrownian_continuous (ω l))
        f hfc eps hf0 hfB v hNr hT (x0 N ω)
      exact ⟨Z, fun _ => ⟨hZc, hZeq⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hN⟩
  choose Z hZ using key
  exact ⟨Z, fun N hN ω => hZ N ω hN⟩

/-- **The comparison, with no path premise.**  For any family of continuous
solutions of (1.6) there is one random variable `β^T` (measurable, nonnegative,
with an exponential moment) bounding `‖X_N(t) - Z_N(t)‖ ≤ β^T log N / N` for
all `N ≥ 2` and `t ∈ [0,T]` almost surely. -/
theorem kurtz_theorem_three_three_bound
    {f : ι → (Fin d → ℝ) → ℝ} {fN : ℕ → ι → (Fin d → ℝ) → ℝ}
    {eps : ι → ℝ} {Gamma M T : ℝ} (v : ι → Fin d → ℝ)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfNm : ∀ N : ℕ, 2 ≤ N → ∀ l, Measurable (fN N l))
    (x0 : ℕ → channelKMTSpace ι → Fin d → ℝ)
    (Z : ℕ → channelKMTSpace ι → ℝ → Fin d → ℝ)
    (hZ : ∀ N, 2 ≤ N → ∀ ω, KurtzDiffusionEq f v T (x0 N ω) N ω (Z N ω)) :
    ∃ betaT : channelKMTSpace ι → ℝ,
      Measurable betaT ∧
      (∀ omega, 0 ≤ betaT omega) ∧
      (∃ lam : ℝ, 0 < lam ∧
        Integrable (fun omega => Real.exp (lam * betaT omega))
          (channelKMTMeasure ι)) ∧
      (∀ᵐ omega ∂(channelKMTMeasure ι), ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖kurtzChain v fN hfN0 h31 hfNm x0 N omega t - Z N omega t‖ ≤
          betaT omega * Real.log (N : ℝ) / (N : ℝ)) := by
  classical
  have heps : ∀ l, 0 ≤ eps l := eps_nonneg_of hfN0 h31
  have hfc : ∀ l, Continuous (f l) := continuous_of_lip heps hM h319
  have hf0 : ∀ l x, 0 ≤ f l x := fun l x => rate_limit_nonneg hfN0 h32 l x
  have hfB : ∀ l x, f l x ≤ eps l := fun l x => rate_limit_le h31 h32 l x
  have hgc : ∀ l x, |f l x| ≤ eps l := fun l x => by
    rw [abs_of_nonneg (hf0 l x)]; exact hfB l x
  refine finiteChannelKurtzClaim (channelKMTMeasure ι) f fN v eps Gamma M T
    (fun l t ω => (channelKMTPoisson l t ω : ℝ)) channelKMTBrownian
    channelKMTCoefficient (kurtzChain v fN hfN0 h31 hfNm x0) Z x0
    heps hGamma hM hT hfN0 h31 h32 h319
    channelKMTBrownian_dyadicBrownianOn measurable_channelKMTCoefficient
    channelKMTCoefficient_nonneg
    (fun l => ⟨AllTimeKurtzMoment.allTimeKurtzGamma / 2,
      by linarith [AllTimeKurtzMoment.allTimeKurtzGamma_pos],
      integrable_exp_channelKMTCoefficient l
        (by linarith [AllTimeKurtzMoment.allTimeKurtzGamma_pos])
        (by linarith [AllTimeKurtzMoment.allTimeKurtzGamma_pos])⟩)
    channelKMT_bound_ae ?_
  refine Filter.Eventually.of_forall fun ω N hN => ?_
  have hc : kurtzChain v fN hfN0 h31 hfNm x0 N ω =
      allTimeChain (n := N) (by omega) v (hfN0 N hN) (h31 N hN) (hfNm N hN)
        (x0 N ω) ω := dif_pos hN
  obtain ⟨hZc, hZeq⟩ := hZ N hN ω
  have hreg := allTimeChain_regularity (n := N) (by omega) (v := v)
    (hfN0 N hN) (h31 N hN) (hfNm N hN) (x0 N ω) ω hT (g := f)
    (fun l => (hfc l).measurable) hgc hZc
  have hXeq := allTimeChain_hXeq (n := N) (by omega) (v := v)
    (hfN0 N hN) (h31 N hN) (hfNm N hN) (x0 N ω) ω (T := T)
  rw [hc]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hreg
  exact ⟨h1, h2, h3, h4, h5, hXeq, hZeq⟩

/-- **Kurtz 1978, Theorem 3.3(a).**  (i) Continuous solutions `Z_N` of (1.6)
exist for every sample, `N ≥ 2` and initial state; (ii) for every such family
there is a measurable nonnegative `β^T` with a positive exponential moment such
that, almost surely, for all `N ≥ 2` and `t ∈ [0,T]`,
`‖X_N(t) - Z_N(t)‖ ≤ β^T log N / N`, where `X_N` is the chain driven by the
KMT-coupled Poisson processes. -/
theorem kurtz_theorem_three_three_a
    {f : ι → (Fin d → ℝ) → ℝ} {fN : ℕ → ι → (Fin d → ℝ) → ℝ}
    {eps : ι → ℝ} {Gamma M T : ℝ} (v : ι → Fin d → ℝ)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfNm : ∀ N : ℕ, 2 ≤ N → ∀ l, Measurable (fN N l))
    (x0 : ℕ → channelKMTSpace ι → Fin d → ℝ) :
    (∃ Z : ℕ → channelKMTSpace ι → ℝ → Fin d → ℝ,
      ∀ N, 2 ≤ N → ∀ ω, KurtzDiffusionEq f v T (x0 N ω) N ω (Z N ω)) ∧
    ∀ Z : ℕ → channelKMTSpace ι → ℝ → Fin d → ℝ,
      (∀ N, 2 ≤ N → ∀ ω, KurtzDiffusionEq f v T (x0 N ω) N ω (Z N ω)) →
      ∃ betaT : channelKMTSpace ι → ℝ,
        Measurable betaT ∧
        (∀ omega, 0 ≤ betaT omega) ∧
        (∃ lam : ℝ, 0 < lam ∧
          Integrable (fun omega => Real.exp (lam * betaT omega))
            (channelKMTMeasure ι)) ∧
        (∀ᵐ omega ∂(channelKMTMeasure ι), ∀ N : ℕ, 2 ≤ N →
          ∀ t ∈ Icc (0 : ℝ) T,
          ‖kurtzChain v fN hfN0 h31 hfNm x0 N omega t - Z N omega t‖ ≤
            betaT omega * Real.log (N : ℝ) / (N : ℝ)) :=
  ⟨exists_kurtz_diffusion_family v hM hT hfN0 h31 h32 h319 x0,
    fun Z hZ => kurtz_theorem_three_three_bound v hGamma hM hT hfN0 h31 h32
      h319 hfNm x0 Z hZ⟩

/-- **Theorem 3.3(a) in Kurtz's form**: a family `β_N^T` with the *identical
distribution* for all `N ≥ 2` (here the same random variable), measurable,
with a common exponential moment. -/
theorem kurtz_theorem_three_three_a_identicalLaw
    {f : ι → (Fin d → ℝ) → ℝ} {fN : ℕ → ι → (Fin d → ℝ) → ℝ}
    {eps : ι → ℝ} {Gamma M T : ℝ} (v : ι → Fin d → ℝ)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hfN0 : ∀ N : ℕ, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N : ℕ, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (h32 : ∀ N : ℕ, 2 ≤ N → ∀ l x,
      |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfNm : ∀ N : ℕ, 2 ≤ N → ∀ l, Measurable (fN N l))
    (x0 : ℕ → channelKMTSpace ι → Fin d → ℝ)
    (Z : ℕ → channelKMTSpace ι → ℝ → Fin d → ℝ)
    (hZ : ∀ N, 2 ≤ N → ∀ ω, KurtzDiffusionEq f v T (x0 N ω) N ω (Z N ω)) :
    ∃ beta : ℕ → channelKMTSpace ι → ℝ,
      (∀ N, Measurable (beta N)) ∧
      (∀ N ω, 0 ≤ beta N ω) ∧
      (∃ lam : ℝ, 0 < lam ∧ ∀ N,
        Integrable (fun ω => Real.exp (lam * beta N ω)) (channelKMTMeasure ι)) ∧
      (∀ N n, IdentDistrib (beta N) (beta n) (channelKMTMeasure ι)
        (channelKMTMeasure ι)) ∧
      (∀ᵐ ω ∂(channelKMTMeasure ι), ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖kurtzChain v fN hfN0 h31 hfNm x0 N ω t - Z N ω t‖ ≤
          beta N ω * Real.log (N : ℝ) / (N : ℝ)) := by
  obtain ⟨betaT, hm, hn, ⟨lam, hlam, hi⟩, hbound⟩ :=
    kurtz_theorem_three_three_bound v hGamma hM hT hfN0 h31 h32 h319 hfNm x0 Z hZ
  exact ⟨fun _ => betaT, fun _ => hm, fun _ => hn,
    ⟨lam, hlam, fun _ => hi⟩, fun _ _ => IdentDistrib.refl hm.aemeasurable, hbound⟩

end Ripple.Kurtz.StrongApprox.KurtzTheoremThreeThree

end
