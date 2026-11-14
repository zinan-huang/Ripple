import Ripple.Kurtz.StrongApprox.TransferredKurtzPaths

/-!
# The diffusion premise from the SDE and the Knight identity

On the base space `P`, where the Brownian families `β N` live, a diffusion `Z N` of population
size `N` solves the physical SDE

`Z t = x0 + ∫_0^t F (Z s) ds + Σ_l (M_l t / N) • v_l`,  `F = tcDrift f v`,

where `M_l` stands for the stochastic integral `∫_0^t sqrt (N f_l (Z s)) dW_l(s)` (the
integrand `kurtzClockIntegrand`). The factor is `1/N`: the physical noise is
`N^{-1/2} Σ_l sqrt (f_l (Z)) dW_l v_l = N^{-1} Σ_l sqrt (N f_l (Z)) dW_l v_l`. The Knight
identity of the `N`th family reads `M_l t = β N l (N ∫_0^t f_l (Z s) ds)`, with the internal
clock `scaledTcClock N f Z l t` passed to `β` through `Real.toNNReal`.

These two path identities give `TransferredDiffusionPaths` on the marked space
`kmtFamilyMeasure P β hβ`, for the diffusion read through the first coordinate. Composed with
`transferred_finiteChannelKurtz_family_of_diffusion`, this gives
`transferred_finiteChannelKurtz_family_of_sde`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {d : ℕ}

/-- The physical SDE of population size `N` on `[0,T]`, sample by sample, with continuous
paths; `M l` is the stochastic integral of `sqrt (N f_l (Z))` against the `l`th physical
Brownian motion. -/
def KurtzSDEPaths (N : ℕ) (f : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ) (T : ℝ)
    (Z : ℝ → Ω → Fin d → ℝ) (M : ι → ℝ → Ω → ℝ) (x0 : Ω → Fin d → ℝ) (ω : Ω) : Prop :=
  Continuous (fun t => Z t ω) ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    Z t ω = x0 ω + (∫ s in (0 : ℝ)..t, tcDrift f v (Z s ω)) +
      ∑ l, (M l t ω / (N : ℝ)) • v l

/-- The Knight identity of the `N`th family on `[0,T]`: each stochastic integral is the
Brownian path `β N l` run on the internal clock `N ∫_0^t f_l (Z s) ds`. -/
def KurtzKnightPaths (N : ℕ) (f : ι → (Fin d → ℝ) → ℝ) (T : ℝ)
    (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (Z : ℝ → Ω → Fin d → ℝ) (M : ι → ℝ → Ω → ℝ) (ω : Ω) :
    Prop :=
  ∀ l, ∀ t ∈ Icc (0 : ℝ) T,
    M l t ω = β N l (scaledTcClock (N : ℝ) f (fun s => Z s ω) l t).toNNReal ω

omit [MeasurableSpace Ω] in
/-- Sample by sample, the SDE and the Knight identity give the internal-clock diffusion
equation driven by the transferred Brownian paths. -/
theorem transferredDiffusionPaths_of_sde {N : ℕ} {f : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {T : ℝ} {β : ℕ → ι → ℝ≥0 → Ω → ℝ}
    {Z : ℝ → Ω → Fin d → ℝ} {M : ι → ℝ → Ω → ℝ} {x0 : Ω → Fin d → ℝ}
    (z : Ω × (ℕ × ι → KMTPoissonCode))
    (hSDE : KurtzSDEPaths N f v T Z M x0 z.1)
    (hKnight : KurtzKnightPaths N f T β Z M z.1) :
    TransferredDiffusionPaths N f v T β (fun z t => Z t z.1) (fun z => x0 z.1) z := by
  obtain ⟨hc, heq⟩ := hSDE
  refine ⟨hc, fun t ht => ?_⟩
  beta_reduce
  rw [heq t ht]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hKnight l t ht]
  rfl

/-- The almost-sure SDE and Knight identity on the base space give the diffusion premise
almost surely on the marked space. -/
theorem ae_transferredDiffusionPaths_of_sde {P : Measure Ω} [IsProbabilityMeasure P]
    {β : ℕ → ι → ℝ≥0 → Ω → ℝ} {hβ : ∀ N l t, Measurable (β N l t)}
    {N : ℕ} {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ} {T : ℝ}
    {Z : ℝ → Ω → Fin d → ℝ} {M : ι → ℝ → Ω → ℝ} {x0 : Ω → Fin d → ℝ}
    (hSDE : ∀ᵐ ω ∂P, KurtzSDEPaths N f v T Z M x0 ω)
    (hKnight : ∀ᵐ ω ∂P, KurtzKnightPaths N f T β Z M ω) :
    ∀ᵐ z ∂kmtFamilyMeasure P β hβ,
      TransferredDiffusionPaths N f v T β (fun z t => Z t z.1) (fun z => x0 z.1) z := by
  have hboth : ∀ᵐ ω ∂(kmtFamilyMeasure P β hβ).map Prod.fst,
      KurtzSDEPaths N f v T Z M x0 ω ∧ KurtzKnightPaths N f T β Z M ω := by
    rw [kmtFamilyMeasure_map_fst]
    exact hSDE.and hKnight
  filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hboth] with z hz
  exact transferredDiffusionPaths_of_sde z hz.1 hz.2

/-- Kurtz Theorem 3.3(a) for every population size `N ≥ 2` on one probability space, from the
SDE of each diffusion and the Knight identity of each Brownian family.

On the base space `P`, `β N` is a finite family of independent pre-Brownian paths with
continuous sample paths for each `N ≥ 2`. The diffusion `Z N` has continuous paths and solves
the physical SDE with stochastic integrals `M N l` (`KurtzSDEPaths`), and `M N l` equals
`β N l` run on the internal clock (`KurtzKnightPaths`), almost surely on `[0,T]`. On the marked
space `kmtFamilyMeasure P β hβmeas`, the chain is the Poisson time change driven by the
transferred cell paths; its coefficient has identical laws for all `N ≥ 2`, one exponential
moment uniform in `N`, and bounds the distance between chain and diffusion for all `N ≥ 2` and
`t ∈ [0,T]` on one conull set. -/
theorem transferred_finiteChannelKurtz_family_of_sde [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (β : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hβmeas : ∀ N l t, Measurable (β N l t))
    (hβB : ∀ N, 2 ≤ N → ∀ l, IsPreBrownian (β N l) P)
    (hβcont : ∀ N, 2 ≤ N → ∀ l, ∀ᵐ ω ∂P, Continuous fun t => β N l t ω)
    (hβind : ∀ N, 2 ≤ N → iIndepFun (fun (l : ι) ω => fun t => β N l t ω) P)
    (f : ι → (Fin d → ℝ) → ℝ) (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ) (Gamma M T : ℝ)
    (Z : ℕ → ℝ → Ω → Fin d → ℝ) (Mint : ℕ → ι → ℝ → Ω → ℝ)
    (x0 : ℕ → Ω → Fin d → ℝ)
    (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf0 : ∀ l x, 0 ≤ f l x)
    (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (h32 : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (hSDE : ∀ N, 2 ≤ N → ∀ᵐ ω ∂P, KurtzSDEPaths N f v T (Z N) (Mint N) (x0 N) ω)
    (hKnight : ∀ N, 2 ≤ N → ∀ᵐ ω ∂P, KurtzKnightPaths N f T β (Z N) (Mint N) ω) :
    ∃ lambdaBeta CBeta : ℝ, 0 < lambdaBeta ∧ 0 ≤ CBeta ∧
      (∀ N, 2 ≤ N → Measurable (transferredKurtzBeta v eps Gamma M T β N)) ∧
      (∀ N, 2 ≤ N → ∀ z, 0 ≤ transferredKurtzBeta v eps Gamma M T β N z) ∧
      (∀ N N', 2 ≤ N → 2 ≤ N' →
        IdentDistrib (transferredKurtzBeta v eps Gamma M T β N)
          (transferredKurtzBeta v eps Gamma M T β N')
          (kmtFamilyMeasure P β hβmeas) (kmtFamilyMeasure P β hβmeas)) ∧
      (∀ N, 2 ≤ N →
        Integrable (fun z => Real.exp (lambdaBeta * transferredKurtzBeta v eps Gamma M T β N z))
          (kmtFamilyMeasure P β hβmeas) ∧
        ∫ z, Real.exp (lambdaBeta * transferredKurtzBeta v eps Gamma M T β N z)
          ∂kmtFamilyMeasure P β hβmeas ≤ CBeta) ∧
      (∀ᵐ z ∂kmtFamilyMeasure P β hβmeas, ∀ N, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖transferredChainFamily v fN eps hfN0 h31 hfNm (fun N z => x0 N z.1) N z t -
            Z N t z.1‖ ≤
          transferredKurtzBeta v eps Gamma M T β N z * Real.log (N : ℝ) / (N : ℝ)) :=
  transferred_finiteChannelKurtz_family_of_diffusion P β hβmeas hβB hβcont hβind f fN v eps
    Gamma M T (fun N z t => Z N t z.1) (fun N z => x0 N z.1) heps hGamma hM hT hf0 hfB h319
    hfN0 h31 hfNm h32
    (fun N hN => ae_transferredDiffusionPaths_of_sde (hSDE N hN) (hKnight N hN))

end Ripple.Kurtz.StrongApprox.KMTTransfer
