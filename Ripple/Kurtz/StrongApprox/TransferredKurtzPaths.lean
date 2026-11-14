import Ripple.Kurtz.StrongApprox.TransferredKurtzFamily
import Ripple.Kurtz.StrongApprox.AllTimeKMTChain

/-!
# The chain side of the transferred Kurtz family

On the marked space `kmtFamilyMeasure P β hβ`, the transferred cell paths
`transferredCellPath N l` drive the Poisson time-change chain of population size `N`:
`transferredChain` is `globalPoissonPath` evaluated on the cell sequences
`z.2 (N, l)`. For every sample, this chain satisfies its equation with the transferred cell
paths as drivers, and together with any continuous diffusion path it has the integrability
and right-continuity required by `FixedScaleKurtzPaths`.

Hence the only path premise left in `transferred_finiteChannelKurtz_family` is the
internal-clock diffusion equation for `Z N`, driven by `transferredBrownian β N`, with a
continuous solution (`TransferredDiffusionPaths`). The corollary
`transferred_finiteChannelKurtz_family_of_diffusion` states the family theorem with this
reduced premise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The Poisson time-change chain of population size `N`, driven by the transferred cell
paths of the `N`th family. -/
def transferredChain {N : ℕ} (hN : 0 < N) (v : ι → Fin d → ℝ)
    {rate : ι → (Fin d → ℝ) → ℝ} {b : ι → ℝ}
    (h0 : ∀ l y, 0 ≤ rate l y) (hb : ∀ l y, rate l y ≤ b l)
    (hm : ∀ l, Measurable (rate l)) (x₀ : Fin d → ℝ)
    (z : Ω × (ℕ × ι → KMTPoissonCode)) : ℝ → Fin d → ℝ :=
  globalPoissonPath (N := canonicalCount) (v := v) hN h0 hb hm x₀
    (cellFamilySample fun l => z.2 (N, l))

/-- The chains of all population sizes `N ≥ 2`, started at `x0 N z`; constant below `2`. -/
def transferredChainFamily (v : ι → Fin d → ℝ)
    (fN : ℕ → ι → (Fin d → ℝ) → ℝ) (eps : ι → ℝ)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (hfNB : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (x0 : ℕ → Ω × (ℕ × ι → KMTPoissonCode) → Fin d → ℝ)
    (N : ℕ) (z : Ω × (ℕ × ι → KMTPoissonCode)) : ℝ → Fin d → ℝ :=
  if h : 2 ≤ N then
    transferredChain (N := N) (by omega) v (hfN0 N h) (hfNB N h) (hfNm N h) (x0 N z) z
  else fun _ => x0 N z

/-- The internal-clock diffusion premise at population size `N`: a continuous path solving
the diffusion equation driven by the transferred Brownian paths of the `N`th family. -/
def TransferredDiffusionPaths (N : ℕ) (f : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ)
    (T : ℝ) (β : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (Z : Ω × (ℕ × ι → KMTPoissonCode) → ℝ → Fin d → ℝ)
    (x0 : Ω × (ℕ × ι → KMTPoissonCode) → Fin d → ℝ)
    (z : Ω × (ℕ × ι → KMTPoissonCode)) : Prop :=
  Continuous (Z z) ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    Z z t = x0 z + (∫ s in (0 : ℝ)..t, tcDrift f v (Z z s)) + ∑ l,
      (transferredBrownian β N l (scaledTcClock (N : ℝ) f (Z z) l t) z / (N : ℝ)) • v l

omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in
/-- The canonical driver of the chain reads the transferred cell path. -/
theorem poisFamily_transferred (N : ℕ) (z : Ω × (ℕ × ι → KMTPoissonCode)) (l : ι) (u : ℝ) :
    ((poisFamily ι canonicalCount l u (cellFamilySample fun l => z.2 (N, l)) : ℕ) : ℝ) =
      transferredCellPath N l u z := by
  show ((poisPath canonicalCount u (cellSample (z.2 (N, l))) : ℕ) : ℝ) = _
  rw [poisPath_cellSample]
  rfl

omit [MeasurableSpace Ω] in
/-- The chain equation with the transferred cell paths as drivers. -/
theorem transferredChain_equation {N : ℕ} (hN : 0 < N) (v : ι → Fin d → ℝ)
    {rate : ι → (Fin d → ℝ) → ℝ} {b : ι → ℝ}
    (h0 : ∀ l y, 0 ≤ rate l y) (hb : ∀ l y, rate l y ≤ b l)
    (hm : ∀ l, Measurable (rate l)) (x₀ : Fin d → ℝ)
    (z : Ω × (ℕ × ι → KMTPoissonCode)) {T : ℝ} :
    ∀ t ∈ Icc (0 : ℝ) T,
      transferredChain hN v h0 hb hm x₀ z t = x₀ + ∑ l,
        (transferredCellPath N l
          (scaledTcClock (N : ℝ) rate (transferredChain hN v h0 hb hm x₀ z) l t) z /
            (N : ℝ)) • v l := by
  intro t ht
  have h := globalPoissonPath_hXeq (N := canonicalCount) (v := v)
    hN h0 hb hm x₀ (cellFamilySample fun l => z.2 (N, l)) (T := T) t ht
  refine h.trans ?_
  congr 1

omit [MeasurableSpace Ω] in
/-- Every chain-side field of `FixedScaleKurtzPaths`, and the diffusion-side regularity, for
the transferred chain and a diffusion premise at `N ≥ 2`. -/
theorem fixedScaleKurtzPaths_of_diffusion
    {N : ℕ} (hN : 2 ≤ N) (f : ι → (Fin d → ℝ) → ℝ) (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ) (M T : ℝ) (β : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (Z : ℕ → Ω × (ℕ × ι → KMTPoissonCode) → ℝ → Fin d → ℝ)
    (x0 : ℕ → Ω × (ℕ × ι → KMTPoissonCode) → Fin d → ℝ)
    (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (hfNB : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (z : Ω × (ℕ × ι → KMTPoissonCode))
    (hZ : TransferredDiffusionPaths N f v T β (Z N) (x0 N) z) :
    FixedScaleKurtzPaths N f (fN N) v T (transferredCellPath N) (transferredBrownian β N)
      (transferredChainFamily v fN eps hfN0 hfNB hfNm x0 N) (Z N) (x0 N) z := by
  have hpos : 0 < N := by omega
  have hX : transferredChainFamily v fN eps hfN0 hfNB hfNm x0 N z =
      transferredChain hpos v (hfN0 N hN) (hfNB N hN) (hfNm N hN) (x0 N z) z := by
    unfold transferredChainFamily
    rw [dif_pos hN]
  have hfm : ∀ l, Measurable (f l) := by
    intro l
    have hK : 0 ≤ eps l * M := mul_nonneg (heps l) hM
    have hL : LipschitzWith (eps l * M).toNNReal (f l) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.coe_toNNReal _ hK, Real.dist_eq, dist_eq_norm]
      exact h319 l x y
    exact hL.continuous.measurable
  have hgc : ∀ l y, |f l y| ≤ eps l := fun l y => by
    rw [abs_of_nonneg (hf0 l y)]
    exact hfB l y
  obtain ⟨hZc, hZeq⟩ := hZ
  have hreg := comparison_pathRegularity (N := canonicalCount) (v := v)
    hpos (hfN0 N hN) (hfNB N hN) (hfNm N hN) (x0 N z)
    (cellFamilySample fun l => z.2 (N, l)) hT hfm hgc hZc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hreg
  unfold FixedScaleKurtzPaths
  rw [hX]
  exact ⟨h1, h2, h3, h4, h5,
    transferredChain_equation hpos v (hfN0 N hN) (hfNB N hN) (hfNm N hN) (x0 N z) z, hZeq⟩

/-- Kurtz Theorem 3.3(a) for every population size `N ≥ 2` on one probability space, with
the chain constructed from the transferred cell paths.

Compared with `transferred_finiteChannelKurtz_family`, the chain `Xchain N` is no longer a
premise: it is `transferredChainFamily`, the Poisson time change driven by
`transferredCellPath N`, and all chain-side path premises are proved. The rates `fN N` are
additionally required to be measurable. The remaining path premise is
`TransferredDiffusionPaths` at every `N ≥ 2`: a continuous diffusion solving the
internal-clock equation driven by `transferredBrownian β N`. -/
theorem transferred_finiteChannelKurtz_family_of_diffusion
    (P : Measure Ω) [IsProbabilityMeasure P]
    (β : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hβmeas : ∀ N l t, Measurable (β N l t))
    (hβB : ∀ N, 2 ≤ N → ∀ l, IsPreBrownian (β N l) P)
    (hβcont : ∀ N, 2 ≤ N → ∀ l, ∀ᵐ ω ∂P, Continuous fun t => β N l t ω)
    (hβind : ∀ N, 2 ≤ N → iIndepFun (fun (l : ι) ω => fun t => β N l t ω) P)
    (f : ι → (Fin d → ℝ) → ℝ) (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ) (Gamma M T : ℝ)
    (Z : ℕ → Ω × (ℕ × ι → KMTPoissonCode) → ℝ → Fin d → ℝ)
    (x0 : ℕ → Ω × (ℕ × ι → KMTPoissonCode) → Fin d → ℝ)
    (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hf0 : ∀ l x, 0 ≤ f l x)
    (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (h32 : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (hDiff : ∀ N, 2 ≤ N → ∀ᵐ z ∂kmtFamilyMeasure P β hβmeas,
      TransferredDiffusionPaths N f v T β (Z N) (x0 N) z) :
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
        ‖transferredChainFamily v fN eps hfN0 h31 hfNm x0 N z t - Z N z t‖ ≤
          transferredKurtzBeta v eps Gamma M T β N z * Real.log (N : ℝ) / (N : ℝ)) :=
  transferred_finiteChannelKurtz_family P β hβmeas hβB hβcont hβind f fN v eps Gamma M T
    (transferredChainFamily v fN eps hfN0 h31 hfNm x0) Z x0 heps hGamma hM hT hf0 hfB h319
    hfN0 h31 h32
    (fun N hN => (hDiff N hN).mono fun z hz =>
      fixedScaleKurtzPaths_of_diffusion hN f fN v eps M T β Z x0 heps hM hT hf0 hfB h319
        hfN0 h31 hfNm z hz)

end Ripple.Kurtz.StrongApprox.KMTTransfer
