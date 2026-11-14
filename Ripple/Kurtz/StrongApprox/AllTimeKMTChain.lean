-- Ripple/Kurtz/StrongApprox/AllTimeKMTChain.lean
import Ripple.Kurtz.StrongApprox.ComparisonPathRegularity
import Ripple.Kurtz.StrongApprox.AllTimeKMTPoissonLaw

/-!
# The chain driven by the KMT-coupled all-time Poisson paths

`globalPoissonPath` reads its channel drivers from `ω : ι → PathSpace Ω`
through `poisFamily`, which is `poisPath N t (ω l)`.  For the canonical
base `N = canonicalCount`, the all-time Poisson path of one channel is the
counting path `cellPath t (poissonCellSeq ω)` of a cell sequence, and
`cellSample` repackages a cell sequence as an element of
`PathSpace CanonicalCountSpace` with `poisPath_cellSample`.  Hence one all-time
KMT sample per channel is a channel-driver sample, and the readout is exactly
`allTimeKMTPoisson`.

Nothing depends on the scale `n`: the same `Y l = allTimeKMTPoisson · (ω l)` is
the driver of the chain `X_n` for every `n`, as Kurtz's Theorem 3.3 requires.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.AllTimeKMTChain

open MeasureTheory ProbabilityTheory Set Finset Filter Topology
open scoped ENNReal BigOperators
open AllTimeKMT AllTimeKMTLaws AllTimeKMTPoissonLaw

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The channel driver map -/

/-- One all-time KMT sample per channel, as a channel-driver sample. -/
def allTimeChannelDriver (ω : ι → AllTimeKMTSpace) :
    ι → PathSpace CanonicalCountSpace :=
  cellFamilySample (fun l => poissonCellSeq (ω l))

theorem measurable_allTimeChannelDriver :
    Measurable (allTimeChannelDriver (ι := ι)) := by
  apply measurable_pi_lambda
  intro l
  exact measurable_cellSample.comp
    (measurable_poissonCellSeq.comp (measurable_pi_apply l))

/-- The driver of channel `l`, read as a real-argument Poisson path. -/
def allTimeKMTDriverY (ω : ι → AllTimeKMTSpace) (l : ι) (u : ℝ) : ℝ :=
  (allTimeKMTPoisson u (ω l) : ℝ)

/-- **Readout identity**: `poisFamily` of the channel driver is the all-time
KMT Poisson path of that channel, for `u ≥ 0`. -/
theorem poisFamily_allTimeChannelDriver (ω : ι → AllTimeKMTSpace) (l : ι)
    {u : ℝ} (hu : 0 ≤ u) :
    poisFamily ι canonicalCount l u (allTimeChannelDriver ω) =
      allTimeKMTPoisson u (ω l) := by
  show poisPath canonicalCount u (cellSample (poissonCellSeq (ω l))) = _
  rw [poisPath_cellSample, allTimeKMTPoisson_eq_cellPath hu]

/-! ## The chain driven by these paths -/

/-- The chain `X_n` of the Poisson time change, driven by the all-time KMT
Poisson paths; the driver does not depend on `n`. -/
def allTimeChain
    {n : ℕ} (hn : 0 < n) (v : ι → Fin d → ℝ)
    {β : ι → (Fin d → ℝ) → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → AllTimeKMTSpace) : ℝ → Fin d → ℝ :=
  globalPoissonPath (N := canonicalCount) (v := v) hn hβ0 hβb hβm x₀
    (allTimeChannelDriver ω)

/-- The chain equation in terms of `allTimeKMTPoisson`: the consumer's
`hXeq` with `Y = allTimeKMTDriverY ω`, the same for every scale. -/
theorem allTimeChain_hXeq
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → AllTimeKMTSpace) {T : ℝ} :
    ∀ t ∈ Icc (0 : ℝ) T,
      allTimeChain hn v hβ0 hβb hβm x₀ ω t =
        x₀ + ∑ l,
          (allTimeKMTDriverY ω l
            (scaledTcClock (n : ℝ) β
              (allTimeChain hn v hβ0 hβb hβm x₀ ω) l t) / (n : ℝ)) • v l := by
  intro t ht
  have h := globalPoissonPath_hXeq (N := canonicalCount) (v := v)
    hn hβ0 hβb hβm x₀ (allTimeChannelDriver ω) (T := T) t ht
  refine h.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have hnn : 0 ≤ scaledTcClock (n : ℝ) β
      (globalPoissonPath (N := canonicalCount) (v := v) hn hβ0 hβb hβm x₀
        (allTimeChannelDriver ω)) l t :=
    mul_nonneg (Nat.cast_nonneg n) (clock_nonneg hβ0 l ht.1)
  rw [poisFamily_allTimeChannelDriver ω l hnn]
  rfl

/-- The chain driven by the all-time paths has the regularity of the pair
(chain, continuous `Z`) required by the comparison; sample by sample. -/
theorem allTimeChain_regularity
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → AllTimeKMTSpace) {T : ℝ} (hT : 0 ≤ T)
    {g : ι → (Fin d → ℝ) → ℝ} (hgm : ∀ l, Measurable (g l))
    {c : ι → ℝ} (hgc : ∀ l y, |g l y| ≤ c l)
    {Z : ℝ → Fin d → ℝ} (hZ : Continuous Z) :
    let X := allTimeChain hn v hβ0 hβb hβm x₀ ω
    (∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => β l (X s)) volume 0 t) ∧
    (∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => g l (X s)) volume 0 t) ∧
    (∀ l t, t ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun s => g l (Z s)) volume 0 t) ∧
    IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T) ∧
    (∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t) :=
  comparison_pathRegularity (N := canonicalCount) (v := v)
    hn hβ0 hβb hβm x₀ (allTimeChannelDriver ω) hT hgm hgc hZ

/-- **All premises of the comparison, for the KMT-coupled objects.**  With
`W l = allTimeKMTBrownian · (ω l)` (continuous for every sample) and the chain
driven by `Y l = allTimeKMTPoisson · (ω l)`, there is a continuous diffusion
`Z` and the exact hypotheses `hXeq`, `hZeq`, `hbetaX`, `hbetaZ`, `huint`,
`hurc` hold on `[0,T]` for every sample of the product space. -/
theorem allTimeChain_hPaths
    {n : ℕ} (hn : 0 < n)
    {β : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {b : ι → ℝ}
    (hβ0 : ∀ l y, 0 ≤ β l y)
    (hβb : ∀ l y, β l y ≤ b l)
    (hβm : ∀ l, Measurable (β l))
    (x₀ : Fin d → ℝ) (ω : ι → AllTimeKMTSpace) {T : ℝ} (hT : 0 ≤ T)
    (f : ι → (Fin d → ℝ) → ℝ) (hf : ∀ l, Continuous (f l))
    (B : ι → ℝ) (hf0 : ∀ l y, 0 ≤ f l y) (hfB : ∀ l y, f l y ≤ B l) :
    let X := allTimeChain hn v hβ0 hβb hβm x₀ ω
    (∀ t ∈ Icc (0 : ℝ) T,
      X t = x₀ + ∑ l,
        (allTimeKMTDriverY ω l (scaledTcClock (n : ℝ) β X l t) / (n : ℝ)) •
          v l) ∧
    ∃ Z : ℝ → Fin d → ℝ,
      Continuous Z ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        Z t = x₀ + (∫ s in (0 : ℝ)..t, tcDrift f v (Z s)) +
          ∑ l, (allTimeKMTBrownian (scaledTcClock (n : ℝ) f Z l t) (ω l) /
            (n : ℝ)) • v l) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => β l (X s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (X s)) volume 0 t) ∧
      (∀ l t, t ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => f l (Z s)) volume 0 t) ∧
      IntegrableOn (fun s => ‖X s - Z s‖) (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Ico (0 : ℝ) T,
        ContinuousWithinAt (fun s => ‖X s - Z s‖) (Ioi t) t) := by
  intro X
  refine ⟨allTimeChain_hXeq hn hβ0 hβb hβm x₀ ω, ?_⟩
  have hpaths := comparison_hPaths_actual (N := canonicalCount) (v := v)
    hn hβ0 hβb hβm x₀ (allTimeChannelDriver ω) hT
    (fun l t => allTimeKMTBrownian t (ω l))
    (fun l => allTimeKMTBrownian_continuous (ω l))
    f hf B hf0 hfB
  exact hpaths.2

end Ripple.Kurtz.StrongApprox.AllTimeKMTChain

end
