import Ripple.Kurtz.StrongApprox.TransferredDiffusionAdapter
import Ripple.Kurtz.StrongApprox.KurtzClockIntegrand
import Ripple.Stochastic.StrongSDEFixedPoint

/-!
# Time conventions between the stochastic producers and the Kurtz comparison

The strong-solution and Knight producers index time by `ℝ≥0` and integrate the rate clock over
`Ioc 0 t` against `timeMeasure` (`kurtzRateClock`). The comparison indexes time by `ℝ` and uses
the interval integral (`scaledTcClock`). This file converts between the two:

* a continuous `ℝ≥0`-indexed path `Z` extends to the continuous real-indexed path
  `t ↦ Z t.toNNReal`, which agrees with `Z` on `[0,∞)`;
* for `t ≥ 0`, `kurtzRateClock N (f l) Z t` equals `scaledTcClock N f (Z ·.toNNReal) l t`,
  and so does the time integral of `kurtzClockIntegrand ^ 2`.

`KurtzSDEPathsNN` and `KurtzKnightPathsNN` state the SDE and the Knight identity in the
producers' conventions; they imply `KurtzSDEPaths` and `KurtzKnightPaths` for the extended
paths. `kurtzSDEPathsNN_of_sdeRhs` reads the SDE from the fixed-point equation `sdeRhs` with
the unscaled channel integrals of `sqrt f_l`. The family theorem in these conventions is
`transferred_finiteChannelKurtz_family_of_nnrealSDE`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Ripple.Kurtz.StrongApprox.KMTTransfer

open Ripple.Stochastic.FilteredItoIntegralL2 Ripple.Stochastic.StrongSDE

/-! ## Paths and clocks -/

/-- A continuous `ℝ≥0`-indexed path extends continuously to the real line. -/
theorem continuous_comp_toNNReal {E : Type*} [TopologicalSpace E] {Z : ℝ≥0 → E}
    (hZ : Continuous Z) : Continuous fun t : ℝ => Z t.toNNReal :=
  hZ.comp continuous_real_toNNReal

/-- The extension agrees with the path on `[0,∞)`. -/
theorem comp_toNNReal_coe {E : Type*} (Z : ℝ≥0 → E) (t : ℝ≥0) :
    Z ((t : ℝ).toNNReal) = Z t := by
  rw [Real.toNNReal_coe]

/-- Integrals over `Ioc 0 t` against `timeMeasure` are interval integrals. -/
theorem setIntegral_timeMeasure_Ioc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (t : ℝ≥0) :
    ∫ s in Set.Ioc 0 t, g (s : ℝ) ∂timeMeasure = ∫ x in (0 : ℝ)..(t : ℝ), g x := by
  have hemb := measurableEmbedding_nnrealCoe
  have hrange : Set.range ((↑) : ℝ≥0 → ℝ) = Set.Ici 0 := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact s.coe_nonneg
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmap : timeMeasure.map ((↑) : ℝ≥0 → ℝ) = volume.restrict (Set.Ici 0) := by
    rw [timeMeasure, hemb.map_comap, hrange]
  have hpre : ((↑) : ℝ≥0 → ℝ) ⁻¹' Set.Ioc 0 (t : ℝ) = Set.Ioc 0 t := by
    ext s
    simp
  rw [intervalIntegral.integral_of_le t.coe_nonneg, ← hpre, ← hemb.setIntegral_map, hmap,
    Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioi_self.trans Set.Ioi_subset_Ici_self)]

/-- The producers' rate clock is the comparison's scaled internal clock. -/
theorem kurtzRateClock_eq_scaledTcClock {Ω ι : Type*} [Fintype ι] {d : ℕ} (N : ℕ)
    (f : ι → (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (l : ι) (t : ℝ≥0) (ω : Ω) :
    kurtzRateClock N (f l) Z t ω =
      scaledTcClock (N : ℝ) f (fun s => Z s.toNNReal ω) l (t : ℝ) := by
  unfold kurtzRateClock scaledTcClock clock
  congr 1
  have h := setIntegral_timeMeasure_Ioc (fun x => f l (Z x.toNNReal ω)) t
  simp only [Real.toNNReal_coe] at h
  exact h

/-- The same identity at a real time `t ≥ 0`. -/
theorem kurtzRateClock_toNNReal_eq_scaledTcClock {Ω ι : Type*} [Fintype ι] {d : ℕ} (N : ℕ)
    (f : ι → (Fin d → ℝ) → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (l : ι) {t : ℝ} (ht : 0 ≤ t)
    (ω : Ω) :
    kurtzRateClock N (f l) Z t.toNNReal ω =
      scaledTcClock (N : ℝ) f (fun s => Z s.toNNReal ω) l t := by
  rw [kurtzRateClock_eq_scaledTcClock, Real.coe_toNNReal t ht]

/-- The time integral of the squared integrand is the scaled internal clock. -/
theorem integral_kurtzClockIntegrand_sq_eq_scaledTcClock {Ω ι : Type*} [Fintype ι] {d : ℕ}
    (N : ℕ) {f : ι → (Fin d → ℝ) → ℝ} (hf : ∀ l x, 0 ≤ f l x)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (l : ι) (t : ℝ≥0) (ω : Ω) :
    (∫ s in Set.Ioc 0 t, (kurtzClockIntegrand N (f l) Z s ω) ^ 2 ∂timeMeasure) =
      scaledTcClock (N : ℝ) f (fun s => Z s.toNNReal ω) l (t : ℝ) := by
  rw [integral_kurtzClockIntegrand_sq N (hf l), kurtzRateClock_eq_scaledTcClock]

/-! ## The SDE and the Knight identity in the producers' conventions -/

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {d : ℕ}

/-- The physical SDE on `[0,T]` for an `ℝ≥0`-indexed diffusion with continuous paths; `M l` is
the stochastic integral of `kurtzClockIntegrand N (f l) Z`, and the drift integral uses the
real interval integral, as in `sdeRhs`. -/
def KurtzSDEPathsNN (N : ℕ) (f : ι → (Fin d → ℝ) → ℝ) (v : ι → Fin d → ℝ) (T : ℝ≥0)
    (Z : ℝ≥0 → Ω → Fin d → ℝ) (M : ι → ℝ≥0 → Ω → ℝ) (x0 : Ω → Fin d → ℝ) (ω : Ω) : Prop :=
  Continuous (fun t => Z t ω) ∧
  ∀ t ≤ T,
    Z t ω = x0 ω + (∑ l, (M l t ω / (N : ℝ)) • v l) +
      ∫ s in (0 : ℝ)..(t : ℝ), tcDrift f v (Z s.toNNReal ω)

/-- The Knight identity on `[0,T]` with the producers' rate clock. -/
def KurtzKnightPathsNN (N : ℕ) (f : ι → (Fin d → ℝ) → ℝ) (T : ℝ≥0)
    (β : ℕ → ι → ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (M : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Prop :=
  ∀ l, ∀ t ≤ T, M l t ω = β N l (kurtzRateClock N (f l) Z t ω).toNNReal ω

omit [MeasurableSpace Ω] in
theorem kurtzSDEPaths_of_nn {N : ℕ} {f : ι → (Fin d → ℝ) → ℝ} {v : ι → Fin d → ℝ}
    {T : ℝ≥0} {Z : ℝ≥0 → Ω → Fin d → ℝ} {M : ι → ℝ≥0 → Ω → ℝ} {x0 : Ω → Fin d → ℝ}
    {ω : Ω} (h : KurtzSDEPathsNN N f v T Z M x0 ω) :
    KurtzSDEPaths N f v (T : ℝ) (fun t ω => Z t.toNNReal ω) (fun l t ω => M l t.toNNReal ω)
      x0 ω := by
  obtain ⟨hc, heq⟩ := h
  refine ⟨continuous_comp_toNNReal hc, fun t ht => ?_⟩
  beta_reduce
  have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
  rw [heq t.toNNReal htT, Real.coe_toNNReal t ht.1, add_right_comm]

omit [MeasurableSpace Ω] in
theorem kurtzKnightPaths_of_nn {N : ℕ} {f : ι → (Fin d → ℝ) → ℝ} {T : ℝ≥0}
    {β : ℕ → ι → ℝ≥0 → Ω → ℝ} {Z : ℝ≥0 → Ω → Fin d → ℝ} {M : ι → ℝ≥0 → Ω → ℝ}
    {ω : Ω} (h : KurtzKnightPathsNN N f T β Z M ω) :
    KurtzKnightPaths N f (T : ℝ) β (fun t ω => Z t.toNNReal ω)
      (fun l t ω => M l t.toNNReal ω) ω := by
  intro l t ht
  beta_reduce
  have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 ht.2
  rw [h l t.toNNReal htT, kurtzRateClock_toNNReal_eq_scaledTcClock N f Z l ht.1]

omit [MeasurableSpace Ω] in
/-- The fixed-point equation `sdeRhs`, with unscaled channel integrals `ito l` of `sqrt f_l`,
gives the SDE in the form `KurtzSDEPathsNN` for `M l = sqrt N * ito l (sqrt f_l (Z))`, the
integral of `kurtzClockIntegrand N (f l) Z`. -/
theorem kurtzSDEPathsNN_of_sdeRhs {N : ℕ} (hN : 0 < N) {f : ι → (Fin d → ℝ) → ℝ}
    {v : ι → Fin d → ℝ} {T : ℝ≥0} {Z : ℝ≥0 → Ω → Fin d → ℝ} {M : ι → ℝ≥0 → Ω → ℝ}
    {ito : ι → (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ} {x₀ : Fin d → ℝ} {ω : Ω}
    (hcont : Continuous fun t => Z t ω)
    (heq : ∀ t ≤ T,
      Z t ω = sdeRhs ito v (fun l x => Real.sqrt (f l x)) (tcDrift f v) x₀ N Z t ω)
    (hscale : ∀ l, ∀ t ≤ T,
      M l t ω = Real.sqrt N * ito l (fun s ω' => Real.sqrt (f l (Z s ω'))) t ω) :
    KurtzSDEPathsNN N f v T Z M (fun _ => x₀) ω := by
  refine ⟨hcont, fun t ht => ?_⟩
  rw [heq t ht]
  unfold sdeRhs
  congr 2
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hscale l t ht]
  congr 1
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg N)
  set s := Real.sqrt (N : ℝ)
  rw [← hsq]
  field_simp

/-- Kurtz Theorem 3.3(a) for every `N ≥ 2` on one probability space, from the SDE and the
Knight identity in the producers' time conventions.

The diffusion `Z N` and the stochastic integrals `Mint N l` (integrands
`kurtzClockIntegrand N (f l) (Z N)`) are indexed by `ℝ≥0`; the Knight identity uses
`kurtzRateClock`. The comparison is stated for the extended paths `t ↦ Z N t.toNNReal`. -/
theorem transferred_finiteChannelKurtz_family_of_nnrealSDE [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (β : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hβmeas : ∀ N l t, Measurable (β N l t))
    (hβB : ∀ N, 2 ≤ N → ∀ l, IsPreBrownian (β N l) P)
    (hβcont : ∀ N, 2 ≤ N → ∀ l, ∀ᵐ ω ∂P, Continuous fun t => β N l t ω)
    (hβind : ∀ N, 2 ≤ N → iIndepFun (fun (l : ι) ω => fun t => β N l t ω) P)
    (f : ι → (Fin d → ℝ) → ℝ) (fN : ℕ → ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ) (eps : ι → ℝ) (Gamma M : ℝ) (T : ℝ≥0)
    (Z : ℕ → ℝ≥0 → Ω → Fin d → ℝ) (Mint : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (x0 : ℕ → Ω → Fin d → ℝ)
    (heps : ∀ l, 0 ≤ eps l)
    (hGamma : 0 ≤ Gamma) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x)
    (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (h32 : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (hSDE : ∀ N, 2 ≤ N → ∀ᵐ ω ∂P, KurtzSDEPathsNN N f v T (Z N) (Mint N) (x0 N) ω)
    (hKnight : ∀ N, 2 ≤ N → ∀ᵐ ω ∂P, KurtzKnightPathsNN N f T β (Z N) (Mint N) ω) :
    ∃ lambdaBeta CBeta : ℝ, 0 < lambdaBeta ∧ 0 ≤ CBeta ∧
      (∀ N, 2 ≤ N → Measurable (transferredKurtzBeta v eps Gamma M (T : ℝ) β N)) ∧
      (∀ N, 2 ≤ N → ∀ z, 0 ≤ transferredKurtzBeta v eps Gamma M (T : ℝ) β N z) ∧
      (∀ N N', 2 ≤ N → 2 ≤ N' →
        IdentDistrib (transferredKurtzBeta v eps Gamma M (T : ℝ) β N)
          (transferredKurtzBeta v eps Gamma M (T : ℝ) β N')
          (kmtFamilyMeasure P β hβmeas) (kmtFamilyMeasure P β hβmeas)) ∧
      (∀ N, 2 ≤ N →
        Integrable
          (fun z => Real.exp (lambdaBeta * transferredKurtzBeta v eps Gamma M (T : ℝ) β N z))
          (kmtFamilyMeasure P β hβmeas) ∧
        ∫ z, Real.exp (lambdaBeta * transferredKurtzBeta v eps Gamma M (T : ℝ) β N z)
          ∂kmtFamilyMeasure P β hβmeas ≤ CBeta) ∧
      (∀ᵐ z ∂kmtFamilyMeasure P β hβmeas, ∀ N, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
        ‖transferredChainFamily v fN eps hfN0 h31 hfNm (fun N z => x0 N z.1) N z t -
            Z N t.toNNReal z.1‖ ≤
          transferredKurtzBeta v eps Gamma M (T : ℝ) β N z * Real.log (N : ℝ) / (N : ℝ)) :=
  transferred_finiteChannelKurtz_family_of_sde P β hβmeas hβB hβcont hβind f fN v eps
    Gamma M (T : ℝ) (fun N t ω => Z N t.toNNReal ω) (fun N l t ω => Mint N l t.toNNReal ω)
    x0 heps hGamma hM T.coe_nonneg hf0 hfB h319 hfN0 h31 hfNm h32
    (fun N hN => (hSDE N hN).mono fun _ h => kurtzSDEPaths_of_nn h)
    (fun N hN => (hKnight N hN).mono fun _ h => kurtzKnightPaths_of_nn h)

end Ripple.Kurtz.StrongApprox.KMTTransfer
