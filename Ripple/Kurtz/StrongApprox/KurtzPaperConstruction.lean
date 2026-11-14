import Ripple.Kurtz.StrongApprox.CountableRateExtension
import Ripple.Kurtz.StrongApprox.KurtzKnightTimeChange

/-!
# The concrete coupling from the printed coefficient hypotheses

Zero directions are masked. Finite-scale rates are made Borel only outside
of the countable reachable set, so no off-lattice measurability assumption
is added. All processes and the coupling measure are chosen before a time
horizon is supplied.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Topology

namespace Ripple.Kurtz.StrongApprox
open PaperSectionFourHypotheses

/-- The fixed sample type: physical channels, auxiliary completion channels,
then the conditionally attached Poisson codes for all population sizes. -/
abbrev sectionFourCouplingSpace (m : ℕ) :=
  (channelKMTSpace (Fin m) × channelKMTSpace (Fin m)) ×
    (ℕ × Fin m → KMTTransfer.KMTPoissonCode)

/-- The finite-active-support form of the paper assumptions. First and second
coordinate derivatives include their existence; second derivatives need not
be continuous. No scalar Lipschitz, full derivative, Knight, or Borel-rate
hypothesis occurs in this record. -/
structure SectionFourPaperData {m d : ℕ}
    (v : Fin m → Fin d → ℝ) (f : Fin m → (Fin d → ℝ) → ℝ)
    (fN : ℕ → Fin m → (Fin d → ℝ) → ℝ) (eps : Fin m → ℝ)
    (Gamma M firstBound secondBound : ℝ) where
  eps_nonneg : ∀ l, 0 ≤ eps l
  gamma_nonneg : 0 ≤ Gamma
  sqrt_nonneg : 0 ≤ M
  rate_nonneg : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x
  rate_bound : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l
  rate_error : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ)
  sqrt_sum : ∀ x y, ∑ l, paperNorm (v l) ^ 2 *
    (Real.sqrt (f l x) - Real.sqrt (f l y)) ^ 2 ≤ M * paperNorm (x - y) ^ 2
  partials : BoundedCoordinatePartials (tcDrift f v) firstBound secondBound

namespace SectionFourPaperData
variable {m d : ℕ} {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ}
  {fN : ℕ → Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {Gamma M firstBound secondBound : ℝ}
  (h : SectionFourPaperData v f fN eps Gamma M firstBound secondBound)

/-- Masked limiting rates. -/
def rate (_h : SectionFourPaperData v f fN eps Gamma M firstBound secondBound) :
    Fin m → (Fin d → ℝ) → ℝ := maskZeroRate v f

/-- Scalar constants derived from the summed square-root condition. -/
def sqrtConstant (_h : SectionFourPaperData v f fN eps Gamma M firstBound secondBound)
    (l : Fin m) : ℝ≥0 := (maskedChannelSqrtConstant M (v l)).toNNReal

/-- Common normalized rate Lipschitz constant; zero rate bounds contribute zero. -/
def rateConstant : ℝ := ∑ l, 2 * (h.sqrtConstant l : ℝ) / Real.sqrt (eps l)

/-- The original drift's Jacobian, assembled from coordinate derivatives. -/
def derivative := jacobian h.partials.first

/-- Borel finite-scale rates agreeing with the masked original rates on every
state reachable from `x0`. -/
def chainRate (x0 : Fin d → ℝ) (N : ℕ) :=
  countableRateExtension v x0 N h.rate (maskZeroRate v (fN N))

theorem rate_bounds : (∀ l x, 0 ≤ h.rate l x) ∧ (∀ l x, h.rate l x ≤ eps l) := by
  have hb := limiting_rate_bounds h.rate_nonneg h.rate_bound h.rate_error
  exact maskZeroRate_bounds h.eps_nonneg hb.1 hb.2

theorem sqrt_lipschitz : ∀ l x y,
    |Real.sqrt (h.rate l x) - Real.sqrt (h.rate l y)| ≤ h.sqrtConstant l * ‖x - y‖ := by
  intro l x y
  have hh := lipschitzWith_sqrt_maskZeroRate h.sqrt_nonneg h.sqrt_sum l
  simpa only [Real.dist_eq, dist_eq_norm] using hh.dist_le_mul x y

theorem rate_lipschitz : 0 ≤ h.rateConstant ∧
    ∀ l x y, |h.rate l x - h.rate l y| ≤ eps l * h.rateConstant * ‖x - y‖ :=
  common_rate_lipschitz h.eps_nonneg (fun l => (h.sqrtConstant l).coe_nonneg)
    h.rate_bounds.1 h.rate_bounds.2 h.sqrt_lipschitz

theorem rate_continuous : ∀ l, Continuous (h.rate l) :=
  continuous_rate_of_lip h.eps_nonneg h.rate_lipschitz.1 h.rate_lipschitz.2

theorem chainRate_bounds (x0 : Fin d → ℝ) :
    (∀ N, 2 ≤ N → ∀ l x, 0 ≤ h.chainRate x0 N l x) ∧
    (∀ N, 2 ≤ N → ∀ l x, h.chainRate x0 N l x ≤ eps l) := by
  have hb := fun N (hN : 2 ≤ N) =>
    maskZeroRate_bounds (v := v) h.eps_nonneg (h.rate_nonneg N hN) (h.rate_bound N hN)
  constructor <;> intro N hN
  · exact (countableRateExtension_bounds v x0 N h.rate_bounds.1 (hb N hN).2
      (hb N hN).1 h.rate_bounds.2).1
  · exact (countableRateExtension_bounds v x0 N h.rate_bounds.1 (hb N hN).2
      (hb N hN).1 h.rate_bounds.2).2

theorem chainRate_measurable (x0 : Fin d → ℝ) (N : ℕ) (l : Fin m) :
    Measurable (h.chainRate x0 N l) :=
  measurable_countableRateExtension v x0 N h.rate (maskZeroRate v (fN N))
    (fun l => (h.rate_continuous l).measurable) l

theorem chainRate_error (x0 : Fin d → ℝ) : ∀ N, 2 ≤ N → ∀ l x,
    |h.rate l x - h.chainRate x0 N l x| ≤ Gamma * eps l / (N : ℝ) := by
  intro N hN
  have hC : ∀ l, 0 ≤ Gamma * eps l / (N : ℝ) := fun l =>
    div_nonneg (mul_nonneg h.gamma_nonneg (h.eps_nonneg l)) (Nat.cast_nonneg N)
  exact countableRateExtension_error v x0 N hC
    (maskZeroRate_approximation hC (h.rate_error N hN))

theorem derivative_hypotheses :
    (∀ x, HasFDerivAt (tcDrift h.rate v) (h.derivative x) x) ∧
    (∀ x, ‖h.derivative x‖ ≤ (d : ℝ) * firstBound) ∧
    (0 ≤ (d : ℝ) ^ 2 * secondBound) ∧
    (∀ x y, ‖h.derivative y - h.derivative x‖ ≤
      ((d : ℝ) ^ 2 * secondBound) * ‖y - x‖) := by
  have hd := h.partials.sectionFour_derivative_hypotheses
  simpa only [rate, tcDrift_maskZeroRate, derivative] using hd

/-- The deterministic fluid path, whose equation has the original drift. -/
def fluid (x0 : Fin d → ℝ) := kurtzFluidLimit h.rate v x0

/-- The installed single Gaussian candidate, on the physical channel space. -/
def limit (x0 : Fin d → ℝ) := sectionFourVAll h.derivative h.rate v x0

/-- Concrete data produced before choosing a horizon. The estimate is a proved
output, not an input to the public theorem. -/
structure Construction (x0 : Fin d → ℝ) where
  Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ
  adapted : ∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)
  continuous : ∀ N ω, Continuous (fun t => Z N t ω)
  sde : ∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
    KMTTransfer.KurtzSDEPathsNN N h.rate v T (Z N)
      (channelRateIntegral T N h.rate (Z N)) (fun _ => x0) ω
  K : KnightTimeChangeData
    (channelKMTSpace (Fin m) × channelKMTSpace (Fin m))
    ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) h.rate Z
  estimate : ∀ T : ℝ≥0,
    ∃ (gamma : ℕ → sectionFourCouplingSpace m → ℝ) (eta C : ℝ),
      0 < eta ∧ (∀ N, 2 ≤ N → Measurable (gamma N)) ∧
      (∀ N, 2 ≤ N → ∀ z, 0 ≤ gamma N z) ∧
      (∀ N, 2 ≤ N → Integrable (fun z => Real.exp (eta * gamma N z))
        (KMTTransfer.kmtFamilyMeasure
          ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) K.β K.measurable_β) ∧
        ∫ z, Real.exp (eta * gamma N z)
          ∂KMTTransfer.kmtFamilyMeasure
          ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) K.β K.measurable_β ≤ C) ∧
      ∀ᵐ z ∂KMTTransfer.kmtFamilyMeasure
          ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) K.β K.measurable_β,
        ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
          ‖Real.sqrt N • (KMTTransfer.transferredChainFamily v (h.chainRate x0) eps
            (h.chainRate_bounds x0).1 (h.chainRate_bounds x0).2
            (fun N _ => h.chainRate_measurable x0 N) (fun _ _ => x0) N z t -
            h.fluid x0 t.toNNReal) - h.limit x0 (K.proj z.1) t‖ ≤
              gamma N z * Real.log (N : ℝ) / Real.sqrt N

/-- Strong solutions and the all-horizon completed Knight theorem discharge
all stochastic construction premises using only the paper data. -/
theorem construction_nonempty (x0 : Fin d → ℝ) : Nonempty (h.Construction x0) := by
  obtain ⟨Z, hZa, hZc, hSDE, happrox⟩ :=
    kurtz_theorem_four_four_of_knight_strong h.eps_nonneg h.rate_lipschitz.1
      h.rate_bounds.1 h.rate_bounds.2 h.rate_lipschitz.2 h.gamma_nonneg
      (h.chainRate_bounds x0).1 (h.chainRate_bounds x0).2
      (fun N _ => h.chainRate_measurable x0 N) (h.chainRate_error x0)
      h.sqrtConstant h.sqrt_lipschitz h.derivative_hypotheses.1
      h.derivative_hypotheses.2.1 h.derivative_hypotheses.2.2.1
      h.derivative_hypotheses.2.2.2 x0
  obtain ⟨K⟩ := knightTimeChangeData_nonempty h.rate h.rate_continuous h.rate_bounds.1 eps
    h.rate_bounds.2 Z (fun N _ => hZa N) (fun N _ => hZc N)
  exact ⟨⟨Z, hZa, hZc, hSDE, K,
    happrox _ ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) K⟩⟩

/-- A single choice, with no horizon parameter. -/
def construction (x0 : Fin d → ℝ) : h.Construction x0 :=
  Classical.choice (h.construction_nonempty x0)

/-- The coupling probability measure on the fixed sample type. -/
def couplingMeasure (x0 : Fin d → ℝ) : Measure (sectionFourCouplingSpace m) :=
  KMTTransfer.kmtFamilyMeasure
    ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)))
    (h.construction x0).K.β (h.construction x0).K.measurable_β

instance couplingMeasure_isProbability (x0 : Fin d → ℝ) :
    IsProbabilityMeasure (h.couplingMeasure x0) := by
  unfold couplingMeasure
  infer_instance

/-- Projection onto the physical channel sample. -/
def projection (x0 : Fin d → ℝ) (z : sectionFourCouplingSpace m) :=
  (h.construction x0).K.proj z.1

/-- The common physical Brownian family. -/
def brownian (x0 : Fin d → ℝ) (l : Fin m) (t : ℝ≥0) (z : sectionFourCouplingSpace m) :=
  channelBrownian l t (h.projection x0 z)

/-- All chains, with the original finite-scale rates on their reachable states. -/
def chain (x0 : Fin d → ℝ) (N : ℕ) (z : sectionFourCouplingSpace m) (t : ℝ) :=
  KMTTransfer.transferredChainFamily v (h.chainRate x0) eps
    (h.chainRate_bounds x0).1 (h.chainRate_bounds x0).2
    (fun N _ => h.chainRate_measurable x0 N) (fun _ _ => x0) N z t

/-- Strong diffusions pulled to the final coupling. -/
def diffusion (x0 : Fin d → ℝ) (N : ℕ) (t : ℝ≥0) (z : sectionFourCouplingSpace m) :=
  (h.construction x0).Z N t (h.projection x0 z)

/-- The single limit process pulled to the final coupling. -/
def gaussian (x0 : Fin d → ℝ) (z : sectionFourCouplingSpace m) (t : ℝ) :=
  h.limit x0 (h.projection x0 z) t

/-- A measure-preserving projection transports all physical-channel laws and
common events to the final coupling. -/
theorem projection_measurePreserving (x0 : Fin d → ℝ) :
    MeasurePreserving (h.projection x0) (h.couplingMeasure x0)
      (channelKMTMeasure (Fin m)) := by
  let K := (h.construction x0).K
  refine ⟨K.measurePreserving.measurable.comp measurable_fst, ?_⟩
  change (KMTTransfer.kmtFamilyMeasure
    ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)))
    K.β K.measurable_β).map (K.proj ∘ Prod.fst) = channelKMTMeasure (Fin m)
  rw [← Measure.map_map K.measurePreserving.measurable measurable_fst,
    KMTTransfer.kmtFamilyMeasure_map_fst, K.measurePreserving.map_eq]

end SectionFourPaperData
end Ripple.Kurtz.StrongApprox
