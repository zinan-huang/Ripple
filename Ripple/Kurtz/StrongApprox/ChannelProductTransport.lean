-- Ripple/Kurtz/StrongApprox/ChannelProductTransport.lean
import Ripple.Kurtz.StrongApprox.KMTCoefficientAdapter

/-!
# Independent all-time KMT channels

Kurtz 1978, Theorem 3.3 (p. 232) is stated for finitely many channels
`l`, with independent Brownian motions `B_l` and Poisson processes `Y_l` that
each satisfy the conclusion of Lemma 3.1 (p. 230).  Each channel here is one
coordinate of the product of the constructed all-time couplings.  Brownian
dyadic laws, Poisson finite-grid laws, and exponential moments are
transported by the measure-preserving coordinate projections; channels are
independent coordinates of the infinite product.  All samplewise assertions
are collected in `channelKMTGoodEvent`, whose complement has measure zero.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open AllTimeKMT AllTimeKurtzMoment AllTimeKMTLaws
open AllTimeKMTBrownianLaw AllTimeKMTPoissonLaw

/-- A sample contains one complete all-time coupling for each channel. -/
abbrev channelKMTSpace (ι : Type*) := ι → AllTimeKMTSpace

/-- Product law of the independently constructed channel couplings. -/
def channelKMTMeasure (ι : Type*) : Measure (channelKMTSpace ι) :=
  Measure.infinitePi fun _ : ι => allTimeKMTMeasure

instance channelKMTMeasure_isProbabilityMeasure (ι : Type*) :
    IsProbabilityMeasure (channelKMTMeasure ι) := by
  unfold channelKMTMeasure
  infer_instance

variable {ι : Type*}

def channelKMTBrownian (l : ι) (t : ℝ) (ω : channelKMTSpace ι) : ℝ :=
  allTimeKMTBrownian t (ω l)

def channelKMTPoisson (l : ι) (t : ℝ) (ω : channelKMTSpace ι) : ℕ :=
  allTimeKMTPoisson t (ω l)

def channelKMTCoefficient (l : ι) (ω : channelKMTSpace ι) : ℝ :=
  kmtCoefficient (ω l)

theorem channelKMTEval_measurePreserving (l : ι) :
    MeasurePreserving (fun ω : channelKMTSpace ι => ω l)
      (channelKMTMeasure ι) allTimeKMTMeasure := by
  simpa [channelKMTMeasure] using
    (measurePreserving_eval_infinitePi (fun _ : ι => allTimeKMTMeasure) l)

/-- Independent coordinates contain the complete coupled Poisson/Brownian paths. -/
theorem channelKMTEval_iIndep :
    iIndepFun (fun l (ω : channelKMTSpace ι) => ω l) (channelKMTMeasure ι) := by
  exact iIndepFun_infinitePi (P := fun _ : ι => allTimeKMTMeasure)
    (X := fun _ x => x) (fun _ => measurable_id)

theorem measurable_channelKMTBrownian (l : ι) (t : ℝ) :
    Measurable (channelKMTBrownian l t) :=
  (measurable_allTimeKMTBrownian t).comp (measurable_pi_apply l)

theorem measurable_channelKMTPoisson (l : ι) (t : ℝ) :
    Measurable (channelKMTPoisson l t) :=
  (measurable_allTimeKMTPoisson t).comp (measurable_pi_apply l)

theorem measurable_channelKMTCoefficient (l : ι) :
    Measurable (channelKMTCoefficient l) :=
  measurable_kmtCoefficient.comp (measurable_pi_apply l)

theorem channelKMTCoefficient_nonneg (l : ι) (ω : channelKMTSpace ι) :
    0 ≤ channelKMTCoefficient l ω := kmtCoefficient_nonneg (ω l)

theorem channelKMTBrownian_continuous (l : ι) (ω : channelKMTSpace ι) :
    Continuous (fun t => channelKMTBrownian l t ω) :=
  allTimeKMTBrownian_continuous (ω l)

/-- Transport a sample assertion through a channel projection. -/
theorem channelKMT_ae_pullback (l : ι) {p : AllTimeKMTSpace → Prop}
    (hp : ∀ᵐ x ∂allTimeKMTMeasure, p x) :
    ∀ᵐ ω ∂channelKMTMeasure ι, p (ω l) := by
  apply MeasureTheory.ae_of_ae_map (channelKMTEval_measurePreserving l).measurable.aemeasurable
  rw [(channelKMTEval_measurePreserving l).map_eq]
  exact hp

/-- Pullback of the complete dyadic Brownian structure, including independence. -/
theorem channelKMTBrownian_dyadicBrownianOn (l : ι) (j : ℕ) :
    DyadicBrownianOn (channelKMTMeasure ι) (channelKMTBrownian l) ((2 : ℝ) ^ j) := by
  let hB := allTimeKMTBrownian_dyadicBrownianOn j
  let hp := channelKMTEval_measurePreserving l
  refine ⟨measurable_channelKMTBrownian l,
    Filter.Eventually.of_forall (channelKMTBrownian_continuous l), ?_, ?_⟩
  · intro m k
    have hm : Measurable (fun x : AllTimeKMTSpace =>
        allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ j) m (k.val + 1)) x -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ j) m k.val) x) :=
      (measurable_allTimeKMTBrownian _).sub (measurable_allTimeKMTBrownian _)
    change (channelKMTMeasure ι).map ((fun x : AllTimeKMTSpace =>
      allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ j) m (k.val + 1)) x -
        allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ j) m k.val) x) ∘
          (fun ω : channelKMTSpace ι => ω l)) = _
    rw [← Measure.map_map hm hp.measurable, hp.map_eq]
    exact hB.cell_law m k
  · intro m
    exact (iIndepFun_comp_map_iff hp.measurable
      (G := fun (k : Fin (2 ^ m)) (x : AllTimeKMTSpace) =>
        allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ j) m (k.val + 1)) x -
          allTimeKMTBrownian (brownianDyadicPoint ((2 : ℝ) ^ j) m k.val) x)
      (fun k => (measurable_allTimeKMTBrownian _).sub
        (measurable_allTimeKMTBrownian _))).mpr
      (by rw [hp.map_eq]; exact hB.cell_independent m)

theorem integrable_exp_channelKMTCoefficient (l : ι) {θ : ℝ}
    (hθpos : 0 < θ) (hθrate : θ < allTimeKurtzGamma) :
    Integrable (fun ω => Real.exp (θ * channelKMTCoefficient l ω))
      (channelKMTMeasure ι) := by
  have h : Integrable (fun x => Real.exp (θ * kmtCoefficient x))
      ((channelKMTMeasure ι).map (fun ω => ω l)) := by
    rw [(channelKMTEval_measurePreserving l).map_eq]
    exact integrable_exp_kmtCoefficient hθpos hθrate
  have hm : Measurable (fun x => Real.exp (θ * kmtCoefficient x)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_kmtCoefficient)
  rw [integrable_map_measure hm.aestronglyMeasurable
    (measurable_pi_apply l).aemeasurable] at h
  exact h

/-- The same positive exponent works for every coordinate. -/
theorem channelKMTCoefficient_exponentialMoment :
    ∃ θ : ℝ, 0 < θ ∧ ∀ l : ι,
      Integrable (fun ω => Real.exp (θ * channelKMTCoefficient l ω))
        (channelKMTMeasure ι) := by
  refine ⟨allTimeKurtzGamma / 2, half_pos allTimeKurtzGamma_pos, fun l => ?_⟩
  exact integrable_exp_channelKMTCoefficient l (half_pos allTimeKurtzGamma_pos)
    (half_lt_self allTimeKurtzGamma_pos)

/-- Vector of increments in one channel, with the source normalization. -/
def channelKMTPoissonIncrementVector (l : ι) {r : ℕ}
    (grid : Fin (r + 1) → ℝ) (ω : channelKMTSpace ι) : Fin r → ℕ :=
  allTimeKMTPoissonIncrementVector grid (ω l)

theorem channelKMTPoisson_incrementVector_law (l : ι) {r : ℕ}
    (grid : Fin (r + 1) → ℝ) (hzero : grid 0 = 0) (hstrict : StrictMono grid) :
    (channelKMTMeasure ι).map (channelKMTPoissonIncrementVector l grid) =
      DyadicConditionalPoissonPath.poissonIncrementProduct grid := by
  change (channelKMTMeasure ι).map
    (allTimeKMTPoissonIncrementVector grid ∘ (fun ω => ω l)) = _
  rw [← Measure.map_map (measurable_allTimeKMTPoissonIncrementVector grid)
    (measurable_pi_apply l), (channelKMTEval_measurePreserving l).map_eq]
  exact allTimeKMTPoisson_incrementVector_law grid hzero hstrict

theorem channelKMTPoisson_increment_iIndep (l : ι) {r : ℕ}
    (grid : Fin (r + 1) → ℝ) (hzero : grid 0 = 0) (hstrict : StrictMono grid) :
    iIndepFun (fun i ω => channelKMTPoissonIncrementVector l grid ω i)
      (channelKMTMeasure ι) := by
  exact (iIndepFun_comp_map_iff (measurable_pi_apply l)
    (G := fun (i : Fin r) (x : AllTimeKMTSpace) =>
      allTimeKMTPoissonIncrementVector grid x i)
    (fun i => (measurable_pi_apply i).comp
      (measurable_allTimeKMTPoissonIncrementVector grid))).mpr
    (by rw [(channelKMTEval_measurePreserving l).map_eq]
        exact allTimeKMTPoisson_increment_iIndep grid hzero hstrict)

/-- One event for all channels, all real times, and every samplewise assertion. -/
def channelKMTGoodEvent (ι : Type*) : Set (channelKMTSpace ι) :=
  {ω | ∀ l : ι,
    allTimeKMTXi (ω l) ≠ ⊤ ∧
    Continuous (fun t => channelKMTBrownian l t ω) ∧
    0 ≤ channelKMTCoefficient l ω ∧
    (∀ s t : ℝ, s ≤ t → channelKMTPoisson l s ω ≤ channelKMTPoisson l t ω) ∧
    (∀ t : ℝ, ContinuousWithinAt (fun s => (channelKMTPoisson l s ω : ℝ)) (Ici t) t) ∧
    (∀ t : ℝ, 0 ≤ t →
      |(channelKMTPoisson l t ω : ℝ) - t - channelKMTBrownian l t ω| ≤
        channelKMTCoefficient l ω * Real.log (max 2 t)) ∧
    (∀ t : ℝ, 0 ≤ t →
      channelKMTPoisson l t ω =
          allTimeKMTPoissonLeft t (ω l) + allTimeKMTPoissonMultiplicity t (ω l) ∧
        allTimeKMTPoissonMultiplicity t (ω l) ≤ 1 ∧
        (0 < channelKMTPoisson l t ω - allTimeKMTPoissonLeft t (ω l) →
          channelKMTPoisson l t ω - allTimeKMTPoissonLeft t (ω l) = 1))}

theorem channelKMTGoodEvent_ae [Fintype ι] :
    ∀ᵐ ω ∂channelKMTMeasure ι, ω ∈ channelKMTGoodEvent ι := by
  apply ae_all_iff.mpr
  intro l
  filter_upwards [channelKMT_ae_pullback l allTimeKMTXi_ae_ne_top,
    channelKMT_ae_pullback l allTimeKMTPoisson_unitJumps_ae] with ω hXi hJumps
  refine ⟨hXi, channelKMTBrownian_continuous l ω,
    channelKMTCoefficient_nonneg l ω, ?_, ?_, ?_, hJumps⟩
  · exact fun s t hst => allTimeKMTPoisson_mono (ω l) hst
  · exact allTimeKMTPoisson_rightContinuous (ω l)
  · exact fun t ht => kmtCoefficient_bound (ω l) hXi ht

theorem channelKMTGoodEvent_compl_null [Fintype ι] :
    channelKMTMeasure ι (channelKMTGoodEvent ι)ᶜ = 0 := by
  exact ae_iff.mp (channelKMTGoodEvent_ae (ι := ι))

theorem channelKMT_bound_ae [Fintype ι] :
    ∀ᵐ ω ∂channelKMTMeasure ι, ∀ l : ι, ∀ t : ℝ, 0 ≤ t →
      |(channelKMTPoisson l t ω : ℝ) - t - channelKMTBrownian l t ω| ≤
        channelKMTCoefficient l ω * Real.log (max 2 t) := by
  filter_upwards [channelKMTGoodEvent_ae (ι := ι)] with ω hω
  exact fun l => (hω l).2.2.2.2.2.1

end Ripple.Kurtz.StrongApprox


end
