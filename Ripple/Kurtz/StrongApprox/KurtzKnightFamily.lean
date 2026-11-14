import Ripple.Stochastic.KnightIntegralCompletion
import Ripple.Kurtz.StrongApprox.KurtzKnightClock
import Ripple.Kurtz.StrongApprox.KnightAuxiliaryChannels

/-!
# One completed Knight family for all population sizes

There are `k` channels, indexed by `Fin k`, and the state has dimension `d`.
Every population size uses the same original probability space and the same
auxiliary channel KMT factor. The rate clock and the finite-horizon integral
are the installed Kurtz objects, lifted through the first projection.

The filtration is assumed right continuous and to contain ambient null sets.
These hypotheses are not inferred from ambient null augmentation. Population
sizes below two use the auxiliary Brownian coordinates directly, making the
entire indexed family measurable without imposing state assumptions there.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped NNReal ENNReal Topology

namespace Ripple.Kurtz.StrongApprox

open Ripple.Stochastic Ripple.Stochastic.Knight
open FilteredItoIntegralCLM ContinuousItoConsistency ContinuousItoLinear
open ContinuousItoHalfLineLinear

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ} {k d : ℕ}

/-- The actual bounded-rate integral family admits completed independent
Brownian channels on one fixed product extension, simultaneously for all
population sizes at least two. All path identities hold on one event.
No exponential normalization, clock-flatness, convergence, or target Brownian
premise is assumed. -/
theorem exists_kurtzKnightFamily
    (B : Fin k → ℝ≥0 → Ω → ℝ)
    (hB : ∀ l, IsFilteredPreBrownian (B l) F P)
    (hcoord : ∀ r t : ℝ≥0, r ≤ t →
      iIndepFun (fun l ω => B l t ω - B l r ω) P)
    (hpast : ∀ r t : ℝ≥0, r ≤ t →
      Indep (MeasurableSpace.comap (fun ω l => B l t ω - B l r ω) inferInstance) (F r) P)
    (hBc : ∀ l ω, Continuous (fun t => B l t ω))
    (hBm : ∀ l t, Measurable (B l t))
    [F.IsRightContinuous]
    (hnull : ∀ t S, MeasurableSet S → P S = 0 → MeasurableSet[F t] S)
    (f : Fin k → (Fin d → ℝ) → ℝ)
    (hf : ∀ l, Continuous (f l)) (hfzero : ∀ l x, 0 ≤ f l x)
    (eps : Fin k → ℝ) (hb : ∀ l x, f l x ≤ eps l)
    (Z : ℕ → ℝ≥0 → Ω → Fin d → ℝ)
    (hZa : ∀ N, 2 ≤ N → Adapted F (Z N))
    (hZc : ∀ N, 2 ≤ N → ∀ ω, Continuous (fun t => Z N t ω))
    (T : ℝ≥0) :
    ∃ β : ℕ → Fin k → ℝ≥0 → Ω × channelKMTSpace (Fin k) → ℝ,
      (∀ N l u, Measurable (β N l u)) ∧
      (∀ N, 2 ≤ N → ∀ l,
        IsPreBrownian (β N l) (P.prod (channelKMTMeasure (Fin k)))) ∧
      (∀ N, 2 ≤ N → ∀ l, ∀ᵐ p ∂P.prod (channelKMTMeasure (Fin k)),
        Continuous (fun u => β N l u p)) ∧
      (∀ N, 2 ≤ N →
        iIndepFun (fun l p u => β N l u p) (P.prod (channelKMTMeasure (Fin k)))) ∧
      (∀ᵐ p ∂P.prod (channelKMTMeasure (Fin k)), ∀ N, 2 ≤ N →
        KMTTransfer.KurtzKnightPathsNN N f T β (fun t p => Z N t p.1)
          (fun l t p =>
            letI : IsFilteredPreBrownian (B l) F P := hB l
            continuousItoOfFun P F T (hBc l) (hBm l)
              (kurtzClockIntegrand N (f l) (Z N)) t p.1) p) := by
  classical
  let H : ℕ → Fin k → ℝ≥0 → Ω → ℝ :=
    fun N l => kurtzClockIntegrand N (f l) (Z N)
  let A : ℕ → Fin k → ℝ≥0 → Ω → ℝ≥0 :=
    fun N l => kurtzRateClockNN N (f l) (Z N)
  let K : ℕ → ℝ := fun N => ∑ l : Fin k, Real.sqrt ((N : ℝ) * eps l)
  have hK : ∀ N, 0 ≤ K N := fun N =>
    Finset.sum_nonneg fun l _ => Real.sqrt_nonneg _
  have hHb : ∀ N l t ω, |H N l t ω| ≤ K N := by
    intro N l t ω
    have hsingle : Real.sqrt ((N : ℝ) * eps l) ≤ K N :=
      Finset.single_le_sum (fun j _ => Real.sqrt_nonneg ((N : ℝ) * eps j))
        (Finset.mem_univ l)
    have h := norm_kurtzClockIntegrand_le N (hb l) (Z N) t ω
    have hnorm : |H N l t ω| ≤ Real.sqrt ((N : ℝ) * eps l) := by
      simpa only [Real.norm_eq_abs] using h
    exact hnorm.trans hsingle
  have hH : ∀ N, 2 ≤ N → ∀ l (n : ℕ),
      MemLp (Function.uncurry (H N l)) 2
        (trimMeasure_T (𝓖 := F) (μ := P) (n : ℝ≥0) (hBm l)) := by
    intro N hN l n
    exact memLp_kurtzClockIntegrand (hBm l) n N (hf l) (hb l) (hZa N hN) (hZc N hN)
  let β : ℕ → Fin k → ℝ≥0 → Ω × channelKMTSpace (Fin k) → ℝ :=
    fun N => if hN : 2 ≤ N then
      integralKnightTimeChange B hB hBc hBm (H N) (hH N hN) (A N) channelBrownian
    else fun l u p => channelBrownian l u p.2
  have hmain : ∀ N (hN : 2 ≤ N),
      (∀ l u, Measurable (β N l u)) ∧
      (∀ l, IsPreBrownian (β N l) (P.prod (channelKMTMeasure (Fin k)))) ∧
      (∀ l, ∀ᵐ p ∂P.prod (channelKMTMeasure (Fin k)),
        Continuous (fun u => β N l u p)) ∧
      iIndepFun (fun l p u => β N l u p) (P.prod (channelKMTMeasure (Fin k))) ∧
      (∀ᵐ p ∂P.prod (channelKMTMeasure (Fin k)), ∀ l t,
        channelHalfLineIto B hB hBc hBm (H N) (hH N hN) l t p.1 =
          β N l (A N l t p.1) p) := by
    intro N hN
    have hreg : ∀ l,
        Adapted F (A N l) ∧
        (∀ ω, Continuous (fun t => A N l t ω)) ∧
        (∀ ω, Monotone (fun t => A N l t ω)) ∧
        (∀ ω, A N l 0 ω = 0) := by
      intro l
      exact kurtzRateClockNN_regularity (hBm l) N (hf l) (hfzero l) (hb l)
        (hZa N hN) (hZc N hN)
    have h := completed_knight_integral B hB hcoord hpast hBc hBm hnull
      (H N) (fun l => adapted_kurtzClockIntegrand N (hf l) (hZa N hN))
      (fun l ω => continuous_kurtzClockIntegrand N (hf l) (hZc N hN ω))
      (hK N) (hHb N) (hH N hN) (A N)
      (fun l => (hreg l).1) (fun l => (hreg l).2.1)
      (fun l => (hreg l).2.2.1) (fun l => (hreg l).2.2.2)
      (fun l ω t => integral_kurtzClockIntegrand_sq_eq_nn N (hfzero l) (Z N) t ω)
      (channelBrownian (ι := Fin k)) channelBrownian_isPreBrownian
      channelBrownian_paths_independent channelBrownian_zero
      measurable_uncurry_channelBrownian
      (fun l => ae_of_all _ (channelBrownian_continuous l))
    simpa only [β, dif_pos hN] using h
  refine ⟨β, ?_, ?_, ?_, ?_, ?_⟩
  · intro N l u
    by_cases hN : 2 ≤ N
    · exact (hmain N hN).1 l u
    · simpa only [β, dif_neg hN] using
        ((measurable_channelBrownian l u).comp
          (measurable_snd : Measurable (Prod.snd : Ω × channelKMTSpace (Fin k) → _)))
  · exact fun N hN => (hmain N hN).2.1
  · exact fun N hN => (hmain N hN).2.2.1
  · exact fun N hN => (hmain N hN).2.2.2.1
  · apply ae_all_iff.mpr
    intro N
    by_cases hN : 2 ≤ N
    · have hfinite : ∀ l, ∀ᵐ ω ∂P, ∀ t ≤ T,
          channelHalfLineIto B hB hBc hBm (H N) (hH N hN) l t ω =
            (letI : IsFilteredPreBrownian (B l) F P := hB l
             continuousItoOfFun P F T (hBc l) (hBm l)
               (kurtzClockIntegrand N (f l) (Z N)) t ω) := by
        intro l
        letI := hB l
        exact kurtz_halfLineIto_eq_continuousItoOfFun (hBc l) (hBm l)
          N (hf l) (hb l) (hZa N hN) (hZc N hN) T
      have hf : MeasurePreserving
          (Prod.fst : Ω × channelKMTSpace (Fin k) → Ω)
          (P.prod (channelKMTMeasure (Fin k))) P := measurePreserving_fst
      have hfiniteAll : ∀ᵐ p ∂P.prod (channelKMTMeasure (Fin k)), ∀ l, ∀ t ≤ T,
          channelHalfLineIto B hB hBc hBm (H N) (hH N hN) l t p.1 =
            (letI : IsFilteredPreBrownian (B l) F P := hB l
             continuousItoOfFun P F T (hBc l) (hBm l)
               (kurtzClockIntegrand N (f l) (Z N)) t p.1) :=
        hf.quasiMeasurePreserving.ae (ae_all_iff.mpr hfinite)
      filter_upwards [(hmain N hN).2.2.2.2, hfiniteAll] with p hrec hfin
      intro _ l t ht
      change (letI : IsFilteredPreBrownian (B l) F P := hB l
        continuousItoOfFun P F T (hBc l) (hBm l)
          (kurtzClockIntegrand N (f l) (Z N)) t p.1) = β N l (A N l t p.1) p
      exact (hfin l t ht).symm.trans (hrec l t)
    · exact ae_of_all _ fun p hN' => False.elim (hN hN')

variable {ι : Type} [Fintype ι]

/-- The same simultaneous Knight family for an arbitrary finite channel type.
Reindexing changes only the channel labels; the auxiliary space remains one
fixed finite product, shared by every population size. -/
theorem exists_kurtzKnightFamily_fintype
    (B : ι → ℝ≥0 → Ω → ℝ)
    (hB : ∀ l, IsFilteredPreBrownian (B l) F P)
    (hcoord : ∀ r t : ℝ≥0, r ≤ t →
      iIndepFun (fun l ω => B l t ω - B l r ω) P)
    (hpast : ∀ r t : ℝ≥0, r ≤ t →
      Indep (MeasurableSpace.comap (fun ω l => B l t ω - B l r ω) inferInstance) (F r) P)
    (hBc : ∀ l ω, Continuous (fun t => B l t ω))
    (hBm : ∀ l t, Measurable (B l t))
    [F.IsRightContinuous]
    (hnull : ∀ t S, MeasurableSet S → P S = 0 → MeasurableSet[F t] S)
    (f : ι → (Fin d → ℝ) → ℝ)
    (hf : ∀ l, Continuous (f l)) (hfzero : ∀ l x, 0 ≤ f l x)
    (eps : ι → ℝ) (hb : ∀ l x, f l x ≤ eps l)
    (Z : ℕ → ℝ≥0 → Ω → Fin d → ℝ)
    (hZa : ∀ N, 2 ≤ N → Adapted F (Z N))
    (hZc : ∀ N, 2 ≤ N → ∀ ω, Continuous (fun t => Z N t ω))
    (T : ℝ≥0) :
    ∃ β : ℕ → ι → ℝ≥0 → Ω × channelKMTSpace (Fin (Fintype.card ι)) → ℝ,
      (∀ N l u, Measurable (β N l u)) ∧
      (∀ N, 2 ≤ N → ∀ l,
        IsPreBrownian (β N l) (P.prod (channelKMTMeasure (Fin (Fintype.card ι))))) ∧
      (∀ N, 2 ≤ N → ∀ l, ∀ᵐ p ∂P.prod (channelKMTMeasure (Fin (Fintype.card ι))),
        Continuous (fun u => β N l u p)) ∧
      (∀ N, 2 ≤ N →
        iIndepFun (fun l p u => β N l u p)
          (P.prod (channelKMTMeasure (Fin (Fintype.card ι))))) ∧
      (∀ᵐ p ∂P.prod (channelKMTMeasure (Fin (Fintype.card ι))), ∀ N, 2 ≤ N →
        KMTTransfer.KurtzKnightPathsNN N f T β (fun t p => Z N t p.1)
          (fun l t p =>
            letI : IsFilteredPreBrownian (B l) F P := hB l
            continuousItoOfFun P F T (hBc l) (hBm l)
              (kurtzClockIntegrand N (f l) (Z N)) t p.1) p) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hcoordFin : ∀ r t : ℝ≥0, r ≤ t →
      iIndepFun (fun i ω => B (e.symm i) t ω - B (e.symm i) r ω) P := by
    intro r t hrt
    exact iIndepFun.precomp e.symm.injective (hcoord r t hrt)
  have hpastFin : ∀ r t : ℝ≥0, r ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω (i : Fin (Fintype.card ι)) => B (e.symm i) t ω - B (e.symm i) r ω)
        inferInstance) (F r) P := by
    intro r t hrt
    apply indep_of_indep_of_le_left (hpast r t hrt)
    have heq : (fun ω (i : Fin (Fintype.card ι)) =>
        B (e.symm i) t ω - B (e.symm i) r ω) =
        (fun x : ι → ℝ => fun i : Fin (Fintype.card ι) => x (e.symm i)) ∘
          (fun ω l => B l t ω - B l r ω) := rfl
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.comap_le
      (measurable_pi_lambda _ fun i => measurable_pi_apply (e.symm i)))
  obtain ⟨βfin, hmeas, hpre, hcont, hind, hpaths⟩ :=
    exists_kurtzKnightFamily (fun i => B (e.symm i)) (fun i => hB (e.symm i))
      hcoordFin hpastFin (fun i => hBc (e.symm i)) (fun i => hBm (e.symm i)) hnull
      (fun i => f (e.symm i)) (fun i => hf (e.symm i))
      (fun i => hfzero (e.symm i)) (fun i => eps (e.symm i))
      (fun i => hb (e.symm i)) Z hZa hZc T
  let β : ℕ → ι → ℝ≥0 → Ω × channelKMTSpace (Fin (Fintype.card ι)) → ℝ :=
    fun N l => βfin N (e l)
  refine ⟨β, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun N l u => hmeas N (e l) u
  · exact fun N hN l => hpre N hN (e l)
  · exact fun N hN l => hcont N hN (e l)
  · intro N hN
    exact iIndepFun.precomp e.injective (hind N hN)
  · filter_upwards [hpaths] with p hp
    intro N hN l t ht
    have h := hp N hN (e l) t ht
    simpa only [β, Equiv.symm_apply_apply] using h

end Ripple.Kurtz.StrongApprox
