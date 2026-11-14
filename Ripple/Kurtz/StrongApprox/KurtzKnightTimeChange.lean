import Ripple.Kurtz.StrongApprox.KurtzKnightFamily
import Ripple.Kurtz.StrongApprox.RightContinuousChannelFiltration
import Ripple.Kurtz.StrongApprox.KurtzTheoremFourFourOfKnight

/-!
# Horizon-compatible Knight data for the Kurtz strong solutions, and Theorem 4.4

The completed half-line integral determines the Brownian family before any
finite horizon is chosen (`exists_kurtzKnightFamily_all_horizons`). On the concrete channel
space, with the right-continuous channel filtration, its reconstruction identities transfer to
the augmented filtration used by the public strong-approximation interface
(`exists_channelKnightFamily`, `knightTimeChangeData_nonempty`): the extension is
`channelKMTSpace × channelKMTSpace` with the product measure and the first projection.

`kurtz_theorem_four_four_channel` is `kurtz_theorem_four_four_of_knight` for the strong
solutions of `exists_kurtz_strong_solution_family` and this Knight family: Kurtz's Theorem 4.4
on the channel space with no Knight premise.
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

/-- One completed Brownian family reconstructs the actual rate integrals on
every finite horizon. The existential family precedes the horizon quantifier;
the exceptional null set may depend on the horizon. -/
theorem exists_kurtzKnightFamily_all_horizons
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
    :
    ∃ β : ℕ → Fin k → ℝ≥0 → Ω × channelKMTSpace (Fin k) → ℝ,
      (∀ N l u, Measurable (β N l u)) ∧
      (∀ N, 2 ≤ N → ∀ l,
        IsPreBrownian (β N l) (P.prod (channelKMTMeasure (Fin k)))) ∧
      (∀ N, 2 ≤ N → ∀ l, ∀ᵐ p ∂P.prod (channelKMTMeasure (Fin k)),
        Continuous (fun u => β N l u p)) ∧
      (∀ N, 2 ≤ N →
        iIndepFun (fun l p u => β N l u p) (P.prod (channelKMTMeasure (Fin k)))) ∧
      (∀ T : ℝ≥0, ∀ᵐ p ∂P.prod (channelKMTMeasure (Fin k)), ∀ N, 2 ≤ N →
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
  · intro T
    apply ae_all_iff.mpr
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

variable {m : ℕ}

/-- The Knight family on the product extension of the channel space, with the noise integrals
written with respect to the augmented filtration (`channelRateIntegral`). -/
theorem exists_channelKnightFamily
    (f : Fin m → (Fin d → ℝ) → ℝ)
    (hf : ∀ l, Continuous (f l)) (hfzero : ∀ l x, 0 ≤ f l x)
    (eps : Fin m → ℝ) (hb : ∀ l x, f l x ≤ eps l)
    (Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ)
    (hZa : ∀ N, 2 ≤ N → ∀ t,
      Measurable[augmentedChannelBrownianFiltration t] (Z N t))
    (hZc : ∀ N, 2 ≤ N → ∀ ω, Continuous (fun t => Z N t ω)) :
    ∃ β : ℕ → Fin m → ℝ≥0 → channelKMTSpace (Fin m) × channelKMTSpace (Fin m) → ℝ,
      (∀ N l u, Measurable (β N l u)) ∧
      (∀ N, 2 ≤ N → ∀ l,
        IsPreBrownian (β N l) ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)))) ∧
      (∀ N, 2 ≤ N → ∀ l,
        ∀ᵐ p ∂(channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)),
          Continuous (fun u => β N l u p)) ∧
      (∀ N, 2 ≤ N → iIndepFun (fun (l : Fin m) p => fun u => β N l u p)
        ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)))) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0,
        ∀ᵐ p ∂(channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)),
          KMTTransfer.KurtzKnightPathsNN N f T β (fun t p => Z N t p.1)
            (fun l t p => channelRateIntegral T N f (Z N) l t p.1) p) := by
  have hZaRight : ∀ N, 2 ≤ N → Adapted
      (rightContinuousChannelFiltration (ι := Fin m)) (Z N) := by
    intro N hN t
    exact (hZa N hN t).mono (augmented_le_rightContinuousChannelFiltration t) le_rfl
  have hcoord : ∀ r t : ℝ≥0, r ≤ t →
      iIndepFun (fun l ω => channelBrownian (ι := Fin m) l t ω -
        channelBrownian l r ω) (channelKMTMeasure (Fin m)) := by
    intro r t _
    exact channelBrownian_paths_independent.comp
      (fun _ x => x t - x r)
      (fun _ => (measurable_pi_apply t).sub (measurable_pi_apply r))
  obtain ⟨β, hmeas, hpre, hcont, hind, hpaths⟩ :=
    exists_kurtzKnightFamily_all_horizons
      (F := rightContinuousChannelFiltration)
      (channelBrownian (ι := Fin m)) channelBrownian_isFilteredPreBrownian_rightCont
      hcoord (fun _ _ hrt => channelBrownian_vectorIncrement_indep_rightCont hrt)
      channelBrownian_continuous measurable_channelBrownian
      rightContinuousChannelFiltration_null f hf hfzero eps hb Z hZaRight hZc
  refine ⟨β, hmeas, hpre, hcont, hind, fun N hN T => ?_⟩
  filter_upwards [hpaths T] with p hp
  have h := hp N hN
  change KMTTransfer.KurtzKnightPathsNN N f T β
    (fun t p => Z N t p.1)
    (fun l t p => rightContChannelRateIntegral T N f (Z N) l t p.1) p at h
  rw [rightContChannelRateIntegral_eq hf hb (hZa N hN) (hZc N hN)] at h
  exact h

/-- Bounded nonnegative continuous rates and augmented-adapted continuous state
paths supply the Knight data on one product of the original channel space and
an auxiliary channel space. No relation between different population sizes is
required of the state family. -/
theorem knightTimeChangeData_nonempty
    (f : Fin m → (Fin d → ℝ) → ℝ)
    (hf : ∀ l, Continuous (f l)) (hfzero : ∀ l x, 0 ≤ f l x)
    (eps : Fin m → ℝ) (hb : ∀ l x, f l x ≤ eps l)
    (Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ)
    (hZa : ∀ N, 2 ≤ N → ∀ t,
      Measurable[augmentedChannelBrownianFiltration t] (Z N t))
    (hZc : ∀ N, 2 ≤ N → ∀ ω, Continuous (fun t => Z N t ω)) :
    Nonempty (KnightTimeChangeData
      (channelKMTSpace (Fin m) × channelKMTSpace (Fin m))
      ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) f Z) := by
  obtain ⟨β, hmeas, hpre, hcont, hind, hknight⟩ :=
    exists_channelKnightFamily f hf hfzero eps hb Z hZa hZc
  exact ⟨{
    proj := Prod.fst
    measurePreserving := measurePreserving_fst
    β := β
    measurable_β := hmeas
    isPreBrownian := hpre
    continuous_β := hcont
    iIndep := hind
    knight := hknight }⟩

section Theorem

variable {v : Fin m → Fin d → ℝ} {f : Fin m → (Fin d → ℝ) → ℝ} {eps : Fin m → ℝ}
  {M : ℝ} {F' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)} {L1 L2 : ℝ}

/-- **Kurtz, Theorem 4.4, on the channel space.** Under the model conditions ((3.1), (3.2),
(3.19), the square-root condition, and a derivative `F'` of the drift with `‖F'‖ ≤ L₁` and
`L₂`-Lipschitz), there are adapted strong solutions `Z_N` of Kurtz's SDE with continuous paths
on the channel space, and Brownian families `β`, independent over channels for each `N ≥ 2`, on
the product extension `channelKMTSpace × channelKMTSpace`, with the Knight identity on every
horizon, such that on the transferred space `kmtFamilyMeasure (P ⊗ P) β`, with the chains `X_N`
of the time-change construction, the fluid limit `X` and the all-time Gaussian limit `V`: for
every horizon `T` there are measurable `γ_N ≥ 0`, `η > 0` and `C` with `∫ exp (η γ_N) ≤ C` for
all `N ≥ 2`, and almost surely, for all `N ≥ 2` and `t ∈ [0, T]`,
`‖sqrt N (X_N t - X t) - V t‖ ≤ γ_N log N / sqrt N`. The processes precede `T`. -/
theorem kurtz_theorem_four_four_channel (heps : ∀ l, 0 ≤ eps l) (hM : 0 ≤ M)
    (hf0 : ∀ l x, 0 ≤ f l x) (hfB : ∀ l x, f l x ≤ eps l)
    (h319 : ∀ l x y, |f l x - f l y| ≤ eps l * M * ‖x - y‖)
    {fN : ℕ → Fin m → (Fin d → ℝ) → ℝ} {Gamma : ℝ} (hGamma : 0 ≤ Gamma)
    (hfN0 : ∀ N, 2 ≤ N → ∀ l x, 0 ≤ fN N l x)
    (h31 : ∀ N, 2 ≤ N → ∀ l x, fN N l x ≤ eps l)
    (hfNm : ∀ N, 2 ≤ N → ∀ l, Measurable (fN N l))
    (h32 : ∀ N, 2 ≤ N → ∀ l x, |f l x - fN N l x| ≤ Gamma * eps l / (N : ℝ))
    (Lg : Fin m → ℝ≥0)
    (hLg : ∀ l x y, |Real.sqrt (f l x) - Real.sqrt (f l y)| ≤ Lg l * ‖x - y‖)
    (hFd : ∀ x, HasFDerivAt (tcDrift f v) (F' x) x) (hL1 : ∀ x, ‖F' x‖ ≤ L1)
    (hL2n : 0 ≤ L2) (hL2 : ∀ x y, ‖F' y - F' x‖ ≤ L2 * ‖y - x‖) (x0 : Fin d → ℝ) :
    ∃ Z : ℕ → ℝ≥0 → channelKMTSpace (Fin m) → Fin d → ℝ,
      (∀ N t, Measurable[augmentedChannelBrownianFiltration t] (Z N t)) ∧
      (∀ N ω, Continuous fun t => Z N t ω) ∧
      (∀ N, 2 ≤ N → ∀ T : ℝ≥0, ∀ᵐ ω ∂channelKMTMeasure (Fin m),
        KMTTransfer.KurtzSDEPathsNN N f v T (Z N) (channelRateIntegral T N f (Z N))
          (fun _ => x0) ω) ∧
      ∃ (β : ℕ → Fin m → ℝ≥0 → channelKMTSpace (Fin m) × channelKMTSpace (Fin m) → ℝ)
        (hβ : ∀ N l t, Measurable (β N l t)),
        (∀ N, 2 ≤ N → ∀ l,
          IsPreBrownian (β N l) ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)))) ∧
        (∀ N, 2 ≤ N → iIndepFun (fun (l : Fin m) p => fun t => β N l t p)
          ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)))) ∧
        (∀ N, 2 ≤ N → ∀ T : ℝ≥0,
          ∀ᵐ p ∂(channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m)),
            KMTTransfer.KurtzKnightPathsNN N f T β (fun t p => Z N t p.1)
              (fun l t p => channelRateIntegral T N f (Z N) l t p.1) p) ∧
        ∀ T : ℝ≥0, ∃ (gamma : ℕ → (channelKMTSpace (Fin m) × channelKMTSpace (Fin m)) ×
            (ℕ × Fin m → KMTTransfer.KMTPoissonCode) → ℝ) (eta C : ℝ),
          0 < eta ∧ (∀ N, 2 ≤ N → Measurable (gamma N)) ∧
          (∀ N, 2 ≤ N → ∀ z, 0 ≤ gamma N z) ∧
          (∀ N, 2 ≤ N →
            Integrable (fun z => Real.exp (eta * gamma N z)) (KMTTransfer.kmtFamilyMeasure
              ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) β hβ) ∧
            ∫ z, Real.exp (eta * gamma N z) ∂KMTTransfer.kmtFamilyMeasure
              ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) β hβ ≤ C) ∧
          ∀ᵐ z ∂KMTTransfer.kmtFamilyMeasure
              ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) β hβ,
            ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Icc (0 : ℝ) T,
              ‖Real.sqrt N • (KMTTransfer.transferredChainFamily v fN eps hfN0 h31 hfNm
                  (fun _ _ => x0) N z t - kurtzFluidLimit f v x0 t.toNNReal) -
                sectionFourVAll F' f v x0 z.1.1 t‖ ≤
                gamma N z * Real.log (N : ℝ) / Real.sqrt N := by
  have hf := continuous_rate_of_lip heps hM h319
  obtain ⟨Z, hZa, hZc, -, hSDE⟩ :=
    exists_kurtz_strong_solution_family (v := v) heps hM hf0 hfB h319 Lg hLg x0
  obtain ⟨β, hmeas, hpre, hcont, hind, hknight⟩ :=
    exists_channelKnightFamily f hf hf0 eps hfB Z (fun N _ => hZa N) (fun N _ => hZc N)
  let K : KnightTimeChangeData (channelKMTSpace (Fin m) × channelKMTSpace (Fin m))
      ((channelKMTMeasure (Fin m)).prod (channelKMTMeasure (Fin m))) f Z :=
    { proj := Prod.fst
      measurePreserving := measurePreserving_fst
      β := β
      measurable_β := hmeas
      isPreBrownian := hpre
      continuous_β := hcont
      iIndep := hind
      knight := hknight }
  refine ⟨Z, hZa, hZc, hSDE, β, hmeas, hpre, hind, hknight, fun T => ?_⟩
  exact kurtz_theorem_four_four_of_knight heps hM hf0 hfB h319 hGamma hfN0 h31 hfNm h32
    (Lg := fun l => (Lg l : ℝ)) (fun l => (Lg l).coe_nonneg) hLg hFd hL1 hL2n hL2 hZa hZc hSDE
    K T

end Theorem

end Ripple.Kurtz.StrongApprox
