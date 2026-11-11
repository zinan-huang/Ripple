import Tri.PaperLemma6
import Tri.Emulation
import Tri.RelaxedProductiveMonotone
import Tri.ByzantinePhase1StochOrder
import Tri.StoppedHitMonotone

/-!
# Lemma 6 for rates selected from the full past

Condon, Hajiaghayi, Kirkpatrick and Mañuch, "Approximate majority analyses
using tri-molecular chemical reaction networks", Natural Computing 19
(2020), Lemma 6 and §5.

A state contains the current X count and all earlier productive counts.
The policy reads the complete nonempty transcript before each transition.
The whole history is frozen at the upper target; its current-count marginal
is exactly the target-frozen productive kernel.

The proof compares every such policy with the fixed minimal firing rate.
The comparison holds at every finite horizon. The existing fixed-rate
trace estimate supplies the two exponential terms without any new
population, independence, or rate-regularity premise.
-/

namespace Tri

open scoped ENNReal NNReal

/-- All earlier counts in reverse order, together with the current count. -/
abbrev LemmaSixHistory := List ℕ × ℕ

/-- The policy receives a nonempty transcript, with the current count first. -/
def lemmaSixHistoryTranscript (h : LemmaSixHistory) : List ℕ :=
  h.2 :: h.1

/-- One productive reaction chosen using the entire current transcript. -/
noncomputable def lemmaSixHistoryRawStep
    (ρ : List ℕ → RelaxedRate) (n : ℕ)
    (h : LemmaSixHistory) : PMF LemmaSixHistory :=
  (relaxedProductiveTriChain (ρ (lemmaSixHistoryTranscript h)) n h.2).map
    (fun x => (lemmaSixHistoryTranscript h, x))

/-- The history is stopped when its current count reaches the target. -/
noncomputable def lemmaSixHistoryStep
    (ρ : List ℕ → RelaxedRate) (n Δ : ℕ) :
    LemmaSixHistory → PMF LemmaSixHistory :=
  freeze (fun h => Lemma3Target n Δ h.2) (lemmaSixHistoryRawStep ρ n)

/-- The stopped history law at the specified productive-step horizon. -/
noncomputable def lemmaSixHistoryLaw
    (ρ : List ℕ → RelaxedRate) (n Δ T x₀ : ℕ) :
    PMF LemmaSixHistory :=
  iter (lemmaSixHistoryStep ρ n Δ) T ([], x₀)

/-- Failure to enter the doubled-gap target by the specified horizon. -/
noncomputable def lemmaSixHistoryFailure
    (ρ : List ℕ → RelaxedRate) (n Δ T x₀ : ℕ) : ℝ≥0∞ :=
  terminalFailureMass (lemmaSixHistoryLaw ρ n Δ T x₀)
    (fun h => Lemma3Target n Δ h.2)

/-- The raw current-count marginal uses the rate selected from the full history. -/
theorem lemmaSixHistoryRawStep_map_current
    (ρ : List ℕ → RelaxedRate) (n : ℕ) (h : LemmaSixHistory) :
    (lemmaSixHistoryRawStep ρ n h).map Prod.snd =
      relaxedProductiveTriChain (ρ (lemmaSixHistoryTranscript h)) n h.2 := by
  unfold lemmaSixHistoryRawStep
  rw [PMF.map_comp]
  change
    (relaxedProductiveTriChain (ρ (lemmaSixHistoryTranscript h)) n h.2).map id = _
  exact PMF.map_id _

/-- Every raw step retains the entire preceding nonempty transcript. -/
theorem lemmaSixHistoryRawStep_map_past
    (ρ : List ℕ → RelaxedRate) (n : ℕ) (h : LemmaSixHistory) :
    (lemmaSixHistoryRawStep ρ n h).map Prod.fst =
      PMF.pure (lemmaSixHistoryTranscript h) := by
  unfold lemmaSixHistoryRawStep
  rw [PMF.map_comp]
  exact PMF.map_const _ _

/-- This is exactly the requested frozen productive law for the current count. -/
theorem lemmaSixHistoryStep_map_current
    (ρ : List ℕ → RelaxedRate) (n Δ : ℕ) (h : LemmaSixHistory) :
    (lemmaSixHistoryStep ρ n Δ h).map Prod.snd =
      freeze (Lemma3Target n Δ)
        (relaxedProductiveTriChain (ρ (lemmaSixHistoryTranscript h)) n) h.2 := by
  unfold lemmaSixHistoryStep
  by_cases hh : Lemma3Target n Δ h.2
  · rw [freeze_of_mem h hh, freeze_of_mem h.2 hh, PMF.pure_map]
  · rw [freeze_of_not_mem h hh, freeze_of_not_mem h.2 hh,
      lemmaSixHistoryRawStep_map_current]

/-- Once the target is reached, the stopped history remains unchanged. -/
theorem lemmaSixHistoryStep_of_target
    (ρ : List ℕ → RelaxedRate) (n Δ : ℕ) (h : LemmaSixHistory)
    (hh : Lemma3Target n Δ h.2) :
    lemmaSixHistoryStep ρ n Δ h = PMF.pure h :=
  freeze_of_mem h hh

/-- A fixed policy gives an exact Markov projection at every history. -/
theorem lemmaSixHistoryStep_const_intertwines
    (r : RelaxedRate) (n Δ : ℕ) :
    Intertwines Prod.snd
      (lemmaSixHistoryStep (fun _ => r) n Δ)
      (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n)) := by
  intro h
  exact lemmaSixHistoryStep_map_current (fun _ => r) n Δ h

/-- The current-state marginal of every fixed-policy history law is the
existing homogeneous frozen chain, for every horizon and initial history. -/
theorem lemmaSixHistory_const_map_current
    (r : RelaxedRate) (n Δ T : ℕ) (h : LemmaSixHistory) :
    (iter (lemmaSixHistoryStep (fun _ => r) n Δ) T h).map Prod.snd =
      iter (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n)) T h.2 :=
  iter_map_of_intertwines
    (lemmaSixHistoryStep_const_intertwines r n Δ) T h

/-- Exact equality of failure masses, with no rate or population premises. -/
theorem lemmaSixHistoryFailure_const
    (r : RelaxedRate) (n Δ T x₀ : ℕ) :
    lemmaSixHistoryFailure (fun _ => r) n Δ T x₀ =
      terminalFailureMass
        (iter (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n)) T x₀)
        (Lemma3Target n Δ) := by
  unfold lemmaSixHistoryFailure lemmaSixHistoryLaw
  rw [← terminalFailureMass_map
    (iter (lemmaSixHistoryStep (fun _ => r) n Δ) T ([], x₀))
    Prod.snd (Lemma3Target n Δ)]
  rw [lemmaSixHistory_const_map_current]

/-- Increasing a positive firing rate stochastically increases one
productive transition, including the totalized boundary states. -/
theorem relaxedProductiveTriChain_expect_mono_rate
    (rlo rhi : RelaxedRate) (n x : ℕ)
    (hlo : 0 < rlo.fire) (hrate : rlo.fire ≤ rhi.fire)
    (f : ℕ → ℝ≥0∞) (hf : Monotone f) :
    expect (relaxedProductiveTriChain rlo n x) f ≤
      expect (relaxedProductiveTriChain rhi n x) f := by
  classical
  by_cases hphys : 3 ≤ n ∧ 0 < x ∧ x < n
  · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 :=
      ⟨x - 1, by omega⟩
    obtain ⟨b, hpop⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - (a + 2), by omega⟩
    have hprodlo :
        relaxedTriStep rlo (a + 1) (b + 1) (by omega) a +
          relaxedTriStep rlo (a + 1) (b + 1) (by omega) (a + 2) ≠ 0 :=
      lemma6_live_productive_nonzero rlo hphys.1 hpop hlo
    have hprodhi :
        relaxedTriStep rhi (a + 1) (b + 1) (by omega) a +
          relaxedTriStep rhi (a + 1) (b + 1) (by omega) (a + 2) ≠ 0 :=
      lemma6_live_productive_nonzero rhi hphys.1 hpop (hlo.trans_le hrate)
    rw [relaxedProductiveTriChain_apply rlo hpop hphys.1 hprodlo,
      relaxedProductiveTriChain_apply rhi hpop hphys.1 hprodhi]
    exact Byzantine.relaxedProductiveTriInterior_expect_mono_fire
      rlo rhi a b (by omega) hrate hprodlo hprodhi f hf
  · have hdegenerate (r : RelaxedRate) :
        relaxedProductiveTriChain r n x = PMF.pure x := by
      unfold relaxedProductiveTriChain
      rw [dif_neg hphys]
    rw [hdegenerate rlo, hdegenerate rhi]

/-- A history-adapted rate bounded below by a positive fixed rate cannot
increase failure to reach the upper Lemma 6 target at any finite horizon. -/
theorem lemmaSixHistory_failure_le_fixed
    (r : RelaxedRate) (ρ : List ℕ → RelaxedRate) (n Δ : ℕ)
    (hfire : 0 < r.fire)
    (hrate : ∀ hist, r.fire ≤ (ρ hist).fire)
    (T : ℕ) (h : LemmaSixHistory) :
    terminalFailureMass
        (iter (lemmaSixHistoryStep ρ n Δ) T h)
        (fun q => Lemma3Target n Δ q.2) ≤
      terminalFailureMass
        (iter (freeze (Lemma3Target n Δ)
          (relaxedProductiveTriChain r n)) T h.2)
        (Lemma3Target n Δ) := by
  classical
  let Kctl : List ℕ → ℕ → PMF (List ℕ × ℕ) :=
    fun hist x =>
      (relaxedProductiveTriChain (ρ (x :: hist)) n x).map
        (fun y => (x :: hist, y))
  have hupper :
      ∀ ⦃i j : ℕ⦄, i ≤ j →
        Lemma3Target n Δ i → Lemma3Target n Δ j := by
    intro i j hij hi
    unfold Lemma3Target at *
    omega
  have hdom :
      ∀ hist i (f : ℕ → ℝ≥0∞), Monotone f →
        expect (relaxedProductiveTriChain r n i) f ≤
          expect (Kctl hist i) (fun q => f q.2) := by
    intro hist i f hf
    simpa only [Kctl, expect_map] using
      relaxedProductiveTriChain_expect_mono_rate
        r (ρ (i :: hist)) n i hfire (hrate (i :: hist)) f hf
  have hcomp :=
    stoppedControlledBand_failure_le_reference
      (fun _ : ℕ => False) (Lemma3Target n Δ)
      (relaxedProductiveTriChain r n) Kctl
      (by intro i j hij hj; exact False.elim hj)
      hupper
      (fun f hf => relaxedProductiveTriChain_expect_monotone r n hfire f hf)
      hdom T h.1 h.2
  have hctl :
      freeze
        (fun q : List ℕ × ℕ => False ∨ Lemma3Target n Δ q.2)
        (fun q => Kctl q.1 q.2) =
      lemmaSixHistoryStep ρ n Δ := by
    change
      freeze
        (fun q : LemmaSixHistory => False ∨ Lemma3Target n Δ q.2)
        (lemmaSixHistoryRawStep ρ n) =
      freeze
        (fun q : LemmaSixHistory => Lemma3Target n Δ q.2)
        (lemmaSixHistoryRawStep ρ n)
    exact lemma7_freeze_congr _ _ _ (fun _ => Iff.of_eq (false_or _))
  have href :
      freeze (fun x : ℕ => False ∨ Lemma3Target n Δ x)
        (relaxedProductiveTriChain r n) =
      freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n) :=
    lemma7_freeze_congr _ _ _ (fun _ => Iff.of_eq (false_or _))
  rw [hctl, href] at hcomp
  exact hcomp

/-- The smallest firing rate allowed by the Lemma 6 rate premise.
The proof parameter is only the existing nondegeneracy hypothesis. -/
noncomputable def lemmaSixFloorRate (n Δ : ℕ) (hΔn : Δ < n) :
    RelaxedRate where
  fire := 1 - ((Δ : NNReal) / ((2 * n : ℕ) : NNReal))
  idle := (Δ : NNReal) / ((2 * n : ℕ) : NNReal)
  add_eq_one := by
    apply tsub_add_cancel_of_le
    have hdenpos : (0 : NNReal) < ((2 * n : ℕ) : NNReal) := by
      exact_mod_cast (show 0 < 2 * n by omega)
    exact le_of_lt ((div_lt_one hdenpos).mpr
      (by exact_mod_cast (show Δ < 2 * n by omega)))

theorem lemmaSixFloorRate_add (n Δ : ℕ) (hΔn : Δ < n) :
    (lemmaSixFloorRate n Δ hΔn).fire +
        (Δ : NNReal) / ((2 * n : ℕ) : NNReal) = 1 :=
  (lemmaSixFloorRate n Δ hΔn).add_eq_one

theorem lemmaSixFloorRate_admissible
    (n Δ : ℕ) (hΔn : Δ < n) :
    (1 : NNReal) ≤
      (lemmaSixFloorRate n Δ hΔn).fire +
        (Δ : NNReal) / ((2 * n : ℕ) : NNReal) :=
  le_of_eq (lemmaSixFloorRate_add n Δ hΔn).symm

theorem lemmaSixFloorRate_fire_pos
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    0 < (lemmaSixFloorRate n Δ hΔn).fire :=
  lemma6_fire_pos hΔ0 hΔn
    (lemmaSixFloorRate_admissible n Δ hΔn)

theorem lemmaSixFloorRate_fire_le
    {n Δ : ℕ} (hΔn : Δ < n) (r : RelaxedRate)
    (hrate : (1 : NNReal) ≤
      r.fire + (Δ : NNReal) / ((2 * n : ℕ) : NNReal)) :
    (lemmaSixFloorRate n Δ hΔn).fire ≤ r.fire :=
  Byzantine.fire_le_of_common_idle_allowance
    (lemmaSixFloorRate_add n Δ hΔn) hrate

/-- The two-term form of the existing fixed-rate Lemma 6 proof.
This retains both terms before the common-exponent simplification. -/
theorem lemma6_fixed_two_term
    (r : RelaxedRate) (n x₀ y₀ Δ : ℕ)
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate :
      (1 : NNReal) ≤
        r.fire + (Δ : NNReal) / ((2 * n : ℕ) : NNReal)) :
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n))
          (5 * n) x₀)
        (Lemma3Target n Δ) ≤
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (8 * (n : ℝ) + 4 * (Δ : ℝ))))) +
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (80 * (n : ℝ) + 16 * (Δ : ℝ))))) := by
  have hfire := lemma6_fire_pos hΔ0 hΔn hrate
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      (Lemma3Target n Δ)
      (relaxedProductiveTriChain r n)
      (lemma6TraceStep r n x₀ Δ)
      Lemma3Trace.toX
      (lemma6TraceStep_isLazyProjection r n x₀ Δ)
      (5 * n) (lemma3Initial x₀)
  calc
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (relaxedProductiveTriChain r n))
          (5 * n) x₀)
        (Lemma3Target n Δ) ≤
      terminalFailureMass
        (iter (lemma6TraceStep r n x₀ Δ) (5 * n)
          (lemma3Initial x₀))
        (fun q => Lemma3Target n Δ q.x) := by
      simpa [Lemma3Trace.toX, lemma3Initial] using hprojection
    _ ≤ _ :=
      lemma6Trace_failure_explicit hpop hgap hΔ0 hΔn hfire hrate

/-- Condon, Hajiaghayi, Kirkpatrick and Mañuch (2020), Lemma 6 and §5:
the two-term productive-clock bound for an arbitrary history-adapted rate
satisfying the same floor at every history. -/
theorem lemma6_paper_adapted
    (ρ : List ℕ → RelaxedRate) (n x₀ y₀ Δ : ℕ)
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate : ∀ hist,
      (1 : NNReal) ≤
        (ρ hist).fire + (Δ : NNReal) / ((2 * n : ℕ) : NNReal)) :
    lemmaSixHistoryFailure ρ n Δ (5 * n) x₀ ≤
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (8 * (n : ℝ) + 4 * (Δ : ℝ))))) +
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (80 * (n : ℝ) + 16 * (Δ : ℝ))))) := by
  have hcompare :
      lemmaSixHistoryFailure ρ n Δ (5 * n) x₀ ≤
        terminalFailureMass
          (iter
            (freeze (Lemma3Target n Δ)
              (relaxedProductiveTriChain
                (lemmaSixFloorRate n Δ hΔn) n))
            (5 * n) x₀)
          (Lemma3Target n Δ) := by
    exact lemmaSixHistory_failure_le_fixed
      (lemmaSixFloorRate n Δ hΔn) ρ n Δ
      (lemmaSixFloorRate_fire_pos hΔ0 hΔn)
      (fun hist => lemmaSixFloorRate_fire_le hΔn (ρ hist) (hrate hist))
      (5 * n) ([], x₀)
  exact hcompare.trans
    (lemma6_fixed_two_term (lemmaSixFloorRate n Δ hΔn)
      n x₀ y₀ Δ hpop hgap hΔ0 hΔn
      (lemmaSixFloorRate_admissible n Δ hΔn))

/-- The common-exponent form of the adapted Lemma 6 bound, with the
same coefficient 2, denominator 96n, and productive deadline 5n. -/
theorem lemma6_paper_adapted_common
    (ρ : List ℕ → RelaxedRate) (n x₀ y₀ Δ : ℕ)
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hrate : ∀ hist,
      (1 : NNReal) ≤
        (ρ hist).fire + (Δ : NNReal) / ((2 * n : ℕ) : NNReal)) :
    lemmaSixHistoryFailure ρ n Δ (5 * n) x₀ ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (96 * (n : ℝ))))) :=
  (lemma6_paper_adapted ρ n x₀ y₀ Δ hpop hgap hΔ0 hΔn hrate).trans
    (lemma6_explicit_errors_le_common hΔ0 hΔn)

end Tri
