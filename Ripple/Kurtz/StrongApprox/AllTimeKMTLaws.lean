-- Ripple/Kurtz/StrongApprox/AllTimeKMTLaws.lean
import Ripple.Kurtz.StrongApprox.AllTimeKurtzMoment

/-!
# Pathwise structure of the concatenated all-time paths

For every sample the all-time Poisson path is monotone, integer valued and
right continuous, and the all-time Brownian path is continuous on all of `ℝ`.
These come from the block formula on the closed block
`[start J, start (J+1)]`:
`path s = (sum of the completed blocks) + (block J path at s - start J)`.
Both block paths vanish at local time `0`, which makes the formula valid at
the right end point.

The unit-jump statement is in the vocabulary of K19: the left count and the
multiplicity of the block `J` with `start J ≤ t ≤ start (J+1)` (the earlier
block at a block start).

Not in this file: the laws.  The Brownian `cell_law` and `cell_independent`
for `DyadicBrownianOn allTimeKMTMeasure W H`, and the product-Poisson law of
increments over a finite grid, need cross-block independence and Gaussian
or Poisson additivity.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox.AllTimeKMTLaws

open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology
open AllTimeKMT ContinuousFiniteHorizonKMT AllTimeKurtzMoment

theorem allTimeBlockStart_lt_succ (J : ℕ) :
    allTimeBlockStart J < allTimeBlockStart (J + 1) := by
  rw [allTimeBlockStart_succ]
  unfold allTimeBlockLength
  have : (0 : ℝ) < 2 ^ J := by positivity
  linarith

theorem allTimeBlockStart_nonneg (J : ℕ) : 0 ≤ allTimeBlockStart J := by
  unfold allTimeBlockStart allTimeBlockLength
  have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
  linarith

/-! ## Values at time zero of the block paths -/

theorem continuousKMTPoisson_zero_time (K : ℕ) (z : ContinuousKMTSpace K) :
    continuousKMTPoisson K 0 z = 0 := by
  simpa using continuousKMTPoisson_natCast K 0 z

theorem continuousKMTBrownian_zero_time (K : ℕ) (z : ContinuousKMTSpace K) :
    continuousKMTBrownian K 0 z = 0 := by
  have h := continuousKMTBrownian_natCast K 0 (Nat.zero_le _) z
  simpa using h

theorem allTimeKMTPoisson_zero_time (ω : AllTimeKMTSpace) :
    allTimeKMTPoisson 0 ω = 0 := by
  rw [allTimeKMTPoisson_of_nonneg 0 le_rfl]
  have hb : allTimeBlock 0 = 0 :=
    allTimeBlock_eq_of_bounds le_rfl (by simp) (by
      simp [allTimeBlockStart, allTimeBlockLength])
  rw [hb]
  simp [allTimeLocalTime, hb, continuousKMTPoisson_zero_time]

theorem allTimeKMTBrownian_zero_time (ω : AllTimeKMTSpace) :
    allTimeKMTBrownian 0 ω = 0 := by
  rw [allTimeKMTBrownian_of_nonneg 0 le_rfl]
  have hb : allTimeBlock 0 = 0 :=
    allTimeBlock_eq_of_bounds le_rfl (by simp) (by
      simp [allTimeBlockStart, allTimeBlockLength])
  rw [hb]
  simp [allTimeLocalTime, hb, continuousKMTBrownian_zero_time]

theorem allTimeKMTPoisson_of_neg {t : ℝ} (ht : t < 0) (ω : AllTimeKMTSpace) :
    allTimeKMTPoisson t ω = 0 := by
  simp [allTimeKMTPoisson, not_le.mpr ht]

theorem allTimeKMTBrownian_of_neg {t : ℝ} (ht : t < 0) (ω : AllTimeKMTSpace) :
    allTimeKMTBrownian t ω = 0 := by
  simp [allTimeKMTBrownian, not_le.mpr ht]

/-! ## The closed-block formula -/

/-- Completed-block totals of the Poisson and Brownian paths. -/
def allTimeCumPoisson (J : ℕ) (ω : AllTimeKMTSpace) : ℕ :=
  ∑ j ∈ range J, continuousKMTPoisson j (allTimeBlockLength j) (ω j)

def allTimeCumBrownian (J : ℕ) (ω : AllTimeKMTSpace) : ℝ :=
  ∑ j ∈ range J, continuousKMTBrownian j (allTimeBlockLength j) (ω j)

theorem allTimeKMTPoisson_closed_block (ω : AllTimeKMTSpace) {J : ℕ} {s : ℝ}
    (h1 : allTimeBlockStart J ≤ s) (h2 : s ≤ allTimeBlockStart (J + 1)) :
    allTimeKMTPoisson s ω = allTimeCumPoisson J ω +
      continuousKMTPoisson J (s - allTimeBlockStart J) (ω J) := by
  have hstart : 0 ≤ allTimeBlockStart J := by
    unfold allTimeBlockStart allTimeBlockLength
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    linarith
  have hs0 : 0 ≤ s := le_trans hstart h1
  rw [allTimeKMTPoisson_of_nonneg s hs0]
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hb := allTimeBlock_eq_of_bounds hs0 h1 hlt
    rw [hb]
    simp [allTimeLocalTime, hb, allTimeCumPoisson]
  · have hb : allTimeBlock s = J + 1 := by
      apply allTimeBlock_eq_of_bounds hs0 (le_of_eq heq.symm)
      rw [heq]
      exact allTimeBlockStart_lt_succ (J + 1)
    rw [hb]
    have hloc : allTimeLocalTime s = 0 := by
      unfold allTimeLocalTime
      rw [hb, heq]
      ring
    rw [hloc, continuousKMTPoisson_zero_time, Finset.sum_range_succ]
    have hsub : s - allTimeBlockStart J = allTimeBlockLength J := by
      rw [heq, allTimeBlockStart_succ]
      ring
    rw [hsub]
    simp [allTimeCumPoisson]

theorem allTimeKMTBrownian_closed_block (ω : AllTimeKMTSpace) {J : ℕ} {s : ℝ}
    (h1 : allTimeBlockStart J ≤ s) (h2 : s ≤ allTimeBlockStart (J + 1)) :
    allTimeKMTBrownian s ω = allTimeCumBrownian J ω +
      continuousKMTBrownian J (s - allTimeBlockStart J) (ω J) := by
  have hstart : 0 ≤ allTimeBlockStart J := by
    unfold allTimeBlockStart allTimeBlockLength
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    linarith
  have hs0 : 0 ≤ s := le_trans hstart h1
  rw [allTimeKMTBrownian_of_nonneg s hs0]
  rcases lt_or_eq_of_le h2 with hlt | heq
  · have hb := allTimeBlock_eq_of_bounds hs0 h1 hlt
    rw [hb]
    simp [allTimeLocalTime, hb, allTimeCumBrownian]
  · have hb : allTimeBlock s = J + 1 := by
      apply allTimeBlock_eq_of_bounds hs0 (le_of_eq heq.symm)
      rw [heq]
      exact allTimeBlockStart_lt_succ (J + 1)
    rw [hb]
    have hloc : allTimeLocalTime s = 0 := by
      unfold allTimeLocalTime
      rw [hb, heq]
      ring
    rw [hloc, continuousKMTBrownian_zero_time, Finset.sum_range_succ]
    have hsub : s - allTimeBlockStart J = allTimeBlockLength J := by
      rw [heq, allTimeBlockStart_succ]
      ring
    rw [hsub]
    simp [allTimeCumBrownian]

/-! ## Monotone and integer valued Poisson path -/

theorem allTimeCumPoisson_mono (ω : AllTimeKMTSpace) :
    Monotone (fun J => allTimeCumPoisson J ω) := by
  apply monotone_nat_of_le_succ
  intro J
  unfold allTimeCumPoisson
  rw [Finset.sum_range_succ]
  exact Nat.le_add_right _ _

theorem allTimeKMTPoisson_mono (ω : AllTimeKMTSpace) {s t : ℝ} (hst : s ≤ t) :
    allTimeKMTPoisson s ω ≤ allTimeKMTPoisson t ω := by
  by_cases hs : s < 0
  · rw [allTimeKMTPoisson_of_neg hs]
    exact Nat.zero_le _
  have hs0 : 0 ≤ s := le_of_not_gt hs
  have ht0 : 0 ≤ t := le_trans hs0 hst
  set Js := allTimeBlock s with hJs
  set Jt := allTimeBlock t with hJt
  have hbs := allTimeBlock_bounds hs0
  have hbt := allTimeBlock_bounds ht0
  rw [← hJs] at hbs
  rw [← hJt] at hbt
  have hJle : Js ≤ Jt := by
    by_contra hnot
    have : Jt + 1 ≤ Js := by omega
    have hm := allTimeBlockStart_mono this
    linarith [hbt.2, hbs.1]
  rw [allTimeKMTPoisson_closed_block ω hbs.1 hbs.2.le,
    allTimeKMTPoisson_closed_block ω hbt.1 hbt.2.le]
  rcases lt_or_eq_of_le hJle with hlt | heq
  · -- strictly earlier block
    have h1 : continuousKMTPoisson Js (s - allTimeBlockStart Js) (ω Js) ≤
        continuousKMTPoisson Js (allTimeBlockLength Js) (ω Js) := by
      apply continuousKMTPoisson_mono
      have := hbs.2
      rw [allTimeBlockStart_succ] at this
      linarith
    have h2 : allTimeCumPoisson Js ω +
        continuousKMTPoisson Js (allTimeBlockLength Js) (ω Js) =
        allTimeCumPoisson (Js + 1) ω := by
      unfold allTimeCumPoisson
      rw [Finset.sum_range_succ]
    have h3 : allTimeCumPoisson (Js + 1) ω ≤ allTimeCumPoisson Jt ω :=
      allTimeCumPoisson_mono ω (Nat.succ_le_of_lt hlt)
    omega
  · rw [← heq]
    have := continuousKMTPoisson_mono Js (ω Js)
      (sub_le_sub_right hst (allTimeBlockStart Js))
    omega

theorem allTimeKMTPoisson_integerValued (t : ℝ) (ω : AllTimeKMTSpace) :
    ∃ m : ℕ, (allTimeKMTPoisson t ω : ℝ) = m :=
  ⟨allTimeKMTPoisson t ω, rfl⟩

/-! ## Continuity of the Brownian path -/

/-- The block path as a function of global time. -/
def allTimeBlockBrownianFun (J : ℕ) (ω : AllTimeKMTSpace) (s : ℝ) : ℝ :=
  allTimeCumBrownian J ω +
    continuousKMTBrownian J (s - allTimeBlockStart J) (ω J)

theorem continuous_allTimeBlockBrownianFun (J : ℕ) (ω : AllTimeKMTSpace) :
    Continuous (allTimeBlockBrownianFun J ω) := by
  unfold allTimeBlockBrownianFun
  have hc := (BrownianFineDyadicCompletion.continuous_brownianPath J
    (continuousKMTToBrownian J (ω J))).comp
    (continuous_id.sub (continuous_const (y := allTimeBlockStart J)))
  exact continuous_const.add hc

theorem allTimeKMTBrownian_continuous (ω : AllTimeKMTSpace) :
    Continuous (fun t => allTimeKMTBrownian t ω) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hneg : ∀ t' : ℝ, t' ∈ Iic (0 : ℝ) →
      ContinuousWithinAt (fun t => allTimeKMTBrownian t ω) (Iic 0) t' := by
    intro t' ht'
    have heq : EqOn (fun t => allTimeKMTBrownian t ω) (fun _ => (0 : ℝ))
        (Iic 0) := by
      intro s hs
      rcases lt_or_eq_of_le (mem_Iic.mp hs) with h | h
      · exact allTimeKMTBrownian_of_neg h ω
      · rw [h]; exact allTimeKMTBrownian_zero_time ω
    exact continuousWithinAt_const.congr heq (heq ht')
  have hpiece : ∀ (J : ℕ) (t' : ℝ),
      t' ∈ Icc (allTimeBlockStart J) (allTimeBlockStart (J + 1)) →
      ContinuousWithinAt (fun t => allTimeKMTBrownian t ω)
        (Icc (allTimeBlockStart J) (allTimeBlockStart (J + 1))) t' := by
    intro J t' ht'
    exact (continuous_allTimeBlockBrownianFun J ω).continuousWithinAt.congr
      (fun s hs => allTimeKMTBrownian_closed_block ω hs.1 hs.2)
      (allTimeKMTBrownian_closed_block ω ht'.1 ht'.2)
  by_cases ht : t < 0
  · exact (hneg t (le_of_lt ht)).continuousAt (Iic_mem_nhds ht)
  have ht0 : 0 ≤ t := le_of_not_gt ht
  obtain ⟨J, hJ⟩ : ∃ J, J = allTimeBlock t := ⟨_, rfl⟩
  have hb := allTimeBlock_bounds ht0
  rw [← hJ] at hb
  rcases lt_or_eq_of_le hb.1 with hlt | heq
  · exact (hpiece J t ⟨hb.1, hb.2.le⟩).continuousAt
      (Icc_mem_nhds hlt hb.2)
  · -- t is the left end point of block J
    cases J with
    | zero =>
        have ht00 : t = 0 := by
          rw [← heq]; simp [allTimeBlockStart, allTimeBlockLength]
        have h1 := hneg t (by rw [ht00]; exact mem_Iic.mpr le_rfl)
        have h2 := hpiece 0 t ⟨hb.1, hb.2.le⟩
        have hu := h1.union h2
        refine hu.continuousAt ?_
        have hpos : (0 : ℝ) < allTimeBlockStart (0 + 1) :=
          lt_of_le_of_lt (allTimeBlockStart_nonneg 0) (allTimeBlockStart_lt_succ 0)
        have hsub : Iio (allTimeBlockStart (0 + 1)) ⊆
            Iic (0 : ℝ) ∪ Icc (allTimeBlockStart 0) (allTimeBlockStart (0 + 1)) := by
          intro s hs
          by_cases hs0 : s ≤ 0
          · exact Or.inl hs0
          · refine Or.inr ⟨?_, (mem_Iio.mp hs).le⟩
            have : allTimeBlockStart 0 = 0 := by
              simp [allTimeBlockStart, allTimeBlockLength]
            rw [this]
            exact (not_le.mp hs0).le
        refine Filter.mem_of_superset ?_ hsub
        apply Iio_mem_nhds
        rw [ht00]
        exact hpos
    | succ J' =>
        have hprev := hpiece J' t
          ⟨(by rw [← heq]; exact (allTimeBlockStart_lt_succ J').le),
            heq.symm.le⟩
        have hcur := hpiece (J' + 1) t ⟨hb.1, hb.2.le⟩
        have hu := hprev.union hcur
        refine hu.continuousAt ?_
        have hlo : allTimeBlockStart J' < t := by
          rw [← heq]; exact allTimeBlockStart_lt_succ J'
        have hhi : t < allTimeBlockStart (J' + 1 + 1) := hb.2
        have hsub : Ioo (allTimeBlockStart J') (allTimeBlockStart (J' + 1 + 1)) ⊆
            Icc (allTimeBlockStart J') (allTimeBlockStart (J' + 1)) ∪
              Icc (allTimeBlockStart (J' + 1)) (allTimeBlockStart (J' + 1 + 1)) := by
          intro s hs
          by_cases hs1 : s ≤ allTimeBlockStart (J' + 1)
          · exact Or.inl ⟨hs.1.le, hs1⟩
          · exact Or.inr ⟨(not_le.mp hs1).le, hs.2.le⟩
        exact Filter.mem_of_superset (Ioo_mem_nhds hlo hhi) hsub


/-! ## Right continuity of the Poisson path -/

theorem allTimeKMTPoisson_rightContinuous (ω : AllTimeKMTSpace) (t : ℝ) :
    ContinuousWithinAt (fun s => (allTimeKMTPoisson s ω : ℝ)) (Ici t) t := by
  by_cases ht : t < 0
  · -- the path vanishes near a negative time
    have hev : (fun s : ℝ => (allTimeKMTPoisson s ω : ℝ)) =ᶠ[nhdsWithin t (Ici t)]
        fun _ => (0 : ℝ) := by
      have hlt : ∀ᶠ s in nhdsWithin t (Ici t), s < 0 :=
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds ht)
      filter_upwards [hlt] with s hs
      rw [allTimeKMTPoisson_of_neg hs]
      simp
    refine continuousWithinAt_const.congr_of_eventuallyEq hev ?_
    rw [allTimeKMTPoisson_of_neg ht]
    simp
  · have ht0 : 0 ≤ t := le_of_not_gt ht
    have hErr := allTimeKMTError_rightContinuous ω ht0
    have hW := (allTimeKMTBrownian_continuous ω).continuousWithinAt
      (s := Ici t) (x := t)
    have hsum := (hErr.add continuousWithinAt_id).add hW
    refine hsum.congr (fun s _ => ?_) ?_
    · simp only [Pi.add_apply, id]
      ring
    · simp only [Pi.add_apply, id]
      ring

/-! ## Almost-sure unit jumps -/

/-- Left count and multiplicity of the block path (K19 vocabulary). -/
def blockLeftCount (K : ℕ) (t : ℝ) (z : ContinuousKMTSpace K) : ℕ :=
  DyadicConditionalPoissonPath.dyadicArrivalLeftCount K
    (continuousKMTToContinuous K z) t

def blockMultiplicity (K : ℕ) (t : ℝ) (z : ContinuousKMTSpace K) : ℕ :=
  DyadicConditionalPoissonPath.dyadicArrivalMultiplicity K
    (continuousKMTToContinuous K z) t

theorem blockUnitJumps_ae (K : ℕ) :
    ∀ᵐ z ∂continuousKMTMeasure K,
      ∀ t : ℝ, 0 ≤ t → t ≤ allTimeBlockLength K →
        continuousKMTPoisson K t z =
            blockLeftCount K t z + blockMultiplicity K t z ∧
          blockMultiplicity K t z ≤ 1 := by
  let P : DyadicConditionalPoissonPath.DyadicContinuousSpace K → Prop := fun x =>
    ∀ t : ℝ, 0 ≤ t → t ≤ ((2 ^ K : ℕ) : ℝ) →
      DyadicConditionalPoissonPath.committedContinuousPoisson K t x =
          DyadicConditionalPoissonPath.dyadicArrivalLeftCount K x t +
            DyadicConditionalPoissonPath.dyadicArrivalMultiplicity K x t ∧
        DyadicConditionalPoissonPath.dyadicArrivalMultiplicity K x t ≤ 1 ∧
        (0 < DyadicConditionalPoissonPath.committedContinuousPoisson K t x -
              DyadicConditionalPoissonPath.dyadicArrivalLeftCount K x t →
          DyadicConditionalPoissonPath.committedContinuousPoisson K t x -
              DyadicConditionalPoissonPath.dyadicArrivalLeftCount K x t = 1)
  have hpull : ∀ᵐ z ∂continuousKMTMeasure K, P (continuousKMTToContinuous K z) := by
    refine MeasureTheory.ae_of_ae_map (p := P)
      (continuousKMTMeasure_toContinuous K).measurable.aemeasurable ?_
    rw [(continuousKMTMeasure_toContinuous K).map_eq]
    exact DyadicConditionalPoissonPath.committedContinuousPoisson_unitJumps_ae K
  filter_upwards [hpull] with z hz
  intro t ht0 htK
  have h := hz t ht0 (by simpa [allTimeBlockLength] using htK)
  exact ⟨h.1, h.2.1⟩

theorem allTimeEval_measurePreserving' (K : ℕ) :
    MeasurePreserving (fun ω : AllTimeKMTSpace => ω K)
      allTimeKMTMeasure (continuousKMTMeasure K) := by
  simpa [allTimeKMTMeasure] using
    (measurePreserving_eval_infinitePi
      (fun j => continuousKMTMeasure j) K)

/-- The block `J` with `start J ≤ t ≤ start (J+1)`, taking the earlier block
at a block start (so the left limit is read inside the block). -/
def allTimeLeftBlock (t : ℝ) : ℕ :=
  if t = allTimeBlockStart (allTimeBlock t) ∧ 0 < allTimeBlock t then
    allTimeBlock t - 1
  else allTimeBlock t

theorem allTimeLeftBlock_bounds {t : ℝ} (ht : 0 ≤ t) :
    allTimeBlockStart (allTimeLeftBlock t) ≤ t ∧
      t ≤ allTimeBlockStart (allTimeLeftBlock t + 1) := by
  have hb := allTimeBlock_bounds ht
  unfold allTimeLeftBlock
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hB1 : allTimeBlock t - 1 + 1 = allTimeBlock t := by omega
    refine ⟨?_, ?_⟩
    · have := allTimeBlockStart_lt_succ (allTimeBlock t - 1)
      rw [hB1] at this
      linarith
    · rw [hB1]
      exact h1.le
  · exact ⟨hb.1, hb.2.le⟩

noncomputable def allTimeKMTPoissonLeft (t : ℝ) (ω : AllTimeKMTSpace) : ℕ :=
  allTimeCumPoisson (allTimeLeftBlock t) ω +
    blockLeftCount (allTimeLeftBlock t)
      (t - allTimeBlockStart (allTimeLeftBlock t)) (ω (allTimeLeftBlock t))

noncomputable def allTimeKMTPoissonMultiplicity (t : ℝ)
    (ω : AllTimeKMTSpace) : ℕ :=
  blockMultiplicity (allTimeLeftBlock t)
    (t - allTimeBlockStart (allTimeLeftBlock t)) (ω (allTimeLeftBlock t))

theorem allTimeKMTPoisson_unitJumps_ae :
    ∀ᵐ ω ∂allTimeKMTMeasure,
      ∀ t : ℝ, 0 ≤ t →
        allTimeKMTPoisson t ω =
            allTimeKMTPoissonLeft t ω + allTimeKMTPoissonMultiplicity t ω ∧
          allTimeKMTPoissonMultiplicity t ω ≤ 1 ∧
          (0 < allTimeKMTPoisson t ω - allTimeKMTPoissonLeft t ω →
            allTimeKMTPoisson t ω - allTimeKMTPoissonLeft t ω = 1) := by
  have hall : ∀ᵐ ω ∂allTimeKMTMeasure, ∀ J : ℕ,
      ∀ t : ℝ, 0 ≤ t → t ≤ allTimeBlockLength J →
        continuousKMTPoisson J t (ω J) =
            blockLeftCount J t (ω J) + blockMultiplicity J t (ω J) ∧
          blockMultiplicity J t (ω J) ≤ 1 := by
    rw [ae_all_iff]
    intro J
    exact MeasureTheory.ae_of_ae_map
      (allTimeEval_measurePreserving' J).measurable.aemeasurable
      (by rw [(allTimeEval_measurePreserving' J).map_eq]; exact blockUnitJumps_ae J)
  filter_upwards [hall] with ω hω
  intro t ht0
  obtain ⟨hlo, hhi⟩ := allTimeLeftBlock_bounds ht0
  set J := allTimeLeftBlock t with hJ
  have hu0 : 0 ≤ t - allTimeBlockStart J := sub_nonneg.mpr hlo
  have hu1 : t - allTimeBlockStart J ≤ allTimeBlockLength J := by
    have := hhi
    rw [allTimeBlockStart_succ] at this
    linarith
  obtain ⟨hdec, hmult⟩ := hω J (t - allTimeBlockStart J) hu0 hu1
  have hY := allTimeKMTPoisson_closed_block ω hlo hhi
  have hdec' : allTimeKMTPoisson t ω =
      allTimeKMTPoissonLeft t ω + allTimeKMTPoissonMultiplicity t ω := by
    change allTimeKMTPoisson t ω =
      (allTimeCumPoisson J ω + blockLeftCount J (t - allTimeBlockStart J) (ω J)) +
        blockMultiplicity J (t - allTimeBlockStart J) (ω J)
    rw [hY, hdec]
    omega
  refine ⟨hdec', hmult, ?_⟩
  intro hpos
  have : allTimeKMTPoissonMultiplicity t ω ≤ 1 := hmult
  omega


theorem allTimeKMTBrownian_continuous_ae :
    ∀ᵐ ω ∂allTimeKMTMeasure, Continuous (fun t => allTimeKMTBrownian t ω) :=
  Filter.Eventually.of_forall allTimeKMTBrownian_continuous

end Ripple.Kurtz.StrongApprox.AllTimeKMTLaws

end
