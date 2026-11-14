/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import Ripple.Stochastic.ContinuousItoElementary
import Ripple.Stochastic.BoundedStochasticExponential
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded predictable approximation on the prescribed filtration

Finite interval endpoints are sorted into one partition;
cell coefficients are clipped before reconstructing the elementary process.
The approximation theorem uses the installed simple-process density result.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Ripple.Stochastic.BoundedPredictableApproximation
open FilteredItoIntegralL2 FilteredItoIntegralCLM FilteredItoIntegralProcess
open FilteredItoIntegralProcessGeneral ContinuousItoElementary AdaptedContinuousSpace
open BoundedStochasticExponential

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
  [IsFilteredPreBrownian B F μ]

def clampM (K x : ℝ) : ℝ := max (-K) (min K x)

lemma clampM_abs_le {K : ℝ} (hK : 0 ≤ K) (x : ℝ) : |clampM K x| ≤ K := by
  rw [clampM, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma measurable_clampM (K : ℝ) : Measurable (clampM K) := by
  unfold clampM
  fun_prop

lemma measurable_clampM_comp {a : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {K : ℝ}
    {f : Ω → ℝ} (hf : Measurable[F a] f) :
    Measurable[F a] (fun ω => clampM K (f ω)) :=
  (measurable_clampM K).comp hf

/-- A single bounded adapted cell in the installed simple-process type. -/
def stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[F a] φ) {K : ℝ} (hφK : ∀ ω, |φ ω| ≤ K) :
    TBoundedSP (𝓖 := F) T hBmeas :=
  ⟨{ valueBot := 0
     value := Finsupp.single (a, b) φ
     le_of_mem_support_value := fun p hp => by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       exact hab
     measurable_valueBot := measurable_const
     measurable_value' := fun p hp => by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same]
       exact hφ
     bounded_valueBot := ⟨0, by simp⟩
     bounded_value := ⟨K, fun p hp ω => by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same, Real.norm_eq_abs]
       exact hφK ω⟩ },
   fun p hp => by
     obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
     exact hbT⟩

noncomputable def marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) : Finset ℝ≥0 :=
  insert 0 (insert T (V.value.support.image Prod.fst ∪ V.value.support.image Prod.snd))

lemma zero_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) :
    (0 : ℝ≥0) ∈ marshalEndpoints hBmeas T V := Finset.mem_insert_self _ _

lemma T_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) :
    T ∈ marshalEndpoints hBmeas T V :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

lemma marshalEndpoints_nonempty (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) :
    (marshalEndpoints hBmeas T V).Nonempty :=
  ⟨0, zero_mem_marshalEndpoints hBmeas T V⟩

lemma marshalEndpoints_le_T (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F)
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    ∀ x ∈ marshalEndpoints hBmeas T V, x ≤ T := by
  intro x hx
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with rfl | rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact zero_le
  · exact le_refl _
  · exact (V.le_of_mem_support_value p hp).trans (hle p hp)
  · exact hle p hp

noncomputable def marshalPart (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (i : ℕ) : ℝ≥0 :=
  if h : i < (marshalEndpoints hBmeas T V).card then
    (marshalEndpoints hBmeas T V).orderEmbOfFin rfl ⟨i, h⟩
  else T

lemma marshalPart_mono (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F)
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    Monotone (marshalPart hBmeas T V) := by
  have hE := marshalEndpoints_le_T hBmeas T V hle
  intro i j hij
  unfold marshalPart
  split_ifs with hi hj hj
  · exact ((marshalEndpoints hBmeas T V).orderEmbOfFin rfl).monotone (Fin.mk_le_mk.mpr hij)
  · exact hE _ (Finset.orderEmbOfFin_mem _ _ _)
  · omega
  · exact le_refl _

noncomputable def marshalMult (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (i : ℕ) (ω : Ω) : ℝ :=
  ∑ p ∈ V.value.support,
    (if p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2
      then V.value p ω else 0)

lemma stronglyMeasurable_marshalMult (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (i : ℕ) :
    StronglyMeasurable[(F (marshalPart hBmeas T V i) : MeasurableSpace Ω)]
      (marshalMult hBmeas T V i) := by
  unfold marshalMult
  refine Finset.stronglyMeasurable_fun_sum _ (fun p _ ↦ ?_)
  by_cases hcond : p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2
  · simp only [hcond]
    exact ((V.measurable_value p).mono (F.mono hcond.1)
      le_rfl).stronglyMeasurable
  · simp only [hcond]
    exact stronglyMeasurable_const

lemma marshalPart_lt (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) {i : ℕ}
    (hi : i + 1 < (marshalEndpoints hBmeas T V).card) :
    marshalPart hBmeas T V i < marshalPart hBmeas T V (i + 1) := by
  have hi' : i < (marshalEndpoints hBmeas T V).card := by omega
  rw [marshalPart, dif_pos hi', marshalPart, dif_pos hi]
  exact ((marshalEndpoints hBmeas T V).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (by omega))

lemma marshalEndpoints_consecutive (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F)
    (hle : ∀ p ∈ V.value.support, p.2 ≤ T) {i : ℕ}
    {x : ℝ≥0} (hx : x ∈ marshalEndpoints hBmeas T V) :
    x ≤ marshalPart hBmeas T V i ∨ marshalPart hBmeas T V (i + 1) ≤ x := by
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (marshalEndpoints hBmeas T V) rfl] at hx
  obtain ⟨k, hk⟩ := hx
  have hxk : marshalPart hBmeas T V k.val = x := by
    rw [marshalPart, dif_pos k.isLt]; exact hk
  rcases le_or_gt k.val i with h | h
  · exact Or.inl (hxk ▸ marshalPart_mono hBmeas T V hle h)
  · exact Or.inr (hxk ▸ marshalPart_mono hBmeas T V hle h)

lemma fst_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) {p : ℝ≥0 × ℝ≥0}
    (hp : p ∈ V.value.support) : p.1 ∈ marshalEndpoints hBmeas T V := by
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))

lemma snd_mem_marshalEndpoints (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) {p : ℝ≥0 × ℝ≥0}
    (hp : p ∈ V.value.support) : p.2 ∈ marshalEndpoints hBmeas T V := by
  simp only [marshalEndpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr (Or.inr ⟨p, hp, rfl⟩))

lemma mem_Ioc_iff_cover (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {i : ℕ} {t : ℝ≥0} (ht1 : marshalPart hBmeas T V i < t)
    (ht2 : t ≤ marshalPart hBmeas T V (i + 1)) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ V.value.support) :
    t ∈ Set.Ioc p.1 p.2 ↔
      (p.1 ≤ marshalPart hBmeas T V i ∧ marshalPart hBmeas T V (i + 1) ≤ p.2) := by
  constructor
  · rintro ⟨htp1, htp2⟩
    refine ⟨?_, ?_⟩
    · rcases marshalEndpoints_consecutive hBmeas T V hle (i := i)
        (fst_mem_marshalEndpoints hBmeas T V hp) with h | h
      · exact h
      · exact absurd ((h.trans_lt htp1).trans_le ht2) (lt_irrefl _)
    · rcases marshalEndpoints_consecutive hBmeas T V hle (i := i)
        (snd_mem_marshalEndpoints hBmeas T V hp) with h | h
      · exact absurd (h.trans_lt (ht1.trans_le htp2)) (lt_irrefl _)
      · exact h
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans_lt ht1, ht2.trans h2⟩

lemma marshalPart_le_iff (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) {a i : ℕ}
    (ha : a < (marshalEndpoints hBmeas T V).card) (hi : i < (marshalEndpoints hBmeas T V).card) :
    marshalPart hBmeas T V a ≤ marshalPart hBmeas T V i ↔ a ≤ i := by
  rw [marshalPart, dif_pos ha, marshalPart, dif_pos hi,
    ((marshalEndpoints hBmeas T V).orderEmbOfFin rfl).le_iff_le]
  exact Fin.mk_le_mk

lemma exists_marshalPart_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) {x : ℝ≥0}
    (hx : x ∈ marshalEndpoints hBmeas T V) :
    ∃ k, k < (marshalEndpoints hBmeas T V).card ∧ marshalPart hBmeas T V k = x := by
  rw [← Finset.mem_coe, ← Finset.range_orderEmbOfFin (marshalEndpoints hBmeas T V) rfl] at hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k.val, k.isLt, by rw [marshalPart, dif_pos k.isLt]; exact hk⟩

lemma marshalPart_zero (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    marshalPart hBmeas T V 0 = 0 := by
  refine le_antisymm ?_ (zero_le)
  obtain ⟨k, _, hk⟩ := exists_marshalPart_eq hBmeas T V (zero_mem_marshalEndpoints hBmeas T V)
  calc marshalPart hBmeas T V 0
      ≤ marshalPart hBmeas T V k := marshalPart_mono hBmeas T V hle (Nat.zero_le k)
    _ = 0 := hk

lemma marshalPart_le_T (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    (i : ℕ) : marshalPart hBmeas T V i ≤ T := by
  by_cases h : i < (marshalEndpoints hBmeas T V).card
  · rw [marshalPart, dif_pos h]
    exact marshalEndpoints_le_T hBmeas T V hle _ (Finset.orderEmbOfFin_mem _ _ _)
  · exact le_of_eq (by rw [marshalPart, dif_neg h])

lemma marshalPart_card_sub_one (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T) :
    marshalPart hBmeas T V ((marshalEndpoints hBmeas T V).card - 1) = T := by
  have hpos : 0 < (marshalEndpoints hBmeas T V).card :=
    Finset.card_pos.mpr (marshalEndpoints_nonempty hBmeas T V)
  refine le_antisymm ?_ ?_
  · have hlt : (marshalEndpoints hBmeas T V).card - 1 <
      (marshalEndpoints hBmeas T V).card := by omega
    rw [marshalPart, dif_pos hlt]
    exact marshalEndpoints_le_T hBmeas T V hle _ (Finset.orderEmbOfFin_mem _ _ _)
  · obtain ⟨k, hk_card, hk⟩ := exists_marshalPart_eq hBmeas T V (T_mem_marshalEndpoints hBmeas T V)
    calc T = marshalPart hBmeas T V k := hk.symm
      _ ≤ marshalPart hBmeas T V ((marshalEndpoints hBmeas T V).card - 1) :=
          marshalPart_mono hBmeas T V hle (by omega)

lemma marshalMult_eq_uncurry (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {i : ℕ} {t : ℝ≥0} (ht1 : marshalPart hBmeas T V i < t)
    (ht2 : t ≤ marshalPart hBmeas T V (i + 1)) (ω : Ω) :
    ⇑V t ω = marshalMult hBmeas T V i ω := by
  have ht0 : t ∉ ({⊥} : Set ℝ≥0) := by
    simp only [Set.mem_singleton_iff]
    exact (lt_of_le_of_lt (zero_le) ht1).ne'
  rw [SimpleProcess.apply_eq, Set.indicator_of_notMem ht0, zero_add, Finsupp.sum, marshalMult]
  refine Finset.sum_congr rfl (fun p hp ↦ ?_)
  rw [Set.indicator_apply]
  by_cases hmem : t ∈ Set.Ioc p.1 p.2
  · rw [if_pos hmem, if_pos ((mem_Ioc_iff_cover hBmeas T V hle ht1 ht2 hp).mp hmem)]
  · rw [if_neg hmem,
      if_neg (fun hc ↦ hmem ((mem_Ioc_iff_cover hBmeas T V hle ht1 ht2 hp).mpr hc))]

/-- Rebuild the clipped process on the disjoint sorted cells. -/
def marshalStepSP (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) : TBoundedSP (𝓖 := F) T hBmeas :=
  ∑ i ∈ Finset.range N,
    stepSP hBmeas (a := marshalPart hBmeas T V i) (b := marshalPart hBmeas T V (i + 1))
      (marshalPart_mono hBmeas T V hle (Nat.le_succ i))
      (marshalPart_le_T hBmeas T V hle (i + 1))
      ((measurable_clampM_comp hBmeas (stronglyMeasurable_marshalMult hBmeas T V i).measurable))
      (fun _ => clampM_abs_le hC _)

lemma uncurry_marshalStepSP (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) (N : ℕ) (s : ℝ≥0) (ω : Ω) :
    Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val (s, ω) =
      ∑ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ => clampM C (marshalMult hBmeas T V i ω)) s := by
  classical
  induction N with
  | zero => simp [marshalStepSP]
  | succ N ih =>
    simp only [marshalStepSP, Finset.sum_range_succ, Submodule.coe_add,
      SimpleProcess.coe_add, Function.uncurry_apply_pair, Pi.add_apply] at ih ⊢
    rw [ih]
    congr 1
    rw [SimpleProcess.apply_eq]
    simp [stepSP, Finsupp.sum_single_index]

lemma sum_cell_indicator_eq_one (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {N : ℕ} (hmpN : marshalPart hBmeas T V N = T) {s : ℝ≥0} (hs0 : 0 < s) (hsT : s ≤ T) :
    ∑ i ∈ Finset.range N,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ ↦ (1 : ℝ)) s = 1 := by
  have hsub : ∀ i,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ ↦ (1 : ℝ)) s
      = (Set.Iic (marshalPart hBmeas T V (i + 1))).indicator (fun _ ↦ (1 : ℝ)) s
        - (Set.Iic (marshalPart hBmeas T V i)).indicator (fun _ ↦ (1 : ℝ)) s := fun i ↦ by
    have hab := marshalPart_mono hBmeas T V hle (Nat.le_succ i)
    simp only [Set.indicator_apply, Set.mem_Ioc, Set.mem_Iic]
    by_cases h1 : s ≤ marshalPart hBmeas T V i
    · rw [if_neg (fun h ↦ absurd h.1 (not_lt.mpr h1)), if_pos (h1.trans hab),
        if_pos h1]
      ring
    · rw [not_le] at h1
      by_cases h2 : s ≤ marshalPart hBmeas T V (i + 1)
      · rw [if_pos ⟨h1, h2⟩, if_pos h2, if_neg (not_le.mpr h1)]; ring
      · rw [not_le] at h2
        rw [if_neg (fun h ↦ absurd h.2 (not_le.mpr h2)), if_neg (not_le.mpr h2),
          if_neg (not_le.mpr (hab.trans_lt h2))]; ring
  simp_rw [hsub]
  rw [Finset.sum_range_sub
      (fun i ↦ (Set.Iic (marshalPart hBmeas T V i)).indicator (fun _ ↦ (1 : ℝ)) s),
    hmpN, marshalPart_zero hBmeas T V hle,
    Set.indicator_of_mem (Set.mem_Iic.mpr hsT),
    Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; exact hs0)]
  norm_num

lemma uncurry_marshalStepSP_eq_clamp (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hmpN : marshalPart hBmeas T V N = T)
    {s : ℝ≥0} (hs0 : 0 < s) (hsT : s ≤ T) (ω : Ω) :
    Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val (s, ω) = clampM C (⇑V s ω) := by
  rw [uncurry_marshalStepSP]
  have hstep : ∀ i ∈ Finset.range N,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ ↦ clampM C (marshalMult hBmeas T V i ω)) s
      = (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ ↦ clampM C (⇑V s ω)) s := by
    intro i _
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
    · rw [if_pos hmem, if_pos hmem]
      congr 1
      exact (marshalMult_eq_uncurry hBmeas T V hle hmem.1 hmem.2 ω).symm
    · rw [if_neg hmem, if_neg hmem]
  have hconst : ∀ i,
      (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ ↦ clampM C (⇑V s ω)) s
      = clampM C (⇑V s ω) *
          (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ ↦ (1 : ℝ)) s := by
    intro i
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
    · rw [if_pos hmem, if_pos hmem, mul_one]
    · rw [if_neg hmem, if_neg hmem, mul_zero]
  rw [Finset.sum_congr rfl hstep]
  simp_rw [hconst]
  rw [← Finset.mul_sum, sum_cell_indicator_eq_one hBmeas T V hle hmpN hs0 hsT, mul_one]

lemma clampM_dist_le {M g x : ℝ} (hg : |g| ≤ M) : |clampM M x - g| ≤ |x - g| := by
  rw [abs_le] at hg
  obtain ⟨hg1, hg2⟩ := hg
  unfold clampM
  rcases le_total x (-M) with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx,
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total x M with hx2 | hx2
    · rw [min_eq_right hx2, max_eq_right hx]
    · rw [min_eq_left hx2, max_eq_right (by linarith),
        abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- The finite-horizon predictable measure is supported on `(0,T] × Ω`. -/
lemma ae_window (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), z.1 ∈ Set.Ioc 0 T := by
  rw [trimMeasure_T_eq_restrict]
  have hset : MeasurableSet[F.predictable] (Set.Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod (𝓕 := F) 0 T MeasurableSet.univ
  filter_upwards [ae_restrict_mem hset] with z hz
  exact hz.1

/-- Clipping whole disjoint cells gives a contraction toward a bounded L² class. -/
lemma norm_clipped_sub_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : TBoundedSP (𝓖 := F) T hBmeas) {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K) :
    ‖simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas
        (marshalStepSP hBmeas T V.val V.property hK ((marshalEndpoints hBmeas T V.val).card - 1)) - φ‖ ≤
      ‖simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V - φ‖ := by
  let W := marshalStepSP hBmeas T V.val V.property hK ((marshalEndpoints hBmeas T V.val).card - 1)
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas W) φ,
    Lp.coeFn_sub (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V) φ,
    (memLp_uncurry_trim_T (𝓖 := F) (μ := μ) T hBmeas W.val).coeFn_toLp,
    (memLp_uncurry_trim_T (𝓖 := F) (μ := μ) T hBmeas V.val).coeFn_toLp,
    ae_window T hBmeas, hφ] with z hsubW hsubV hW hV hz hφz
  have hW' : (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas W : ℝ≥0 × Ω → ℝ) z =
      Function.uncurry ⇑W.val z := hW
  have hV' : (simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V : ℝ≥0 × Ω → ℝ) z =
      Function.uncurry ⇑V.val z := hV
  rw [hsubW, hsubV, Pi.sub_apply, Pi.sub_apply, hW', hV']
  change |⇑W.val z.1 z.2 - φ z| ≤ |⇑V.val z.1 z.2 - φ z|
  have hc := uncurry_marshalStepSP_eq_clamp hBmeas T V.val V.property hK
    (marshalPart_card_sub_one hBmeas T V.val V.property) hz.1 hz.2 z.2
  rw [show ⇑W.val z.1 z.2 = clampM K (⇑V.val z.1 z.2) from hc]
  exact clampM_dist_le hφz

/-- Raw fast approximants are selected from the installed density theorem. -/
def rawApprox (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n : ℕ) :
    TBoundedSP (𝓖 := F) T hBmeas :=
  Classical.choose ((simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) T hBmeas).exists_dist_lt
    φ (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n))

lemma rawApprox_error (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n : ℕ) :
    ‖simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas (rawApprox T hBmeas φ n) - φ‖ ≤
      (1 / 2 : ℝ) ^ n := by
  have h := Classical.choose_spec
    ((simpleAssembly_T_denseRange (𝓖 := F) (μ := μ) T hBmeas).exists_dist_lt
      φ (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n))
  rw [dist_comm, dist_eq_norm] at h
  exact h.le

/-- The actual bounded approximation is formed by clipping the coefficients on
one common endpoint partition. -/
def boundedApprox (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n : ℕ) :
    TBoundedSP (𝓖 := F) T hBmeas :=
  let V := rawApprox T hBmeas φ n
  marshalStepSP hBmeas T V.val V.property hK ((marshalEndpoints hBmeas T V.val).card - 1)

lemma boundedApprox_error (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K) (n : ℕ) :
    ‖simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas (boundedApprox T hBmeas hK φ n) - φ‖ ≤
      (1 / 2 : ℝ) ^ n :=
  (norm_clipped_sub_le T hBmeas (rawApprox T hBmeas φ n) hK φ hφ).trans
    (rawApprox_error T hBmeas φ n)

/-- Bounded approximants converge to the actual predictable L² class. -/
theorem boundedApprox_tendsto (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K) :
    Tendsto (fun n => simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas
      (boundedApprox T hBmeas hK φ n)) atTop (𝓝 φ) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (boundedApprox_error T hBmeas hK φ hφ)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- Read the exact partition witnesses consumed by the elementary exponential. -/
def approxPartition (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n : ℕ) : ℕ → ℝ≥0 :=
  marshalPart hBmeas T (rawApprox T hBmeas φ n).val

def approxCoefficient (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (K : ℝ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n i : ℕ) (ω : Ω) : ℝ :=
  clampM K (marshalMult hBmeas T (rawApprox T hBmeas φ n).val i ω)

def approxCells (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n : ℕ) : ℕ :=
  (marshalEndpoints hBmeas T (rawApprox T hBmeas φ n).val).card - 1

lemma approxPartition_mono (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n : ℕ) :
    Monotone (approxPartition T hBmeas φ n) :=
  marshalPart_mono hBmeas T _ (rawApprox T hBmeas φ n).property

lemma approxPartition_zero (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n : ℕ) :
    approxPartition T hBmeas φ n 0 = 0 :=
  marshalPart_zero hBmeas T _ (rawApprox T hBmeas φ n).property

lemma approxCoefficient_adapted (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) (K : ℝ)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n i : ℕ) :
    StronglyMeasurable[F (approxPartition T hBmeas φ n i)]
      (approxCoefficient T hBmeas K φ n i) :=
  ((measurable_clampM K).comp
    (stronglyMeasurable_marshalMult hBmeas T (rawApprox T hBmeas φ n).val i).measurable).stronglyMeasurable

lemma approxCoefficient_bound (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)) (n i : ℕ) (ω : Ω) :
    |approxCoefficient T hBmeas K φ n i ω| ≤ K := clampM_abs_le hK _

lemma itoSimpleProcess_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {ψ : Ω → ℝ}
    (hψ : Measurable[F a] ψ) {K : ℝ} (hψK : ∀ ω, |ψ ω| ≤ K) (t : ℝ≥0) (ω : Ω) :
    itoSimpleProcess hBmeas (stepSP hBmeas hab hbT hψ hψK).val t ω =
      ψ ω * (B (min b t) ω - B (min a t) ω) := by
  rw [itoSimpleProcess_apply]
  change (Finsupp.single (a, b) ψ).sum
    (fun p v => v ω * (B (min p.2 t) ω - B (min p.1 t) ω)) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- The exponential's finite Brownian sum is exactly the constructed elementary integral. -/
lemma simpleSum_boundedApprox (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    simpleSum B (approxPartition T hBmeas φ n) (approxCoefficient T hBmeas K φ n)
      (approxCells T hBmeas φ n) t ω =
      itoSimpleProcess hBmeas (boundedApprox T hBmeas hK φ n).val t ω := by
  let V := rawApprox T hBmeas φ n
  have hsum : ∀ N,
      itoSimpleProcess hBmeas (marshalStepSP hBmeas T V.val V.property hK N).val t ω =
        simpleSum B (marshalPart hBmeas T V.val)
          (fun i ω => clampM K (marshalMult hBmeas T V.val i ω)) N t ω := by
    intro N
    induction N with
    | zero => simp [marshalStepSP, simpleSum, itoSimpleProcess, SimpleProcess.integral]
    | succ N ih =>
      rw [marshalStepSP, Finset.sum_range_succ, Submodule.coe_add, itoSimpleProcess_add]
      simp only [Pi.add_apply]
      rw [itoSimpleProcess_stepSP]
      change _ + _ = _
      rw [show itoSimpleProcess hBmeas
          (∑ i ∈ Finset.range N, stepSP hBmeas
            (marshalPart_mono hBmeas T V.val V.property (Nat.le_succ i))
            (marshalPart_le_T hBmeas T V.val V.property (i + 1))
            (measurable_clampM_comp hBmeas (stronglyMeasurable_marshalMult hBmeas T V.val i).measurable)
            (fun _ => clampM_abs_le hK _)).val t ω = _ from ih]
      simp [simpleSum, Finset.sum_range_succ]
  exact (hsum (approxCells T hBmeas φ n)).symm

lemma simpleBracket_marshalStepSP_eq (hBmeas : ∀ t, Measurable (B t)) (T : ℝ≥0)
    (V : SimpleProcess ℝ F) (hle : ∀ p ∈ V.value.support, p.2 ≤ T)
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hmpN : marshalPart hBmeas T V N = T) (u : ℝ≥0) (hu : u ≤ T) (ω : Ω) :
    simpleBracket (marshalPart hBmeas T V)
        (fun i ω ↦ clampM C (marshalMult hBmeas T V i ω)) N u ω
      = ∫ s in Set.Ioc (0 : ℝ≥0) u,
          (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2 ∂timeMeasure := by
  have : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)) :=
    ⟨by rw [Measure.restrict_apply_univ, timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have htoReal : ∀ i : ℕ, marshalPart hBmeas T V i ≤ marshalPart hBmeas T V (i + 1) →
      (timeMeasure (Set.Ioc (0 : ℝ≥0) u ∩
          Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1)))).toReal
        = NNReal.toReal (min (marshalPart hBmeas T V (i + 1)) u)
          - NNReal.toReal (min (marshalPart hBmeas T V i) u) := by
    intro i hi12
    rw [Set.inter_comm, timeMeasure_Ioc_inter, NNReal.coe_zero,
      max_eq_left (marshalPart hBmeas T V i).coe_nonneg, NNReal.coe_min, NNReal.coe_min]
    by_cases hiT : marshalPart hBmeas T V i ≤ u
    · rw [ENNReal.toReal_ofReal (by
            have : (marshalPart hBmeas T V i : ℝ) ≤ min (marshalPart hBmeas T V (i + 1) : ℝ) u :=
              le_min (by exact_mod_cast hi12) (by exact_mod_cast hiT)
            linarith),
        min_eq_left (by exact_mod_cast hiT : (marshalPart hBmeas T V i : ℝ) ≤ u)]
    · rw [not_le] at hiT
      have h1 : (u : ℝ) ≤ marshalPart hBmeas T V i := le_of_lt (by exact_mod_cast hiT)
      have h2 : (u : ℝ) ≤ marshalPart hBmeas T V (i + 1) := h1.trans (by exact_mod_cast hi12)
      rw [min_eq_right h2, min_eq_right h1, sub_self,
        ENNReal.ofReal_eq_zero.mpr (by linarith), ENNReal.toReal_zero]
  have hsq_eq : Set.EqOn (fun s ↦ (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2)
      (fun s ↦ ∑ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
          (fun _ ↦ (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s) (Set.Ioc (0 : ℝ≥0) u) := by
    intro s hs
    dsimp only
    have hlhs : (⇑(marshalStepSP hBmeas T V hle hC N).val s ω) ^ 2 = (clampM C (⇑V s ω)) ^ 2 := by
      rw [show ⇑(marshalStepSP hBmeas T V hle hC N).val s ω
          = Function.uncurry ⇑(marshalStepSP hBmeas T V hle hC N).val (s, ω) from rfl,
        uncurry_marshalStepSP_eq_clamp hBmeas T V hle hC hmpN hs.1 (hs.2.trans hu) ω]
    rw [hlhs]
    have hstep : ∀ i ∈ Finset.range N,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ ↦ (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s
        = (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ ↦ (clampM C (⇑V s ω)) ^ 2) s := by
      intro i _
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
      · rw [if_pos hmem, if_pos hmem,
          marshalMult_eq_uncurry hBmeas T V hle hmem.1 hmem.2 ω]
      · rw [if_neg hmem, if_neg hmem]
    have hconst : ∀ i,
        (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
            (fun _ ↦ (clampM C (⇑V s ω)) ^ 2) s
        = (clampM C (⇑V s ω)) ^ 2 *
            (Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))).indicator
              (fun _ ↦ (1 : ℝ)) s := by
      intro i
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hmem : s ∈ Set.Ioc (marshalPart hBmeas T V i) (marshalPart hBmeas T V (i + 1))
      · rw [if_pos hmem, if_pos hmem, mul_one]
      · rw [if_neg hmem, if_neg hmem, mul_zero]
    rw [Finset.sum_congr rfl hstep]
    simp_rw [hconst]
    rw [← Finset.mul_sum, sum_cell_indicator_eq_one hBmeas T V hle hmpN hs.1 (hs.2.trans hu), mul_one]
  have hint : ∀ i ∈ Finset.range N,
      Integrable (fun s ↦ (Set.Ioc (marshalPart hBmeas T V i)
          (marshalPart hBmeas T V (i + 1))).indicator
        (fun _ ↦ (clampM C (marshalMult hBmeas T V i ω)) ^ 2) s)
        (timeMeasure.restrict (Set.Ioc (0 : ℝ≥0) u)) :=
    fun i _ ↦ (integrable_const _).indicator measurableSet_Ioc
  rw [setIntegral_congr_fun measurableSet_Ioc hsq_eq, integral_finsetSum _ hint, simpleBracket]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul, measureReal_def,
    htoReal i (marshalPart_mono hBmeas T V hle (Nat.le_succ i)), mul_comm]
  simp only [NNReal.coe_min]

/-- A common subsequence converges as continuous integral paths and as integrands
for almost every sample and almost every time. Both extractions are performed
on actual L² convergences; neither convergence is supplied as a premise. -/
theorem exists_common_path_integrand_subsequence (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ ω ∂μ, Tendsto
        (fun n => ContinuousItoConstruction.simpleIntegralPath T hB
          (boundedApprox T hBmeas hK φ (ns n)).val ω)
        atTop (𝓝 (representative (continuousIto T hB hBmeas φ) ω))) ∧
      (∀ᵐ ω ∂μ, ∀ᵐ s ∂(timeMeasure_T T), Tendsto
        (fun n => ⇑(boundedApprox T hBmeas hK φ (ns n)).val s ω)
        atTop (𝓝 (φ (s, ω)))) := by
  let W := boundedApprox T hBmeas hK φ
  have hW := boundedApprox_tendsto T hBmeas hK φ hφ
  have hpathLp : Tendsto (fun n => boundedSimplePathLp T hB hBmeas (W n)) atTop
      (𝓝 (continuousIto T hB hBmeas φ)) := by
    exact ContinuousItoConstruction.continuousIntegral_tendsto _
      (simpleAssembly_T_denseRange T hBmeas) _ _
      (boundedSimplePathLp_norm_le T hB hBmeas) hW
  have hpath : TendstoInMeasure μ
      (fun n ω => ContinuousItoConstruction.simpleIntegralPath T hB (W n).val ω) atTop
      (representative (continuousIto T hB hBmeas φ)) := by
    apply TendstoInMeasure.congr
      (fun n => (simpleIntegralPath_memLp T hB hBmeas (W n).val).coeFn_toLp)
      (representative_ae (continuousIto T hB hBmeas φ))
      (tendstoInMeasure_of_tendsto_Lp hpathLp)
  obtain ⟨u, hu, hPu⟩ := hpath.exists_seq_tendsto_ae
  have hint : TendstoInMeasure (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas)
      (fun n => Function.uncurry ⇑(W n).val) atTop (φ : ℝ≥0 × Ω → ℝ) := by
    exact TendstoInMeasure.congr
      (fun n => (memLp_uncurry_trim_T (𝓖 := F) (μ := μ) T hBmeas (W n).val).coeFn_toLp)
      EventuallyEq.rfl (tendstoInMeasure_of_tendsto_Lp hW)
  obtain ⟨v, hv, hIv⟩ := (hint.comp hu.tendsto_atTop).exists_seq_tendsto_ae
  have hprod : ∀ᵐ z ∂((timeMeasure_T T).prod μ), Tendsto
      (fun n => ⇑(W (u (v n))).val z.1 z.2) atTop (𝓝 (φ z)) :=
    ae_of_ae_trim F.predictable_le_prod hIv
  have hswap : ∀ᵐ z ∂(μ.prod (timeMeasure_T T)), Tendsto
      (fun n => ⇑(W (u (v n))).val z.2 z.1) atTop (𝓝 (φ (z.2, z.1))) :=
    (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure_T T)).quasiMeasurePreserving.ae hprod
  refine ⟨u ∘ v, hu.comp hv, ?_, Measure.ae_ae_of_ae_prod hswap⟩
  filter_upwards [hPu] with ω hω
  exact hω.comp hv.tendsto_atTop

lemma measurable_simple_time (V : SimpleProcess ℝ F) (ω : Ω) :
    Measurable (fun s => ⇑V s ω) := by
  simp only [SimpleProcess.apply_eq, Finsupp.sum]
  apply Measurable.add
  · exact measurable_const.indicator (measurableSet_singleton 0)
  · exact Finset.measurable_sum _ fun p _ => measurable_const.indicator measurableSet_Ioc

/-- A single full-measure event supports both stochastic-integral convergence
at every time and quadratic-variation convergence at every time in the window. -/
theorem exists_common_integral_bracket_subsequence (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂μ, ∀ t : Set.Icc (0 : ℝ≥0) T,
      Tendsto (fun n => simpleSum B (approxPartition T hBmeas φ (ns n))
        (approxCoefficient T hBmeas K φ (ns n)) (approxCells T hBmeas φ (ns n)) t.val ω)
        atTop (𝓝 (representative (continuousIto T hB hBmeas φ) ω t)) ∧
      Tendsto (fun n => simpleBracket (approxPartition T hBmeas φ (ns n))
        (approxCoefficient T hBmeas K φ (ns n)) (approxCells T hBmeas φ (ns n)) t.val ω)
        atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ≥0) t.val, (φ (s, ω)) ^ 2 ∂timeMeasure)) := by
  obtain ⟨ns, hns, hpath, hint⟩ :=
    exists_common_path_integrand_subsequence T hB hBmeas hK φ hφ
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hpath, hint] with ω hpathω hintω
  intro t
  refine ⟨?_, ?_⟩
  · have h := ((ContinuousMap.evalCLM ℝ t).continuous.tendsto
      (representative (continuousIto T hB hBmeas φ) ω)).comp hpathω
    simp only [ContinuousMap.evalCLM_apply, Function.comp_def] at h
    refine h.congr (fun n => ?_)
    rw [simpleSum_boundedApprox T hBmeas hK φ]
    exact ContinuousItoConstruction.simpleIntegralPath_apply T hB hBmeas _ ω t
  · have hrestr : timeMeasure_T t.val ≤ timeMeasure_T T :=
      Measure.restrict_mono (Set.Ioc_subset_Ioc_right t.property.2) le_rfl
    have hintt : ∀ᵐ s ∂(timeMeasure_T t.val), Tendsto
        (fun n => ⇑(boundedApprox T hBmeas hK φ (ns n)).val s ω)
        atTop (𝓝 (φ (s, ω))) := hintω.filter_mono (ae_mono hrestr)
    have hsq : Tendsto
        (fun n => ∫ s,
          (⇑(boundedApprox T hBmeas hK φ (ns n)).val s ω) ^ 2 ∂(timeMeasure_T t.val))
        atTop (𝓝 (∫ s, (φ (s, ω)) ^ 2 ∂(timeMeasure_T t.val))) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => K ^ 2)
      · intro n
        exact ((measurable_simple_time _ ω).pow_const 2).aestronglyMeasurable
      · exact integrable_const _
      · intro n
        filter_upwards [ae_restrict_mem (μ := timeMeasure) measurableSet_Ioc] with s hs
        have hb : |⇑(boundedApprox T hBmeas hK φ (ns n)).val s ω| ≤ K := by
          rw [boundedApprox]
          have hc := uncurry_marshalStepSP_eq_clamp hBmeas T
            (rawApprox T hBmeas φ (ns n)).val (rawApprox T hBmeas φ (ns n)).property hK
            (marshalPart_card_sub_one hBmeas T _ (rawApprox T hBmeas φ (ns n)).property)
            hs.1 (hs.2.trans t.property.2) ω
          rw [show ⇑(marshalStepSP hBmeas T (rawApprox T hBmeas φ (ns n)).val
            (rawApprox T hBmeas φ (ns n)).property hK
            ((marshalEndpoints hBmeas T (rawApprox T hBmeas φ (ns n)).val).card - 1)).val s ω =
              clampM K (⇑(rawApprox T hBmeas φ (ns n)).val s ω) from hc]
          exact clampM_abs_le hK _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
      · filter_upwards [hintt] with s hs
        exact hs.pow 2
    have heq : ∀ n, simpleBracket (approxPartition T hBmeas φ (ns n))
        (approxCoefficient T hBmeas K φ (ns n)) (approxCells T hBmeas φ (ns n)) t.val ω =
          ∫ s, (⇑(boundedApprox T hBmeas hK φ (ns n)).val s ω) ^ 2 ∂(timeMeasure_T t.val) := by
      intro n
      exact simpleBracket_marshalStepSP_eq hBmeas T _
        (rawApprox T hBmeas φ (ns n)).property hK
        (marshalPart_card_sub_one hBmeas T _ (rawApprox T hBmeas φ (ns n)).property)
        t.val t.property.2 ω
    simpa only [heq, timeMeasure_T] using hsq

/-- Elementary bracket increments are nonnegative and bounded by K² times
elapsed time, independently of the partition and its number of cells. -/
lemma simpleBracket_increment_bound (s : ℕ → ℝ≥0) (hs : Monotone s) (hz : s 0 = 0)
    (c : ℕ → Ω → ℝ) {K : ℝ} (hK : ∀ i ω, |c i ω| ≤ K)
    (N : ℕ) {u t : ℝ≥0} (hut : u ≤ t) (ω : Ω) :
    0 ≤ simpleBracket s c N t ω - simpleBracket s c N u ω ∧
      simpleBracket s c N t ω - simpleBracket s c N u ω ≤ K ^ 2 * ((t : ℝ) - u) := by
  let d := fun i (x : ℝ≥0) => ((min (s (i + 1)) x : ℝ≥0) : ℝ) - (min (s i) x : ℝ)
  have hdelta : ∀ i, 0 ≤ d i t - d i u := by
    intro i
    have hab : (s i : ℝ) ≤ s (i + 1) := by exact_mod_cast hs (Nat.le_succ i)
    have hutreal : (u : ℝ) ≤ t := by exact_mod_cast hut
    dsimp [d]
    simp only [NNReal.coe_min, min_def]
    split_ifs <;> linarith
  have htel : ∀ n x, ∑ i ∈ Finset.range n, d i x =
      ((min (s n) x : ℝ≥0) : ℝ) - (min (s 0) x : ℝ) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp [d]
      simp only [NNReal.coe_min]
      ring
  have hlength : (∑ i ∈ Finset.range N, (d i t - d i u)) ≤ (t : ℝ) - u := by
    rw [Finset.sum_sub_distrib, htel, htel, hz]
    simp only [zero_min, NNReal.coe_zero, sub_zero, NNReal.coe_min]
    have hutreal : (u : ℝ) ≤ t := by exact_mod_cast hut
    simp only [min_def]
    split_ifs <;> linarith
  have hexp : simpleBracket s c N t ω - simpleBracket s c N u ω =
      ∑ i ∈ Finset.range N, (c i ω) ^ 2 * (d i t - d i u) := by
    simp only [simpleBracket, d, mul_sub, Finset.sum_sub_distrib]
  rw [hexp]
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (hdelta i)), ?_⟩
  calc
    (∑ i ∈ Finset.range N, (c i ω) ^ 2 * (d i t - d i u)) ≤
        ∑ i ∈ Finset.range N, K ^ 2 * (d i t - d i u) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (hdelta i)
      nlinarith [(abs_le.mp (hK i ω)).1, (abs_le.mp (hK i ω)).2]
    _ = K ^ 2 * ∑ i ∈ Finset.range N, (d i t - d i u) := (Finset.mul_sum ..).symm
    _ ≤ K ^ 2 * ((t : ℝ) - u) := mul_le_mul_of_nonneg_left hlength (sq_nonneg K)

/-- The actual time-integral bracket inherits monotonicity and continuity from
the uniform increment bound, on a single full-measure event for the window. -/
theorem actualBracket_ae_regular (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K) :
    ∀ᵐ ω ∂μ,
      Monotone (fun t : Set.Icc (0 : ℝ≥0) T =>
        ∫ s in Set.Ioc (0 : ℝ≥0) t.val, (φ (s, ω)) ^ 2 ∂timeMeasure) ∧
      Continuous (fun t : Set.Icc (0 : ℝ≥0) T =>
        ∫ s in Set.Ioc (0 : ℝ≥0) t.val, (φ (s, ω)) ^ 2 ∂timeMeasure) := by
  obtain ⟨ns, hns, hconv⟩ := exists_common_integral_bracket_subsequence T hB hBmeas hK φ hφ
  filter_upwards [hconv] with ω hω
  let A := fun t : Set.Icc (0 : ℝ≥0) T =>
    ∫ s in Set.Ioc (0 : ℝ≥0) t.val, (φ (s, ω)) ^ 2 ∂timeMeasure
  have hinc : ∀ u t : Set.Icc (0 : ℝ≥0) T, u ≤ t →
      0 ≤ A t - A u ∧ A t - A u ≤ K ^ 2 * ((t.val : ℝ) - u.val) := by
    intro u t hut
    have hlim := (hω t).2.sub (hω u).2
    have hb := fun n => simpleBracket_increment_bound
      (approxPartition T hBmeas φ (ns n)) (approxPartition_mono T hBmeas φ (ns n))
      (approxPartition_zero T hBmeas φ (ns n)) (approxCoefficient T hBmeas K φ (ns n))
      (approxCoefficient_bound T hBmeas hK φ (ns n)) (approxCells T hBmeas φ (ns n)) hut ω
    exact ⟨ge_of_tendsto hlim (Eventually.of_forall fun n => (hb n).1),
      le_of_tendsto hlim (Eventually.of_forall fun n => (hb n).2)⟩
  have hcase : ∀ u t : Set.Icc (0 : ℝ≥0) T, u ≤ t →
      dist (A t) (A u) ≤ K ^ 2 * dist t u := by
    intro u t hut
    change dist (A t) (A u) ≤ K ^ 2 * dist (t.val : ℝ) (u.val : ℝ)
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (hinc u t hut).1,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hut))]
    exact (hinc u t hut).2
  have hlip : LipschitzWith ⟨K ^ 2, sq_nonneg K⟩ A := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rcases le_total u t with hut | htu
    · exact hcase u t hut
    · simpa only [dist_comm] using hcase t u htu
  exact ⟨fun u t hut => sub_nonneg.mp (hinc u t hut).1, hlip.continuous⟩

/-- The bounded predictable stochastic exponential on a compact window.
The bracket is selected as a measurable limsup of elementary brackets and is
identified with the actual time integral on one event for every time. -/
theorem exists_bounded_predictable_stochastic_exponential (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K)
    (lam : ℝ) :
    ∃ Q : Set.Icc (0 : ℝ≥0) T → Ω → ℝ,
      StronglyAdapted
        (Doob.Filtration.compMono mΩ F (fun t : Set.Icc (0 : ℝ≥0) T => t.val)
          (fun _ _ h => h)) Q ∧
      (∀ ω, Q ⟨0, zero_le, zero_le⟩ ω = 0) ∧
      (∀ᵐ ω ∂μ, Monotone (fun t => Q t ω) ∧ Continuous (fun t => Q t ω)) ∧
      (∀ᵐ ω ∂μ, ∀ t, Q t ω =
        ∫ s in Set.Ioc (0 : ℝ≥0) t.val, (φ (s, ω)) ^ 2 ∂timeMeasure) ∧
      Martingale (fun t ω => Real.exp (lam *
        representative (continuousIto T hB hBmeas φ) ω t - lam ^ 2 * Q t ω / 2))
        (Doob.Filtration.compMono mΩ F (fun t : Set.Icc (0 : ℝ≥0) T => t.val)
          (fun _ _ h => h)) μ := by
  obtain ⟨ns, hns, hconv⟩ := exists_common_integral_bracket_subsequence T hB hBmeas hK φ hφ
  let s := fun n => approxPartition T hBmeas φ (ns n)
  let c := fun n => approxCoefficient T hBmeas K φ (ns n)
  let N := fun n => approxCells T hBmeas φ (ns n)
  have hs : ∀ n, Monotone (s n) := fun n => approxPartition_mono T hBmeas φ (ns n)
  have hz : ∀ n, s n 0 = 0 := fun n => approxPartition_zero T hBmeas φ (ns n)
  have hc : ∀ n i, StronglyMeasurable[F (s n i)] (c n i) :=
    fun n i => approxCoefficient_adapted T hBmeas K φ (ns n) i
  have hb : ∀ n i ω, |c n i ω| ≤ K :=
    fun n i ω => approxCoefficient_bound T hBmeas hK φ (ns n) i ω
  let G := Doob.Filtration.compMono mΩ F (fun t : Set.Icc (0 : ℝ≥0) T => t.val)
    (fun _ _ h => h)
  let Q : Set.Icc (0 : ℝ≥0) T → Ω → ℝ :=
    fun t ω => Filter.limsup (fun n => simpleBracket (s n) (c n) (N n) t.val ω) atTop
  have hQa : StronglyAdapted G Q := by
    intro t
    apply Measurable.stronglyMeasurable
    exact Measurable.limsup fun n =>
      (simpleBracket_stronglyAdapted F (s n) (hs n) (c n) (hc n) (N n) t.val).measurable
  have hQid : ∀ᵐ ω ∂μ, ∀ t, Q t ω =
      ∫ r in Set.Ioc (0 : ℝ≥0) t.val, (φ (r, ω)) ^ 2 ∂timeMeasure := by
    filter_upwards [hconv] with ω hω t
    exact (hω t).2.limsup_eq
  have hQzero : ∀ ω, Q ⟨0, zero_le, zero_le⟩ ω = 0 := by
    intro ω
    simp [Q, simpleBracket]
  have hQreg : ∀ᵐ ω ∂μ, Monotone (fun t => Q t ω) ∧ Continuous (fun t => Q t ω) := by
    filter_upwards [hQid, actualBracket_ae_regular T hB hBmeas hK φ hφ] with ω hQω hreg
    have heq : (fun t => Q t ω) =
        (fun t : Set.Icc (0 : ℝ≥0) T =>
          ∫ r in Set.Ioc (0 : ℝ≥0) t.val, (φ (r, ω)) ^ 2 ∂timeMeasure) := funext hQω
    rw [heq]
    exact hreg
  refine ⟨Q, hQa, hQzero, hQreg, hQid, ?_⟩
  let Z : ℕ → Set.Icc (0 : ℝ≥0) T → Ω → ℝ := fun n t ω =>
    Real.exp (lam * simpleSum B (s n) (c n) (N n) t.val ω -
      lam ^ 2 * simpleBracket (s n) (c n) (N n) t.val ω / 2)
  apply ExponentialMartingaleLimit.martingale_of_ae_limit_of_sq_integral_le G Z
  · intro n
    exact Doob.martingale_compMono
      (scaled_simple_martingale (s n) (hs n) (c n) (hc n) (hb n) lam (N n))
      (fun t : Set.Icc (0 : ℝ≥0) T => t.val) (fun _ _ h => h)
  · intro t
    exact (Real.measurable_exp.comp
      (((continuousIto_representative_adapted T hB hBmeas hnull φ t).measurable.const_mul
        lam).sub (((hQa t).measurable.const_mul (lam ^ 2)).div_const 2))).stronglyMeasurable
  · intro n t
    exact (simple_exp_sq_bound (s n) (hs n) (hz n) (c n) (hc n) (hb n) lam (N n) t.val).1
  · intro t
    exact ⟨Real.exp (lam ^ 2 * (K ^ 2 * (t.val : ℝ))), fun n =>
      (simple_exp_sq_bound (s n) (hs n) (hz n) (c n) (hc n) (hb n) lam (N n) t.val).2⟩
  · intro t
    filter_upwards [hconv, hQid] with ω hω hQω
    have hq : Tendsto (fun n => simpleBracket (s n) (c n) (N n) t.val ω)
        atTop (𝓝 (Q t ω)) := by
      rw [hQω t]
      exact (hω t).2
    exact Real.continuous_exp.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul (hω t).1).sub ((tendsto_const_nhds.mul hq).div_const 2))

/-- Exponential maximal inequality for the actual continuous integral and
actual time-integral bracket of a bounded predictable L² class on `[0,T]`. -/
theorem bounded_predictable_exponential_maximal (T : ℝ≥0)
    (hB : ∀ ω, Continuous (fun t => B t ω)) (hBmeas : ∀ t, Measurable (B t))
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    {K : ℝ} (hK : 0 ≤ K)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ z ∂(trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas), |φ z| ≤ K)
    {r q : ℝ} (hr : 0 ≤ r) (hq : 0 < q) :
    μ {ω | (∃ t : Set.Icc (0 : ℝ≥0) T,
        r ≤ representative (continuousIto T hB hBmeas φ) ω t) ∧
      (∫ s in Set.Ioc (0 : ℝ≥0) T, (φ (s, ω)) ^ 2 ∂timeMeasure) ≤ q} ≤
        ENNReal.ofReal (Real.exp (-r ^ 2 / (2 * q))) := by
  obtain ⟨Q, hQa, hQzero, hQreg, hQid, hZ⟩ :=
    exists_bounded_predictable_stochastic_exponential T hB hBmeas hnull hK φ hφ (r / q)
  have hMzero : ∀ᵐ ω ∂μ,
      representative (continuousIto T hB hBmeas φ) ω ⟨0, zero_le, zero_le⟩ = 0 := by
    obtain ⟨ns, hns, hconv⟩ := exists_common_integral_bracket_subsequence T hB hBmeas hK φ hφ
    filter_upwards [hconv] with ω hω
    have hlim := (hω ⟨0, zero_le, zero_le⟩).1
    have hzlim : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (representative (continuousIto T hB hBmeas φ) ω ⟨0, zero_le, zero_le⟩)) := by
      simpa only [simpleSum, min_zero, NNReal.coe_zero, sub_self, mul_zero, Finset.sum_const_zero] using hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hzlim).symm
  have hbound := ContinuousExponentialMaximal.compact_exponential_maximal_ae T
    (fun t ω => representative (continuousIto T hB hBmeas φ) ω t) Q
    hMzero (ae_of_all _ hQzero) (hQreg.mono fun _ h => h.1)
    (ae_of_all _ fun ω => (representative (continuousIto T hB hBmeas φ) ω).continuous)
    (hQreg.mono fun _ h => h.2) hr hq hZ.supermartingale
  apply le_trans (measure_mono_ae ?_) hbound
  filter_upwards [hQid] with ω hQω
  intro hω
  exact ⟨hω.1, by simpa only [hQω ⟨T, zero_le, le_rfl⟩] using hω.2⟩

end Ripple.Stochastic.BoundedPredictableApproximation
