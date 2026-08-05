/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.MultiProductiveClock
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The embedded productive-event chain for multi-species Tri

The paper's proper-stage proof is expressed in productive-event time.  This
file constructs that chain by conditioning the finite physical sampler at
each full configuration.  The construction remains on `Config`; no projected
gap is asserted to be Markov.
-/

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- Productive mass is a genuine probability. -/
theorem productiveMass_le_one
    (c : Config m n) (h3 : 3 ≤ n) :
    productiveMass c h3 ≤ 1 := by
  rw [← productiveMass_add_nonproductiveMass c h3]
  exact le_add_right le_rfl

/-- The physical triple sampler conditioned on firing. -/
noncomputable def productiveSamplePMF
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0) :
    PMF (TripleSample c) := by
  classical
  let P := productiveMass c h3
  have hPtop : P ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (productiveMass_le_one c h3)
  refine PMF.ofFintype
    (fun t =>
      if IsProductiveSample t then triplePMF c h3 t / P else 0) ?_
  calc
    (∑ t : TripleSample c,
      if IsProductiveSample t then triplePMF c h3 t / P else 0) =
        (∑ t : TripleSample c,
          if IsProductiveSample t then triplePMF c h3 t else 0) / P := by
      simp only [div_eq_mul_inv]
      calc
        (∑ t : TripleSample c,
            if IsProductiveSample t then triplePMF c h3 t * P⁻¹ else 0) =
            ∑ t : TripleSample c,
              (if IsProductiveSample t then triplePMF c h3 t else 0) *
                P⁻¹ := by
          apply Finset.sum_congr rfl
          intro t _ht
          by_cases ht : IsProductiveSample t <;> simp [ht]
        _ = (∑ t : TripleSample c,
              if IsProductiveSample t then triplePMF c h3 t else 0) *
                P⁻¹ := by
          rw [Finset.sum_mul]
    _ = productiveMass c h3 / P := by
      unfold productiveMass
      rw [tsum_fintype]
    _ = P / P := by rfl
    _ = 1 := ENNReal.div_self hprod hPtop

@[simp] theorem productiveSamplePMF_apply
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (t : TripleSample c) :
    productiveSamplePMF c h3 hprod t =
      if IsProductiveSample t then
        triplePMF c h3 t / productiveMass c h3
      else 0 := by
  rfl

/-- The conditioned sampler assigns zero mass to inert samples. -/
theorem productiveSamplePMF_eq_zero_of_not_productive
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (t : TripleSample c) (ht : ¬ IsProductiveSample t) :
    productiveSamplePMF c h3 hprod t = 0 := by
  simp [productiveSamplePMF_apply, ht]

/-- Exact expectation formula under the conditioned productive sampler. -/
theorem expect_productiveSamplePMF
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (F : TripleSample c → ℝ≥0∞) :
    expect (productiveSamplePMF c h3 hprod) F =
      (∑' t : TripleSample c,
        if IsProductiveSample t then triplePMF c h3 t * F t else 0) /
          productiveMass c h3 := by
  classical
  unfold expect
  simp only [productiveSamplePMF_apply, tsum_fintype]
  simp only [div_eq_mul_inv]
  calc
    (∑ t : TripleSample c,
      (if IsProductiveSample t then
          triplePMF c h3 t * (productiveMass c h3)⁻¹ else 0) * F t) =
        ∑ t : TripleSample c,
          (if IsProductiveSample t then triplePMF c h3 t * F t else 0) *
            (productiveMass c h3)⁻¹ := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases ht : IsProductiveSample t <;> simp [ht]
      ring
    _ = (∑ t : TripleSample c,
          if IsProductiveSample t then triplePMF c h3 t * F t else 0) *
            (productiveMass c h3)⁻¹ := by
      rw [Finset.sum_mul]

/-- A productive sample involves `X` when `X` is either its winner or loser. -/
def IsXInvolvingSample
    {c : Config m n} (X : Species m) (t : TripleSample c) : Prop :=
  ∃ Y, Y ≠ X ∧
    (IsFirePair t (X, Y) ∨ IsFirePair t (Y, X))

noncomputable instance isXInvolvingSampleDecidable
    {c : Config m n} (X : Species m) (t : TripleSample c) :
    Decidable (IsXInvolvingSample X t) :=
  Classical.dec _

/-- Every `X`-involving sample is productive. -/
theorem isProductiveSample_of_isXInvolvingSample
    {c : Config m n} (X : Species m) (t : TripleSample c)
    (ht : IsXInvolvingSample X t) :
    IsProductiveSample t := by
  obtain ⟨Y, _hYX, hfire⟩ := ht
  unfold IsProductiveSample
  intro hnone
  have hnofire := (classify_eq_none_iff t).mp hnone
  rcases hfire with hfire | hfire
  · exact hnofire (X, Y) hfire
  · exact hnofire (Y, X) hfire

/-- Pointwise disjoint partition of an `X`-involving sample into the directed
fibers where `X` wins or loses. -/
theorem xFireIndicator_sum_eq_involving
    {c : Config m n} (t : TripleSample c)
    (X : Species m) (q : ℝ≥0∞) :
    (∑ Y ∈ Finset.univ.erase X,
      (fireIndicator t (X, Y) q + fireIndicator t (Y, X) q)) =
        if IsXInvolvingSample X t then q else 0 := by
  classical
  by_cases ht : IsXInvolvingSample X t
  · rw [if_pos ht]
    obtain ⟨Y, hYX, hfire | hfire⟩ := ht
    · have hmem :
          Y ∈ (Finset.univ.erase X : Finset (Species m)) := by
        simp [hYX]
      calc
        (∑ Z ∈ Finset.univ.erase X,
          (fireIndicator t (X, Z) q +
            fireIndicator t (Z, X) q)) =
            fireIndicator t (X, Y) q +
              fireIndicator t (Y, X) q := by
          apply Finset.sum_eq_single_of_mem Y hmem
          intro Z _hZ hZY
          have hforward : ¬ IsFirePair t (X, Z) := by
            intro hZ
            have hp := isFirePair_unique t hfire hZ
            have hYZ : Y = Z := congrArg Prod.snd hp
            exact hZY hYZ.symm
          have hreverse : ¬ IsFirePair t (Z, X) := by
            intro hZ
            have hp := isFirePair_unique t hfire hZ
            have hbad : Y = X := congrArg Prod.snd hp
            exact hYX hbad
          simp [fireIndicator, hforward, hreverse]
        _ = q := by
          have hreverse : ¬ IsFirePair t (Y, X) := by
            intro hrev
            have hp := isFirePair_unique t hfire hrev
            have hbad : Y = X := congrArg Prod.snd hp
            exact hYX hbad
          simp [fireIndicator, hfire, hreverse]
    · have hmem :
          Y ∈ (Finset.univ.erase X : Finset (Species m)) := by
        simp [hYX]
      calc
        (∑ Z ∈ Finset.univ.erase X,
          (fireIndicator t (X, Z) q +
            fireIndicator t (Z, X) q)) =
            fireIndicator t (X, Y) q +
              fireIndicator t (Y, X) q := by
          apply Finset.sum_eq_single_of_mem Y hmem
          intro Z _hZ hZY
          have hforward : ¬ IsFirePair t (X, Z) := by
            intro hZ
            have hp := isFirePair_unique t hfire hZ
            have hfirst : Y = X := congrArg Prod.fst hp
            exact hYX hfirst
          have hreverse : ¬ IsFirePair t (Z, X) := by
            intro hZ
            have hp := isFirePair_unique t hfire hZ
            have hYZ : Y = Z := congrArg Prod.fst hp
            exact hZY hYZ.symm
          simp [fireIndicator, hforward, hreverse]
        _ = q := by
          have hforward : ¬ IsFirePair t (X, Y) := by
            intro hfwd
            have hp := isFirePair_unique t hfire hfwd
            have hbad : Y = X := congrArg Prod.fst hp
            exact hYX hbad
          simp [fireIndicator, hfire, hforward]
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro Y hY
    have hYX : Y ≠ X := (Finset.mem_erase.mp hY).1
    have hforward : ¬ IsFirePair t (X, Y) := by
      intro hfire
      exact ht ⟨Y, hYX, Or.inl hfire⟩
    have hreverse : ¬ IsFirePair t (Y, X) := by
      intro hfire
      exact ht ⟨Y, hYX, Or.inr hfire⟩
    simp [fireIndicator, hforward, hreverse]

/-- The raw mass of the `X`-involving event is the previously computed sum of
all `X`-winner and `X`-loser fibers. -/
theorem xInvolvingMass_eq_event
    (c : Config m n) (h3 : 3 ≤ n) (X : Species m) :
    xInvolvingMass c h3 X =
      ∑' t : TripleSample c,
        if IsXInvolvingSample X t then triplePMF c h3 t else 0 := by
  classical
  unfold xInvolvingMass xWinnerFireMass xLoserFireMass directedFireMass
  simp only [tsum_fintype]
  calc
    (∑ Y ∈ Finset.univ.erase X,
        ∑ t : TripleSample c,
          if IsFirePair t (X, Y) then triplePMF c h3 t else 0) +
      (∑ Y ∈ Finset.univ.erase X,
        ∑ t : TripleSample c,
          if IsFirePair t (Y, X) then triplePMF c h3 t else 0) =
        ∑ Y ∈ Finset.univ.erase X,
          ((∑ t : TripleSample c,
              if IsFirePair t (X, Y) then triplePMF c h3 t else 0) +
            ∑ t : TripleSample c,
              if IsFirePair t (Y, X) then triplePMF c h3 t else 0) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ Y ∈ Finset.univ.erase X,
          ∑ t : TripleSample c,
            ((if IsFirePair t (X, Y) then triplePMF c h3 t else 0) +
              if IsFirePair t (Y, X) then triplePMF c h3 t else 0) := by
      apply Finset.sum_congr rfl
      intro Y _hY
      rw [Finset.sum_add_distrib]
    _ = ∑ t : TripleSample c,
          ∑ Y ∈ Finset.univ.erase X,
            ((if IsFirePair t (X, Y) then triplePMF c h3 t else 0) +
              if IsFirePair t (Y, X) then triplePMF c h3 t else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ t : TripleSample c,
          if IsXInvolvingSample X t then triplePMF c h3 t else 0 := by
      apply Finset.sum_congr rfl
      intro t _ht
      simpa [fireIndicator] using
        xFireIndicator_sum_eq_involving
          t X (triplePMF c h3 t)

/-- Under the productive-event law, the chance of involving `X` is exactly
the raw involving mass divided by total productive mass. -/
theorem productiveSamplePMF_involvingMass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0) (X : Species m) :
    (∑' t : TripleSample c,
      if IsXInvolvingSample X t then
        productiveSamplePMF c h3 hprod t else 0) =
      xInvolvingMass c h3 X / productiveMass c h3 := by
  classical
  simp only [productiveSamplePMF_apply, tsum_fintype]
  simp only [div_eq_mul_inv]
  calc
    (∑ t : TripleSample c,
      if IsXInvolvingSample X t then
        (if IsProductiveSample t then
          triplePMF c h3 t * (productiveMass c h3)⁻¹ else 0)
      else 0) =
        ∑ t : TripleSample c,
          (if IsXInvolvingSample X t then triplePMF c h3 t else 0) *
            (productiveMass c h3)⁻¹ := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases hXt : IsXInvolvingSample X t
      · have hpt := isProductiveSample_of_isXInvolvingSample X t hXt
        simp [hXt, hpt]
      · simp [hXt]
    _ = (∑ t : TripleSample c,
          if IsXInvolvingSample X t then triplePMF c h3 t else 0) *
            (productiveMass c h3)⁻¹ := by
      rw [Finset.sum_mul]
    _ = xInvolvingMass c h3 X * (productiveMass c h3)⁻¹ := by
      rw [xInvolvingMass_eq_event, tsum_fintype]

/-- If `X` retains at least half its stage-start count `x0`, then under the
productive-event law the probability that the next reaction involves `X` is
at least `x0/(2n)`. -/
theorem initialCount_div_two_population_le_productive_involvingMass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X : Species m) (x0 : ℕ)
    (hx : x0 ≤ 2 * count c X) :
    (x0 : ℝ≥0∞) / (2 * n : ℕ) ≤
      ∑' t : TripleSample c,
        if IsXInvolvingSample X t then
          productiveSamplePMF c h3 hprod t else 0 := by
  rw [productiveSamplePMF_involvingMass]
  have hPtop : productiveMass c h3 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (productiveMass_le_one c h3)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hprod) (Or.inl hPtop)).2
  have hden0 : (((2 * n : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast
      Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt (by omega : 0 < n))
  have hdentop : (((2 * n : ℕ) : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  have hcross :
      (x0 : ℝ≥0∞) * productiveMass c h3 ≤
        (2 * n : ℕ) * xInvolvingMass c h3 X :=
    initialCount_mul_productiveMass_le_two_population_mul_xInvolvingMass
      c h3 X x0 hx
  have hdiv :
      ((x0 : ℝ≥0∞) * productiveMass c h3) / (2 * n : ℕ) ≤
        xInvolvingMass c h3 X := by
    apply (ENNReal.div_le_iff_le_mul
      (Or.inl hden0) (Or.inl hdentop)).2
    simpa [mul_comm] using hcross
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- Conditional probability that the next productive reaction involves `X`. -/
noncomputable def productiveInvolvingMass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X : Species m) : ℝ≥0∞ :=
  ∑' t : TripleSample c,
    if IsXInvolvingSample X t then
      productiveSamplePMF c h3 hprod t else 0

/-- Complementary conditional mass of productive reactions not involving
`X`. -/
noncomputable def productiveNoninvolvingMass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X : Species m) : ℝ≥0∞ :=
  ∑' t : TripleSample c,
    if IsXInvolvingSample X t then 0
    else productiveSamplePMF c h3 hprod t

/-- Involving and noninvolving productive reactions partition the conditioned
sampler. -/
theorem productiveInvolvingMass_add_noninvolvingMass
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X : Species m) :
    productiveInvolvingMass c h3 hprod X +
        productiveNoninvolvingMass c h3 hprod X = 1 := by
  classical
  unfold productiveInvolvingMass productiveNoninvolvingMass
  simp only [tsum_fintype, ← Finset.sum_add_distrib]
  calc
    ∑ t : TripleSample c,
        ((if IsXInvolvingSample X t then
            productiveSamplePMF c h3 hprod t else 0) +
          if IsXInvolvingSample X t then 0
          else productiveSamplePMF c h3 hprod t) =
        ∑ t : TripleSample c, productiveSamplePMF c h3 hprod t := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases hXt : IsXInvolvingSample X t <;> simp [hXt]
    _ = ∑' t : TripleSample c, productiveSamplePMF c h3 hprod t := by
      rw [tsum_fintype]
    _ = 1 := PMF.tsum_coe _

/-- Productive-event chain augmented by the number of reactions involving
`X`.  Zero-productive-mass states are made absorbing. -/
noncomputable def productiveInvolvingCount
    (h3 : 3 ≤ n) (X : Species m) :
    Config m n × ℕ → PMF (Config m n × ℕ) := by
  classical
  exact fun q => by
    by_cases hprod : productiveMass q.1 h3 ≠ 0
    · exact (productiveSamplePMF q.1 h3 hprod).map fun t =>
        (sampleNext q.1 t,
          if IsXInvolvingSample X t then q.2 + 1 else q.2)
    · exact PMF.pure q

/-- Exact two-way counter decomposition in a positive-productive-mass state. -/
theorem expect_productiveInvolvingCount
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X : Species m) (k : ℕ) (w : ℝ≥0∞) :
    expect (productiveInvolvingCount h3 X (c, k))
        (fun q => w ^ q.2) =
      productiveNoninvolvingMass c h3 hprod X * w ^ k +
        productiveInvolvingMass c h3 hprod X * w ^ (k + 1) := by
  classical
  rw [show productiveInvolvingCount h3 X (c, k) =
      (productiveSamplePMF c h3 hprod).map
        (fun t =>
          (sampleNext c t,
            if IsXInvolvingSample X t then k + 1 else k)) by
    unfold productiveInvolvingCount
    simp [hprod]]
  rw [expect_map]
  unfold expect productiveInvolvingMass productiveNoninvolvingMass
  simp only [tsum_fintype]
  calc
    ∑ t : TripleSample c,
        productiveSamplePMF c h3 hprod t *
          w ^ (if IsXInvolvingSample X t then k + 1 else k) =
      ∑ t : TripleSample c,
        ((if IsXInvolvingSample X t then 0
          else productiveSamplePMF c h3 hprod t) * w ^ k +
        (if IsXInvolvingSample X t then
          productiveSamplePMF c h3 hprod t else 0) * w ^ (k + 1)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases hXt : IsXInvolvingSample X t <;> simp [hXt]
    _ = (∑ t : TripleSample c,
          if IsXInvolvingSample X t then 0
          else productiveSamplePMF c h3 hprod t) * w ^ k +
        (∑ t : TripleSample c,
          if IsXInvolvingSample X t then
            productiveSamplePMF c h3 hprod t else 0) * w ^ (k + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]

/-- Any lower bound on the conditional involving mass gives the adapted
one-step counter contraction. -/
theorem productiveInvolvingCount_step_of_lower
    (c : Config m n) (h3 : 3 ≤ n)
    (hprod : productiveMass c h3 ≠ 0)
    (X : Species m) (k : ℕ)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hpq : p ≤ productiveInvolvingMass c h3 hprod X) :
    expect (productiveInvolvingCount h3 X (c, k))
        (fun q => w ^ q.2) ≤
      (p' + p * w) * w ^ k := by
  apply count_step_of_masses
    (q := productiveInvolvingMass c h3 hprod X)
    (q' := productiveNoninvolvingMass c h3 hprod X)
    (p := p) (p' := p')
  · exact productiveInvolvingMass_add_noninvolvingMass
      c h3 hprod X
  · exact hp
  · exact hw
  · exact hpq
  · exact expect_productiveInvolvingCount c h3 hprod X k w

/-- Stop the involving counter if productive conditioning becomes undefined,
`X` falls below half its stage-start count, or the involving-event target has
already been exceeded. -/
def ProductiveInvolvingBoundary
    (h3 : 3 ≤ n) (X : Species m) (x0 M : ℕ)
    (q : Config m n × ℕ) : Prop :=
  productiveMass q.1 h3 = 0 ∨
    2 * count q.1 X < x0 ∨ M < q.2

noncomputable instance productiveInvolvingBoundaryDecidable
    (h3 : 3 ≤ n) (X : Species m) (x0 M : ℕ) :
    DecidablePred (ProductiveInvolvingBoundary h3 X x0 M) :=
  Classical.decPred _

/-- Productive-event involving counter frozen on the stage boundary. -/
noncomputable def productiveInvolvingStop
    (h3 : 3 ≤ n) (X : Species m) (x0 M : ℕ) :
    Config m n × ℕ → PMF (Config m n × ℕ) :=
  freeze (ProductiveInvolvingBoundary h3 X x0 M)
    (productiveInvolvingCount h3 X)

/-- Vanishing counter potential for the stopped productive-event stage. -/
theorem productiveInvolvingStop_count_super
    (h3 : 3 ≤ n) (X : Species m) (x0 M : ℕ)
    (w p p' : ℝ≥0∞)
    (hw : w ≤ 1) (hp : p + p' = 1)
    (hpFloor : p ≤ (x0 : ℝ≥0∞) / (2 * n : ℕ)) :
    ∀ q,
      expect (productiveInvolvingStop h3 X x0 M q)
          (fun z => if ProductiveInvolvingBoundary h3 X x0 M z
            then 0 else w ^ z.2) ≤
        (p' + p * w) *
          (if ProductiveInvolvingBoundary h3 X x0 M q
            then 0 else w ^ q.2) := by
  intro q
  by_cases hq : ProductiveInvolvingBoundary h3 X x0 M q
  · rw [productiveInvolvingStop, freeze_of_mem q hq, expect_pure]
    simp [hq]
  · rw [productiveInvolvingStop, freeze_of_not_mem q hq, if_neg hq]
    have hprod : productiveMass q.1 h3 ≠ 0 := by
      unfold ProductiveInvolvingBoundary at hq
      tauto
    have hx : x0 ≤ 2 * count q.1 X := by
      unfold ProductiveInvolvingBoundary at hq
      omega
    have hpq :
        p ≤ productiveInvolvingMass q.1 h3 hprod X := by
      unfold productiveInvolvingMass
      exact hpFloor.trans
        (initialCount_div_two_population_le_productive_involvingMass
          q.1 h3 hprod X x0 hx)
    calc
      expect (productiveInvolvingCount h3 X q)
          (fun z => if ProductiveInvolvingBoundary h3 X x0 M z
            then 0 else w ^ z.2) ≤
          expect (productiveInvolvingCount h3 X q)
            (fun z => w ^ z.2) := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun z =>
                mul_le_mul_right (by
                  change
                    (if ProductiveInvolvingBoundary h3 X x0 M z
                      then 0 else w ^ z.2) ≤ w ^ z.2
                  split_ifs <;> simp) _
      _ ≤ (p' + p * w) * w ^ q.2 := by
        simpa only using
          productiveInvolvingCount_step_of_lower
            q.1 h3 hprod X q.2 w p p' hw hp hpq

/-- Adapted lower tail for insufficient `X`-involving reactions in
productive-event time. -/
theorem productiveInvolvingStop_tail
    (h3 : 3 ≤ n) (X : Species m) (x0 M : ℕ)
    (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hp : p + p' = 1)
    (hpFloor : p ≤ (x0 : ℝ≥0∞) / (2 * n : ℕ))
    (T : ℕ) (q0 : Config m n × ℕ) :
    (∑' q, if q.2 ≤ M ∧
        ¬ ProductiveInvolvingBoundary h3 X x0 M q then
        iter (productiveInvolvingStop h3 X x0 M) T q0 q else 0) ≤
      (p' + p * w) ^ T *
        (if ProductiveInvolvingBoundary h3 X x0 M q0
          then 0 else w ^ q0.2) / w ^ M := by
  let V : Config m n × ℕ → ℝ≥0∞ := fun q =>
    if ProductiveInvolvingBoundary h3 X x0 M q
      then 0 else w ^ q.2
  let θ : ℝ≥0∞ := w ^ M
  have hwtop : w ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hθ0 : θ ≠ 0 := pow_ne_zero _ hw0
  have hθtop : θ ≠ ⊤ := ENNReal.pow_ne_top hwtop
  have hsub : ∀ q,
      (if q.2 ≤ M ∧
          ¬ ProductiveInvolvingBoundary h3 X x0 M q then
          iter (productiveInvolvingStop h3 X x0 M) T q0 q else 0) ≤
        (if θ ≤ V q then
          iter (productiveInvolvingStop h3 X x0 M) T q0 q else 0) := by
    intro q
    by_cases hq : q.2 ≤ M ∧
        ¬ ProductiveInvolvingBoundary h3 X x0 M q
    · have hle : θ ≤ V q := by
        simp only [V, hq.2, if_false, θ]
        exact pow_le_pow_right_of_le_one' hw1 hq.1
      simp [hq, hle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans
    (markov_div
      (iter (productiveInvolvingStop h3 X x0 M) T q0)
      V θ hθ0 hθtop) ?_
  have hiter :=
    expect_iter_le
      (productiveInvolvingStop h3 X x0 M)
      V (p' + p * w)
      (by
        simpa only [V] using
          productiveInvolvingStop_count_super
            h3 X x0 M w p p' hw1 hp hpFloor)
      T q0
  exact ENNReal.div_le_div_right
    (by simpa only [V] using hiter) θ

/-- The involving-count tail instantiated at its proved conditional floor
`p=x0/(2n)`. -/
theorem productiveInvolvingStop_tail_floor
    (h3 : 3 ≤ n) (X : Species m) (x0 M : ℕ)
    (hx0 : x0 ≤ n)
    (w : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (T : ℕ) (q0 : Config m n × ℕ) :
    (∑' q, if q.2 ≤ M ∧
        ¬ ProductiveInvolvingBoundary h3 X x0 M q then
        iter (productiveInvolvingStop h3 X x0 M) T q0 q else 0) ≤
      ((1 - (x0 : ℝ≥0∞) / (2 * n : ℕ)) +
          ((x0 : ℝ≥0∞) / (2 * n : ℕ)) * w) ^ T *
        (if ProductiveInvolvingBoundary h3 X x0 M q0
          then 0 else w ^ q0.2) / w ^ M := by
  let p : ℝ≥0∞ := (x0 : ℝ≥0∞) / (2 * n : ℕ)
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    have hcross : (x0 : ℝ≥0∞) ≤ (2 * n : ℕ) := by
      exact_mod_cast (hx0.trans (by omega : n ≤ 2 * n))
    exact ENNReal.div_le_of_le_mul (by simpa using hcross)
  have hpSum : p + (1 - p) = 1 := by
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  simpa only [p] using
    productiveInvolvingStop_tail
      h3 X x0 M w p (1 - p)
      hw1 hw0 hpSum le_rfl T q0

/-- Scalar form of the paper's claim: among `2n` productive reactions, having
at most `⌊x0/2⌋` reactions involving `X` costs at most `exp(-x0/8)`. -/
theorem productiveInvolving_two_population_error_le
    (n x0 : ℕ) (h3 : 3 ≤ n) (hx0 : x0 ≤ n) :
    ((1 - (x0 : ℝ≥0∞) / (2 * n : ℕ)) +
          ((x0 : ℝ≥0∞) / (2 * n : ℕ)) *
            ((1 : ℝ≥0∞) / 2)) ^ (2 * n) /
        ((1 : ℝ≥0∞) / 2) ^ (x0 / 2) ≤
      ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by
  let p : ℝ≥0∞ := (x0 : ℝ≥0∞) / (2 * n : ℕ)
  let p' : ℝ≥0∞ := 1 - p
  let half : ℝ≥0∞ := (1 : ℝ≥0∞) / 2
  let x : ℝ≥0∞ := p * half
  let δ : ℝ := (x0 : ℝ) / (4 * (n : ℝ))
  let δe : ℝ≥0∞ := ENNReal.ofReal δ
  let T : ℕ := 2 * n
  let E : ℕ := x0 / 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ0 : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hδ1 : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_one (by positivity : (0 : ℝ) < 4 * n)]
    have hx0R : (x0 : ℝ) ≤ n := by exact_mod_cast hx0
    nlinarith
  have hpLe : p ≤ 1 := by
    dsimp only [p]
    have hcross : (x0 : ℝ≥0∞) ≤ (2 * n : ℕ) := by
      exact_mod_cast (hx0.trans (by omega : n ≤ 2 * n))
    exact ENNReal.div_le_of_le_mul (by simpa using hcross)
  have hppsum : p + p' = 1 := by
    dsimp only [p']
    rw [add_comm]
    exact tsub_add_cancel_of_le hpLe
  have hhalfCancel : (2 : ℝ≥0∞) * half = 1 := by
    dsimp only [half]
    rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hhalfAdd : half + half = 1 := by
    calc
      half + half = 2 * half := by ring
      _ = 1 := hhalfCancel
  have hxx : x + x = p := by
    dsimp only [x]
    calc
      p * half + p * half = p * (half + half) := by ring
      _ = p := by rw [hhalfAdd, mul_one]
  have hxδ : x = δe := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by unfold x p half; finiteness)
      (by unfold δe; exact ENNReal.ofReal_ne_top)).mp
    dsimp only [x, p, half, δe, δ]
    rw [ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_div, ENNReal.toReal_ofReal hδ0]
    norm_num only [ENNReal.toReal_natCast, Nat.cast_mul,
      Nat.cast_ofNat, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_mul]
    norm_num only [ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    dsimp only [δ]
    field_simp
    ring
  have hphiSum : (p' + x) + δe ≤ 1 := by
    rw [← hxδ]
    calc
      (p' + x) + x = p' + (x + x) := by ring
      _ = p' + p := by rw [hxx]
      _ = 1 := by rw [add_comm, hppsum]
      _ ≤ 1 := le_rfl
  have hδtop : δe ≠ ⊤ := by
    dsimp only [δe]
    exact ENNReal.ofReal_ne_top
  have hphiSub : p' + x ≤ 1 - δe :=
    ENNReal.le_sub_of_add_le_right hδtop hphiSum
  have hsub : 1 - δe = ENNReal.ofReal (1 - δ) := by
    dsimp only [δe]
    rw [ENNReal.ofReal_sub 1 hδ0, ENNReal.ofReal_one]
  have hphi : p' + x ≤ ENNReal.ofReal (1 - δ) := by
    rwa [← hsub]
  have hnum :
      (p' + x) ^ T ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) :=
    enn_pow_le_ofReal_exp (p' + x) δ T hδ0 hδ1 hphi
  have hdiv :
      (p' + x) ^ T / half ^ E ≤
        ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ E :=
    ENNReal.div_le_div_right hnum _
  have hhalf :
      half = ENNReal.ofReal (1 / 2 : ℝ) := by
    dsimp only [half]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hquot :
      ENNReal.ofReal (Real.exp (-(δ * (T : ℝ)))) /
          half ^ E =
        ENNReal.ofReal
          (Real.exp
            (-(δ * (T : ℝ)) + (E : ℝ) * Real.log 2)) := by
    rw [hhalf, ← ENNReal.ofReal_pow
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← ENNReal.ofReal_div_of_pos
      (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ E)]
    congr 2
    have hhalfReal :
        (1 / 2 : ℝ) ^ E =
          Real.exp (-(E : ℝ) * Real.log 2) := by
      rw [← Real.exp_log
        (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ E),
        Real.log_pow]
      have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      rw [hlogHalf]
      congr 1
      ring
    rw [hhalfReal, ← Real.exp_sub]
    congr 1
    ring
  have hT : (T : ℝ) = 2 * (n : ℝ) := by
    dsimp only [T]
    push_cast
    ring
  have hδT : δ * (T : ℝ) = (x0 : ℝ) / 2 := by
    rw [hT]
    dsimp only [δ]
    field_simp
    ring
  have hER : (E : ℝ) ≤ (x0 : ℝ) / 2 := by
    dsimp only [E]
    have hnat : 2 * (x0 / 2) ≤ x0 := by omega
    have hreal : (2 * (x0 / 2) : ℕ) ≤ (x0 : ℝ) := by
      exact_mod_cast hnat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hreal
    linarith
  have hlog2 : Real.log 2 ≤ (3 : ℝ) / 4 :=
    le_trans (Real.log_two_lt_d9).le (by norm_num)
  have hE0 : (0 : ℝ) ≤ E := by positivity
  have hscaledE :
      (E : ℝ) * Real.log 2 ≤ 3 * (x0 : ℝ) / 8 := by
    calc
      (E : ℝ) * Real.log 2 ≤ (E : ℝ) * ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hlog2 hE0
      _ ≤ ((x0 : ℝ) / 2) * ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hER (by norm_num)
      _ = 3 * (x0 : ℝ) / 8 := by ring
  have hexponent :
      -(δ * (T : ℝ)) + (E : ℝ) * Real.log 2 ≤
        -(x0 : ℝ) / 8 := by
    rw [hδT]
    linarith
  change (p' + x) ^ T / half ^ E ≤ _
  exact hdiv.trans (hquot.le.trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)))

/-- The stopped-chain version of the paper's `2n` productive-event
involvement estimate. -/
theorem productiveInvolvingStop_two_population_deadline
    (h3 : 3 ≤ n) (X : Species m) (x0 : ℕ)
    (hx0 : x0 ≤ n) (q0 : Config m n × ℕ)
    (hq0 : ¬ ProductiveInvolvingBoundary h3 X x0 (x0 / 2) q0)
    (hc0 : q0.2 = 0) :
    (∑' q, if q.2 ≤ x0 / 2 ∧
        ¬ ProductiveInvolvingBoundary h3 X x0 (x0 / 2) q then
        iter (productiveInvolvingStop h3 X x0 (x0 / 2))
          (2 * n) q0 q else 0) ≤
      ENNReal.ofReal (Real.exp (-(x0 : ℝ) / 8)) := by
  have htail :=
    productiveInvolvingStop_tail_floor
      h3 X x0 (x0 / 2) hx0
      ((1 : ℝ≥0∞) / 2) (by norm_num) (by norm_num)
      (2 * n) q0
  rw [if_neg hq0, hc0, pow_zero, mul_one] at htail
  exact htail.trans
    (productiveInvolving_two_population_error_le n x0 h3 hx0)

/-- Full-state productive-event transition.  At a zero-productive-mass state
(necessarily outside the stage regions where it will be used), it is made
absorbing so the kernel is total. -/
noncomputable def productiveStep
    (h3 : 3 ≤ n) (c : Config m n) : PMF (Config m n) := by
  classical
  by_cases hprod : productiveMass c h3 ≠ 0
  · exact (productiveSamplePMF c h3 hprod).map (sampleNext c)
  · exact PMF.pure c

/-- In every positive-productive-mass state, the total productive kernel is
exactly the conditioned sampler mapped through the physical update. -/
theorem productiveStep_of_mass_ne_zero
    (h3 : 3 ≤ n) (c : Config m n)
    (hprod : productiveMass c h3 ≠ 0) :
    productiveStep h3 c =
      (productiveSamplePMF c h3 hprod).map (sampleNext c) := by
  classical
  unfold productiveStep
  simp [hprod]

end Tri.Multi

#print axioms Tri.Multi.productiveSamplePMF_apply
#print axioms Tri.Multi.expect_productiveSamplePMF
#print axioms Tri.Multi.xFireIndicator_sum_eq_involving
#print axioms Tri.Multi.xInvolvingMass_eq_event
#print axioms Tri.Multi.productiveSamplePMF_involvingMass
#print axioms Tri.Multi.initialCount_div_two_population_le_productive_involvingMass
#print axioms Tri.Multi.productiveInvolvingMass_add_noninvolvingMass
#print axioms Tri.Multi.expect_productiveInvolvingCount
#print axioms Tri.Multi.productiveInvolvingCount_step_of_lower
#print axioms Tri.Multi.productiveInvolvingStop_count_super
#print axioms Tri.Multi.productiveInvolvingStop_tail_floor
#print axioms Tri.Multi.productiveInvolving_two_population_error_le
#print axioms Tri.Multi.productiveInvolvingStop_two_population_deadline
#print axioms Tri.Multi.productiveStep_of_mass_ne_zero
