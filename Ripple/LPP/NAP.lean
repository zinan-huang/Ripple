/-
  Ripple.LPP.NAP — Non-Autocatalytic Protocols via Cubing

  Formalizes the PP → NAP construction from [BD] (Huang-Huls, DNA 30):
  - The r²-trick lifts a PP (degree 2) to a 4-PP (degree 4)
  - Cubing (degree-3 lifting) produces a NAP
  - NAP Splitting Feasibility: every positive monomial admits a
    non-autocatalytic factorization

  The key theorem (NAP Splitting Feasibility) is purely combinatorial:
  it concerns exponent vectors of monomials and their factorizations.

  Reference: Note 14 (working_notes/14_cubing_NAP_feasibility.tex)
-/

import Ripple.LPP.Syntactic
import Ripple.LPP.Stages

namespace Ripple

/-! ## Multi-indices

A multi-index α ∈ ℕⁿ represents the monomial x₀^{α₀} · x₁^{α₁} · ⋯.
The weight |α| = Σ αⱼ is the total degree. -/

/-- The weight (total degree) of a multi-index. -/
def miWeight {n : ℕ} (α : Fin n → ℕ) : ℕ := ∑ j, α j

/-- The support of a multi-index: indices where αⱼ > 0. -/
def miSupp {n : ℕ} (α : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < α j)

/-- A multi-index divides another if αⱼ ≤ βⱼ for all j. -/
def miDvd {n : ℕ} (α β : Fin n → ℕ) : Prop := ∀ j, α j ≤ β j

/-- The standard basis multi-index eⱼ (1 at position j, 0 elsewhere). -/
def miUnit {n : ℕ} (j : Fin n) : Fin n → ℕ := fun k => if k = j then 1 else 0

theorem miWeight_unit {n : ℕ} (j : Fin n) : miWeight (miUnit j) = 1 := by
  simp [miWeight, miUnit]

/-! ## Degree-3 factorizations

A factorization of a degree-6 monomial δ is a pair (β, γ) with
β + γ = δ and |β| = |γ| = 3.

A factorization is *non-autocatalytic* for α if β ≠ α and γ ≠ α. -/

/-- A factorization of δ into β + γ. -/
structure MonomialSplit {n : ℕ} (δ : Fin n → ℕ) where
  β : Fin n → ℕ
  γ : Fin n → ℕ
  sum_eq : ∀ j, β j + γ j = δ j

/-- The split type forgets the dependent proof `β + γ = δ` and remembers only
the two degree-3 factors. This is the right indexing object for supply/demand
aggregation in the PP -> NAP matching argument. -/
structure SplitType (n : ℕ) where
  β : Fin n → ℕ
  γ : Fin n → ℕ
deriving DecidableEq

def MonomialSplit.toType {n : ℕ} {δ : Fin n → ℕ} (s : MonomialSplit δ) : SplitType n :=
  ⟨s.β, s.γ⟩

/-- A split is degree-balanced (both factors have degree 3). -/
def MonomialSplit.balanced {n : ℕ} {δ : Fin n → ℕ} (s : MonomialSplit δ) : Prop :=
  miWeight s.β = 3 ∧ miWeight s.γ = 3

/-- A split avoids autocatalysis for target α. -/
def MonomialSplit.nonAutocatalytic {n : ℕ} {δ : Fin n → ℕ}
    (s : MonomialSplit δ) (α : Fin n → ℕ) : Prop :=
  s.β ≠ α ∧ s.γ ≠ α

/-! ## Cubed coefficients and rate balancing

The notebook uses the multinomial-lifted variables
`v_α = c_α · x^α`, where `c_α = 3! / ∏ᵢ αᵢ!`. If a degree-6 monomial
`coeff · x^δ` is routed to `v_β · v_γ`, the correct NAP rate is
`coeff / (c_β c_γ)`. The theorem below is the formal reconstruction identity
behind that formula. -/

/-- The raw monomial `x^α = ∏ᵢ xᵢ^{αᵢ}`. -/
noncomputable def rawMonomial {n : ℕ} (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, x i ^ α i

/-- The multinomial coefficient `3! / ∏ᵢ αᵢ!` for degree-3 lifted variables. -/
noncomputable def cubedCoeff {n : ℕ} (α : Fin n → ℕ) : ℚ :=
  6 / ∏ i, (Nat.factorial (α i) : ℚ)

/-- The lifted cubed variable `v_α = c_α · x^α`. -/
noncomputable def cubedLift {n : ℕ} (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  (cubedCoeff α : ℝ) * rawMonomial α x

/-- The balancing rate from the flow network:
`coeff / (c_β c_γ)`. -/
noncomputable def splitRate {n : ℕ} {δ : Fin n → ℕ}
    (coeff : ℚ) (s : MonomialSplit δ) : ℚ :=
  coeff / (cubedCoeff s.β * cubedCoeff s.γ)

theorem cubedCoeff_pos {n : ℕ} (α : Fin n → ℕ) :
    0 < cubedCoeff α := by
  unfold cubedCoeff
  apply div_pos
  · norm_num
  · exact Finset.prod_pos fun i _ => by
      exact_mod_cast Nat.factorial_pos (α i)

theorem cubedCoeff_nonneg {n : ℕ} (α : Fin n → ℕ) :
    0 ≤ cubedCoeff α :=
  le_of_lt (cubedCoeff_pos α)

theorem splitRate_nonneg {n : ℕ} {δ : Fin n → ℕ}
    {coeff : ℚ} (hcoeff : 0 ≤ coeff) (s : MonomialSplit δ) :
    0 ≤ splitRate coeff s := by
  unfold splitRate
  exact div_nonneg hcoeff
    (mul_nonneg (cubedCoeff_nonneg s.β) (cubedCoeff_nonneg s.γ))

theorem splitRate_neg {n : ℕ} {δ : Fin n → ℕ}
    (coeff : ℚ) (s : MonomialSplit δ) :
    splitRate (-coeff) s = -splitRate coeff s := by
  unfold splitRate
  ring

/-- Evaluate a split type as the corresponding NAP interaction monomial
`v_β · v_γ`. -/
noncomputable def SplitType.eval {n : ℕ} (τ : SplitType n) (x : Fin n → ℝ) : ℝ :=
  cubedLift τ.β x * cubedLift τ.γ x

theorem rawMonomial_add {n : ℕ} (α β : Fin n → ℕ) (x : Fin n → ℝ) :
    rawMonomial (fun i => α i + β i) x = rawMonomial α x * rawMonomial β x := by
  unfold rawMonomial
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib]

/-- The notebook's rate formula is exact: routing `coeff · x^δ` through a split
`δ = β + γ` at rate `coeff / (c_β c_γ)` reproduces the original monomial. -/
theorem splitRate_reconstructs {n : ℕ} {δ : Fin n → ℕ} (coeff : ℚ)
    (s : MonomialSplit δ) (x : Fin n → ℝ) :
    (splitRate coeff s : ℝ) * cubedLift s.β x * cubedLift s.γ x =
      (coeff : ℝ) * rawMonomial δ x := by
  have hfacβ_ne : ((∏ i, (Nat.factorial (s.β i) : ℚ)) : ℚ) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
      exact_mod_cast (Nat.factorial_pos _).ne')
  have hfacγ_ne : ((∏ i, (Nat.factorial (s.γ i) : ℚ)) : ℚ) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
      exact_mod_cast (Nat.factorial_pos _).ne')
  have hβ_ne : cubedCoeff s.β ≠ 0 := by
    unfold cubedCoeff
    exact div_ne_zero (by norm_num) hfacβ_ne
  have hγ_ne : cubedCoeff s.γ ≠ 0 := by
    unfold cubedCoeff
    exact div_ne_zero (by norm_num) hfacγ_ne
  have hcoeff :
      splitRate coeff s * cubedCoeff s.β * cubedCoeff s.γ = coeff := by
    unfold splitRate
    field_simp [hβ_ne, hγ_ne]
  have hmon :
      rawMonomial δ x = rawMonomial s.β x * rawMonomial s.γ x := by
    have hs : (fun i => s.β i + s.γ i) = δ := by
      funext i
      exact s.sum_eq i
    have hmon' :
        rawMonomial (fun i => s.β i + s.γ i) x =
          rawMonomial s.β x * rawMonomial s.γ x :=
      rawMonomial_add s.β s.γ x
    simpa [hs] using hmon'
  calc
    (splitRate coeff s : ℝ) * cubedLift s.β x * cubedLift s.γ x
        = ((splitRate coeff s * cubedCoeff s.β * cubedCoeff s.γ : ℚ) : ℝ) *
            (rawMonomial s.β x * rawMonomial s.γ x) := by
            unfold cubedLift
            simp_rw [Rat.cast_mul]
            ring
    _ = (coeff : ℝ) * (rawMonomial s.β x * rawMonomial s.γ x) := by
          norm_num [hcoeff]
    _ = (coeff : ℝ) * rawMonomial δ x := by rw [hmon]

/-! ## The 4-PP Condition

After the r²-trick, every derivative x'ⱼ = fⱼ(x) has degree 4,
and the positive part of fⱼ contains no monomial with x_j-exponent ≥ 4.

We model this as a constraint on exponent vectors of positive monomials. -/

/-- A degree-4 monomial (represented by its exponent vector δ with |δ| = 4)
satisfies the 4-PP condition for variable j if δⱼ < 4. -/
def is4PPMonomial {n : ℕ} (j : Fin n) (δ : Fin n → ℕ) : Prop :=
  δ j < 4

/-- The 4-PP condition: for each variable j, every positive monomial
in x'ⱼ has x_j-exponent < 4.

In fact, from the PP structure + r²-trick, the self-exponent is ≤ 2
(Proposition 2 in Note 14), but we only need < 4 for the main theorem. -/
structure Is4PP (n : ℕ) where
  /-- For each variable j and each positive monomial δ in x'ⱼ,
  the exponent of xⱼ in δ is < 4. -/
  no_self_fourth : ∀ (j : Fin n) (δ : Fin n → ℕ),
    miWeight δ = 4 → δ j < 4

/-! ## Cubed Variables

The cubing step defines v_α = C(3,α) · ∏ xⱼ^{αⱼ} for |α| = 3.
By the chain rule, each positive monomial in v̇_α has degree
(3-1) + 4 = 6. The NAP Splitting Feasibility theorem says every
such monomial admits a non-autocatalytic degree-3 × degree-3 split. -/

/-- A cubed index is a multi-index of weight 3. -/
def IsCubedIndex {n : ℕ} (α : Fin n → ℕ) : Prop := miWeight α = 3

/-- A production monomial for v_α is a degree-6 monomial δ arising
from the chain rule: v̇_α = Σ_{j: αⱼ>0} αⱼ (v_α/xⱼ) · fⱼ(x).

It satisfies:
  (1) |δ| = 6
  (2) There exists j ∈ supp(α) such that δ = (α - eⱼ) + μ
      where μ is a positive degree-4 monomial in fⱼ with μⱼ < 4. -/
structure ProductionMonomial {n : ℕ} (α : Fin n → ℕ) where
  /-- The exponent vector of the degree-6 monomial. -/
  δ : Fin n → ℕ
  /-- Total degree is 6. -/
  weight_eq : miWeight δ = 6
  /-- Source variable: the j such that v̇_α gets a contribution from fⱼ. -/
  source : Fin n
  /-- The source is in the support of α. -/
  source_in_supp : 0 < α source
  /-- The degree-4 monomial from the positive part of fⱼ. -/
  μ : Fin n → ℕ
  /-- μ has degree 4. -/
  μ_weight : miWeight μ = 4
  /-- δ = (α - eⱼ) + μ (the chain rule product). -/
  chain_rule : ∀ k, δ k = (α k - if k = source then 1 else 0) + μ k
  /-- The pipeline condition on μ: the self-exponent is ≤ 2.
  This is stronger than the bare 4-PP condition (< 4) and comes from the
  PP structure: after the r²-trick, the maximum self-power in positive
  terms is 2 (Proposition 2 in Note 14). The bare 4-PP condition (< 4)
  is insufficient — e.g., α = 3eⱼ with μⱼ = 3 gives δ = (5,1,0,...),
  which has no valid non-autocatalytic split. -/
  pipeline_bound : μ source ≤ 2
  /-- The r²-trick structural property: μ has weight on at least 2 distinct
  non-source variables. In the pipeline, every positive monomial contains
  the r² factor (2 units on the r-variable, which is ≠ source for non-r
  derivatives) plus at least one other non-source variable from the original
  PP polynomial. For the r-derivative, the positive terms come from
  q_j · x_j · r², giving weight on both j and the variable in q_j. -/
  foreign_pair : ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
    0 < μ i₁ ∧ 0 < μ i₂

/-! ## Exponent Redistribution Lemma

This is the algebraic heart of the proof. If α has support size ≥ 2,
then for any δ = 2α, the split β = α + eⱼ - eₖ gives a valid
non-autocatalytic factorization.

More generally: if α | δ and |supp(α)| ≥ 2, then δ has a degree-3
divisor β ≠ α with δ - β ≠ α. -/

/-- Shift one exponent unit from k to j: β(j) = α(j)+1, β(k) = α(k)-1, else β = α. -/
noncomputable def miShift {n : ℕ} (α : Fin n → ℕ) (j k : Fin n) : Fin n → ℕ :=
  fun i => if i = j then α i + 1 else if i = k then α i - 1 else α i

theorem miShift_at_j {n : ℕ} {α : Fin n → ℕ} {j k : Fin n} (_hjk : j ≠ k) :
    miShift α j k j = α j + 1 := by simp [miShift]

theorem miShift_at_k {n : ℕ} {α : Fin n → ℕ} {j k : Fin n} (hjk : j ≠ k) :
    miShift α j k k = α k - 1 := by simp only [miShift, hjk.symm, ite_false, ite_true]

theorem miShift_at_other {n : ℕ} {α : Fin n → ℕ} {j k i : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) : miShift α j k i = α i := by
  simp [miShift, hij, hik]

/-- The weight of miShift α j k equals the weight of α (when α k ≥ 1). -/
theorem miShift_weight {n : ℕ} {α : Fin n → ℕ} {j k : Fin n}
    (hk : 0 < α k) (hjk : j ≠ k) :
    miWeight (miShift α j k) = miWeight α := by
  simp only [miWeight]
  -- Extract j and k from both sums, leaving the same remainder R
  have hjk' : k ≠ j := hjk.symm
  have hj_mem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hk_mem : k ∈ (Finset.univ : Finset (Fin n)).erase j :=
    Finset.mem_erase.mpr ⟨hjk', Finset.mem_univ k⟩
  set R := ∑ i ∈ (Finset.univ.erase j).erase k, α i
  -- LHS = (α j + 1) + ((α k - 1) + R)
  have lhs : ∑ i, miShift α j k i = (α j + 1) + ((α k - 1) + R) := by
    rw [← Finset.add_sum_erase _ _ hj_mem, ← Finset.add_sum_erase _ _ hk_mem]
    rw [miShift_at_j hjk, miShift_at_k hjk]
    congr 1; congr 1
    exact Finset.sum_congr rfl fun i hi => by
      simp only [Finset.mem_erase] at hi; exact miShift_at_other hi.2.1 hi.1
  -- RHS = α j + (α k + R)
  have rhs : ∑ i, α i = α j + (α k + R) := by
    rw [← Finset.add_sum_erase _ _ hj_mem, ← Finset.add_sum_erase _ _ hk_mem]
  rw [lhs, rhs]; omega

/-- miShift α j k ≠ α when α k ≥ 1 and j ≠ k. -/
theorem miShift_ne {n : ℕ} {α : Fin n → ℕ} {j k : Fin n}
    (_hk : 0 < α k) (hjk : j ≠ k) : miShift α j k ≠ α := by
  intro h
  have := congr_fun h j
  rw [miShift_at_j hjk] at this
  omega

/-- miShift α k j ≠ α when j ≠ k (it increases α at k). -/
theorem miShift_reverse_ne {n : ℕ} {α : Fin n → ℕ} {j k : Fin n}
    (hjk : j ≠ k) : miShift α k j ≠ α := by
  intro h
  have := congr_fun h k
  rw [miShift_at_j hjk.symm] at this
  omega

/-- **Exponent Redistribution Lemma**: If α has support size ≥ 2
(witnessed by distinct j, k with αⱼ, αₖ > 0), then the monomial 2α
admits a non-autocatalytic degree-3 split.

β = miShift α j k = (α+eⱼ-eₖ), γ = miShift α k j = (α-eⱼ+eₖ).
Both have weight 3, both ≠ α, and β + γ = 2α componentwise. -/
theorem exponent_redistribution {n : ℕ} (α : Fin n → ℕ)
    (hα : miWeight α = 3)
    {j k : Fin n} (hj : 0 < α j) (hk : 0 < α k) (hjk : j ≠ k) :
    let β := miShift α j k
    let γ := miShift α k j
    -- |β| = 3
    miWeight β = 3 ∧
    -- |γ| = 3
    miWeight γ = 3 ∧
    -- β + γ = 2α
    (∀ i, β i + γ i = 2 * α i) ∧
    -- β ≠ α
    β ≠ α ∧
    -- γ ≠ α
    γ ≠ α := by
  refine ⟨?_, ?_, ?_, miShift_ne hk hjk, miShift_reverse_ne hjk⟩
  -- |β| = 3
  · rw [miShift_weight hk hjk, hα]
  -- |γ| = 3
  · rw [miShift_weight hj hjk.symm, hα]
  -- β + γ = 2α
  · intro i
    unfold miShift
    by_cases hij : i = j
    · subst hij
      simp [hjk]
      omega
    · by_cases hik : i = k
      · subst hik
        simp [hjk.symm]
        omega
      · simp [hij, hik]
        omega

/-! ## Helper: existence of non-source weight

From the pipeline bound, μ_source ≤ 2 and |μ| = 4, so at least 2 units
of μ are on non-source variables. This gives a "foreign atom" to use
in constructing non-autocatalytic splits. -/

/-- If μ has weight 4 and μ_source ≤ 2, there exists i₀ ≠ source with μ_{i₀} ≥ 1. -/
theorem exists_foreign_atom {n : ℕ} {μ : Fin n → ℕ} {source : Fin n}
    (hμ : miWeight μ = 4) (hbound : μ source ≤ 2) :
    ∃ i₀ : Fin n, i₀ ≠ source ∧ 0 < μ i₀ := by
  by_contra h
  push Not at h
  -- h : ∀ i₀, i₀ ≠ source → μ i₀ = 0  (push_neg turns ¬(0 < μ i₀) to μ i₀ ≤ 0, i.e. = 0 in ℕ)
  have hzero : ∀ i, i ≠ source → μ i = 0 := fun i hi => Nat.le_zero.mp (h i hi)
  have : ∑ i, μ i = μ source := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ source)]
    suffices ∑ x ∈ Finset.univ.erase source, μ x = 0 by omega
    exact Finset.sum_eq_zero fun i hi => hzero i (Finset.ne_of_mem_erase hi)
  rw [miWeight] at hμ; omega

/-! ## Pure-power case: |supp(α)| = 1

When α = 3·eⱼ, the split β = (2·eⱼ + e_{i₀}), γ = δ - β avoids
autocatalysis because β has weight on i₀ (so β ≠ α) and γ has
γⱼ = μⱼ ≤ 2 < 3 (so γ ≠ α). -/

/-- When |supp(α)| = 1 (pure power at source), construct a valid split.
β = 2·e_source + 1·e_{i₀}, γ = δ - β. Works because:
  - β ≠ α since β_{i₀} = 1 but α_{i₀} = 0
  - γ ≠ α since γ_source = μ_source ≤ 2 < 3 = α_source -/
theorem pure_power_split {n : ℕ} (α : Fin n → ℕ)
    (hα : IsCubedIndex α)
    (pm : ProductionMonomial α)
    (h_pure : ∀ i, i ≠ pm.source → α i = 0) :
    ∃ s : MonomialSplit pm.δ, s.balanced ∧ s.nonAutocatalytic α := by
  -- α is a pure power: α_source = 3
  have hα_source : α pm.source = 3 := by
    have hwt := hα; unfold IsCubedIndex miWeight at hwt
    have : ∑ i, α i = α pm.source := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pm.source)]
      suffices ∑ x ∈ Finset.univ.erase pm.source, α x = 0 by omega
      exact Finset.sum_eq_zero fun i hi => h_pure i (Finset.ne_of_mem_erase hi)
    linarith
  -- Get a foreign atom i₀ ≠ source with μ_{i₀} ≥ 1
  obtain ⟨i₀, hi₀_ne, hi₀_pos⟩ := exists_foreign_atom pm.μ_weight pm.pipeline_bound
  -- δ_{i₀} ≥ 1 (from chain rule + h_pure)
  have hδi₀ : 1 ≤ pm.δ i₀ := by
    rw [pm.chain_rule i₀]; simp [hi₀_ne]; omega
  -- δ_source ≥ 2 (from chain rule: 3 - 1 + μ_source ≥ 2)
  have hδs : 2 ≤ pm.δ pm.source := by
    rw [pm.chain_rule pm.source]; simp; omega
  -- Define β: 2 on source, 1 on i₀, 0 elsewhere
  set β : Fin n → ℕ := fun i => if i = pm.source then 2 else if i = i₀ then 1 else 0
  -- Key values
  have hβ_s : β pm.source = 2 := if_pos rfl
  have hβ_i₀ : β i₀ = 1 := by simp [β, hi₀_ne]
  have hβ_other : ∀ i, i ≠ pm.source → i ≠ i₀ → β i = 0 :=
    fun i h1 h2 => by simp only [β, if_neg h1, if_neg h2]
  -- β ≤ δ
  have hβ_le : ∀ i, β i ≤ pm.δ i := by
    intro i
    by_cases hs : i = pm.source
    · rw [hs, hβ_s]; exact hδs
    · by_cases hi : i = i₀
      · rw [hi, hβ_i₀]; exact hδi₀
      · rw [hβ_other i hs hi]; exact Nat.zero_le _
  -- |β| = 3 (via extract j, k from sum)
  have hβ_wt : miWeight β = 3 := by
    simp only [miWeight]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pm.source), hβ_s]
    rw [← Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨hi₀_ne, Finset.mem_univ i₀⟩), hβ_i₀]
    suffices ∑ x ∈ (Finset.univ.erase pm.source).erase i₀, β x = 0 by omega
    exact Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_erase] at hi; exact hβ_other i hi.2.1 hi.1
  -- |γ| = 3 (weight of δ - β = 6 - 3)
  have hγ_wt : miWeight (fun i => pm.δ i - β i) = 3 := by
    simp only [miWeight]
    have key : ∑ i : Fin n, (β i + (pm.δ i - β i)) = ∑ i, pm.δ i :=
      Finset.sum_congr rfl fun i _ => Nat.add_sub_of_le (hβ_le i)
    rw [Finset.sum_add_distrib] at key
    have h1 : ∑ i : Fin n, β i = 3 := hβ_wt
    have h2 : ∑ i : Fin n, pm.δ i = 6 := pm.weight_eq
    omega
  -- Construct the split
  refine ⟨⟨β, fun i => pm.δ i - β i, fun i => Nat.add_sub_of_le (hβ_le i)⟩,
    ⟨hβ_wt, hγ_wt⟩, ?_, ?_⟩
  · -- β ≠ α: β_{i₀} = 1 but α_{i₀} = 0
    intro h
    have hv := congr_fun h i₀
    dsimp at hv
    rw [hβ_i₀, h_pure i₀ hi₀_ne] at hv
    exact absurd hv (by omega)
  · -- γ ≠ α: γ_source = δ_source - 2 = μ_source ≤ 2 < 3 = α_source
    intro h
    have hval : pm.δ pm.source - β pm.source = α pm.source := by
      have := congr_fun h pm.source; dsimp at this; exact this
    rw [hβ_s, hα_source] at hval
    have hδ_s : pm.δ pm.source = 2 + pm.μ pm.source := by
      have h := pm.chain_rule pm.source
      simp only [ite_true] at h; rw [hα_source] at h; omega
    rw [hδ_s] at hval
    -- hval : 2 + μ_source - 2 = 3, i.e. μ_source = 3
    have := pm.pipeline_bound; omega

/-! ## Mixed support case: |supp(α)| ≥ 2

When α has support on at least two variables (source and k), the proof
constructs β = miShift α i₀ source (primary) or β = miShift α i₀ k
(backup), where i₀ is a foreign atom of μ.

Key insight: if the primary split has γ₁ = α, then μ_source = α_source,
and the backup's γ₂ at source equals α_source - 1 ≠ α_source.
The two failures are contradictory, so at least one split works. -/

/-- Helper: construct a balanced split from β ≤ δ with |β| = 3, |δ| = 6. -/
private theorem balanced_of_le {n : ℕ} {δ : Fin n → ℕ} {β : Fin n → ℕ}
    (hle : ∀ i, β i ≤ δ i) (hβ : miWeight β = 3) (hδ : miWeight δ = 6) :
    miWeight (fun i => δ i - β i) = 3 := by
  simp only [miWeight]
  have key : ∑ i : Fin n, (β i + (δ i - β i)) = ∑ i, δ i :=
    Finset.sum_congr rfl fun i _ => Nat.add_sub_of_le (hle i)
  rw [Finset.sum_add_distrib] at key
  have h1 : ∑ i : Fin n, β i = 3 := hβ
  have h2 : ∑ i : Fin n, δ i = 6 := hδ
  omega

/-- Mixed support case: k ∈ supp(α) with k ≠ source. -/
theorem mixed_support_split {n : ℕ} (α : Fin n → ℕ)
    (hα : IsCubedIndex α)
    (pm : ProductionMonomial α)
    (k : Fin n) (hk_ne : k ≠ pm.source) (hk_supp : 0 < α k) :
    ∃ s : MonomialSplit pm.δ, s.balanced ∧ s.nonAutocatalytic α := by
  -- Foreign atoms: i₁ ≠ i₂, both ≠ source, μ positive at both
  obtain ⟨i₁, i₂, hi₁₂, hi₁_ne, hi₂_ne, hμ₁, hμ₂⟩ := pm.foreign_pair
  -- Choose i₀ ∈ {i₁, i₂} with i₀ ≠ k
  obtain ⟨i₀, hi₀_ne_s, hμ₀, hi₀_ne_k⟩ : ∃ i₀, i₀ ≠ pm.source ∧ 0 < pm.μ i₀ ∧ i₀ ≠ k := by
    by_cases h : i₁ = k
    · exact ⟨i₂, hi₂_ne, hμ₂, fun h2 => hi₁₂ (h.trans h2.symm)⟩
    · exact ⟨i₁, hi₁_ne, hμ₁, h⟩
  -- Chain rule simplified forms
  have hcr_s : pm.δ pm.source = α pm.source - 1 + pm.μ pm.source := by
    have := pm.chain_rule pm.source; simp only [ite_true] at this; exact this
  have hcr_ne : ∀ i, i ≠ pm.source → pm.δ i = α i + pm.μ i := by
    intro i hi; have := pm.chain_rule i; simp only [if_neg hi, Nat.sub_zero] at this; exact this
  -- Primary β₁ ≤ δ (using miShift directly, no `set`)
  have hβ₁_le : ∀ i, miShift α i₀ pm.source i ≤ pm.δ i := by
    intro i
    by_cases h1 : i = i₀
    · subst h1; rw [miShift_at_j hi₀_ne_s, hcr_ne _ hi₀_ne_s]; omega
    · by_cases h2 : i = pm.source
      · subst h2; rw [miShift_at_k hi₀_ne_s, hcr_s]; omega
      · rw [miShift_at_other h1 h2, hcr_ne _ h2]; omega
  have hβ₁_wt : miWeight (miShift α i₀ pm.source) = 3 :=
    (miShift_weight pm.source_in_supp hi₀_ne_s).trans hα
  -- Case split on whether the primary γ equals α pointwise
  by_cases hγ₁ : ∀ i, pm.δ i - miShift α i₀ pm.source i = α i
  · -- **Backup**: γ₁ = α at every coordinate → μ_source = α_source
    have hμs_eq : pm.μ pm.source = α pm.source := by
      have := hγ₁ pm.source; rw [miShift_at_k hi₀_ne_s, hcr_s] at this; omega
    -- Backup β₂ ≤ δ
    have hβ₂_le : ∀ i, miShift α i₀ k i ≤ pm.δ i := by
      intro i
      by_cases h1 : i = i₀
      · subst h1; rw [miShift_at_j hi₀_ne_k, hcr_ne _ hi₀_ne_s]; omega
      · by_cases h2 : i = k
        · subst h2; rw [miShift_at_k hi₀_ne_k, hcr_ne _ hk_ne]; omega
        · rw [miShift_at_other h1 h2]
          by_cases h3 : i = pm.source
          · subst h3; rw [hcr_s, hμs_eq]; omega
          · rw [hcr_ne _ h3]; omega
    have hβ₂_wt : miWeight (miShift α i₀ k) = 3 :=
      (miShift_weight hk_supp hi₀_ne_k).trans hα
    -- γ₂ at source: (α_s - 1 + α_s) - α_s = α_s - 1 ≠ α_s (since α_s ≥ 1)
    have hγ₂_ne : ¬∀ i, pm.δ i - miShift α i₀ k i = α i := by
      intro h; have := h pm.source
      rw [miShift_at_other (Ne.symm hi₀_ne_s) (Ne.symm hk_ne), hcr_s, hμs_eq] at this
      have := pm.source_in_supp; omega
    refine ⟨⟨miShift α i₀ k, fun i => pm.δ i - miShift α i₀ k i,
      fun i => Nat.add_sub_of_le (hβ₂_le i)⟩,
      ⟨hβ₂_wt, balanced_of_le hβ₂_le hβ₂_wt pm.weight_eq⟩, ?_, ?_⟩
    · intro h; exact absurd (by dsimp at h; exact h) (miShift_ne hk_supp hi₀_ne_k)
    · intro h; exact hγ₂_ne (fun i => by have := congr_fun h i; dsimp at this; exact this)
  · -- **Primary**: γ₁ ≠ α
    refine ⟨⟨miShift α i₀ pm.source, fun i => pm.δ i - miShift α i₀ pm.source i,
      fun i => Nat.add_sub_of_le (hβ₁_le i)⟩,
      ⟨hβ₁_wt, balanced_of_le hβ₁_le hβ₁_wt pm.weight_eq⟩, ?_, ?_⟩
    · intro h; exact absurd (by dsimp at h; exact h) (miShift_ne pm.source_in_supp hi₀_ne_s)
    · intro h; exact hγ₁ (fun i => by have := congr_fun h i; dsimp at this; exact this)

/-! ## NAP Splitting Feasibility — Main Theorem

Every positive degree-6 monomial in v̇_α admits a factorization
m_δ = m_β · m_γ with |β| = |γ| = 3, β ≠ α, γ ≠ α.

The proof splits into two cases:
  Case 1 (pure power): |supp(α)| = 1 → use pure_power_split
  Case 2 (mixed): |supp(α)| ≥ 2 → use mixed_support_split -/

/-- **NAP Splitting Feasibility** (Theorem 1 in Note 14):
For any cubed variable v_α (|α| = 3) and any production monomial δ
arising from the chain rule of a 4-PP, there exists a balanced
non-autocatalytic split of δ. -/
theorem nap_splitting_feasibility {n : ℕ} (α : Fin n → ℕ)
    (hα : IsCubedIndex α)
    (pm : ProductionMonomial α) :
    ∃ s : MonomialSplit pm.δ, s.balanced ∧ s.nonAutocatalytic α := by
  -- Does α have support beyond the source variable?
  by_cases h : ∃ k, k ≠ pm.source ∧ 0 < α k
  · obtain ⟨k, hk_ne, hk_supp⟩ := h
    exact mixed_support_split α hα pm k hk_ne hk_supp
  · push Not at h
    exact pure_power_split α hα pm (fun i hi => Nat.le_zero.mp (h i hi))

/-! ## Trivial Non-Autocatalytic Split

When the source exponent in δ is strictly less than in α, EVERY balanced
split is automatically non-autocatalytic. This handles the case where
the production monomial μ has μ_source = 0 (from PP no-self-production):
  δ_source = α_source - 1 + 0 = α_source - 1 < α_source
so any β with β_source ≤ δ_source < α_source gives β ≠ α, and similarly
γ_source = δ_source - β_source ≤ α_source - 1 < α_source gives γ ≠ α. -/

/-- When δ_source < α_source, any split β + γ = δ with β ≤ δ has
β ≠ α and γ ≠ α (both factors differ from α at the source coordinate). -/
theorem trivial_split_of_lt {n : ℕ} {α δ : Fin n → ℕ} {source : Fin n}
    (hlt : δ source < α source)
    (β : Fin n → ℕ) (hle : ∀ i, β i ≤ δ i) :
    β ≠ α ∧ (fun i => δ i - β i) ≠ α := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- β = α would give α source ≤ δ source, contradicting hlt
    rw [h] at hle; exact absurd (hle source) (not_le.mpr hlt)
  · -- (δ - β) = α at source: δ_s - β_s = α_s, but δ_s - β_s ≤ δ_s < α_s
    have h1 : ∀ i, δ i - β i = α i := fun i => congr_fun h i
    have h2 := h1 source
    have h3 := hle source
    omega

/-- Any multi-index of weight ≥ k has a divisor of weight exactly k.
This is a standard combinatorial fact: a "greedy fill" works. -/
private theorem exists_weight_divisor {n : ℕ} :
    ∀ (k : ℕ) (δ : Fin n → ℕ), k ≤ miWeight δ →
    ∃ β : Fin n → ℕ, miWeight β = k ∧ ∀ i, β i ≤ δ i := by
  intro k; induction k with
  | zero => intro _ _; exact ⟨fun _ => 0, by simp [miWeight], fun _ => Nat.zero_le _⟩
  | succ k ih =>
    intro δ hk
    -- |δ| ≥ 1, so ∃ i with δ_i ≥ 1
    have ⟨i, hi_pos⟩ : ∃ i, 0 < δ i := by
      by_contra h; push Not at h
      have : ∀ j, δ j = 0 := fun j => Nat.le_zero.mp (h j)
      simp [miWeight, this] at hk
    -- Let δ' = δ - e_i. Then |δ'| = |δ| - 1 ≥ k.
    set δ' := fun j => if j = i then δ j - 1 else δ j with hδ'_def
    have hδ'_wt : miWeight δ' = miWeight δ - 1 := by
      simp only [miWeight, hδ'_def]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true]
      rw [show ∑ x ∈ Finset.univ.erase i, (if x = i then δ x - 1 else δ x) =
        ∑ x ∈ Finset.univ.erase i, δ x from
        Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]]
      have : δ i + ∑ x ∈ Finset.univ.erase i, δ x = ∑ x, δ x :=
        Finset.add_sum_erase Finset.univ (fun x => δ x) (Finset.mem_univ i)
      omega
    obtain ⟨β', hβ'_wt, hβ'_le⟩ := ih δ' (by omega)
    -- β = β' + e_i
    refine ⟨fun j => β' j + if j = i then 1 else 0, ?_, ?_⟩
    · simp only [miWeight]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [ite_true]
      rw [show ∑ x ∈ Finset.univ.erase i,
        ((fun j => β' j + if j = i then 1 else 0) x) =
        ∑ x ∈ Finset.univ.erase i, β' x from
        Finset.sum_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]]
      simp only [miWeight] at hβ'_wt
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hβ'_wt
      omega
    · intro j
      by_cases hj : j = i
      · subst hj
        have h1 := hβ'_le j
        simp only [hδ'_def, ite_true] at h1
        simp only [ite_true]; omega
      · simp only [if_neg hj, add_zero]
        have h1 := hβ'_le j
        simp only [hδ'_def, if_neg hj] at h1
        exact h1

/-- When δ_source < α_source and |δ| = 6, there exists a balanced
non-autocatalytic split. The split is "trivial" because ANY weight-3
divisor of δ gives β ≠ α and γ ≠ α (both factors must have
source-exponent ≤ δ_source < α_source). -/
theorem trivial_balanced_split {n : ℕ} (α δ : Fin n → ℕ)
    (hδ : miWeight δ = 6) (source : Fin n)
    (hlt : δ source < α source) :
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  obtain ⟨β, hβ_wt, hβ_le⟩ := exists_weight_divisor 3 δ (by omega)
  refine ⟨⟨β, fun i => δ i - β i, fun i => Nat.add_sub_of_le (hβ_le i)⟩,
    ⟨hβ_wt, balanced_of_le hβ_le hβ_wt hδ⟩, ?_⟩
  exact trivial_split_of_lt hlt β hβ_le

/-- Canonical split for a negative chain-rule term.

If a degree-6 monomial `δ` contains `α` as a degree-3 divisor, then the CRN
negative rewriting is forced: the first factor is `α`, and the second factor is
the residual exponent vector `δ - α`. This is the formal `demand` node in the
flow-network view of `PP -> NAP`. -/
theorem negative_split_canonical {n : ℕ} (α δ : Fin n → ℕ)
    (hα : IsCubedIndex α) (hδ : miWeight δ = 6)
    (hdiv : miDvd α δ) :
    ∃ s : MonomialSplit δ,
      s.β = α ∧
      s.γ = (fun i => δ i - α i) ∧
      s.balanced := by
  refine ⟨⟨α, (fun i => δ i - α i), fun i => Nat.add_sub_of_le (hdiv i)⟩, rfl, rfl, ?_⟩
  exact ⟨hα, balanced_of_le hdiv hα hδ⟩

/-- Uniqueness of the CRN-determined negative split once the left factor is fixed to `α`. -/
theorem negative_split_unique {n : ℕ} {α δ : Fin n → ℕ}
    {s : MonomialSplit δ}
    (hβ : s.β = α) :
    s.γ = (fun i => δ i - α i) := by
  funext i
  have hs : α i + s.γ i = δ i := by simpa [hβ] using s.sum_eq i
  omega

/-! ## Structural Chain: PP → 4-PP → NAP

The three-step causal chain:
  PP (x_j ∤ p_j) →[r²-trick] 4-PP →[cubing] NAP

The PP **no-self-production** condition: for each species j, the
production polynomial p_j is not divisible by x_j. This means x_j
does not appear at all in p_j — not even x_j · x_k.

After the r²-trick (multiply all derivatives by r²):
- For source j: μ = (degree-2 monomial from p_j) · r².
  Since x_j ∤ p_j, every monomial has μ_j = 0.

Two cases for each production monomial:
1. **foreign_pair holds** (μ has ≥2 distinct non-source positive variables):
   Apply nap_splitting_feasibility via ProductionMonomial.
2. **foreign_pair fails** (μ concentrated on one non-source variable):
   μ_source = 0, so δ_source = α_source - 1 < α_source.
   Any balanced split is automatically non-autocatalytic. -/

/-- The degree-4 monomial created by the `r²`-trick from a quadratic PP
production monomial `x_a x_b`: two units on the slack variable `zero`, plus
one unit on each of `a` and `b`. -/
def r2PPMonomial {n : ℕ} (zero a b : Fin n) : Fin n → ℕ :=
  fun i => (if i = zero then 2 else 0) + (if i = a then 1 else 0) + (if i = b then 1 else 0)

theorem r2PPMonomial_weight {n : ℕ} {zero a b : Fin n}
    (hza : a ≠ zero) (hzb : b ≠ zero) :
    miWeight (r2PPMonomial zero a b) = 4 := by
  unfold miWeight r2PPMonomial
  have hsum0 : ∑ x : Fin n, (if x = zero then 2 else 0) = 2 := by
    simp
  have hsuma : ∑ x : Fin n, (if x = a then 1 else 0) = 1 := by
    simp
  have hsumb : ∑ x : Fin n, (if x = b then 1 else 0) = 1 := by
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum0, hsuma, hsumb]

theorem r2PPMonomial_source_eq_zero {n : ℕ} {zero a b source : Fin n}
    (h0s : zero ≠ source) (has : a ≠ source) (hbs : b ≠ source) :
    r2PPMonomial zero a b source = 0 := by
  have hz : source ≠ zero := h0s.symm
  have ha : source ≠ a := has.symm
  have hb : source ≠ b := hbs.symm
  simp [r2PPMonomial, hz, ha, hb]

theorem r2PPMonomial_foreign_pair {n : ℕ} {zero a b source : Fin n}
    (h0s : zero ≠ source) (hza : a ≠ zero)
    (has : a ≠ source) :
    ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
      0 < r2PPMonomial zero a b i₁ ∧ 0 < r2PPMonomial zero a b i₂ := by
  refine ⟨zero, a, hza.symm, h0s, has, ?_, ?_⟩
  · simp [r2PPMonomial]
  · by_cases hab : a = b
    · simp [r2PPMonomial, hza, hab]
    · simp [r2PPMonomial, hza, hab]

theorem r2PPMonomial_foreign_pair_at_zero {n : ℕ} {zero a b : Fin n}
    (hza : a ≠ zero) (hzb : b ≠ zero) (hab : a ≠ b) :
    ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ zero ∧ i₂ ≠ zero ∧
      0 < r2PPMonomial zero a b i₁ ∧ 0 < r2PPMonomial zero a b i₂ := by
  refine ⟨a, b, hab, hza, hzb, ?_, ?_⟩
  · simp [r2PPMonomial, hza, hab]
  · simp [r2PPMonomial, hzb, hab.symm]

private theorem chain_rule_weight_six {n : ℕ} {α μ : Fin n → ℕ} {source : Fin n}
    (hα : IsCubedIndex α) (hμ : miWeight μ = 4) (hsrc : 0 < α source) :
    miWeight (fun k => (α k - if k = source then 1 else 0) + μ k) = 6 := by
  unfold IsCubedIndex at hα
  unfold miWeight at hμ ⊢
  rw [Finset.sum_add_distrib]
  have hs :
      ∑ k : Fin n, (α k - if k = source then 1 else 0) = 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ source)]
    simp only [ite_true]
    rw [show ∑ x ∈ Finset.univ.erase source, (α x - if x = source then 1 else 0) =
      ∑ x ∈ Finset.univ.erase source, α x by
      exact Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]]
    have hdecomp :
        α source + ∑ x ∈ Finset.univ.erase source, α x = 3 := by
      have hdecomp0 :
          α source + ∑ x ∈ Finset.univ.erase source, α x = ∑ x : Fin n, α x :=
        Finset.add_sum_erase Finset.univ (fun x : Fin n => α x) (Finset.mem_univ source)
      calc
        α source + ∑ x ∈ Finset.univ.erase source, α x = ∑ x : Fin n, α x := hdecomp0
        _ = 3 := hα
    omega
  omega

/-- Direct `PP -> x_0² -> cubing` theorem for a nonzero source variable.

If a positive quadratic PP monomial `x_a x_b` appears in the production field
for `source`, then after multiplying by `x_zero²` the resulting degree-4
monomial automatically satisfies the strong hypotheses needed for the cubing
split theorem: the source exponent is `0`, and there are two distinct positive
non-source coordinates (`zero` and `a`). -/
theorem pp_r2_nonzero_source_split {n : ℕ}
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (zero source a b : Fin n)
    (hsrc : 0 < α source)
    (h0s : zero ≠ source) (hza : a ≠ zero) (hzb : b ≠ zero)
    (has : a ≠ source) (hbs : b ≠ source) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  dsimp
  have hμ : miWeight (r2PPMonomial zero a b) = 4 := r2PPMonomial_weight hza hzb
  have hδ :
      miWeight (fun k => (α k - if k = source then 1 else 0) + r2PPMonomial zero a b k) = 6 :=
    chain_rule_weight_six hα hμ hsrc
  have hμs : r2PPMonomial zero a b source = 0 :=
    r2PPMonomial_source_eq_zero h0s has hbs
  have hfp :
      ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
        0 < r2PPMonomial zero a b i₁ ∧ 0 < r2PPMonomial zero a b i₂ :=
    r2PPMonomial_foreign_pair h0s hza has
  exact nap_splitting_feasibility α hα
    ⟨_, hδ, source, hsrc, _, hμ, (fun k => rfl), by simpa [hμs], hfp⟩

/-- Direct `PP -> x_0² -> cubing` theorem for the slack variable itself,
in the generic case where the residual quadratic monomial uses two distinct
nonzero variables. Then the non-source support is visibly spread over `a` and
`b`, so the cubing split theorem applies directly. -/
theorem pp_r2_zero_source_split_distinct {n : ℕ}
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (zero a b : Fin n)
    (hsrc : 0 < α zero)
    (hza : a ≠ zero) (hzb : b ≠ zero) (hab : a ≠ b) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = zero then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  dsimp
  have hμ : miWeight (r2PPMonomial zero a b) = 4 := r2PPMonomial_weight hza hzb
  have hδ :
      miWeight (fun k => (α k - if k = zero then 1 else 0) + r2PPMonomial zero a b k) = 6 :=
    chain_rule_weight_six hα hμ hsrc
  have hfp :
      ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ zero ∧ i₂ ≠ zero ∧
        0 < r2PPMonomial zero a b i₁ ∧ 0 < r2PPMonomial zero a b i₂ :=
    r2PPMonomial_foreign_pair_at_zero hza hzb hab
  exact nap_splitting_feasibility α hα
    ⟨_, hδ, zero, hsrc, _, hμ, (fun k => rfl), by
      simp [r2PPMonomial, hza.symm, hzb.symm], hfp⟩

/-- Direct `PP -> x_0² -> cubing` theorem for the slack variable itself in the
repeated-variable case `x_0² x_a²`. The generic split is
`(2e_0 + e_a) + (α - e_0 + e_a)`, except for the single exceptional shape
`α = 2e_0 + e_a`, where we instead use `3e_0 + 3e_a`. -/
theorem pp_r2_zero_source_split_doubled {n : ℕ}
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (zero a : Fin n)
    (hsrc : 0 < α zero)
    (hza : a ≠ zero) :
    let μ := r2PPMonomial zero a a
    let δ := fun k => (α k - if k = zero then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  dsimp
  let β0 : Fin n → ℕ := fun i => if i = zero then 2 else if i = a then 1 else 0
  by_cases hspecial : α = β0
  · let β : Fin n → ℕ := fun i => if i = zero then 3 else 0
    let γ : Fin n → ℕ := fun i => if i = a then 3 else 0
    have hαzero : α zero = 2 := by
      simpa [β0] using congr_fun hspecial zero
    have hαa : α a = 1 := by
      simpa [β0, hza] using congr_fun hspecial a
    have hsum : ∀ i, β i + γ i =
        (fun k => (α k - if k = zero then 1 else 0) + r2PPMonomial zero a a k) i := by
      intro i
      by_cases hiz : i = zero
      · subst hiz
        simp [β, γ, r2PPMonomial, hza.symm, hαzero]
      · by_cases hia : i = a
        · subst hia
          simp [β, γ, r2PPMonomial, hza, hαa]
        · simp [β, γ, r2PPMonomial, hiz, hia]
          have hαi : α i = 0 := by
            simpa [β0, hiz, hia] using congr_fun hspecial i
          simp [hαi]
    have hβ_wt : miWeight β = 3 := by
      unfold miWeight β
      simp
    have hγ_wt : miWeight γ = 3 := by
      unfold miWeight γ
      simp
    refine ⟨⟨β, γ, hsum⟩, ⟨hβ_wt, hγ_wt⟩, ?_⟩
    constructor
    · intro h
      have hzero : β zero = α zero := congr_fun h zero
      simp [β, hαzero] at hzero
    · intro h
      have hzero : γ zero = α zero := congr_fun h zero
      have : (0 : ℕ) = 2 := by simpa [γ, hza.symm, hαzero] using hzero
      omega
  · let γ : Fin n → ℕ := fun i => (α i - if i = zero then 1 else 0) + (if i = a then 1 else 0)
    have hsum : ∀ i, β0 i + γ i =
        (fun k => (α k - if k = zero then 1 else 0) + r2PPMonomial zero a a k) i := by
      intro i
      by_cases hiz : i = zero
      · subst hiz
        simp [β0, γ, r2PPMonomial, hza.symm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · by_cases hia : i = a
        · subst hia
          simp [β0, γ, r2PPMonomial, hza, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        · simp [β0, γ, r2PPMonomial, hiz, hia]
    have hβ_le : ∀ i, β0 i ≤ (fun k => (α k - if k = zero then 1 else 0) + r2PPMonomial zero a a k) i := by
      intro i
      by_cases hiz : i = zero
      · subst hiz
        simp [β0, r2PPMonomial, hza.symm]
      · by_cases hia : i = a
        · subst hia
          simp [β0, r2PPMonomial, hza]
        · simp [β0, r2PPMonomial, hiz, hia]
    have hβ_wt : miWeight β0 = 3 := by
      unfold miWeight β0
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ zero)]
      simp [hza]
      rw [Finset.sum_eq_single a]
      · simp [hza]
      · intro i hi hia
        have hiz : i ≠ zero := Finset.ne_of_mem_erase hi
        simp [hia, hiz]
      · intro ha
        exact False.elim (ha (Finset.mem_erase.mpr ⟨hza, Finset.mem_univ _⟩))
    have hδ_wt :
        miWeight (fun k => (α k - if k = zero then 1 else 0) + r2PPMonomial zero a a k) = 6 := by
      have hμ : miWeight (r2PPMonomial zero a a) = 4 := r2PPMonomial_weight hza hza
      exact chain_rule_weight_six hα hμ hsrc
    have hγ_wt : miWeight γ = 3 := by
      unfold miWeight γ
      rw [Finset.sum_add_distrib]
      have hs :
          ∑ i : Fin n, (α i - if i = zero then 1 else 0) = 2 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ zero)]
        simp only [ite_true]
        rw [show ∑ x ∈ Finset.univ.erase zero, (α x - if x = zero then 1 else 0) =
          ∑ x ∈ Finset.univ.erase zero, α x by
          exact Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]]
        have hdecomp0 :
            α zero + ∑ x ∈ Finset.univ.erase zero, α x = ∑ x : Fin n, α x :=
          Finset.add_sum_erase Finset.univ (fun x : Fin n => α x) (Finset.mem_univ zero)
        have hdecomp :
            α zero + ∑ x ∈ Finset.univ.erase zero, α x = 3 := by
          calc
            α zero + ∑ x ∈ Finset.univ.erase zero, α x = ∑ x : Fin n, α x := hdecomp0
            _ = 3 := hα
        omega
      have ha : ∑ i : Fin n, (if i = a then 1 else 0) = 1 := by simp
      rw [hs, ha]
    refine ⟨⟨β0, γ, hsum⟩, ⟨hβ_wt, hγ_wt⟩, ?_⟩
    constructor
    · intro h
      exact hspecial (by
        funext i
        exact (congr_fun h i).symm)
    · intro h
      have hzero : γ zero = α zero := congr_fun h zero
      simp [γ, hza.symm] at hzero
      omega

/-- Unified direct `PP -> x_0² -> cubing` split theorem for one quadratic
production monomial `x_a x_b`.

This is the actual monomial-level statement for the direct pipeline:
after multiplying by `x_zero²`, every chain-rule production monomial from
`x_a x_b` admits a balanced non-autocatalytic split. The proof dispatches
exactly the three real cases:
`source ≠ zero`, `source = zero ∧ a ≠ b`, and `source = zero ∧ a = b`. -/
theorem pp_r2_split {n : ℕ}
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (zero source a b : Fin n)
    (hsrc : 0 < α source)
    (hza : a ≠ zero) (hzb : b ≠ zero)
    (hcase : source = zero ∨ (a ≠ source ∧ b ≠ source)) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  by_cases hse : source = zero
  · subst hse
    by_cases hab : a = b
    · subst hab
      exact pp_r2_zero_source_split_doubled α hα source a hsrc hza
    · exact pp_r2_zero_source_split_distinct α hα source a b hsrc hza hzb hab
  · rcases hcase with hcase | ⟨has, hbs⟩
    · exact (hse hcase).elim
    · exact pp_r2_nonzero_source_split α hα zero source a b hsrc
        (Ne.symm hse) hza hzb has hbs

/-- A direct cubed production monomial arising from the `PP -> x_0² -> cubing`
pipeline, tracked all the way down to a single original quadratic PP monomial
`x_a x_b` in the source equation. The side condition `source = zero ∨
(a ≠ source ∧ b ≠ source)` is exactly the structural PP invariant needed for
the direct proof: either the source is the slack variable, or the original PP
monomial avoids the source variable. -/
structure CubedDirectPPMonomial {n : ℕ} where
  α : Fin n → ℕ
  α_cubed : IsCubedIndex α
  zero : Fin n
  source : Fin n
  source_in_supp : 0 < α source
  a : Fin n
  b : Fin n
  a_ne_zero : a ≠ zero
  b_ne_zero : b ≠ zero
  source_case : source = zero ∨ (a ≠ source ∧ b ≠ source)

/-- Protocol-level direct `PP -> x_0² -> cubing -> NAP` theorem for one
production monomial coming from a quadratic PP monomial `x_a x_b`. -/
theorem cubed_direct_pp_nap {n : ℕ} (m : @CubedDirectPPMonomial n) :
    let μ := r2PPMonomial m.zero m.a m.b
    let δ := fun k => (m.α k - if k = m.source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic m.α :=
  pp_r2_split m.α m.α_cubed m.zero m.source m.a m.b
    m.source_in_supp m.a_ne_zero m.b_ne_zero m.source_case

/-- The degree-4 monomial on the PP side of a direct `x_0^2` lift. -/
def directCubedMu {n : ℕ} (m : @CubedDirectPPMonomial n) : Fin n → ℕ :=
  r2PPMonomial m.zero m.a m.b

/-- The degree-6 chain-rule monomial produced from a direct cubed PP monomial. -/
def directCubedDelta {n : ℕ} (m : @CubedDirectPPMonomial n) : Fin n → ℕ :=
  fun k => (m.α k - if k = m.source then 1 else 0) + directCubedMu m k

/-- A canonical split witness for a direct cubed PP monomial. -/
noncomputable def directCubedSplit {n : ℕ} (m : @CubedDirectPPMonomial n) :
    MonomialSplit (directCubedDelta m) :=
  Classical.choose (show ∃ s : MonomialSplit (directCubedDelta m),
    s.balanced ∧ s.nonAutocatalytic m.α from by
      simpa [directCubedDelta, directCubedMu] using cubed_direct_pp_nap m)

theorem directCubedSplit_balanced {n : ℕ} (m : @CubedDirectPPMonomial n) :
    (directCubedSplit m).balanced := by
  exact (Classical.choose_spec
    (show ∃ s : MonomialSplit (directCubedDelta m),
      s.balanced ∧ s.nonAutocatalytic m.α from by
        simpa [directCubedDelta, directCubedMu] using cubed_direct_pp_nap m)).1

theorem directCubedSplit_nonAutocatalytic {n : ℕ} (m : @CubedDirectPPMonomial n) :
    (directCubedSplit m).nonAutocatalytic m.α := by
  exact (Classical.choose_spec
    (show ∃ s : MonomialSplit (directCubedDelta m),
      s.balanced ∧ s.nonAutocatalytic m.α from by
        simpa [directCubedDelta, directCubedMu] using cubed_direct_pp_nap m)).2

/-- A direct cubed PP monomial can be routed into a single NAP interaction with
the notebook's balancing rate `coeff / (c_β c_γ)`, and this routed interaction
reconstructs the original monomial exactly. -/
theorem cubed_direct_pp_nap_with_rate {n : ℕ} (m : @CubedDirectPPMonomial n)
    (coeff : ℚ) (x : Fin n → ℝ) :
    let μ := r2PPMonomial m.zero m.a m.b
    let δ := fun k => (m.α k - if k = m.source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ,
      s.balanced ∧
      s.nonAutocatalytic m.α ∧
      (splitRate coeff s : ℝ) * cubedLift s.β x * cubedLift s.γ x =
        (coeff : ℝ) * rawMonomial δ x := by
  dsimp
  obtain ⟨s, hs_bal, hs_nap⟩ := cubed_direct_pp_nap m
  refine ⟨s, hs_bal, hs_nap, ?_⟩
  exact splitRate_reconstructs coeff s x

/-- Finite families of direct cubed PP monomials can be routed simultaneously:
choosing one split per monomial and summing the routed interactions reconstructs
the entire finite sum exactly. This is the first formal "whole polynomial"
balancing step toward PP -> NAP. -/
theorem finite_sum_cubed_direct_pp_with_rate {ι n : ℕ} [DecidableEq (Fin ι)]
    (S : Finset (Fin ι)) (m : Fin ι → @CubedDirectPPMonomial n)
    (coeff : Fin ι → ℚ) (x : Fin n → ℝ) :
    (Finset.sum S fun t =>
      (splitRate (coeff t) (directCubedSplit (m t)) : ℝ) *
        cubedLift (directCubedSplit (m t)).β x *
        cubedLift (directCubedSplit (m t)).γ x)
      =
    (Finset.sum S fun t => (coeff t : ℝ) * rawMonomial (directCubedDelta (m t)) x) := by
  refine Finset.sum_congr rfl ?_
  intro t ht
  exact splitRate_reconstructs (coeff t) (directCubedSplit (m t)) x


/-! ## Connection to Stage 3 Self-Product

The self-product z-PP (from Stage2CubicForm, see Stages.lean) has the field:
  z'_{(i,j)} = prod_{(i,j)} - degr_{(i,j)}

**Analysis of self-production in the z-PP:**

* **Case 1 (i,j ≠ 0)**: production = z(0,j)·Pz_i + z(0,i)·Pz_j.
  z_{(i,j)} appears only via A(i,i,j) or A(j,i,j). Both vanish under strict
  no-self-production (A(i,i,·) = 0 and A(j,·,j) = 0). **μ_source = 0 ✓**

* **Case 2a (i=0, j≠0)**: production includes colCoupling_j = Σ_{k≠0} z(k,j)·x0Qz_k.
  When x0Qz_k has a z(0,j) term (B(k,j)·z(0,j)), the monomial z(k,j)·z(0,j)
  contains the source variable z(0,j). **μ_source = 1**, but pipeline_bound (≤ 2)
  and foreign_pair (r + z(k,j)) both hold. ✓

* **Case 2b (i≠0, j=0)**: symmetric to 2a via rowCoupling. ✓

* **Case 3 (i=j=0)**: production = 2·z(0,0)·totalQxz, every monomial has z(0,0)
  as a factor. **μ_source = 1**, with foreign_pair (r + z(a,k) for k≠0). ✓

**Conclusion:** `nap_split_comprehensive` covers ALL production monomials of the
cubed self-product PP. The self-product preserves strict no-self-production for
interior variables (Case 1) and satisfies the weaker comprehensive criterion for
boundary variables (Cases 2, 3). -/

/-- Stage 3 self-product, Case 1: interior variables preserve no-self-production.

For an interior variable `ij` with `ij.1, ij.2 ≠ 0`, the only way the source
monomial `z(ij.1, ij.2)` can enter the positive part `ppProd ij` is through
the coefficients `A ij.1 ij.1 ij.2` or `A ij.2 ij.1 ij.2`. If both vanish,
then the positive part is insensitive to the self-coordinate. -/
theorem selfProduct_case1_no_self_production
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (ij : Fin d × Fin d) (z : Fin d × Fin d → ℝ) (u : ℝ)
    (h1 : ij.1 ≠ s.zero ∧ ij.2 ≠ s.zero)
    (hA_left : s.A ij.1 ij.1 ij.2 = 0)
    (hA_right : s.A ij.2 ij.1 ij.2 = 0) :
    s.ppProd ij (Function.update z ij u) = s.ppProd ij z :=
  s.ppProd_case1_update_self_eq ij z u h1 hA_left hA_right

/-- Updating the single coordinate `(0,j)` in `x0Qz k` changes it affinely:
all other summands stay fixed, and the `j`-summand is replaced by `u`. -/
theorem x0Qz_update_zero_coord {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (k j : Fin d) (z : Fin d × Fin d → ℝ) (u : ℝ) :
    s.x0Qz k (Function.update z (s.zero, j) u) =
      (∑ a ∈ Finset.univ.erase j, s.B k a * z (s.zero, a)) + s.B k j * u := by
  unfold Stage2CubicForm.x0Qz
  rw [← Finset.add_sum_erase Finset.univ
    (fun a : Fin d => s.B k a * Function.update z (s.zero, j) u (s.zero, a))
    (Finset.mem_univ j)]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    have hneq : a ≠ j := (Finset.mem_erase.mp ha).1
    have hp : (s.zero, a) ≠ (s.zero, j) := by
      intro h
      exact hneq (by simpa using congrArg Prod.snd h)
    simp [Function.update, hp]
  · simp [Function.update]

/-- Updating a nonzero-row coordinate `(i,0)` does not affect `x0Qz k`, since
`x0Qz` only reads coordinates of the form `(0,a)`. -/
theorem x0Qz_update_nonzero_row_zero_eq {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (k i : Fin d) (hi : i ≠ s.zero) (z : Fin d × Fin d → ℝ) (u : ℝ) :
    s.x0Qz k (Function.update z (i, s.zero) u) = s.x0Qz k z := by
  unfold Stage2CubicForm.x0Qz
  apply Finset.sum_congr rfl
  intro a ha
  have hp : (s.zero, a) ≠ (i, s.zero) := by
    intro h
    exact hi (by simpa using (congrArg Prod.fst h).symm)
  simp [Function.update, hp]

/-- Updating a single coordinate of `z` changes `Pz i` by exactly the matching
coefficient times the increment on that coordinate. -/
theorem Pz_update_single_coord_affine {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (i a b : Fin d) (z : Fin d × Fin d → ℝ) (u : ℝ) :
    s.Pz i (Function.update z (a, b) u) =
      s.Pz i z + s.A i a b * (u - z (a, b)) := by
  unfold Stage2CubicForm.Pz
  rw [← Finset.add_sum_erase Finset.univ
    (fun x : Fin d => ∑ y, s.A i x y * Function.update z (a, b) u (x, y))
    (Finset.mem_univ a)]
  rw [← Finset.add_sum_erase Finset.univ
    (fun x : Fin d => ∑ y, s.A i x y * z (x, y))
    (Finset.mem_univ a)]
  have houter :
      ∑ x ∈ Finset.univ.erase a, ∑ y, s.A i x y * Function.update z (a, b) u (x, y) =
        ∑ x ∈ Finset.univ.erase a, ∑ y, s.A i x y * z (x, y) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxa : x ≠ a := (Finset.mem_erase.mp hx).1
    apply Finset.sum_congr rfl
    intro y hy
    have hp : (x, y) ≠ (a, b) := by
      intro h
      exact hxa (by simpa using congrArg Prod.fst h)
    simp [Function.update, hp]
  have hinner :
      (∑ y, s.A i a y * Function.update z (a, b) u (a, y)) =
        (∑ y, s.A i a y * z (a, y)) + s.A i a b * (u - z (a, b)) := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun y : Fin d => s.A i a y * Function.update z (a, b) u (a, y))
      (Finset.mem_univ b)]
    rw [← Finset.add_sum_erase Finset.univ
      (fun y : Fin d => s.A i a y * z (a, y))
      (Finset.mem_univ b)]
    have herase :
        ∑ y ∈ Finset.univ.erase b, s.A i a y * Function.update z (a, b) u (a, y) =
          ∑ y ∈ Finset.univ.erase b, s.A i a y * z (a, y) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyb : y ≠ b := (Finset.mem_erase.mp hy).1
      have hp : (a, y) ≠ (a, b) := by
        intro h
        exact hyb (by simpa using congrArg Prod.snd h)
      simp [Function.update, hp]
    rw [herase]
    simp [Function.update]
    ring
  rw [houter, hinner]
  ring

/-- The boundary production term for `z'_{0,j}` is affine in the self-coordinate
`z_{0,j}`. In particular no square of `z_{0,j}` is created inside `ppProd`. -/
theorem selfProduct_case2a_ppProd_update_self_affine
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (j : Fin d) (hj : j ≠ s.zero)
    (z : Fin d × Fin d → ℝ) (u : ℝ) :
    s.ppProd (s.zero, j) (Function.update z (s.zero, j) u)
      =
    z (s.zero, s.zero) * (s.Pz j z + s.A j s.zero j * (u - z (s.zero, j)))
      +
    ∑ k ∈ Finset.univ.filter (· ≠ s.zero),
      z (k, j) * ((∑ a ∈ Finset.univ.erase j, s.B k a * z (s.zero, a)) + s.B k j * u) := by
  have hcase : ¬ (s.zero ≠ s.zero ∧ j ≠ s.zero) := by simp
  have hnot00 : ¬ (s.zero = s.zero ∧ j = s.zero) := by simp [hj]
  have hzero : (s.zero : Fin d) = s.zero := rfl
  unfold Stage2CubicForm.ppProd
  rw [if_neg hcase, if_neg hnot00, if_pos hzero]
  have hz00 : Function.update z (s.zero, j) u (s.zero, s.zero) = z (s.zero, s.zero) := by
    have hp : (s.zero, s.zero) ≠ (s.zero, j) := by
      intro h
      exact hj (by simpa using (congrArg Prod.snd h).symm)
    simp [Function.update, hp]
  have hcol :
      s.colCoupling j (Function.update z (s.zero, j) u) =
        ∑ k ∈ Finset.univ.filter (· ≠ s.zero),
          z (k, j) * ((∑ a ∈ Finset.univ.erase j, s.B k a * z (s.zero, a)) + s.B k j * u) := by
    unfold Stage2CubicForm.colCoupling
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ s.zero := (Finset.mem_filter.mp hk).2
    have hzkj : Function.update z (s.zero, j) u (k, j) = z (k, j) := by
      have hp : (k, j) ≠ (s.zero, j) := by
        intro h
        exact hk0 (by simpa using congrArg Prod.fst h)
      simp [Function.update, hp]
    rw [hzkj, x0Qz_update_zero_coord s k j z u]
  rw [hz00, hcol, Pz_update_single_coord_affine s j s.zero j z u]

/-- Symmetric boundary case: the production term for `z'_{i,0}` is affine in
the self-coordinate `z_{i,0}`. -/
theorem selfProduct_case2b_ppProd_update_self_affine
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (i : Fin d) (hi : i ≠ s.zero)
    (z : Fin d × Fin d → ℝ) (u : ℝ) :
    s.ppProd (i, s.zero) (Function.update z (i, s.zero) u)
      =
    z (s.zero, s.zero) * (s.Pz i z + s.A i i s.zero * (u - z (i, s.zero)))
      +
    s.rowCoupling i z := by
  have hcase : ¬ (i ≠ s.zero ∧ s.zero ≠ s.zero) := by simp
  have hnot00 : ¬ (i = s.zero ∧ s.zero = s.zero) := by simp [hi]
  have hzero : ¬ i = s.zero := hi
  unfold Stage2CubicForm.ppProd
  rw [if_neg hcase, if_neg hnot00, if_neg hzero]
  have hz00 : Function.update z (i, s.zero) u (s.zero, s.zero) = z (s.zero, s.zero) := by
    have hp : (s.zero, s.zero) ≠ (i, s.zero) := by
      intro h
      exact hi (by simpa using congrArg Prod.fst h.symm)
    simp [Function.update, hp]
  have hrow :
      s.rowCoupling i (Function.update z (i, s.zero) u) = s.rowCoupling i z := by
    unfold Stage2CubicForm.rowCoupling
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ s.zero := (Finset.mem_filter.mp hk).2
    have hzjk : Function.update z (i, s.zero) u (i, k) = z (i, k) := by
      have hp : (i, k) ≠ (i, s.zero) := by
        intro h
        exact hk0 (by simpa using congrArg Prod.snd h)
      simp [Function.update, hp]
    rw [hzjk, x0Qz_update_nonzero_row_zero_eq s k i hi z u]
  rw [hz00, hrow, Pz_update_single_coord_affine s i i s.zero z u]

/-- The corner production term for `z'_{0,0}` is linear in `z_{0,0}`: the other
factor `totalQxz` is independent of that coordinate. -/
theorem selfProduct_case3_ppProd_update_self_linear
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (z : Fin d × Fin d → ℝ) (u : ℝ) :
    s.ppProd (s.zero, s.zero) (Function.update z (s.zero, s.zero) u) =
      2 * u * s.totalQxz z := by
  have hcase : ¬ (s.zero ≠ s.zero ∧ s.zero ≠ s.zero) := by simp
  have h00 : s.zero = s.zero ∧ s.zero = s.zero := ⟨rfl, rfl⟩
  unfold Stage2CubicForm.ppProd
  rw [if_neg hcase, if_pos h00]
  have htot :
      s.totalQxz (Function.update z (s.zero, s.zero) u) = s.totalQxz z := by
    unfold Stage2CubicForm.totalQxz
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro a ha
    have hk0 : k ≠ s.zero := (Finset.mem_filter.mp hk).2
    have hp : (a, k) ≠ (s.zero, s.zero) := by
      intro h
      exact hk0 (by simpa using congrArg Prod.snd h)
    simp [Function.update, hp]
  simp [Function.update, htot]

/-- **Capstone.** The self-product positive part `ppProd q` is affine in the
self-coordinate `z q`, for every `q : Fin d × Fin d`.

This unifies the four structural cases for `ppProd` of a `Stage2CubicForm`:

* Case 1 (interior, `q.1 ≠ 0 ∧ q.2 ≠ 0`): nontrivial affine, with slope
  `z(0,q.2)·A q.1 q.1 q.2 + z(0,q.1)·A q.2 q.1 q.2`.
* Case 2a (boundary row 0, `q = (0, j)`, `j ≠ 0`): nontrivial affine.
* Case 2b (boundary col 0, `q = (i, 0)`, `i ≠ 0`): nontrivial affine.
* Case 3 (corner, `q = (0, 0)`): in fact linear, slope `2·totalQxz z`.

The existential form `∃ c₀ c₁, ppProd q (update z q u) = c₀ + c₁ · u` is what
the flow-network / NAP argument needs: it rules out quadratic-or-higher
self-production of any cubed variable. -/
theorem selfProduct_ppProd_update_self_affine
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ) :
    ∃ c₀ c₁ : ℝ, ∀ u, s.ppProd q (Function.update z q u) = c₀ + c₁ * u := by
  obtain ⟨qa, qb⟩ := q
  by_cases h1a : qa = s.zero
  · by_cases h1b : qb = s.zero
    · -- Case 3: corner q = (0, 0)
      subst h1a; subst h1b
      refine ⟨0, 2 * s.totalQxz z, fun u => ?_⟩
      rw [selfProduct_case3_ppProd_update_self_linear s z u]
      ring
    · -- Case 2a: boundary q = (0, qb), qb ≠ 0
      subst h1a
      refine ⟨
        z (s.zero, s.zero) * (s.Pz qb z - s.A qb s.zero qb * z (s.zero, qb))
          + ∑ k ∈ Finset.univ.filter (· ≠ s.zero),
              z (k, qb) * ∑ a ∈ Finset.univ.erase qb, s.B k a * z (s.zero, a),
        z (s.zero, s.zero) * s.A qb s.zero qb
          + ∑ k ∈ Finset.univ.filter (· ≠ s.zero), z (k, qb) * s.B k qb,
        fun u => ?_⟩
      rw [selfProduct_case2a_ppProd_update_self_affine s qb h1b z u]
      have hsum :
          ∑ k ∈ Finset.univ.filter (· ≠ s.zero),
              z (k, qb) * ((∑ a ∈ Finset.univ.erase qb, s.B k a * z (s.zero, a))
                + s.B k qb * u)
            = (∑ k ∈ Finset.univ.filter (· ≠ s.zero),
                z (k, qb) * ∑ a ∈ Finset.univ.erase qb, s.B k a * z (s.zero, a))
              + (∑ k ∈ Finset.univ.filter (· ≠ s.zero), z (k, qb) * s.B k qb) * u := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hsum]
      ring
  · by_cases h1b : qb = s.zero
    · -- Case 2b: boundary q = (qa, 0), qa ≠ 0
      subst h1b
      refine ⟨
        z (s.zero, s.zero) * (s.Pz qa z - s.A qa qa s.zero * z (qa, s.zero))
          + s.rowCoupling qa z,
        z (s.zero, s.zero) * s.A qa qa s.zero,
        fun u => ?_⟩
      rw [selfProduct_case2b_ppProd_update_self_affine s qa h1a z u]
      ring
    · -- Case 1: interior q = (qa, qb), qa ≠ 0, qb ≠ 0
      have h1 : ((qa, qb) : Fin d × Fin d).1 ≠ s.zero ∧
                ((qa, qb) : Fin d × Fin d).2 ≠ s.zero := ⟨h1a, h1b⟩
      refine ⟨
        z (s.zero, qb) * (s.Pz qa z - s.A qa qa qb * z (qa, qb))
          + z (s.zero, qa) * (s.Pz qb z - s.A qb qa qb * z (qa, qb)),
        z (s.zero, qb) * s.A qa qa qb + z (s.zero, qa) * s.A qb qa qb,
        fun u => ?_⟩
      have hz1 : Function.update z (qa, qb) u (s.zero, qb) = z (s.zero, qb) := by
        have hp : (s.zero, qb) ≠ (qa, qb) := fun h =>
          h1a (by simpa using (congrArg Prod.fst h).symm)
        simp [Function.update, hp]
      have hz2 : Function.update z (qa, qb) u (s.zero, qa) = z (s.zero, qa) := by
        have hp : (s.zero, qa) ≠ (qa, qb) := fun h =>
          h1a (by simpa using (congrArg Prod.fst h).symm)
        simp [Function.update, hp]
      have hPzA := Pz_update_single_coord_affine s qa qa qb z u
      have hPzB := Pz_update_single_coord_affine s qb qa qb z u
      unfold Stage2CubicForm.ppProd
      rw [if_pos h1, hz1, hz2, hPzA, hPzB]
      ring

/-- Updating a single coordinate `(a,b)` in `totalPz` changes it affinely: the
summed `Pz k` over `k ≠ 0` each pick up the same coefficient `A k a b`, so the
total increment is `(∑ k≠0, A k a b) · (u - z(a,b))`. -/
theorem totalPz_update_single_coord_affine
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (a b : Fin d) (z : Fin d × Fin d → ℝ) (u : ℝ) :
    s.totalPz (Function.update z (a, b) u) =
      s.totalPz z
        + (∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.A k a b) * (u - z (a, b)) := by
  unfold Stage2CubicForm.totalPz
  have hpoint : ∀ k, s.Pz k (Function.update z (a, b) u)
      = s.Pz k z + s.A k a b * (u - z (a, b)) :=
    fun k => Pz_update_single_coord_affine s k a b z u
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]

/-- **Capstone (degradation side).** The self-product degradation rate `ppDegr q`
is affine in the self-coordinate `z q`, for every `q : Fin d × Fin d`.

Paired with `selfProduct_ppProd_update_self_affine`, this gives a complete
structural picture: `ppField q = ppProd q - ppDegr q · z q` has *at worst
quadratic* self-feedback, and the quadratic piece carries a *non-positive*
sign (it comes from `-ppDegr · z q` with `ppDegr ≥ 0` on the orthant). So no
cubed self-product variable exhibits runaway quadratic self-production —
the NAP-compatible structure survives the cubic lift. -/
theorem selfProduct_ppDegr_update_self_affine
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧
      ∀ u, s.ppDegr q (Function.update z q u) = c₀ + c₁ * u := by
  obtain ⟨qa, qb⟩ := q
  by_cases h1a : qa = s.zero
  · by_cases h1b : qb = s.zero
    · -- Case 3: corner q = (0, 0)
      subst h1a; subst h1b
      have hcase1 : ¬ ((s.zero : Fin d) ≠ s.zero ∧ (s.zero : Fin d) ≠ s.zero) := by simp
      have hcase3 : (s.zero : Fin d) = s.zero ∧ (s.zero : Fin d) = s.zero := ⟨rfl, rfl⟩
      refine ⟨2 * s.totalPz z
                - 2 * (∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.A k s.zero s.zero)
                  * z (s.zero, s.zero),
              2 * (∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.A k s.zero s.zero),
              ?_, fun u => ?_⟩
      · exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (Finset.sum_nonneg (fun k _ => s.A_nonneg k s.zero s.zero))
      · have htP := totalPz_update_single_coord_affine s s.zero s.zero z u
        unfold Stage2CubicForm.ppDegr
        rw [if_neg hcase1, if_pos hcase3, htP]
        ring
    · -- Case 2a: q = (0, qb), qb ≠ 0
      subst h1a
      have hcase1 : ¬ ((s.zero : Fin d) ≠ s.zero ∧ qb ≠ s.zero) := by simp
      have hcase3 : ¬ ((s.zero : Fin d) = s.zero ∧ qb = s.zero) := by simp [h1b]
      have hcase2a : (s.zero : Fin d) = s.zero := rfl
      refine ⟨(∑ a ∈ Finset.univ.erase qb, s.B qb a * z (s.zero, a))
                + s.totalPz z
                - (∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.A k s.zero qb)
                  * z (s.zero, qb),
              s.B qb qb
                + ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.A k s.zero qb,
              ?_, fun u => ?_⟩
      · exact add_nonneg (s.B_nonneg qb qb)
          (Finset.sum_nonneg (fun k _ => s.A_nonneg k s.zero qb))
      · have htP := totalPz_update_single_coord_affine s s.zero qb z u
        have hx0 := x0Qz_update_zero_coord s qb qb z u
        unfold Stage2CubicForm.ppDegr
        rw [if_neg hcase1, if_neg hcase3, if_pos hcase2a, hx0, htP]
        ring
  · by_cases h1b : qb = s.zero
    · -- Case 2b: q = (qa, 0), qa ≠ 0
      subst h1b
      have hcase1 : ¬ (qa ≠ s.zero ∧ (s.zero : Fin d) ≠ s.zero) := by simp
      have hcase3 : ¬ (qa = s.zero ∧ (s.zero : Fin d) = s.zero) := by simp [h1a]
      refine ⟨s.x0Qz qa z + s.totalPz z
                - (∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.A k qa s.zero)
                  * z (qa, s.zero),
              ∑ k ∈ Finset.univ.filter (· ≠ s.zero), s.A k qa s.zero,
              ?_, fun u => ?_⟩
      · exact Finset.sum_nonneg (fun k _ => s.A_nonneg k qa s.zero)
      · have htP := totalPz_update_single_coord_affine s qa s.zero z u
        have hx0 := x0Qz_update_nonzero_row_zero_eq s qa qa h1a z u
        unfold Stage2CubicForm.ppDegr
        rw [if_neg hcase1, if_neg hcase3, if_neg h1a, hx0, htP]
        ring
    · -- Case 1: interior q = (qa, qb), qa ≠ 0, qb ≠ 0
      have hcase1 : ((qa, qb) : Fin d × Fin d).1 ≠ s.zero ∧
                    ((qa, qb) : Fin d × Fin d).2 ≠ s.zero := ⟨h1a, h1b⟩
      refine ⟨s.x0Qz qa z + s.x0Qz qb z, 0, le_refl 0, fun u => ?_⟩
      have hx1 : s.x0Qz qa (Function.update z (qa, qb) u) = s.x0Qz qa z := by
        unfold Stage2CubicForm.x0Qz
        apply Finset.sum_congr rfl
        intro a _
        have hp : (s.zero, a) ≠ (qa, qb) := fun h =>
          h1a (by simpa using (congrArg Prod.fst h).symm)
        simp [Function.update, hp]
      have hx2 : s.x0Qz qb (Function.update z (qa, qb) u) = s.x0Qz qb z := by
        unfold Stage2CubicForm.x0Qz
        apply Finset.sum_congr rfl
        intro a _
        have hp : (s.zero, a) ≠ (qa, qb) := fun h =>
          h1a (by simpa using (congrArg Prod.fst h).symm)
        simp [Function.update, hp]
      unfold Stage2CubicForm.ppDegr
      rw [if_pos hcase1, hx1, hx2]
      ring

/-- **Payoff theorem.** Combining the two capstones: `ppField q` has at most
*quadratic* self-feedback in its own coordinate, and the quadratic term is
*non-positive*. Explicitly, for every `q : Fin d × Fin d` there exist reals
`a, b, c` with `0 ≤ c` such that

  `∀ u, s.ppField (update z q u) q = a + b · u − c · u²`.

So `ppField q`, restricted to the self-line `{update z q u : u ∈ ℝ}`, is a
downward-facing parabola in `u`. This is the NAP-compatibility structure for
cubed self-product variables of a `Stage2CubicForm`: no variable has runaway
positive quadratic self-feedback. The sign of `c` comes from `A_nonneg` /
`B_nonneg` inside `selfProduct_ppDegr_update_self_affine`. -/
theorem selfProduct_ppField_update_self_nonpos_quadratic
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ) :
    ∃ a b c : ℝ, 0 ≤ c ∧
      ∀ u, s.ppField (Function.update z q u) q = a + b * u - c * u * u := by
  obtain ⟨cP0, cP1, hP⟩ := selfProduct_ppProd_update_self_affine s q z
  obtain ⟨cD0, cD1, hcD1, hD⟩ := selfProduct_ppDegr_update_self_affine s q z
  refine ⟨cP0, cP1 - cD0, cD1, hcD1, fun u => ?_⟩
  have hzq : Function.update z q u q = u := by simp [Function.update]
  rw [s.ppField_eq_crn (Function.update z q u) q, hzq, hP u, hD u]
  ring

/-- **Corollary.** The self-product field `ppField q` itself is a
*non-positive quadratic* in the self-coordinate `z q`, with coefficients
depending only on the other coordinates.

Formally: `∃ a b c, 0 ≤ c ∧ s.ppField z q = a + b · z q − c · (z q)²`.

This is the unconditional (not-along-update) version of the payoff: the
self-line statement extends to the full orthant by plugging the original
coordinate value back in. -/
theorem selfProduct_ppField_nonpos_quadratic_in_self
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ) :
    ∃ a b c : ℝ, 0 ≤ c ∧
      s.ppField z q = a + b * z q - c * z q * z q := by
  obtain ⟨a, b, c, hc, hfield⟩ :=
    selfProduct_ppField_update_self_nonpos_quadratic s q z
  refine ⟨a, b, c, hc, ?_⟩
  have hId : Function.update z q (z q) = z := by
    funext p
    by_cases h : p = q
    · subst h; simp
    · simp [Function.update, h]
  have heval := hfield (z q)
  rw [hId] at heval
  exact heval

/-- **Linear upper bound.** On the non-negative orthant (in the self-coord),
the cubed self-product field is bounded above by an affine function of the
self-coordinate:

  `0 ≤ z q → ppField z q ≤ a + b · z q`

with `a, b` depending only on the other coordinates. This is the direct
stability consequence of `selfProduct_ppField_nonpos_quadratic_in_self`:
the non-positive quadratic term `− c·(z q)²` can only pull `ppField` lower
on the nonneg orthant, never higher. -/
theorem selfProduct_ppField_linear_upper_bound
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ) (hnn : 0 ≤ z q) :
    ∃ a b : ℝ, s.ppField z q ≤ a + b * z q := by
  obtain ⟨a, b, c, hc, heq⟩ :=
    selfProduct_ppField_nonpos_quadratic_in_self s q z
  refine ⟨a, b, ?_⟩
  have hquad : 0 ≤ c * z q * z q :=
    mul_nonneg (mul_nonneg hc hnn) hnn
  linarith [heq]

/-! ### Invariance of the non-negative orthant

The cubed self-product field decomposes as `ppField = ppProd - ppDegr · z q`
(see `ppField_eq_crn`). On the non-negative orthant, `ppProd` and `ppDegr`
are both non-negative (`ppProd_nonneg`, `ppDegr_nonneg` in `Stages.lean`).
Combined with non-negativity of `z q` itself, this pins down the two-sided
envelope of `ppField` and — crucially — the **face-invariance**: along the
face `{z q = 0}`, the field points into the orthant (`ppField z q ≥ 0`),
so solutions cannot leak out through any cubed self-product coordinate. -/

/-- Upper envelope on the non-negative orthant: `ppField q ≤ ppProd q`. The
subtracted term `ppDegr q · z q` is non-negative when both `ppDegr q ≥ 0`
(by `ppDegr_nonneg`) and `z q ≥ 0`, so dropping it gives an upper bound. -/
theorem selfProduct_ppField_le_ppProd
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (hz : ∀ p, 0 ≤ z p) :
    s.ppField z q ≤ s.ppProd q z := by
  have heq := s.ppField_eq_crn z q
  have hsub : 0 ≤ s.ppDegr q z * z q :=
    mul_nonneg (s.ppDegr_nonneg q z hz) (hz q)
  linarith [heq]

/-- Lower envelope on the non-negative orthant:
`-(ppDegr q · z q) ≤ ppField q`. The added `ppProd q` is non-negative
(by `ppProd_nonneg`), so the decomposition is pinned from below by the
degradation term alone. -/
theorem selfProduct_ppField_ge_neg_ppDegr_self
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (hz : ∀ p, 0 ≤ z p) :
    -(s.ppDegr q z * z q) ≤ s.ppField z q := by
  have heq := s.ppField_eq_crn z q
  have hprod : 0 ≤ s.ppProd q z := s.ppProd_nonneg q z hz
  linarith [heq]

/-- The underlying field of any `Stage2CubicForm` is conservative.
This is an immediate consequence of the `field_zero` axiom: setting the
balancing coordinate to `-(sum of the rest)` forces the total sum to 0. -/
theorem Stage2CubicForm.field_isConservative
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field) : IsConservative field := by
  intro x
  have hz := s.field_zero x
  have hsplit : ∑ i, field x i =
      field x s.zero +
        ∑ i ∈ Finset.univ.filter (· ≠ s.zero), field x i := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = s.zero)]
    simp [Finset.filter_eq']
  rw [hsplit, hz]; ring

/-- **Interior case: no quadratic self-feedback.** For interior self-product
variables (`q.1, q.2 ≠ 0`), the cubed field `ppField` restricted to the
self-line `{Function.update z q u}` is *exactly affine* in `u` — the
quadratic coefficient is `0`. This strengthens
`selfProduct_ppField_update_self_nonpos_quadratic` in the interior case:
there `c` is merely known to be `≥ 0`; here we pin it to exactly `0`.

The reason: in case 1, `ppDegr q` depends only on `x0Qz qa z + x0Qz qb z`,
each of which sums `B i a · z(s.zero, a)` over `a`. For interior `q`,
`(s.zero, a) ≠ (qa, qb)` for every `a`, so `ppDegr q` is insensitive to
updating the self-coordinate, and the quadratic term `ppDegr · u · u` in
`ppField = ppProd - ppDegr · u` never fires. `ppProd` itself *does* depend
linearly on `u` through the `A qa qa qb · z(qa,qb)` etc. terms in
`Pz qa`, `Pz qb`, which is why the combined expression is still affine
(linear in `u`), not constant. -/
theorem selfProduct_ppField_update_self_affine_interior
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (h1 : q.1 ≠ s.zero ∧ q.2 ≠ s.zero) :
    ∃ c₀ c₁ : ℝ, ∀ u, s.ppField (Function.update z q u) q = c₀ + c₁ * u := by
  obtain ⟨cP0, cP1, hP⟩ := selfProduct_ppProd_update_self_affine s q z
  -- ppDegr is constant in the interior case
  have hD : ∀ u, s.ppDegr q (Function.update z q u) = s.ppDegr q z := by
    intro u
    obtain ⟨qa, qb⟩ := q
    obtain ⟨h1a, h1b⟩ := h1
    have hcond : ((qa, qb) : Fin d × Fin d).1 ≠ s.zero ∧
                 ((qa, qb) : Fin d × Fin d).2 ≠ s.zero := ⟨h1a, h1b⟩
    have hx : ∀ i : Fin d,
        s.x0Qz i (Function.update z (qa, qb) u) = s.x0Qz i z := by
      intro i
      unfold Stage2CubicForm.x0Qz
      apply Finset.sum_congr rfl
      intro a _
      have hp : (s.zero, a) ≠ (qa, qb) := fun h => h1a (Prod.mk.inj h).1.symm
      simp [Function.update, hp]
    unfold Stage2CubicForm.ppDegr
    rw [if_pos hcond, if_pos hcond, hx qa, hx qb]
  refine ⟨cP0, cP1 - s.ppDegr q z, fun u => ?_⟩
  have hzq : Function.update z q u q = u := by simp [Function.update]
  rw [s.ppField_eq_crn (Function.update z q u) q, hzq, hP u, hD u]
  ring

/-- **Manifold conservation of `ppField`.** On the self-product manifold
`z(i,j) = x(i)·x(j)` with `∑ x = 1`, the cubed-variable field `ppField` is
conservative: `∑_{q} ppField z q = 0`.

This is the bridge from the off-manifold definition (where `ppField` is
*not* conservative in general) to the on-manifold dynamics. The proof
composes `ppField_eq_on_manifold` (cellwise agreement with
`selfProductField`) with `selfProductField_conservative` (conservation of
the degree-4 self-product field, which inherits conservation from the
base field via `field_isConservative`). -/
theorem ppField_conservative_on_manifold
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (x : Fin d → ℝ) (hsum : ∑ j, x j = 1) :
    ∑ q : Fin d × Fin d, s.ppField (fun ab => x ab.1 * x ab.2) q = 0 := by
  have hcong : ∀ q : Fin d × Fin d,
      s.ppField (fun ab => x ab.1 * x ab.2) q =
        selfProductField field (fun ab => x ab.1 * x ab.2) q :=
    fun q => s.ppField_eq_on_manifold x hsum q
  rw [Finset.sum_congr rfl (fun q _ => hcong q)]
  exact selfProductField_conservative s.field_isConservative _

/-- **Face invariance of the non-negative orthant.** On the face
`{z q = 0}` of the non-negative orthant, the cubed self-product field
is non-negative, so the vector field points into the orthant along that
face. This is the formal expression of "no cubed self-product variable
can exit the non-negative orthant under its own dynamics."

Proof: at `z q = 0` the degradation term `ppDegr q z · z q` vanishes, so
`ppField = ppProd`, which is non-negative by `ppProd_nonneg`. -/
theorem selfProduct_ppField_nonneg_on_zero_face
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (q : Fin d × Fin d) (z : Fin d × Fin d → ℝ)
    (hz : ∀ p, 0 ≤ z p) (hq0 : z q = 0) :
    0 ≤ s.ppField z q := by
  have heq := s.ppField_eq_crn z q
  have hprod : 0 ≤ s.ppProd q z := s.ppProd_nonneg q z hz
  rw [hq0] at heq
  linarith [heq]

/-! ### Swap-symmetry on symmetric `z`

The cubed-variable field `ppField` is defined asymmetrically in the four
cases (Case 2a treats `(0, j)` differently from Case 2b at `(j, 0)`), yet
on any `z` satisfying `z(a, b) = z(b, a)` the value at `(i, j)` equals the
value at `(j, i)`. This is the structural symmetry inherited from the
self-product manifold, and it is the reason Cases 2a and 2b give
"equivalent" dynamics. -/

/-- On symmetric `z`, `colCoupling j z = rowCoupling j z`. The defining
sums `∑_{k≠0} z(k, j) · x0Qz k` and `∑_{k≠0} z(j, k) · x0Qz k` differ
only by the `(k, j) ↔ (j, k)` swap, which `z`-symmetry absorbs. -/
theorem colCoupling_eq_rowCoupling_of_symmetric
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field) (j : Fin d)
    (z : Fin d × Fin d → ℝ) (hsym : ∀ a b, z (a, b) = z (b, a)) :
    s.colCoupling j z = s.rowCoupling j z := by
  unfold Stage2CubicForm.colCoupling Stage2CubicForm.rowCoupling
  apply Finset.sum_congr rfl
  intro k _
  rw [hsym k j]

/-- **Swap-symmetry of `ppField` on symmetric `z`.** If `z(a, b) = z(b, a)`
for every `a, b`, then `ppField z (i, j) = ppField z (j, i)`. The four
cases unfold to addition/multiplication that commute once the `z`-symmetry
is applied, and Cases 2a/2b swap into each other. -/
theorem ppField_swap_of_symmetric
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (z : Fin d × Fin d → ℝ) (hsym : ∀ a b, z (a, b) = z (b, a)) (i j : Fin d) :
    s.ppField z (i, j) = s.ppField z (j, i) := by
  unfold Stage2CubicForm.ppField
  by_cases hi : i = s.zero
  · by_cases hj : j = s.zero
    · subst hi; subst hj; rfl
    · -- (0, j): Case 2a; (j, 0): Case 2b
      subst hi
      have h1 : ¬ ((s.zero : Fin d) ≠ s.zero ∧ j ≠ s.zero) := by simp
      have h1' : ¬ (j ≠ s.zero ∧ (s.zero : Fin d) ≠ s.zero) := by simp
      have h3 : ¬ ((s.zero : Fin d) = s.zero ∧ j = s.zero) := fun h => hj h.2
      have h3' : ¬ (j = s.zero ∧ (s.zero : Fin d) = s.zero) := fun h => hj h.1
      have h2a : (s.zero : Fin d) = s.zero := rfl
      rw [if_neg h1, if_neg h3, if_pos h2a,
          if_neg h1', if_neg h3', if_neg hj]
      have hcol := colCoupling_eq_rowCoupling_of_symmetric s j z hsym
      rw [hsym s.zero j, hcol]
  · by_cases hj : j = s.zero
    · -- (i, 0): Case 2b; (0, i): Case 2a
      subst hj
      have h1 : ¬ (i ≠ s.zero ∧ (s.zero : Fin d) ≠ s.zero) := by simp
      have h1' : ¬ ((s.zero : Fin d) ≠ s.zero ∧ i ≠ s.zero) := by simp
      have h3 : ¬ (i = s.zero ∧ (s.zero : Fin d) = s.zero) := fun h => hi h.1
      have h3' : ¬ ((s.zero : Fin d) = s.zero ∧ i = s.zero) := fun h => hi h.2
      have h2a : (s.zero : Fin d) = s.zero := rfl
      rw [if_neg h1, if_neg h3, if_neg hi,
          if_neg h1', if_neg h3', if_pos h2a]
      have hrow := colCoupling_eq_rowCoupling_of_symmetric s i z hsym
      rw [hsym i s.zero, ← hrow]
    · -- Case 1 at both (i, j) and (j, i)
      have h1 : (i, j).1 ≠ s.zero ∧ (i, j).2 ≠ s.zero := ⟨hi, hj⟩
      have h1' : (j, i).1 ≠ s.zero ∧ (j, i).2 ≠ s.zero := ⟨hj, hi⟩
      rw [if_pos h1, if_pos h1']
      rw [hsym i j]
      ring

/-- **Manifold corollary of `ppField_swap_of_symmetric`.** The self-product
manifold `z(a, b) = x(a) · x(b)` is automatically symmetric (multiplication
in `ℝ` commutes), so `ppField` applied to such a `z` satisfies
`f(x⊗x)(i, j) = f(x⊗x)(j, i)`. In words: *the cubed-variable dynamics on
the self-product manifold are index-swap symmetric.* -/
theorem ppField_swap_on_manifold
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (x : Fin d → ℝ) (i j : Fin d) :
    s.ppField (fun ab => x ab.1 * x ab.2) (i, j) =
      s.ppField (fun ab => x ab.1 * x ab.2) (j, i) := by
  apply ppField_swap_of_symmetric s
  intro a b
  exact mul_comm (x a) (x b)

/-! ### The all-zero fixed point

The zero state `z ≡ 0` is a fixed point of the cubed-variable ODE:
`ppField 0 q = 0` for every `q`. This falls out of the degree-2
homogeneity `ppField (c • z) = c² · ppField z` specialized at `c = 0`,
but the direct four-case unfolding is just as short and does not require
going through `smul`. -/

/-- Zero state is a fixed point: `ppField 0 q = 0`. -/
theorem ppField_at_zero
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field) (q : Fin d × Fin d) :
    s.ppField (fun _ => (0 : ℝ)) q = 0 := by
  unfold Stage2CubicForm.ppField
  have hPz : ∀ i : Fin d, s.Pz i (fun _ : Fin d × Fin d => (0 : ℝ)) = 0 := by
    intro i
    unfold Stage2CubicForm.Pz
    simp
  have hxQ : ∀ i : Fin d, s.x0Qz i (fun _ : Fin d × Fin d => (0 : ℝ)) = 0 := by
    intro i
    unfold Stage2CubicForm.x0Qz
    simp
  have htP : s.totalPz (fun _ : Fin d × Fin d => (0 : ℝ)) = 0 := by
    unfold Stage2CubicForm.totalPz
    simp [hPz]
  have htQ : s.totalQxz (fun _ : Fin d × Fin d => (0 : ℝ)) = 0 := by
    unfold Stage2CubicForm.totalQxz
    simp
  have hcol : ∀ j : Fin d, s.colCoupling j (fun _ : Fin d × Fin d => (0 : ℝ)) = 0 := by
    intro j
    unfold Stage2CubicForm.colCoupling
    simp
  have hrow : ∀ i : Fin d, s.rowCoupling i (fun _ : Fin d × Fin d => (0 : ℝ)) = 0 := by
    intro i
    unfold Stage2CubicForm.rowCoupling
    simp
  split_ifs with h1 h3 h2a
  · rw [hPz, hPz, hxQ, hxQ]; ring
  · rw [htQ, htP]; ring
  · rw [hPz, hcol, hxQ, htP]; ring
  · rw [hPz, hrow, hxQ, htP]; ring

/-! ### Transferring face-invariance to `selfProductField`

`selfProduct_ppField_nonneg_on_zero_face` is stated for the off-manifold
`ppField`. On the self-product manifold `z(a, b) = x(a) · x(b)`, the
identity `ppField = selfProductField` (from `ppField_eq_on_manifold`)
lets us transfer the face-invariance to the degree-4 field that actually
governs the product trajectory `z(t) = x(t) ⊗ x(t)`. -/

/-- **Manifold-level face invariance.** On the self-product manifold with
non-negative `x` and `∑ x = 1`, if the cubed coordinate `z(i, j) =
x(i) · x(j)` vanishes, then `selfProductField (x⊗x) (i, j) ≥ 0`. This
says: the ODE `z' = selfProductField z` cannot drive `z(i, j)` negative
through a zero crossing — the vector field pushes inward. -/
theorem selfProductField_nonneg_on_zero_face_manifold
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ}
    (s : Stage2CubicForm d field)
    (x : Fin d → ℝ) (hsum : ∑ j, x j = 1) (hx : ∀ i, 0 ≤ x i)
    (q : Fin d × Fin d) (hq0 : x q.1 * x q.2 = 0) :
    0 ≤ selfProductField field (fun ab => x ab.1 * x ab.2) q := by
  have hz : ∀ p : Fin d × Fin d, 0 ≤ (fun ab : Fin d × Fin d => x ab.1 * x ab.2) p := by
    intro p
    exact mul_nonneg (hx _) (hx _)
  have hface : 0 ≤ s.ppField (fun ab => x ab.1 * x ab.2) q :=
    selfProduct_ppField_nonneg_on_zero_face s q _ hz hq0
  rw [s.ppField_eq_on_manifold x hsum q] at hface
  exact hface

/-- **Closing tie.** The `selfProductField` lift of a Stage-2 cubic form field
is conservative on *any* `z` (not just the manifold): it is the direct corollary
of `Stage2CubicForm.field_isConservative` and the generic
`selfProductField_conservative`. This is the analytic side of the invariant that
`∑ z` stays constant along the lifted ODE, matching the combinatorial fact
that the total mass is preserved by Stage-2 reactions. -/
theorem Stage2CubicForm.selfProductField_conservative
    {d : ℕ} {field : (Fin d → ℝ) → Fin d → ℝ} (s : Stage2CubicForm d field)
    (z : Fin d × Fin d → ℝ) :
    ∑ ij : Fin d × Fin d, selfProductField field z ij = 0 :=
  Ripple.selfProductField_conservative s.field_isConservative z

/-! ## Protocol-level NoSelfMix invariant

For the PP → NAP pipeline (paper §11), the r²-trick lifts a quadratic PP
to a degree-4 PIVP by introducing a slack variable `zero` and setting
`ẋ_r = x_zero² · f_r(x)`. After cubing, every positive chain-rule
monomial `μ = x_zero² · x_a · x_b` has bounded self-exponent at the source.

Concretely: `μ source = 2·[source=zero] + [a=source] + [b=source]`.
- For `source ≠ zero`: `μ source = [a=source] + [b=source] ≤ 2` automatically.
- For `source = zero`: `μ source = 2 + [a=zero] + [b=zero]`, and since
  `a ≠ zero, b ≠ zero` (r²-trick side condition), we get `μ source = 2`.

So `μ source ≤ 2` (the `pipeline_bound` needed by `ProductionMonomial`)
holds unconditionally for `r2PPMonomial`. This is the structural invariant
that drives the NAP existence proof. -/

/-- **Pipeline bound**: every `r2PPMonomial` has source-exponent ≤ 2.

This is the structural fact that the r²-trick produces monomials whose
self-exponent is bounded by 2 — strictly tighter than the bare 4-PP
condition (self-exponent < 4), and exactly what `ProductionMonomial`'s
`pipeline_bound` field requires. -/
theorem r2PPMonomial_source_le_two {n : ℕ} {zero a b source : Fin n}
    (hza : a ≠ zero) (hzb : b ≠ zero) :
    r2PPMonomial zero a b source ≤ 2 := by
  unfold r2PPMonomial
  by_cases hsz : source = zero
  · -- When source = zero, a ≠ source and b ≠ source, so the last two if's are 0.
    rw [hsz]
    have ha : ¬ (zero : Fin n) = a := fun h => hza h.symm
    have hb : ¬ (zero : Fin n) = b := fun h => hzb h.symm
    simp [ha, hb]
  · -- When source ≠ zero, the first if is 0; the other two are each at most 1.
    have h1 : (if source = zero then 2 else 0) = 0 := by simp [hsz]
    rw [h1, Nat.zero_add]
    have h2 : (if source = a then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have h3 : (if source = b then 1 else 0) ≤ 1 := by split_ifs <;> omega
    omega

/-! ### ProductionMonomial builder from r²-trick data

Given a cubed index α, a source variable in supp(α), and a PP monomial
`x_a · x_b` (with `a, b ≠ zero`), we build a `ProductionMonomial α` with
`μ = r2PPMonomial zero a b`, provided the foreign_pair witness is supplied
by the caller. The pipeline_bound (`μ source ≤ 2`) is automatic via
`r2PPMonomial_source_le_two`.

The caller supplies foreign_pair because different cases (source at/off
the slack, a = b, etc.) need different witnesses; this keeps the builder
clean and defers dispatch to the protocol-level theorem. -/

/-- Build a `ProductionMonomial α` whose `μ` is an r²-trick monomial
`r2PPMonomial zero a b`, given the caller supplies a foreign-pair witness.

Side conditions:
* `α` is a cubed index (weight 3)
* `source ∈ supp(α)` (`0 < α source`)
* `a ≠ zero`, `b ≠ zero` (r²-trick side condition)
* Foreign pair of distinct non-source atoms with `μ > 0` (supplied). -/
noncomputable def productionMonomial_of_r2 {n : ℕ} {α : Fin n → ℕ}
    (hα : IsCubedIndex α) (zero source a b : Fin n)
    (hsrc : 0 < α source) (hza : a ≠ zero) (hzb : b ≠ zero)
    (hfp : ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
      0 < r2PPMonomial zero a b i₁ ∧ 0 < r2PPMonomial zero a b i₂) :
    ProductionMonomial α where
  δ := fun k => (α k - if k = source then 1 else 0) + r2PPMonomial zero a b k
  weight_eq := chain_rule_weight_six hα (r2PPMonomial_weight hza hzb) hsrc
  source := source
  source_in_supp := hsrc
  μ := r2PPMonomial zero a b
  μ_weight := r2PPMonomial_weight hza hzb
  chain_rule := fun _ => rfl
  pipeline_bound := r2PPMonomial_source_le_two hza hzb
  foreign_pair := hfp

/-- Foreign-pair witness when `source ≠ zero` and `a ≠ source`: take
`(zero, a)`. Uses `r2PPMonomial_foreign_pair`. -/
theorem r2PPMonomial_foreign_pair_a {n : ℕ} {zero a b source : Fin n}
    (hsz : source ≠ zero) (hza : a ≠ zero) (has : a ≠ source) :
    ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
      0 < r2PPMonomial zero a b i₁ ∧ 0 < r2PPMonomial zero a b i₂ :=
  r2PPMonomial_foreign_pair hsz.symm hza has

/-- Foreign-pair witness when `source ≠ zero` and `b ≠ source`: take
`(zero, b)`. Symmetric-in-role variant of `r2PPMonomial_foreign_pair`. -/
theorem r2PPMonomial_foreign_pair_b {n : ℕ} {zero a b source : Fin n}
    (hsz : source ≠ zero) (hzb : b ≠ zero) (hbs : b ≠ source) :
    ∃ i₁ i₂, i₁ ≠ i₂ ∧ i₁ ≠ source ∧ i₂ ≠ source ∧
      0 < r2PPMonomial zero a b i₁ ∧ 0 < r2PPMonomial zero a b i₂ := by
  refine ⟨zero, b, hzb.symm, hsz.symm, hbs, ?_, ?_⟩
  · simp [r2PPMonomial]
  · by_cases hab : a = b
    · simp [r2PPMonomial, hzb, hab]
    · simp [r2PPMonomial, hzb, hab]

/-- **Unified PP → NAP split theorem**: for every positive PP monomial
`x_a x_b` in `f_source`, the r²-trick chain-rule monomial
`(α - e_source) + (2 e_zero + e_a + e_b)` admits a balanced non-
autocatalytic split.

The side condition `hnoself : source ≠ zero → (a ≠ source ∨ b ≠ source)`
is supplied by `NoSelfSelf`-plus-positivity at the protocol level: if
the monomial `coeff source a b > 0` and `coeff source source source = 0`,
then it cannot be the case that `a = b = source`.

This theorem replaces `pp_r2_split` (which required the stricter
`a ≠ source ∧ b ≠ source` instead of the disjunction), and correctly
covers the case where exactly one of `a, b` equals `source`. -/
theorem pp_r2_nap_split {n : ℕ}
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (zero source a b : Fin n)
    (hsrc : 0 < α source)
    (hza : a ≠ zero) (hzb : b ≠ zero)
    (hnoself : source ≠ zero → (a ≠ source ∨ b ≠ source)) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  by_cases hse : source = zero
  · -- Case A: source = zero. Dispatch on a = b.
    subst hse
    by_cases hab : a = b
    · subst hab
      exact pp_r2_zero_source_split_doubled α hα source a hsrc hza
    · exact pp_r2_zero_source_split_distinct α hα source a b hsrc hza hzb hab
  · -- Case B: source ≠ zero. Dispatch on which of a, b is ≠ source.
    rcases hnoself hse with has | hbs
    · -- B1: a ≠ source. foreign_pair = (zero, a). Build PM + invoke feasibility.
      have hfp := @r2PPMonomial_foreign_pair_a n zero a b source hse hza has
      exact nap_splitting_feasibility α hα
        (productionMonomial_of_r2 hα zero source a b hsrc hza hzb hfp)
    · -- B2: b ≠ source. foreign_pair = (zero, b).
      have hfp := @r2PPMonomial_foreign_pair_b n zero a b source hse hzb hbs
      exact nap_splitting_feasibility α hα
        (productionMonomial_of_r2 hα zero source a b hsrc hza hzb hfp)

/-- **Protocol-level PP → NAP theorem**: for every SynPPBalance satisfying
`NoSelfSelf` and every positive PP monomial `x_a x_b` in `f_source`
(witnessed by `coeff source a b > 0`, with `a, b ≠ zero` from the r²-trick
side condition), every chain-rule production monomial in v̇_α for a cubed α
with `source ∈ supp(α)` admits a balanced non-autocatalytic split.

This is the main theorem for the cubing step of the PP → NAP pipeline. -/
theorem synpp_r2_nap_split {n : ℕ}
    (eq : SynPPBalance n) (hnss : eq.NoSelfSelf)
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (zero source a b : Fin n)
    (hsrc : 0 < α source)
    (hza : a ≠ zero) (hzb : b ≠ zero)
    (hpos : 0 < eq.coeff source a b) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  -- NoSelfSelf + positivity excludes a = b = source.
  refine pp_r2_nap_split α hα zero source a b hsrc hza hzb ?_
  intro _
  by_contra hnot
  push Not at hnot
  obtain ⟨has, hbs⟩ := hnot
  -- a = source ∧ b = source. But coeff source source source = 0 (NoSelfSelf),
  -- contradicting coeff source a b > 0.
  have : eq.coeff source a b = 0 := by
    rw [has, hbs]; exact hnss source
  linarith

/-- **SlackStructured PP → NAP (global form)**: for every λ-trick-structured
`SynPPBalance (n+1)` with slack `zero`, every positive coefficient
`coeff source a b > 0` (with `a, b ≠ zero`) yields a balanced
non-autocatalytic split of the chain-rule production monomial for every
cubed `α` with `source ∈ supp(α)`.

This is the statement used to glue the PP-side invariant
(`SlackStructured`) to the protocol-level cubing theorem. -/
theorem synpp_r2_nap_split_of_slackStructured {n : ℕ}
    {eq : SynPPBalance n} {zero : Fin n}
    (hslack : eq.SlackStructured zero)
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (source a b : Fin n)
    (hsrc : 0 < α source)
    (hza : a ≠ zero) (hzb : b ≠ zero)
    (hpos : 0 < eq.coeff source a b) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α :=
  synpp_r2_nap_split eq hslack.noSelfSelf α hα zero source a b hsrc hza hzb hpos

/-! ### QuadField variants

Parallels of `synpp_r2_nap_split` / `synpp_r2_nap_split_of_slackStructured`
that consume a `QuadField n` directly. The proofs are identical modulo
the structure type — `pp_r2_nap_split` only needs the coefficient-tensor
properties, so both flavours reduce through the same underlying theorem. -/

/-- **QuadField PP → NAP theorem**: for a `QuadField n` satisfying
`NoSelfSelf`, every positive coefficient `F.coeff source a b > 0` (with
`a, b ≠ zero`) yields a balanced non-autocatalytic split of the chain-rule
production monomial for every cubed `α` with `source ∈ supp(α)`. -/
theorem quad_r2_nap_split {n : ℕ}
    (F : QuadField n) (hnss : F.NoSelfSelf)
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (zero source a b : Fin n)
    (hsrc : 0 < α source)
    (hza : a ≠ zero) (hzb : b ≠ zero)
    (hpos : 0 < F.coeff source a b) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  refine pp_r2_nap_split α hα zero source a b hsrc hza hzb ?_
  intro _
  by_contra hnot
  push Not at hnot
  obtain ⟨has, hbs⟩ := hnot
  -- a = source ∧ b = source. NoSelfSelf gives F.coeff source source source ≤ 0,
  -- contradicting F.coeff source a b > 0.
  have : F.coeff source a b ≤ 0 := by
    rw [has, hbs]; exact hnss source
  linarith

/-- **QuadField SlackStructured → NAP (global form)**. -/
theorem quad_r2_nap_split_of_slackStructured {n : ℕ}
    {F : QuadField n} {zero : Fin n}
    (hslack : F.SlackStructured zero)
    (α : Fin n → ℕ) (hα : IsCubedIndex α)
    (source a b : Fin n)
    (hsrc : 0 < α source)
    (hza : a ≠ zero) (hzb : b ≠ zero)
    (hpos : 0 < F.coeff source a b) :
    let μ := r2PPMonomial zero a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α :=
  quad_r2_nap_split F hslack.noSelfSelf α hα zero source a b hsrc hza hzb hpos

/-! ### End-to-end closure: SynPPBalance → λ-lift → NAP

Composes the whole loop:
`SynPPBalance n → toQuadField → lambdaLift j₀ λ → SlackStructured 0 →
quad_r2_nap_split_of_slackStructured`. The semantic BD construction requires
`λ ∈ (0, 1)` to keep both `u := λ x_{j₀}` and slack `r := (1-λ) x_{j₀}`
non-negative on the simplex; the NAP existence statement is pass-through
on that interval.

No extra hypothesis on the input PP beyond its defining invariants
(`sum_coeff = 2`, `coeff_nonneg`). -/

/-- **End-to-end PP → NAP via λ-lift**: for any `SynPPBalance n`, any split
index `j₀` and slack parameter `λ ∈ (0, 1)`, every positive coefficient of
the λ-lifted `QuadField (n+1)` yields a balanced non-autocatalytic split
for every cubed `α` with the source coordinate in its support.

The hypothesis `lam < 1` is not used inside the proof (the underlying
combinatorial split needs only positivity of the target coefficient), but
it is the semantic BD constraint: outside `(0, 1)` the split into
`u, r` leaves the non-negative cone and the construction loses meaning. -/
theorem SynPPBalance.nap_split_via_lambdaLift {n : ℕ}
    (eq : SynPPBalance n) (j₀ : Fin n) {lam : ℚ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source a b : Fin (n + 1))
    (hsrc : 0 < α source)
    (hza : a ≠ 0) (hzb : b ≠ 0)
    (hpos : 0 < (eq.toQuadField.lambdaLift j₀ lam).coeff source a b) :
    let μ := r2PPMonomial 0 a b
    let δ := fun k => (α k - if k = source then 1 else 0) + μ k
    ∃ s : MonomialSplit δ, s.balanced ∧ s.nonAutocatalytic α := by
  have _ : (0 : ℚ) < 1 - lam := by linarith
  exact quad_r2_nap_split_of_slackStructured
    (eq.toQuadField.lambdaLift_slackStructured j₀ lam
      eq.toQuadField_noSelfSelf hlam)
    α hα source a b hsrc hza hzb hpos

end Ripple
