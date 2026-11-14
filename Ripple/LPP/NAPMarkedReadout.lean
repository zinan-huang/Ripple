-- Ripple/LPP/NAPMarkedReadout.lean
/-
# Marked readout of the cubing construction

The marked lifted species are precisely the degree-three multi-indices supported on the
successors of the original marked set. Their total concentration is the cube of the original
marked mass when the shrunk set is disjoint from the marked set.

This file is an additive extension of `NAPPipelineSet`.
-/

import Ripple.LPP.NAPPipelineSet
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace Ripple
namespace NAPTransport

open Set Filter Topology Finset

/-- Cubic multi-indices whose positive exponents all lie in `S`. -/
def supportedCubicSet (m : ℕ) (S : Finset (Fin m)) : Finset (MI m 3) :=
  Finset.univ.filter fun α => ∀ j, 0 < (α.1 j : ℕ) → j ∈ S

@[simp] theorem mem_supportedCubicSet (m : ℕ) (S : Finset (Fin m)) (α : MI m 3) :
    α ∈ supportedCubicSet m S ↔ ∀ j, 0 < (α.1 j : ℕ) → j ∈ S := by
  simp only [supportedCubicSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Masking coordinates outside `S` removes exactly the unsupported Veronese monomials. -/
theorem ver_mask_eq (m : ℕ) (S : Finset (Fin m)) (x : Fin m → ℝ) (α : MI m 3) :
    ver m (fun j => if j ∈ S then x j else 0) α =
      if α ∈ supportedCubicSet m S then ver m x α else 0 := by
  classical
  by_cases hα : α ∈ supportedCubicSet m S
  · rw [if_pos hα]
    have hs := (mem_supportedCubicSet m S α).mp hα
    unfold ver
    apply congrArg (fun q : ℝ => (MI.mult m 3 α : ℝ) * q)
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j ∈ S
    · simp only [if_pos hj]
    · have hz : (α.1 j : ℕ) = 0 := by
        by_contra hn
        exact hj (hs j (Nat.pos_of_ne_zero hn))
      simp only [if_neg hj, hz, pow_zero]
  · rw [if_neg hα]
    have hs : ¬ ∀ j, 0 < (α.1 j : ℕ) → j ∈ S := by
      intro hs
      exact hα ((mem_supportedCubicSet m S α).mpr hs)
    push_neg at hs
    obtain ⟨j, hj, hjS⟩ := hs
    unfold ver
    have hz : ∏ k, (if k ∈ S then x k else 0) ^ (α.1 k : ℕ) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [if_neg hjS]
      exact zero_pow (Nat.ne_of_gt hj)
    rw [hz, mul_zero]

/-- The multinomial theorem restricted to a set of coordinates. No simplex hypothesis is needed. -/
theorem sum_supportedCubicSet_ver (m : ℕ) (S : Finset (Fin m)) (x : Fin m → ℝ) :
    ∑ α ∈ supportedCubicSet m S, ver m x α = (∑ j ∈ S, x j) ^ 3 := by
  classical
  calc
    ∑ α ∈ supportedCubicSet m S, ver m x α =
        ∑ α, if α ∈ supportedCubicSet m S then ver m x α else 0 :=
      (sum_ite_mem_univ (supportedCubicSet m S) (ver m x)).symm
    _ = ∑ α, ver m (fun j => if j ∈ S then x j else 0) α := by
      apply Finset.sum_congr rfl
      intro α _
      exact (ver_mask_eq m S x α).symm
    _ = (∑ j, if j ∈ S then x j else 0) ^ 3 := sum_ver_eq _
    _ = (∑ j ∈ S, x j) ^ 3 := by rw [sum_ite_mem_univ]

/-- A singleton support leaves exactly the pure cubic species. -/
theorem supportedCubicSet_singleton (m : ℕ) (j : Fin m) :
    supportedCubicSet m {j} = {MI.pow m 3 j} := by
  ext α
  constructor
  · intro hα
    have hs := (mem_supportedCubicSet m {j} α).mp hα
    apply Finset.mem_singleton.mpr
    have hz : ∀ k : Fin m, k ≠ j → (α.1 k : ℕ) = 0 := by
      intro k hkj
      by_contra hk
      exact hkj (Finset.mem_singleton.mp (hs k (Nat.pos_of_ne_zero hk)))
    have hj : (α.1 j : ℕ) = 3 := by
      have hsum : ∑ k, (α.1 k : ℕ) = (α.1 j : ℕ) := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          exact hz k hkj
        · intro hj
          exact False.elim (hj (Finset.mem_univ j))
      exact hsum.symm.trans α.2
    apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [MI.pow, MI.ofFun_val]
    by_cases hkj : k = j
    · subst k
      simpa only [if_pos rfl] using hj
    · rw [if_neg hkj]
      exact hz k hkj
  · intro hα
    have heq : α = MI.pow m 3 j := Finset.mem_singleton.mp hα
    subst α
    apply (mem_supportedCubicSet m {j} (MI.pow m 3 j)).mpr
    intro k hk
    by_cases hkj : k = j
    · exact Finset.mem_singleton.mpr hkj
    · simp only [MI.pow, MI.ofFun_val, if_neg hkj] at hk
      omega

/-- The original marked coordinates, embedded after the slack coordinate `0`. -/
def markedSuccSet (n : ℕ) (M : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  M.image Fin.succ

@[simp] theorem markedSuccSet_singleton (n : ℕ) (j : Fin n) :
    markedSuccSet n {j} = {j.succ} := by
  simp only [markedSuccSet, Finset.image_singleton]

@[simp] theorem mem_markedSuccSet (n : ℕ) (M : Finset (Fin n)) (j : Fin n) :
    j.succ ∈ markedSuccSet n M ↔ j ∈ M := by
  change j.succ ∈ M.image Fin.succ ↔ j ∈ M
  constructor
  · intro h
    obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp h
    have hkj' : k = j := Fin.succ_inj.mp hkj
    simpa only [hkj'] using hk
  · intro hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

@[simp] theorem zero_not_mem_markedSuccSet (n : ℕ) (M : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∉ markedSuccSet n M := by
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
  exact Fin.succ_ne_zero j hj

/-- The genuine marked subset of cubic species: all three slots belong to `M`. -/
def markedCubicSet (n : ℕ) (M : Finset (Fin n)) : Finset (MI (n + 1) 3) :=
  supportedCubicSet (n + 1) (markedSuccSet n M)

/-- For an original marked singleton, the new marked set is one pure cubic species. -/
@[simp] theorem markedCubicSet_singleton (n : ℕ) (j : Fin n) :
    markedCubicSet n {j} = {MI.pow (n + 1) 3 j.succ} := by
  unfold markedCubicSet
  rw [markedSuccSet_singleton, supportedCubicSet_singleton]

@[simp] theorem mem_markedCubicSet (n : ℕ) (M : Finset (Fin n))
    (α : MI (n + 1) 3) :
    α ∈ markedCubicSet n M ↔
      ∀ j, 0 < (α.1 j : ℕ) → j ∈ markedSuccSet n M := by
  exact mem_supportedCubicSet (n + 1) (markedSuccSet n M) α

/-- In particular the slack exponent vanishes in every marked cubic species. -/
theorem mem_markedCubicSet_iff (n : ℕ) (M : Finset (Fin n))
    (α : MI (n + 1) 3) :
    α ∈ markedCubicSet n M ↔
      (α.1 0 : ℕ) = 0 ∧ ∀ j : Fin n, 0 < (α.1 j.succ : ℕ) → j ∈ M := by
  rw [mem_markedCubicSet]
  constructor
  · intro h
    constructor
    · by_contra hz
      exact zero_not_mem_markedSuccSet n M (h 0 (Nat.pos_of_ne_zero hz))
    · intro j hj
      exact (mem_markedSuccSet n M j).mp (h j.succ hj)
  · intro h j
    induction j using Fin.cases with
    | zero =>
        intro hj
        have hz := h.1
        omega
    | succ j =>
        intro hj
        exact (mem_markedSuccSet n M j).mpr (h.2 j hj)

/-- A shrunk set contained in the unmarked coordinates is disjoint from `M`. -/
theorem marked_disjoint_of_subset_compl (n : ℕ) (M J : Finset (Fin n))
    (hJM : J ⊆ Mᶜ) : Disjoint M J := by
  apply Finset.disjoint_left.mpr
  intro j hjM hjJ
  exact (Finset.mem_compl.mp (hJM hjJ)) hjM

/-- The slack map leaves the total original marked mass unchanged when only unmarked
coordinates are shrunk. -/
theorem sum_markedSuccSet_slackMapSet (n : ℕ) (M J : Finset (Fin n))
    (hJM : J ⊆ Mᶜ) (lam : ℝ) (x : Fin n → ℝ) :
    ∑ j' ∈ markedSuccSet n M, slackMapSet n J lam x j' = ∑ j ∈ M, x j := by
  unfold markedSuccSet
  rw [Finset.sum_image (fun a _ b _ hab => Fin.succ_inj.mp hab)]
  apply Finset.sum_congr rfl
  intro j hjM
  have hjJ : j ∉ J := by
    intro hjJ
    exact (Finset.mem_compl.mp (hJM hjJ)) hjM
  simp only [slackMapSet_succ, if_neg hjJ, one_mul]

/-- **Marked cubic identity.** This is a subset sum with coefficients in `{0,1}`, and its
value is the cube of the original marked mass. It is a polynomial identity for every `x`
and every real `lam`; the pipeline restrictions on `lam` are only needed for dynamics. -/
theorem sum_markedCubicSet_ver_slackMapSet (n : ℕ) (M J : Finset (Fin n))
    (hJM : J ⊆ Mᶜ) (lam : ℝ) (x : Fin n → ℝ) :
    ∑ α ∈ markedCubicSet n M, ver (n + 1) (slackMapSet n J lam x) α =
      (∑ j ∈ M, x j) ^ 3 := by
  unfold markedCubicSet
  rw [sum_supportedCubicSet_ver, sum_markedSuccSet_slackMapSet n M J hJM lam x]

/-- The singleton special case is a single concentration, provided that the chosen original
coordinate is not shrunk. Existence of a protocol with a singleton readout is not assumed by
the general pipeline theorem. -/
theorem ver_slackMapSet_pure_marked (n : ℕ) (j : Fin n) (J : Finset (Fin n))
    (hjJ : j ∉ J) (lam : ℝ) (x : Fin n → ℝ) :
    ver (n + 1) (slackMapSet n J lam x) (MI.pow (n + 1) 3 j.succ) = x j ^ 3 := by
  have hJM : J ⊆ ({j} : Finset (Fin n))ᶜ := by
    intro k hk
    apply Finset.mem_compl.mpr
    intro hkj
    have heq : k = j := Finset.mem_singleton.mp hkj
    subst k
    exact hjJ hk
  have h := sum_markedCubicSet_ver_slackMapSet n {j} J hJM lam x
  simpa only [markedCubicSet_singleton, Finset.sum_singleton] using h

/-- The same one-species identity along the actual form of the pipeline trajectory. -/
theorem single_marked_cubic_trajectory (n : ℕ) (j : Fin n) (J : Finset (Fin n))
    (hjJ : j ∉ J) (lam : ℝ) (x : ℝ → Fin n → ℝ) (τ : ℝ → ℝ) (t : ℝ) :
    ver (n + 1) (slackMapSet n J lam (x (τ t))) (MI.pow (n + 1) 3 j.succ) =
      x (τ t) j ^ 3 :=
  ver_slackMapSet_pure_marked n j J hjJ lam (x (τ t))

/-- Indicator weights of an original marked subset. -/
def markedIndicator (n : ℕ) (M : Finset (Fin n)) (j : Fin n) : ℝ :=
  if j ∈ M then 1 else 0

theorem sum_markedIndicator (n : ℕ) (M : Finset (Fin n)) (x : Fin n → ℝ) :
    ∑ j, markedIndicator n M j * x j = ∑ j ∈ M, x j := by
  simp only [markedIndicator, ite_mul, one_mul, zero_mul]
  exact sum_ite_mem_univ M x

theorem markedIndicator_eq_zero_on (n : ℕ) (M J : Finset (Fin n))
    (hJM : J ⊆ Mᶜ) : ∀ j ∈ J, markedIndicator n M j = 0 := by
  intro j hj
  exact if_neg (Finset.mem_compl.mp (hJM hj))

/-- Coordinate nonnegativity of the slack map, including the endpoint scaling factors. -/
theorem slackMapSet_nonneg (n : ℕ) (J : Finset (Fin n)) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) : ∀ j', 0 ≤ slackMapSet n J lam x j' := by
  intro j'
  induction j' using Fin.cases with
  | zero =>
      rw [slackMapSet_zero]
      exact mul_nonneg (sub_nonneg.mpr hlam1) (Finset.sum_nonneg fun j _ => hx j)
  | succ j =>
      rw [slackMapSet_succ]
      apply mul_nonneg _ (hx j)
      split_ifs
      · exact hlam0
      · norm_num

theorem ver_nonneg (m : ℕ) (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (α : MI m 3) :
    0 ≤ ver m x α := by
  unfold ver
  apply mul_nonneg
  · exact_mod_cast (MI.mult_pos m 3 α).le
  · exact Finset.prod_nonneg fun j _ => pow_nonneg (hx j) _

/-- The explicit lifted initial point and trajectory lie in the lifted simplex. -/
theorem ver_slackMapSet_simplex (n : ℕ) (J : Finset (Fin n)) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hxs : ∑ j, x j = 1) :
    (∀ α, 0 ≤ ver (n + 1) (slackMapSet n J lam x) α) ∧
      ∑ α, ver (n + 1) (slackMapSet n J lam x) α = 1 := by
  constructor
  · exact ver_nonneg (n + 1) _ (slackMapSet_nonneg n J lam hlam0 hlam1 x hx)
  · rw [sum_ver_eq, sum_slackMapSet, hxs, one_pow]

/-- A marked sum of a simplex point belongs to the unit interval. -/
theorem markedMass_mem_unitInterval (n : ℕ) (M : Finset (Fin n)) (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hxs : ∑ j, x j = 1) :
    0 ≤ ∑ j ∈ M, x j ∧ ∑ j ∈ M, x j ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun j _ => hx j
  · rw [← hxs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M) fun j _ _ => hx j

/-- When the shrunk set is exactly the complement, its mass is one minus the marked mass.
A mere subset of the complement does not satisfy this identity. -/
theorem sum_compl_eq_one_sub_marked (n : ℕ) (M : Finset (Fin n)) (x : Fin n → ℝ)
    (hxs : ∑ j, x j = 1) :
    ∑ j ∈ Mᶜ, x j = 1 - ∑ j ∈ M, x j := by
  have h := Finset.sum_add_sum_compl M x
  rw [hxs] at h
  linarith

/-- The limiting mass `1 - ν` is available for the full complement. -/
theorem complement_markedMass_tendsto (n : ℕ) (M : Finset (Fin n))
    {x : ℝ → Fin n → ℝ} {ν : ℝ}
    (hxs : ∀ s, 0 ≤ s → ∑ j, x s j = 1)
    (hν : Tendsto (fun s => ∑ j ∈ M, x s j) atTop (𝓝 ν)) :
    Tendsto (fun s => ∑ j ∈ Mᶜ, x s j) atTop (𝓝 (1 - ν)) := by
  have h : Tendsto (fun s => 1 - ∑ j ∈ M, x s j) atTop (𝓝 (1 - ν)) :=
    tendsto_const_nhds.sub hν
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact (sum_compl_eq_one_sub_marked n M (x s) (hxs s hs)).symm

/-- Cubing is 3-Lipschitz on the unit interval. -/
theorem abs_cube_sub_cube_le {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |a ^ 3 - b ^ 3| ≤ 3 * |a - b| := by
  have haSq : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hbSq : b ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]
  have hab : a * b ≤ 1 := mul_le_one₀ ha1 hb0 hb1
  have hf0 : 0 ≤ a ^ 2 + a * b + b ^ 2 :=
    add_nonneg (add_nonneg (sq_nonneg a) (mul_nonneg ha0 hb0)) (sq_nonneg b)
  have hf1 : a ^ 2 + a * b + b ^ 2 ≤ 3 := by linarith
  have hfactor : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  calc
    |a ^ 3 - b ^ 3| = |a - b| * (a ^ 2 + a * b + b ^ 2) := by
      rw [hfactor, abs_mul, abs_of_nonneg hf0]
    _ ≤ |a - b| * 3 := mul_le_mul_of_nonneg_left hf1 (abs_nonneg _)
    _ = 3 * |a - b| := mul_comm _ _

/-- Any clock tending to infinity transfers convergence of the marked mass to convergence of
the marked cubic subset sum, with the target cubed. -/
theorem markedCubicSet_tendsto (n : ℕ) (M J : Finset (Fin n))
    (hJM : J ⊆ Mᶜ) (lam : ℝ) {x : ℝ → Fin n → ℝ} {τ : ℝ → ℝ} {ν : ℝ}
    (hτ : Tendsto τ atTop atTop)
    (hx : Tendsto (fun s => ∑ j ∈ M, x s j) atTop (𝓝 ν)) :
    Tendsto (fun t => ∑ α ∈ markedCubicSet n M,
      ver (n + 1) (slackMapSet n J lam (x (τ t))) α) atTop (𝓝 (ν ^ 3)) := by
  have heq : (fun t => ∑ α ∈ markedCubicSet n M,
      ver (n + 1) (slackMapSet n J lam (x (τ t))) α) =
      fun t => (∑ j ∈ M, x (τ t) j) ^ 3 := by
    funext t
    exact sum_markedCubicSet_ver_slackMapSet n M J hJM lam (x (τ t))
  rw [heq]
  exact (hx.comp hτ).pow 3

end NAPTransport
end Ripple
