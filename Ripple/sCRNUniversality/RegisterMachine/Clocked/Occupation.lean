/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.RegisterMachine.Clocked.Network

/-!
# Occupation measures of the clocked register-machine network

For the jump chain `rawLaw (net M L)` started at `enc a σ₀` (`docs/audit/FIX3-SCWB.md` §1, §3):

* `Z n ω` is the state after `n` jumps and `K n ω` the number of machine reactions among the
  first `n` labels; every `Z n ω` is an encoded state `enc a σ` (`Z_enc`);
* `E n k σ = {K n = k, Z n = enc a σ}`, and `occ k σ = Σ_n P(E n k σ)` is the expected number of
  visits to `(k, σ)`;
* `occ_balance`: the balance law (1.1),
  `occ k' σ' = [k' = 0, σ' = σ₀] + Σ_{k, σ} Σ_i (occ k σ / B σ) · β_i(σ) · [k + rm i = k', tgt_i σ = σ']`.
-/

namespace Ripple.sCRNUniversality.RegisterMachine.Clocked

open MeasureTheory ProbabilityTheory Preorder Stochastic Stochastic.MassAction
open scoped ENNReal

variable {Reg Label : Type} [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label]
variable {L : ℕ} (M : RM Reg Label)

/-- Total unit-rate propensity at a reduced state. -/
def Btot (a : ℕ) (σ : RState Reg Label L) : ℕ := ∑ i : Idx M L, beta M a i σ

theorem totalPropensity_enc (a : ℕ) (σ : RState Reg Label L) :
    (net M L).totalPropensity (enc a σ) = (Btot M a σ : Rate) := by
  unfold Network.totalPropensity Btot
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => propensity_enc M a i σ

variable {M}

theorem Btot_pos {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ : RState Reg Label L) :
    0 < Btot M a σ := by
  have hle : ∀ i, beta M a i σ ≤ Btot M a σ := fun i =>
    Finset.single_le_sum (f := fun i => beta M a i σ) (fun i _ => Nat.zero_le _)
      (Finset.mem_univ i)
  by_cases hc : σ.2 = 0
  · have h1 := hle (.inr (.inr (.inr (.inl ⟨0, hL⟩))))
    have hj : beta M a (.inr (.inr (.inr (.inl ⟨0, hL⟩)))) σ = a := by
      simp [beta, hc]
    omega
  · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hc
    have h1 := hle (.inr (.inr (.inr (.inr j))))
    have hb : beta M a (.inr (.inr (.inr (.inr j)))) σ = 1 := by simp [beta, hj]
    omega

theorem beta_ne_zero_of_enabled {a : ℕ} {i : Idx M L} {σ : RState Reg Label L}
    (h : ((net M L).rxn i).enabled (enc a σ)) : beta M a i σ ≠ 0 := by
  have := Reaction.propensity_ne_zero_of_enabled_of_positive_rate h (net_hasPositiveRates M L i)
  rw [propensity_enc] at this
  exact_mod_cast this

theorem enabled_of_beta_ne_zero {a : ℕ} {i : Idx M L} {σ : RState Reg Label L}
    (h : beta M a i σ ≠ 0) : ((net M L).rxn i).enabled (enc a σ) := by
  by_contra hne
  have := Reaction.propensity_eq_zero_of_not_enabled hne
  rw [propensity_enc] at this
  exact h (by exact_mod_cast this)

theorem not_terminal_enc {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ : RState Reg Label L) :
    ¬ (net M L).Terminal (enc a σ) := by
  intro hT
  obtain ⟨i, hi⟩ : ∃ i, beta M a i σ ≠ 0 := by
    by_contra h
    push Not at h
    have := Btot_pos (M := M) ha hL σ
    simp [Btot, h] at this
  exact hT i (enabled_of_beta_ne_zero hi)

theorem stateStep_enc_of_beta {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) {i : Idx M L}
    {σ : RState Reg Label L} (h : beta M a i σ ≠ 0) :
    stateStep (net M L) (enc a σ) (some i) = enc a (tgt M i σ) := by
  unfold stateStep
  rw [dif_neg (not_terminal_enc ha hL σ),
    fireOptionSanitized_of_enabled _ _ _ _ (enabled_of_beta_ne_zero h)]
  exact fire_enc M a i σ h

theorem stateStep_enc {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ : RState Reg Label L)
    (o : Option (net M L).I) : ∃ τ, stateStep (net M L) (enc a σ) o = enc a τ := by
  unfold stateStep
  rw [dif_neg (not_terminal_enc ha hL σ)]
  have hen := fireOptionSanitized_enabled (net M L) (enc a σ) o (not_terminal_enc ha hL σ)
  exact ⟨_, fire_enc M a _ σ (beta_ne_zero_of_enabled hen)⟩

/-! ### The PMF at encoded states -/

theorem pmf_enc_none {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ : RState Reg Label L) :
    massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) none = 0 := by
  change massActionWeight (net M L) (net_hasPositiveRates M L) (enc a σ) none = 0
  simp only [massActionWeight, not_terminal_enc ha hL σ, dite_false]

theorem pmf_enc_some {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ : RState Reg Label L)
    (i : Idx M L) :
    massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) (some i) =
      (beta M a i σ : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) := by
  change massActionWeight (net M L) (net_hasPositiveRates M L) (enc a σ) (some i) = _
  simp only [massActionWeight, not_terminal_enc ha hL σ, dite_false]
  have hB : (Btot M a σ : NNReal) ≠ 0 := by exact_mod_cast (Btot_pos (M := M) ha hL σ).ne'
  rw [jumpProbAt, propensity_enc, totalPropensity_enc, ← ENNReal.coe_nnratCast, NNRat.cast_div,
    NNRat.cast_natCast, NNRat.cast_natCast, ENNReal.coe_div hB, ENNReal.coe_natCast,
    ENNReal.coe_natCast]

/-! ### Paths, counters and events -/

/-- Sample space of label sequences. -/
abbrev Ω (M : RM Reg Label) (L : ℕ) := (n : ℕ) → Option (net M L).I

/-- The jump-chain law from `enc a σ₀`. -/
noncomputable def law (M : RM Reg Label) (L : ℕ) (a : ℕ) (σ₀ : RState Reg Label L) :
    Measure (Ω M L) :=
  rawLaw (net M L) (net_hasPositiveRates M L) (enc a σ₀)

instance (a : ℕ) (σ₀ : RState Reg Label L) : IsProbabilityMeasure (law M L a σ₀) :=
  rawLaw_isProbabilityMeasure _ _ _

/-- State after `n` jumps. -/
noncomputable def Z (a : ℕ) (σ₀ : RState Reg Label L) (n : ℕ) (ω : Ω M L) :
    State (Sp Reg Label L) :=
  prefixToState (net M L) (enc a σ₀) n (frestrictLe n ω)

theorem Z_zero (a : ℕ) (σ₀ : RState Reg Label L) (ω : Ω M L) : Z a σ₀ 0 ω = enc a σ₀ := rfl

theorem Z_succ (a : ℕ) (σ₀ : RState Reg Label L) (n : ℕ) (ω : Ω M L) :
    Z a σ₀ (n + 1) ω = stateStep (net M L) (Z a σ₀ n ω) (ω (n + 1)) := rfl

theorem Z_enc {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L) :
    ∀ n (ω : Ω M L), ∃ σ, Z a σ₀ n ω = enc a σ
  | 0, _ => ⟨σ₀, rfl⟩
  | n + 1, ω => by
    obtain ⟨σ, hσ⟩ := Z_enc ha hL σ₀ n ω
    rw [Z_succ, hσ]
    exact stateStep_enc ha hL σ _

/-- `1` for a machine-reaction label, else `0`. -/
def rmOpt : Option (net M L).I → ℕ
  | none => 0
  | some i => if isRM (M := M) (L := L) i then 1 else 0

/-- Number of machine-reaction labels among the first `n`. -/
def K : ℕ → Ω M L → ℕ
  | 0, _ => 0
  | n + 1, ω => K n ω + rmOpt (ω (n + 1))

theorem K_succ (n : ℕ) (ω : Ω M L) : K (n + 1) ω = K n ω + rmOpt (ω (n + 1)) := rfl

theorem K_mono (ω : Ω M L) {m n : ℕ} (h : m ≤ n) : K m ω ≤ K n ω := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_add_right _ _)

theorem rmOpt_le_one (o : Option (net M L).I) : rmOpt o ≤ 1 := by
  cases o with
  | none => simp [rmOpt]
  | some i => simp only [rmOpt]; split_ifs <;> omega

/-- The event `{K n = k, Z n = enc a σ}`. -/
def E (a : ℕ) (σ₀ : RState Reg Label L) (n k : ℕ) (σ : RState Reg Label L) : Set (Ω M L) :=
  {ω | K n ω = k ∧ Z a σ₀ n ω = enc a σ}

theorem K_det : ∀ (n : ℕ) {ω ω' : Ω M L}, frestrictLe n ω = frestrictLe n ω' → K n ω = K n ω'
  | 0, _, _, _ => rfl
  | n + 1, ω, ω', h => by
    have h1 : frestrictLe n ω = frestrictLe n ω' := by
      funext k
      have := congrFun h ⟨k.1, Finset.mem_Iic.mpr
        (le_trans (Finset.mem_Iic.mp k.2) (Nat.le_succ n))⟩
      simpa using this
    have h2 : ω (n + 1) = ω' (n + 1) := by
      have := congrFun h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
      simpa using this
    rw [K_succ, K_succ, K_det n h1, h2]

theorem Z_det (a : ℕ) (σ₀ : RState Reg Label L) (n : ℕ) {ω ω' : Ω M L}
    (h : frestrictLe n ω = frestrictLe n ω') : Z a σ₀ n ω = Z a σ₀ n ω' := by
  simp only [Z, h]

theorem mem_E_iff (a : ℕ) (σ₀ : RState Reg Label L) (n k : ℕ) (σ : RState Reg Label L)
    (ω : Ω M L) :
    ω ∈ E a σ₀ n k σ ↔ frestrictLe n ω ∈ frestrictLe n '' E a σ₀ n k σ := by
  constructor
  · intro h; exact ⟨ω, h, rfl⟩
  · rintro ⟨ω', hω', heq⟩
    exact ⟨(K_det n heq).symm.trans hω'.1, (Z_det a σ₀ n heq).symm.trans hω'.2⟩

theorem E_eq_preimage (a : ℕ) (σ₀ : RState Reg Label L) (n k : ℕ) (σ : RState Reg Label L) :
    E (M := M) a σ₀ n k σ = frestrictLe n ⁻¹' (frestrictLe n '' E a σ₀ n k σ) := by
  ext ω; exact mem_E_iff a σ₀ n k σ ω

theorem measurableSet_E (a : ℕ) (σ₀ : RState Reg Label L) (n k : ℕ) (σ : RState Reg Label L) :
    MeasurableSet (E (M := M) a σ₀ n k σ) := by
  rw [E_eq_preimage]
  exact measurable_frestrictLe n (measurableSet_prefixSet _ _ _)

theorem measurableSet_label (n : ℕ) (o : Option (net M L).I) :
    MeasurableSet {ω : Ω M L | ω n = o} :=
  measurableSet_eq_fun (measurable_pi_apply n) measurable_const

/-- **One-step Markov property for the events `E`.** -/
theorem law_E_label (a : ℕ) (σ₀ : RState Reg Label L) (n k : ℕ) (σ : RState Reg Label L)
    (o : Option (net M L).I) :
    law M L a σ₀ (E a σ₀ n k σ ∩ {ω | ω (n + 1) = o}) =
      law M L a σ₀ (E a σ₀ n k σ) *
        massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) o := by
  have h := rawLaw_prefix_next (net M L) (net_hasPositiveRates M L) (enc a σ₀) n
    (frestrictLe n '' E a σ₀ n k σ) (enc a σ) (by
      rintro p ⟨ω, ⟨_, hZ⟩, rfl⟩
      exact hZ) o
  have h1 : {ω : Ω M L | frestrictLe n ω ∈ frestrictLe n '' E a σ₀ n k σ ∧ ω (n + 1) = o} =
      E a σ₀ n k σ ∩ {ω | ω (n + 1) = o} := by
    ext ω; exact and_congr (mem_E_iff a σ₀ n k σ ω).symm Iff.rfl
  have h2 : {ω : Ω M L | frestrictLe n ω ∈ frestrictLe n '' E a σ₀ n k σ} = E a σ₀ n k σ := by
    ext ω; exact (mem_E_iff a σ₀ n k σ ω).symm
  rw [h1, h2] at h
  exact h

/-- The events `E n k σ` partition the sample space. -/
theorem law_eq_tsum_E {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L) (n : ℕ)
    (S : Set (Ω M L)) (hS : MeasurableSet S) :
    law M L a σ₀ S = ∑' ξ : ℕ × RState Reg Label L, law M L a σ₀ (S ∩ E a σ₀ n ξ.1 ξ.2) := by
  have hcover : S = ⋃ ξ : ℕ × RState Reg Label L, S ∩ E a σ₀ n ξ.1 ξ.2 := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hω
      obtain ⟨σ, hσ⟩ := Z_enc ha hL σ₀ n ω
      exact ⟨(K n ω, σ), hω, rfl, hσ⟩
    · rintro ⟨_, hω, _⟩; exact hω
  conv_lhs => rw [hcover]
  refine measure_iUnion ?_ fun ξ => hS.inter (measurableSet_E a σ₀ n ξ.1 ξ.2)
  intro ξ ξ' hne
  refine Set.disjoint_left.mpr ?_
  rintro ω ⟨_, hK, hZ⟩ ⟨_, hK', hZ'⟩
  apply hne
  refine Prod.ext (hK.symm.trans hK') (enc_injective a (hZ.symm.trans hZ'))

/-- Labels at step `n+1` partition the sample space. -/
theorem law_eq_sum_label (a : ℕ) (σ₀ : RState Reg Label L) (n : ℕ) (S : Set (Ω M L))
    (hS : MeasurableSet S) :
    law M L a σ₀ S = ∑ o : Option (net M L).I, law M L a σ₀ (S ∩ {ω | ω (n + 1) = o}) := by
  have hcover : S = ⋃ o : Option (net M L).I, S ∩ {ω | ω (n + 1) = o} := by
    ext ω; simp
  conv_lhs => rw [hcover]
  rw [measure_iUnion, tsum_fintype]
  · intro o o' hne
    refine Set.disjoint_left.mpr ?_
    rintro ω ⟨_, h⟩ ⟨_, h'⟩
    exact hne (h.symm.trans h')
  · exact fun o => hS.inter (measurableSet_label _ o)

/-- Transition weight from `(k, σ)` by label `o` to `ξ'`. -/
noncomputable def trans (a : ℕ) (k : ℕ) (σ : RState Reg Label L) (o : Option (net M L).I)
    (ξ' : ℕ × RState Reg Label L) : ℝ≥0∞ :=
  match o with
  | none => 0
  | some i => if (k + rmOpt (M := M) (some i), tgt M i σ) = ξ' then
      (beta M a i σ : ℝ≥0∞) / (Btot M a σ : ℝ≥0∞) else 0

theorem law_E_label_E {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L) (n k : ℕ)
    (σ : RState Reg Label L) (o : Option (net M L).I) (ξ' : ℕ × RState Reg Label L) :
    law M L a σ₀ (E a σ₀ (n + 1) ξ'.1 ξ'.2 ∩ E a σ₀ n k σ ∩ {ω | ω (n + 1) = o}) =
      law M L a σ₀ (E a σ₀ n k σ) * trans (M := M) a k σ o ξ' := by
  have hsub : E a σ₀ (n + 1) ξ'.1 ξ'.2 ∩ E a σ₀ n k σ ∩ {ω | ω (n + 1) = o} ⊆
      E a σ₀ n k σ ∩ {ω | ω (n + 1) = o} := fun ω h => ⟨h.1.2, h.2⟩
  have hzero : massActionPMF (net M L) (net_hasPositiveRates M L) (enc a σ) o = 0 →
      law M L a σ₀ (E a σ₀ (n + 1) ξ'.1 ξ'.2 ∩ E a σ₀ n k σ ∩ {ω | ω (n + 1) = o}) = 0 := by
    intro h0
    refine le_antisymm ?_ zero_le
    calc _ ≤ law M L a σ₀ (E a σ₀ n k σ ∩ {ω | ω (n + 1) = o}) := measure_mono hsub
      _ = 0 := by rw [law_E_label, h0, mul_zero]
  cases o with
  | none =>
    rw [hzero (pmf_enc_none ha hL σ)]
    simp [trans]
  | some i =>
    by_cases hβ : beta M a i σ = 0
    · rw [hzero (by rw [pmf_enc_some ha hL]; simp [hβ])]
      simp [trans, hβ]
    · -- the step lands in `E (n+1) (k + rm i) (tgt i σ)`
      have hstep : E a σ₀ n k σ ∩ {ω | ω (n + 1) = some i} ⊆
          E a σ₀ (n + 1) (k + rmOpt (M := M) (some i)) (tgt M i σ) := by
        rintro ω ⟨⟨hK, hZ⟩, ho⟩
        refine ⟨?_, ?_⟩
        · rw [K_succ, hK]; simp only [Set.mem_setOf_eq] at ho; rw [ho]
        · rw [Z_succ, hZ]; simp only [Set.mem_setOf_eq] at ho; rw [ho]
          exact stateStep_enc_of_beta ha hL hβ
      by_cases hξ : (k + rmOpt (M := M) (some i), tgt M i σ) = ξ'
      · have hset : E a σ₀ (n + 1) ξ'.1 ξ'.2 ∩ E a σ₀ n k σ ∩ {ω | ω (n + 1) = some i} =
            E a σ₀ n k σ ∩ {ω | ω (n + 1) = some i} := by
          refine Set.Subset.antisymm hsub fun ω hω => ⟨⟨?_, hω.1⟩, hω.2⟩
          rw [← hξ]; exact hstep hω
        rw [hset, law_E_label, pmf_enc_some ha hL]
        simp [trans, hξ]
      · have hset : E a σ₀ (n + 1) ξ'.1 ξ'.2 ∩ E a σ₀ n k σ ∩ {ω | ω (n + 1) = some i} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω => hξ ?_
          have h1 := hstep ⟨hω.1.2, hω.2⟩
          exact Prod.ext (h1.1.symm.trans hω.1.1.1)
            (enc_injective a (h1.2.symm.trans hω.1.1.2))
        rw [hset, measure_empty]
        simp [trans, hξ]

/-- **One-step recursion** for `P(E n k σ)`. -/
theorem law_E_succ {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L) (n : ℕ)
    (ξ' : ℕ × RState Reg Label L) :
    law M L a σ₀ (E a σ₀ (n + 1) ξ'.1 ξ'.2) =
      ∑' ξ : ℕ × RState Reg Label L, ∑ o : Option (net M L).I,
        law M L a σ₀ (E a σ₀ n ξ.1 ξ.2) * trans (M := M) a ξ.1 ξ.2 o ξ' := by
  rw [law_eq_tsum_E ha hL σ₀ n _ (measurableSet_E a σ₀ _ _ _)]
  refine tsum_congr fun ξ => ?_
  rw [law_eq_sum_label a σ₀ n _ ((measurableSet_E a σ₀ _ _ _).inter (measurableSet_E a σ₀ _ _ _))]
  exact Finset.sum_congr rfl fun o _ => law_E_label_E ha hL σ₀ n ξ.1 ξ.2 o ξ'

theorem law_E_zero (a : ℕ) (σ₀ : RState Reg Label L) (ξ : ℕ × RState Reg Label L) :
    law M L a σ₀ (E a σ₀ 0 ξ.1 ξ.2) = if ξ = (0, σ₀) then 1 else 0 := by
  by_cases h : ξ = (0, σ₀)
  · have : E (M := M) a σ₀ 0 ξ.1 ξ.2 = Set.univ := by
      ext ω; simp [E, h, K, Z_zero]
    rw [if_pos h, this, measure_univ]
  · have : E (M := M) a σ₀ 0 ξ.1 ξ.2 = ∅ := by
      ext ω
      simp only [E, K, Z_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hk hσ
      exact h (Prod.ext hk.symm (enc_injective a hσ).symm)
    rw [if_neg h, this, measure_empty]

/-- Expected number of visits to `(k, σ)`. -/
noncomputable def occ (a : ℕ) (σ₀ : RState Reg Label L) (ξ : ℕ × RState Reg Label L) : ℝ≥0∞ :=
  ∑' n, law M L a σ₀ (E a σ₀ n ξ.1 ξ.2)

/-- **Balance law** (FIX3-SCWB (1.1)). -/
theorem occ_balance {a : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L) (σ₀ : RState Reg Label L)
    (ξ' : ℕ × RState Reg Label L) :
    occ (M := M) a σ₀ ξ' = (if ξ' = (0, σ₀) then 1 else 0) +
      ∑' ξ : ℕ × RState Reg Label L, ∑ o : Option (net M L).I,
        occ (M := M) a σ₀ ξ * trans (M := M) a ξ.1 ξ.2 o ξ' := by
  unfold occ
  rw [tsum_eq_zero_add' ENNReal.summable, law_E_zero]
  congr 1
  conv_lhs => enter [1, n]; rw [law_E_succ ha hL σ₀ n ξ']
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun ξ => ?_
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact Finset.sum_congr rfl fun o _ => ENNReal.tsum_mul_right

end Ripple.sCRNUniversality.RegisterMachine.Clocked
