/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stages A′, B56 and B56M: sorting and decision on `S_rank` (P3 Lemmas 12, 13, 14)

* `sortDecide_bound` (P3 Lemmas 12, 13): from a class `Good ⊆ S_rank` whose steps stay in `Good`
  or land in an escape class `E`, the goal `(D ∩ Good) ∪ E` is missed within `23 n²` interactions
  with probability at most `π²/120 + 0.002479`. First `20 n²` steps: sorting. The number `J` of
  B-agents below rank `n_A` never increases and drops at the `J²` ordered pairs (B-agent below
  `n_A`, A-agent at or above `n_A`) (`srank_step_misB`, `card_VA_eq`); the potential
  `Φ = Σ_{i ≤ J} n(n-1)/i²` has drift at least `1` (`srank_sort_drift`), so P2 Lemma 1.4 gives
  failure at most `Φ/(20 n²) ≤ (π²/6) n(n-1)/(20 n²) < π²/120` (`hasSum_zeta_two`). Next `3 n²`
  steps: two ordered decision pairs decide (`ssorted_step_decide`), failure at most `e^{-6}`.
* `stageA' : StageA'` (P3 Lemma 13): `Good = S_rank`, `E = PT_L` (a reset lands in `PT_L`).
* `tick_hit_bound` (P3 Lemma 14, tick bound): from `R(99)`, the median timer drops below `6`
  within `23 n²` interactions with probability at most `10⁻⁶` (stopped potential `2^(99 - medT)`,
  `E[2^{ticks}] ≤ (1 + 2/(n(n-1)))^(23 n²) ≤ e^{47}`, against `2^94`); no reset happens before
  (`srank_step_srank_of_medT`).
* `stageB56 : StageB56`, `stageB56M : StageB56M` (P3 Lemma 14 with `θ = 99`): `Good = S_rank ∩
  {medT ≥ 6}` (and `AnsOK` for B56M, kept by non-reset steps, `ansOK_step`), `E = ¬ Good`; union
  bound with the tick bound.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.StagesSRankC
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

/-! ### Counting misplaced agents -/

/-- B-agents of rank below `n_A`. -/
def setVB (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => (C w).2 = .B ∧ (C w).1.rank.val < nAOf C)

/-- A-agents of rank at least `n_A`. -/
def setVA (C : Config (AgentState n) Opinion n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => (C w).2 = .A ∧ nAOf C ≤ (C w).1.rank.val)

theorem misB_eq_card (C : Config (AgentState n) Opinion n) : misB C = (setVB C).card := by
  simp only [misB, setVB, misTerm, Finset.card_filter]

/-- On `S_rank`, exactly `k` agents have rank below `k`. -/
theorem card_rank_lt {C : Config (AgentState n) Opinion n} (hC : SRank C) (k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun w => (C w).1.rank.val < k)).card = k := by
  have hbij : Function.Bijective (fun w => (C w).1.rank) :=
    ⟨hC.2, Finite.injective_iff_surjective.mp hC.2⟩
  calc (Finset.univ.filter (fun w => (C w).1.rank.val < k)).card
      = ∑ w, (if (C w).1.rank.val < k then 1 else 0) := Finset.card_filter _ _
    _ = ∑ r : Fin n, (if r.val < k then 1 else 0) :=
        hbij.sum_comp (fun r : Fin n => if r.val < k then (1 : ℕ) else 0)
    _ = (Finset.univ.filter (fun r : Fin n => r.val < k)).card := (Finset.card_filter _ _).symm
    _ = k := by rw [Fin.card_filter_val_lt]; omega

/-- On `S_rank`, as many A-agents sit at or above `n_A` as B-agents below `n_A`. -/
theorem card_VA_eq {C : Config (AgentState n) Opinion n} (hC : SRank C) :
    (setVA C).card = (setVB C).card := by
  have hL := card_rank_lt hC (nAOf C) (nAOf_le C)
  have hA : (Finset.univ.filter (fun w => (C w).2 = .A)).card = nAOf C := rfl
  have s1 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun w => (C w).1.rank.val < nAOf C)) (fun w => (C w).2 = .A)
  have s2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun w => (C w).2 = .A)) (fun w => (C w).1.rank.val < nAOf C)
  rw [Finset.filter_filter, Finset.filter_filter] at s1 s2
  have e1 : Finset.univ.filter (fun w => (C w).1.rank.val < nAOf C ∧ (C w).2 = .A) =
      Finset.univ.filter (fun w => (C w).2 = .A ∧ (C w).1.rank.val < nAOf C) :=
    Finset.filter_congr (fun w _ => and_comm)
  have e2 : Finset.univ.filter (fun w => (C w).1.rank.val < nAOf C ∧ ¬ (C w).2 = .A) =
      setVB C := by
    unfold setVB
    refine Finset.filter_congr (fun w _ => ?_)
    cases (C w).2 <;> simp [and_comm]
  have e3 : Finset.univ.filter (fun w => (C w).2 = .A ∧ ¬ (C w).1.rank.val < nAOf C) =
      setVA C := by
    unfold setVA
    exact Finset.filter_congr (fun w _ => by rw [not_lt])
  rw [e1, e2, hL] at s1
  rw [e3, hA] at s2
  omega

/-! ### The sorting potential -/

/-- `Φ(j) = n(n-1) Σ_{i < j} 1/(i+1)²` (P3 Lemma 12). -/
noncomputable def phiR (n j : ℕ) : ℝ := npairs n * ∑ i ∈ Finset.range j, 1 / ((i : ℝ) + 1) ^ 2

theorem phiR_succ (n j : ℕ) : phiR n (j + 1) = phiR n j + npairs n / ((j : ℝ) + 1) ^ 2 := by
  unfold phiR
  rw [Finset.sum_range_succ]
  ring

theorem phiR_nonneg (n j : ℕ) (hN : 0 ≤ npairs n) : 0 ≤ phiR n j := by
  unfold phiR
  apply mul_nonneg hN
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem phiR_mono (n : ℕ) (hN : 0 ≤ npairs n) {j k : ℕ} (h : j ≤ k) : phiR n j ≤ phiR n k := by
  unfold phiR
  apply mul_le_mul_of_nonneg_left _ hN
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro i _ _
  positivity

/-- `Φ(j) ≤ n(n-1) π²/6` (`hasSum_zeta_two`). -/
theorem phiR_le (n j : ℕ) (hN : 0 ≤ npairs n) : phiR n j ≤ npairs n * (Real.pi ^ 2 / 6) := by
  unfold phiR
  apply mul_le_mul_of_nonneg_left _ hN
  have e : ∑ i ∈ Finset.range j, 1 / ((i : ℝ) + 1) ^ 2 =
      ∑ i ∈ Finset.range (j + 1), 1 / ((i : ℕ) : ℝ) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp
  rw [e]
  exact sum_le_hasSum _ (fun i _ => by positivity) hasSum_zeta_two

/-- **Sorting drift** (P3 Lemma 12): on `S_rank` outside `S_sw`, the potential
`Φ(misB)` drops by at least `1` in mean per step. -/
theorem srank_sort_drift {hn : 0 < n} (hn2 : 2 ≤ n) {C : Config (AgentState n) Opinion n}
    (hC : SRank C) (hns : ¬ SSorted C) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        ENNReal.ofReal (phiR n (misB (C.step (PEM40 n hn) p.1 p.2))) + 1 ≤
      ENNReal.ofReal (phiR n (misB C)) := by
  have hN := two_le_npairs hn2
  have hN0 : (0 : ℝ) ≤ npairs n := by linarith
  have hNne : npairs n ≠ 0 := by linarith
  have hcard := card_VA_eq hC
  -- at least one misplaced B-agent
  have hj : 1 ≤ misB C := by
    rw [misB_eq_card]
    by_contra h0
    apply hns
    have hB : setVB C = ∅ := Finset.card_eq_zero.mp (by omega)
    have hA : setVA C = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨hC, fun w => ⟨fun hw => ?_, fun hlt => ?_⟩⟩
    · by_contra hlt
      have hmem : w ∈ setVA C := by
        simp only [setVA, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hw, by omega⟩
      rw [hA] at hmem
      simp at hmem
    · cases hx : (C w).2
      · rfl
      · have hmem : w ∈ setVB C := by
          simp only [setVB, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hx, hlt⟩
        rw [hB] at hmem
        simp at hmem
  obtain ⟨k, hk⟩ : ∃ k, misB C = k + 1 := ⟨misB C - 1, by omega⟩
  have hSoff : ∀ p ∈ setVB C ×ˢ setVA C, p.1 ≠ p.2 := by
    intro p hp h
    rw [Finset.mem_product] at hp
    simp only [setVB, setVA, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [h] at hp
    have := hp.1.1.symm.trans hp.2.1
    cases this
  have hScard : (setVB C ×ˢ setVA C).card = (k + 1) * (k + 1) := by
    rw [Finset.card_product, hcard, ← misB_eq_card, hk]
  have hmass : ∑ p ∈ setVB C ×ˢ setVA C, uniformPair n hn2 p =
      ENNReal.ofReal ((((k + 1) * (k + 1) : ℕ) : ℝ) / npairs n) := by
    rw [uniformPair_mass_card hn2 _ hSoff, hScard]
    rfl
  have hlow : ∀ p ∈ setVB C ×ˢ setVA C,
      ENNReal.ofReal (phiR n (misB (C.step (PEM40 n hn) p.1 p.2))) ≤
        ENNReal.ofReal (phiR n k) := by
    intro p hp
    apply ENNReal.ofReal_le_ofReal
    apply phiR_mono n hN0
    have hp' := hp
    rw [Finset.mem_product] at hp'
    simp only [setVB, setVA, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
    have h := srank_step_misB (hn := hn) hC (hSoff p hp)
    rw [if_pos ⟨hp'.1.1, hp'.1.2, hp'.2.1, hp'.2.2⟩] at h
    omega
  have hall : ∀ p ∉ setVB C ×ˢ setVA C,
      ENNReal.ofReal (phiR n (misB (C.step (PEM40 n hn) p.1 p.2))) ≤
        ENNReal.ofReal (phiR n (k + 1)) := by
    intro p _
    apply ENNReal.ofReal_le_ofReal
    apply phiR_mono n hN0
    by_cases h : p.1 = p.2
    · have e : C.step (PEM40 n hn) p.1 p.2 = C := by rw [h]; exact step_self' _ _ _
      rw [e]
      omega
    · have := srank_step_misB (hn := hn) hC h
      omega
  have hs := sum_uniformPair_split hn2
    (fun p => ENNReal.ofReal (phiR n (misB (C.step (PEM40 n hn) p.1 p.2))))
    (setVB C ×ˢ setVA C) (phiR n k) (phiR n (k + 1)) (phiR_nonneg n k hN0)
    (phiR_nonneg n (k + 1) hN0) hlow hall
  rw [hmass, ENNReal.toReal_ofReal (by positivity)] at hs
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have key : (((k + 1) * (k + 1) : ℕ) : ℝ) / npairs n * phiR n k +
      (1 - (((k + 1) * (k + 1) : ℕ) : ℝ) / npairs n) * phiR n (k + 1) = phiR n (k + 1) - 1 := by
    rw [phiR_succ]
    push_cast
    field_simp
    ring
  rw [key] at hs
  have hge : 1 ≤ phiR n (k + 1) := by
    have h1 : phiR n 1 ≤ phiR n (k + 1) := phiR_mono n hN0 (by omega)
    have h2 : phiR n 1 = npairs n := by simp [phiR]
    linarith
  rw [hk]
  calc ∑ p : Fin n × Fin n, uniformPair n hn2 p *
          ENNReal.ofReal (phiR n (misB (C.step (PEM40 n hn) p.1 p.2))) + 1
      ≤ ENNReal.ofReal (phiR n (k + 1) - 1) + ENNReal.ofReal 1 := by
        rw [ENNReal.ofReal_one]
        exact add_le_add hs le_rfl
    _ = ENNReal.ofReal (phiR n (k + 1)) := by
        rw [← ENNReal.ofReal_add (by linarith) zero_le_one]
        congr 1
        ring

/-! ### Decision pairs -/

theorem srank_decision_pairs (hn2 : 2 ≤ n) {C : Config (AgentState n) Opinion n}
    (hC : SRank C) :
    ∃ a b : Fin n, a ≠ b ∧ DecisionPair n (C a).1 (C b).1 ∧ DecisionPair n (C b).1 (C a).1 := by
  obtain ⟨μ, hμ⟩ := srank_exists_median hC hn2
  by_cases hev : n % 2 = 0
  · obtain ⟨μ', hμ'⟩ := srank_exists_rank hC ⟨ceilHalf n, by unfold ceilHalf; omega⟩
    have hμ'v : (C μ').1.rank.val = ceilHalf n := by rw [hμ']
    have hne : μ ≠ μ' := by
      intro h; rw [h] at hμ; omega
    have m1 : IsMedType n (C μ).1.rank.val := Or.inl hμ
    have m2 : IsMedType n (C μ').1.rank.val := Or.inr ⟨hev, hμ'v⟩
    exact ⟨μ, μ', hne, Or.inr ⟨hev, m1, m2⟩, Or.inr ⟨hev, m2, m1⟩⟩
  · obtain ⟨ν, hν⟩ := srank_exists_last hC hn2
    have hne : μ ≠ ν := by
      intro h; rw [h] at hμ; unfold ceilHalf at hμ; omega
    have hodd : n % 2 = 1 := by omega
    exact ⟨μ, ν, hne, Or.inl ⟨hodd, Or.inl hμ⟩, Or.inl ⟨hodd, Or.inr hμ⟩⟩

/-! ### Sorting and decision -/

/-- **Sorting and decision** (P3 Lemmas 12, 13): from `Good ⊆ S_rank`, with every step from
`Good` landing in `Good` or `E`, the goal `(D ∩ Good) ∪ E` is missed within `23 n²` steps with
probability at most `π²/120 + 0.002479`. -/
theorem sortDecide_bound {hn : 0 < n} (hn2 : 2 ≤ n)
    (Good E : Config (AgentState n) Opinion n → Prop) (hGood : ∀ C, Good C → SRank C)
    (hE : ∀ C, Good C → ∀ i j : Fin n,
      Good (C.step (PEM40 n hn) i j) ∨ E (C.step (PEM40 n hn) i j))
    (X : Config (AgentState n) Opinion n) (hX : Good X) :
    probNotHitBy (PEM40 n hn) hn2 X (fun C => (Decided C ∧ Good C) ∨ E C) (23 * n ^ 2) ≤
      ENNReal.ofReal (Real.pi ^ 2 / 120 + 0.002479) := by
  have hN := two_le_npairs hn2
  have hNsq := npairs_le_sq hn2
  have hN0 : (0 : ℝ) ≤ npairs n := by linarith
  let Mid : Config (AgentState n) Opinion n → Prop := fun C => (SSorted C ∧ Good C) ∨ E C
  let Goal : Config (AgentState n) Opinion n → Prop := fun C => (Decided C ∧ Good C) ∨ E C
  -- phase 1: sorting within `20 n²`
  have h1 : probNotHitBy (PEM40 n hn) hn2 X Mid (20 * n ^ 2) ≤
      ENNReal.ofReal (Real.pi ^ 2 / 120) := by
    have hd := probNotHitBy_window_le_drift_avoid (PEM40 n hn) hn2 X Mid Good
      (fun C => ENNReal.ofReal (phiR n (misB C))) hX
      (fun C hC _ i j => (hE C hC i j).imp id Or.inr)
      (fun C hC hM => srank_sort_drift hn2 (hGood C hC) (fun hs => hM (Or.inl ⟨hs, hC⟩)))
      (20 * n ^ 2)
    have hW0 : ((20 * n ^ 2 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
    have hWtop : ((20 * n ^ 2 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← ENNReal.mul_le_mul_iff_right hW0 hWtop]
    refine hd.trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc phiR n (misB X) ≤ npairs n * (Real.pi ^ 2 / 6) := phiR_le n _ hN0
      _ ≤ ((20 * n ^ 2 : ℕ) : ℝ) * (Real.pi ^ 2 / 120) := by
          have := mul_le_mul_of_nonneg_right hNsq (sq_nonneg Real.pi)
          push_cast
          linarith
  -- phase 2: decision within `3 n²`
  have hMG : ∀ C, Mid C → ¬ Goal C → SSorted C ∧ Good C := by
    intro C hI hG
    rcases hI with h | h
    · exact h
    · exact absurd (Or.inr h) hG
  have hInv2 : ∀ C, Mid C → ¬ Goal C → ∀ i j : Fin n,
      Mid (C.step (PEM40 n hn) i j) ∨ Goal (C.step (PEM40 n hn) i j) := by
    intro C hI hG i j
    have hC := hMG C hI hG
    by_cases hij : i = j
    · subst hij; rw [step_self']; exact Or.inl hI
    · rcases hE C hC.2 i j with h | h
      · exact Or.inl (Or.inl ⟨ssorted_step hC.1 hij (hGood _ h), h⟩)
      · exact Or.inr (Or.inr h)
  have hstep2 : ∀ C, Mid C → ¬ Goal C → ∃ S : Finset (Fin n × Fin n),
      (∀ p ∈ S, Goal (C.step (PEM40 n hn) p.1 p.2)) ∧
        ENNReal.ofReal (2 / npairs n) ≤ ∑ p ∈ S, uniformPair n hn2 p := by
    intro C hI hG
    have hC := hMG C hI hG
    obtain ⟨a, b, hab, d1, d2⟩ := srank_decision_pairs hn2 hC.1.1
    refine ⟨{(a, b), (b, a)}, ?_, (mass_two hn2 hab).ge⟩
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · rcases hE C hC.2 a b with h | h
      · exact Or.inl ⟨ssorted_step_decide hC.1 hab (hGood _ h) d1, h⟩
      · exact Or.inr h
    · rcases hE C hC.2 b a with h | h
      · exact Or.inl ⟨ssorted_step_decide hC.1 (Ne.symm hab) (hGood _ h) d2, h⟩
      · exact Or.inr h
  have h2 : ∀ C, Mid C → probNotHitBy (PEM40 n hn) hn2 C Goal (3 * n ^ 2) ≤
      ENNReal.ofReal 0.002479 := by
    intro C hC
    refine (probNotHitBy_le_geom (PEM40 n hn) hn2 C Goal Mid (2 / npairs n)
      (by positivity) hC hInv2 hstep2 (3 * n ^ 2)).trans ?_
    refine (pow_pairs_le hn2 2 (by norm_num) le_rfl 3).trans (ENNReal.ofReal_le_ofReal ?_)
    have := exp_neg_six_lt
    have e : -(2 * ((3 : ℕ) : ℝ)) = -6 := by norm_num
    rw [e]
    exact this.le
  have h := probNotHitBy_compose_le (PEM40 n hn) hn2 X Mid Goal _ _ _ _ h1 h2
  rw [← ENNReal.ofReal_add (by positivity) (by norm_num),
    show 20 * n ^ 2 + 3 * n ^ 2 = 23 * n ^ 2 by ring] at h
  exact h

theorem pi_numeric : Real.pi ^ 2 / 120 + 0.002479 + 0.000001 ≤ 0.085 := by
  have h := Real.pi_lt_d4
  have h0 := Real.pi_pos
  have : Real.pi ^ 2 < 3.1416 ^ 2 := by nlinarith
  norm_num at this ⊢
  linarith

/-! ### Stage A′ -/

/-- **Stage A′** (P3 Lemma 13): `S_rank → D ∪ PT_L` within `23 n²`, probability `0.915`. -/
theorem stageA' : StageA' := by
  intro n hN hn hn2 X _ hX
  have h := sortDecide_bound (hn := hn) hn2 SRank PTL (fun C h => h) (fun C hC i j => by
      by_cases hij : i = j
      · subst hij; rw [step_self']; exact Or.inl hC
      · exact srank_step_srank_or_ptl (hn := hn) hC hij) X hX
  have h' := (probNotHitBy_mono_goal (PEM40 n hn) hn2 X
    (fun C => (Decided C ∧ SRank C) ∨ PTL C) (fun C => Decided C ∨ PTL C)
    (fun C h => h.imp And.left id) _).trans h
  exact probHitBy_ge_of_probNotHitBy_le _ hn2 X _ _ _ 0.915 (by positivity)
    (by have := pi_numeric; linarith) h'

/-! ### The tick bound -/

/-- **Tick bound** (P3 Lemma 14): from `S_rank` with median timer at least `99`, the class
`S_rank ∩ {medT ≥ 6} ∩ Extra` is left within `23 n²` steps with probability at most `10⁻⁶`. -/
theorem tick_hit_bound {hn : 0 < n} (hN : 1608 ≤ n) (hn2 : 2 ≤ n)
    (Extra : Config (AgentState n) Opinion n → Prop)
    (hExtra : ∀ C, SRank C → Extra C → ∀ i j : Fin n, SRank (C.step (PEM40 n hn) i j) →
      Extra (C.step (PEM40 n hn) i j))
    (X : Config (AgentState n) Opinion n) (hX : SRank X) (hX99 : 99 ≤ medT X) (hXe : Extra X) :
    probHitBy (PEM40 n hn) hn2 X (fun C => ¬ (SRank C ∧ 6 ≤ medT C ∧ Extra C)) (23 * n ^ 2) ≤
      ENNReal.ofReal 0.000001 := by
  have hN2 := two_le_npairs hn2
  have hq : 0 ≤ 2 / npairs n := by positivity
  have hInv : ∀ C, (SRank C ∧ 5 ≤ medT C ∧ Extra C) → ¬ ¬ (SRank C ∧ 6 ≤ medT C ∧ Extra C) →
      ∀ i j : Fin n, SRank (C.step (PEM40 n hn) i j) ∧ 5 ≤ medT (C.step (PEM40 n hn) i j) ∧
        Extra (C.step (PEM40 n hn) i j) := by
    intro C hI hG i j
    have hG' := not_not.mp hG
    by_cases hij : i = j
    · subst hij; rw [step_self']; exact hI
    · have hS := srank_step_srank_of_medT (hn := hn) hG'.1 hij (by omega)
      refine ⟨hS, ?_, hExtra C hG'.1 hG'.2.2 i j hS⟩
      rw [srank_step_medT hG'.1 hij]
      split_ifs <;> omega
  have hstep : ∀ C, (SRank C ∧ 5 ≤ medT C ∧ Extra C) → ¬ ¬ (SRank C ∧ 6 ≤ medT C ∧ Extra C) →
      ∑ p : Fin n × Fin n, uniformPair n hn2 p *
          (2 : ℝ≥0∞) ^ (99 - medT (C.step (PEM40 n hn) p.1 p.2)) ≤
        ENNReal.ofReal (1 + 2 / npairs n) * 2 ^ (99 - medT C) := by
    intro C _ hG
    have hC := (not_not.mp hG).1
    obtain ⟨μ, hμ⟩ := srank_exists_median hC hn2
    obtain ⟨ν, hν⟩ := srank_exists_last hC hn2
    have hμν : μ ≠ ν := by
      intro h; rw [h] at hμ; unfold ceilHalf at hμ; omega
    have hdiag : ∀ p : Fin n × Fin n, p.1 = p.2 → C.step (PEM40 n hn) p.1 p.2 = C := by
      intro p h; rw [h]; exact step_self' _ _ _
    have hS : ∀ p ∈ ({(μ, ν), (ν, μ)} : Finset (Fin n × Fin n)),
        (2 : ℝ≥0∞) ^ (99 - medT (C.step (PEM40 n hn) p.1 p.2)) ≤
          ENNReal.ofReal (2 * 2 ^ (99 - medT C)) := by
      intro p _
      rw [← pow_succ', ← two_pow_eq_ofReal]
      apply pow_le_pow_right₀ (by norm_num)
      by_cases h : p.1 = p.2
      · rw [hdiag p h]; omega
      · rw [srank_step_medT hC h]; split_ifs <;> omega
    have hT : ∀ p ∉ ({(μ, ν), (ν, μ)} : Finset (Fin n × Fin n)),
        (2 : ℝ≥0∞) ^ (99 - medT (C.step (PEM40 n hn) p.1 p.2)) ≤
          ENNReal.ofReal (2 ^ (99 - medT C)) := by
      intro p hp
      rw [← two_pow_eq_ofReal]
      apply pow_le_pow_right₀ (by norm_num)
      by_cases h : p.1 = p.2
      · exact le_of_eq (by rw [hdiag p h])
      · rw [srank_step_medT hC h, if_neg]
        · omega
        intro ht
        apply hp
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have e1 : p.1 = μ := hC.2 (show (C p.1).1.rank = (C μ).1.rank from Fin.ext (by omega))
          have e2 : p.2 = ν := hC.2 (show (C p.2).1.rank = (C ν).1.rank from Fin.ext (by omega))
          exact Or.inl (Prod.ext e1 e2)
        · have e1 : p.1 = ν := hC.2 (show (C p.1).1.rank = (C ν).1.rank from Fin.ext (by omega))
          have e2 : p.2 = μ := hC.2 (show (C p.2).1.rank = (C μ).1.rank from Fin.ext (by omega))
          exact Or.inr (Prod.ext e1 e2)
    have hs := sum_uniformPair_split hn2
      (fun p => (2 : ℝ≥0∞) ^ (99 - medT (C.step (PEM40 n hn) p.1 p.2)))
      {(μ, ν), (ν, μ)} (2 * 2 ^ (99 - medT C)) (2 ^ (99 - medT C)) (by positivity)
      (by positivity) hS hT
    rw [mass_two hn2 hμν, ENNReal.toReal_ofReal hq] at hs
    refine hs.trans (le_of_eq ?_)
    rw [two_pow_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hlow : ∀ C, (SRank C ∧ 5 ≤ medT C ∧ Extra C) → ¬ (SRank C ∧ 6 ≤ medT C ∧ Extra C) →
      (2 : ℝ≥0∞) ^ 94 ≤ 2 ^ (99 - medT C) := by
    intro C hI hG
    have h5 : medT C ≤ 5 := by
      by_contra h
      exact hG ⟨hI.1, by omega, hI.2.2⟩
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h := probHitBy_le_potential_grow (PEM40 n hn) hn2 X
    (fun C => ¬ (SRank C ∧ 6 ≤ medT C ∧ Extra C)) (fun C => SRank C ∧ 5 ≤ medT C ∧ Extra C)
    (fun C => (2 : ℝ≥0∞) ^ (99 - medT C)) (ENNReal.ofReal (1 + 2 / npairs n)) (2 ^ 94)
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
    ⟨hX, by omega, hXe⟩ hInv hstep hlow (23 * n ^ 2)
  have e0 : 99 - medT X = 0 := by omega
  simp only [e0, pow_zero, mul_one] at h
  have hb : ENNReal.ofReal (1 + 2 / npairs n) ^ (23 * n ^ 2) ≤ ENNReal.ofReal (Real.exp 47) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    refine (one_add_pow_le_exp hq _).trans (Real.exp_le_exp.mpr ?_)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), npairs_eq hn2]
    push_cast
    have : (1608 : ℝ) ≤ n := by exact_mod_cast hN
    nlinarith
  have h94 : (2 : ℝ≥0∞) ^ 94 ≠ 0 := pow_ne_zero _ (by norm_num)
  have h94' : (2 : ℝ≥0∞) ^ 94 ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [← ENNReal.mul_le_mul_iff_right h94 h94']
  refine h.trans (hb.trans ?_)
  rw [two_pow_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp 47 ≤ 2.72 ^ 47 := by
    rw [show (47 : ℝ) = (47 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 47
  calc Real.exp 47 ≤ 2.72 ^ 47 := he
    _ ≤ 2 ^ 94 * 0.000001 := by norm_num

/-! ### Stage B56 -/

/-- **Stage B56, common form** (P3 Lemma 14 with `θ = 99`): from `R(99) ∩ Extra`, the goal
`Target ⊇ D ∩ S_rank ∩ {medT ≥ 6} ∩ Extra` is hit within `23 n²` with probability `0.915`. -/
theorem stageB56_core {hn : 0 < n} (hN : 1608 ≤ n) (hn2 : 2 ≤ n)
    (Extra : Config (AgentState n) Opinion n → Prop)
    (hExtra : ∀ C, SRank C → Extra C → ∀ i j : Fin n, SRank (C.step (PEM40 n hn) i j) →
      Extra (C.step (PEM40 n hn) i j))
    (Target : Config (AgentState n) Opinion n → Prop)
    (hT : ∀ C, Decided C → SRank C ∧ 6 ≤ medT C ∧ Extra C → Target C)
    (X : Config (AgentState n) Opinion n) (hX : RTheta 99 X) (hXe : Extra X) :
    ENNReal.ofReal 0.915 ≤ probHitBy (PEM40 n hn) hn2 X Target (23 * n ^ 2) := by
  classical
  let Good : Config (AgentState n) Opinion n → Prop := fun C => SRank C ∧ 6 ≤ medT C ∧ Extra C
  have h99 : 99 ≤ medT X := by
    obtain ⟨μ, hμ⟩ := srank_exists_median hX.1 hn2
    rw [medT_eq hX.1 hμ]
    exact hX.2 μ hμ
  have h1 := sortDecide_bound (hn := hn) hn2 Good (fun C => ¬ Good C) (fun C h => h.1)
    (fun C _ i j => em _) X ⟨hX.1, by omega, hXe⟩
  have h2 := tick_hit_bound hN hn2 Extra hExtra X hX.1 h99 hXe
  have h3 : ENNReal.ofReal (1 - (Real.pi ^ 2 / 120 + 0.002479)) ≤
      probHitBy (PEM40 n hn) hn2 X (fun C => (Decided C ∧ Good C) ∨ ¬ Good C) (23 * n ^ 2) :=
    probHitBy_ge_of_probNotHitBy_le _ hn2 X _ _ _ _ (by positivity) le_rfl h1
  have h4 : probHitBy (PEM40 n hn) hn2 X (fun C => (Decided C ∧ Good C) ∨ ¬ Good C)
      (23 * n ^ 2) ≤ probHitBy (PEM40 n hn) hn2 X (fun C => Target C ∨ ¬ Good C) (23 * n ^ 2) :=
    probHitBy_mono_goal _ hn2 X _ _ (fun C h => h.imp (fun h => hT C h.1 h.2) id) _
  have h5 := probHitBy_union_le (PEM40 n hn) hn2 X Target (fun C => ¬ Good C) (23 * n ^ 2)
  have h6 : ENNReal.ofReal (1 - (Real.pi ^ 2 / 120 + 0.002479)) ≤
      probHitBy (PEM40 n hn) hn2 X Target (23 * n ^ 2) + ENNReal.ofReal 0.000001 :=
    h3.trans (h4.trans (h5.trans (add_le_add le_rfl h2)))
  rw [← tsub_le_iff_right, ← ENNReal.ofReal_sub _ (by norm_num)] at h6
  refine (ENNReal.ofReal_le_ofReal ?_).trans h6
  have := pi_numeric
  linarith

/-- **Stage B56** (P3 Lemma 14): `R(99) → D` within `23 n²`, probability `0.915`. -/
theorem stageB56 : StageB56 := by
  intro n hN hn hn2 X _ hX
  exact stageB56_core hN hn2 (fun _ => True) (fun _ _ _ _ _ _ => trivial) Decided
    (fun C hD _ => hD) X hX trivial

/-- **Stage B56M** (P3 Lemma 14 with `AnsOK`): `R(99) ∩ AnsOK → Cons` within `23 n²`,
probability `0.915`. -/
theorem stageB56M : StageB56M := by
  intro n hN hn hn2 X _ hX
  refine stageB56_core hN hn2 AnsOK ?_ IsConsensusConfig ?_ X hX.1 hX.2
  · intro C hC hA i j hS
    by_cases hij : i = j
    · subst hij; rw [step_self']; exact hA
    · exact ansOK_step hC hA hij hS
  · intro C hD hG
    refine ⟨hD.1.1.1, hD.1.1.2, hD.1.2, fun v => ?_⟩
    by_cases hm : IsMedType n (C v).1.rank.val
    · exact hD.2 v hm
    · exact hG.2.2 v (hD.1.1.1 v) hm


/-- Non-vacuity of the premises of Stages E, C, A′, B56, B56M at `n = 1608`: the identity ranking
with all opinions `A`, all answers `outA` and median timer `T₀ = 308`. -/
example : ∃ X : Config (AgentState 1608) Opinion 1608, GoodPaper X ∧ IsConsensusConfig X ∧
    Decided X ∧ RTheta 99 X ∧ AnsOK X := by
  classical
  let X : Config (AgentState 1608) Opinion 1608 := fun v =>
    (AgentState.mk .Settled v .F 0 .outA 308 0 0 0, Opinion.A)
  have hA : nAOf X = 1608 := by
    have hf : Finset.univ.filter (fun v => X.inputOf v = Opinion.A) = Finset.univ :=
      Finset.filter_true_of_mem (fun v _ => rfl)
    unfold nAOf Config.agentsWithInput
    rw [hf]
    simp
  have hB : nBOf X = 0 := by
    unfold nBOf Config.agentsWithInput
    rw [Finset.filter_false_of_mem (fun v _ => by
      show ¬ X.inputOf v = Opinion.B
      exact (by decide : ¬ Opinion.A = Opinion.B))]
    simp
  have hmaj : majorityAnswer X = .outA := by
    unfold majorityAnswer; rw [hA, hB]; simp
  have hinj : Function.Injective (fun v => (X v).1.rank) := fun a b h => h
  have hin : ∀ v, ((X v).2 = Opinion.A ↔ (X v).1.rank.val < nAOf X) := fun v => by
    rw [hA]; exact ⟨fun _ => v.isLt, fun _ => rfl⟩
  have hans : ∀ v, (X v).1.answer = majorityAnswer X := fun v => by rw [hmaj]
  refine ⟨X, fun v => ?_, ⟨fun v => rfl, hinj, hin, hans⟩,
    ⟨⟨⟨fun v => rfl, hinj⟩, hin⟩, fun v _ => hans v⟩,
    ⟨⟨fun v => rfl, hinj⟩, fun v _ => by show 99 ≤ 308; norm_num⟩, fun v _ _ => hans v⟩
  simp [X, GoodPEM]

end Ripple.PopulationProtocol.SSEM
