/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealTwoSequential

/-!
# The exact zero/one/two mixture law of a physical activation batch

The batch size depends only on the active and inactive totals.  Conditional
on size one, the activated identity is uniform; conditional on size two, the
ordered pair is uniform without replacement.
-/

namespace Tri

open scoped ENNReal

noncomputable section

noncomputable def infectionRevealBatchZeroWeight
    (n A I : ℕ) : ℝ≥0∞ :=
  ((Nat.choose A 3 + Nat.choose I 3 : ℕ) : ℝ≥0∞) /
    (Nat.choose n 3 : ℝ≥0∞)

noncomputable def infectionRevealBatchOneWeight
    (n A I : ℕ) : ℝ≥0∞ :=
  ((Nat.choose A 2 * I : ℕ) : ℝ≥0∞) /
    (Nat.choose n 3 : ℝ≥0∞)

noncomputable def infectionRevealBatchTwoWeight
    (n A I : ℕ) : ℝ≥0∞ :=
  ((A * Nat.choose I 2 : ℕ) : ℝ≥0∞) /
    (Nat.choose n 3 : ℝ≥0∞)

/-- The three batch-size coefficients form a probability distribution. -/
theorem infectionRevealBatch_weights_sum
    (n A I : ℕ) (h3 : 3 ≤ n)
    (htotal : A + I = n) :
    infectionRevealBatchZeroWeight n A I +
        infectionRevealBatchOneWeight n A I +
        infectionRevealBatchTwoWeight n A I = 1 := by
  have hnum :
      (Nat.choose A 3 + Nat.choose I 3) +
          Nat.choose A 2 * I +
          A * Nat.choose I 2 =
        Nat.choose n 3 := by
    have h := choose_three_add A I
    simpa [htotal, add_assoc, add_left_comm, add_comm] using h
  have hden0 :
      ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (choose_three_pos h3).ne'
  have hdenTop :
      ((Nat.choose n 3 : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    infectionRevealBatchZeroWeight n A I +
          infectionRevealBatchOneWeight n A I +
          infectionRevealBatchTwoWeight n A I =
        (((Nat.choose A 3 + Nat.choose I 3) +
          Nat.choose A 2 * I +
          A * Nat.choose I 2 : ℕ) : ℝ≥0∞) /
            (Nat.choose n 3 : ℝ≥0∞) := by
              unfold infectionRevealBatchZeroWeight
                infectionRevealBatchOneWeight
                infectionRevealBatchTwoWeight
              rw [ENNReal.div_add_div_same,
                ENNReal.div_add_div_same]
              push_cast
              rfl
    _ = (Nat.choose n 3 : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) := by
            rw [hnum]
    _ = 1 := ENNReal.div_self hden0 hdenTop

inductive InfectionRevealBatchSize
  | zero
  | one
  | two
  deriving DecidableEq, Fintype, Repr

noncomputable def infectionRevealBatchSizeMass
    (n A I : ℕ) : InfectionRevealBatchSize → ℝ≥0∞
  | .zero => infectionRevealBatchZeroWeight n A I
  | .one => infectionRevealBatchOneWeight n A I
  | .two => infectionRevealBatchTwoWeight n A I

noncomputable def infectionRevealBatchSizePMF
    (n A I : ℕ) (h3 : 3 ≤ n)
    (htotal : A + I = n) :
    PMF InfectionRevealBatchSize :=
  PMF.ofFintype
    (infectionRevealBatchSizeMass n A I)
    (by
      rw [show
        (Finset.univ : Finset InfectionRevealBatchSize) =
          {InfectionRevealBatchSize.zero,
            InfectionRevealBatchSize.one,
            InfectionRevealBatchSize.two} from rfl]
      simpa [infectionRevealBatchSizeMass, add_assoc] using
        infectionRevealBatch_weights_sum n A I h3 htotal)

@[simp] theorem infectionRevealBatchSizePMF_apply
    (n A I : ℕ) (h3 : 3 ≤ n)
    (htotal : A + I = n)
    (d : InfectionRevealBatchSize) :
    infectionRevealBatchSizePMF n A I h3 htotal d =
      infectionRevealBatchSizeMass n A I d :=
  rfl

/-- Conditional identity law at each batch size.  Missing fibres use an
arbitrary empty fallback whose coefficient is zero. -/
noncomputable def infectionRevealGivenBatchSize
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    InfectionRevealBatchSize → PMF (InfectionRevealBatch s.inactive) := by
  classical
  exact fun
    | .zero => PMF.pure .none
    | .one =>
        if h : Nonempty (InfectionInactiveId s.inactive) then
          (infectionRevealOnePMF s.inactive h).map
            InfectionRevealBatch.one
        else
          PMF.pure .none
    | .two =>
        if h : Nonempty
            (InfectionOrderedRevealTwo s.inactive) then
          (infectionRevealTwoPMF s.inactive h).map
            InfectionRevealBatch.two
        else
          PMF.pure .none

theorem infectionReveal_active_add_inactive
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    s.coarse.1.active + s.inactive.ids.card = n := by
  rw [s.hinactiveCard]
  simpa [InfectionCfg.Inv, InfectionCfg.total] using s.coarse.2

/-- Explicit state-dependent zero/one/two batch mixture. -/
noncomputable def infectionRevealBatchMixturePMF
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n) :
    PMF (InfectionRevealBatch s.inactive) :=
  (infectionRevealBatchSizePMF n
      s.coarse.1.active s.inactive.ids.card h3
      (infectionReveal_active_add_inactive s)).bind
    (infectionRevealGivenBatchSize s)

theorem infectionRevealGivenBatchSize_one_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive) :
    infectionRevealGivenBatchSize s .one (.one i) =
      infectionRevealOnePMF s.inactive ⟨i⟩ i := by
  classical
  unfold infectionRevealGivenBatchSize
  rw [dif_pos (show Nonempty
    (InfectionInactiveId s.inactive) from ⟨i⟩)]
  have hinj : Function.Injective
      (@InfectionRevealBatch.one n s.inactive) := by
    intro a b h
    cases h
    rfl
  simpa using
    pmf_map_apply_of_injective
      (infectionRevealOnePMF s.inactive ⟨i⟩)
      InfectionRevealBatch.one
      hinj
      i

theorem infectionRevealGivenBatchSize_two_apply
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive) :
    infectionRevealGivenBatchSize s .two (.two p) =
      infectionRevealTwoPMF s.inactive ⟨p⟩ p := by
  classical
  unfold infectionRevealGivenBatchSize
  rw [dif_pos (show Nonempty
    (InfectionOrderedRevealTwo s.inactive) from ⟨p⟩)]
  have hinj : Function.Injective
      (@InfectionRevealBatch.two n s.inactive) := by
    intro a b h
    cases h
    rfl
  simpa using
    pmf_map_apply_of_injective
      (infectionRevealTwoPMF s.inactive ⟨p⟩)
      InfectionRevealBatch.two
      hinj
      p

theorem infectionRevealGivenBatchSize_two_apply_one
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive) :
    infectionRevealGivenBatchSize s .two (.one i) = 0 := by
  classical
  simp only [infectionRevealGivenBatchSize]
  split_ifs with h
  · apply pmf_map_apply_eq_zero_of_not_mem_range
    intro p
    simp
  · simp

theorem infectionRevealGivenBatchSize_one_apply_two
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive) :
    infectionRevealGivenBatchSize s .one (.two p) = 0 := by
  classical
  simp only [infectionRevealGivenBatchSize]
  split_ifs with h
  · apply pmf_map_apply_eq_zero_of_not_mem_range
    intro i
    simp
  · simp

@[simp] theorem infectionRevealGivenBatchSize_zero_apply_one
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive) :
    infectionRevealGivenBatchSize s .zero (.one i) = 0 := by
  simp [infectionRevealGivenBatchSize]

@[simp] theorem infectionRevealGivenBatchSize_zero_apply_two
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive) :
    infectionRevealGivenBatchSize s .zero (.two p) = 0 := by
  simp [infectionRevealGivenBatchSize]

theorem infectionRevealBatchMixturePMF_one_apply
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive) :
    infectionRevealBatchMixturePMF n h3 s (.one i) =
      infectionRevealBatchOneWeight n s.coarse.1.active
          s.inactive.ids.card *
        infectionRevealOnePMF s.inactive ⟨i⟩ i := by
  classical
  unfold infectionRevealBatchMixturePMF
  rw [PMF.bind_apply, tsum_fintype]
  rw [show
    (Finset.univ : Finset InfectionRevealBatchSize) =
      {InfectionRevealBatchSize.zero,
        InfectionRevealBatchSize.one,
        InfectionRevealBatchSize.two} from rfl]
  simp [infectionRevealBatchSizeMass,
    infectionRevealGivenBatchSize_one_apply,
    infectionRevealGivenBatchSize_two_apply_one]

theorem infectionRevealBatchMixturePMF_two_apply
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive) :
    infectionRevealBatchMixturePMF n h3 s (.two p) =
      infectionRevealBatchTwoWeight n s.coarse.1.active
          s.inactive.ids.card *
        infectionRevealTwoPMF s.inactive ⟨p⟩ p := by
  classical
  unfold infectionRevealBatchMixturePMF
  rw [PMF.bind_apply, tsum_fintype]
  rw [show
    (Finset.univ : Finset InfectionRevealBatchSize) =
      {InfectionRevealBatchSize.zero,
        InfectionRevealBatchSize.one,
        InfectionRevealBatchSize.two} from rfl]
  simp [infectionRevealBatchSizeMass,
    infectionRevealGivenBatchSize_two_apply,
    infectionRevealGivenBatchSize_one_apply_two]

theorem infectionRevealBatchMixturePMF_one_fixed
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (i : InfectionInactiveId s.inactive) :
    infectionRevealBatchMixturePMF n h3 s (.one i) =
      (Nat.choose s.coarse.1.active 2 : ℝ≥0∞) /
        (Nat.choose n 3 : ℝ≥0∞) := by
  rw [infectionRevealBatchMixturePMF_one_apply,
    infectionRevealOnePMF_apply, card_infectionInactiveId]
  have hI : s.inactive.ids.card ≠ 0 :=
    (Finset.card_pos.mpr ⟨i.1, i.2⟩).ne'
  have hD : Nat.choose n 3 ≠ 0 :=
    (choose_three_pos h3).ne'
  simpa [infectionRevealBatchOneWeight] using
    ennreal_event_uniform_cancel
      (Nat.choose s.coarse.1.active 2)
      s.inactive.ids.card
      (Nat.choose n 3) 1 hI hD

theorem infectionRevealBatchMixturePMF_two_fixed
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n)
    (p : InfectionOrderedRevealTwo s.inactive) :
    infectionRevealBatchMixturePMF n h3 s (.two p) =
      (s.coarse.1.active : ℝ≥0∞) /
        ((2 * Nat.choose n 3 : ℕ) : ℝ≥0∞) := by
  rw [infectionRevealBatchMixturePMF_two_apply,
    infectionRevealTwoPMF_apply]
  have hne : p.1.1.1 ≠ p.1.2.1 := by
    intro h
    apply p.2
    exact Subtype.ext h
  have hcard : 1 < s.inactive.ids.card :=
    Finset.one_lt_card.mpr
      ⟨p.1.1.1, p.1.1.2, p.1.2.1, p.1.2.2, hne⟩
  have hc : Nat.choose s.inactive.ids.card 2 ≠ 0 := by
    rw [Nat.choose_ne_zero_iff]
    omega
  have hD : Nat.choose n 3 ≠ 0 :=
    (choose_three_pos h3).ne'
  have hordered :
      Fintype.card (InfectionOrderedRevealTwo s.inactive) =
        2 * Nat.choose s.inactive.ids.card 2 := by
    simpa only [card_infectionInactiveId] using
      card_ordered_distinct_pair (InfectionInactiveId s.inactive)
  rw [hordered]
  simpa [infectionRevealBatchTwoWeight, Nat.cast_mul, Nat.cast_ofNat] using
    ennreal_event_uniform_cancel
      s.coarse.1.active
      (Nat.choose s.inactive.ids.card 2)
      (Nat.choose n 3) 2 hc hD

/-- Two PMFs agreeing off one atom agree everywhere; the remaining atom is
recovered from total mass one. -/
theorem pmf_ext_of_eq_off
    {α : Type*} [DecidableEq α]
    (p q : PMF α) (a₀ : α)
    (h : ∀ a, a ≠ a₀ → p a = q a) :
    p = q := by
  apply PMF.ext
  intro a
  by_cases ha : a = a₀
  · subst a
    let tp : ℝ≥0∞ :=
      ∑' b, if b = a₀ then 0 else p b
    let tq : ℝ≥0∞ :=
      ∑' b, if b = a₀ then 0 else q b
    have ht : tp = tq := by
      dsimp only [tp, tq]
      apply tsum_congr
      intro b
      by_cases hb : b = a₀
      · simp [hb]
      · simp [hb, h b hb]
    have hp : p a₀ + tp = 1 := by
      have hsingle :
          (∑' b, if b = a₀ then p b else 0) = p a₀ :=
        tsum_ite_eq a₀ p
      calc
        p a₀ + tp =
            (∑' b, if b = a₀ then p b else 0) +
              ∑' b, if b = a₀ then 0 else p b := by
                rw [hsingle]
        _ = ∑' b,
              ((if b = a₀ then p b else 0) +
                (if b = a₀ then 0 else p b)) :=
          ENNReal.tsum_add.symm
        _ = ∑' b, p b := by
          apply tsum_congr
          intro b
          by_cases hb : b = a₀ <;> simp [hb]
        _ = 1 := p.tsum_coe
    have hq : q a₀ + tq = 1 := by
      have hsingle :
          (∑' b, if b = a₀ then q b else 0) = q a₀ :=
        tsum_ite_eq a₀ q
      calc
        q a₀ + tq =
            (∑' b, if b = a₀ then q b else 0) +
              ∑' b, if b = a₀ then 0 else q b := by
                rw [hsingle]
        _ = ∑' b,
              ((if b = a₀ then q b else 0) +
                (if b = a₀ then 0 else q b)) :=
          ENNReal.tsum_add.symm
        _ = ∑' b, q b := by
          apply tsum_congr
          intro b
          by_cases hb : b = a₀ <;> simp [hb]
        _ = 1 := q.tsum_coe
    rw [ht] at hp
    have htq : tq ≠ ⊤ := by
      intro htop
      have : (⊤ : ℝ≥0∞) = 1 := by
        simpa [htop] using hq
      exact ENNReal.top_ne_one this
    exact add_left_injective_of_ne_top tq htq (hp.trans hq.symm)
  · exact h a ha

/-- Exact factorization of the physical batch law into batch size and a
uniform conditional identity law. -/
theorem infectionRevealBatchPMF_eq_mixture
    (n : ℕ) (h3 : 3 ≤ n)
    (s : InfectionRevealPhysicalState n) :
    infectionRevealBatchPMF n h3 s =
      infectionRevealBatchMixturePMF n h3 s := by
  apply pmf_ext_of_eq_off _ _ .none
  intro b hb
  cases b with
  | none => contradiction
  | one i =>
      rw [infectionRevealBatchPMF_one_apply,
        infectionRevealBatchMixturePMF_one_fixed]
  | two p =>
      rw [infectionRevealBatchPMF_two_apply,
        infectionRevealBatchMixturePMF_two_fixed]

end
end Tri

#print axioms Tri.infectionRevealBatch_weights_sum
#print axioms Tri.infectionRevealBatchMixturePMF_one_fixed
#print axioms Tri.infectionRevealBatchMixturePMF_two_fixed
#print axioms Tri.pmf_ext_of_eq_off
#print axioms Tri.infectionRevealBatchPMF_eq_mixture
