-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockContactIntervals.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockHourOccupancyRow

/-!
Exact interval arithmetic for the seed-frozen physical Clock contacts.
The lower-chain lemma counts each actual contact once; no time-change
or conditional law is used in these deterministic identities.
-/

noncomputable section
open scoped BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactIntervals

open TimeTheorem PairLog StageEventSpec PhaseThreeClockCore PhaseThreeClockVirtual
  PhaseThreeClockRawLocalRow PhaseThreeClockHourOccupancyRow

variable {n : ℕ}

theorem core_contact_mono_right (init : InputCfg n) (f : Lab init)
    (draws : Draws init) (a b c : ℕ) (hbc : b ≤ c) :
    clockContactsL init f draws a b ≤ clockContactsL init f draws a c := by
  classical
  apply Finset.card_le_card
  intro t ht
  obtain ⟨ht, hp⟩ := Finset.mem_filter.mp ht
  obtain ⟨hat, htb⟩ := Finset.mem_Ioc.mp ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hat, htb.trans hbc⟩, hp⟩

theorem core_contact_antitone_left (init : InputCfg n) (f : Lab init)
    (draws : Draws init) (a b c : ℕ) (hab : a ≤ b) :
    clockContactsL init f draws b c ≤ clockContactsL init f draws a c := by
  classical
  apply Finset.card_le_card
  intro t ht
  obtain ⟨ht, hp⟩ := Finset.mem_filter.mp ht
  obtain ⟨hbt, htc⟩ := Finset.mem_Ioc.mp ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hab.trans_lt hbt, htc⟩, hp⟩

theorem core_contact_triangle (init : InputCfg n) (f : Lab init)
    (draws : Draws init) (a b c : ℕ) :
    clockContactsL init f draws a c ≤
      clockContactsL init f draws a b + clockContactsL init f draws b c := by
  classical
  let A := (Finset.Ioc a b).filter (clockContactL init f draws)
  let B := (Finset.Ioc b c).filter (clockContactL init f draws)
  have hsub : (Finset.Ioc a c).filter (clockContactL init f draws) ⊆ A ∪ B := by
    intro t ht
    obtain ⟨ht, hp⟩ := Finset.mem_filter.mp ht
    obtain ⟨hat, htc⟩ := Finset.mem_Ioc.mp ht
    by_cases htb : t ≤ b
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hat, htb⟩, hp⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, htc⟩, hp⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le A B)

theorem core_contact_add (init : InputCfg n) (f : Lab init)
    (draws : Draws init) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    clockContactsL init f draws a c =
      clockContactsL init f draws a b + clockContactsL init f draws b c := by
  classical
  let A := (Finset.Ioc a b).filter (clockContactL init f draws)
  let B := (Finset.Ioc b c).filter (clockContactL init f draws)
  have heq : (Finset.Ioc a c).filter (clockContactL init f draws) = A ∪ B := by
    ext t
    simp only [A, B, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · rintro ⟨⟨hat, htc⟩, hp⟩
      by_cases htb : t ≤ b
      · exact Or.inl ⟨⟨hat, htb⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, htc⟩, hp⟩
    · rintro (⟨⟨hat, htb⟩, hp⟩ | ⟨⟨hbt, htc⟩, hp⟩)
      · exact ⟨⟨hat, htb.trans hbc⟩, hp⟩
      · exact ⟨⟨hab.trans_lt hbt, htc⟩, hp⟩
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro t ha hb
    have hat := Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1
    have hbt := Finset.mem_Ioc.mp (Finset.mem_filter.mp hb).1
    omega
  unfold clockContactsL
  rw [heq, Finset.card_union_of_disjoint hd]

theorem core_front_antitone_level (init : InputCfg n) (f g : Lab init)
    (a b : ℕ) (hab : a ≤ b) :
    frontCountL init f g b ≤ frontCountL init f g a := by
  classical
  unfold frontCountL StageEventSpec.labelCount
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hi.1, hab.trans hi.2⟩

theorem bulk_times_mono (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) (hp : LevelPassages init ω s w)
    (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ clockTop n) :
    w.bulk a ≤ w.bulk b := by
  have hfa := hp.2 a ha (hab.trans hb)
  have hfb := hp.2 b (ha.trans hab) hb
  by_contra hn
  exact hfa.2.2 (w.bulk b) hfb.1 (by omega)
    (hfb.2.1.trans (core_front_antitone_level init _ _ a b hab))

/-- Sum r positive-minute lower bounds on their disjoint actual intervals. -/
theorem lower_contact_chain (init : InputCfg n) (ω : InputLog n)
    (s : ℕ) (w : ClockTimes init) (hp : LevelPassages init ω s w)
    (c : ℝ)
    (hstep : ∀ i, 1 ≤ i → i < clockTop n →
      c ≤ (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
        (w.bulk i) (w.bulk (i + 1)) : ℝ)) :
    ∀ j r, 1 ≤ j → j + r ≤ clockTop n →
      (r : ℝ) * c ≤
        (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
          (w.bulk j) (w.bulk (j + r)) : ℝ) := by
  intro j r hj
  induction r with
  | zero =>
      intro _
      simp [clockContactsL]
  | succ r ih =>
      intro htop
      have hprev := ih (by omega)
      have hlast := hstep (j + r) (by omega) (by omega)
      have hab := bulk_times_mono init ω s w hp j (j + r) hj (by omega) (by omega)
      have hbc := bulk_times_mono init ω s w hp (j + r) (j + r + 1)
        (by omega) (by omega) (by omega)
      have heq := core_contact_add init (virtualLabels init ω s) (drawLabels init ω)
        (w.bulk j) (w.bulk (j + r)) (w.bulk (j + r + 1)) hab hbc
      have heqR :
          (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
            (w.bulk j) (w.bulk (j + (r + 1))) : ℝ) =
          (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
            (w.bulk j) (w.bulk (j + r)) : ℝ) +
          (clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
            (w.bulk (j + r)) (w.bulk (j + r + 1)) : ℝ) := by
        rw [show j + (r + 1) = j + r + 1 by omega]
        exact_mod_cast heq
      rw [heqR]
      push_cast
      linarith

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactIntervals

end
