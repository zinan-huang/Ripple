-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainPairCounts.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainProcessIncrement
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockCapSpread
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationRoleFloors
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeFreeze

/-!
# Ordered-pair counts for the killed Main process

The contact count is covered by the two orientations of
`MainMask × HighClock`.  Deep cancellations are covered by the two orientations of
`DeepPos × DeepNeg`; AM--GM is applied only after this sign split, retaining the
factor one half which is essential in P12.  A gated tick updates only two Clocks and
therefore preserves the Main ledger exactly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainPairCounts

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockEmbeddingBridge PhaseThreeClockMainLedger PhaseThreeClockMainPath
  PhaseThreeClockMainAlgebra PhaseThreeClockMainProcess
  PhaseThreeClockMainProcessIncrement PhaseThreeClockCapSpread
  PhaseThreeClockActivationRoleFloors PhaseThreeClockShapeFreeze PhaseThreeClockCore PhaseThreeClockProbabilityFloors
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

/-- The contact atom of `mainPairCredit`, as a pair predicate. -/
def MainContactPair (h : ℕ) (f : Lab init) (i j : Fin init.card) : Prop :=
  contactInd h (f i) (f j) = 1

/-- The deep-cancellation atom of `mainPairCredit`, as a pair predicate. -/
def MainDeepPair (h : ℕ) (f : Lab init) (i j : Fin init.card) : Prop :=
  deepCancelInd h (f i) (f j) = 1

open Classical in
/-- Active deep Mains of a fixed sign, without fixing their common index. -/
def deepSignSet (h : ℕ) (σ : Sign) (f : Lab init) : Finset (Fin init.card) :=
  Finset.univ.filter fun i =>
    3 ≤ (f i).phase.val ∧ (f i).role = .main ∧
      ∃ j : Fin (hourIndex n + 1), (f i).bias = Bias.dyadic σ j ∧ h < j.val

theorem mainLevel_pos (h : ℕ) : 0 < mainLevel h := by
  unfold mainLevel
  omega

theorem mainLevel_le_clockCap {h : ℕ} (hh : h ≤ hourIndex n) :
    mainLevel h ≤ 256 * (hourIndex n + 1) := by
  unfold mainLevel
  omega

/-- At a positive level, `aboveSet` is exactly the Phase-3/minute formulation
used by `contactInd`. -/
theorem mem_aboveSet_mainLevel_iff (h : ℕ) (f : Lab init) (i : Fin init.card) :
    i ∈ aboveSet f (mainLevel h) ↔
      (f i).role = .clock ∧ 3 ≤ (f i).phase.val ∧
        mainLevel h ≤ (f i).minute.val := by
  simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hr, hm⟩
    have hp : 3 ≤ (f i).phase.val := by
      unfold effMinute at hm
      split_ifs at hm with hp
      · exact hp
      · have := mainLevel_pos h
        omega
    refine ⟨hr, hp, ?_⟩
    simpa only [effMinute, if_pos hp] using hm
  · rintro ⟨hr, hp, hm⟩
    exact ⟨hr, by simpa only [effMinute, if_pos hp] using hm⟩

/-- The fixed seed Main mask has exactly the stored Main population. -/
theorem mainSeed_mainMask_card (seed : MainSeed init) :
    (fixedRoleMask init seed.1.labels .main).card = mainSeedM init seed := by
  rw [main_mask_card]
  unfold mainSeedM
  rw [seed.2.cfg_eq]

/-- Pointwise role agreement identifies the current Clock count with the seed count. -/
theorem mainSeed_clockCount_eq (seed : MainSeed init) (f : Lab init)
    (hroles : ∀ i, (f i).role = (seed.1.labels i).role) :
    PhaseThreeClockGatedLaw.clockCount f = mainSeedC init seed := by
  have hset : clockSet f = fixedRoleMask init seed.1.labels .clock := by
    classical
    ext i
    simp only [clockSet, fixedRoleMask, Finset.mem_filter, Finset.mem_univ,
      true_and, fixedRoleL]
    rw [hroles i]
  unfold PhaseThreeClockGatedLaw.clockCount mainSeedC
  rw [hset, clock_mask_card, seed.2.cfg_eq]
  rfl

private theorem contact_condition_of_eq_one {L K : ℕ} (h : ℕ)
    (s t : AgentState L K) (heq : contactInd h s t = 1) :
    (s.role = .main ∧ t.role = .clock ∧ 3 ≤ t.phase.val ∧
        (h + 1) * K ≤ t.minute.val) ∨
      (t.role = .main ∧ s.role = .clock ∧ 3 ≤ s.phase.val ∧
        (h + 1) * K ≤ s.minute.val) := by
  unfold contactInd at heq
  split_ifs at heq with hcond
  · exact hcond

/-- Ordered Main/high-Clock contacts are at most `2 M Z`. -/
theorem goodPairs_mainContact_card_le {h : ℕ} (data : MainLive init h) :
    (goodPairs (MainContactPair init h) data.lab).card ≤
      2 * mainSeedM init data.seed * data.front := by
  classical
  let Mset := fixedRoleMask init data.seed.1.labels .main
  let Zset := aboveSet data.lab (mainLevel h)
  have hsub : goodPairs (MainContactPair init h) data.lab ⊆
      (Mset ×ˢ Zset) ∪ (Zset ×ˢ Mset) := by
    rintro ⟨i, j⟩ hp
    simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hij, hpair⟩ := hp
    rcases contact_condition_of_eq_one h (data.lab i) (data.lab j) hpair with hc | hc
    · apply Finset.mem_union_left
      apply Finset.mem_product.mpr
      constructor
      · dsimp only [Mset]
        simp only [fixedRoleMask, Finset.mem_filter, Finset.mem_univ, true_and,
          fixedRoleL]
        rw [← data.valid.accepted.roles i]
        exact hc.1
      · dsimp only [Zset]
        rw [mem_aboveSet_mainLevel_iff]
        exact ⟨hc.2.1, hc.2.2.1, by unfold mainLevel; have := hc.2.2.2; omega⟩
    · apply Finset.mem_union_right
      apply Finset.mem_product.mpr
      constructor
      · dsimp only [Zset]
        rw [mem_aboveSet_mainLevel_iff]
        exact ⟨hc.2.1, hc.2.2.1, by unfold mainLevel; have := hc.2.2.2; omega⟩
      · dsimp only [Mset]
        simp only [fixedRoleMask, Finset.mem_filter, Finset.mem_univ, true_and,
          fixedRoleL]
        rw [← data.valid.accepted.roles j]
        exact hc.1
  calc
    (goodPairs (MainContactPair init h) data.lab).card ≤
        ((Mset ×ˢ Zset) ∪ (Zset ×ˢ Mset)).card := Finset.card_le_card hsub
    _ ≤ (Mset ×ˢ Zset).card + (Zset ×ˢ Mset).card := Finset.card_union_le _ _
    _ = 2 * mainSeedM init data.seed * data.front := by
      simp only [Finset.card_product]
      rw [show Mset.card = mainSeedM init data.seed by
        simpa only [Mset] using mainSeed_mainMask_card init data.seed]
      rw [show Zset.card = data.front by
        simpa only [Zset, PhaseThreeClockGatedLaw.frontCount] using data.valid.accepted.front_eq]
      ring

private theorem deepPair_signs {h : ℕ} {f : Lab init} {i j : Fin init.card}
    (hp : MainDeepPair init h f i j) :
    (i ∈ deepSignSet init h .pos f ∧ j ∈ deepSignSet init h .neg f) ∨
      (i ∈ deepSignSet init h .neg f ∧ j ∈ deepSignSet init h .pos f) := by
  unfold MainDeepPair deepCancelInd at hp
  split_ifs at hp with hactive
  · obtain ⟨hi3, hj3, him, hjm⟩ := hactive
    cases hib : (f i).bias with
    | zero => simp [cancelIdx, hib] at hp
    | dyadic σi ki =>
      cases hjb : (f j).bias with
      | zero => cases σi <;> simp [cancelIdx, hib, hjb] at hp
      | dyadic σj kj =>
        cases σi <;> cases σj
        · simp [cancelIdx, hib, hjb] at hp
        · simp only [cancelIdx, hib, hjb] at hp
          split_ifs at hp with hk
          · left
            constructor
            · simp [deepSignSet, hib, hi3, him, hk.2]
            · have hkj : h < kj.val := by rw [← hk.1]; exact hk.2
              simp [deepSignSet, hjb, hj3, hjm, hkj]
        · simp only [cancelIdx, hib, hjb] at hp
          split_ifs at hp with hk
          · right
            constructor
            · simp [deepSignSet, hib, hi3, him, hk.2]
            · have hkj : h < kj.val := by rw [← hk.1]; exact hk.2
              simp [deepSignSet, hjb, hj3, hjm, hkj]
        · simp [cancelIdx, hib, hjb] at hp

/-- Deep cancellation pairs lie in the two sign orientations. -/
theorem goodPairs_mainDeep_card_le (h : ℕ) (f : Lab init) :
    (goodPairs (MainDeepPair init h) f).card ≤
      2 * (deepSignSet init h .pos f).card *
        (deepSignSet init h .neg f).card := by
  classical
  let P := deepSignSet init h .pos f
  let N := deepSignSet init h .neg f
  have hsub : goodPairs (MainDeepPair init h) f ⊆
      (P ×ˢ N) ∪ (N ×ˢ P) := by
    rintro ⟨i, j⟩ hp
    have hpair : MainDeepPair init h f i j :=
      (Finset.mem_filter.mp hp).2.2
    rcases deepPair_signs init hpair with h | h
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr h)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr h)
  calc
    (goodPairs (MainDeepPair init h) f).card ≤
        ((P ×ˢ N) ∪ (N ×ˢ P)).card := Finset.card_le_card hsub
    _ ≤ (P ×ˢ N).card + (N ×ˢ P).card := Finset.card_union_le _ _
    _ = 2 * P.card * N.card := by
      simp only [Finset.card_product]
      ring

/-- The two signed deep populations together are bounded by `vSum`. -/
theorem deepSign_card_add_le_vSum (h : ℕ) (f : Lab init) :
    (deepSignSet init h .pos f).card +
        (deepSignSet init h .neg f).card ≤ vSum init h f := by
  classical
  unfold deepSignSet
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  unfold vSum
  apply Finset.sum_le_sum
  intro i _
  dsimp only
  cases hb : (f i).bias with
  | zero => simp [deepSignSet, creditV, deepInd, deepIdx, hb]
  | dyadic σ j =>
      cases σ <;>
        simp only [deepSignSet, Finset.mem_filter, Finset.mem_univ, true_and,
          hb, Bias.dyadic.injEq, exists_eq_right, reduceCtorEq, and_false,
          false_and, if_false, creditV, deepInd, deepIdx] <;>
        split_ifs <;> simp_all <;> omega

/-- The credit-weighted deep-cancellation count is at most `4 A²`. -/
theorem weighted_mainDeep_card_le {h : ℕ} (data : MainLive init h) :
    2 * ((goodPairs (MainDeepPair init h) data.lab).card : ℝ) ≤
      4 * (data.credit : ℝ) ^ 2 := by
  let p := (deepSignSet init h .pos data.lab).card
  let q := (deepSignSet init h .neg data.lab).card
  let B := vSum init h data.lab
  have hJnat := goodPairs_mainDeep_card_le init h data.lab
  have hpqnat : p + q ≤ B := by
    simpa only [p, q, B] using deepSign_card_add_le_vSum init h data.lab
  have hBAnat : B ≤ 2 * data.credit := by
    simpa only [B] using data.valid.accepted.vertical_le
  have hJ :
      ((goodPairs (MainDeepPair init h) data.lab).card : ℝ) ≤
        2 * (p : ℝ) * (q : ℝ) := by exact_mod_cast hJnat
  have hpq : (p : ℝ) + (q : ℝ) ≤ (B : ℝ) := by exact_mod_cast hpqnat
  have hBA : (B : ℝ) ≤ 2 * (data.credit : ℝ) := by exact_mod_cast hBAnat
  exact ordered_cancel_weight_le hJ (Nat.cast_nonneg p) (Nat.cast_nonneg q)
    (Nat.cast_nonneg B) (Nat.cast_nonneg data.credit) hpq hBA

/-- The gated raising count is at least the epidemic term `2 Z (C-Z)`. -/
theorem goodPairs_mainRaising_card_ge {h : ℕ} (data : MainLive init h) :
    2 * data.front * (mainSeedC init data.seed - data.front) ≤
      (goodPairs (GatedTick (mainLevel h)) data.lab).card := by
  have hraw := epidemic_le_gated_pairs data.lab (mainLevel h)
    (show 1 ≤ mainLevel h by have := mainLevel_pos h; omega)
  rw [data.valid.accepted.front_eq,
    mainSeed_clockCount_eq init data.seed data.lab data.valid.accepted.roles] at hraw
  exact hraw

private theorem ruleUpdate_property
    {L K m : ℕ} (P : AgentState L K → Prop)
    (f : Fin m → AgentState L K) (i j : Fin m) (hij : i ≠ j)
    (hout : P (virtualRule (f i) (f j)).1 ∧
      P (virtualRule (f i) (f j)).2) (hall : ∀ k, P (f k)) :
    ∀ k, P (ruleUpdate virtualRule f i j k) := by
  intro k
  by_cases hkj : k = j
  · subst k
    simpa only [ruleUpdate, Function.update_self] using hout.2
  · by_cases hki : k = i
    · subst k
      simpa only [ruleUpdate, Function.update_of_ne hij,
        Function.update_self] using hout.1
    · simpa only [ruleUpdate, Function.update_of_ne hkj,
        Function.update_of_ne hki] using hall k

/-- Every gated raising tick satisfies the next-state accepted guard.  Therefore a
rejected sampled step has zero raising atom. -/
theorem mainAccepted_of_gated {h : ℕ} (hh : h ≤ hourIndex n)
    (data : MainLive init h) (i j : Fin init.card) (hij : i ≠ j)
    (hg : GatedTick (mainLevel h) data.lab i j) :
    MainAcceptedCondition init h data.seed
      (ruleUpdate virtualRule data.lab i j)
      (mainNextCredit init data (some (i, j)))
      (mainNextFront init data (some (i, j))) := by
  have hclock := gatedTick_clock_roles data.lab (mainLevel h) i j hg
  have henv := data.valid.accepted.environment
  have hiReg := henv.clock_regime i hclock.1
  have hjReg := henv.clock_regime j hclock.2
  have hactive : (data.lab i).phase.val = 3 ∨ (data.lab j).phase.val = 3 := by
    rcases hg.2 with hi | hj
    · exact Or.inl (le_antisymm (henv.phase_range i).2 hi)
    · exact Or.inr (le_antisymm (henv.phase_range j).2 hj)
  obtain ⟨hri, hrj, hpi, hpj, -, -⟩ :=
    virtualRule_clock_pair_some_active (data.lab i) (data.lab j)
      (by norm_num) hiReg hjReg hactive
  have hcarrier := virtualRule_preserves_carrier (data.lab i) (data.lab j)
    (henv.carrier i) (henv.carrier j)
  have hcreditZero : mainPairCredit init h data.lab (some (i, j)) = 0 := by
    simp [mainPairCredit, contactInd, deepCancelInd, hclock.1, hclock.2]
  have hraisingOne : mainPairRaising init h data.lab (some (i, j)) = 1 := by
    simp [mainPairRaising, hg]
  have hv := sum_update_pair (creditV h) data.lab i j hij
    (virtualRule (data.lab i) (data.lab j)).1
    (virtualRule (data.lab i) (data.lab j)).2
  have hhour := sum_update_pair (highHourInd h) data.lab i j hij
    (virtualRule (data.lab i) (data.lab j)).1
    (virtualRule (data.lab i) (data.lab j)).2
  have hvi : creditV h (data.lab i) = 0 :=
    creditV_eq_zero_of_not_main h _ (by rw [hclock.1]; decide)
  have hvj : creditV h (data.lab j) = 0 :=
    creditV_eq_zero_of_not_main h _ (by rw [hclock.2]; decide)
  have hvoi : creditV h (virtualRule (data.lab i) (data.lab j)).1 = 0 :=
    creditV_eq_zero_of_not_main h _ (by rw [hri]; decide)
  have hvoj : creditV h (virtualRule (data.lab i) (data.lab j)).2 = 0 :=
    creditV_eq_zero_of_not_main h _ (by rw [hrj]; decide)
  have hhi : highHourInd h (data.lab i) = 0 :=
    highHourInd_eq_zero_of_not_main h _ (by rw [hclock.1]; decide)
  have hhj : highHourInd h (data.lab j) = 0 :=
    highHourInd_eq_zero_of_not_main h _ (by rw [hclock.2]; decide)
  have hhoi : highHourInd h (virtualRule (data.lab i) (data.lab j)).1 = 0 :=
    highHourInd_eq_zero_of_not_main h _ (by rw [hri]; decide)
  have hhoj : highHourInd h (virtualRule (data.lab i) (data.lab j)).2 = 0 :=
    highHourInd_eq_zero_of_not_main h _ (by rw [hrj]; decide)
  have hvEq :
      vSum init h (ruleUpdate virtualRule data.lab i j) =
        vSum init h data.lab := by
    unfold vSum
    simp only [ruleUpdate] at hv ⊢
    omega
  have hhEq :
      hSum init h (ruleUpdate virtualRule data.lab i j) =
        hSum init h data.lab := by
    unfold hSum
    simp only [ruleUpdate] at hhour ⊢
    omega
  refine
    { environment := ?_
      roles := ?_
      front_eq := ?_
      vertical_le := ?_
      hour_le := ?_ }
  · refine
      { phase_range := ruleUpdate_property
          (fun a => 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
          data.lab i j hij ⟨by omega, by omega⟩ henv.phase_range
        carrier := ruleUpdate_property nonMainCarrierSmallBiasZeroAgent
          data.lab i j hij hcarrier henv.carrier }
  · intro k
    by_cases hkj : k = j
    · subst k
      simp only [ruleUpdate, Function.update_self, hrj]
      exact hclock.2.symm.trans (data.valid.accepted.roles j)
    · by_cases hki : k = i
      · subst k
        simp only [ruleUpdate, Function.update_of_ne hij, Function.update_self, hri]
        exact hclock.1.symm.trans (data.valid.accepted.roles i)
      · simp only [ruleUpdate, Function.update_of_ne hkj,
          Function.update_of_ne hki]
        exact data.valid.accepted.roles k
  · have hfront := frontCount_ruleUpdate_clock_pair_some_active data.lab
      (by norm_num) i j hij hiReg hjReg hactive (mainLevel h)
      (show 1 ≤ mainLevel h by have := mainLevel_pos h; omega)
      (mainLevel_le_clockCap hh)
    rw [hfront, if_pos hg.1, data.valid.accepted.front_eq]
    simp only [mainNextFront, hraisingOne]
  · rw [mainNextCredit, hcreditZero, add_zero, hvEq]
    exact data.valid.accepted.vertical_le
  · rw [mainNextCredit, hcreditZero, add_zero, hhEq]
    exact data.valid.accepted.hour_le

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainPairCounts

end
