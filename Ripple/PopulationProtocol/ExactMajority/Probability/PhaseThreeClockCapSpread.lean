import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRegime
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProductTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockProbabilityFloors

/-!
# The cap level on the virtual path (N12, step 4: P13/P14 structural layer)

The step-4 estimates of PHASE3 (the all-cap deadline P13, the local cap spread and the
contact budget P14) are statements about the top level `Q = clockTop n` of the virtual
front from an asynchronous entry. This file collects the deterministic and one-step
facts they share:

* `topCount init ω t = X_Q(t)`, the number of Clocks at the cap minute at time `t`, with
  its one-step law `topCount_succ` (the gated-tick indicator of level `Q`, from
  `PhaseThreeClockEmbeddingBridge.frontCount_virtualLabels_succ_of_asyncEntry`) and its
  monotonicity after the seed;
* the pair events of a step and their exact or one-sided counts: `CCPair` (two Clocks,
  `C (C - 1)` ordered pairs), `TagPair i₀` (a Clock pair containing `i₀`, at most
  `2 (C - 1)`), `HitPair j` (`j` meets a capped Clock, at least `2 X_Q`), and the gated
  tick of level `Q` (`2 X_Q (C - X_Q) + Y (Y - 1)`), with the conditional law of the
  corresponding step indicator `pairInd` given the pair log
  (`PairLogAuxiliary.aux_pair_conditional_probability`);
* a capped Phase-3 Clock stays capped under every virtual interaction after the seed
  (`capped_persist`), and an uncapped Phase-3 Clock meeting a capped Clock is capped
  after the step (`capped_of_hitPair`);
* the window predicates used by the step-4 products (`reachedOne`, `reachedBulk`,
  `reachedHigh`, `allCapAt`) are first-hit events of the canonical witness, and are
  measurable at the current time.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapSpread

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockProductTails PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockProbabilityFloors PhaseThreeClockRegime
open StageEventSpec hiding frontCount clockCount

variable {n : ℕ} (init : InputCfg n)

/-! ## Labelling-level counts -/

theorem two_le_clockTop : 2 ≤ clockTop n := by
  unfold clockTop
  omega

theorem one_le_clockTop : 1 ≤ clockTop n := le_trans (by norm_num) two_le_clockTop

/-- The row front count with the roles of `fS` is the current-roles front count when
the roles agree. -/
theorem frontCountL_eq_frontCount (fS fv : Lab init)
    (hr : ∀ i, (fv i).role = (fS i).role) (ℓ : ℕ) :
    frontCountL init fS fv ℓ = frontCount fv ℓ := by
  classical
  unfold frontCountL labelCount frontCount aboveSet
  rw [Finset.card_filter, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  have heff : effectiveMinuteL init fv i = effMinute (fv i) := by
    unfold effectiveMinuteL effMinute activeL
    split_ifs <;> first | rfl | omega
  have hrole : fixedRoleL init fS .clock i ↔ (fv i).role = .clock := by
    unfold fixedRoleL
    rw [hr i]
  by_cases h : (fv i).role = .clock ∧ ℓ ≤ effMinute (fv i)
  · rw [if_pos h, if_pos ⟨hrole.mpr h.1, by rw [heff]; exact h.2⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨hrole.mp h'.1, by rw [← heff]; exact h'.2⟩)]

theorem clockCount_virtualCfg_eq (ω : InputLog n) (t : ℕ) :
    StageEventSpec.clockCount (virtualCfg init ω t) = clockCount (virtualLabels init ω t) := by
  rw [virtualCfg_eq_labelCfg]
  unfold StageEventSpec.clockCount
  rw [countP_role_labelCfg]
  rfl

/-- The pair events of a step. -/
def CCPair (f : Lab init) (i j : Fin init.card) : Prop :=
  (f i).role = .clock ∧ (f j).role = .clock

def TagPair (i₀ : Fin init.card) (f : Lab init) (i j : Fin init.card) : Prop :=
  CCPair init f i j ∧ (i = i₀ ∨ j = i₀)

/-- A capped Clock label: a Clock with effective minute at the cap. -/
def Capped (f : Lab init) (j : Fin init.card) : Prop := j ∈ aboveSet f (clockTop n)

theorem capped_iff (f : Lab init) (j : Fin init.card) :
    Capped init f j ↔ (f j).role = .clock ∧ clockTop n ≤ effMinute (f j) := by
  unfold Capped aboveSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The drawn pair lets `j` meet a capped Clock. -/
def HitPair (j : Fin init.card) (f : Lab init) (i i' : Fin init.card) : Prop :=
  (i = j ∧ Capped init f i') ∨ (i' = j ∧ Capped init f i)

theorem gatedTick_ccPair (f : Lab init) (i j : Fin init.card)
    (h : GatedTick (clockTop n) f i j) : CCPair init f i j := by
  constructor
  · by_contra hc
    exact not_gatedTick_of_not_clock_left _ f i j hc h
  · by_contra hc
    exact not_gatedTick_of_not_clock_right _ f i j hc h

theorem goodPairs_ccPair_eq (f : Lab init) :
    goodPairs (CCPair init) f = (clockSet f).offDiag := by
  ext ⟨i, j⟩
  simp only [goodPairs, CCPair, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_offDiag, clockSet]
  tauto

theorem goodPairs_ccPair_card (f : Lab init) :
    (goodPairs (CCPair init) f).card = clockCount f * (clockCount f - 1) := by
  rw [goodPairs_ccPair_eq, Finset.offDiag_card, Nat.mul_sub_one]
  rfl

theorem goodPairs_tagPair_card_le (i₀ : Fin init.card) (f : Lab init)
    (hi₀ : (f i₀).role = .clock) :
    (goodPairs (TagPair init i₀) f).card ≤ 2 * (clockCount f - 1) := by
  classical
  have hi₀C : i₀ ∈ clockSet f := by
    simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and, hi₀]
  let S₁ : Finset (Fin init.card × Fin init.card) :=
    ((clockSet f).erase i₀).image (fun l => (i₀, l))
  let S₂ : Finset (Fin init.card × Fin init.card) :=
    ((clockSet f).erase i₀).image (fun l => (l, i₀))
  have hsub : goodPairs (TagPair init i₀) f ⊆ S₁ ∪ S₂ := by
    rintro ⟨i, j⟩ h
    simp only [goodPairs, TagPair, CCPair, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨hij, ⟨hi, hj⟩, hor⟩ := h
    rcases hor with rfl | rfl
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_erase.mpr ⟨fun h => hij h.symm, ?_⟩, rfl⟩
      simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and, hj]
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_erase.mpr ⟨hij, ?_⟩, rfl⟩
      simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and, hi]
  have h1 : S₁.card ≤ clockCount f - 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem hi₀C]
    exact le_rfl
  have h2 : S₂.card ≤ clockCount f - 1 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem hi₀C]
    exact le_rfl
  calc (goodPairs (TagPair init i₀) f).card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsub
    _ ≤ S₁.card + S₂.card := Finset.card_union_le _ _
    _ ≤ 2 * (clockCount f - 1) := by omega

theorem goodPairs_hitPair_card_ge (j : Fin init.card) (f : Lab init)
    (hj : ¬ Capped init f j) :
    2 * frontCount f (clockTop n) ≤ (goodPairs (HitPair init j) f).card := by
  classical
  let S₁ : Finset (Fin init.card × Fin init.card) :=
    (aboveSet f (clockTop n)).image (fun l => (j, l))
  let S₂ : Finset (Fin init.card × Fin init.card) :=
    (aboveSet f (clockTop n)).image (fun l => (l, j))
  have hS₁ : S₁ ⊆ goodPairs (HitPair init j) f := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    have hcl : Capped init f l := hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun h => hj (by have h' : j = l := h; exact h'.symm ▸ hcl), Or.inl ⟨rfl, hcl⟩⟩
  have hS₂ : S₂ ⊆ goodPairs (HitPair init j) f := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    have hcl : Capped init f l := hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun h => hj (by have h' : l = j := h; exact h' ▸ hcl), Or.inr ⟨rfl, hcl⟩⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp1
    obtain ⟨l', hl', hEq⟩ := Finset.mem_image.mp hp2
    have : l' = j := (Prod.mk.inj hEq).1
    exact hj (this ▸ hl')
  have hc1 : S₁.card = frontCount f (clockTop n) :=
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)
  have hc2 : S₂.card = frontCount f (clockTop n) :=
    Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)
  calc 2 * frontCount f (clockTop n) = S₁.card + S₂.card := by rw [hc1, hc2, two_mul]
    _ = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (goodPairs (HitPair init j) f).card :=
        Finset.card_le_card (Finset.union_subset hS₁ hS₂)

/-- PHASE3 (25) at the top level: the gated count is the raising count. -/
theorem goodPairs_gatedTick_top_card (f : Lab init) :
    (goodPairs (GatedTick (clockTop n)) f).card =
      2 * frontCount f (clockTop n) * (clockCount f - frontCount f (clockTop n)) +
        exactCount f (clockTop n - 1) * (exactCount f (clockTop n - 1) - 1) := by
  rw [goodPairs_gatedTick_eq_of_two_le f _ two_le_clockTop, goodPairs_raisingTick_card]

/-! ## The step indicators and their conditional laws -/

variable (ω : InputLog n)

open Classical in
/-- The indicator that the pair drawn at `t + 1` satisfies `A` at the virtual labelling of
time `t`. -/
def pairInd (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) (ω : InputLog n) :
    ℝ :=
  if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧ A (virtualLabels init ω t) i j
  then 1 else 0

theorem pairInd_stronglyMeasurable (A : Lab init → Fin init.card → Fin init.card → Prop)
    (t : ℕ) :
    StronglyMeasurable[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 (t + 1)]
      (pairInd init A t) :=
  stronglyMeasurable_aux_pair_indicator init virtualRule A t

theorem pairInd_zero_one (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ)
    (ω : InputLog n) : pairInd init A t ω = 0 ∨ pairInd init A t ω = 1 := by
  unfold pairInd
  split_ifs <;> simp

theorem pairInd_nonneg (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ)
    (ω : InputLog n) : 0 ≤ pairInd init A t ω := by
  rcases pairInd_zero_one init A t ω with h | h <;> rw [h] <;> norm_num

theorem pairInd_le_one (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ)
    (ω : InputLog n) : pairInd init A t ω ≤ 1 := by
  rcases pairInd_zero_one init A t ω with h | h <;> rw [h] <;> norm_num

theorem pairInd_mono {A B : Lab init → Fin init.card → Fin init.card → Prop}
    (h : ∀ f i j, A f i j → B f i j) (t : ℕ) (ω : InputLog n) :
    pairInd init A t ω ≤ pairInd init B t ω := by
  unfold pairInd
  split_ifs with hA hB hB
  · exact le_rfl
  · exact absurd (by obtain ⟨i, j, hd, hij⟩ := hA; exact ⟨i, j, hd, h _ i j hij⟩) hB
  · norm_num
  · exact le_rfl

theorem pairInd_integrable (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    Integrable (pairInd init A t) (law init) :=
  bernoulli_integrable (ℱ := pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256)
    (pairInd_stronglyMeasurable init A) (fun t => ae_of_all _ (pairInd_zero_one init A t)) t

/-- The conditional probability of a step event given the pair log is its ordered-pair
fraction at the current virtual labelling. -/
theorem pairInd_condExp (hc : 2 ≤ init.card)
    (A : Lab init → Fin init.card → Fin init.card → Prop) (t : ℕ) :
    (law init)[pairInd init A t |
        pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t] =ᵐ[law init]
      fun ω => ((goodPairs A (virtualLabels init ω t)).card : ℝ) /
        ((init.card : ℝ) * ((init.card : ℝ) - 1)) :=
  aux_pair_conditional_probability init hc virtualRule A t

/-! ## The top level on the virtual path -/

/-- `X_Q(t)`: the Clocks at the cap minute at time `t` on the virtual path. -/
def topCount (t : ℕ) : ℕ := frontCount (virtualLabels init ω t) (clockTop n)

theorem topCount_le_clockCount (t : ℕ) :
    topCount init ω t ≤ clockCount (virtualLabels init ω t) :=
  frontCount_le_clockCount _ _

/-- One step of the top level after the seed: the gated-tick indicator of level `Q`. -/
theorem topCount_succ {S T : ℕ} (hentry : AsyncEntry init ω S T) (t : ℕ) (hSt : S ≤ t) :
    (topCount init ω (t + 1) : ℝ) =
      topCount init ω t + pairInd init (GatedTick (clockTop n)) t ω := by
  classical
  unfold pairInd
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      unfold topCount
      rw [frontCount_virtualLabels_succ_of_none init ω t hd]
      simp [hd]
  | some p =>
      obtain ⟨i, j⟩ := p
      unfold topCount
      rw [frontCount_virtualLabels_succ_of_asyncEntry init ω S T hentry t hSt i j hd
        (clockTop n) one_le_clockTop le_rfl]
      push_cast
      congr 1
      by_cases hg : GatedTick (clockTop n) (virtualLabels init ω t) i j
      · rw [if_pos hg, if_pos ⟨i, j, rfl, hg⟩]
      · rw [if_neg hg, if_neg]
        rintro ⟨i', j', hd', hg'⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hd')
        exact hg hg'

theorem topCount_succ_nat {S T : ℕ} (hentry : AsyncEntry init ω S T) (t : ℕ) (hSt : S ≤ t) :
    topCount init ω t ≤ topCount init ω (t + 1) ∧
      topCount init ω (t + 1) ≤ topCount init ω t + 1 := by
  have h := topCount_succ init ω hentry t hSt
  rcases pairInd_zero_one init (GatedTick (clockTop n)) t ω with h0 | h1
  · rw [h0, add_zero] at h
    have : topCount init ω (t + 1) = topCount init ω t := by exact_mod_cast h
    omega
  · rw [h1] at h
    have : topCount init ω (t + 1) = topCount init ω t + 1 := by exact_mod_cast h
    omega

theorem topCount_mono {S T : ℕ} (hentry : AsyncEntry init ω S T) {t t' : ℕ} (hSt : S ≤ t)
    (htt : t ≤ t') : topCount init ω t ≤ topCount init ω t' := by
  induction t', htt using Nat.le_induction with
  | base => exact le_rfl
  | succ t' htt ih =>
      exact ih.trans (topCount_succ_nat init ω hentry t' (by omega)).1

/-- The row front count at the top level is `topCount`. -/
theorem frontCountL_top_eq {S T : ℕ} (hentry : AsyncEntry init ω S T) (v : ℕ) (hSv : S ≤ v) :
    frontCountL init (virtualLabels init ω S) (virtualLabels init ω v) (clockTop n) =
      topCount init ω v := by
  apply frontCountL_eq_frontCount
  intro i
  have hroles := virtualLabels_roles_fixed_of_asyncEntry init ω S T hentry
  exact (hroles v hSv i).trans (hroles S le_rfl i).symm

theorem clockCount_virtual_eq_seed {S T : ℕ} (hentry : AsyncEntry init ω S T) (v : ℕ)
    (hSv : S ≤ v) :
    clockCount (virtualLabels init ω v) = clockCount (virtualLabels init ω S) := by
  unfold clockCount
  rw [clockSet_virtualLabels_eq_seed init ω S T hentry v hSv,
    clockSet_virtualLabels_eq_seed init ω S T hentry S le_rfl]

/-! ## Capped Clocks persist; a hit caps -/

theorem clockRegime_virtual {S T : ℕ} (hentry : AsyncEntry init ω S T) (t : ℕ) (hSt : S ≤ t)
    (i : Fin init.card) (hi : (virtualLabels init ω t i).role = .clock) :
    ClockRegime (virtualLabels init ω t i) :=
  (virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry t hSt).clock_regime i hi

theorem minute_le_clockTop (a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) :
    a.minute.val ≤ clockTop n := by
  have := a.minute.isLt
  unfold clockTop
  omega

theorem effMinute_le_clockTop (a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256) :
    effMinute a ≤ clockTop n := by
  unfold effMinute
  split_ifs
  · exact minute_le_clockTop a
  · exact Nat.zero_le _

theorem phase_three_of_capped (f : Lab init) (j : Fin init.card) (hj : Capped init f j)
    (hle : (f j).phase.val ≤ 3) : (f j).phase.val = 3 := by
  rw [capped_iff] at hj
  have h := hj.2
  unfold effMinute at h
  split_ifs at h with h3
  · omega
  · have := one_le_clockTop (n := n)
    omega

/-- A capped Clock keeps the cap through one virtual interaction after the seed. -/
theorem capped_succ {S T : ℕ} (hentry : AsyncEntry init ω S T) (t : ℕ) (hSt : S ≤ t)
    (j : Fin init.card) (hj : Capped init (virtualLabels init ω t) j) :
    Capped init (virtualLabels init ω (t + 1)) j := by
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  have hreg := (henv t hSt)
  have hpost := (henv (t + 1) (by omega)).phase_range
  have hjr : (virtualLabels init ω t j).role = .clock := ((capped_iff init _ j).mp hj).1
  have hjm : clockTop n ≤ effMinute (virtualLabels init ω t j) := ((capped_iff init _ j).mp hj).2
  have hjeff : effMinute (virtualLabels init ω t j) = clockTop n :=
    le_antisymm (effMinute_le_clockTop _) hjm
  have hj3 : (virtualLabels init ω t j).phase.val = 3 :=
    phase_three_of_capped init _ j hj (hreg.phase_range j).2
  have hjreg : ClockRegime (virtualLabels init ω t j) := hreg.clock_regime j hjr
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      rw [PhaseThreeClockReserve.virtualLabels_succ_none init ω hd]
      exact hj
  | some p =>
      obtain ⟨a, b⟩ := p
      have hab : a ≠ b := (labelsAt_selected_transition init ω t a b hd).1
      by_cases hja : j = a
      · subst hja
        rw [capped_iff, PhaseThreeClockReserve.virtualLabels_succ_left init ω hd hab]
        set s := virtualLabels init ω t j with hs
        set x := virtualLabels init ω t b with hx
        by_cases hxc : x.role = .clock
        · have hxreg : ClockRegime x := hreg.clock_regime b hxc
          obtain ⟨h1, -, h3, -, h5, -⟩ :=
            virtualRule_clock_pair_some_active s x (by norm_num) hjreg hxreg (Or.inl hj3)
          refine ⟨h1, ?_⟩
          rw [effMinute_eq_minute_of_three _ h3, h5, hjeff]
          have hxle := effMinute_le_clockTop x
          split_ifs with hne hlt
          · exact le_max_left _ _
          · exfalso
            unfold clockTop at hlt
            omega
          · exact le_rfl
        · have hleft : (virtualRule s x).1.phase.val ≤ 3 := by
            have := (hpost j).2
            rwa [PhaseThreeClockReserve.virtualLabels_succ_left init ω hd hab] at this
          have hright : (virtualRule s x).2.phase.val ≤ 3 := by
            have := (hpost b).2
            rwa [PhaseThreeClockReserve.virtualLabels_succ_right init ω hd] at this
          have hnb := virtualRule_no_backup_of_phase_le_three s x hleft hright
          obtain ⟨h1, h2, -, -⟩ := virtualRule_clock_nonclock s x hjreg hxc
            (hreg.phase_range b).1 (hreg.phase_range b).2 hnb
          exact ⟨h1, by rw [h2]; exact hjm⟩
      · by_cases hjb : j = b
        · subst hjb
          rw [capped_iff, PhaseThreeClockReserve.virtualLabels_succ_right init ω hd]
          set s := virtualLabels init ω t j with hs
          set x := virtualLabels init ω t a with hx
          by_cases hxc : x.role = .clock
          · have hxreg : ClockRegime x := hreg.clock_regime a hxc
            obtain ⟨-, h2, -, h4, -, h6⟩ :=
              virtualRule_clock_pair_some_active x s (by norm_num) hxreg hjreg (Or.inr hj3)
            refine ⟨h2, ?_⟩
            rw [effMinute_eq_minute_of_three _ h4, h6, hjeff]
            split_ifs with hne
            · exact le_max_right _ _
            · exact le_rfl
          · have hleft : (virtualRule x s).1.phase.val ≤ 3 := by
              have := (hpost a).2
              rwa [PhaseThreeClockReserve.virtualLabels_succ_left init ω hd hab] at this
            have hright : (virtualRule x s).2.phase.val ≤ 3 := by
              have := (hpost j).2
              rwa [PhaseThreeClockReserve.virtualLabels_succ_right init ω hd] at this
            have hnb := virtualRule_no_backup_of_phase_le_three x s hleft hright
            obtain ⟨h1, h2, -, -⟩ := virtualRule_nonclock_clock x s hjreg hxc
              (hreg.phase_range a).1 (hreg.phase_range a).2 hnb
            exact ⟨h1, by rw [h2]; exact hjm⟩
        · rw [capped_iff, PhaseThreeClockReserve.virtualLabels_succ_other init ω hd hja hjb,
            ← capped_iff]
          exact hj

theorem capped_persist {S T : ℕ} (hentry : AsyncEntry init ω S T) {t t' : ℕ} (hSt : S ≤ t)
    (htt : t ≤ t') (j : Fin init.card) (hj : Capped init (virtualLabels init ω t) j) :
    Capped init (virtualLabels init ω t') j := by
  induction t', htt using Nat.le_induction with
  | base => exact hj
  | succ t' htt ih => exact capped_succ init ω hentry t' (by omega) j ih

/-- A Phase-3 Clock that meets a capped Clock is capped after the step. -/
theorem capped_of_hitPair {S T : ℕ} (hentry : AsyncEntry init ω S T) (t : ℕ) (hSt : S ≤ t)
    (j : Fin init.card) (hjr : (virtualLabels init ω t j).role = .clock)
    (hj3 : (virtualLabels init ω t j).phase.val = 3)
    (a b : Fin init.card) (hd : drawLabels init ω (t + 1) = some (a, b))
    (hhit : HitPair init j (virtualLabels init ω t) a b) :
    Capped init (virtualLabels init ω (t + 1)) j := by
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  have hreg := henv t hSt
  have hab : a ≠ b := (labelsAt_selected_transition init ω t a b hd).1
  have hjreg : ClockRegime (virtualLabels init ω t j) := hreg.clock_regime j hjr
  rcases hhit with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
  · rw [capped_iff, PhaseThreeClockReserve.virtualLabels_succ_left init ω hd hab]
    have hbr : (virtualLabels init ω t b).role = .clock := ((capped_iff init _ b).mp hb).1
    have hbm : clockTop n ≤ effMinute (virtualLabels init ω t b) := ((capped_iff init _ b).mp hb).2
    have hbreg : ClockRegime (virtualLabels init ω t b) := hreg.clock_regime b hbr
    obtain ⟨h1, -, h3, -, h5, -⟩ := virtualRule_clock_pair_some_active
      (virtualLabels init ω t a) (virtualLabels init ω t b) (by norm_num) hjreg hbreg (Or.inl hj3)
    refine ⟨h1, ?_⟩
    rw [effMinute_eq_minute_of_three _ h3, h5]
    split_ifs with hne hlt
    · exact hbm.trans (le_max_right _ _)
    · exfalso
      push_neg at hne
      unfold clockTop at hbm
      omega
    · push_neg at hne
      rw [hne]
      exact hbm
  · rw [capped_iff, PhaseThreeClockReserve.virtualLabels_succ_right init ω hd]
    have har : (virtualLabels init ω t a).role = .clock := ((capped_iff init _ a).mp ha).1
    have ham : clockTop n ≤ effMinute (virtualLabels init ω t a) := ((capped_iff init _ a).mp ha).2
    have hareg : ClockRegime (virtualLabels init ω t a) := hreg.clock_regime a har
    obtain ⟨-, h2, -, h4, -, h6⟩ := virtualRule_clock_pair_some_active
      (virtualLabels init ω t a) (virtualLabels init ω t b) (by norm_num) hareg hjreg (Or.inr hj3)
    refine ⟨h2, ?_⟩
    rw [effMinute_eq_minute_of_three _ h4, h6]
    split_ifs with hne
    · exact ham.trans (le_max_left _ _)
    · push_neg at hne
      rw [← hne]
      exact ham

open Classical in
/-- Capped Clocks are exactly the labels counted by `topCount`. -/
theorem topCount_eq_card_capped (t : ℕ) :
    topCount init ω t = (Finset.univ.filter (Capped init (virtualLabels init ω t))).card := by
  unfold topCount frontCount Capped
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A Clock in Phase 3 at the seed-initialized time stays in Phase 3 (virtual counter
ledger). -/
theorem clock_phase_three_after {S T : ℕ} (hentry : AsyncEntry init ω S T) (i : Fin init.card)
    (hi : (virtualLabels init ω S i).role = .clock) {τ v : ℕ} (hSτ : S ≤ τ)
    (hτ3 : 3 ≤ (virtualLabels init ω τ i).phase.val) (hτv : τ ≤ v) :
    (virtualLabels init ω v i).phase.val = 3 := by
  have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω S T hentry
  have h3 : (virtualLabels init ω τ i).phase.val = 3 :=
    le_antisymm ((henv τ hSτ).phase_range i).2 hτ3
  exact (PhaseThreeClockReserve.virtual_counter_ledger init ω hentry i hi τ hSτ h3 v hτv).1

/-! ## Measurability of state predicates at the current time -/

theorem measurableSet_virtual_single {v t : ℕ} (hv : v ≤ t) (P : Lab init → Prop) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | P (virtualLabels init ω v)} := by
  have h := (measurable_virtualLabels init v).mono
    ((pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256).mono hv) le_rfl
  exact (show MeasurableSet {f : Lab init | P f} from
    (Set.to_countable _).measurableSet).preimage h

theorem measurableSet_virtual_pair {s v t : ℕ} (hs : s ≤ t) (hv : v ≤ t)
    (P : Lab init → Lab init → Prop) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | P (virtualLabels init ω s) (virtualLabels init ω v)} := by
  have hset : {ω | P (virtualLabels init ω s) (virtualLabels init ω v)} =
      ⋃ f : Lab init, ({ω | virtualLabels init ω s = f} ∩ {ω | P f (virtualLabels init ω v)}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨virtualLabels init ω s, rfl, h⟩
    · rintro ⟨f, hf, h⟩
      rw [hf]
      exact h
  rw [hset]
  refine MeasurableSet.iUnion fun f => MeasurableSet.inter ?_ ?_
  · exact measurableSet_virtual_single init hs (fun g => g = f)
  · exact measurableSet_virtual_single init hv (fun g => P f g)

theorem measurableSet_forall_le {m' : MeasurableSpace (InputLog n)} (t : ℕ)
    (P : ℕ → Set (InputLog n)) (hP : ∀ v, v ≤ t → MeasurableSet[m'] (P v)) :
    MeasurableSet[m'] {ω | ∀ v, v ≤ t → ω ∈ P v} := by
  have hset : {ω | ∀ v, v ≤ t → ω ∈ P v} = ⋂ v ∈ Finset.range (t + 1), P v := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Nat.lt_succ_iff]
  rw [hset]
  exact Finset.measurableSet_biInter _ fun v hv =>
    hP v (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))

/-! ## Window predicates of the top level -/

/-- The threshold of the top level is reached at time `t`. -/
def ReachedTop (b : ℕ) (t : ℕ) (ω : InputLog n) : Prop := b ≤ topCount init ω t

/-- All Clocks (with the roles of `S`) are capped at time `t`. -/
def AllCapAt (S t : ℕ) (ω : InputLog n) : Prop :=
  topCount init ω t = clockCount (virtualLabels init ω S)

theorem reachedTop_measurableSet (b : ℕ) {v t : ℕ} (hv : v ≤ t) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | ReachedTop init b v ω} :=
  measurableSet_virtual_single init hv (fun f => b ≤ frontCount f (clockTop n))

theorem allCapAt_measurableSet {S v t : ℕ} (hS : S ≤ t) (hv : v ≤ t) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | AllCapAt init S v ω} :=
  measurableSet_virtual_pair init hS hv
    (fun fS fv => frontCount fv (clockTop n) = clockCount fS)

/-- No all-cap time `v ≥ S` with `v + k ≤ t`: the time `t` is before `cap + k`. -/
def BeforeCapPlus (S k t : ℕ) (ω : InputLog n) : Prop :=
  ∀ v, S ≤ v → v + k ≤ t → ¬ AllCapAt init S v ω

theorem beforeCapPlus_measurableSet {S k t : ℕ} (hS : S ≤ t) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | BeforeCapPlus init S k t ω} := by
  have hset : {ω | BeforeCapPlus init S k t ω} =
      {ω | ∀ v, v ≤ t → ω ∈ {ω | S ≤ v → v + k ≤ t → ¬ AllCapAt init S v ω}} := by
    ext ω
    simp only [BeforeCapPlus, Set.mem_setOf_eq]
    constructor
    · intro h v _ hSv hvk
      exact h v hSv hvk
    · intro h v hSv hvk
      exact h v (by omega) hSv hvk
  rw [hset]
  apply measurableSet_forall_le
  intro v hv
  by_cases hcond : S ≤ v ∧ v + k ≤ t
  · have hset' : {ω : InputLog n | S ≤ v → v + k ≤ t → ¬ AllCapAt init S v ω} =
        {ω | ¬ AllCapAt init S v ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, hcond.1, hcond.2, true_implies]
    rw [hset']
    exact (allCapAt_measurableSet init hS hv).compl
  · have hset' : {ω : InputLog n | S ≤ v → v + k ≤ t → ¬ AllCapAt init S v ω} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hcond
    rw [hset']
    exact MeasurableSet.univ

/-- The same, with the threshold `b` in place of all-cap. -/
def BeforeHighPlus (S b k t : ℕ) (ω : InputLog n) : Prop :=
  ∀ v, S ≤ v → v + k ≤ t → ¬ ReachedTop init b v ω

theorem beforeHighPlus_measurableSet {S : ℕ} (b : ℕ) {k t : ℕ} :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | BeforeHighPlus init S b k t ω} := by
  have hset : {ω | BeforeHighPlus init S b k t ω} =
      {ω | ∀ v, v ≤ t → ω ∈ {ω | S ≤ v → v + k ≤ t → ¬ ReachedTop init b v ω}} := by
    ext ω
    simp only [BeforeHighPlus, Set.mem_setOf_eq]
    constructor
    · intro h v _ hSv hvk
      exact h v hSv hvk
    · intro h v hSv hvk
      exact h v (by omega) hSv hvk
  rw [hset]
  apply measurableSet_forall_le
  intro v hv
  by_cases hcond : S ≤ v ∧ v + k ≤ t
  · have hset' : {ω : InputLog n | S ≤ v → v + k ≤ t → ¬ ReachedTop init b v ω} =
        {ω | ¬ ReachedTop init b v ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, hcond.1, hcond.2, true_implies]
    rw [hset']
    exact (reachedTop_measurableSet init b hv).compl
  · have hset' : {ω : InputLog n | S ≤ v → v + k ≤ t → ¬ ReachedTop init b v ω} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hcond
    rw [hset']
    exact MeasurableSet.univ

theorem capped_measurableSet (j : Fin init.card) {v t : ℕ} (hv : v ≤ t) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 t]
      {ω | Capped init (virtualLabels init ω v) j} :=
  measurableSet_virtual_single init hv (fun f => Capped init f j)

/-! ## Reached thresholds and the canonical witness -/

/-- After the seed, a threshold reached at `t` is reached at every later time. -/
theorem reachedTop_persist {S T : ℕ} (hentry : AsyncEntry init ω S T) (b : ℕ) {t t' : ℕ}
    (hSt : S ≤ t) (htt : t ≤ t') (h : ReachedTop init b t ω) : ReachedTop init b t' ω :=
  le_trans h (topCount_mono init ω hentry hSt htt)

theorem allCapAt_persist {S T : ℕ} (hentry : AsyncEntry init ω S T) {t t' : ℕ}
    (hSt : S ≤ t) (htt : t ≤ t') (h : AllCapAt init S t ω) : AllCapAt init S t' ω := by
  unfold AllCapAt at *
  have h1 := topCount_mono init ω hentry hSt htt
  have h2 := topCount_le_clockCount init ω t'
  rw [clockCount_virtual_eq_seed init ω hentry t' (by omega)] at h2
  omega

/-- The first time at or after `S` at which the threshold `b` is reached. -/
theorem firstAfter_reachedTop_iff {S T : ℕ} (hentry : AsyncEntry init ω S T) (b : ℕ) {u t : ℕ}
    (hfirst : firstAfter (fun v => ReachedTop init b v ω) S u) (hSt : S ≤ t) :
    ReachedTop init b t ω ↔ u ≤ t := by
  constructor
  · intro h
    by_contra hlt
    exact hfirst.2.2 t hSt (by omega) h
  · intro h
    exact reachedTop_persist init ω hentry b hfirst.1 h hfirst.2.1

theorem firstAfter_allCapAt_iff {S T : ℕ} (hentry : AsyncEntry init ω S T) {u t : ℕ}
    (hfirst : firstAfter (fun v => AllCapAt init S v ω) S u) (hSt : S ≤ t) :
    AllCapAt init S t ω ↔ u ≤ t := by
  constructor
  · intro h
    by_contra hlt
    exact hfirst.2.2 t hSt (by omega) h
  · intro h
    exact allCapAt_persist init ω hentry hfirst.1 h hfirst.2.1

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockCapSpread

end
