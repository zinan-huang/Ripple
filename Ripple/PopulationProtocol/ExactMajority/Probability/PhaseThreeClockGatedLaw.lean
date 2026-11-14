import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockVirtual

/-!
# The embedded clock count law on the virtual continuation (N12, step 2, active part)

PHASE3 Lemma P2, equation (25): at a labelled Clock pair the level-`ℓ` front count
`X_ℓ` (Clock labels with effective minute at least `ℓ`) rises by exactly one when the
pair copies across level `ℓ` or drips from level `ℓ - 1`, and is unchanged otherwise;
the number of ordered distinct label pairs that raise it is
`2 X_ℓ (C - X_ℓ) + Y (Y - 1)` with `Y = X_{ℓ-1} - X_ℓ`.

Contents.
* `effMinute`, `frontCount`, `exactCount`, `clockCount` on a labelling.
* `RaisingTick ℓ f i j`: the ordered pair `(i, j)` of Clock labels copies across `ℓ`
  or drips from `ℓ - 1` (a purely combinatorial predicate of the effective minutes).
* `goodPairs_raisingTick_card`: the exact ordered-pair count, with no regime
  assumption (it is the count of the predicate, not yet of the increment).
* `virtualRule_active_clock_pair`: the exact minute outcome of the virtual rule on a
  pair of Phase-3 Clocks (copy to the maximum, initiator drip below the cap, saturated
  counters at the cap).
* `frontCount_ruleUpdate_active_clock_pair`: for a pair of Phase-3 Clocks the front
  count rises by one exactly on a raising tick.
* `raisingTick_conditional_law`: the conditional probability, given the pair log, that
  the next drawn pair is a raising tick of the virtual labelling is the exact count over
  `n (n - 1)`.

Not in this file (open): the gated level-one law (25a), which needs the mixed
active/inactive Clock pair (initialize-then-drip) and the inactive/inactive pair; and
the invariance of Clock effective minutes under non-Clock interactions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockGatedLaw

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual

variable {L K : ℕ}

/-! ## Protocol facts on an active Clock pair -/

/-- The wrapper dispatches to the Phase-3 rule when the initiator is in Phase 3 after
the phase epidemic. -/
theorem transition_eq_phase3_of_dispatch (s t : AgentState L K)
    (h3 : (phaseEpidemicUpdate L K s t).1.phase.val = 3) :
    Transition L K s t =
      (finishPhase10Entry L K (phaseEpidemicUpdate L K s t).1
          (Phase3Transition L K (phaseEpidemicUpdate L K s t).1
            (phaseEpidemicUpdate L K s t).2).1,
        finishPhase10Entry L K (phaseEpidemicUpdate L K s t).2
          (Phase3Transition L K (phaseEpidemicUpdate L K s t).1
            (phaseEpidemicUpdate L K s t).2).2) := by
  unfold Transition
  generalize hd : phaseEpidemicUpdate L K s t = d at *
  obtain ⟨s', t'⟩ := d
  simp only at h3 ⊢
  have hph : s'.phase = ⟨3, by omega⟩ := Fin.ext h3
  rw [hph]

/-- Unequal minutes: both Clocks copy the maximum. -/
theorem phase3Transition_copy (s t : AgentState L K)
    (hsr : s.role = .clock) (htr : t.role = .clock) (hne : s.minute ≠ t.minute) :
    Phase3Transition L K s t =
      ({ s with minute := max s.minute t.minute },
        { t with minute := max s.minute t.minute }) := by
  simp only [Phase3Transition, hsr, htr, and_self, if_true, hne, ne_eq, not_false_eq_true]
  simp [hsr, htr]

/-- Equal minutes below the cap: the initiator drips. -/
theorem phase3Transition_drip (s t : AgentState L K)
    (hsr : s.role = .clock) (htr : t.role = .clock) (hmin : s.minute = t.minute)
    (hlt : s.minute.val < K * (L + 1)) :
    Phase3Transition L K s t =
      ({ s with minute := ⟨s.minute.val + 1, by omega⟩ }, t) := by
  have hlt' : t.minute.val < K * (L + 1) := by rw [← hmin]; exact hlt
  simp only [Phase3Transition, hsr, htr, and_self, if_true, hmin, ne_eq, not_true_eq_false,
    if_false, hlt', dif_pos]
  simp [hsr, htr]

theorem fin_val_max {k : ℕ} (a b : Fin k) : (max a b).val = max a.val b.val := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Fin.le_iff_val_le_val.mp h)]
  · rw [max_eq_left h, max_eq_left (Fin.le_iff_val_le_val.mp h)]

/-- The exact outcome of the virtual rule on a pair of Phase-3 Clocks. -/
theorem virtualRule_active_clock_pair (s t : AgentState L K)
    (hs3 : s.phase.val = 3) (ht3 : t.phase.val = 3)
    (hsr : s.role = .clock) (htr : t.role = .clock) :
    (virtualRule s t).1.role = .clock ∧ (virtualRule s t).2.role = .clock ∧
    (virtualRule s t).1.phase.val = 3 ∧ (virtualRule s t).2.phase.val = 3 ∧
    (virtualRule s t).1.minute.val =
      (if s.minute.val ≠ t.minute.val then max s.minute.val t.minute.val
        else if s.minute.val < K * (L + 1) then s.minute.val + 1 else s.minute.val) ∧
    (virtualRule s t).2.minute.val =
      (if s.minute.val ≠ t.minute.val then max s.minute.val t.minute.val
        else t.minute.val) := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs3 ht3
  by_cases hne : s.minute = t.minute
  · have hv' : s.minute.val = t.minute.val := congrArg Fin.val hne
    by_cases hlt : s.minute.val < K * (L + 1)
    · have hnc : ¬ CapCounterPair s t := by
        intro h
        obtain ⟨-, -, -, -, -, hcap⟩ := h
        rw [hepi] at hcap
        simp only at hcap
        omega
      have hv : virtualRule s t = Transition L K s t := by
        unfold virtualRule
        rw [if_neg hnc]
      rw [hv, transition_eq_phase3_of_dispatch s t (by rw [hepi]; exact hs3), hepi]
      simp only []
      rw [phase3Transition_drip s t hsr htr hne hlt]
      have hlt' : t.minute.val < K * (L + 1) := by omega
      simp [hsr, htr, hs3, ht3, hv', hlt, hlt']
    · have hc : CapCounterPair s t := by
        unfold CapCounterPair
        rw [hepi]
        refine ⟨hs3, ht3, hsr, htr, hne, ?_⟩
        have := s.minute.isLt
        change s.minute.val = K * (L + 1)
        omega
      have hv : virtualRule s t = (saturatedCounterStep s, saturatedCounterStep t) := by
        unfold virtualRule
        rw [if_pos hc, hepi]
      rw [hv]
      have hlt' : ¬ t.minute.val < K * (L + 1) := by omega
      simp [saturatedCounterStep, hsr, htr, hs3, ht3, hv', hlt, hlt']
  · have hv' : s.minute.val ≠ t.minute.val := fun h => hne (Fin.ext h)
    have hnc : ¬ CapCounterPair s t := by
      intro h
      obtain ⟨-, -, -, -, hmin, -⟩ := h
      rw [hepi] at hmin
      exact hne hmin
    have hv : virtualRule s t = Transition L K s t := by
      unfold virtualRule
      rw [if_neg hnc]
    rw [hv, transition_eq_phase3_of_dispatch s t (by rw [hepi]; exact hs3), hepi]
    simp only []
    rw [phase3Transition_copy s t hsr htr hne]
    simp [hsr, htr, hs3, ht3, hv', fin_val_max]

/-! ## Front counts on a labelling -/

variable {m : ℕ}

/-- Effective minute: zero before Phase 3, the physical minute afterwards. -/
def effMinute (a : AgentState L K) : ℕ :=
  if 3 ≤ a.phase.val then a.minute.val else 0

def clockSet (f : Fin m → AgentState L K) : Finset (Fin m) :=
  Finset.univ.filter fun i => (f i).role = .clock

def aboveSet (f : Fin m → AgentState L K) (ℓ : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => (f i).role = .clock ∧ ℓ ≤ effMinute (f i)

def belowSet (f : Fin m → AgentState L K) (ℓ : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => (f i).role = .clock ∧ ¬ ℓ ≤ effMinute (f i)

def exactSet (f : Fin m → AgentState L K) (e : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => (f i).role = .clock ∧ effMinute (f i) = e

def clockCount (f : Fin m → AgentState L K) : ℕ := (clockSet f).card

/-- `X_ℓ`: Clock labels with effective minute at least `ℓ`. -/
def frontCount (f : Fin m → AgentState L K) (ℓ : ℕ) : ℕ := (aboveSet f ℓ).card

/-- Clock labels with effective minute exactly `e`. -/
def exactCount (f : Fin m → AgentState L K) (e : ℕ) : ℕ := (exactSet f e).card

theorem belowSet_card (f : Fin m → AgentState L K) (ℓ : ℕ) :
    (belowSet f ℓ).card = clockCount f - frontCount f ℓ := by
  have habove : aboveSet f ℓ = (clockSet f).filter fun i => ℓ ≤ effMinute (f i) := by
    ext i
    simp [aboveSet, clockSet, Finset.mem_filter]
  have hbelow : belowSet f ℓ = (clockSet f).filter fun i => ¬ ℓ ≤ effMinute (f i) := by
    ext i
    simp [belowSet, clockSet, Finset.mem_filter]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := clockSet f) (fun i => ℓ ≤ effMinute (f i))
  unfold clockCount frontCount
  rw [habove, hbelow]
  omega

/-- `Y = X_{ℓ-1} - X_ℓ` for `1 ≤ ℓ`. -/
theorem frontCount_pred (f : Fin m → AgentState L K) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    frontCount f (ℓ - 1) = frontCount f ℓ + exactCount f (ℓ - 1) := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := aboveSet f (ℓ - 1)) (fun i => ℓ ≤ effMinute (f i))
  have h1 : (aboveSet f (ℓ - 1)).filter (fun i => ℓ ≤ effMinute (f i)) = aboveSet f ℓ := by
    ext i
    simp only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, -⟩, hl⟩; exact ⟨hr, hl⟩
    · rintro ⟨hr, hl⟩; exact ⟨⟨hr, by omega⟩, hl⟩
  have h2 : (aboveSet f (ℓ - 1)).filter (fun i => ¬ ℓ ≤ effMinute (f i)) =
      exactSet f (ℓ - 1) := by
    ext i
    simp only [aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, hl⟩, hn⟩; exact ⟨hr, by omega⟩
    · rintro ⟨hr, he⟩; exact ⟨⟨hr, by omega⟩, by omega⟩
  unfold frontCount exactCount
  rw [h1, h2] at h
  omega

/-! ## Raising ticks and their exact count -/

/-- The ordered Clock pair `(i, j)` copies across level `ℓ` (exactly one endpoint is at
or above `ℓ`) or drips from level `ℓ - 1` (both endpoints exactly at `ℓ - 1`). -/
def RaisingTick (ℓ : ℕ) (f : Fin m → AgentState L K) (i j : Fin m) : Prop :=
  (i ∈ belowSet f ℓ ∧ j ∈ aboveSet f ℓ) ∨
  (i ∈ aboveSet f ℓ ∧ j ∈ belowSet f ℓ) ∨
  (i ∈ exactSet f (ℓ - 1) ∧ j ∈ exactSet f (ℓ - 1))

instance (ℓ : ℕ) (f : Fin m → AgentState L K) (i j : Fin m) :
    Decidable (RaisingTick ℓ f i j) := by
  unfold RaisingTick
  infer_instance

theorem goodPairs_raisingTick (f : Fin m → AgentState L K) (ℓ : ℕ) :
    goodPairs (RaisingTick ℓ) f =
      (belowSet f ℓ ×ˢ aboveSet f ℓ) ∪ (aboveSet f ℓ ×ˢ belowSet f ℓ) ∪
        (exactSet f (ℓ - 1)).offDiag := by
  ext ⟨i, j⟩
  simp only [goodPairs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_product, Finset.mem_offDiag, RaisingTick]
  constructor
  · rintro ⟨hij, h | h | h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨h.1, h.2, hij⟩
  · rintro ((⟨hi, hj⟩ | ⟨hi, hj⟩) | ⟨hi, hj, hij⟩)
    · refine ⟨?_, Or.inl ⟨hi, hj⟩⟩
      rintro rfl
      simp only [belowSet, aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact hi.2 hj.2
    · refine ⟨?_, Or.inr (Or.inl ⟨hi, hj⟩)⟩
      rintro rfl
      simp only [belowSet, aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact hj.2 hi.2
    · exact ⟨hij, Or.inr (Or.inr ⟨hi, hj⟩)⟩

/-- PHASE3 (25): the exact number of ordered distinct label pairs that raise `X_ℓ`,
`2 X_ℓ (C - X_ℓ) + Y (Y - 1)` with `Y` the number of Clock labels exactly at `ℓ - 1`. -/
theorem goodPairs_raisingTick_card (f : Fin m → AgentState L K) (ℓ : ℕ) :
    (goodPairs (RaisingTick ℓ) f).card =
      2 * frontCount f ℓ * (clockCount f - frontCount f ℓ) +
        exactCount f (ℓ - 1) * (exactCount f (ℓ - 1) - 1) := by
  rw [goodPairs_raisingTick]
  have hd1 : Disjoint (belowSet f ℓ ×ˢ aboveSet f ℓ) (aboveSet f ℓ ×ˢ belowSet f ℓ) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [Finset.mem_product, belowSet, aboveSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at h1 h2
    exact h1.1.2 h2.1.2
  have hd2 : Disjoint ((belowSet f ℓ ×ˢ aboveSet f ℓ) ∪ (aboveSet f ℓ ×ˢ belowSet f ℓ))
      (exactSet f (ℓ - 1)).offDiag := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ h1 h2
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_offDiag, belowSet, aboveSet,
      exactSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with h1 | h1
    · have := h2.2.1.2
      have := h1.2.2
      omega
    · have := h2.1.2
      have := h1.1.2
      omega
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Finset.card_product, Finset.card_product, Finset.offDiag_card, belowSet_card]
  unfold frontCount exactCount
  rw [Nat.mul_sub_one]
  ring

/-! ## The one-pair increment on an active Clock pair -/

/-- Indicator of membership in the level-`ℓ` front. -/
def frontInd (ℓ : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = .clock ∧ ℓ ≤ effMinute a then 1 else 0

theorem frontCount_eq_sum (f : Fin m → AgentState L K) (ℓ : ℕ) :
    frontCount f ℓ = ∑ k, frontInd ℓ (f k) := by
  unfold frontCount aboveSet frontInd
  rw [Finset.card_filter]

theorem sum_update_pair {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (g : α → ℕ) (f : ι → α) (i j : ι) (hij : i ≠ j) (a b : α) :
    (∑ k, g (Function.update (Function.update f i a) j b k)) + g (f i) + g (f j) =
      (∑ k, g (f k)) + g a + g b := by
  have hsplit : ∀ h : ι → ℕ, ∑ k, h k =
      h i + h j + ∑ k ∈ (Finset.univ.erase i).erase j, h k := by
    intro h
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      add_assoc]
  rw [hsplit (fun k => g (Function.update (Function.update f i a) j b k)),
    hsplit (fun k => g (f k))]
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j,
      g (Function.update (Function.update f i a) j b k) =
      ∑ k ∈ (Finset.univ.erase i).erase j, g (f k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    rw [Function.update_of_ne hk.1, Function.update_of_ne hk.2.1]
  rw [hrest]
  simp only [Function.update_self, Function.update_of_ne hij, Function.update_of_ne hij.symm]
  omega

/-- On a pair of Phase-3 Clocks the level-`ℓ` front count (for `1 ≤ ℓ ≤ Q`, `Q` the
cap) rises by one exactly on a raising tick, and is otherwise unchanged. The upper
bound is needed: at `ℓ = Q + 1` an equal-cap pair is a formal drip but the counters are
saturated. -/
theorem frontCount_ruleUpdate_active_clock_pair (f : Fin m → AgentState L K)
    (i j : Fin m) (hij : i ≠ j)
    (hi3 : (f i).phase.val = 3) (hj3 : (f j).phase.val = 3)
    (hir : (f i).role = .clock) (hjr : (f j).role = .clock)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ K * (L + 1)) :
    frontCount (ruleUpdate virtualRule f i j) ℓ =
      frontCount f ℓ + if RaisingTick ℓ f i j then 1 else 0 := by
  obtain ⟨har, hbr, ha3, hb3, ham, hbm⟩ :=
    virtualRule_active_clock_pair (f i) (f j) hi3 hj3 hir hjr
  have hsum := sum_update_pair (frontInd ℓ) f i j hij
    (virtualRule (f i) (f j)).1 (virtualRule (f i) (f j)).2
  rw [frontCount_eq_sum, frontCount_eq_sum]
  unfold ruleUpdate
  suffices hkey : frontInd ℓ (virtualRule (f i) (f j)).1 + frontInd ℓ (virtualRule (f i) (f j)).2 =
      frontInd ℓ (f i) + frontInd ℓ (f j) + if RaisingTick ℓ f i j then 1 else 0 by
    omega
  have hRT : RaisingTick ℓ f i j ↔
      ((f i).minute.val < ℓ ∧ ℓ ≤ (f j).minute.val) ∨
      (ℓ ≤ (f i).minute.val ∧ (f j).minute.val < ℓ) ∨
      ((f i).minute.val = ℓ - 1 ∧ (f j).minute.val = ℓ - 1) := by
    simp only [RaisingTick, belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ,
      true_and, hir, hjr, effMinute, hi3, hj3, le_refl, if_true, not_le]
  have e1 : frontInd ℓ (f i) = if ℓ ≤ (f i).minute.val then 1 else 0 := by
    simp [frontInd, effMinute, hir, hi3]
  have e2 : frontInd ℓ (f j) = if ℓ ≤ (f j).minute.val then 1 else 0 := by
    simp [frontInd, effMinute, hjr, hj3]
  have e3 : frontInd ℓ (virtualRule (f i) (f j)).1 =
      if ℓ ≤ (virtualRule (f i) (f j)).1.minute.val then 1 else 0 := by
    simp [frontInd, effMinute, har, ha3]
  have e4 : frontInd ℓ (virtualRule (f i) (f j)).2 =
      if ℓ ≤ (virtualRule (f i) (f j)).2.minute.val then 1 else 0 := by
    simp [frontInd, effMinute, hbr, hb3]
  have hRT' : (if RaisingTick ℓ f i j then (1 : ℕ) else 0) =
      if ((f i).minute.val < ℓ ∧ ℓ ≤ (f j).minute.val) ∨
        (ℓ ≤ (f i).minute.val ∧ (f j).minute.val < ℓ) ∨
        ((f i).minute.val = ℓ - 1 ∧ (f j).minute.val = ℓ - 1) then 1 else 0 :=
    if_congr hRT rfl rfl
  rw [e1, e2, e3, e4, hRT', ham, hbm]
  split_ifs <;> omega

/-! ## The conditional law of a raising tick given the pair log -/

open Classical in
/-- The conditional probability, given the pair log through `t`, that the next drawn
pair is a raising tick of level `ℓ` for the virtual labelling
(`auxLabels init virtualRule ω t = virtualLabels init ω t`) is the exact ordered-pair
count over `n (n - 1)`. -/
theorem raisingTick_conditional_law (init : Cfg L K) (hc : 2 ≤ init.card) (ℓ t : ℕ) :
    (law init)[fun ω =>
      if ∃ i j, drawLabels init ω (t + 1) = some (i, j) ∧
          RaisingTick ℓ (auxLabels init virtualRule ω t) i j
      then (1 : ℝ) else 0 | pairLogFiltration L K t]
      =ᵐ[law init]
    (fun ω => ((2 * frontCount (auxLabels init virtualRule ω t) ℓ *
        (clockCount (auxLabels init virtualRule ω t) -
          frontCount (auxLabels init virtualRule ω t) ℓ) +
        exactCount (auxLabels init virtualRule ω t) (ℓ - 1) *
          (exactCount (auxLabels init virtualRule ω t) (ℓ - 1) - 1) : ℕ) : ℝ) /
      ((init.card : ℝ) * ((init.card : ℝ) - 1))) := by
  have h := aux_pair_conditional_probability init hc virtualRule (RaisingTick ℓ) t
  convert h using 3 with ω
  · congr!
  · rw [goodPairs_raisingTick_card]

/-- One virtual step on a drawn pair of Phase-3 Clocks changes `X_ℓ` by the raising
indicator. -/
theorem frontCount_virtualLabels_succ_of_clock_pair (init : Cfg L K) (ω : Ω L K) (t : ℕ)
    (i j : Fin init.card) (hd : drawLabels init ω (t + 1) = some (i, j))
    (hi3 : (virtualLabels init ω t i).phase.val = 3)
    (hj3 : (virtualLabels init ω t j).phase.val = 3)
    (hir : (virtualLabels init ω t i).role = .clock)
    (hjr : (virtualLabels init ω t j).role = .clock)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hcap : ℓ ≤ K * (L + 1)) :
    frontCount (virtualLabels init ω (t + 1)) ℓ =
      frontCount (virtualLabels init ω t) ℓ +
        if RaisingTick ℓ (virtualLabels init ω t) i j then 1 else 0 := by
  have hij := (labelsAt_selected_transition init ω t i j hd).1
  rw [virtualLabels_succ, hd]
  exact frontCount_ruleUpdate_active_clock_pair _ i j hij hi3 hj3 hir hjr ℓ hℓ hcap

theorem frontCount_virtualLabels_succ_of_none (init : Cfg L K) (ω : Ω L K) (t : ℕ)
    (hd : drawLabels init ω (t + 1) = none) (ℓ : ℕ) :
    frontCount (virtualLabels init ω (t + 1)) ℓ = frontCount (virtualLabels init ω t) ℓ := by
  rw [virtualLabels_succ, hd]
  rfl

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockGatedLaw

end
