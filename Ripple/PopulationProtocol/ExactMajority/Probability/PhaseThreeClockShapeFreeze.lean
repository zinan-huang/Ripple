-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockShapeFreeze.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalRiseStoppedLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkInitialization
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockNormalBarrierTails
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockObservedPassage

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeFreeze

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbeddingBridge
  PhaseThreeClockEarlyMarks PhaseThreeClockEarlyMarkEmbedding PhaseThreeClockNormalRise
  PhaseThreeClockNormalRiseStoppedLaw PhaseThreeClockActivationLaw
  PhaseThreeClockActivationSeed PhaseThreeClockSeedTails PhaseThreeClockPrefixTails
  PhaseThreeClockStoppedPassage PhaseThreeClockNormalBarrierTails
  PhaseThreeClockObservedPassage

variable {n : ℕ}

def shapeSafeAt (init : InputCfg n) (C : Finset (Fin init.card))
    (s v : ℕ) (ω : InputLog n) : Prop :=
  ω ∈ seedMaskPrefix init s C ∧
    ∀ i, (virtualLabels init ω v i).phase.val ≤ 3

theorem shapeSafeAt_anti (init : InputCfg n) (C : Finset (Fin init.card))
    (s v w : ℕ) (hvw : v ≤ w) (ω : InputLog n)
    (hw : shapeSafeAt init C s w ω) : shapeSafeAt init C s v ω :=
  ⟨hw.1, fun i => (virtualLabels_phase_mono init ω i hvw).trans (hw.2 i)⟩

theorem shapeSafeAt_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (s v : ℕ) (hsv : s ≤ v) :
    MeasurableSet[pairLogFiltration _ _ v] {ω | shapeSafeAt init C s v ω} := by
  have hs := ((pairLogFiltration _ _).mono hsv) _
    (seedMaskPrefix_measurable init s C)
  have hp : MeasurableSet[pairLogFiltration _ _ v]
      {ω | ∀ i, (virtualLabels init ω v i).phase.val ≤ 3} :=
    (show MeasurableSet {f : Fin init.card →
      AgentState (PhaseThreeModel.Numeric.hourIndex n) 256 |
        ∀ i, (f i).phase.val ≤ 3} from
      (Set.to_countable _).measurableSet).preimage (measurable_virtualLabels init v)
  exact hs.inter hp

theorem shapeSafeAt_guard (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s v : ℕ) (hsv : s ≤ v) (hℓ : 1 ≤ ℓ) (ω : InputLog n)
    (hv : shapeSafeAt init C s v ω) :
    CurrentMarkedGuard init C ℓ cutoff s v ω :=
  currentMarkedGuard_of_seedPrefix init ω C ℓ cutoff s v
    hv.1.1 hsv hℓ hv.1.2.symm hv.2

def rawShapeCounts (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s v : ℕ) (ω : InputLog n) : ℕ × ℕ :=
  (frontCount (virtualLabels init ω v) ℓ,
    normalCount (virtualLabels init ω v) (markedAt init C ℓ cutoff s ω v) ℓ)

theorem rawShapeCounts_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s v : ℕ) :
    Measurable[pairLogFiltration _ _ v] (rawShapeCounts init C ℓ cutoff s v) := by
  let H : ((i : Finset.Iic v) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256) → ℕ × ℕ := fun p =>
    (frontCount (auxPrefix init virtualRule v p) ℓ,
      normalCount (auxPrefix init virtualRule v p)
        (markedPrefix init C ℓ cutoff s v p) ℓ)
  change Measurable[pairLogFiltration _ _ v] (fun ω => H (frestrictLe v ω))
  exact (measurable_of_countable H).comp (measurable_pairLog_prefix _ _ v)

open Classical in
def frozenShapeCounts (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) : ℕ → InputLog n → ℕ × ℕ
  | 0, ω =>
      if shapeSafeAt init C s u ω then rawShapeCounts init C ℓ cutoff s u ω else (0, 0)
  | t + 1, ω =>
      if shapeSafeAt init C s (u + (t + 1)) ω then
        rawShapeCounts init C ℓ cutoff s (u + (t + 1)) ω
      else frozenShapeCounts init C ℓ cutoff s u t ω

def frozenFront (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : InputLog n) : ℝ :=
  ((frozenShapeCounts init C ℓ cutoff s u t ω).1 : ℝ)

def frozenNormal (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : InputLog n) : ℝ :=
  ((frozenShapeCounts init C ℓ cutoff s u t ω).2 : ℝ)

theorem frozenShapeCounts_eq_raw (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s (u + t) ω) :
    frozenShapeCounts init C ℓ cutoff s u t ω =
      rawShapeCounts init C ℓ cutoff s (u + t) ω := by
  classical
  cases t with
  | zero =>
      simpa only [Nat.add_zero, frozenShapeCounts, if_pos
        (show shapeSafeAt init C s u ω by simpa only [Nat.add_zero] using hsafe)]
  | succ t =>
      exact if_pos hsafe

theorem frozenShapeCounts_skip (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : InputLog n)
    (hbad : ¬ shapeSafeAt init C s (u + (t + 1)) ω) :
    frozenShapeCounts init C ℓ cutoff s u (t + 1) ω =
      frozenShapeCounts init C ℓ cutoff s u t ω := by
  classical
  exact if_neg hbad

theorem frozenShapeCounts_frozen (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t v : ℕ) (htv : t ≤ v) (ω : InputLog n)
    (hbad : ¬ shapeSafeAt init C s (u + t) ω) :
    frozenShapeCounts init C ℓ cutoff s u v ω =
      frozenShapeCounts init C ℓ cutoff s u t ω := by
  induction v, htv using Nat.le_induction with
  | base => rfl
  | succ v htv ih =>
      rw [frozenShapeCounts_skip init C ℓ cutoff s u v ω
        (fun h => hbad (shapeSafeAt_anti init C s _ _ (by omega) ω h))]
      exact ih

theorem frozenShapeCounts_measurable (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (t : ℕ) :
    Measurable[shiftedFiltration (pairLogFiltration _ _) u t]
      (frozenShapeCounts init C ℓ cutoff s u t) := by
  classical
  induction t with
  | zero =>
      simpa only [shiftedFiltration_apply, Nat.add_zero, frozenShapeCounts] using
        Measurable.ite (shapeSafeAt_measurable init C s u hsu)
          (rawShapeCounts_measurable init C ℓ cutoff s u) measurable_const
  | succ t ih =>
      have hi := ih.mono
        ((shiftedFiltration (pairLogFiltration _ _) u).mono (Nat.le_succ t))
        le_rfl
      exact Measurable.ite
        (shapeSafeAt_measurable init C s (u + (t + 1)) (by omega))
        (rawShapeCounts_measurable init C ℓ cutoff s (u + (t + 1))) hi

theorem frozenFront_adapted (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) :
    StronglyAdapted (shiftedFiltration (pairLogFiltration _ _) u)
      (frozenFront init C ℓ cutoff s u) := by
  intro t
  have h := (frozenShapeCounts_measurable init C ℓ cutoff s u hsu t).fst
  exact ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp h).stronglyMeasurable

theorem frozenNormal_adapted (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) :
    StronglyAdapted (shiftedFiltration (pairLogFiltration _ _) u)
      (frozenNormal init C ℓ cutoff s u) := by
  intro t
  have h := (frozenShapeCounts_measurable init C ℓ cutoff s u hsu t).snd
  exact ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp h).stronglyMeasurable

theorem frozenFront_nonneg (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (ω : InputLog n) :
    0 ≤ frozenFront init C ℓ cutoff s u t ω := Nat.cast_nonneg _

theorem frozenNormal_bound (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ) (t : ℕ) (ω : InputLog n) :
    frozenNormal init C ℓ cutoff s u t ω ≤ (C.card : ℝ) := by
  classical
  have hraw (v : ℕ) (hsv : s ≤ v) (h : shapeSafeAt init C s v ω) :
      (rawShapeCounts init C ℓ cutoff s v ω).2 ≤ C.card := by
    have hg := shapeSafeAt_guard init C ℓ cutoff s v hsv hℓ ω h
    have hc : clockCount (virtualLabels init ω v) = C.card := by
      change (clockSet (virtualLabels init ω v)).card = C.card
      rw [← hg.2.1]
    exact (normalCount_le_clockCount _ _ ℓ).trans_eq hc
  have hb : (frozenShapeCounts init C ℓ cutoff s u t ω).2 ≤ C.card := by
    induction t with
    | zero =>
        by_cases h : shapeSafeAt init C s u ω
        · simpa only [frozenShapeCounts, if_pos h] using hraw u hsu h
        · simp only [frozenShapeCounts, if_neg h, Nat.zero_le]
    | succ t ih =>
        by_cases h : shapeSafeAt init C s (u + (t + 1)) ω
        · simpa only [frozenShapeCounts, if_pos h] using hraw _ (by omega) h
        · simpa only [frozenShapeCounts, if_neg h] using ih
  unfold frozenNormal
  exact_mod_cast hb

theorem gatedTick_clock_roles {L K m : ℕ}
    (f : Fin m → AgentState L K) (ℓ : ℕ) (i j : Fin m)
    (hg : GatedTick ℓ f i j) :
    (f i).role = .clock ∧ (f j).role = .clock := by
  rcases hg.1 with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ <;>
    simp only [belowSet, aboveSet, exactSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hi hj <;> exact ⟨hi.1, hj.1⟩

theorem shapeSafeAt_succ_of_gated (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (hst : s ≤ t) (hℓ : 1 ≤ ℓ) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s t ω)
    (i j : Fin init.card) (hd : drawLabels init ω (t + 1) = some (i, j))
    (hg : GatedTick ℓ (virtualLabels init ω t) i j) :
    shapeSafeAt init C s (t + 1) ω := by
  have henv := (shapeSafeAt_guard init C ℓ cutoff s t hst hℓ ω hsafe).1
  have hroles := gatedTick_clock_roles _ ℓ i j hg
  have hact : (virtualLabels init ω t i).phase.val = 3 ∨
      (virtualLabels init ω t j).phase.val = 3 := by
    rcases hg.2 with hi | hj
    · left
      have := (henv.phase_range i).2
      omega
    · right
      have := (henv.phase_range j).2
      omega
  have hout := virtualRule_clock_pair_some_active
    (virtualLabels init ω t i) (virtualLabels init ω t j) (by decide)
    (henv.clock_regime i hroles.1) (henv.clock_regime j hroles.2) hact
  have hij := (labelsAt_selected_transition init ω t i j hd).1
  refine ⟨hsafe.1, ?_⟩
  intro k
  rw [virtualLabels_succ, hd]
  by_cases hkj : k = j
  · subst k
    simpa only [auxStep, ruleUpdate, Function.update_self, hout.2.2.2.1]
      using (show (3 : ℕ) ≤ 3 from le_rfl)
  · by_cases hki : k = i
    · subst k
      simpa only [auxStep, ruleUpdate, Function.update_of_ne hij,
        Function.update_self, hout.2.2.1]
        using (show (3 : ℕ) ≤ 3 from le_rfl)
    · simpa only [auxStep, ruleUpdate, Function.update_of_ne hkj,
        Function.update_of_ne hki] using hsafe.2 k

theorem front_step_safe (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s t : ℕ) (hst : s ≤ t) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hnext : shapeSafeAt init C s (t + 1) ω) :
    (frontCount (virtualLabels init ω (t + 1)) ℓ : ℝ) =
      (frontCount (virtualLabels init ω t) ℓ : ℝ) + gatedIndicator init ℓ t ω := by
  classical
  have hcur := shapeSafeAt_anti init C s t (t + 1) (Nat.le_succ t) ω hnext
  have henv := (shapeSafeAt_guard init C ℓ cutoff s t hst hℓ ω hcur).1
  cases hd : drawLabels init ω (t + 1) with
  | none =>
      have h := frontCount_virtualLabels_succ_of_none init ω t hd ℓ
      simp only [gatedIndicator, hd, reduceCtorEq, false_and, exists_false,
        if_false, add_zero]
      exact_mod_cast h
  | some ij =>
      rcases ij with ⟨i, j⟩
      have h := frontCount_virtualLabels_succ_of_phase_range init ω t i j hd
        henv.phase_range (fun k hk => henv.carrier k (Or.inr (Or.inr hk)))
        hnext.2 ℓ hℓ hcap
      have hevent :
          (∃ a b, drawLabels init ω (t + 1) = some (a, b) ∧
            GatedTick ℓ (auxLabels init virtualRule ω t) a b) ↔
          GatedTick ℓ (virtualLabels init ω t) i j := by
        simp only [hd, Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro ⟨a, b, ⟨rfl, rfl⟩, hg⟩
          exact hg
        · intro hg
          exact ⟨i, j, ⟨rfl, rfl⟩, hg⟩
      have hreal :
          (frontCount (virtualLabels init ω (t + 1)) ℓ : ℝ) =
            (frontCount (virtualLabels init ω t) ℓ : ℝ) +
              if GatedTick ℓ (virtualLabels init ω t) i j then (1 : ℝ) else 0 := by
        by_cases hg : GatedTick ℓ (virtualLabels init ω t) i j
        · rw [if_pos hg] at h ⊢
          exact_mod_cast h
        · rw [if_neg hg] at h ⊢
          exact_mod_cast h
      simpa only [gatedIndicator, hevent] using hreal

theorem frozenFront_delta_of_safe (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u t : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) (hnext : shapeSafeAt init C s (u + (t + 1)) ω) :
    frozenFront init C ℓ cutoff s u (t + 1) ω -
      frozenFront init C ℓ cutoff s u t ω = gatedIndicator init ℓ (u + t) ω := by
  have hcur := shapeSafeAt_anti init C s (u + t) (u + (t + 1)) (by omega) ω hnext
  have hf := front_step_safe init C ℓ cutoff s (u + t) (by omega) hℓ hcap ω
    (by simpa only [Nat.add_assoc] using hnext)
  simp only [frozenFront, frozenShapeCounts_eq_raw init C ℓ cutoff s u (t + 1) ω hnext,
    frozenShapeCounts_eq_raw init C ℓ cutoff s u t ω hcur, rawShapeCounts, Nat.add_assoc]
  simp only [Nat.add_assoc] at hf
  linarith only [hf]

theorem frozenFront_delta_cases (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (t : ℕ) (ω : InputLog n) :
    frozenFront init C ℓ cutoff s u (t + 1) ω -
      frozenFront init C ℓ cutoff s u t ω = 0 ∨
    frozenFront init C ℓ cutoff s u (t + 1) ω -
      frozenFront init C ℓ cutoff s u t ω = 1 := by
  by_cases hnext : shapeSafeAt init C s (u + (t + 1)) ω
  · rw [frozenFront_delta_of_safe init C ℓ cutoff s u t hsu hℓ hcap ω hnext]
    exact gatedIndicator_zero_one init ℓ (u + t) ω
  · left
    simp only [frozenFront, frozenShapeCounts_skip init C ℓ cutoff s u t ω hnext,
      sub_self]

theorem frozenNormal_delta_cases (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ + 1 ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (t : ℕ) (ω : InputLog n) :
    frozenNormal init C ℓ cutoff s u (t + 1) ω -
      frozenNormal init C ℓ cutoff s u t ω ≤ 0 ∨
    frozenNormal init C ℓ cutoff s u (t + 1) ω -
      frozenNormal init C ℓ cutoff s u t ω = 1 := by
  by_cases hnext : shapeSafeAt init C s (u + (t + 1)) ω
  · have hcur := shapeSafeAt_anti init C s (u + t) (u + (t + 1)) (by omega) ω hnext
    have hg := shapeSafeAt_guard init C ℓ cutoff s (u + t) (by omega) hℓ ω hcur
    simpa only [frozenNormal,
      frozenShapeCounts_eq_raw init C ℓ cutoff s u (t + 1) ω hnext,
      frozenShapeCounts_eq_raw init C ℓ cutoff s u t ω hcur,
      rawShapeCounts, Nat.add_assoc] using
      normalCount_delta_cases init C ℓ cutoff s (u + t) ω (by omega) hℓ hcap
        hg.1 hg.2.1 hg.2.2 (by simpa only [Nat.add_assoc] using hnext.2)
  · left
    simp only [frozenNormal, frozenShapeCounts_skip init C ℓ cutoff s u t ω hnext,
      sub_self, le_refl]

theorem gatedIndicator_le_frozenFront_increment
    (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (t : ℕ) (ω : InputLog n) :
    ({ω | shapeSafeAt init C s (u + t) ω}.indicator
      (gatedIndicator init ℓ (u + t))) ω ≤
        incrementIndicator (frozenFront init C ℓ cutoff s u) t ω := by
  classical
  by_cases hcur : shapeSafeAt init C s (u + t) ω
  · have hm : ω ∈ {ω | shapeSafeAt init C s (u + t) ω} := hcur
    rw [Set.indicator_of_mem hm]
    rcases gatedIndicator_zero_one init ℓ (u + t) ω with hz | ho
    · rw [hz]
      exact incrementIndicator_nonneg _ _ _
    · have hex : ∃ i j, drawLabels init ω (u + t + 1) = some (i, j) ∧
          GatedTick ℓ (virtualLabels init ω (u + t)) i j := by
        by_contra hn
        have hzero : gatedIndicator init ℓ (u + t) ω = 0 := by
          simp only [gatedIndicator, show ¬ ∃ i j,
            drawLabels init ω (u + t + 1) = some (i, j) ∧
              GatedTick ℓ (auxLabels init virtualRule ω (u + t)) i j from hn,
            if_false]
        rw [hzero] at ho
        norm_num at ho
      obtain ⟨i, j, hd, hg⟩ := hex
      have hs := shapeSafeAt_succ_of_gated init C ℓ cutoff s (u + t) (by omega)
        hℓ ω hcur i j hd hg
      have hdelta := frozenFront_delta_of_safe init C ℓ cutoff s u t hsu hℓ hcap ω
        (by simpa only [Nat.add_assoc] using hs)
      rw [ho] at hdelta
      simp only [ho, incrementIndicator, hdelta, if_true, le_refl]
  · have hm : ω ∉ {ω | shapeSafeAt init C s (u + t) ω} := hcur
    rw [Set.indicator_of_notMem hm]
    exact incrementIndicator_nonneg _ _ _

theorem frozenNormal_increment_le_nextSafe
    (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (t : ℕ) (ω : InputLog n) :
    incrementIndicator (frozenNormal init C ℓ cutoff s u) t ω ≤
      nextSafeNormalIndicator init C ℓ cutoff s (u + t) ω := by
  classical
  by_cases hdelta : frozenNormal init C ℓ cutoff s u (t + 1) ω -
      frozenNormal init C ℓ cutoff s u t ω = 1
  · have hnext : shapeSafeAt init C s (u + (t + 1)) ω := by
      by_contra hn
      have he := frozenShapeCounts_skip init C ℓ cutoff s u t ω hn
      simp only [frozenNormal, he, sub_self] at hdelta
      norm_num at hdelta
    have hcur := shapeSafeAt_anti init C s (u + t) (u + (t + 1)) (by omega) ω hnext
    have hg := shapeSafeAt_guard init C ℓ cutoff s (u + t) (by omega) hℓ ω hcur
    have hd :
        (normalCount (virtualLabels init ω (u + t + 1))
          (markedAt init C ℓ cutoff s ω (u + t + 1)) ℓ : ℝ) -
        (normalCount (virtualLabels init ω (u + t))
          (markedAt init C ℓ cutoff s ω (u + t)) ℓ : ℝ) = 1 := by
      simpa only [frozenNormal,
        frozenShapeCounts_eq_raw init C ℓ cutoff s u (t + 1) ω hnext,
        frozenShapeCounts_eq_raw init C ℓ cutoff s u t ω hcur,
        rawShapeCounts, Nat.add_assoc] using hdelta
    have heR :
        (normalCount (virtualLabels init ω (u + t + 1))
          (markedAt init C ℓ cutoff s ω (u + t + 1)) ℓ : ℝ) =
        (normalCount (virtualLabels init ω (u + t))
          (markedAt init C ℓ cutoff s ω (u + t)) ℓ : ℝ) + 1 := by linarith
    have he :
        normalCount (virtualLabels init ω (u + t + 1))
          (markedAt init C ℓ cutoff s ω (u + t + 1)) ℓ =
        normalCount (virtualLabels init ω (u + t))
          (markedAt init C ℓ cutoff s ω (u + t)) ℓ + 1 := by exact_mod_cast heR
    have hp : ∀ i, (virtualLabels init ω (u + t + 1) i).phase.val ≤ 3 := by
      simpa only [Nat.add_assoc] using hnext.2
    have hcond : CurrentMarkedGuard init C ℓ cutoff s (u + t) ω ∧
        (∀ k, (virtualLabels init ω (u + t + 1) k).phase.val ≤ 3) ∧
        normalCount (virtualLabels init ω (u + t + 1))
          (markedAt init C ℓ cutoff s ω (u + t + 1)) ℓ =
        normalCount (virtualLabels init ω (u + t))
          (markedAt init C ℓ cutoff s ω (u + t)) ℓ + 1 := ⟨hg, hp, he⟩
    simp only [incrementIndicator, if_pos hdelta, nextSafeNormalIndicator,
      if_pos hcond, le_refl]
  · rw [show incrementIndicator (frozenNormal init C ℓ cutoff s u) t ω = 0 by
      simp only [incrementIndicator, if_neg hdelta]]
    rcases nextSafeNormalIndicator_zero_one init C ℓ cutoff s (u + t) ω with h | h <;>
      simp only [h] <;> norm_num

theorem frozenFront_mono (init : InputCfg n) (C : Finset (Fin init.card))
    (ℓ cutoff s u : ℕ) (hsu : s ≤ u) (hℓ : 1 ≤ ℓ)
    (hcap : ℓ ≤ 256 * (PhaseThreeModel.Numeric.hourIndex n + 1))
    (ω : InputLog n) :
    Monotone (fun t => frozenFront init C ℓ cutoff s u t ω) := by
  apply monotone_nat_of_le_succ
  intro t
  rcases frozenFront_delta_cases init C ℓ cutoff s u hsu hℓ hcap t ω with h | h <;>
    linarith

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockShapeFreeze

end
