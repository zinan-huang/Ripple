import Ripple.PopulationProtocol.ExactMajority.Compact.State
import Ripple.PopulationProtocol.ExactMajority.Probability.PairLog
import Ripple.PopulationProtocol.ExactMajority.Probability.StabilizationTime

/-!
# Doty et al. Theorem 3.1 for one protocol

Doty, Eftekhari, Gąsieniec, Severson, Stachowiak, Uznański, *A time and space optimal stable
population protocol solving exact majority* (FOCS 2021; arXiv:2106.10201v2), Theorem 3.1: one
protocol with `O(log n)` states stably computes majority and stabilizes in `O(log n)` parallel time,
with probability `1 - O(1/n²)` and in expectation.

`exact_majority_theorem_three_one` states the three parts for the compact protocol
`NonuniformMajorityCompact (clog 2 n) 256`. The time bounds concern that protocol's own
stabilization time: the compact transition is run directly on the scheduled labels of the pair-log
law, the run equals the encoding of the flat run on every log, its semantic stable-correct set
corresponds to the flat one, and the flat semantic stabilization time is at most the endpoint
hitting time `τ_D` bounded by `StabilizationTime.exact_majority_stabilization_time`.
-/

namespace Ripple.PopulationProtocol.ExactMajority.TheoremThreeOne

open Compact TimeTheorem MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

variable {L K n : ℕ}

/-- Update the two persistent labels using the compact protocol's own transition. -/
def compactUpdateLabels (f : Fin n → CompactState L K) (i j : Fin n) :
    Fin n → CompactState L K :=
  Function.update (Function.update f i
    ((Compact.NonuniformMajorityCompact L K).δ (f i) (f j)).1) j
      ((Compact.NonuniformMajorityCompact L K).δ (f i) (f j)).2

/-- The compact transition commutes with encoding on good flat states. This is
`Transition_normalize` packaged by the state simulation. -/
theorem compact_transition_enc (a b : AgentState L K)
    (ha : Compact.Good a) (hb : Compact.Good b) :
    (Compact.NonuniformMajorityCompact L K).δ
        ((Compact.simulation L K).enc a) ((Compact.simulation L K).enc b) =
      ((Compact.simulation L K).enc ((NonuniformMajority L K).δ a b).1,
       (Compact.simulation L K).enc ((NonuniformMajority L K).δ a b).2) :=
  (Compact.simulation L K).enc_δ a b ha hb

/-- Encoding commutes with a labeled compact update. -/
theorem compactUpdateLabels_enc (f : Fin n → AgentState L K) (i j : Fin n)
    (hi : Compact.Good (f i)) (hj : Compact.Good (f j)) :
    compactUpdateLabels ((Compact.simulation L K).enc ∘ f) i j =
      (Compact.simulation L K).enc ∘ PairLog.updateLabels f i j := by
  classical
  have hδ := compact_transition_enc (f i) (f j) hi hj
  funext k
  by_cases hkj : k = j
  · subst k
    simp [compactUpdateLabels, PairLog.updateLabels, Function.comp_def, hδ]
  · by_cases hki : k = i
    · subst k
      simp [compactUpdateLabels, PairLog.updateLabels, Function.comp_def, hδ, hkj]
    · simp [compactUpdateLabels, PairLog.updateLabels, Function.comp_def, hkj, hki]

/-- Run the compact transition on the canonical persistent-label pair schedule.
The schedule guards unsupported draws in exactly the same way as `PairLog`. -/
noncomputable def compactLabels (init : Cfg L K) (ω : Ω L K) :
    ℕ → Fin init.card → CompactState L K
  | 0 => (Compact.simulation L K).enc ∘ PairLog.initialLabels init
  | t + 1 =>
      match PairLog.drawLabels init ω (t + 1) with
      | none => compactLabels init ω t
      | some (i, j) => compactUpdateLabels (compactLabels init ω t) i j

/-- The configuration of the directly defined compact run. -/
noncomputable def compactTrace (init : Cfg L K) (ω : Ω L K) (t : ℕ) :
    Config (CompactState L K) :=
  Finset.univ.val.map (compactLabels init ω t)

/-- Each scheduled compact interaction involves two different physical labels. -/
theorem compact_schedule_distinct (init : Cfg L K) (ω : Ω L K) (t : ℕ)
    (i j : Fin init.card)
    (h : PairLog.drawLabels init ω (t + 1) = some (i, j)) : i ≠ j := by
  change PairLog.selectLabels (PairLog.labelsAt init ω t) (ω (t + 1)) =
    some (i, j) at h
  exact PairLog.selectLabels_distinct _ _ i j h

open Classical in
/-- The compact run's selected physical pair is conditionally uniform under
the same law, even conditioned on the full recorded past. -/
theorem compact_schedule_conditional_probability
    (D : Config (CompactState L K)) (hc : 2 ≤ D.card)
    (i j : Fin ((Compact.simulation L K).embC D).card) (hij : i ≠ j) (t : ℕ) :
    (law ((Compact.simulation L K).embC D))[fun ω =>
      if PairLog.drawLabels ((Compact.simulation L K).embC D) ω (t + 1) = some (i, j)
      then (1 : ℝ) else 0 | PairLog.pairLogFiltration L K t]
      =ᵐ[law ((Compact.simulation L K).embC D)]
    (fun _ => 1 / ((D.card : ℝ) * ((D.card : ℝ) - 1))) := by
  simpa only [StateSimulation.card_embC] using
    PairLog.selected_pair_conditional_probability
      ((Compact.simulation L K).embC D) (by simpa using hc) i j hij t

/-- Valid flat inputs start inside the simulation invariant. -/
theorem goodC_of_validInitial (init : Cfg L K) (hinit : validInitial init) :
    (Compact.simulation L K).GoodC init := by
  intro a ha
  have hp : a.phase.val = 0 := congrArg Fin.val (hinit a ha).1
  exact Compact.good_of_phase_ne_three a (by omega)

/-- Every configuration of every recorded path retains the simulation invariant. -/
theorem trace_goodC (init : Cfg L K) (hinit : validInitial init)
    (ω : Ω L K) (t : ℕ) :
    (Compact.simulation L K).GoodC (TimeTheorem.trace init ω t) := by
  have hreach : (NonuniformMajority L K).Reachable init
      (TimeTheorem.trace init ω t) := by
    simpa only [TimeTheorem.trace_zero] using
      (TimeTheorem.trace_reachable init ω (s := 0) (t := t) (Nat.zero_le t))
  exact ((Compact.simulation L K).reachable_encC
    (goodC_of_validInitial init hinit) hreach).2

/-- The flat state of every persistent label is good, including on unsupported logs. -/
theorem labelsAt_good (init : Cfg L K) (hinit : validInitial init)
    (ω : Ω L K) (t : ℕ) (i : Fin init.card) :
    Compact.Good (PairLog.labelsAt init ω t i) := by
  apply trace_goodC init hinit ω t
  rw [← PairLog.labelsAt_config]
  exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩

/-- The directly defined compact chain agrees with the encoded flat chain at
all labels and times, pointwise on the entire recorded-log space. -/
theorem compactLabels_eq_enc (init : Cfg L K) (hinit : validInitial init)
    (ω : Ω L K) (t : ℕ) :
    compactLabels init ω t =
      (Compact.simulation L K).enc ∘ PairLog.labelsAt init ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [compactLabels, PairLog.labelsAt_succ, PairLog.stepLabels]
      cases hs : PairLog.drawLabels init ω (t + 1) with
      | none =>
          have hsel : PairLog.selectLabels (PairLog.labelsAt init ω t)
              (ω (t + 1)) = none := hs
          simp only [hsel]
          exact ih
      | some p =>
          rcases p with ⟨i, j⟩
          have hsel : PairLog.selectLabels (PairLog.labelsAt init ω t)
              (ω (t + 1)) = some (i, j) := hs
          simp only [hsel]
          rw [ih]
          exact compactUpdateLabels_enc _ i j
            (labelsAt_good init hinit ω t i) (labelsAt_good init hinit ω t j)

/-- Pointwise configuration correspondence for the compact chain. -/
theorem compactTrace_eq_encC (init : Cfg L K) (hinit : validInitial init)
    (ω : Ω L K) (t : ℕ) :
    compactTrace init ω t =
      (Compact.simulation L K).encC (TimeTheorem.trace init ω t) := by
  rw [compactTrace, compactLabels_eq_enc init hinit]
  change Finset.univ.val.map
      ((Compact.simulation L K).enc ∘ PairLog.labelsAt init ω t) =
    (TimeTheorem.trace init ω t).map (Compact.simulation L K).enc
  rw [← Multiset.map_map, PairLog.labelsAt_config]

/-- The compact run begins at the encoded initial configuration. -/
@[simp] theorem compactTrace_zero (init : Cfg L K) (ω : Ω L K) :
    compactTrace init ω 0 = (Compact.simulation L K).encC init := by
  change Finset.univ.val.map
      ((Compact.simulation L K).enc ∘ PairLog.initialLabels init) =
    init.map (Compact.simulation L K).enc
  rw [← Multiset.map_map]
  change (PairLog.labelCfg (PairLog.initialLabels init)).map _ = _
  rw [PairLog.initialLabels_config]

/-- Starting the flat scheduler from the embedding realizes every compact input. -/
@[simp] theorem compactTrace_embC_zero (D : Config (CompactState L K))
    (ω : Ω L K) :
    compactTrace ((Compact.simulation L K).embC D) ω 0 = D := by
  rw [compactTrace_zero, StateSimulation.encC_embC]

/-- Correct output at every reachable future configuration: the semantic
stable-correct set, defined using the protocol's own reachability relation. -/
def stableCorrect {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (P : Protocol Λ) (part : OutputPartition Λ) (u : Bool × Bool × Bool)
    (c : Config Λ) : Prop :=
  ∀ c', P.Reachable c c' → part.output u c'

/-- Semantic stable correctness supplies both the current output and stability. -/
theorem stableCorrect_output_isStable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {P : Protocol Λ} {part : OutputPartition Λ} {u : Bool × Bool × Bool}
    {c : Config Λ} (h : stableCorrect P part u c) :
    part.output u c ∧ P.IsStable part c := by
  have hout := h c Relation.ReflTransGen.refl
  exact ⟨hout, u, hout, h⟩

/-- Output compatibility is an equivalence on encoded good configurations. -/
theorem output_encC_iff {Λ Λ' : Type*}
    [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
    {P : Protocol Λ} {P' : Protocol Λ'} (S : StateSimulation P P')
    {part : OutputPartition Λ} {part' : OutputPartition Λ'}
    (hcompat : S.OutputCompat part part') {c : Config Λ}
    (hc : S.GoodC c) (u : Bool × Bool × Bool) :
    part'.output u (S.encC c) ↔ part.output u c := by
  constructor
  · intro h a ha
    have he := h (S.enc a) (Multiset.mem_map.mpr ⟨a, ha, rfl⟩)
    rw [hcompat a (hc a ha)] at he
    exact he
  · exact S.output_encC hcompat hc u

/-- Reachability lifting and projection identify the semantic stable sets.
This concerns semantic stability, not the smaller phase-endpoint set. -/
theorem stableCorrect_encC_iff {Λ Λ' : Type*}
    [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']
    {P : Protocol Λ} {P' : Protocol Λ'} (S : StateSimulation P P')
    {part : OutputPartition Λ} {part' : OutputPartition Λ'}
    (hcompat : S.OutputCompat part part') {c : Config Λ}
    (hc : S.GoodC c) (u : Bool × Bool × Bool) :
    stableCorrect P' part' u (S.encC c) ↔ stableCorrect P part u c := by
  constructor
  · intro h c' hreach
    obtain ⟨henc, hgood⟩ := S.reachable_encC hc hreach
    exact (output_encC_iff S hcompat hgood u).mp (h _ henc)
  · intro h C' hreach
    obtain ⟨c', hflat, rfl, hgood⟩ := S.lift_reachable hc hreach
    exact S.output_encC hcompat hgood u (h c' hflat)

/-- The compact protocol's own stable-correct set for a compact input. -/
def compactStableDone (D : Config (CompactState L K)) :
    Set (Config (CompactState L K)) :=
  {C | stableCorrect (Compact.NonuniformMajorityCompact L K)
    (Compact.compactPartition L K) (Compact.compactMajorityVerdict D) C}

/-- The actual compact stable set corresponds exactly to semantic flat stability. -/
theorem compactStableDone_encC_iff (D : Config (CompactState L K))
    (c : Cfg L K) (hc : (Compact.simulation L K).GoodC c) :
    (Compact.simulation L K).encC c ∈ compactStableDone D ↔
      stableCorrect (NonuniformMajority L K) (doutPartition L K)
        (majorityVerdict ((Compact.simulation L K).embC D)) c := by
  change stableCorrect _ _ _ _ ↔ _
  rw [Compact.majorityVerdict_embC]
  exact stableCorrect_encC_iff (Compact.simulation L K)
    (Compact.outputCompat L K) hc _

/-- Every phase endpoint used by the time theorem is semantically stable-correct. -/
theorem stableCorrect_of_StableDone (init c : Cfg L K)
    (hc : c ∈ StableDone L K init) :
    stableCorrect (NonuniformMajority L K) (doutPartition L K)
      (majorityVerdict init) c := by
  intro c' hreach
  exact (stable_output_of_majorityStableEndpoint init c'
    (majorityStableEndpoint_preserved_by_reachable init c c' hc hreach)).1

open Classical in
/-- First time at which a predicate holds, with infinity when it never holds. -/
noncomputable def firstHit (p : ℕ → Prop) : ℝ≥0∞ :=
  if h : ∃ t, p t then (Nat.find h : ℝ≥0∞) else ⊤

/-- Enlarging the target can only decrease its first hitting time. -/
theorem firstHit_mono {p q : ℕ → Prop} (hpq : ∀ t, p t → q t) :
    firstHit q ≤ firstHit p := by
  classical
  by_cases hp : ∃ t, p t
  · have hq : ∃ t, q t := ⟨Nat.find hp, hpq _ (Nat.find_spec hp)⟩
    rw [firstHit, dif_pos hq, firstHit, dif_pos hp]
    exact_mod_cast (Nat.find_min' hq (hpq _ (Nat.find_spec hp)))
  · simp only [firstHit, dif_neg hp]
    exact le_top

/-- Pointwise equivalent predicates have identical first hitting times. -/
theorem firstHit_congr {p q : ℕ → Prop} (hpq : ∀ t, p t ↔ q t) :
    firstHit p = firstHit q := by
  have heq : p = q := funext fun t => propext (hpq t)
  rw [heq]

/-- Finite-time characterization of the first hitting time. -/
theorem firstHit_le_iff (p : ℕ → Prop) (T : ℕ) :
    firstHit p ≤ (T : ℝ≥0∞) ↔ ∃ t ≤ T, p t := by
  classical
  by_cases hp : ∃ t, p t
  · rw [firstHit, dif_pos hp]
    constructor
    · intro h
      exact ⟨Nat.find hp, by exact_mod_cast h, Nat.find_spec hp⟩
    · rintro ⟨t, ht, hpt⟩
      exact_mod_cast (Nat.find_min' hp hpt).trans ht
  · rw [firstHit, dif_neg hp]
    simp only [top_le_iff, ENNReal.natCast_ne_top, false_iff]
    rintro ⟨t, _, hpt⟩
    exact hp ⟨t, hpt⟩

/-- Stabilization time of the directly executed compact protocol. -/
noncomputable def compactStabilizationTime (D : Config (CompactState L K))
    (ω : Ω L K) : ℝ≥0∞ :=
  firstHit fun t =>
    compactTrace ((Compact.simulation L K).embC D) ω t ∈ compactStableDone D

/-- Exact equality holds with the flat protocol's semantic stabilization time. -/
theorem compactStabilizationTime_eq_semantic (D : Config (CompactState L K))
    (hD : Compact.compactValidInitial D) (ω : Ω L K) :
    compactStabilizationTime D ω =
      firstHit (fun t => stableCorrect (NonuniformMajority L K) (doutPartition L K)
        (majorityVerdict ((Compact.simulation L K).embC D))
        (TimeTheorem.trace ((Compact.simulation L K).embC D) ω t)) := by
  apply firstHit_congr
  intro t
  have hv := Compact.validInitial_embC D hD
  rw [compactTrace_eq_encC _ hv]
  exact compactStableDone_encC_iff D _ (trace_goodC _ hv ω t)

open Classical in
/-- A first hitting time is the infimum of the successful observation times. -/
theorem firstHit_eq_iInf (p : ℕ → Prop) :
    firstHit p = ⨅ t : ℕ, if p t then (t : ℝ≥0∞) else ⊤ := by
  by_cases h : ∃ t, p t
  · rw [firstHit, dif_pos h]
    apply le_antisymm
    · apply le_iInf
      intro t
      by_cases ht : p t
      · rw [if_pos ht]
        exact_mod_cast (Nat.find_min' h ht)
      · rw [if_neg ht]
        exact le_top
    · apply iInf_le_of_le (Nat.find h)
      rw [if_pos (Nat.find_spec h)]
  · rw [firstHit, dif_neg h]
    apply le_antisymm
    · apply le_iInf
      intro t
      rw [if_neg (fun ht => h ⟨t, ht⟩)]
    · exact le_top

/-- Semantic stabilization of the compact run is a measurable random time. -/
theorem measurable_compactStabilizationTime (D : Config (CompactState L K))
    (hD : Compact.compactValidInitial D) :
    Measurable (compactStabilizationTime D) := by
  classical
  let init := (Compact.simulation L K).embC D
  let A : Set (Cfg L K) := {c | stableCorrect (NonuniformMajority L K)
    (doutPartition L K) (majorityVerdict init) c}
  have heq : compactStabilizationTime D = fun ω =>
      ⨅ t : ℕ, if TimeTheorem.trace init ω t ∈ A
        then (t : ℝ≥0∞) else ⊤ := by
    funext ω
    exact (compactStabilizationTime_eq_semantic D hD ω).trans (firstHit_eq_iInf _)
  rw [heq]
  change Measurable (fun ω => ⨆ t : ℕ, (show OrderDual ℝ≥0∞ from
    if TimeTheorem.trace init ω t ∈ A then (t : ℝ≥0∞) else (⊤ : ℝ≥0∞)))
  apply Measurable.iSup
  intro t
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  exact Measurable.ite
    (hA.preimage ((measurable_pi_apply t).comp (TimeTheorem.measurable_trace init)))
    measurable_const measurable_const

/-- The semantic stabilization time is bounded by the phase-endpoint hitting time.
No equality between semantic stability and the endpoint predicate is assumed. -/
theorem compactStabilizationTime_le_endpoint (D : Config (CompactState L K))
    (hD : Compact.compactValidInitial D) (ω : Ω L K) :
    compactStabilizationTime D ω ≤
      TimeTheorem.τ_D ((Compact.simulation L K).embC D) ω := by
  rw [compactStabilizationTime_eq_semantic D hD ω]
  change firstHit _ ≤ firstHit (fun t =>
    TimeTheorem.trace ((Compact.simulation L K).embC D) ω t ∈
      StableDone L K ((Compact.simulation L K).embC D))
  exact firstHit_mono fun t ht => stableCorrect_of_StableDone _ _ ht

/-- Both quantitative bounds, for the compact chain's semantic stabilization time
under the original occurrence-pair law. Times are measured in interactions. -/
def CompactInputTimeClaim (n : ℕ)
    (D : Config (CompactState (Nat.clog 2 n) 256)) : Prop :=
  TimeTheorem.law ((Compact.simulation (Nat.clog 2 n) 256).embC D)
      {ω | (TimeTheorem.fastHorizon n : ℝ≥0∞) < compactStabilizationTime D ω} ≤
        ENNReal.ofReal (110 / (n : ℝ) ^ 2) ∧
    (∫⁻ ω, compactStabilizationTime D ω
      ∂TimeTheorem.law ((Compact.simulation (Nat.clog 2 n) 256).embC D)) ≤
        ENNReal.ofReal (470235 * (n : ℝ) * Real.log (n : ℝ))

/-- Transfer both bounds by the pointwise comparison of the actual hitting times. -/
theorem compact_input_time_claim (n : ℕ)
    (hn : TimeTheorem.timePopulationThreshold ≤ n)
    (D : Config (CompactState (Nat.clog 2 n) 256))
    (hD : Compact.compactValidInitial D) (hcard : D.card = n) :
    CompactInputTimeClaim n D := by
  have hv := Compact.validInitial_embC D hD
  have hc : ((Compact.simulation (Nat.clog 2 n) 256).embC D).card = n := by
    simpa using hcard
  have htime := StabilizationTime.exact_majority_stabilization_time n hn
    ((Compact.simulation (Nat.clog 2 n) 256).embC D) hv hc
  obtain ⟨htail, hmean⟩ := htime
  constructor
  · exact (measure_mono (fun ω hω =>
      lt_of_lt_of_le hω (compactStabilizationTime_le_endpoint D hD ω))).trans htail
  · exact (lintegral_mono (fun ω =>
      compactStabilizationTime_le_endpoint D hD ω)).trans hmean

/-- An explicit linear-in-log state bound at the time theorem's counter parameter. -/
theorem compact_state_count_time_parameters (n : ℕ) :
    Fintype.card (CompactState (Nat.clog 2 n) 256) ≤
      23136960 * (Nat.clog 2 n + 1) := by
  have h := Compact.card_compactState_le (Nat.clog 2 n) 256
  refine h.trans ?_
  have hsplit : (73920 : ℕ) * ((256 + 53) * (Nat.clog 2 n + 1) + 4) =
      22841280 * (Nat.clog 2 n + 1) + 295680 := by ring
  rw [hsplit]
  nlinarith [Nat.zero_le (Nat.clog 2 n)]

/-- Doty et al. Theorem 3.1 for one compact protocol: logarithmic states,
stable majority computation, and the stated tail and expected-time bounds
for that protocol's own stabilization time. -/
theorem exact_majority_theorem_three_one (n : ℕ)
    (hn : TimeTheorem.timePopulationThreshold ≤ n) :
    Fintype.card (CompactState (Nat.clog 2 n) 256) ≤
        23136960 * (Nat.clog 2 n + 1) ∧
      Protocol.StablyComputes
        (Compact.NonuniformMajorityCompact (Nat.clog 2 n) 256)
        (Compact.compactPartition (Nat.clog 2 n) 256)
        (fun D => Compact.compactValidInitial D ∧ D.card = n)
        Compact.compactMajorityVerdict ∧
      ∀ D : Config (CompactState (Nat.clog 2 n) 256),
        Compact.compactValidInitial D → D.card = n → CompactInputTimeClaim n D := by
  refine ⟨compact_state_count_time_parameters n, ?_, compact_input_time_claim n hn⟩
  apply Compact.compact_stable_majority_correct_clog
  have hlarge := (TimeTheorem.time_population_bounds hn).2
  omega

end Ripple.PopulationProtocol.ExactMajority.TheoremThreeOne
