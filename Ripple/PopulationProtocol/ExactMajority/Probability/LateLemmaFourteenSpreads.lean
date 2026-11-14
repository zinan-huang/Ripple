import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaThirteenRoute
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaFourteenCleanup
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2CarrierEpidemic
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase9OutputCleanup
import Ripple.PopulationProtocol.ExactMajority.Probability.ThresholdEpidemic

/-!
# Lemma 14: the phase-threshold spread

The sharp state-independent threshold tail is applied at the genuine first
Phase-9 seed. Its existing stopping-time splice retains each seed fibre's
probability, so the bound has no extra factor for times or population labels.
The exact Phase-9 corollary additionally uses the observed trace's phase ceiling.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads

open TimeTheorem PairLog StageEventSpec
open LateTimerProtectionOriginalLaw

variable {n : ℕ}

/-- Failure of threshold 9 to cover within the first four-unit window of
Lemma 14, measured from its genuine exact first seed. -/
def phaseNineSpreadFailure (init : InputCfg n) : Set (InputLog n) :=
  {omega | ∃ firstNine : ℕ,
    firstPhaseSeed init 9 firstNine omega ∧
      ¬ ∀ a ∈ trace init omega (firstNine + logWindow n 4),
        9 ≤ a.phase.val}

/-- The first Phase-9 spread has a measurable failure event. -/
theorem measurableSet_phaseNineSpreadFailure (init : InputCfg n) :
    MeasurableSet (phaseNineSpreadFailure init) := by
  rw [show phaseNineSpreadFailure init =
      ⋃ firstNine : ℕ,
        {omega | firstPhaseSeed init 9 firstNine omega} ∩
        {omega | ¬ ∀ a ∈ trace init omega
          (firstNine + logWindow n 4), 9 ≤ a.phase.val} by
    ext omega
    simp [phaseNineSpreadFailure]]
  apply MeasurableSet.iUnion
  intro firstNine
  apply (((pairLogFiltration
    (PhaseThreeModel.Numeric.hourIndex n) 256).le firstNine) _
      (firstPhaseSeed_measurableSet init 9 firstNine)).inter
  exact (Set.to_countable
    {c : InputCfg n | ¬ ∀ a ∈ c, 9 ≤ a.phase.val}).measurableSet.preimage
      ((measurable_trace_at init (firstNine + logWindow n 4)).mono
        ((pairLogFiltration
          (PhaseThreeModel.Numeric.hourIndex n) 256).le
            (firstNine + logWindow n 4)) le_rfl)

/-- The unconditional threshold-9 failure budget in Lemma 14 is exactly
`exp 3 * n ^ (-3)`, without a union factor for seed times. -/
theorem law_phaseNineSpreadFailure (init : InputCfg n)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseNineSpreadFailure init) ≤
      ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (-3 : ℝ)) := by
  have hexponent : (1 : ℝ) - (4 : ℝ) = -3 := by norm_num
  simpa [phaseNineSpreadFailure, hexponent] using
    (ThresholdEpidemic.threshold_spread_sharp_tail
      init hinput (⟨9, by norm_num⟩ : Fin 11)
      (by norm_num) 4 (by norm_num))

/-- Outside the named failure event, the exact first seed supplies threshold
coverage at the end of the first spread window. -/
theorem phaseNineThreshold_of_not_failure
    (init : InputCfg n) (omega : InputLog n) (firstNine : ℕ)
    (hseed : firstPhaseSeed init 9 firstNine omega)
    (hgood : omega ∉ phaseNineSpreadFailure init) :
    ∀ a ∈ trace init omega (firstNine + logWindow n 4),
      9 ≤ a.phase.val := by
  by_contra hbad
  exact hgood ⟨firstNine, hseed, hbad⟩

/-- A finite threshold-9 entry is the exact first Phase-9 seed whenever the
observed entry state contains no phase above 9. -/
theorem firstPhaseNineSeed_of_time_and_ceiling
    (init : InputCfg n) (omega : InputLog n) (firstNine : ℕ)
    (hfirst : phaseSeedTime init 9 omega = (firstNine : WithTop ℕ))
    (hceiling : ∀ a ∈ trace init omega firstNine, a.phase.val ≤ 9) :
    firstPhaseSeed init 9 firstNine omega := by
  have hhit := (phaseSeedTime_eq_iff init 9 omega firstNine).mp hfirst
  constructor
  · obtain ⟨a, ha, hge⟩ := hhit.1
    exact ⟨a, ha, Nat.le_antisymm (hceiling a ha) hge⟩
  · intro s hs a ha
    by_contra hbad
    exact hhit.2 s hs ⟨a, ha, by omega⟩

/-- An observed phase ceiling turns the threshold conclusion of the first
spread into exact homogeneous Phase 9. -/
theorem phaseNineExactly_of_not_failure
    (init : InputCfg n) (omega : InputLog n) (firstNine : ℕ)
    (hseed : firstPhaseSeed init 9 firstNine omega)
    (hgood : omega ∉ phaseNineSpreadFailure init)
    (hceiling : ∀ a ∈ trace init omega (firstNine + logWindow n 4),
      a.phase.val ≤ 9) :
    ∀ a ∈ trace init omega (firstNine + logWindow n 4),
      a.phase.val = 9 := by
  intro a ha
  exact Nat.le_antisymm (hceiling a ha)
    (phaseNineThreshold_of_not_failure init omega firstNine hseed hgood a ha)

/-- The finite canonical first-nine time and observed ceilings at entry and at
the first window's end give homogeneous Phase 9 outside the unconditional event. -/
theorem phaseNineExactly_of_time_and_ceiling
    (init : InputCfg n) (omega : InputLog n) (firstNine : ℕ)
    (hfirst : phaseSeedTime init 9 omega = (firstNine : WithTop ℕ))
    (hentry : ∀ a ∈ trace init omega firstNine, a.phase.val ≤ 9)
    (hgood : omega ∉ phaseNineSpreadFailure init)
    (hceiling : ∀ a ∈ trace init omega (firstNine + logWindow n 4),
      a.phase.val ≤ 9) :
    ∀ a ∈ trace init omega (firstNine + logWindow n 4),
      a.phase.val = 9 :=
  phaseNineExactly_of_not_failure init omega firstNine
    (firstPhaseNineSeed_of_time_and_ceiling init omega firstNine hfirst hentry)
    hgood hceiling

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads

end

/-!
# Phase-9 carrier propagation from Phase-2 union semantics

Opinion compatibility and the carrier bit depend only on the opinion masks.
The public Phase-2 carrier theorem therefore supplies their union properties.
The nonconflicting Phase-9 dispatcher writes the same union without changing phase.
-/

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads

variable {L K : ℕ}

private theorem same_phase_epidemic_eq_self
    (s t : AgentState L K) (hphase : s.phase = t.phase) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  classical
  have hbad : ¬ ((t.phase.val < 10 ∨ t.phase.val < 10) ∧
      (t.phase.val = 10 ∨ t.phase.val = 10)) := by omega
  unfold phaseEpidemicUpdate
  rw [hphase, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

/-- Outside the conflicting-sign branch, the opinion transition preserves
both phases and writes exactly the union to both endpoints. -/
private theorem phase_two_fields_of_no_conflict
    (s t : AgentState L K)
    (hnc : (hasMinusOne (opinionsUnion s.opinions t.opinions) &&
      hasPlusOne (opinionsUnion s.opinions t.opinions)) = false) :
    (Phase2Transition L K s t).1.phase = s.phase ∧
    (Phase2Transition L K s t).2.phase = t.phase ∧
    (Phase2Transition L K s t).1.opinions = opinionsUnion s.opinions t.opinions ∧
    (Phase2Transition L K s t).2.opinions = opinionsUnion s.opinions t.opinions := by
  unfold Phase2Transition
  simp only [hnc, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem transition_two_opinions_of_no_conflict
    (s t : AgentState L K) (hs : s.phase.val = 2) (ht : t.phase.val = 2)
    (hnc : (hasMinusOne (opinionsUnion s.opinions t.opinions) &&
      hasPlusOne (opinionsUnion s.opinions t.opinions)) = false) :
    (Transition L K s t).1.opinions = opinionsUnion s.opinions t.opinions ∧
    (Transition L K s t).2.opinions = opinionsUnion s.opinions t.opinions := by
  have hsp : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  have hepi := same_phase_epidemic_eq_self s t (hsp.trans htp.symm)
  have hf := phase_two_fields_of_no_conflict s t hnc
  have hleft : (Phase2Transition L K s t).1.phase.val ≠ 10 := by
    rw [hf.1]
    omega
  have hright : (Phase2Transition L K s t).2.phase.val ≠ 10 := by
    rw [hf.2.1]
    omega
  simpa only [Transition, hepi, hsp,
    finishPhase10Entry_eq_self_of_after_ne_10 L K s _ hleft,
    finishPhase10Entry_eq_self_of_after_ne_10 L K t _ hright] using hf.2.2

/-- The public Phase-2 carrier theorem implies compatibility and carrier
propagation for the opinion union itself. -/
theorem opinion_union_carrier_properties
    (out : Output) (s t : AgentState L K)
    (hs : Phase2CarrierEpidemic.opinionCompatible out s.opinions)
    (ht : Phase2CarrierEpidemic.opinionCompatible out t.opinions) :
    Phase2CarrierEpidemic.opinionCompatible out (opinionsUnion s.opinions t.opinions) ∧
      (Phase2CarrierEpidemic.opinionCarrier out s.opinions ∨
        Phase2CarrierEpidemic.opinionCarrier out t.opinions →
        Phase2CarrierEpidemic.opinionCarrier out (opinionsUnion s.opinions t.opinions)) := by
  let sTwo : AgentState L K := { s with phase := ⟨2, by decide⟩ }
  let tTwo : AgentState L K := { t with phase := ⟨2, by decide⟩ }
  have hnc := Phase2CarrierEpidemic.opinionCompatible_union_not_conflicting
    out s.opinions t.opinions hs ht
  have hpair := Phase2CarrierEpidemic.Transition_phase2_carrier_pair
    out sTwo tTwo rfl rfl hs ht
  have hop := transition_two_opinions_of_no_conflict sTwo tTwo rfl rfl hnc
  rw [hop.1] at hpair
  exact ⟨hpair.1.2, fun h => (hpair.2.2 h).1⟩

/-- Compatibility excludes the Phase-9 advance branch. Union then copies any
selected carrier to both endpoints, including opinions containing neutral bits. -/
theorem Transition_phase_nine_carrier_pair_structural
    (out : Output) (s t : AgentState L K)
    (hs : s.phase.val = 9) (ht : t.phase.val = 9)
    (hsc : Phase2CarrierEpidemic.opinionCompatible out s.opinions)
    (htc : Phase2CarrierEpidemic.opinionCompatible out t.opinions) :
    ((Transition L K s t).1.phase.val = 9 ∧
        Phase2CarrierEpidemic.opinionCompatible out (Transition L K s t).1.opinions) ∧
      ((Transition L K s t).2.phase.val = 9 ∧
        Phase2CarrierEpidemic.opinionCompatible out (Transition L K s t).2.opinions) ∧
      (Phase2CarrierEpidemic.opinionCarrier out s.opinions ∨
          Phase2CarrierEpidemic.opinionCarrier out t.opinions →
        Phase2CarrierEpidemic.opinionCarrier out (Transition L K s t).1.opinions ∧
          Phase2CarrierEpidemic.opinionCarrier out (Transition L K s t).2.opinions) := by
  have hsp : s.phase = ⟨9, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨9, by decide⟩ := Fin.ext ht
  have hepi := same_phase_epidemic_eq_self s t (hsp.trans htp.symm)
  have hnc := Phase2CarrierEpidemic.opinionCompatible_union_not_conflicting
    out s.opinions t.opinions hsc htc
  have hf := phase_two_fields_of_no_conflict s t hnc
  have hleft : (Phase2Transition L K s t).1.phase.val ≠ 10 := by
    rw [hf.1]
    omega
  have hright : (Phase2Transition L K s t).2.phase.val ≠ 10 := by
    rw [hf.2.1]
    omega
  have heq : Transition L K s t = Phase2Transition L K s t := by
    simp only [Transition, hepi, hsp, Phase9Transition,
      finishPhase10Entry_eq_self_of_after_ne_10 L K s _ hleft,
      finishPhase10Entry_eq_self_of_after_ne_10 L K t _ hright]
  have hunion := opinion_union_carrier_properties out s t hsc htc
  rw [heq, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]
  exact ⟨⟨hs, hunion.1⟩, ⟨ht, hunion.1⟩,
    fun h => ⟨hunion.2 h, hunion.2 h⟩⟩

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads

/-!
# Lemma 14 majority-opinion spread

The surviving sign follows the two-orientation SI epidemic after the population
enters Phase 9. Neutral opinions may occur in any mask.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal Real
namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads
open AdvanceEpidemics RoleSplitConcentration
variable {L K : ℕ}

/-- Opinion-bitset compatibility with a fixed Phase-9 verdict branch. -/
def opinionCompatible (out : Output) (o : Fin 8) : Prop :=
  match out with
  | .A => hasMinusOne o = false
  | .B => hasPlusOne o = false
  | .T => o = phase2OpinionT

/-- The selected strict verdict sign is present in an opinion bitset. -/
def opinionCarrier (out : Output) (o : Fin 8) : Prop :=
  match out with
  | .A => hasPlusOne o = true
  | .B => hasMinusOne o = true
  | .T => False

instance (out : Output) (o : Fin 8) : Decidable (opinionCompatible out o) := by
  cases out <;> unfold opinionCompatible <;> infer_instance

instance (out : Output) (o : Fin 8) : Decidable (opinionCarrier out o) := by
  cases out <;> unfold opinionCarrier <;> infer_instance

/-- Two opinions compatible with one verdict cannot trigger Phase 9's
conflicting-sign advance branch after union. -/
theorem opinionCompatible_union_not_conflicting
    (out : Output) (u v : Fin 8)
    (hu : opinionCompatible out u) (hv : opinionCompatible out v) :
    (hasMinusOne (opinionsUnion u v) &&
        hasPlusOne (opinionsUnion u v)) = false := by
  exact Phase2CarrierEpidemic.opinionCompatible_union_not_conflicting out u v hu hv

/-- Number of agents whose Phase-9 opinion contains the selected strict sign. -/
noncomputable def opinionCount (out : Output)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP
    (fun a => opinionCarrier out a.opinions) c

/-- The exact pointwise surface retained during strict-branch propagation. -/
def OpinionSpreadPre (out : Output) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
    (∀ a ∈ c, a.phase.val = 9 ∧
      opinionCompatible out a.opinions) ∧
    1 ≤ opinionCount out c

/-- Compatibility excludes the Phase-9 advance branch, and opinion union
copies any selected carrier to both endpoints. -/
theorem Transition_phase_nine_carrier_pair
    (out : Output) (s t : AgentState L K)
    (hs2 : s.phase.val = 9) (ht2 : t.phase.val = 9)
    (hs : opinionCompatible out s.opinions)
    (ht : opinionCompatible out t.opinions) :
    ((Transition L K s t).1.phase.val = 9 ∧
        opinionCompatible out (Transition L K s t).1.opinions) ∧
      ((Transition L K s t).2.phase.val = 9 ∧
        opinionCompatible out (Transition L K s t).2.opinions) ∧
      (opinionCarrier out s.opinions ∨
          opinionCarrier out t.opinions →
        opinionCarrier out (Transition L K s t).1.opinions ∧
          opinionCarrier out (Transition L K s t).2.opinions) := by
  exact Transition_phase_nine_carrier_pair_structural out s t hs2 ht2 hs ht

/-- Replacing an applicable pair preserves the pointwise Phase-9 compatibility
surface. -/
theorem OpinionSpreadPre_pointwise_stepOrSelf
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : OpinionSpreadPre out n c) (s t : AgentState L K) :
    ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val = 9 ∧ opinionCompatible out a.opinions := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := Transition_phase_nine_carrier_pair out s t
      (hInv.2.1 s hs_mem).1 (hInv.2.1 t ht_mem).1
      (hInv.2.1 s hs_mem).2 (hInv.2.1 t ht_mem).2
    have hc' :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    rw [hc']
    intro a ha
    have ha' :
        a = (Transition L K s t).1 ∨ a ∈ c - {s, t} ∨
          a = (Transition L K s t).2 := by
      simpa using ha
    rcases ha' with rfl | haold | rfl
    · exact hpair.1
    · exact hInv.2.1 a
        (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) haold)
    · exact hpair.2.1
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hInv.2.1

/-- The carrier count never decreases on the strict compatibility surface. -/
theorem opinionCount_stepOrSelf_le
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : OpinionSpreadPre out n c) (s t : AgentState L K) :
    opinionCount out c ≤
      opinionCount out
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := Transition_phase_nine_carrier_pair out s t
      (hInv.2.1 s hs_mem).1 (hInv.2.1 t ht_mem).1
      (hInv.2.1 s hs_mem).2 (hInv.2.1 t ht_mem).2
    have hc' :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
    have hsplit : opinionCount out c =
        opinionCount out (c - {s, t}) +
          Multiset.countP
            (fun a => opinionCarrier out a.opinions)
            ({s, t} : Multiset (AgentState L K)) := by
      unfold opinionCount
      rw [← Multiset.countP_add, Multiset.sub_add_cancel hsub]
    unfold opinionCount at hsplit
    unfold opinionCount
    rw [hc', Multiset.countP_add]
    rw [hsplit]
    rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
      show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl]
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero,
      Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    by_cases hsCarrier : opinionCarrier out s.opinions <;>
      by_cases htCarrier : opinionCarrier out t.opinions
    · have hout := hpair.2.2 (Or.inl hsCarrier)
      simp [hsCarrier, htCarrier, hout.1, hout.2]
    · have hout := hpair.2.2 (Or.inl hsCarrier)
      simp [hsCarrier, htCarrier, hout.1, hout.2]
    · have hout := hpair.2.2 (Or.inr htCarrier)
      simp [hsCarrier, htCarrier, hout.1, hout.2]
    · simp [hsCarrier, htCarrier]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- A selected carrier/non-carrier pair raises the global carrier count by one. -/
theorem opinionCount_stepOrSelf_advance
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : OpinionSpreadPre out n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hmixed : (opinionCarrier out s.opinions ∧ ¬ opinionCarrier out t.opinions) ∨
      (¬ opinionCarrier out s.opinions ∧ opinionCarrier out t.opinions)) :
    opinionCount out c + 1 ≤
      opinionCount out
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := Transition_phase_nine_carrier_pair out s t
    (hInv.2.1 s hs_mem).1 (hInv.2.1 t ht_mem).1
    (hInv.2.1 s hs_mem).2 (hInv.2.1 t ht_mem).2
  have hout := hpair.2.2 (hmixed.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2))
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold opinionCount
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le :
      Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions) {s, t} ≤
        Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions) c :=
    Multiset.countP_le_of_le
    (fun a : AgentState L K =>
      opinionCarrier out a.opinions) hsub
  have hold :
      Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions) {s, t} = 1 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
      Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    rcases hmixed with ⟨hsCarrier, htCarrier⟩ | ⟨hsCarrier, htCarrier⟩ <;>
      simp [hsCarrier, htCarrier]
  have hnew :
      Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions)
          {(Transition L K s t).1, (Transition L K s t).2} = 2 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl,
      Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    simp [hout.1, hout.2]
  rw [hold] at hpair_le
  rw [hnew]
  omega

/-- The strict invariant is preserved by every scheduled pair. -/
theorem OpinionSpreadPre_stepOrSelf
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : OpinionSpreadPre out n c) (s t : AgentState L K) :
    OpinionSpreadPre out n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  refine ⟨?_, OpinionSpreadPre_pointwise_stepOrSelf out n c hInv s t, ?_⟩
  · rw [Protocol.stepOrSelf_card_eq]
    exact hInv.1
  · exact le_trans hInv.2.2 (opinionCount_stepOrSelf_le out n c hInv s t)

/-- Strict-invariant closure along one deterministic protocol step. -/
theorem OpinionSpreadPre_stepRel
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : OpinionSpreadPre out n c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    OpinionSpreadPre out n c' := by
  classical
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  have heq :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t = c' := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    exact hc'.symm
  rw [← heq]
  exact OpinionSpreadPre_stepOrSelf out n c hInv s t

/-- The strict surface is closed along every finite execution. -/
theorem OpinionSpreadPre_reachable
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : OpinionSpreadPre out n c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    OpinionSpreadPre out n c' := by
  classical
  induction hreach with
  | refl => exact hInv
  | tail _ hstep ih => exact OpinionSpreadPre_stepRel out n ih hstep

/-- Carrier-count monotonicity along one deterministic protocol step. -/
theorem opinionCount_stepRel_le
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : OpinionSpreadPre out n c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    opinionCount out c ≤ opinionCount out c' := by
  classical
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  have heq :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t = c' := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    exact hc'.symm
  rw [← heq]
  exact opinionCount_stepOrSelf_le out n c hInv s t

/-- Carrier-count monotonicity along every finite execution. -/
theorem opinionCount_reachable_le
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : OpinionSpreadPre out n c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    opinionCount out c ≤ opinionCount out c' := by
  classical
  induction hreach with
  | refl => exact le_rfl
  | @tail b d hprefix hstep ih =>
      exact le_trans ih
        (opinionCount_stepRel_le out n
          (OpinionSpreadPre_reachable out n hInv hprefix) hstep)

/-- Scheduler-support form of strict-invariant closure. -/
theorem OpinionSpreadPre_of_stepDistOrSelf_support
    (out : Output) (n : ℕ) (c c' : Config (AgentState L K))
    (hInv : OpinionSpreadPre out n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    OpinionSpreadPre out n c' :=
  OpinionSpreadPre_reachable out n hInv
    (Protocol.stepDistOrSelf_support_reachable
      (NonuniformMajority L K) c c' hsupp)

/-- Scheduler-support form of carrier-count monotonicity. -/
theorem opinionCount_of_stepDistOrSelf_support_le
    (out : Output) (n : ℕ) (c c' : Config (AgentState L K))
    (hInv : OpinionSpreadPre out n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    opinionCount out c ≤ opinionCount out c' :=
  opinionCount_reachable_le out n hInv
    (Protocol.stepDistOrSelf_support_reachable
      (NonuniformMajority L K) c c' hsupp)

/-! ## Carrier/non-carrier rectangle -/

/-- Sum of occurrence counts over a decidable state predicate. -/
private theorem sum_count_filter_eq_countP
    (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter p, c.count a) = Multiset.countP p c := by
  classical
  calc
    (∑ a ∈ Finset.univ.filter p, c.count a)
        = ∑ a : AgentState L K, if p a then c.count a else 0 :=
          Finset.sum_filter _ _
    _ = ∑ a : AgentState L K, (c.filter p).count a := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      show _ = Multiset.count a (c.filter p)
      rw [Multiset.count_filter]
      rfl
    _ = (c.filter p).card :=
      Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm

/-- Every occurrence is either a carrier or a non-carrier. -/
private theorem opinionCount_add_noncarrierCount
    (out : Output) (c : Config (AgentState L K)) :
    opinionCount out c +
        Multiset.countP
          (fun a : AgentState L K =>
            ¬ opinionCarrier out a.opinions) c =
      c.card := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [opinionCount]
  | @cons a c ih =>
      unfold opinionCount at ih ⊢
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
      by_cases h : opinionCarrier out a.opinions <;>
        simp [h] at ih ⊢ <;> omega

/-- States carrying the selected branch sign. -/
noncomputable def carrierStates (out : Output) : Finset (AgentState L K) :=
  Finset.univ.filter
    (fun a => opinionCarrier out a.opinions)

/-- States not yet carrying the selected branch sign. -/
noncomputable def noncarrierStates (out : Output) : Finset (AgentState L K) :=
  Finset.univ.filter
    (fun a => ¬ opinionCarrier out a.opinions)

theorem carrierStates_noncarrierStates_disjoint
    (out : Output) (a : AgentState L K) (ha : a ∈ carrierStates out)
    (b : AgentState L K) (hb : b ∈ noncarrierStates out) : a ≠ b := by
  classical
  simp only [carrierStates, noncarrierStates, Finset.mem_filter] at ha hb
  intro hab
  subst b
  exact hb.2 ha.2

/-- Exact scheduler mass of the one-way carrier/non-carrier rectangle. -/
theorem sum_interactionCount_carrierRect
    (out : Output) (c : Config (AgentState L K)) :
    (∑ p ∈ carrierStates (L := L) (K := K) out ×ˢ
        noncarrierStates (L := L) (K := K) out,
        c.interactionCount p.1 p.2) =
      opinionCount out c * (c.card - opinionCount out c) := by
  classical
  rw [Phase5Convergence.sum_interactionCount_cross_disjoint5 c _ _
      (carrierStates_noncarrierStates_disjoint out),
    carrierStates, noncarrierStates,
    sum_count_filter_eq_countP, sum_count_filter_eq_countP]
  have hsplit := opinionCount_add_noncarrierCount out c
  have hle : opinionCount out c ≤ c.card := by
    unfold opinionCount
    exact Multiset.countP_le_card _ _
  have hnon :
      Multiset.countP
          (fun a : AgentState L K =>
            ¬ opinionCarrier out a.opinions) c =
        c.card - opinionCount out c := by
    omega
  rw [hnon]
  rfl

/-- Both orientations of a selected mixed pair contribute to the SI rate. -/
theorem opinion_advance_probability
    (out : Output) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : OpinionSpreadPre out n c) :
    ENNReal.ofReal
        (((2 * opinionCount out c * (n - opinionCount out c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {d | opinionCount out c + 1 ≤ opinionCount out d} := by
  classical
  let A := carrierStates (L := L) (K := K) out
  let B := noncarrierStates (L := L) (K := K) out
  let R := (A ×ˢ B) ∪ (B ×ˢ A)
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b :=
    carrierStates_noncarrierStates_disjoint out
  have hBA : ∀ b ∈ B, ∀ a ∈ A, b ≠ a :=
    fun b hb a ha => (hAB a ha b hb).symm
  have hdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    refine Finset.disjoint_left.mpr ?_
    intro pr hpr hpr'
    exact hAB pr.1 (Finset.mem_product.mp hpr).1
      pr.1 (Finset.mem_product.mp hpr').1 rfl
  have hA : (∑ a ∈ A, c.count a) = opinionCount out c := by
    exact sum_count_filter_eq_countP _ c
  have hB : (∑ a ∈ B, c.count a) = n - opinionCount out c := by
    have hsplit := opinionCount_add_noncarrierCount out c
    rw [hInv.1] at hsplit
    have hsum : (∑ a ∈ B, c.count a) =
        Multiset.countP (fun a => ¬ opinionCarrier out a.opinions) c :=
      sum_count_filter_eq_countP _ c
    omega
  have hsum : (∑ pr ∈ R, c.interactionCount pr.1 pr.2) =
      2 * opinionCount out c * (n - opinionCount out c) := by
    rw [show R = (A ×ˢ B) ∪ (B ×ˢ A) from rfl,
      Finset.sum_union hdisj,
      Phase5Convergence.sum_interactionCount_cross_disjoint5 c A B hAB,
      Phase5Convergence.sum_interactionCount_cross_disjoint5 c B A hBA, hA, hB]
    ring
  refine Phase5Convergence.rise_prob_of_rect5 (opinionCount out) n hn c hInv.1 R
    (2 * opinionCount out c * (n - opinionCount out c)) ?_ (by rw [hsum])
  rintro ⟨a, b⟩ hpr ha hb _
  have hmixed :
      (opinionCarrier out a.opinions ∧ ¬ opinionCarrier out b.opinions) ∨
        (¬ opinionCarrier out a.opinions ∧ opinionCarrier out b.opinions) := by
    rcases Finset.mem_union.mp hpr with hpr | hpr
    · exact Or.inl ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hpr).1).2,
        (Finset.mem_filter.mp (Finset.mem_product.mp hpr).2).2⟩
    · exact Or.inr ⟨(Finset.mem_filter.mp (Finset.mem_product.mp hpr).1).2,
        (Finset.mem_filter.mp (Finset.mem_product.mp hpr).2).2⟩
  have hab : a ≠ b := by
    intro hab
    subst b
    rcases hmixed with h | h
    · exact h.2 h.1
    · exact h.1 h.2
  have happ : Protocol.Applicable c a b :=
    Phase5Convergence.applicable_of_mem_distinct5
      (Multiset.one_le_count_iff_mem.mp ha) (Multiset.one_le_count_iff_mem.mp hb) hab
  exact opinionCount_stepOrSelf_advance out n c hInv a b happ hmixed

private noncomputable def opinionRate (n : ℕ) (i : Fin (n - 1)) : ℝ :=
  2 * ((i.val : ℝ) + 1) *
    ((n : ℝ) - ((i.val : ℝ) + 1)) /
    ((n : ℝ) * ((n : ℝ) - 1))

private theorem opinionRate_bounds {n : ℕ} (hn : 2 ≤ n)
    (i : Fin (n - 1)) :
    0 < opinionRate n i ∧ opinionRate n i ≤ 1 ∧
      1 / (n : ℝ) < opinionRate n i := by
  have hi : i.val + 1 < n := by have := i.isLt; omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hiR : (i.val : ℝ) + 1 < n := by exact_mod_cast hi
  have hiRpos : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
  have hnRpos : (0 : ℝ) < n := by linarith
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hnum : 0 < 2 * ((i.val : ℝ) + 1) *
      ((n : ℝ) - ((i.val : ℝ) + 1)) :=
    mul_pos (mul_pos (by norm_num) hiRpos) (sub_pos.mpr hiR)
  refine ⟨div_pos hnum hden, ?_, ?_⟩
  · unfold opinionRate
    rw [div_le_one hden]
    nlinarith [sq_nonneg ((n : ℝ) - 2 * ((i.val : ℝ) + 1)),
      mul_nonneg hnRpos.le (sub_nonneg.mpr hnR)]
  · have hfloorN := AdvanceEpidemics.sub_one_le_mul_sub n (i.val + 1) (by omega) hi
    have hfloor : (n : ℝ) - 1 ≤
        ((i.val : ℝ) + 1) * ((n : ℝ) - ((i.val : ℝ) + 1)) := by
      have hcast : ((n - 1 : ℕ) : ℝ) ≤
          (((i.val + 1) * (n - (i.val + 1)) : ℕ) : ℝ) := by
        exact_mod_cast hfloorN
      simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one,
        Nat.cast_mul, Nat.cast_sub hi.le, Nat.cast_add] using hcast
    have hcancel :
        (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) - 1)) = (n : ℝ) - 1 := by
      field_simp [hnRpos.ne']
    unfold opinionRate
    rw [lt_div_iff₀ hden, hcancel]
    nlinarith

private theorem opinionRate_converges {n : ℕ} (hn : 2 ≤ n)
    (i : Fin (n - 1)) :
    (1 - opinionRate n i) * Real.exp (1 / (n : ℝ)) < 1 :=
  shifted_geometric_mgf_converges_of_nonneg_lt
    (opinionRate_bounds hn i).1 (by positivity)
    (opinionRate_bounds hn i).2.2

/-- SI milestones retain the closed Phase-9 sign surface. -/
private noncomputable def opinionMilestones
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    RoleSplitConcentration.MilestonePhaseOn (NonuniformMajority L K) where
  k := n - 1
  milestone i c := OpinionSpreadPre out n c ∧ i.val + 2 ≤ opinionCount out c
  p := opinionRate n
  hp_pos i := (opinionRate_bounds hn i).1
  hp_le_one i := (opinionRate_bounds hn i).2.1
  milestone_monotone := by
    intro i c d h hsupp
    exact ⟨OpinionSpreadPre_of_stepDistOrSelf_support out n c d h.1 hsupp,
      le_trans h.2 (opinionCount_of_stepDistOrSelf_support_le out n c d h.1 hsupp)⟩
  Inv := OpinionSpreadPre out n
  inv_closed := by
    classical
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {d | ¬ OpinionSpreadPre out n d} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
    intro d hsupp hbad
    exact hbad (OpinionSpreadPre_of_stepDistOrSelf_support out n c d hInv hsupp)
  progress_on := by
    classical
    intro i c hInv hprev hcur
    have hcount : opinionCount out c = i.val + 1 := by
      have hlt : opinionCount out c < i.val + 2 :=
        Nat.lt_of_not_ge (fun h => hcur ⟨hInv, h⟩)
      have hle : i.val + 1 ≤ opinionCount out c := by
        by_cases hi : i.val = 0
        · have := hInv.2.2
          omega
        · have hh := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          have := hh.2
          dsimp only at this
          omega
      omega
    have hbound := opinion_advance_probability out n hn c hInv
    have hi : i.val + 1 ≤ n := by have := i.isLt; omega
    have heq :
        (((2 * opinionCount out c * (n - opinionCount out c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) = opinionRate n i := by
      rw [hcount]
      simp only [opinionRate, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    rw [heq] at hbound
    have hescape : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {d | ¬ OpinionSpreadPre out n d} = 0 := by
      rw [PMF.toMeasure_apply_eq_zero_iff
        (p := (NonuniformMajority L K).stepDistOrSelf c)
        (DiscreteMeasurableSpace.forall_measurableSet _), Set.disjoint_left]
      intro d hsupp hbad
      exact hbad (OpinionSpreadPre_of_stepDistOrSelf_support out n c d hInv hsupp)
    have hsub : {d : Config (AgentState L K) | opinionCount out c + 1 ≤ opinionCount out d} ⊆
        {d | OpinionSpreadPre out n d ∧ i.val + 2 ≤ opinionCount out d} ∪
          {d | ¬ OpinionSpreadPre out n d} := by
      intro d hd
      by_cases hpre : OpinionSpreadPre out n d
      · left
        exact ⟨hpre, by dsimp only [Set.mem_setOf_eq] at hd; omega⟩
      · exact Or.inr hpre
    calc
      ENNReal.ofReal (opinionRate n i) ≤
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {d | opinionCount out c + 1 ≤ opinionCount out d} := hbound
      _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          ({d | OpinionSpreadPre out n d ∧ i.val + 2 ≤ opinionCount out d} ∪
            {d | ¬ OpinionSpreadPre out n d}) := measure_mono hsub
      _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
          {d | OpinionSpreadPre out n d ∧ i.val + 2 ≤ opinionCount out d} +
            ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
              {d | ¬ OpinionSpreadPre out n d} := measure_union_le _ _
      _ = _ := by rw [hescape, add_zero]

/-- The milestone factors are precisely the moments of independent SI phases.
This auxiliary product space is a comparison law, not the law of actual
protocol holding times. -/
private theorem opinion_mgf_product_le {n : ℕ} (hn : 2 ≤ n) :
    (∏ i : Fin (n - 1),
      opinionRate n i * Real.exp (1 / (n : ℝ)) /
        (1 - (1 - opinionRate n i) * Real.exp (1 / (n : ℝ)))) ≤
      Real.exp 3 * (n : ℝ) := by
  let p : Fin (n - 1) → unitInterval := fun i =>
    ⟨opinionRate n i,
      (opinionRate_bounds hn i).1.le, (opinionRate_bounds hn i).2.1⟩
  let μ : Measure (Fin (n - 1) → ℕ) :=
    Measure.pi (fun i => ProbabilityTheory.geometricMeasure (p i))
  let G : Fin (n - 1) → (Fin (n - 1) → ℕ) → ℕ :=
    fun i ω => ω i
  have hG : ∀ i, Measurable (G i) := fun i => measurable_pi_apply i
  have hIndep : iIndepFun G μ := by
    exact iIndepFun_pi
      (μ := fun i => ProbabilityTheory.geometricMeasure (p i))
      (X := fun (_ : Fin (n - 1)) (k : ℕ) => k)
      (fun _ => measurable_id.aemeasurable)
  have hLaw : ∀ i, Measure.map (G i) μ =
      ProbabilityTheory.geometricMeasure (p i) :=
    fun i => (measurePreserving_eval
      (fun i => ProbabilityTheory.geometricMeasure (p i)) i).map_eq
  have hScalar := ScalarTails.epidemic_geometric_exp_moment
    (μ := μ) hn G p hG hIndep hLaw (fun _ => rfl)
  have hmoment :
      (∫ ω : Fin (n - 1) → ℕ,
        Real.exp ((∑ i : Fin (n - 1), ((ω i : ℝ) + 1)) / (n : ℝ)) ∂μ) =
        ∏ i : Fin (n - 1),
          opinionRate n i * Real.exp (1 / (n : ℝ)) /
            (1 - (1 - opinionRate n i) * Real.exp (1 / (n : ℝ))) := by
    calc
      _ = ∫ ω : Fin (n - 1) → ℕ,
          ∏ i : Fin (n - 1), Real.exp ((1 / (n : ℝ)) * ((ω i : ℝ) + 1)) ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        dsimp only
        rw [← Real.exp_sum, ← Finset.mul_sum]
        congr 1
        ring
      _ = ∏ i : Fin (n - 1),
          ∫ k : ℕ, Real.exp ((1 / (n : ℝ)) * ((k : ℝ) + 1))
            ∂ProbabilityTheory.geometricMeasure (p i) :=
        integral_fintype_prod_eq_prod
          (fun (_ : Fin (n - 1)) (k : ℕ) =>
            Real.exp ((1 / (n : ℝ)) * ((k : ℝ) + 1)))
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        simpa only [p, geometricMeasure', div_eq_mul_inv,
          mul_comm, mul_left_comm, mul_assoc] using
          shifted_geometric_exp_integral_geometricMeasure
            (opinionRate_bounds hn i).1
            (opinionRate_bounds hn i).2.1
            (opinionRate_converges hn i)
  rw [← hmoment]
  exact hScalar.2

/-- Completing the carrier milestones supplies the cleanup entry surface. -/
private theorem opinion_post_imp_signsDone
    (out : Output) (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hPost : (opinionMilestones (L := L) (K := K) out n hn).Post c) :
    Phase9OutputCleanup.Phase9SignsDone out n c := by
  classical
  have hi := hPost ⟨n - 2, by change n - 2 < n - 1; omega⟩
  change OpinionSpreadPre out n c ∧ n - 2 + 2 ≤ opinionCount out c at hi
  have hcount : Multiset.countP
      (fun a : AgentState L K => opinionCarrier out a.opinions) c = c.card := by
    apply le_antisymm (Multiset.countP_le_card _ _)
    change c.card ≤ opinionCount out c
    rw [hi.1.1]
    omega
  have hall := Multiset.countP_eq_card.mp hcount
  refine ⟨hi.1.1, ?_⟩
  intro a ha
  have hp := hi.1.2.1 a ha
  have hb := hall a ha
  cases out with
  | A => exact ⟨hp.1, hb, hp.2⟩
  | B => exact ⟨hp.1, hb, hp.2⟩
  | T => exact (hb : False).elim

/-- State-independent sharp SI bound from any seeded compatible Phase-9 state.
Neutral bits do not affect the carrier predicate or its two-orientation rate. -/
theorem opinion_kernel_sharp_tail
    {n : ℕ} (hn : 2 ≤ n) (out : Output)
    (c : Config (AgentState L K)) (hc : OpinionSpreadPre out n c) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {d | ¬ Phase9OutputCleanup.Phase9SignsDone out n d} ≤
      ENNReal.ofReal
        (Real.exp (-(t : ℝ) / (n : ℝ)) * (Real.exp 3 * (n : ℝ))) := by
  let mp := opinionMilestones (L := L) (K := K) out n hn
  have hpos : (0 : ℝ) < 1 / (n : ℝ) :=
    one_div_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  have hvalid : ∀ i, (1 - mp.p i) * Real.exp (1 / (n : ℝ)) < 1 :=
    fun i => opinionRate_converges hn i
  have htail := mp.milestone_tail_bound_via_mgf_on_partial c hc hpos hvalid t
  have hprod : (∏ i : Fin mp.k, mp.mgfFactor (1 / (n : ℝ)) i) ≤
      Real.exp 3 * (n : ℝ) := opinion_mgf_product_le hn
  have hsub : {d : Config (AgentState L K) |
      ¬ Phase9OutputCleanup.Phase9SignsDone out n d} ⊆ {d | ¬ mp.Post d} := by
    intro d hbad hpost
    exact hbad (opinion_post_imp_signsDone out n hn d hpost)
  refine (measure_mono hsub).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  have heq : -(1 / (n : ℝ)) * (t : ℝ) = -(t : ℝ) / (n : ℝ) := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le

/-- A four-unit logarithmic window gives the unconditional local charge
`exp(3) n^(-3)` for the majority-bit spread in Lemma 14 item 2. -/
theorem opinion_kernel_logWindow_tail
    {n : ℕ} (hn : 2 ≤ n) (out : Output)
    (c : Config (AgentState L K)) (hc : OpinionSpreadPre out n c) :
    ((NonuniformMajority L K).transitionKernel ^ TimeTheorem.logWindow n 4) c
        {d | ¬ Phase9OutputCleanup.Phase9SignsDone out n d} ≤
      ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (-3 : ℝ)) := by
  have htail := opinion_kernel_sharp_tail hn out c hc (TimeTheorem.logWindow n 4)
  have hb := ThresholdEpidemic.epidemic_logWindow_bound (n := n) (by omega) 4
  norm_num only [Nat.cast_ofNat, show (1 : ℝ) - 4 = -3 by norm_num] at hb
  exact htail.trans (ENNReal.ofReal_le_ofReal hb)

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads
end

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal NNReal MeasureTheory ProbabilityTheory
namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads
open TimeTheorem PairLog

private theorem seeded_partial_endpoint_kernel {L K : ℕ} (s t : ℕ) :
    (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s (s + t)).map
        (fun x : Finset.Iic (s + t) → Cfg L K =>
          x ⟨s + t, Finset.mem_Iic.mpr le_rfl⟩) =
      (((NonuniformMajority L K).transitionKernel ^ t).comap
        (fun x : Finset.Iic s → Cfg L K =>
          x ⟨s, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _)) := by
  induction t with
  | zero =>
      simp only [Nat.add_zero]
      ext x A hA
      rw [Kernel.map_apply _ (measurable_pi_apply _) x,
        Kernel.partialTraj_self, Kernel.id_apply,
        Measure.map_dirac' (measurable_pi_apply _) x,
        Kernel.comap_apply, pow_zero]
      change (Measure.dirac (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩)) A =
        (Kernel.id (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩)) A
      rw [Kernel.id_apply]
  | succ t ih =>
      let P : Kernel (Cfg L K) (Cfg L K) :=
        (NonuniformMajority L K).transitionKernel
      let coordStart : (Finset.Iic s → Cfg L K) → Cfg L K :=
        fun x => x ⟨s, Finset.mem_Iic.mpr le_rfl⟩
      let coordNow : (Finset.Iic (s + t) → Cfg L K) → Cfg L K :=
        fun x => x ⟨s + t, Finset.mem_Iic.mpr le_rfl⟩
      let coordNext : (Finset.Iic (s + t + 1) → Cfg L K) → Cfg L K :=
        fun x => x ⟨s + t + 1, Finset.mem_Iic.mpr le_rfl⟩
      change (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
          s (s + t + 1)).map coordNext =
        ((P ^ (t + 1)).comap coordStart (measurable_pi_apply _))
      calc
        (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
            s (s + t + 1)).map coordNext =
            ((Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                (s + t) (s + t + 1) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t))).map coordNext := by
          rw [Kernel.partialTraj_succ_eq_comp (Nat.le_add_right s t)]
        _ = ((Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                (s + t) (s + t + 1)).map coordNext) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t) := by rw [Kernel.map_comp]
        _ = ProtocolTraceLaw.kfamily (L := L) (K := K) (s + t) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t) := by rw [Kernel.map_partialTraj_succ_self]
        _ = (P.comap coordNow (measurable_pi_apply _)) ∘ₖ
              Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
                s (s + t) := rfl
        _ = P ∘ₖ ((Kernel.partialTraj
              (ProtocolTraceLaw.kfamily (L := L) (K := K)) s (s + t)).map
                coordNow) := by
          rw [← Kernel.comp_map (Kernel.partialTraj
            (ProtocolTraceLaw.kfamily (L := L) (K := K)) s (s + t)) P
            (measurable_pi_apply _)]
        _ = P ∘ₖ ((P ^ t).comap coordStart (measurable_pi_apply _)) := by
          simpa only [P, coordStart, coordNow] using
            congrArg (fun η => P ∘ₖ η) ih
        _ = (P ^ (t + 1)).comap coordStart (measurable_pi_apply _) := by
          ext x A hA
          rw [Kernel.comap_apply,
            Kernel.pow_succ_apply_eq_lintegral P t (coordStart x) hA,
            Kernel.comp_apply' _ _ _ hA, Kernel.comap_apply]

private theorem seeded_endpoint_law {L K : ℕ} (s t : ℕ)
    (x : Finset.Iic s → Cfg L K) :
    Measure.map (fun tr : ℕ → Cfg L K => tr (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x) =
      ((NonuniformMajority L K).transitionKernel ^ t)
        (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) := by
  let coord : (Finset.Iic (s + t) → Cfg L K) → Cfg L K :=
    fun y => y ⟨s + t, Finset.mem_Iic.mpr le_rfl⟩
  calc
    Measure.map (fun tr : ℕ → Cfg L K => tr (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x) =
      Measure.map (coord ∘ frestrictLe (π := fun _ : ℕ => Cfg L K) (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x) := rfl
    _ = Measure.map coord (Measure.map (frestrictLe (π := fun _ : ℕ => Cfg L K) (s + t))
        (Kernel.traj (ProtocolTraceLaw.kfamily (L := L) (K := K)) s x)) := by
      rw [← Measure.map_map (measurable_pi_apply _)
        (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) (s + t))]
    _ = Measure.map coord
        (Kernel.partialTraj (ProtocolTraceLaw.kfamily (L := L) (K := K))
          s (s + t) x) := by rw [Kernel.traj_map_frestrictLe_apply]
    _ = ((NonuniformMajority L K).transitionKernel ^ t)
        (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) := by
      rw [← Kernel.map_apply _ (measurable_pi_apply _) x,
        seeded_partial_endpoint_kernel, Kernel.comap_apply]

private theorem prefix_event_future_bound {L K : ℕ}
    (init : Cfg L K) (s t : ℕ)
    (A : Set (Finset.Iic s → Cfg L K)) (hA : MeasurableSet A)
    (B : Set (Cfg L K)) (hB : MeasurableSet B) (ε : ℝ≥0∞)
    (hbound : ∀ x ∈ A,
      ((NonuniformMajority L K).transitionKernel ^ t)
        (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) B ≤ ε) :
    ProtocolTraceLaw.μ init
      ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A ∩
        (fun tr => tr (s + t)) ⁻¹' B) ≤
      ε * ProtocolTraceLaw.μ init
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A) := by
  classical
  let κ := ProtocolTraceLaw.kfamily (L := L) (K := K)
  let Γ := Kernel.traj κ s
  let ν : Measure (Finset.Iic s → Cfg L K) :=
    Kernel.partialTraj κ 0 s (fun _ => init)
  let E : Set (ℕ → Cfg L K) :=
    (frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' A
  let F : Set (ℕ → Cfg L K) := (fun tr => tr (s + t)) ⁻¹' B
  have hE : MeasurableSet E := hA.preimage
    (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) s)
  have hF : MeasurableSet F := hB.preimage (measurable_pi_apply _)
  have hsplit (D : Set (ℕ → Cfg L K)) (hD : MeasurableSet D) :
      ProtocolTraceLaw.μ init D = ∫⁻ x, Γ x D ∂ν := by
    change Kernel.traj κ 0 (fun _ => init) D =
      ∫⁻ x, Kernel.traj κ s x D ∂(Kernel.partialTraj κ 0 s (fun _ => init))
    rw [← Kernel.traj_comp_partialTraj (Nat.zero_le s),
      Kernel.comp_apply' _ _ _ hD]
  have hlocal (x : Finset.Iic s → Cfg L K) :
      Γ x (E ∩ F) ≤ ε * Γ x E := by
    have hfreeze : ∀ᵐ tr ∂Γ x,
        frestrictLe (π := fun _ : ℕ => Cfg L K) s tr = x := by
      rw [ae_iff]
      change (Kernel.traj κ s x)
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) s) ⁻¹' ({x}ᶜ)) = 0
      rw [← Measure.map_apply
        (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) s)
        (measurableSet_singleton x).compl,
        Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
      simp
    by_cases hx : x ∈ A
    · have hwhole : Γ x E = 1 := by
        calc
          Γ x E = Γ x Set.univ := by
            apply measure_congr
            filter_upwards [hfreeze] with tr htr
            show (tr ∈ E) = (tr ∈ Set.univ)
            simp only [E, Set.mem_preimage, htr, hx, Set.mem_univ]
          _ = 1 := measure_univ
      have hinter : Γ x (E ∩ F) = Γ x F := by
        apply measure_congr
        filter_upwards [hfreeze] with tr htr
        show (tr ∈ E ∩ F) = (tr ∈ F)
        simp only [Set.mem_inter_iff, E, Set.mem_preimage, htr, hx, true_and]
      have hfuture : Γ x F =
          ((NonuniformMajority L K).transitionKernel ^ t)
            (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) B := by
        calc
          Γ x F =
              Measure.map (fun tr : ℕ → Cfg L K => tr (s + t))
                (Kernel.traj κ s x) B := by
            rw [Measure.map_apply
              (measurable_pi_apply (s + t) : Measurable fun tr : ℕ → Cfg L K => tr (s + t)) hB]
          _ = ((NonuniformMajority L K).transitionKernel ^ t)
                (x ⟨s, Finset.mem_Iic.mpr le_rfl⟩) B := by
            rw [seeded_endpoint_law]
      rw [hwhole, mul_one, hinter, hfuture]
      exact hbound x hx
    · have hzero : Γ x E = 0 := by
        calc
          Γ x E = Γ x ∅ := by
            apply measure_congr
            filter_upwards [hfreeze] with tr htr
            show (tr ∈ E) = (tr ∈ (∅ : Set _))
            simp only [E, Set.mem_preimage, htr, hx, Set.mem_empty_iff_false]
          _ = 0 := measure_empty
      rw [hzero, mul_zero]
      exact (measure_mono Set.inter_subset_left).trans_eq hzero
  change ProtocolTraceLaw.μ init (E ∩ F) ≤ ε * ProtocolTraceLaw.μ init E
  calc
    ProtocolTraceLaw.μ init (E ∩ F) = ∫⁻ x, Γ x (E ∩ F) ∂ν :=
      hsplit (E ∩ F) (hE.inter hF)
    _ ≤ ∫⁻ x, ε * Γ x E ∂ν := lintegral_mono hlocal
    _ = ε * ∫⁻ x, Γ x E ∂ν :=
      lintegral_const_mul ε (Kernel.measurable_coe Γ hE)
    _ = ε * ProtocolTraceLaw.μ init E := by rw [← hsplit E hE]


/-- A state-independent tail after a fixed offset from the genuine first seed.
The first-seed fibres retain their probability mass, so no factor is charged
for the number of possible starting times. -/
theorem seeded_window_tail {L K : ℕ}
    (init : Cfg L K) (q offset duration : ℕ)
    (Pre Post : Cfg L K → Prop) (ε : ℝ≥0∞)
    (hbound : ∀ c, Pre c →
      ((NonuniformMajority L K).transitionKernel ^ duration) c
        {d | ¬ Post d} ≤ ε) :
    law init {ω | ∃ s : ℕ, firstPhaseSeed init q s ω ∧
      Pre (trace init ω (s + offset)) ∧
      ¬ Post (trace init ω (s + offset + duration))} ≤ ε := by
  classical
  let Bad : Set (Ω L K) := {ω | ∃ s : ℕ, firstPhaseSeed init q s ω ∧
    Pre (trace init ω (s + offset)) ∧
    ¬ Post (trace init ω (s + offset + duration))}
  apply PhaseThreeClockProducer.splice_of_local (law init)
    (PhaseThreeClockProducer.seedTime init q) Bad ε
    (fun s => (pairLogFiltration L K).le s _
      (PhaseThreeClockProducer.seedTime_pastTime init q s))
  · rintro ω ⟨s, hs, _⟩
    rw [(PhaseThreeClockProducer.seedTime_eq_iff init q ω s).mpr hs]
    exact WithTop.coe_ne_top
  · intro s
    let A : Set (Finset.Iic (s + offset) → Cfg L K) :=
      {x | (∃ a ∈ x ⟨s, Finset.mem_Iic.mpr (Nat.le_add_right s offset)⟩,
          a.phase.val = q) ∧
        (∀ u : Finset.Iic (s + offset), u.val < s →
          ∀ a ∈ x u, a.phase.val < q) ∧
        Pre (x ⟨s + offset, Finset.mem_Iic.mpr le_rfl⟩)}
    let B : Set (Cfg L K) := {d | ¬ Post d}
    have hA : MeasurableSet A := (Set.to_countable _).measurableSet
    have hB : MeasurableSet B := (Set.to_countable _).measurableSet
    have hpull : (trace init) ⁻¹'
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) (s + offset)) ⁻¹' A) =
        {ω | firstPhaseSeed init q s ω ∧ Pre (trace init ω (s + offset))} := by
      ext ω
      constructor
      · rintro ⟨hs, hpast, hpre⟩
        refine ⟨⟨hs, ?_⟩, hpre⟩
        intro u hu a ha
        exact hpast ⟨u, Finset.mem_Iic.mpr (by omega)⟩ hu a ha
      · rintro ⟨hs, hpre⟩
        exact ⟨hs.1, fun u hu a ha => hs.2 u.val hu a ha, hpre⟩
    have hE : MeasurableSet
        ((frestrictLe (π := fun _ : ℕ => Cfg L K) (s + offset)) ⁻¹' A) :=
      hA.preimage (measurable_frestrictLe (X := fun _ : ℕ => Cfg L K) _)
    have hF : MeasurableSet
        ((fun tr : ℕ → Cfg L K => tr (s + offset + duration)) ⁻¹' B) :=
      hB.preimage (measurable_pi_apply _)
    have h := prefix_event_future_bound init (s + offset) duration A hA B hB ε
      (fun x hx => hbound _ hx.2.2)
    rw [← PairLog.pair_log_projects init,
      Measure.map_apply (measurable_trace init) (hE.inter hF),
      Measure.map_apply (measurable_trace init) hE,
      Set.preimage_inter, hpull] at h
    have hsub : Bad ∩
        {ω | PhaseThreeClockProducer.seedTime init q ω = (s : WithTop ℕ)} ⊆
        {ω | firstPhaseSeed init q s ω ∧ Pre (trace init ω (s + offset))} ∩
          (trace init) ⁻¹'
            ((fun tr : ℕ → Cfg L K => tr (s + offset + duration)) ⁻¹' B) := by
      rintro ω ⟨⟨r, hr, hpre, hbad⟩, hs⟩
      have hfirst := (PhaseThreeClockProducer.seedTime_eq_iff init q ω s).mp hs
      have hrs := PhaseThreeClockProducer.firstPhaseSeed_unique init q ω hr hfirst
      subst r
      exact ⟨⟨hfirst, hpre⟩, hbad⟩
    refine (measure_mono hsub).trans (h.trans ?_)
    apply mul_le_mul_left'
    apply measure_mono
    intro ω hω
    exact (PhaseThreeClockProducer.seedTime_eq_iff init q ω s).mpr hω.1

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads

end
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads
open TimeTheorem PairLog StageEventSpec
open LateTimerProtectionOriginalLaw Phase9OutputCleanup LateLemmaFourteenCleanup

variable {n : ℕ}

/-- Absence of the bit opposite to the chosen verdict, with no constraint
on the neutral bit. Only the signed branches are used in Lemma 14. -/
def NoOppositeBit {L K : ℕ} (out : Output) (c : Cfg L K) : Prop :=
  ∀ a ∈ c, opinionCompatible out a.opinions

/-- The majority-bit spread fails after its finite first-nine start despite
entering the homogeneous, compatible, seeded state. -/
def majorityBitSpreadFailure (init : InputCfg n) (out : Output) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, firstPhaseSeed init 9 s ω ∧
    OpinionSpreadPre out n (trace init ω (s + logWindow n 4)) ∧
    ¬ Phase9SignsDone out n (trace init ω (s + logWindow n 4 + logWindow n 4))}

/-- The majority-bit failure event is measurable independently of whether
the Lemma 14 no-minority invariant holds on the observed trace. -/
theorem measurableSet_majorityBitSpreadFailure (init : InputCfg n) (out : Output) :
    MeasurableSet (majorityBitSpreadFailure init out) := by
  have heq : majorityBitSpreadFailure init out = ⋃ s : ℕ,
      {ω | firstPhaseSeed init 9 s ω} ∩
        {ω | OpinionSpreadPre out n (trace init ω (s + logWindow n 4))} ∩
        {ω | ¬ Phase9SignsDone out n
          (trace init ω (s + logWindow n 4 + logWindow n 4))} := by
    ext ω
    simp only [majorityBitSpreadFailure, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨s, hs, hp, hb⟩
      exact ⟨s, ⟨hs, hp⟩, hb⟩
    · rintro ⟨s, ⟨hs, hp⟩, hb⟩
      exact ⟨s, hs, hp, hb⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  have hm (t : ℕ) : Measurable (fun ω : InputLog n => trace init ω t) :=
    (measurable_pi_apply t).comp (measurable_trace init)
  exact ((((pairLogFiltration _ _).le s) _
    (firstPhaseSeed_measurableSet init 9 s)).inter
    ((Set.to_countable {c : InputCfg n | OpinionSpreadPre out n c}).measurableSet.preimage
      (hm _))).inter
    ((Set.to_countable {c : InputCfg n | ¬ Phase9SignsDone out n c}).measurableSet.preimage
      (hm _))

/-- Each spread contributes its own unconditional sharp epidemic charge. -/
theorem law_majorityBitSpreadFailure (init : InputCfg n) (out : Output)
    (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (majorityBitSpreadFailure init out) ≤
      ENNReal.ofReal (Real.exp 3 * Real.rpow (n : ℝ) (-3 : ℝ)) := by
  have hnlarge := (time_population_bounds hinput.1).2
  have hn : 2 ≤ n := by omega
  apply seeded_window_tail init 9 (logWindow n 4) (logWindow n 4)
    (OpinionSpreadPre out n) (Phase9SignsDone out n)
  intro c hc
  exact opinion_kernel_logWindow_tail hn out c hc

/-- The Lemma 14 invariant observations and the first spread supply the seeded homogeneous
state used by the second spread. -/
theorem opinionSpreadPre_of_observed
    (init : InputCfg n) (out : Output) (ω : InputLog n) (firstNine : ℕ)
    (hcard : init.card = n)
    (hfirst : phaseSeedTime init 9 ω = (firstNine : WithTop ℕ))
    (hentry : ∀ a ∈ trace init ω firstNine, a.phase.val ≤ 9)
    (hceiling : ∀ a ∈ trace init ω (firstNine + logWindow n 4), a.phase.val ≤ 9)
    (hnone : NoOppositeBit out (trace init ω (firstNine + logWindow n 4)))
    (hseed : ∃ a ∈ trace init ω (firstNine + logWindow n 4),
      opinionCarrier out a.opinions)
    (hgood : ω ∉ phaseNineSpreadFailure init) :
    OpinionSpreadPre out n (trace init ω (firstNine + logWindow n 4)) := by
  have hall := phaseNineExactly_of_time_and_ceiling init ω firstNine hfirst hentry
    hgood hceiling
  refine ⟨?_, fun a ha => ⟨hall a ha, hnone a ha⟩, ?_⟩
  · have hc := Protocol.reachable_card_eq
      (trace_reachable init ω (s := 0) (t := firstNine + logWindow n 4) (by omega))
    simpa only [trace_zero, hcard] using hc
  · exact Multiset.countP_pos.mpr hseed

/-- At the end of the second spread all agents have the selected sign and
no opposite bit, in Phase 9. -/
theorem lemma_fourteen_signs_done
    (init : InputCfg n) (out : Output) (ω : InputLog n) (firstNine : ℕ)
    (hcard : init.card = n)
    (hfirst : phaseSeedTime init 9 ω = (firstNine : WithTop ℕ))
    (hentry : ∀ a ∈ trace init ω firstNine, a.phase.val ≤ 9)
    (hceiling : ∀ a ∈ trace init ω (firstNine + logWindow n 4), a.phase.val ≤ 9)
    (hnone : NoOppositeBit out (trace init ω (firstNine + logWindow n 4)))
    (hseed : ∃ a ∈ trace init ω (firstNine + logWindow n 4),
      opinionCarrier out a.opinions)
    (hthreshold : ω ∉ phaseNineSpreadFailure init)
    (hbit : ω ∉ majorityBitSpreadFailure init out) :
    Phase9SignsDone out n
      (trace init ω (firstNine + logWindow n 4 + logWindow n 4)) := by
  have hpre := opinionSpreadPre_of_observed init out ω firstNine hcard hfirst
    hentry hceiling hnone hseed hthreshold
  by_contra hbad
  exact hbit ⟨firstNine, firstPhaseNineSeed_of_time_and_ceiling init ω firstNine
    hfirst hentry, hpre, hbad⟩

/-- The two Phase-9 spreads reach the existing cleanup stopping time within
two four-unit windows, under the Lemma 14 no-minority invariant on the observed trace. -/
theorem lemma_fourteen_cleanup_start_le
    (init : InputCfg n) (out : Output) (ω : InputLog n) (firstNine : ℕ)
    (hcard : init.card = n)
    (hfirst : phaseSeedTime init 9 ω = (firstNine : WithTop ℕ))
    (hentry : ∀ a ∈ trace init ω firstNine, a.phase.val ≤ 9)
    (hceiling : ∀ a ∈ trace init ω (firstNine + logWindow n 4), a.phase.val ≤ 9)
    (hnone : NoOppositeBit out (trace init ω (firstNine + logWindow n 4)))
    (hseed : ∃ a ∈ trace init ω (firstNine + logWindow n 4),
      opinionCarrier out a.opinions)
    (hthreshold : ω ∉ phaseNineSpreadFailure init)
    (hbit : ω ∉ majorityBitSpreadFailure init out) :
    cleanupStart init out n ω ≤
      ((firstNine + logWindow n 4 + logWindow n 4 : ℕ) : WithTop ℕ) := by
  apply (TraceDrain.exitTime_le_iff init (Phase9SignsDone out n) ω _).2
  exact ⟨_, le_rfl, lemma_fourteen_signs_done init out ω firstNine hcard hfirst
    hentry hceiling hnone hseed hthreshold hbit⟩

end Ripple.PopulationProtocol.ExactMajority.LateLemmaFourteenSpreads
end
