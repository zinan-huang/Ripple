-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSharpPotentialTransport.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSharpInitialPotential
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingShallowTransport
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFuel
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiDrift

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority
namespace LateSharpPotentialTransport

open TimeTheorem StageEventSpec PairLog
open LateStrengthening LateF6Acceptance LateF6OriginalLaw
open LateMixedFuelLedger LateMixedFuel
open LateSamplingStrongSeedReceipt
open AveragingMixedLedgers AveragingIntegerPotential
open LateSharpInitialPotential
open P3DeterministicAlgebra

variable {L K n : ℕ}

private theorem phiMass_pair'
    (ell : ℕ) (x y : AgentState L K) :
    Phase6PhiPotential.phiMass ell ({x, y} : Multiset (AgentState L K)) =
      Phase6PhiPotential.agentPhiW ell x +
        Phase6PhiPotential.agentPhiW ell y :=
  Phase6PhiDrift.phiMass_pair ell x y

private theorem agentPhiW_eq_of_role_bias
    (ell : ℕ) (before after : AgentState L K)
    (hrole : after.role = before.role)
    (hbias : after.bias = before.bias) :
    Phase6PhiPotential.agentPhiW ell after =
      Phase6PhiPotential.agentPhiW ell before := by
  unfold Phase6PhiPotential.agentPhiW
  rw [hrole, hbias]

private theorem agentPhiW_cast_of_main
    (ell : ℕ) (a : AgentState L K) (hmain : a.role = .main) :
    (Phase6PhiPotential.agentPhiW ell a : ℚ) = agentPhiAboveQ ell a := by
  have hnat :
      Phase6PhiPotential.agentPhiW ell a = activeAgentPhiNat ell a := by
    unfold Phase6PhiPotential.agentPhiW
      Phase6PhiPotential.biasPhiW activeAgentPhiNat
    rw [if_pos hmain]
    cases a.bias <;> rfl
  calc
    (Phase6PhiPotential.agentPhiW ell a : ℚ) =
        (activeAgentPhiNat ell a : ℚ) := by rw [hnat]
    _ = agentPhiAboveQ ell a := activeAgentPhiNat_cast ell a

/-- A genuine Phase-3 dispatch cannot increase the role-filtered base-4 pair
potential. If both agents are Mains this is the landed augmented-potential
inequality; otherwise both roles and both biases are preserved. -/
theorem phaseThree_agentPhiW_pair_le
    (ell : ℕ) (s t : AgentState L 256)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    Phase6PhiPotential.agentPhiW ell (Phase3Transition L 256 s t).1 +
        Phase6PhiPotential.agentPhiW ell (Phase3Transition L 256 s t).2 ≤
      Phase6PhiPotential.agentPhiW ell s +
        Phase6PhiPotential.agentPhiW ell t := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · have hroles := Phase5To6FuelProducer.Phase3Transition_roles s t hs ht
    have houtLeft : (Phase3Transition L 256 s t).1.role = .main :=
      hroles.1.trans hmain.1
    have houtRight : (Phase3Transition L 256 s t).2.role = .main :=
      hroles.2.trans hmain.2
    have hphase := Phase3Transition_phase_nondec L 256 s t
    have hnLeft : ¬ (Phase3Transition L 256 s t).1.phase.val < 3 := by omega
    have hnRight : ¬ (Phase3Transition L 256 s t).2.phase.val < 3 := by omega
    have hnSourceLeft : ¬ s.phase.val < 3 := by omega
    have hnSourceRight : ¬ t.phase.val < 3 := by omega
    have hrat :
        (Phase6PhiPotential.agentPhiW ell
            (Phase3Transition L 256 s t).1 : ℚ) +
            (Phase6PhiPotential.agentPhiW ell
              (Phase3Transition L 256 s t).2 : ℚ) ≤
          (Phase6PhiPotential.agentPhiW ell s : ℚ) +
            (Phase6PhiPotential.agentPhiW ell t : ℚ) := by
      rw [agentPhiW_cast_of_main ell _ houtLeft,
        agentPhiW_cast_of_main ell _ houtRight,
        agentPhiW_cast_of_main ell s hmain.1,
        agentPhiW_cast_of_main ell t hmain.2]
      simpa only [augmentedAgentPhi, if_neg hnLeft, if_neg hnRight,
        if_neg hnSourceLeft, if_neg hnSourceRight] using
        phaseThree_augmentedPhi_pair_le ell s t hs ht
    exact_mod_cast hrat
  · have hroles := Phase5To6FuelProducer.Phase3Transition_roles s t hs ht
    have hbias :=
      Phase5To6FuelProducer.Phase3Transition_biases_of_not_both_main
        s t hs ht hmain
    unfold Phase6PhiPotential.agentPhiW
    rw [hroles.1, hroles.2, hbias.1, hbias.2]

/-- Wrapper form for an actual pair whose two input phases are three. -/
theorem transition_agentPhiW_pair_le_of_three
    (ell : ℕ) (s t : AgentState L 256)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) :
    Phase6PhiPotential.agentPhiW ell (Transition L 256 s t).1 +
        Phase6PhiPotential.agentPhiW ell (Transition L 256 s t).2 ≤
      Phase6PhiPotential.agentPhiW ell s +
        Phase6PhiPotential.agentPhiW ell t := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hactual : Transition L 256 s t =
      (finishPhase10Entry L 256 s (Phase3Transition L 256 s t).1,
       finishPhase10Entry L 256 t (Phase3Transition L 256 s t).2) := by
    unfold Transition
    rw [hepi]
    simp only [hsp]
  have hpair := phaseThree_agentPhiW_pair_le ell s t hs ht
  rw [hactual]
  simpa only [Phase6PhiPotential.agentPhiW,
    finishPhase10Entry_role, finishPhase10Entry_bias] using hpair

private theorem agentPhiW_left_eq_of_freeze
    (ell : ℕ) (s t : AgentState L 256)
    (hs : Window s) (ht : Window t)
    (hmax : 4 ≤ max s.phase.val t.phase.val) :
    Phase6PhiPotential.agentPhiW ell (Transition L 256 s t).1 =
      Phase6PhiPotential.agentPhiW ell s := by
  have hfields := transition_freeze_fields s t hs ht hmax
  exact agentPhiW_eq_of_role_bias ell s _ hfields.1 hfields.2.1

private theorem agentPhiW_right_eq_of_freeze
    (ell : ℕ) (s t : AgentState L 256)
    (hs : Window s) (ht : Window t)
    (hmax : 4 ≤ max s.phase.val t.phase.val) :
    Phase6PhiPotential.agentPhiW ell (Transition L 256 s t).2 =
      Phase6PhiPotential.agentPhiW ell t := by
  have hfields := transition_freeze_fields s t hs ht hmax
  exact agentPhiW_eq_of_role_bias ell t _ hfields.2.2.1 hfields.2.2.2

/-- Pair nonincrease throughout the actual mixed Phase-3/4/5 window. -/
theorem transition_agentPhiW_pair_le_of_window
    (ell : ℕ) (s t : AgentState L 256)
    (hs : Window s) (ht : Window t) :
    Phase6PhiPotential.agentPhiW ell (Transition L 256 s t).1 +
        Phase6PhiPotential.agentPhiW ell (Transition L 256 s t).2 ≤
      Phase6PhiPotential.agentPhiW ell s +
        Phase6PhiPotential.agentPhiW ell t := by
  by_cases hfreeze : 4 ≤ max s.phase.val t.phase.val
  · rw [agentPhiW_left_eq_of_freeze ell s t hs ht hfreeze,
      agentPhiW_right_eq_of_freeze ell s t hs ht hfreeze]
  · obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨ht1, ht2⟩ := ht
    have hsphase : s.phase.val = 3 := by omega
    have htphase : t.phase.val = 3 := by omega
    exact transition_agentPhiW_pair_le_of_three ell s t hsphase htphase

/-- Configuration lift for one chosen pair in the Phase-3/4/5 window. -/
theorem phiMass_stepOrSelf_le_of_window
    (ell : ℕ) (c : Cfg L 256) (s t : AgentState L 256)
    (hwindow : ∀ a ∈ c, Window a) :
    Phase6PhiPotential.phiMass ell
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      Phase6PhiPotential.phiMass ell c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
          c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hpair := transition_agentPhiW_pair_le_of_window
      ell s t (hwindow s hs) (hwindow t ht)
    have hsplit : c = c - {s, t} +
        ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, Phase6PhiDrift.phiMass_add, phiMass_pair']
    conv_rhs => rw [hsplit]
    rw [Phase6PhiDrift.phiMass_add, phiMass_pair']
    exact Nat.add_le_add_left hpair _
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

private theorem phiMass_draw_le_of_window
    (ell : ℕ) (c : Cfg L 256) (d : Draw L 256)
    (hwindow : ∀ a ∈ c, Window a) :
    Phase6PhiPotential.phiMass ell (applyDraw c d) ≤
      Phase6PhiPotential.phiMass ell c := by
  cases d with
  | none => exact le_rfl
  | some pair =>
      exact phiMass_stepOrSelf_le_of_window
        ell c pair.1.1 pair.2.1 hwindow

/-- Trace transport through the Phase-3/4/5 segment. -/
theorem phiMass_trace_le_of_window
    (ell : ℕ) (init : Cfg L 256) (omega : Ω L 256)
    (s t : ℕ) (hst : s ≤ t)
    (hwindow : ∀ u, s ≤ u → u < t →
      ∀ a ∈ trace init omega u, Window a) :
    Phase6PhiPotential.phiMass ell (trace init omega t) ≤
      Phase6PhiPotential.phiMass ell (trace init omega s) := by
  revert hwindow
  induction t, hst using Nat.le_induction with
  | base =>
      intro _
      exact le_rfl
  | succ t hst ih =>
      intro hwindow
      have hprevious := ih (fun u hsu hut => hwindow u hsu (by omega))
      have hnext :
          Phase6PhiPotential.phiMass ell (trace init omega (t + 1)) ≤
            Phase6PhiPotential.phiMass ell (trace init omega t) := by
        rw [TimeTheorem.trace_succ]
        exact phiMass_draw_le_of_window ell (trace init omega t)
          (omega (t + 1)) (hwindow t hst (by omega))
      exact hnext.trans hprevious

/-- From the genuine first Phase-4 seed to any endpoint of the pre-six path. -/
theorem phiMass_seed_mono
    {init : InputCfg n} {omega : InputLog n}
    {allStart seed endpoint ell : ℕ}
    (hpath : Prefix init omega allStart seed endpoint) :
    Phase6PhiPotential.phiMass ell (trace init omega endpoint) ≤
      Phase6PhiPotential.phiMass ell (trace init omega seed) := by
  apply phiMass_trace_le_of_window ell init omega seed endpoint hpath.observed
  intro u hsu hut a ha
  exact hpath.window u
    (hpath.start_order.trans hsu) hut.le a ha

@[simp] private theorem agentPhiW_phaseSixEntry_eq
    (ell : ℕ) (a : AgentState L K) :
    Phase6PhiPotential.agentPhiW ell
        (phaseSixEntry (L := L) (K := K) a) =
      Phase6PhiPotential.agentPhiW ell a := by
  exact agentPhiW_eq_of_role_bias ell a _
    (phaseSixEntry_role a) (phaseSixEntry_bias a)

@[simp] private theorem agentPhiW_set_phase_eq
    (ell : ℕ) (a : AgentState L K) (p : Fin 11) :
    Phase6PhiPotential.agentPhiW ell {a with phase := p} =
      Phase6PhiPotential.agentPhiW ell a := by
  rfl

private theorem transition_agentPhiW_pair_le_of_five_five
    (ell : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    Phase6PhiPotential.agentPhiW ell (Transition L K s t).1 +
        Phase6PhiPotential.agentPhiW ell (Transition L K s t).2 ≤
      Phase6PhiPotential.agentPhiW ell s +
        Phase6PhiPotential.agentPhiW ell t := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  rw [agentPhiW_eq_of_role_bias ell s (Phase5Transition L K s t).1
      (Phase5Convergence.Phase5Transition_fst_role_eq s t hs)
      (Phase5Convergence.Phase5Transition_fst_bias_eq s t hs),
    agentPhiW_eq_of_role_bias ell t (Phase5Transition L K s t).2
      (Phase5Convergence.Phase5Transition_snd_role_eq s t ht)
      (Phase5Convergence.Phase5Transition_snd_bias_eq s t ht)]

private theorem transition_agentPhiW_pair_le_of_five_six
    (ell : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 6) :
    Phase6PhiPotential.agentPhiW ell (Transition L K s t).1 +
        Phase6PhiPotential.agentPhiW ell (Transition L K s t).2 ≤
      Phase6PhiPotential.agentPhiW ell s +
        Phase6PhiPotential.agentPhiW ell t := by
  rw [Transition_eq_Phase6Transition_of_five_six s t hs ht]
  have hpair := Phase6PhiDrift.Phase6Transition_phi_pair_le
    ell (phaseSixEntry (L := L) (K := K) s)
      {t with phase := ⟨6, by decide⟩}
      (by rw [phaseSixEntry_phase]) (by simp)
  simpa only [agentPhiW_phaseSixEntry_eq, agentPhiW_set_phase_eq] using hpair

private theorem transition_agentPhiW_pair_le_of_six_five
    (ell : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 5) :
    Phase6PhiPotential.agentPhiW ell (Transition L K s t).1 +
        Phase6PhiPotential.agentPhiW ell (Transition L K s t).2 ≤
      Phase6PhiPotential.agentPhiW ell s +
        Phase6PhiPotential.agentPhiW ell t := by
  rw [Transition_eq_Phase6Transition_of_six_five s t hs ht]
  have hpair := Phase6PhiDrift.Phase6Transition_phi_pair_le
    ell {s with phase := ⟨6, by decide⟩}
      (phaseSixEntry (L := L) (K := K) t)
      (by simp) (by rw [phaseSixEntry_phase])
  simpa only [agentPhiW_phaseSixEntry_eq, agentPhiW_set_phase_eq] using hpair

/-- Pair nonincrease in the complete mixed Phase-5/6 source window. -/
theorem transition_agentPhiW_pair_le_of_mixed_five_six
    (ell : ℕ) (s t : AgentState L K)
    (hs : s.phase.val = 5 ∨ s.phase.val = 6)
    (ht : t.phase.val = 5 ∨ t.phase.val = 6) :
    Phase6PhiPotential.agentPhiW ell (Transition L K s t).1 +
        Phase6PhiPotential.agentPhiW ell (Transition L K s t).2 ≤
      Phase6PhiPotential.agentPhiW ell s +
        Phase6PhiPotential.agentPhiW ell t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact transition_agentPhiW_pair_le_of_five_five ell s t hs ht
  · exact transition_agentPhiW_pair_le_of_five_six ell s t hs ht
  · exact transition_agentPhiW_pair_le_of_six_five ell s t hs ht
  · rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6 s t hs ht]
    exact Phase6PhiDrift.Phase6Transition_phi_pair_le
      ell s t (by omega) (by omega)

private theorem phiMass_stepOrSelf_le_of_mixed_five_six
    (ell population : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin population c)
    (s t : AgentState L K) :
    Phase6PhiPotential.phiMass ell
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      Phase6PhiPotential.phiMass ell c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hpair := transition_agentPhiW_pair_le_of_mixed_five_six
      ell s t (hwin.2 s hs) (hwin.2 t ht)
    have hsplit : c = c - {s, t} +
        ({s, t} : Multiset (AgentState L K)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ)]
    rw [hstep, Phase6PhiDrift.phiMass_add, phiMass_pair']
    conv_rhs => rw [hsplit]
    rw [Phase6PhiDrift.phiMass_add, phiMass_pair']
    exact Nat.add_le_add_left hpair _
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

private theorem phiMass_draw_le_of_mixed_five_six
    (ell population : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin population c) (d : Draw L K) :
    Phase6PhiPotential.phiMass ell (applyDraw c d) ≤
      Phase6PhiPotential.phiMass ell c := by
  cases d with
  | none => exact le_rfl
  | some pair =>
      exact phiMass_stepOrSelf_le_of_mixed_five_six
        ell population c hwin pair.1.1 pair.2.1

/-- Transport from sampling completion to the genuine first all-Phase-6 state. -/
theorem phiMass_mixed_trace_le
    (ell : ℕ) (init : InputCfg n) (omega : InputLog n)
    (completed homogeneous : ℕ) (hcompleted : completed ≤ homogeneous)
    (hwindow : ∀ u, completed ≤ u → u < homogeneous →
      MixedFiveSixWin n (trace init omega u)) :
    Phase6PhiPotential.phiMass ell (trace init omega homogeneous) ≤
      Phase6PhiPotential.phiMass ell (trace init omega completed) := by
  revert hwindow
  induction homogeneous, hcompleted using Nat.le_induction with
  | base =>
      intro _
      exact le_rfl
  | succ homogeneous hcompleted ih =>
      intro hwindow
      have hprevious := ih (fun u hcu huh => hwindow u hcu (by omega))
      have hnext :
          Phase6PhiPotential.phiMass ell
              (trace init omega (homogeneous + 1)) ≤
            Phase6PhiPotential.phiMass ell (trace init omega homogeneous) := by
        rw [TimeTheorem.trace_succ]
        exact phiMass_draw_le_of_mixed_five_six ell n
          (trace init omega homogeneous)
          (hwindow homogeneous hcompleted (by omega))
          (omega (homogeneous + 1))
      exact hnext.trans hprevious

/-- Complete seed-to-homogeneous transport. -/
theorem phiMass_homogeneous_le_seed
    {init : InputCfg n} {omega : InputLog n}
    {allStart seed completed homogeneous ell : ℕ}
    (hpath : Prefix init omega allStart seed completed)
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous) :
    Phase6PhiPotential.phiMass ell (trace init omega homogeneous) ≤
      Phase6PhiPotential.phiMass ell (trace init omega seed) := by
  exact (phiMass_mixed_trace_le ell init omega completed homogeneous
    hmixed.completion_le hmixed.source_window).trans
      (phiMass_seed_mono (ell := ell) hpath)

/-- Zero preservation transports the old-index cutoff. -/
theorem oldIndexCutoff_at_homogeneous
    {init : InputCfg n} {omega : InputLog n}
    {allStart seed completed homogeneous cutoff : ℕ}
    (hpath : Prefix init omega allStart seed completed)
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hcut : noIndexBelow cutoff (trace init omega seed)) :
    noIndexBelow cutoff (trace init omega homogeneous) := by
  have hseedZero :
      Phase6PhiPotential.phiMass cutoff (trace init omega seed) = 0 := by
    rw [LateSharpInitialPotential.phiMass_eq_shallowPotential]
    exact (noIndexBelow_iff_shallowPotential_eq_zero
      cutoff (trace init omega seed)).mp hcut
  have hmono := phiMass_homogeneous_le_seed
    (ell := cutoff) hpath hmixed
  have hfinalZero :
      Phase6PhiPotential.phiMass cutoff
        (trace init omega homogeneous) = 0 := by omega
  rw [noIndexBelow_iff_shallowPotential_eq_zero,
    ← LateSharpInitialPotential.phiMass_eq_shallowPotential]
  exact hfinalZero

/-- Sharp equation (46) at the actual homogeneous Phase-6 work start. -/
theorem homogeneous_largePotential_scaled_le_main
    {init : InputCfg n} {omega : InputLog n}
    {allStart seed completed homogeneous M ell : ℕ} {sigma : Sign}
    (hpath : Prefix init omega allStart seed completed)
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hread : LateSeedReadout init M ell sigma (trace init omega seed)) :
    1000 * LatePotential.shallowLargePotential ell
        (trace init omega homogeneous) ≤
      32 ^ terminalCutoff n * M := by
  have hcut := oldIndexCutoff_at_homogeneous hpath hmixed hread.oldIndexCutoff
  have hlarge :=
    LateSharpInitialPotential.shallowLargePotential_le_pow_mul_phiMass
      ell (terminalCutoff n) (trace init omega homogeneous) hcut
  have hmono := phiMass_homogeneous_le_seed
    (ell := ell) hpath hmixed
  have hseed := LateSharpInitialPotential.seed_phiMass_scaled_le hread
  calc
    1000 * LatePotential.shallowLargePotential ell
        (trace init omega homogeneous)
        ≤ 1000 * (32 ^ terminalCutoff n *
          Phase6PhiPotential.phiMass ell (trace init omega homogeneous)) :=
      Nat.mul_le_mul_left 1000 hlarge
    _ = 32 ^ terminalCutoff n *
        (1000 * Phase6PhiPotential.phiMass ell
          (trace init omega homogeneous)) := by ring
    _ ≤ 32 ^ terminalCutoff n *
        (1000 * Phase6PhiPotential.phiMass ell
          (trace init omega seed)) :=
      Nat.mul_le_mul_left (32 ^ terminalCutoff n)
        (Nat.mul_le_mul_left 1000 hmono)
    _ ≤ 32 ^ terminalCutoff n * M :=
      Nat.mul_le_mul_left (32 ^ terminalCutoff n) hseed

/-- Paper form, using only `M ≤ n` from the role split. -/
theorem homogeneous_largePotential_scaled_le_population
    {init : InputCfg n} {omega : InputLog n}
    {allStart seed completed homogeneous M C R ell : ℕ} {sigma : Sign}
    (hpath : Prefix init omega allStart seed completed)
    (hmixed : MixedFiveSixPrefix init omega completed homogeneous)
    (hread : LateSeedReadout init M ell sigma (trace init omega seed))
    (hdensity : StrongSeedDensity n M C R) :
    1000 * LatePotential.shallowLargePotential ell
        (trace init omega homogeneous) ≤
      32 ^ terminalCutoff n * n := by
  have hupper := hdensity.mains_upper
  have hmain : M ≤ n := by omega
  exact (homogeneous_largePotential_scaled_le_main hpath hmixed hread).trans
    (Nat.mul_le_mul_left (32 ^ terminalCutoff n) hmain)

end LateSharpPotentialTransport
end Ripple.PopulationProtocol.ExactMajority

end
