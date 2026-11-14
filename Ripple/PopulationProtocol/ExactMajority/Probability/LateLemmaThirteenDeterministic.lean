-- Ripple/PopulationProtocol/ExactMajority/Probability/LateLemmaThirteenDeterministic.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateLemmaTwelveSmallGap
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase78WitnessTransport
import Ripple.PopulationProtocol.ExactMajority.Probability.CounterGuardedPhase

/-!
# Lemma 13: deterministic full-flag credit

From `LateLemmaTwelveSmallGap` this file uses:

* `LemmaTwelveRouteReceipt`, retaining the synchronized Lemma-11 path,
  homogeneous Phase-7 time, first Phase-8 seed, and `12*n ≤ 25*M`;
* `phaseSevenDeadline_lt_eight`, hence the homogeneous Phase-7 time is strictly
  before the first Phase-8 seed;
* `AllMinorityIndicesAbove`, supplied at the first Phase-8 seed by
  `phaseSevenBands_clear_at_firstEight` / `lemmaTwelve_smallGap`.

From the Lemma-11 files it uses
`phaseEightCreditConsumer_of_path`, whose fields give `J ≥ .544 M` and
`NoShallowMain` at the exact first Phase-8 seed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateLemmaThirteenDeterministic

open TimeTheorem TraceDrain StageEventSpec
open PhaseOneDrain PhaseOneDrainStopping
open Phase7BandDefs Phase7MajorityBlockLedger
open Phase7Convergence Phase8Convergence Phase8WitnessSupply
open Phase78WitnessTransport
open LateBiasedResourceCredit
open LateBiasedResourceCreditPhaseSeven
open LateBiasedResourceCreditPath
open LateLemmaElevenFiniteTimes
open LateLemmaTwelveSmallGap
open LateTimerUpperOriginalLaw
open Phase6BlockSnapshot

variable {L K n M R : ℕ}

/-! ## Equation (54) -/

/-- A Main that is actually in Phase 8 and whose one-use absorption flag is set. -/
def phaseEightFullSt (a : AgentState L K) : Prop :=
  a.phase.val = 8 ∧ a.role = Role.main ∧ a.full

instance : DecidablePred (phaseEightFullSt (L := L) (K := K)) :=
  fun a => by unfold phaseEightFullSt; infer_instance

/-- Per-agent `F₈` indicator. -/
def phaseEightFullUnit (a : AgentState L K) : ℕ :=
  if phaseEightFullSt a then 1 else 0

/-- `F₈`: actual Phase-8 full Mains. -/
def phaseEightFullCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP phaseEightFullSt c

/-- The per-agent summand of (54). -/
def latePhaseEightCreditAtom
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) : ℤ :=
  lateBiasedResourceAtom sigma ell hell a - phaseEightFullUnit a

/-- Equation (54), literally `J₈ = J - F₈`. -/
def latePhaseEightCredit
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K)) : ℤ :=
  lateBiasedResourceCredit sigma ell hell c - phaseEightFullCount c

@[simp] theorem phaseEightFullCount_add
    (a b : Config (AgentState L K)) :
    phaseEightFullCount (a + b) =
      phaseEightFullCount a + phaseEightFullCount b := by
  simp [phaseEightFullCount, Multiset.countP_add]

@[simp] theorem phaseEightFullCount_pair
    (a b : AgentState L K) :
    phaseEightFullCount ({a, b} : Config (AgentState L K)) =
      phaseEightFullUnit a + phaseEightFullUnit b := by
  change Multiset.countP phaseEightFullSt (a ::ₘ b ::ₘ 0) = _
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero,
    zero_add, add_comm]
  rfl

@[simp] theorem latePhaseEightCredit_add
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a b : Config (AgentState L K)) :
    latePhaseEightCredit sigma ell hell (a + b) =
      latePhaseEightCredit sigma ell hell a +
        latePhaseEightCredit sigma ell hell b := by
  unfold latePhaseEightCredit
  rw [lateBiasedResourceCredit_add, phaseEightFullCount_add]
  push_cast
  ring

@[simp] theorem latePhaseEightCredit_pair
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a b : AgentState L K) :
    latePhaseEightCredit sigma ell hell
        ({a, b} : Config (AgentState L K)) =
      latePhaseEightCreditAtom sigma ell hell a +
        latePhaseEightCreditAtom sigma ell hell b := by
  unfold latePhaseEightCredit latePhaseEightCreditAtom
  rw [lateBiasedResourceCredit_pair, phaseEightFullCount_pair]
  push_cast
  ring

/-- Agentwise form of the Lemma-12 depth conclusion. -/
def DeepMinorityAgent
    (sigma : Sign) (ell : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main →
    ∀ j : Fin (L + 1),
      a.bias = Bias.dyadic sigma j → ell.val + 2 < j.val

private theorem noShallow_of_staticFields
    (ell : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias)
    (hy : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val y) :
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val x := by
  rintro ⟨hm, s, j, hb, hj⟩
  apply hy
  exact ⟨by simpa [hrole] using hm, s, j,
    by simpa [hbias] using hb, hj⟩

private theorem deepMinority_of_staticFields
    (sigma : Sign) (ell : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias)
    (hy : DeepMinorityAgent sigma ell y) :
    DeepMinorityAgent sigma ell x := by
  intro hm j hb
  exact hy (by simpa [hrole] using hm) j
    (by simpa [hbias] using hb)

private theorem noShallow_fullUpdate
    (ell : Fin (L + 1)) (a : AgentState L K) (f : Bool)
    (h : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val a) :
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val
      ({a with full := f} : AgentState L K) :=
  noShallow_of_staticFields ell _ a rfl rfl h

private theorem noShallow_biasZero
    (ell : Fin (L + 1)) (a : AgentState L K) :
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val
      ({a with bias := Bias.zero} : AgentState L K) := by
  rintro ⟨_, s, j, hb, _⟩
  simp at hb

private theorem deepMinority_fullUpdate
    (sigma : Sign) (ell : Fin (L + 1))
    (a : AgentState L K) (f : Bool)
    (h : DeepMinorityAgent sigma ell a) :
    DeepMinorityAgent sigma ell ({a with full := f} : AgentState L K) :=
  deepMinority_of_staticFields sigma ell _ a rfl rfl h

private theorem deepMinority_biasZero
    (sigma : Sign) (ell : Fin (L + 1)) (a : AgentState L K) :
    DeepMinorityAgent sigma ell
      ({a with bias := Bias.zero} : AgentState L K) := by
  intro _ j hb
  simp at hb

/-! ## First Phase-8 seed has `F₈ = 0` -/

private theorem transition_fst_eq_self_phaseSeven_notBoth_nonclock
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main))
    (hclock : s.role ≠ Role.clock) :
    (Transition L K s t).1 = s := by
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
  have hp : (Phase7Transition L K s t).1 = s := by
    unfold Phase7Transition
    simp only [if_neg hnb]
    rw [if_neg hclock]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) s _ (by rw [hp, hs]; decide)]
  exact hp

private theorem transition_snd_eq_self_phaseSeven_notBoth_nonclock
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main))
    (hclock : t.role ≠ Role.clock) :
    (Transition L K s t).2 = t := by
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
  have hp : (Phase7Transition L K s t).2 = t := by
    unfold Phase7Transition
    simp only [if_neg hnb]
    rw [if_neg hclock]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) t _ (by rw [hp, ht]; decide)]
  exact hp

private theorem transition_fst_not_phaseEightFull_of_phaseSeven
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7) :
    ¬ phaseEightFullSt (L := L) (K := K) (Transition L K s t).1 := by
  rintro ⟨hphase, hmain, _⟩
  obtain ⟨hr, _⟩ :=
    PhaseOnlyWindows.Transition_role_phase7
      (L := L) (K := K) s t hs ht
  have hsMain : s.role = Role.main := by simpa [hr] using hmain
  by_cases htMain : t.role = Role.main
  · rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
      s t hs ht hsMain htMain] at hphase
    have hp := CounterGuardedPhase.cancelSplit_phase_fst
      (L := L) (K := K) s t
    have hpval : (cancelSplit L K s t).1.phase.val = 7 := by
      rw [show (cancelSplit L K s t).1.phase = s.phase from hp, hs]
    omega
  · have hnb : ¬ (s.role = Role.main ∧ t.role = Role.main) :=
      fun h => htMain h.2
    rw [transition_fst_eq_self_phaseSeven_notBoth_nonclock
      s t hs ht hnb (by rw [hsMain]; decide)] at hphase
    omega

private theorem transition_snd_not_phaseEightFull_of_phaseSeven
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7) :
    ¬ phaseEightFullSt (L := L) (K := K) (Transition L K s t).2 := by
  rintro ⟨hphase, hmain, _⟩
  obtain ⟨_, hr⟩ :=
    PhaseOnlyWindows.Transition_role_phase7
      (L := L) (K := K) s t hs ht
  have htMain : t.role = Role.main := by simpa [hr] using hmain
  by_cases hsMain : s.role = Role.main
  · rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
      s t hs ht hsMain htMain] at hphase
    have hp := CounterGuardedPhase.cancelSplit_phase_snd
      (L := L) (K := K) s t
    have hpval : (cancelSplit L K s t).2.phase.val = 7 := by
      rw [show (cancelSplit L K s t).2.phase = t.phase from hp, ht]
    omega
  · have hnb : ¬ (s.role = Role.main ∧ t.role = Role.main) :=
      fun h => hsMain h.1
    rw [transition_snd_eq_self_phaseSeven_notBoth_nonclock
      s t hs ht hnb (by rw [htMain]; decide)] at hphase
    omega

/-- At the exact first Phase-8 seed, no Main is already a full Phase-8 Main.
The predecessor lies after the homogeneous Phase-7 time and before the first
Phase-8 seed, hence is pure Phase 7.  A Phase-7 step can create Phase 8 only
through a Clock counter update; Main outputs remain Phase 7. -/
theorem phaseEightFullCount_firstSeed_eq_zero
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneous eight ell hell sigma tau) :
    phaseEightFullCount (trace init omega eight) = 0 := by
  classical
  have hhomEight : homogeneous < eight := by
    have hdeadline := phaseSevenDeadline_lt_eight hroute
    omega
  have heightPos : eight ≠ 0 := by omega
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero heightPos
  have hhomR : homogeneous ≤ r := by omega
  have hpure : allPhaseExactly 7 (trace init omega homogeneous) :=
    ((homogeneousLatePhaseStart_eq_iff
      init 7 homogeneous omega).mp hroute.height.homogeneous_time).1
  have hreach := TimeTheorem.trace_reachable init omega hhomR
  have hlower := PhaseOneDrainStopping.phase_lower_reachable
    (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256)
    7 (trace init omega homogeneous) (trace init omega r)
    hreach (fun a ha => by rw [hpure a ha])
  have hseven :
      ∀ a ∈ trace init omega r, a.phase.val = 7 := by
    intro a ha
    have hlo := hlower a ha
    have hhi := hroute.path.eight_seed.2 r (Nat.lt_succ_self r) a ha
    omega
  have hsourceZero : phaseEightFullCount (trace init omega r) = 0 := by
    unfold phaseEightFullCount
    rw [Multiset.countP_eq_zero]
    intro a ha
    rintro ⟨haEight, _, _⟩
    have := hseven a ha
    omega
  rw [TimeTheorem.trace_succ]
  cases hdraw : omega (r + 1) with
  | none =>
      simpa [TimeTheorem.applyDraw, hdraw] using hsourceZero
  | some pair =>
      change phaseEightFullCount
        (Protocol.stepOrSelf
          (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256)
          (trace init omega r) pair.1.1 pair.2.1) = 0
      by_cases happ : Protocol.Applicable
          (trace init omega r) pair.1.1 pair.2.1
      · have hsMem : pair.1.1 ∈ trace init omega r :=
          Multiset.mem_of_le happ (by simp)
        have htMem : pair.2.1 ∈ trace init omega r :=
          Multiset.mem_of_le happ (by simp)
        have hs := hseven pair.1.1 hsMem
        have ht := hseven pair.2.1 htMem
        have hleft := transition_fst_not_phaseEightFull_of_phaseSeven
          pair.1.1 pair.2.1 hs ht
        have hright := transition_snd_not_phaseEightFull_of_phaseSeven
          pair.1.1 pair.2.1 hs ht
        have houtZero :
            phaseEightFullCount
              ({(Transition _ _ pair.1.1 pair.2.1).1,
                (Transition _ _ pair.1.1 pair.2.1).2} :
                Config (AgentState (PhaseThreeModel.Numeric.hourIndex n) 256)) = 0 := by
          rw [phaseEightFullCount_pair]
          simp [phaseEightFullUnit, hleft, hright]
        have hstep :
            Protocol.stepOrSelf
                (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256)
                (trace init omega r) pair.1.1 pair.2.1 =
              trace init omega r - {pair.1.1, pair.2.1} +
                {(Transition _ _ pair.1.1 pair.2.1).1,
                  (Transition _ _ pair.1.1 pair.2.1).2} := by
          unfold Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        unfold phaseEightFullCount at hsourceZero houtZero ⊢
        rw [hstep, Multiset.countP_add,
          Multiset.countP_sub happ, hsourceZero, houtZero]
        omega
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
        exact hsourceZero

/-! ## Literal Phase-8 absorption ledger -/

private theorem atom_biasZero_of_main
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) (hm : a.role = Role.main) :
    lateBiasedResourceAtom sigma ell hell
      ({a with bias := Bias.zero} : AgentState L K) = 0 := by
  simp [lateBiasedResourceAtom, phaseSixChargeUnit, biasedMainUnit,
    minoritySplitDebtUnit, Phase6FuelLedger.agentDebt,
    dangerousReserveUnit, hm]

private theorem atom_le_negOne_of_main_dyadic_notBlock
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) (s : Sign) (j : Fin (L + 1))
    (hm : a.role = Role.main) (hb : a.bias = Bias.dyadic s j)
    (hQ : majorityBlockUnit sigma ell.val a = 0) :
    lateBiasedResourceAtom sigma ell hell a ≤ -1 := by
  have hV : biasedMainUnit a = 1 := by
    simp [biasedMainUnit, hm, hb]
  unfold lateBiasedResourceAtom phaseSixChargeUnit
  rw [hQ, hV]
  omega

private theorem consumedRight_not_in_majorityBlock
    (sigma : Sign) (ell : Fin (L + 1))
    (s t : AgentState L K) (ss tt : Sign)
    (i j : Fin (L + 1))
    (hsMain : s.role = Role.main) (htMain : t.role = Role.main)
    (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic tt j)
    (hsgn : ss ≠ tt) (hij : i.val < j.val)
    (hsDeep : DeepMinorityAgent sigma ell s) :
    majorityBlockUnit sigma ell.val t = 0 := by
  rw [majorityBlockUnit_main_dyadic sigma tt ell.val j t htMain htb]
  apply if_neg
  rintro ⟨htt, _, hjtop⟩
  have hss : ss = sigma := by
    revert hsgn htt
    cases sigma <;> cases ss <;> cases tt <;> decide
  have hideep := hsDeep hsMain i (by simpa [hss] using hsb)
  omega

private theorem consumedLeft_not_in_majorityBlock
    (sigma : Sign) (ell : Fin (L + 1))
    (s t : AgentState L K) (ss tt : Sign)
    (i j : Fin (L + 1))
    (hsMain : s.role = Role.main) (htMain : t.role = Role.main)
    (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic tt j)
    (hsgn : ss ≠ tt) (hji : j.val < i.val)
    (htDeep : DeepMinorityAgent sigma ell t) :
    majorityBlockUnit sigma ell.val s = 0 := by
  rw [majorityBlockUnit_main_dyadic sigma ss ell.val i s hsMain hsb]
  apply if_neg
  rintro ⟨hss, _, hitop⟩
  have htt : tt = sigma := by
    revert hsgn hss
    cases sigma <;> cases ss <;> cases tt <;> decide
  have hjdeep := htDeep htMain j (by simpa [htt] using htb)
  omega

/-- Result form used below: output invariants plus input-to-output credit
monotonicity. -/
private structure PairTransport
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t x y : AgentState L K) : Prop where
  noShallowLeft :
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val x
  noShallowRight :
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val y
  deepLeft : DeepMinorityAgent sigma ell x
  deepRight : DeepMinorityAgent sigma ell y
  credit :
    latePhaseEightCreditAtom sigma ell hell s +
        latePhaseEightCreditAtom sigma ell hell t ≤
      latePhaseEightCreditAtom sigma ell hell x +
        latePhaseEightCreditAtom sigma ell hell y

private theorem absorb_left_firing
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K) (ss tt : Sign)
    (i j : Fin (L + 1))
    (hsEight : s.phase.val = 8) (htEight : t.phase.val = 8)
    (hsMain : s.role = Role.main) (htMain : t.role = Role.main)
    (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic tt j)
    (hsgn : ss ≠ tt) (hfire : i.val < j.val ∧ ¬ s.full)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t)
    (hsDeep : DeepMinorityAgent sigma ell s)
    (htDeep : DeepMinorityAgent sigma ell t)
    (hshape : absorbConsume L K s t =
      ({s with full := true}, {t with bias := Bias.zero})) :
    PairTransport sigma ell hell s t
      (absorbConsume L K s t).1 (absorbConsume L K s t).2 := by
  rw [hshape]
  refine
    { noShallowLeft := noShallow_fullUpdate ell s true hsNo
      noShallowRight := noShallow_biasZero ell t
      deepLeft := deepMinority_fullUpdate sigma ell s true hsDeep
      deepRight := deepMinority_biasZero sigma ell t
      credit := ?_ }
  have hQ := consumedRight_not_in_majorityBlock
    sigma ell s t ss tt i j hsMain htMain hsb htb hsgn hfire.1 hsDeep
  have htAtom := atom_le_negOne_of_main_dyadic_notBlock
    sigma ell hell t tt j htMain htb hQ
  have hsAtom :
      lateBiasedResourceAtom sigma ell hell
          ({s with full := true} : AgentState L K) =
        lateBiasedResourceAtom sigma ell hell s :=
    lateBiasedResourceAtom_eq_of_staticFields
      sigma ell hell _ s rfl rfl (fun _ => rfl)
  have htZero := atom_biasZero_of_main sigma ell hell t htMain
  have hsFullZero : phaseEightFullUnit s = 0 := by
    simp [phaseEightFullUnit, phaseEightFullSt,
      hsEight, hsMain, hfire.2]
  have hsFullOne :
      phaseEightFullUnit ({s with full := true} : AgentState L K) = 1 := by
    simp [phaseEightFullUnit, phaseEightFullSt, hsEight, hsMain]
  have htFull :
      phaseEightFullUnit ({t with bias := Bias.zero} : AgentState L K) =
        phaseEightFullUnit t := rfl
  unfold latePhaseEightCreditAtom
  rw [hsAtom, htZero, hsFullZero, hsFullOne, htFull]
  push_cast
  linarith

private theorem absorb_right_firing
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K) (ss tt : Sign)
    (i j : Fin (L + 1))
    (hsEight : s.phase.val = 8) (htEight : t.phase.val = 8)
    (hsMain : s.role = Role.main) (htMain : t.role = Role.main)
    (hsb : s.bias = Bias.dyadic ss i)
    (htb : t.bias = Bias.dyadic tt j)
    (hsgn : ss ≠ tt) (hfire : j.val < i.val ∧ ¬ t.full)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t)
    (hsDeep : DeepMinorityAgent sigma ell s)
    (htDeep : DeepMinorityAgent sigma ell t)
    (hshape : absorbConsume L K s t =
      ({s with bias := Bias.zero}, {t with full := true})) :
    PairTransport sigma ell hell s t
      (absorbConsume L K s t).1 (absorbConsume L K s t).2 := by
  rw [hshape]
  refine
    { noShallowLeft := noShallow_biasZero ell s
      noShallowRight := noShallow_fullUpdate ell t true htNo
      deepLeft := deepMinority_biasZero sigma ell s
      deepRight := deepMinority_fullUpdate sigma ell t true htDeep
      credit := ?_ }
  have hQ := consumedLeft_not_in_majorityBlock
    sigma ell s t ss tt i j hsMain htMain hsb htb hsgn hfire.1 htDeep
  have hsAtom := atom_le_negOne_of_main_dyadic_notBlock
    sigma ell hell s ss i hsMain hsb hQ
  have hsZero := atom_biasZero_of_main sigma ell hell s hsMain
  have htAtom :
      lateBiasedResourceAtom sigma ell hell
          ({t with full := true} : AgentState L K) =
        lateBiasedResourceAtom sigma ell hell t :=
    lateBiasedResourceAtom_eq_of_staticFields
      sigma ell hell _ t rfl rfl (fun _ => rfl)
  have htFullZero : phaseEightFullUnit t = 0 := by
    simp [phaseEightFullUnit, phaseEightFullSt,
      htEight, htMain, hfire.2]
  have htFullOne :
      phaseEightFullUnit ({t with full := true} : AgentState L K) = 1 := by
    simp [phaseEightFullUnit, phaseEightFullSt, htEight, htMain]
  have hsFull :
      phaseEightFullUnit ({s with bias := Bias.zero} : AgentState L K) =
        phaseEightFullUnit s := rfl
  unfold latePhaseEightCreditAtom
  rw [hsZero, htAtom, htFullZero, htFullOne, hsFull]
  push_cast
  linarith

set_option maxHeartbeats 800000 in
/-- Exhaustive literal `absorbConsume` table.  The scoped allowance is for the
five dependent branch splits; no unbounded setting is used. -/
theorem absorbConsume_pair_transport
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hsEight : s.phase.val = 8) (htEight : t.phase.val = 8)
    (hsMain : s.role = Role.main) (htMain : t.role = Role.main)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t)
    (hsDeep : DeepMinorityAgent sigma ell s)
    (htDeep : DeepMinorityAgent sigma ell t) :
    PairTransport sigma ell hell s t
      (absorbConsume L K s t).1 (absorbConsume L K s t).2 := by
  rcases hsb : s.bias with _ | ⟨ss, i⟩
  · have hshape : absorbConsume L K s t = (s, t) := by
      unfold absorbConsume
      rw [hsb]
    rw [hshape]
    exact ⟨hsNo, htNo, hsDeep, htDeep, le_rfl⟩
  · rcases htb : t.bias with _ | ⟨tt, j⟩
    · have hshape : absorbConsume L K s t = (s, t) := by
        unfold absorbConsume
        rw [hsb, htb]
        cases ss <;> rfl
      rw [hshape]
      exact ⟨hsNo, htNo, hsDeep, htDeep, le_rfl⟩
    · by_cases hsgn : ss ≠ tt
      · by_cases hleft : i.val < j.val ∧ ¬ s.full
        · have hshape : absorbConsume L K s t =
              ({s with full := true}, {t with bias := Bias.zero}) := by
            unfold absorbConsume
            rw [hsb, htb]
            cases ss <;> cases tt <;>
              (first | exact absurd rfl hsgn | simp [hleft.1, hleft.2])
          exact absorb_left_firing sigma ell hell s t ss tt i j
            hsEight htEight hsMain htMain hsb htb hsgn hleft
            hsNo htNo hsDeep htDeep hshape
        · by_cases hright : j.val < i.val ∧ ¬ t.full
          · have hshape : absorbConsume L K s t =
                ({s with bias := Bias.zero}, {t with full := true}) := by
              unfold absorbConsume
              rw [hsb, htb]
              cases ss <;> cases tt <;>
                (first | exact absurd rfl hsgn | simp only [if_neg hleft, if_pos hright])
            exact absorb_right_firing sigma ell hell s t ss tt i j
              hsEight htEight hsMain htMain hsb htb hsgn hright
              hsNo htNo hsDeep htDeep hshape
          · have hshape : absorbConsume L K s t = (s, t) := by
              unfold absorbConsume
              rw [hsb, htb]
              cases ss <;> cases tt <;>
                (first | exact absurd rfl hsgn | simp only [if_neg hleft, if_neg hright])
            rw [hshape]
            exact ⟨hsNo, htNo, hsDeep, htDeep, le_rfl⟩
      · have hshape : absorbConsume L K s t = (s, t) := by
          unfold absorbConsume
          have heq : ss = tt := not_not.mp hsgn
          subst heq
          rw [hsb, htb]
          cases ss <;> rfl
        rw [hshape]
        exact ⟨hsNo, htNo, hsDeep, htDeep, le_rfl⟩

/-! ## Actual Phase-8 dispatch, including mixed 7/8 epidemic entry -/

private theorem transition_fst_eq_self_phaseEight_notBoth_nonclock
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main))
    (hclock : s.role ≠ Role.clock) :
    (Transition L K s t).1 = s := by
  have hepi := Phase8Convergence.phaseEpidemicUpdate_eq_self_of_phase8
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
  have hp : (Phase8Transition L K s t).1 = s := by
    unfold Phase8Transition
    simp only [if_neg hnb]
    rw [if_neg hclock]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) s _ (by rw [hp, hs]; decide)]
  exact hp

private theorem transition_snd_eq_self_phaseEight_notBoth_nonclock
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main))
    (hclock : t.role ≠ Role.clock) :
    (Transition L K s t).2 = t := by
  have hepi := Phase8Convergence.phaseEpidemicUpdate_eq_self_of_phase8
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
  have hp : (Phase8Transition L K s t).2 = t := by
    unfold Phase8Transition
    simp only [if_neg hnb]
    rw [if_neg hclock]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) t _ (by rw [hp, ht]; decide)]
  exact hp

private theorem transition_atom_eq_phaseEight_notBoth_fst
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    latePhaseEightCreditAtom sigma ell hell (Transition L K s t).1 =
      latePhaseEightCreditAtom sigma ell hell s := by
  obtain ⟨hr, _⟩ :=
    PhaseOnlyWindows.Transition_role_phase8
      (L := L) (K := K) s t hs ht
  by_cases hm : s.role = Role.main
  · rw [transition_fst_eq_self_phaseEight_notBoth_nonclock
      s t hs ht hnb (by rw [hm]; decide)]
  · by_cases hv : s.role = Role.reserve
    · rw [transition_fst_eq_self_phaseEight_notBoth_nonclock
        s t hs ht hnb (by rw [hv]; decide)]
    · have houtM : (Transition L K s t).1.role ≠ Role.main := by
        simpa [hr] using hm
      have houtR : (Transition L K s t).1.role ≠ Role.reserve := by
        simpa [hr] using hv
      have hin := lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
        sigma ell hell s hm hv
      have hout := lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
        sigma ell hell (Transition L K s t).1 houtM houtR
      have hfullIn : phaseEightFullUnit s = 0 := by
        simp [phaseEightFullUnit, phaseEightFullSt, hm]
      have hfullOut : phaseEightFullUnit (Transition L K s t).1 = 0 := by
        simp [phaseEightFullUnit, phaseEightFullSt, houtM]
      unfold latePhaseEightCreditAtom
      rw [hin, hout, hfullIn, hfullOut]

private theorem transition_atom_eq_phaseEight_notBoth_snd
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    latePhaseEightCreditAtom sigma ell hell (Transition L K s t).2 =
      latePhaseEightCreditAtom sigma ell hell t := by
  obtain ⟨_, hr⟩ :=
    PhaseOnlyWindows.Transition_role_phase8
      (L := L) (K := K) s t hs ht
  by_cases hm : t.role = Role.main
  · rw [transition_snd_eq_self_phaseEight_notBoth_nonclock
      s t hs ht hnb (by rw [hm]; decide)]
  · by_cases hv : t.role = Role.reserve
    · rw [transition_snd_eq_self_phaseEight_notBoth_nonclock
        s t hs ht hnb (by rw [hv]; decide)]
    · have houtM : (Transition L K s t).2.role ≠ Role.main := by
        simpa [hr] using hm
      have houtR : (Transition L K s t).2.role ≠ Role.reserve := by
        simpa [hr] using hv
      have hin := lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
        sigma ell hell t hm hv
      have hout := lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
        sigma ell hell (Transition L K s t).2 houtM houtR
      have hfullIn : phaseEightFullUnit t = 0 := by
        simp [phaseEightFullUnit, phaseEightFullSt, hm]
      have hfullOut : phaseEightFullUnit (Transition L K s t).2 = 0 := by
        simp [phaseEightFullUnit, phaseEightFullSt, houtM]
      unfold latePhaseEightCreditAtom
      rw [hin, hout, hfullIn, hfullOut]

private theorem transition_phaseEight_pair_transport
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t)
    (hsDeep : DeepMinorityAgent sigma ell s)
    (htDeep : DeepMinorityAgent sigma ell t) :
    PairTransport sigma ell hell s t
      (Transition L K s t).1 (Transition L K s t).2 := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · have heq := Phase8Convergence.Transition_eq_absorbConsume_of_phase8_main
      (L := L) (K := K) s t hs ht hboth.1 hboth.2
    simpa [heq] using
      absorbConsume_pair_transport sigma ell hell s t hs ht
        hboth.1 hboth.2 hsNo htNo hsDeep htDeep
  · obtain ⟨hrLeft, hrRight⟩ :=
      PhaseOnlyWindows.Transition_role_phase8
        (L := L) (K := K) s t hs ht
    have hNoLeft :
        ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val
          (Transition L K s t).1 := by
      rintro hhigh
      have hm : s.role = Role.main := by simpa [hrLeft] using hhigh.1
      rw [transition_fst_eq_self_phaseEight_notBoth_nonclock
        s t hs ht hboth (by rw [hm]; decide)] at hhigh
      exact hsNo hhigh
    have hNoRight :
        ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val
          (Transition L K s t).2 := by
      rintro hhigh
      have hm : t.role = Role.main := by simpa [hrRight] using hhigh.1
      rw [transition_snd_eq_self_phaseEight_notBoth_nonclock
        s t hs ht hboth (by rw [hm]; decide)] at hhigh
      exact htNo hhigh
    have hDeepLeft : DeepMinorityAgent sigma ell (Transition L K s t).1 := by
      intro hm j hb
      have hsMain : s.role = Role.main := by simpa [hrLeft] using hm
      rw [transition_fst_eq_self_phaseEight_notBoth_nonclock
        s t hs ht hboth (by rw [hsMain]; decide)] at hb
      exact hsDeep hsMain j hb
    have hDeepRight : DeepMinorityAgent sigma ell (Transition L K s t).2 := by
      intro hm j hb
      have htMain : t.role = Role.main := by simpa [hrRight] using hm
      rw [transition_snd_eq_self_phaseEight_notBoth_nonclock
        s t hs ht hboth (by rw [htMain]; decide)] at hb
      exact htDeep htMain j hb
    refine ⟨hNoLeft, hNoRight, hDeepLeft, hDeepRight, ?_⟩
    rw [transition_atom_eq_phaseEight_notBoth_fst
        sigma ell hell s t hs ht hboth,
      transition_atom_eq_phaseEight_notBoth_snd
        sigma ell hell s t hs ht hboth]

private theorem transition_phaseSeven_deep_pair
    (sigma : Sign) (ell : Fin (L + 1))
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hsDeep : DeepMinorityAgent sigma ell s)
    (htDeep : DeepMinorityAgent sigma ell t) :
    DeepMinorityAgent sigma ell (Transition L K s t).1 ∧
      DeepMinorityAgent sigma ell (Transition L K s t).2 := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · have heq := Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
      (L := L) (K := K) s t hs ht hboth.1 hboth.2
    have hsFloor : ∀ j : Fin (L + 1),
        s.bias = Bias.dyadic sigma j → ell.val + 3 ≤ j.val := by
      intro j hb
      have := hsDeep hboth.1 j hb
      omega
    have htFloor : ∀ j : Fin (L + 1),
        t.bias = Bias.dyadic sigma j → ell.val + 3 ≤ j.val := by
      intro j hb
      have := htDeep hboth.2 j hb
      omega
    constructor <;> intro _ j hb
    · rw [heq] at hb
      have h := (cancelSplit_sigma_output_index_ge
        sigma (ell.val + 3) s t hsFloor htFloor j).1 hb
      omega
    · rw [heq] at hb
      have h := (cancelSplit_sigma_output_index_ge
        sigma (ell.val + 3) s t hsFloor htFloor j).2 hb
      omega
  · obtain ⟨hrLeft, hrRight⟩ :=
      PhaseOnlyWindows.Transition_role_phase7
        (L := L) (K := K) s t hs ht
    constructor
    · intro hm j hb
      have hsMain : s.role = Role.main := by simpa [hrLeft] using hm
      rw [transition_fst_eq_self_phaseSeven_notBoth_nonclock
        s t hs ht hboth (by rw [hsMain]; decide)] at hb
      exact hsDeep hsMain j hb
    · intro hm j hb
      have htMain : t.role = Role.main := by simpa [hrRight] using hm
      rw [transition_snd_eq_self_phaseSeven_notBoth_nonclock
        s t hs ht hboth (by rw [htMain]; decide)] at hb
      exact htDeep htMain j hb

private theorem transition_phaseSeven_pair_transport
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t)
    (hsDeep : DeepMinorityAgent sigma ell s)
    (htDeep : DeepMinorityAgent sigma ell t) :
    PairTransport sigma ell hell s t
      (Transition L K s t).1 (Transition L K s t).2 := by
  have hNo := Transition_noShallow_pair_of_phaseSixOrSeven
    ell s t (Or.inr hs) (Or.inr ht) hsNo htNo
  have hDeep := transition_phaseSeven_deep_pair
    sigma ell s t hs ht hsDeep htDeep
  have hJ := Transition_atom_pair_mono_of_phaseSixOrSeven
    sigma ell hell s t (Or.inr hs) (Or.inr ht) hsNo htNo
  have hsFull : phaseEightFullUnit s = 0 := by
    simp [phaseEightFullUnit, phaseEightFullSt, hs]
  have htFull : phaseEightFullUnit t = 0 := by
    simp [phaseEightFullUnit, phaseEightFullSt, ht]
  have hoLeft : phaseEightFullUnit (Transition L K s t).1 = 0 := by
    simp [phaseEightFullUnit,
      transition_fst_not_phaseEightFull_of_phaseSeven s t hs ht]
  have hoRight : phaseEightFullUnit (Transition L K s t).2 = 0 := by
    simp [phaseEightFullUnit,
      transition_snd_not_phaseEightFull_of_phaseSeven s t hs ht]
  refine ⟨hNo.1, hNo.2, hDeep.1, hDeep.2, ?_⟩
  unfold latePhaseEightCreditAtom
  rw [hsFull, htFull, hoLeft, hoRight]
  push_cast
  linarith

private theorem runInitsBetween_seven_eight_data
    (a : AgentState L K) :
    let z := runInitsBetween L K 7 8
      ({a with phase := ⟨8, by decide⟩} : AgentState L K)
    z.phase.val = 8 ∧ z.full = false := by
  intro z
  have hlist :
      (List.range 11).filter (fun k => 7 < k ∧ k ≤ 8) = [8] := by
    decide
  have hz : z = phaseInit L K ⟨8, by decide⟩
      ({a with phase := ⟨8, by decide⟩} : AgentState L K) := by
    show runInitsBetween L K 7 8 _ = _
    unfold runInitsBetween
    rw [hlist]
    rfl
  rw [hz]
  unfold phaseInit
  simp

private theorem epidemic_seven_eight_data
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 8) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 8 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 8 ∧
      (phaseEpidemicUpdate L K s t).1.full = false ∧
      (phaseEpidemicUpdate L K s t).2.full = t.full := by
  have hpval : (max s.phase t.phase).val = 8 := by simp [hs, ht]
  have hsData :
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({s with phase := max s.phase t.phase} : AgentState L K)).phase.val = 8 ∧
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({s with phase := max s.phase t.phase} : AgentState L K)).full = false := by
    rw [hs, hpval]
    simpa only [show max s.phase t.phase = ⟨8, by decide⟩ from Fin.ext hpval]
      using runInitsBetween_seven_eight_data (L := L) (K := K) s
  have htData :
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({t with phase := max s.phase t.phase} : AgentState L K)).phase.val = 8 ∧
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({t with phase := max s.phase t.phase} : AgentState L K)).full = t.full := by
    rw [ht, hpval, runInitsBetween_self]
    simp [max_eq_right (show s.phase ≤ t.phase by rw [Fin.le_def]; omega), ht]
  unfold phaseEpidemicUpdate
  dsimp only
  rw [if_neg (by omega)]
  exact ⟨hsData.1, htData.1, hsData.2, htData.2⟩

private theorem epidemic_eight_seven_data
    (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 7) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 8 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 8 ∧
      (phaseEpidemicUpdate L K s t).1.full = s.full ∧
      (phaseEpidemicUpdate L K s t).2.full = false := by
  have hpval : (max s.phase t.phase).val = 8 := by simp [hs, ht]
  have hsData :
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({s with phase := max s.phase t.phase} : AgentState L K)).phase.val = 8 ∧
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({s with phase := max s.phase t.phase} : AgentState L K)).full = s.full := by
    rw [hs, hpval, runInitsBetween_self]
    simp [max_eq_left (show t.phase ≤ s.phase by rw [Fin.le_def]; omega), hs]
  have htData :
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({t with phase := max s.phase t.phase} : AgentState L K)).phase.val = 8 ∧
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({t with phase := max s.phase t.phase} : AgentState L K)).full = false := by
    rw [ht, hpval]
    simpa only [show max s.phase t.phase = ⟨8, by decide⟩ from Fin.ext hpval]
      using runInitsBetween_seven_eight_data (L := L) (K := K) t
  unfold phaseEpidemicUpdate
  dsimp only
  rw [if_neg (by omega)]
  exact ⟨hsData.1, htData.1, hsData.2, htData.2⟩

private theorem transition_eq_epidemic_of_phaseEight
    (s t : AgentState L K)
    (hleft : (phaseEpidemicUpdate L K s t).1.phase.val = 8)
    (hright : (phaseEpidemicUpdate L K s t).2.phase.val = 8) :
    Transition L K s t =
      Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2 := by
  let ep := phaseEpidemicUpdate L K s t
  have hepid : phaseEpidemicUpdate L K ep.1 ep.2 = ep :=
    Phase8Convergence.phaseEpidemicUpdate_eq_self_of_phase8
      ep.1 ep.2 hleft hright
  unfold Transition
  rw [hepid]

private theorem pairTransport_of_epidemicEight
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hep : (phaseEpidemicUpdate L K s t).1.phase.val = 8 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 8)
    (hAtomLeft : lateBiasedResourceAtom sigma ell hell
        (phaseEpidemicUpdate L K s t).1 =
      lateBiasedResourceAtom sigma ell hell s)
    (hAtomRight : lateBiasedResourceAtom sigma ell hell
        (phaseEpidemicUpdate L K s t).2 =
      lateBiasedResourceAtom sigma ell hell t)
    (hFullLeft : phaseEightFullUnit (phaseEpidemicUpdate L K s t).1 =
      phaseEightFullUnit s)
    (hFullRight : phaseEightFullUnit (phaseEpidemicUpdate L K s t).2 =
      phaseEightFullUnit t)
    (hNoLeft : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val (phaseEpidemicUpdate L K s t).1)
    (hNoRight : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val (phaseEpidemicUpdate L K s t).2)
    (hDeepLeft : DeepMinorityAgent sigma ell
      (phaseEpidemicUpdate L K s t).1)
    (hDeepRight : DeepMinorityAgent sigma ell
      (phaseEpidemicUpdate L K s t).2) :
    PairTransport sigma ell hell s t
      (Transition L K s t).1 (Transition L K s t).2 := by
  have hcore := transition_phaseEight_pair_transport
    sigma ell hell
    (phaseEpidemicUpdate L K s t).1
    (phaseEpidemicUpdate L K s t).2
    hep.1 hep.2 hNoLeft hNoRight hDeepLeft hDeepRight
  rw [transition_eq_epidemic_of_phaseEight s t hep.1 hep.2]
  refine ⟨hcore.noShallowLeft, hcore.noShallowRight,
    hcore.deepLeft, hcore.deepRight, ?_⟩
  have hc := hcore.credit
  unfold latePhaseEightCreditAtom at hc ⊢
  rw [hAtomLeft, hAtomRight, hFullLeft, hFullRight] at hc
  exact hc

/-- Full actual dispatch on a source pair in phases `7..8`. -/
theorem transition_pair_transport_of_phaseSevenOrEight
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 7 ∨ s.phase.val = 8)
    (ht : t.phase.val = 7 ∨ t.phase.val = 8)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t)
    (hsDeep : DeepMinorityAgent sigma ell s)
    (htDeep : DeepMinorityAgent sigma ell t) :
    PairTransport sigma ell hell s t
      (Transition L K s t).1 (Transition L K s t).2 := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact transition_phaseSeven_pair_transport
      sigma ell hell s t hs ht hsNo htNo hsDeep htDeep
  · have hdata := epidemic_seven_eight_data
      (L := L) (K := K) s t hs ht
    have hbias := Phase6Convergence.phaseEpidemicUpdate_bias_ge_five
      (L := L) (K := K) s t (by omega) (by omega)
    have hfields := ReserveSampling.phaseEpidemicUpdate_role_hour_ge5
      (L := L) (K := K) s t (by omega) (by omega)
    have hAtomLeft := lateBiasedResourceAtom_eq_of_staticFields
      sigma ell hell _ s hfields.1 hbias.1 (fun _ => hfields.2.1)
    have hAtomRight := lateBiasedResourceAtom_eq_of_staticFields
      sigma ell hell _ t hfields.2.2.1 hbias.2 (fun _ => hfields.2.2.2)
    have hFullLeft : phaseEightFullUnit (phaseEpidemicUpdate L K s t).1 =
        phaseEightFullUnit s := by
      simp [phaseEightFullUnit, phaseEightFullSt,
        hs, hdata.1, hdata.2.2.1, hfields.1]
    have hFullRight : phaseEightFullUnit (phaseEpidemicUpdate L K s t).2 =
        phaseEightFullUnit t := by
      simp [phaseEightFullUnit, phaseEightFullSt,
        ht, hdata.2.1, hdata.2.2.2, hfields.2.2.1]
    exact pairTransport_of_epidemicEight sigma ell hell s t
      ⟨hdata.1, hdata.2.1⟩ hAtomLeft hAtomRight
      hFullLeft hFullRight
      (noShallow_of_staticFields ell _ s hfields.1 hbias.1 hsNo)
      (noShallow_of_staticFields ell _ t hfields.2.2.1 hbias.2 htNo)
      (deepMinority_of_staticFields sigma ell _ s hfields.1 hbias.1 hsDeep)
      (deepMinority_of_staticFields sigma ell _ t hfields.2.2.1 hbias.2 htDeep)
  · have hdata := epidemic_eight_seven_data
      (L := L) (K := K) s t hs ht
    have hbias := Phase6Convergence.phaseEpidemicUpdate_bias_ge_five
      (L := L) (K := K) s t (by omega) (by omega)
    have hfields := ReserveSampling.phaseEpidemicUpdate_role_hour_ge5
      (L := L) (K := K) s t (by omega) (by omega)
    have hAtomLeft := lateBiasedResourceAtom_eq_of_staticFields
      sigma ell hell _ s hfields.1 hbias.1 (fun _ => hfields.2.1)
    have hAtomRight := lateBiasedResourceAtom_eq_of_staticFields
      sigma ell hell _ t hfields.2.2.1 hbias.2 (fun _ => hfields.2.2.2)
    have hFullLeft : phaseEightFullUnit (phaseEpidemicUpdate L K s t).1 =
        phaseEightFullUnit s := by
      simp [phaseEightFullUnit, phaseEightFullSt,
        hs, hdata.1, hdata.2.2.1, hfields.1]
    have hFullRight : phaseEightFullUnit (phaseEpidemicUpdate L K s t).2 =
        phaseEightFullUnit t := by
      simp [phaseEightFullUnit, phaseEightFullSt,
        ht, hdata.2.1, hdata.2.2.2, hfields.2.2.1]
    exact pairTransport_of_epidemicEight sigma ell hell s t
      ⟨hdata.1, hdata.2.1⟩ hAtomLeft hAtomRight
      hFullLeft hFullRight
      (noShallow_of_staticFields ell _ s hfields.1 hbias.1 hsNo)
      (noShallow_of_staticFields ell _ t hfields.2.2.1 hbias.2 htNo)
      (deepMinority_of_staticFields sigma ell _ s hfields.1 hbias.1 hsDeep)
      (deepMinority_of_staticFields sigma ell _ t hfields.2.2.1 hbias.2 htDeep)
  · exact transition_phaseEight_pair_transport
      sigma ell hell s t hs ht hsNo htNo hsDeep htDeep

/-! ## Source-guarded mixed 7/8 reachability -/

/-- Literal mixed-7/8 source window. -/
def PhaseSevenEightWindow (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 7 ∨ a.phase.val = 8

/-- One actual source-guarded step. -/
structure PhaseSevenEightCreditStep
    (init c d : Config (AgentState L K)) : Prop where
  source_reachable : (NonuniformMajority L K).Reachable init c
  source_window : PhaseSevenEightWindow c
  step : (NonuniformMajority L K).StepRel c d

def PhaseSevenEightCreditReachable
    (init c d : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen (PhaseSevenEightCreditStep init) c d

/-- One actual step preserves the depth floor, Lemma 10's no-shallow fact, and
`J₈`. -/
theorem phaseSevenEightCreditStep_preserves
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {init c d : Config (AgentState L K)}
    (hNo : NoShallowMain ell c)
    (hDeep : AllMinorityIndicesAbove sigma ell c)
    (hstep : PhaseSevenEightCreditStep init c d) :
    NoShallowMain ell d ∧
      AllMinorityIndicesAbove sigma ell d ∧
      latePhaseEightCredit sigma ell hell c ≤
        latePhaseEightCredit sigma ell hell d := by
  rcases hstep.step with ⟨s, t, happ, hd0⟩
  have hd : d = c - ({s, t} : Config (AgentState L K)) +
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Config (AgentState L K)) := hd0
  have hsMem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have htMem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hsDeep : DeepMinorityAgent sigma ell s :=
    fun hm j hb => hDeep s hsMem hm j hb
  have htDeep : DeepMinorityAgent sigma ell t :=
    fun hm j hb => hDeep t htMem hm j hb
  have hpair := transition_pair_transport_of_phaseSevenOrEight
    sigma ell hell s t
    (hstep.source_window s hsMem) (hstep.source_window t htMem)
    (hNo s hsMem) (hNo t htMem) hsDeep htDeep
  have hsub : ({s, t} : Config (AgentState L K)) ≤ c := happ
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]
    intro a ha
    rw [Multiset.mem_add] at ha
    rcases ha with hold | hnew
    · exact hNo a (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) hold)
    · have hnew' : a = (Transition L K s t).1 ∨
          a = (Transition L K s t).2 := by simpa using hnew
      rcases hnew' with hleft | hright
      · rw [hleft]; exact hpair.noShallowLeft
      · rw [hright]; exact hpair.noShallowRight
  · rw [hd]
    intro a ha hm j hb
    rw [Multiset.mem_add] at ha
    rcases ha with hold | hnew
    · exact hDeep a
        (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) hold)
        hm j hb
    · have hnew' : a = (Transition L K s t).1 ∨
          a = (Transition L K s t).2 := by simpa using hnew
      rcases hnew' with hleft | hright
      · rw [hleft] at hm hb
        exact hpair.deepLeft hm j hb
      · rw [hright] at hm hb
        exact hpair.deepRight hm j hb
  · rw [hd]
    have haddIn := latePhaseEightCredit_add sigma ell hell
      (c - {s, t}) ({s, t} : Config (AgentState L K))
    have haddOut := latePhaseEightCredit_add sigma ell hell
      (c - {s, t})
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Config (AgentState L K))
    have hc : c - {s, t} + ({s, t} : Config (AgentState L K)) = c :=
      tsub_add_cancel_of_le hsub
    rw [hc] at haddIn
    rw [haddOut]
    have hpIn := latePhaseEightCredit_pair sigma ell hell s t
    have hpOut := latePhaseEightCredit_pair sigma ell hell
      (Transition L K s t).1 (Transition L K s t).2
    linarith [hpair.credit]

/-- Iteration through mixed 7/8 and homogeneous Phase 8. -/
theorem phaseSevenEightCreditReachable_preserves
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {init c d : Config (AgentState L K)}
    (hreach : PhaseSevenEightCreditReachable init c d)
    (hNo : NoShallowMain ell c)
    (hDeep : AllMinorityIndicesAbove sigma ell c) :
    NoShallowMain ell d ∧
      AllMinorityIndicesAbove sigma ell d ∧
      latePhaseEightCredit sigma ell hell c ≤
        latePhaseEightCredit sigma ell hell d := by
  induction hreach with
  | refl => exact ⟨hNo, hDeep, le_rfl⟩
  | tail _ hlast ih =>
      have hnext := phaseSevenEightCreditStep_preserves
        sigma ell hell ih.1 ih.2.1 hlast
      exact ⟨hnext.1, hnext.2.1, ih.2.2.trans hnext.2.2⟩

/-- At the exact first Phase-8 seed, (54) equals the Lemma-11 credit and has
the `.544 M` floor. -/
theorem latePhaseEightCredit_firstSeed
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneous eight ell hell sigma tau)
    (hDeep : AllMinorityIndicesAbove sigma ell (trace init omega eight)) :
    NoShallowMain ell (trace init omega eight) ∧
      AllMinorityIndicesAbove sigma ell (trace init omega eight) ∧
      phaseEightFullCount (trace init omega eight) = 0 ∧
      (544 : ℤ) * (M : ℤ) ≤
        1000 * latePhaseEightCredit sigma ell hell
          (trace init omega eight) := by
  have hconsumer := phaseEightCreditConsumer_of_path hroute.path
  have hfull := phaseEightFullCount_firstSeed_eq_zero hroute
  refine ⟨hconsumer.no_shallow, hDeep, hfull, ?_⟩
  have heq :
      latePhaseEightCredit sigma ell hell (trace init omega eight) =
        lateBiasedResourceCredit sigma ell hell (trace init omega eight) := by
    simp [latePhaseEightCredit, hfull]
  rw [heq]
  exact hconsumer.credit_scaled

/-- Consequently `J₈ ≥ .544 M` at every endpoint of the concrete guarded
mixed-7/8 route. -/
theorem latePhaseEightCredit_floor_of_reachable
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneous eight ell hell sigma tau)
    (hDeep : AllMinorityIndicesAbove sigma ell (trace init omega eight))
    {d : InputCfg n}
    (hreach : PhaseSevenEightCreditReachable init
      (trace init omega eight) d) :
    NoShallowMain ell d ∧
      AllMinorityIndicesAbove sigma ell d ∧
      (544 : ℤ) * (M : ℤ) ≤
        1000 * latePhaseEightCredit sigma ell hell d := by
  have hstart := latePhaseEightCredit_firstSeed hroute hDeep
  have hmono := phaseSevenEightCreditReachable_preserves
    sigma ell hell hreach hstart.1 hstart.2.1
  exact ⟨hmono.1, hmono.2.1,
    hstart.2.2.2.trans (mul_le_mul_of_nonneg_left hmono.2.2 (by norm_num))⟩

/-! ## Availability, equation (56) -/

/-- A biased Main on the majority side, expressed without choosing its sign. -/
def majorityBiasedSt (sigma : Sign) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias ≠ Bias.zero ∧
    ¬ Phase7Convergence.minoritySt sigma a

/-- A majority-side Main that has not used its Phase-8 absorption. -/
def availableMajoritySt (sigma : Sign) (a : AgentState L K) : Prop :=
  majorityBiasedSt sigma a ∧ ¬ a.full

open Classical in
def majorityBiasedCount (sigma : Sign)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (majorityBiasedSt sigma) c

open Classical in
def availableMajorityCount (sigma : Sign)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (availableMajoritySt sigma) c

private theorem minoritySt_implies_biasedMain
    (sigma : Sign) (a : AgentState L K)
    (h : Phase7Convergence.minoritySt sigma a) :
    a.role = Role.main ∧ a.bias ≠ Bias.zero := by
  rcases h with ⟨hm, j, hb⟩
  exact ⟨hm, by rw [hb]; simp⟩

/-- `V = A + B₋`. -/
theorem biasedMainCount_eq_majority_add_minority
    (sigma : Sign) (c : Config (AgentState L K)) :
    Lemma613OFloor.phase3BiasedMainCount c =
      majorityBiasedCount sigma c + Phase7Convergence.minorityU sigma c := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [Lemma613OFloor.phase3BiasedMainCount,
      majorityBiasedCount, Phase7Convergence.minorityU]
  | cons a c ih =>
      unfold Lemma613OFloor.phase3BiasedMainCount
        majorityBiasedCount Phase7Convergence.minorityU at ih ⊢
      rw [Multiset.countP_cons, Multiset.countP_cons,
        Multiset.countP_cons]
      by_cases hb : a.role = Role.main ∧ a.bias ≠ Bias.zero
      · by_cases hm : Phase7Convergence.minoritySt sigma a
        · have hmaj : ¬ majorityBiasedSt sigma a := by
            intro h
            exact h.2.2 hm
          simp [hb, hm, hmaj, ih] <;> omega
        · have hmaj : majorityBiasedSt sigma a := ⟨hb.1, hb.2, hm⟩
          simp [hb, hm, hmaj, ih] <;> omega
      · have hm : ¬ Phase7Convergence.minoritySt sigma a := by
          intro h
          exact hb (minoritySt_implies_biasedMain sigma a h)
        have hmaj : ¬ majorityBiasedSt sigma a := fun h => hb ⟨h.1, h.2.1⟩
        simp [hb, hm, hmaj, ih] <;> omega

private theorem countP_le_of_imp
    {α : Type*} (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (c : Multiset α) (h : ∀ a, P a → Q a) :
    Multiset.countP P c ≤ Multiset.countP Q c := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a c ih =>
      rw [Multiset.countP_cons, Multiset.countP_cons]
      by_cases hp : P a
      · rw [if_pos hp, if_pos (h a hp)]
        omega
      · rw [if_neg hp]
        split_ifs <;> omega

private theorem majorityBiased_of_mem_majorityBand
    (sigma : Sign) (ell : Fin (L + 1)) (a : AgentState L K)
    (h : a ∈ majorityBand3 (L := L) (K := K) sigma ell.val) :
    majorityBiasedSt sigma a := by
  rw [majorityBand3, Finset.mem_filter] at h
  obtain ⟨_, hm, s, j, hs, hb, _, _⟩ := h
  refine ⟨hm, by rw [hb]; simp, ?_⟩
  rintro ⟨_, k, hk⟩
  rw [hb] at hk
  injection hk with hsign _
  exact hs hsign

/-- The fixed block is part of the majority pool: `A ≥ Q`. -/
theorem majorityBlockCount_le_majorityBiasedCount
    (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K)) :
    majorityBlockCount sigma ell.val c ≤ majorityBiasedCount sigma c := by
  classical
  unfold majorityBlockCount majorityBiasedCount
  exact countP_le_of_imp _ _ c
    (fun a h => majorityBiased_of_mem_majorityBand sigma ell a h)

/-- On a homogeneous Phase-8 configuration, each block agent is either
available or counted by `F₈`: `Q ≤ A_avail + F₈`. -/
theorem majorityBlockCount_le_available_add_full
    (sigma : Sign) (ell : Fin (L + 1))
    {population : ℕ} {c : Config (AgentState L K)}
    (hEight : PhaseOnlyWindows.Phase8Win (L := L) (K := K) population c) :
    majorityBlockCount sigma ell.val c ≤
      availableMajorityCount sigma c + phaseEightFullCount c := by
  classical
  induction c using Multiset.induction_on generalizing population with
  | empty => simp [majorityBlockCount, availableMajorityCount,
      phaseEightFullCount]
  | cons a c ih =>
      have haEight := hEight.2 a (by simp)
      have hcEight : PhaseOnlyWindows.Phase8Win
          (L := L) (K := K) c.card c :=
        ⟨rfl, fun b hb => hEight.2 b (by simp [hb])⟩
      have ih' := ih hcEight
      unfold majorityBlockCount availableMajorityCount
        phaseEightFullCount at ih' ⊢
      rw [Multiset.countP_cons, Multiset.countP_cons,
        Multiset.countP_cons]
      by_cases hq : a ∈ majorityBand3
          (L := L) (K := K) sigma ell.val
      · have hmaj := majorityBiased_of_mem_majorityBand sigma ell a hq
        by_cases hf : a.full
        · have hfull : phaseEightFullSt a := ⟨haEight, hmaj.1, hf⟩
          have havail : ¬ availableMajoritySt sigma a :=
            fun h => h.2 hf
          simp [hq, hfull, havail]
          omega
        · have havail : availableMajoritySt sigma a := ⟨hmaj, hf⟩
          have hfull : ¬ phaseEightFullSt a := fun h => hf h.2.2
          simp [hq, hfull, havail]
          omega
      · simp [hq]
        omega

/-- Removing the nonnegative debt terms from (54). -/
private theorem latePhaseEightCredit_le_core
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K)) :
    latePhaseEightCredit sigma ell hell c ≤
      2 * (majorityBlockCount sigma ell.val c : ℤ) -
        (Lemma613OFloor.phase3BiasedMainCount c : ℤ) -
        (phaseEightFullCount c : ℤ) := by
  unfold latePhaseEightCredit lateBiasedResourceCredit phaseSixCharge
  omega

/-- Algebraic equation (56): `A_avail - B₋ ≥ J₈`. -/
theorem latePhaseEightCredit_le_availableExcess
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {population : ℕ} {c : Config (AgentState L K)}
    (hEight : PhaseOnlyWindows.Phase8Win (L := L) (K := K) population c) :
    latePhaseEightCredit sigma ell hell c ≤
      (availableMajorityCount sigma c : ℤ) -
        (Phase7Convergence.minorityU sigma c : ℤ) := by
  have hcore := latePhaseEightCredit_le_core sigma ell hell c
  have hpart := biasedMainCount_eq_majority_add_minority sigma c
  have hQA := majorityBlockCount_le_majorityBiasedCount sigma ell c
  have hQAF := majorityBlockCount_le_available_add_full
    sigma ell hEight
  have hpartZ :
      (Lemma613OFloor.phase3BiasedMainCount c : ℤ) =
        (majorityBiasedCount sigma c : ℤ) +
          (Phase7Convergence.minorityU sigma c : ℤ) := by
    exact_mod_cast hpart
  have hQAZ :
      (majorityBlockCount sigma ell.val c : ℤ) ≤
        (majorityBiasedCount sigma c : ℤ) := by exact_mod_cast hQA
  have hQAFZ :
      (majorityBlockCount sigma ell.val c : ℤ) ≤
        (availableMajorityCount sigma c : ℤ) +
          (phaseEightFullCount c : ℤ) := by exact_mod_cast hQAF
  omega

/-- Scaled `.26112 n` availability. -/
theorem phaseEightAvailability_scaled
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {population mainCount : ℕ} {c : Config (AgentState L K)}
    (hpopulation : 1 ≤ population)
    (hmain : 12 * population ≤ 25 * mainCount)
    (hEight : PhaseOnlyWindows.Phase8Win
      (L := L) (K := K) population c)
    (hcredit : (544 : ℤ) * (mainCount : ℤ) ≤
      1000 * latePhaseEightCredit sigma ell hell c) :
    Phase7Convergence.minorityU sigma c ≤
        availableMajorityCount sigma c ∧
      26112 * population ≤
        100000 * (availableMajorityCount sigma c -
          Phase7Convergence.minorityU sigma c) := by
  let A := availableMajorityCount sigma c
  let B := Phase7Convergence.minorityU sigma c
  have hcreditExcess :
      (544 : ℤ) * (mainCount : ℤ) ≤
        1000 * ((A : ℤ) - (B : ℤ)) := by
    exact hcredit.trans
      (mul_le_mul_of_nonneg_left
        (latePhaseEightCredit_le_availableExcess
          sigma ell hell hEight) (by norm_num))
  have hmainZ : (12 : ℤ) * population ≤ 25 * mainCount := by
    exact_mod_cast hmain
  have hscaledZ :
      (26112 : ℤ) * population ≤
        100000 * ((A : ℤ) - (B : ℤ)) := by
    nlinarith
  have hBA : B ≤ A := by
    by_contra hnot
    have hneg : (A : ℤ) - (B : ℤ) < 0 := by
      have := Nat.lt_of_not_ge hnot
      omega
    have hpositive : (0 : ℤ) < 26112 * population := by
      exact mul_pos (by norm_num) (by exact_mod_cast hpopulation)
    nlinarith
  refine ⟨hBA, ?_⟩
  exact_mod_cast hscaledZ

/-- Deterministic Lemma-13 handoff from the Lemma-12 route to a homogeneous
Phase-8 endpoint. -/
theorem lemmaThirteen_availability_of_route
    {init : InputCfg n} {omega : InputLog n}
    {completed seven homogeneous eight M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (hroute : LemmaTwelveRouteReceipt (M := M) (R := R)
      init omega completed seven homogeneous eight ell hell sigma tau)
    (hDeep : AllMinorityIndicesAbove sigma ell (trace init omega eight))
    {d : InputCfg n}
    (hreach : PhaseSevenEightCreditReachable init
      (trace init omega eight) d)
    (hEight : PhaseOnlyWindows.Phase8Win
      (L := PhaseThreeModel.Numeric.hourIndex n) (K := 256) n d) :
    NoShallowMain ell d ∧
      AllMinorityIndicesAbove sigma ell d ∧
      (544 : ℤ) * (M : ℤ) ≤
          1000 * latePhaseEightCredit sigma ell hell d ∧
      Phase7Convergence.minorityU sigma d ≤
          availableMajorityCount sigma d ∧
      26112 * n ≤
          100000 * (availableMajorityCount sigma d -
            Phase7Convergence.minorityU sigma d) := by
  have hfloor := latePhaseEightCredit_floor_of_reachable
    hroute hDeep hreach
  have hn : 1 ≤ n := by
    have hnlarge := (time_population_bounds hroute.path.good_input.1).2
    omega
  have havail := phaseEightAvailability_scaled
    sigma ell hell hn hroute.main_lower hEight hfloor.2.2
  exact ⟨hfloor.1, hfloor.2.1, hfloor.2.2,
    havail.1, havail.2⟩

/-!
THEOREM LIST
* `phaseEightFullSt`, `phaseEightFullCount`
* `latePhaseEightCreditAtom`, `latePhaseEightCredit`
* `phaseEightFullCount_firstSeed_eq_zero`
* `absorbConsume_pair_transport`
* `transition_pair_transport_of_phaseSevenOrEight`
* `PhaseSevenEightWindow`, `PhaseSevenEightCreditStep`,
  `PhaseSevenEightCreditReachable`
* `phaseSevenEightCreditStep_preserves`
* `phaseSevenEightCreditReachable_preserves`
* `latePhaseEightCredit_firstSeed`
* `latePhaseEightCredit_floor_of_reachable`
* `majorityBiasedCount`, `availableMajorityCount`
* `biasedMainCount_eq_majority_add_minority`
* `majorityBlockCount_le_majorityBiasedCount`
* `majorityBlockCount_le_available_add_full`
* `latePhaseEightCredit_le_availableExcess`
* `phaseEightAvailability_scaled`
* `lemmaThirteen_availability_of_route`

CLOSES ITEM 1
* Defines literal `F₈` and `J₈ = J - F₈`.
* Proves `F₈ = 0` at the exact first Phase-8 seed from the retained Lemma-12
  route.  The preceding configuration is pure Phase 7; a newly created
  Phase-8 output is a Clock, never a Main.
* Therefore the first-seed `J₈` is exactly Lemma 11's `J` and inherits the
  scaled `.544 M` floor.

CLOSES ITEM 2
* Uses the actual `Transition`, not an abstract invented chain.
* Carries the corrected invariant “every minority index is `> ell+2`”; the
  Phase-7 gap-two copy may raise the count but cannot move a minority shallower.
* Exhausts the two firing orientations of `absorbConsume`.  In either firing,
  the consumed victim has `J`-atom at most `-1`, exactly paying the new full
  absorber; any additional minority debt removal strictly raises `J₈`.
* Proves `J₈` nondecreasing through the source-guarded mixed 7/8 relation and
  homogeneous Phase 8.

CLOSES ITEM 3
* Defines all majority-biased Mains `A` and available majority Mains
  `A_avail`.
* Proves `V = A + B₋`, `A ≥ Q`, and on a homogeneous Phase-8 configuration
  `A_avail + F₈ ≥ Q`.
* Concludes `A_avail - B₋ ≥ J₈ ≥ .544 M ≥ .26112 n`, in the exact natural
  scaling `26112*n ≤ 100000*(A_avail-B₋)`.

CARRIED PREMISES AND PRODUCERS
* `LemmaTwelveRouteReceipt`: produced in the library by
  `exists_lemmaTwelveRouteReceipt_of_not_producerFailure`; it supplies the
  synchronized Lemma-11 path, strict Phase-8 protection, and
  `12*n ≤ 25*M`.
* `AllMinorityIndicesAbove` at the first Phase-8 seed: produced in the library by
  `phaseSevenBands_clear_at_firstEight`, and returned by
  `lemmaTwelve_smallGap` outside `lemmaTwelveFailure`.
* `PhaseSevenEightCreditReachable`: a concrete finite source-guarded relation
  on one execution path; no premise ranges over all logs or arbitrary
  configurations.  The trace adapter producing this relation up to the first
  homogeneous Phase-8 time belongs to later probabilistic/timing files.
* `Phase8Win n d`: the homogeneous Phase-8 endpoint supplied by the Phase-8
  threshold-spread/timer route in the later Lemma-13 assembly.

UNFINISHED
* The original-law constructor of the mixed-7/8 route and its finite
  homogeneous Phase-8 endpoint.
* The one-step scheduler hazard, the `ceil(8 n ln n)` multiplicative drain,
  and the probability `n^(-3.17792)` in equation (57).
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateLemmaThirteenDeterministic

end
