-- Ripple/PopulationProtocol/ExactMajority/Probability/LateBiasedResourceCreditPhaseSix.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateBiasedResourceCredit
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixReachableWf

/-!
# Phase-6 transport of the Lemma-11 credit

Theorem list:
* `doSplit_charge_block_pair`
* `doSplit_atom_pair_mono`
* `Phase6Transition_atom_pair_mono`
* `Transition_atom_pair_mono_of_phaseSixDispatch`
* `ReachablePhaseSixWindow.of_mixedFiveSix`
* `ReachablePhaseSixWindow.of_phaseSixToSeven`
* `reachablePhaseSixWindow_wf`
* `reachablePhaseSixWindow_step`
* `phaseSixStep_credit_mono`
* `phaseSixStep_preserves_window_and_credit`

Covers actual Phase-6 dispatches.  Phase-7 cases, pathwise
instances, and consumer forms are intentionally absent.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCreditPhaseSix

open LateBiasedResourceCredit
open Phase7BandDefs
open Phase7MajorityBlockLedger
open Phase6BlockSnapshot
open LateMixedFuelLedger

variable {L K : ℕ}

private theorem agentDebt_of_nonmain
    (i : Fin (L + 1)) (a : AgentState L K) (h : a.role ≠ Role.main) :
    Phase6FuelLedger.agentDebt (L := L) (K := K) i a = 0 := by
  simp [Phase6FuelLedger.agentDebt, h]

private theorem minoritySplitDebtUnit_of_nonmain
    (sigma : Sign) (i : Fin (L + 1)) (a : AgentState L K)
    (h : a.role ≠ Role.main) :
    minoritySplitDebtUnit (L := L) (K := K) sigma i a = 0 := by
  unfold minoritySplitDebtUnit
  cases hb : a.bias with
  | zero => rfl
  | dyadic s j =>
      simp only
      split_ifs
      · exact agentDebt_of_nonmain i a h
      · rfl

private theorem minoritySplitDebtUnit_of_dyadic
    (sigma s : Sign) (i j : Fin (L + 1)) (a : AgentState L K)
    (hb : a.bias = Bias.dyadic s j) :
    minoritySplitDebtUnit (L := L) (K := K) sigma i a =
      if s = sigma then Phase6FuelLedger.agentDebt (L := L) (K := K) i a
      else 0 := by
  unfold minoritySplitDebtUnit
  rw [hb]

private theorem biasedMainUnit_main_dyadic
    (a : AgentState L K) (s : Sign) (j : Fin (L + 1))
    (hm : a.role = Role.main) (hb : a.bias = Bias.dyadic s j) :
    biasedMainUnit (L := L) (K := K) a = 1 := by
  unfold biasedMainUnit
  rw [if_pos]
  rw [hb]
  exact ⟨hm, by simp⟩

private theorem biasedMainUnit_nonmain
    (a : AgentState L K) (hm : a.role ≠ Role.main) :
    biasedMainUnit (L := L) (K := K) a = 0 := by
  unfold biasedMainUnit
  rw [if_neg]
  exact fun h => hm h.1

/-- Abstract form of the Phase-6 split table: only the facts about the two
outputs that the credit sees are used. -/
private theorem split_core
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (sgn : Sign) (j j1 : Fin (L + 1)) (hj1 : j1.val = j.val + 1)
    (r m r' m' : AgentState L K)
    (hr : r.role = Role.reserve) (hm : m.role = Role.main)
    (hb : m.bias = Bias.dyadic sgn j) (hgt : r.hour.val > j.val)
    (hr'r : r'.role = Role.main) (hr'b : r'.bias = Bias.dyadic sgn j1)
    (hm'r : m'.role = Role.main) (hm'b : m'.bias = Bias.dyadic sgn j1)
    (hDk : Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) r' +
        Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) m' ≤
      Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) r +
        Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) m)
    (hDk' : j.val < ell.val + 2 →
      Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) r' +
        Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) m' + 1 =
      Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) r +
        Phase6FuelLedger.agentDebt (L := L) (K := K)
          (middleIndex ell hell) m)
    (hDl : Phase6FuelLedger.agentDebt (L := L) (K := K) ell r' +
        Phase6FuelLedger.agentDebt (L := L) (K := K) ell m' ≤
      Phase6FuelLedger.agentDebt (L := L) (K := K) ell r +
        Phase6FuelLedger.agentDebt (L := L) (K := K) ell m)
    (hDl' : j.val < ell.val →
      Phase6FuelLedger.agentDebt (L := L) (K := K) ell r' +
        Phase6FuelLedger.agentDebt (L := L) (K := K) ell m' + 1 =
      Phase6FuelLedger.agentDebt (L := L) (K := K) ell r +
        Phase6FuelLedger.agentDebt (L := L) (K := K) ell m) :
    2 * (majorityBlockUnit sigma ell.val r +
          majorityBlockUnit sigma ell.val m) +
        (phaseSixChargeUnit sigma ell hell r' +
          phaseSixChargeUnit sigma ell hell m') ≤
      2 * (majorityBlockUnit sigma ell.val r' +
          majorityBlockUnit sigma ell.val m') +
        (phaseSixChargeUnit sigma ell hell r +
          phaseSixChargeUnit sigma ell hell m) := by
  have hrne : r.role ≠ Role.main := by rw [hr]; decide
  have hrne' : r.role ≠ Role.reserve → False := fun h => h hr
  have hMr : majorityBlockUnit (L := L) (K := K) sigma ell.val r = 0 :=
    majorityBlockUnit_of_role_ne_main sigma ell.val r hrne
  have hMm := majorityBlockUnit_main_dyadic (L := L) (K := K)
    sigma sgn ell.val j m hm hb
  have hMr' := majorityBlockUnit_main_dyadic (L := L) (K := K)
    sigma sgn ell.val j1 r' hr'r hr'b
  have hMm' := majorityBlockUnit_main_dyadic (L := L) (K := K)
    sigma sgn ell.val j1 m' hm'r hm'b
  have hBr := biasedMainUnit_nonmain (L := L) (K := K) r hrne
  have hBm := biasedMainUnit_main_dyadic (L := L) (K := K) m sgn j hm hb
  have hBr' := biasedMainUnit_main_dyadic (L := L) (K := K) r' sgn j1 hr'r hr'b
  have hBm' := biasedMainUnit_main_dyadic (L := L) (K := K) m' sgn j1 hm'r hm'b
  have hEr := minoritySplitDebtUnit_of_nonmain (L := L) (K := K)
    sigma (middleIndex ell hell) r hrne
  have hEm := minoritySplitDebtUnit_of_dyadic (L := L) (K := K)
    sigma sgn (middleIndex ell hell) j m hb
  have hEr' := minoritySplitDebtUnit_of_dyadic (L := L) (K := K)
    sigma sgn (middleIndex ell hell) j1 r' hr'b
  have hEm' := minoritySplitDebtUnit_of_dyadic (L := L) (K := K)
    sigma sgn (middleIndex ell hell) j1 m' hm'b
  have hAr := agentDebt_of_nonmain (L := L) (K := K) ell r hrne
  have hAr2 := agentDebt_of_nonmain (L := L) (K := K) (middleIndex ell hell) r hrne
  have hSr := dangerousReserveUnit_of_role_reserve (L := L) (K := K)
    ell.val r hr
  have hSm : dangerousReserveUnit (L := L) (K := K) ell.val m = 0 :=
    dangerousReserveUnit_of_role_ne_reserve ell.val m (by rw [hm]; decide)
  have hSr' : dangerousReserveUnit (L := L) (K := K) ell.val r' = 0 :=
    dangerousReserveUnit_of_role_ne_reserve ell.val r' (by rw [hr'r]; decide)
  have hSm' : dangerousReserveUnit (L := L) (K := K) ell.val m' = 0 :=
    dangerousReserveUnit_of_role_ne_reserve ell.val m' (by rw [hm'r]; decide)
  unfold phaseSixChargeUnit
  rw [hMr, hBr, hEr, hAr, hSr, hMm, hMr', hMm', hBm, hBr', hBm', hEm, hEr', hEm',
    hSm, hSr', hSm']
  have hk : (middleIndex ell hell).val = ell.val + 2 := rfl
  by_cases hs : sgn = sigma
  · subst hs
    simp only [ne_eq, not_true_eq_false, false_and, if_false, if_true]
    split_ifs <;> omega
  · simp only [ne_eq, hs, not_false_eq_true, true_and, if_false]
    rw [hj1] at *
    split_ifs <;> omega

/-- The Phase-6 split table, before adding the separately monotone `Dminus`.
The subtraction-free orientation is equivalent to monotonicity of
`2 Q - V - Eminus - Dhigh - 3 Sbad`. -/
theorem doSplit_charge_block_pair
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (r m : AgentState L K)
    (hr : r.role = Role.reserve) (hm : m.role = Role.main) :
    2 * (majorityBlockUnit sigma ell.val r +
          majorityBlockUnit sigma ell.val m) +
        (phaseSixChargeUnit sigma ell hell (doSplit L K r m).1 +
          phaseSixChargeUnit sigma ell hell (doSplit L K r m).2) ≤
      2 * (majorityBlockUnit sigma ell.val (doSplit L K r m).1 +
          majorityBlockUnit sigma ell.val (doSplit L K r m).2) +
        (phaseSixChargeUnit sigma ell hell r +
          phaseSixChargeUnit sigma ell hell m) := by
  classical
  by_cases happ : Phase6Convergence.DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨sgn, j, hb, hne, hgt, hlt⟩ := happ
    have happly := Phase6Convergence.doSplit_apply
      (L := L) (K := K) r m hb hne hgt hlt
    have hDle : ∀ i : Fin (L + 1),
        Phase6FuelLedger.agentDebt (L := L) (K := K) i (doSplit L K r m).1 +
          Phase6FuelLedger.agentDebt (L := L) (K := K) i (doSplit L K r m).2 ≤
        Phase6FuelLedger.agentDebt (L := L) (K := K) i r +
          Phase6FuelLedger.agentDebt (L := L) (K := K) i m :=
      fun i => Phase6FuelLedger.doSplit_agentDebt_pair_le
        (L := L) (K := K) i r m hr hm
    have hDdrop : ∀ i : Fin (L + 1), j.val < i.val →
        Phase6FuelLedger.agentDebt (L := L) (K := K) i (doSplit L K r m).1 +
          Phase6FuelLedger.agentDebt (L := L) (K := K) i (doSplit L K r m).2 + 1 =
        Phase6FuelLedger.agentDebt (L := L) (K := K) i r +
          Phase6FuelLedger.agentDebt (L := L) (K := K) i m :=
      fun i hji => Phase6FuelLedger.doSplit_agentDebt_pair_drop
        (L := L) (K := K) i r m hr hm hb hne hgt hlt hji
    have hout1 : (doSplit L K r m).1.role = Role.main := by rw [happly]
    have hout1b : (doSplit L K r m).1.bias =
        Bias.dyadic sgn ⟨j.val + 1, by omega⟩ := by rw [happly]
    have hout2 : (doSplit L K r m).2.role = Role.main := by rw [happly]; exact hm
    have hout2b : (doSplit L K r m).2.bias =
        Bias.dyadic sgn ⟨j.val + 1, by omega⟩ := by rw [happly]
    exact split_core sigma ell hell sgn j ⟨j.val + 1, by omega⟩ rfl
      r m _ _ hr hm hb hgt hout1 hout1b hout2 hout2b
      (hDle _)
      (fun h => hDdrop (middleIndex ell hell) (by rw [middleIndex_val]; exact h))
      (hDle _) (fun h => hDdrop ell h)
  · rw [Phase6Convergence.doSplit_eq_self_of_not_applicable
      (L := L) (K := K) r m happ]

/-- Add the independently non-increasing `Dminus` term. -/
theorem doSplit_atom_pair_mono
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (r m : AgentState L K)
    (hr : r.role = Role.reserve) (hm : m.role = Role.main) :
    lateBiasedResourceAtom sigma ell hell r +
        lateBiasedResourceAtom sigma ell hell m ≤
      lateBiasedResourceAtom sigma ell hell (doSplit L K r m).1 +
        lateBiasedResourceAtom sigma ell hell (doSplit L K r m).2 := by
  have hcore := doSplit_charge_block_pair sigma ell hell r m hr hm
  have hdebt := doSplit_minorityDebt_pair_le sigma ell.val r m hr hm
  have hcoreInt :
      (2 * (majorityBlockUnit sigma ell.val r +
          majorityBlockUnit sigma ell.val m) +
        (phaseSixChargeUnit sigma ell hell (doSplit L K r m).1 +
          phaseSixChargeUnit sigma ell hell (doSplit L K r m).2) : ℤ) ≤
      (2 * (majorityBlockUnit sigma ell.val (doSplit L K r m).1 +
          majorityBlockUnit sigma ell.val (doSplit L K r m).2) +
        (phaseSixChargeUnit sigma ell hell r +
          phaseSixChargeUnit sigma ell hell m) : ℤ) := by
    exact_mod_cast hcore
  have hdebtInt :
      (minorityDebtUnit sigma ell.val (doSplit L K r m).1 +
          minorityDebtUnit sigma ell.val (doSplit L K r m).2 : ℤ) ≤
        (minorityDebtUnit sigma ell.val r +
          minorityDebtUnit sigma ell.val m : ℤ) := by
    exact_mod_cast hdebt
  unfold lateBiasedResourceAtom
  push_cast at hcoreInt hdebtInt ⊢
  omega

private theorem clockBranch_atom_eq
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    lateBiasedResourceAtom sigma ell hell
        (if a.role = Role.clock then stdCounterSubroutine L K a else a) =
      lateBiasedResourceAtom sigma ell hell a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    have hout : (stdCounterSubroutine L K a).role = Role.clock := by
      rw [Phase6Convergence.stdCounterSubroutine_role_ge_five6
        (L := L) (K := K) a ha, hc]
    rw [lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
          sigma ell hell (stdCounterSubroutine L K a)
          (by rw [hout]; decide) (by rw [hout]; decide),
      lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
          sigma ell hell a (by rw [hc]; decide) (by rw [hc]; decide)]
  · rw [if_neg hc]

/-- Full Phase-6 work transition, including the trailing clock update. -/
theorem Phase6Transition_atom_pair_mono
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : 6 ≤ s.phase.val) (ht : 6 ≤ t.phase.val) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Phase6Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Phase6Transition L K s t).2 := by
  unfold Phase6Transition
  simp only
  set sWork :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).1
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).2
    else s) with hsWork
  set tWork :=
    (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).2
    else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).1
    else t) with htWork
  have hwork :
      lateBiasedResourceAtom sigma ell hell s +
          lateBiasedResourceAtom sigma ell hell t ≤
        lateBiasedResourceAtom sigma ell hell sWork +
          lateBiasedResourceAtom sigma ell hell tWork := by
    rw [hsWork, htWork]
    split_ifs with hleft hright
    · exact doSplit_atom_pair_mono sigma ell hell s t
        hleft.1 hleft.2.1
    · have h := doSplit_atom_pair_mono sigma ell hell t s
        hright.1 hright.2.1
      omega
    · exact le_rfl
  have hsPhase : 6 ≤ sWork.phase.val := by
    rw [hsWork]
    split_ifs with hleft hright
    · rw [Phase6Convergence.doSplit_phase_fst_eq
        (L := L) (K := K) s t]
      exact hs
    · rw [Phase6Convergence.doSplit_phase_snd_eq
        (L := L) (K := K) t s]
      exact hs
    · exact hs
  have htPhase : 6 ≤ tWork.phase.val := by
    rw [htWork]
    split_ifs with hleft hright
    · rw [Phase6Convergence.doSplit_phase_snd_eq
        (L := L) (K := K) s t]
      exact ht
    · rw [Phase6Convergence.doSplit_phase_fst_eq
        (L := L) (K := K) t s]
      exact ht
    · exact ht
  rw [clockBranch_atom_eq sigma ell hell sWork (by omega),
    clockBranch_atom_eq sigma ell hell tWork (by omega)]
  exact hwork

private theorem Transition_atom_pair_mono_of_five_six
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 6) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
  have hT := Transition_eq_Phase6Transition_of_five_six s t hs ht
  have hsSix : 6 ≤ (phaseSixEntry (L := L) (K := K) s).phase.val := by
    rw [phaseSixEntry_phase (L := L) (K := K) s]
  have htSix : 6 ≤
      ({t with phase := ⟨6, by decide⟩} : AgentState L K).phase.val := by
    exact le_rfl
  have h := Phase6Transition_atom_pair_mono sigma ell hell
    (phaseSixEntry (L := L) (K := K) s)
    ({t with phase := ⟨6, by decide⟩} : AgentState L K) hsSix htSix
  have e1 := lateBiasedResourceAtom_phaseSixEntry_eq sigma ell hell s
  have e2 := lateBiasedResourceAtom_set_phase_eq sigma ell hell t
    (⟨6, by decide⟩ : Fin 11)
  rw [hT]
  linarith

private theorem Transition_atom_pair_mono_of_six_five
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 5) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
  have hT := Transition_eq_Phase6Transition_of_six_five s t hs ht
  have hsSix : 6 ≤
      ({s with phase := ⟨6, by decide⟩} : AgentState L K).phase.val := by
    exact le_rfl
  have htSix : 6 ≤ (phaseSixEntry (L := L) (K := K) t).phase.val := by
    rw [phaseSixEntry_phase (L := L) (K := K) t]
  have h := Phase6Transition_atom_pair_mono sigma ell hell
    ({s with phase := ⟨6, by decide⟩} : AgentState L K)
    (phaseSixEntry (L := L) (K := K) t) hsSix htSix
  have e1 := lateBiasedResourceAtom_phaseSixEntry_eq sigma ell hell t
  have e2 := lateBiasedResourceAtom_set_phase_eq sigma ell hell s
    (⟨6, by decide⟩ : Fin 11)
  rw [hT]
  linarith

private theorem Transition_atom_pair_mono_of_six_six
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
  rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
    (L := L) (K := K) s t hs ht]
  exact Phase6Transition_atom_pair_mono sigma ell hell s t
    (by omega) (by omega)

/-- Exactly the pairs whose actual dispatcher executes Phase 6 in a late seam. -/
inductive PhaseSixDispatchPair (s t : AgentState L K) : Prop
  | five_six (hs : s.phase.val = 5) (ht : t.phase.val = 6)
  | six_five (hs : s.phase.val = 6) (ht : t.phase.val = 5)
  | six_six (hs : s.phase.val = 6) (ht : t.phase.val = 6)

/-- Pairwise transport for the actual Lean `Transition`. -/
theorem Transition_atom_pair_mono_of_phaseSixDispatch
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K) (hpair : PhaseSixDispatchPair s t) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
  cases hpair with
  | five_six hs ht =>
      exact Transition_atom_pair_mono_of_five_six sigma ell hell s t hs ht
  | six_five hs ht =>
      exact Transition_atom_pair_mono_of_six_five sigma ell hell s t hs ht
  | six_six hs ht =>
      exact Transition_atom_pair_mono_of_six_six sigma ell hell s t hs ht

/-- Reachability plus the combined mixed-5/6 and mixed-6/7 phase envelope. -/
structure ReachablePhaseSixWindow
    (init c : Config (AgentState L K)) : Prop where
  reachable : (NonuniformMajority L K).Reachable init c
  phase_range : ∀ a ∈ c, 5 ≤ a.phase.val ∧ a.phase.val ≤ 7

namespace ReachablePhaseSixWindow

/-- The existing mixed-5/6 window embeds in the common reachable invariant. -/
theorem of_mixedFiveSix
    {init c : Config (AgentState L K)} {n : ℕ}
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hwin : MixedFiveSixWin n c) :
    ReachablePhaseSixWindow init c := by
  refine ⟨hreach, ?_⟩
  intro a ha
  rcases hwin.2 a ha with h | h <;> omega

/-- The existing mixed-6/7 window embeds in the same invariant. -/
theorem of_phaseSixToSeven
    {init c : Config (AgentState L K)}
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hwin : Phase6To7Window (L := L) (K := K) c) :
    ReachablePhaseSixWindow init c := by
  refine ⟨hreach, ?_⟩
  intro a ha
  rcases hwin a ha with h | h <;> omega

end ReachablePhaseSixWindow

/-- The reachable envelope supplies the existing `AdvanceNoOvershoot.Wf`. -/
theorem reachablePhaseSixWindow_wf
    {init c : Config (AgentState L K)}
    (hvalid : validInitial init)
    (hwin : ReachablePhaseSixWindow init c) :
    AdvanceNoOvershoot.Wf c := by
  apply LateMixedFiveSixReachableWf.wf_of_reachable_phase_range
    hvalid hwin.reachable
  · intro a ha
    have h := (hwin.phase_range a ha).1
    omega
  · intro a ha
    have h := (hwin.phase_range a ha).2
    omega

/-- One actual protocol step whose selected pair dispatches Phase 6. -/
inductive PhaseSixStep
    (c cNext : Config (AgentState L K)) : Prop
  | mk (first second : AgentState L K)
    (applicable : Protocol.Applicable c first second)
    (dispatch : PhaseSixDispatchPair first second)
    (result_eq :
      cNext = c - ({first, second} : Config (AgentState L K)) +
        ({(Transition L K first second).1,
          (Transition L K first second).2} : Config (AgentState L K))) :
    PhaseSixStep c cNext

private theorem phaseSixDispatch_inputs_ge_five
    (s t : AgentState L K) (h : PhaseSixDispatchPair s t) :
    5 ≤ s.phase.val ∧ 5 ≤ t.phase.val := by
  cases h with
  | five_six hs ht => omega
  | six_five hs ht => omega
  | six_six hs ht => omega

private theorem phaseSixDispatch_outputs_le_seven
    (s t : AgentState L K) (h : PhaseSixDispatchPair s t) :
    (Transition L K s t).1.phase.val ≤ 7 ∧
      (Transition L K s t).2.phase.val ≤ 7 := by
  cases h with
  | five_six hs ht =>
      rw [Transition_eq_Phase6Transition_of_five_six s t hs ht]
      let sSix := phaseSixEntry (L := L) (K := K) s
      let tSix : AgentState L K := {t with phase := ⟨6, by decide⟩}
      have hsSix : sSix.phase.val = 6 := by
        simpa [sSix] using phaseSixEntry_phase (L := L) (K := K) s
      have htSix : tSix.phase.val = 6 := by simp [tSix]
      exact Phase6Convergence.Phase6Transition_phase_le_seven
        (L := L) (K := K) sSix tSix hsSix htSix
  | six_five hs ht =>
      rw [Transition_eq_Phase6Transition_of_six_five s t hs ht]
      let sSix : AgentState L K := {s with phase := ⟨6, by decide⟩}
      let tSix := phaseSixEntry (L := L) (K := K) t
      have hsSix : sSix.phase.val = 6 := by simp [sSix]
      have htSix : tSix.phase.val = 6 := by
        simpa [tSix] using phaseSixEntry_phase (L := L) (K := K) t
      exact Phase6Convergence.Phase6Transition_phase_le_seven
        (L := L) (K := K) sSix tSix hsSix htSix
  | six_six hs ht =>
      rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
        (L := L) (K := K) s t hs ht]
      exact Phase6Convergence.Phase6Transition_phase_le_seven
        (L := L) (K := K) s t hs ht

/-- The reachable phase envelope is preserved by every actual Phase-6 step. -/
theorem reachablePhaseSixWindow_step
    {init c cNext : Config (AgentState L K)}
    (hwin : ReachablePhaseSixWindow init c)
    (hstep : PhaseSixStep c cNext) :
    ReachablePhaseSixWindow init cNext := by
  rcases hstep with ⟨s, t, happ, hdispatch, rfl⟩
  have hrel :
      (NonuniformMajority L K).StepRel c
        (c - ({s, t} : Config (AgentState L K)) +
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Config (AgentState L K))) :=
    ⟨s, t, happ, rfl⟩
  refine ⟨hwin.reachable.tail hrel, ?_⟩
  have hinputs := phaseSixDispatch_inputs_ge_five s t hdispatch
  have houtputs := phaseSixDispatch_outputs_le_seven s t hdispatch
  have hmono := Transition_phase_monotone (L := L) (K := K) s t
  intro a ha
  rw [Multiset.mem_add] at ha
  rcases ha with hold | hnew
  · exact hwin.phase_range a
      (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) hold)
  · have hnew' : a = (Transition L K s t).1 ∨ a = (Transition L K s t).2 := by
      simpa using hnew
    rcases hnew' with hleft | hright
    · rw [hleft]
      exact ⟨hinputs.1.trans hmono.1, houtputs.1⟩
    · rw [hright]
      exact ⟨hinputs.2.trans hmono.2, houtputs.2⟩

/-- Configuration-level monotonicity, with the reachable source invariant
explicitly quantified as required by the premise rule. -/
theorem phaseSixStep_credit_mono
    {init c cNext : Config (AgentState L K)}
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (_hwin : ReachablePhaseSixWindow init c)
    (hstep : PhaseSixStep c cNext) :
    lateBiasedResourceCredit sigma ell hell c ≤
      lateBiasedResourceCredit sigma ell hell cNext := by
  rcases hstep with ⟨s, t, happ, hdispatch, hresult⟩
  subst cNext
  have hsub : ({s, t} : Config (AgentState L K)) ≤ c := happ
  have hpairAtom := Transition_atom_pair_mono_of_phaseSixDispatch
    sigma ell hell s t hdispatch
  have hpair :
      lateBiasedResourceCredit sigma ell hell
          ({s, t} : Config (AgentState L K)) ≤
        lateBiasedResourceCredit sigma ell hell
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Config (AgentState L K)) := by
    simpa only [lateBiasedResourceCredit_pair] using hpairAtom
  have hadd1 := lateBiasedResourceCredit_add sigma ell hell
    (c - {s, t}) ({s, t} : Config (AgentState L K))
  have hadd2 := lateBiasedResourceCredit_add sigma ell hell
    (c - {s, t})
    ({(Transition L K s t).1, (Transition L K s t).2} :
      Config (AgentState L K))
  have hc : c - {s, t} + ({s, t} : Config (AgentState L K)) = c :=
    tsub_add_cancel_of_le hsub
  rw [hc] at hadd1
  rw [hadd2]
  linarith

/-- The combined induction interface for the pathwise route. -/
theorem phaseSixStep_preserves_window_and_credit
    {init c cNext : Config (AgentState L K)}
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (hwin : ReachablePhaseSixWindow init c)
    (hstep : PhaseSixStep c cNext) :
    ReachablePhaseSixWindow init cNext ∧
      lateBiasedResourceCredit sigma ell hell c ≤
        lateBiasedResourceCredit sigma ell hell cNext := by
  exact ⟨reachablePhaseSixWindow_step hwin hstep,
    phaseSixStep_credit_mono sigma ell hell hwin hstep⟩

end Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCreditPhaseSix
