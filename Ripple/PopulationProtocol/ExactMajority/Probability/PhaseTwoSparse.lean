import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoDrainedSafety
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase3TransitionAlgebra
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStages

/-!
# Sparse mixed mass from the retained drained endpoint

The scalar mass reads integer smallBias before Init-3 and dyadic bias
afterward. Averaging cannot increase its absolute sum; safe initialization
preserves it; Phase-3 cancellation/splitting cannot increase it.
-/

namespace Ripple.PopulationProtocol.ExactMajority.PhaseTwoSparse

open TimeTheorem PhaseTwoProvenance PhaseTwoActivationLocal PhaseTwoActivation

variable {L : ℕ}

def smallValue (b : Fin 7) : ℚ := (b.val : ℚ) - 3

theorem mass_before_three (a : AgentState L 256) (ha : a.phase.val < 3) :
    prePhase4Mass a = smallValue a.smallBias := by
  simp [prePhase4Mass, ha, AgentState.smallBiasInt, smallValue]

theorem mass_after_three (a : AgentState L 256) (ha : 3 ≤ a.phase.val) :
    prePhase4Mass a = Bias.toRat a.bias := by
  simp [prePhase4Mass, show ¬ a.phase.val < 3 from by omega]

theorem averaging_absolute_mass :
    ∀ x y : Fin 7,
      |smallValue (avgFin7 x y).1| + |smallValue (avgFin7 x y).2| ≤
        |smallValue x| + |smallValue y| := by
  intro x y
  have h := PhaseOneDrainStages.avgFin7_mass_pair_le x y
  have h' : (((avgFin7 x y).1.val : ℤ) - 3).natAbs + (((avgFin7 x y).2.val : ℤ) - 3).natAbs ≤
      ((x.val : ℤ) - 3).natAbs + ((y.val : ℤ) - 3).natAbs := h
  have hq : ∀ z : Fin 7, |smallValue z| = ((((z.val : ℤ) - 3).natAbs : ℕ) : ℚ) := by
    intro z
    rw [smallValue, Nat.cast_natAbs]
    push_cast
    rfl
  rw [hq, hq, hq, hq]
  exact_mod_cast h'

theorem init_three_bias_value (a : AgentState L 256)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hzero : a.role ≠ .main → a.smallBias.val = 3) :
    Bias.toRat (phaseInit L 256 ⟨3, by decide⟩ a).bias = smallValue a.smallBias := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases smallBias <;>
    (try norm_num at hsafe) <;> (try norm_num at hzero) <;> (try cases hzero) <;>
    norm_num [phaseInit, smallValue, Bias.toRat]

theorem entry_mass_value (a : AgentState L 256)
    (hentry : Phase3Pre3.Phase3EntryAgent a)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hzero : a.role ≠ .main → a.smallBias.val = 3) :
    prePhase4Mass a = smallValue a.smallBias := by
  rw [mass_after_three a (le_of_eq hentry.1.symm)]
  by_cases hm : a.role = .main
  · rw [Phase3Pre3.main_bias_of_Phase3EntryAgent hentry hm]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
    rcases hsafe with hb | hb | hb <;>
      norm_num [Phase3Pre3.phase3BiasOfSmallBias, hb, smallValue, Bias.toRat]
  · rw [Phase3Pre3.nonMain_bias_zero_of_Phase3EntryAgent hentry hm]
    simp [Bias.toRat, smallValue, hzero hm]

theorem pending_mass_eq (before after : AgentState L 256)
    (hbefore : before.phase.val ≤ 2) (hafter : after.phase.val ≤ 3)
    (hrole : after.role = before.role) (hsmall : after.smallBias = before.smallBias)
    (hsafe : before.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hzero : before.role ≠ .main → before.smallBias.val = 3)
    (hfresh : after.phase.val = 3 → Phase3Pre3.Phase3EntryAgent after) :
    prePhase4Mass after = prePhase4Mass before := by
  rw [mass_before_three before (by omega)]
  by_cases hp : after.phase.val = 3
  · have hsafeAfter : after.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      simpa only [hsmall] using hsafe
    have hzeroAfter : after.role ≠ .main → after.smallBias.val = 3 := by
      intro hm
      have hmBefore : before.role ≠ .main := by simpa only [hrole] using hm
      simpa only [hsmall] using hzero hmBefore
    rw [entry_mass_value after (hfresh hp) hsafeAfter hzeroAfter, hsmall]
  · rw [mass_before_three after (by omega), hsmall]

theorem enter_three_mass_eq (a : AgentState L 256)
    (ha : 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hzero : a.role ≠ .main → a.smallBias.val = 3) :
    prePhase4Mass (enterThree a) = prePhase4Mass a := by
  have hfields := enter_three_fields a ha
  have hge : 3 ≤ (enterThree a).phase.val := by
    rcases hfields.2.1 with hp | hp <;> omega
  have hcases : a.phase.val = 1 ∨ a.phase.val = 2 ∨ a.phase.val = 3 := by omega
  rcases hcases with hone | htwo | hthree
  · have hlist : (List.range 11).filter
        (fun k => decide (1 < k) && decide (k ≤ 3)) = [2, 3] := by decide
    have heq : enterThree a =
        phaseInit L 256 ⟨3, by decide⟩
          (phaseInit L 256 ⟨2, by decide⟩ {a with phase := ⟨3, by decide⟩}) := by
      simp [enterThree, hone, runInitsBetween, hlist]
    let b := phaseInit L 256 ⟨2, by decide⟩ {a with phase := ⟨3, by decide⟩}
    have hbsmall : b.smallBias = a.smallBias := by
      simp only [b, phaseInit_smallBias_eq]
    have hbrole : b.role = a.role := by simp [b, phaseInit_role]
    have hbsafe : b.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      simpa only [hbsmall] using hsafe
    have hbzero : b.role ≠ .main → b.smallBias.val = 3 := by
      intro hm
      have hm' : a.role ≠ .main := by simpa only [hbrole] using hm
      simpa only [hbsmall] using hzero hm'
    rw [mass_after_three (enterThree a) hge, heq, mass_before_three a (by omega)]
    simpa only [b, phaseInit_smallBias_eq] using init_three_bias_value b hbsafe hbzero
  · have hlist : (List.range 11).filter
        (fun k => decide (2 < k) && decide (k ≤ 3)) = [3] := by decide
    have heq : enterThree a =
        phaseInit L 256 ⟨3, by decide⟩ {a with phase := ⟨3, by decide⟩} := by
      simp [enterThree, htwo, runInitsBetween, hlist]
    rw [mass_after_three (enterThree a) hge, heq, mass_before_three a (by omega)]
    exact init_three_bias_value {a with phase := ⟨3, by decide⟩} hsafe hzero
  · have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext hthree
    have heq : enterThree a = a := by
      unfold enterThree
      rw [hthree, runInitsBetween_self]
      cases a
      simp_all
    rw [heq]

theorem epidemic_three_mass_eq (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hmax : max s.phase.val t.phase.val = 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hszero : s.role ≠ .main → s.smallBias.val = 3)
    (htzero : t.role ≠ .main → t.smallBias.val = 3) :
    prePhase4Mass (phaseEpidemicUpdate L 256 s t).1 = prePhase4Mass s ∧
      prePhase4Mass (phaseEpidemicUpdate L 256 s t).2 = prePhase4Mass t := by
  have hmaxFin : max s.phase t.phase = ⟨3, by decide⟩ := Fin.ext hmax
  let a := enterThree s
  let b := enterThree t
  have ha := enter_three_mass_eq s hs hssafe hszero
  have hb := enter_three_mass_eq t ht htsafe htzero
  have haf := enter_three_fields s hs
  have hbf := enter_three_fields t ht
  have hage : 3 ≤ a.phase.val := by
    show 3 ≤ (enterThree s).phase.val
    rcases haf.2.1 with hp | hp <;> omega
  have hbge : 3 ≤ b.phase.val := by
    show 3 ≤ (enterThree t).phase.val
    rcases hbf.2.1 with hp | hp <;> omega
  have hma : prePhase4Mass (phase10EpidemicEntry L 256 s a) = prePhase4Mass a := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) s a (by omega)
    rw [mass_after_three (phase10EpidemicEntry L 256 s a) (by omega),
      mass_after_three a hage]
    simp only [phase10EpidemicEntry_bias]
  have hmb : prePhase4Mass (phase10EpidemicEntry L 256 t b) = prePhase4Mass b := by
    have hp := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := 256) t b (by omega)
    rw [mass_after_three (phase10EpidemicEntry L 256 t b) (by omega),
      mass_after_three b hbge]
    simp only [phase10EpidemicEntry_bias]
  have hepi : phaseEpidemicUpdate L 256 s t =
      if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (a.phase.val = 10 ∨ b.phase.val = 10) then
        (phase10EpidemicEntry L 256 s a, phase10EpidemicEntry L 256 t b)
      else (a, b) := by
    unfold phaseEpidemicUpdate
    rw [hmaxFin]
    rfl
  rw [hepi]
  split_ifs
  · exact ⟨hma.trans ha, hmb.trans hb⟩
  · exact ⟨ha, hb⟩

theorem dyadic_mass_eq_abs (a : AgentState L 256) :
    P3DeterministicAlgebra.agentMassQ a = |Bias.toRat a.bias| := by
  cases hb : a.bias with
  | zero =>
      simp [P3DeterministicAlgebra.agentMassQ, P3DeterministicAlgebra.biasMassQ,
        P3DeterministicAlgebra.biasPosMassQ, P3DeterministicAlgebra.biasNegMassQ,
        Bias.toRat, hb]
  | dyadic sigma i =>
      have hp : (0 : ℚ) ≤ 2 ^ i.val := by positivity
      cases sigma <;>
        simp [P3DeterministicAlgebra.agentMassQ, P3DeterministicAlgebra.biasMassQ,
          P3DeterministicAlgebra.biasPosMassQ, P3DeterministicAlgebra.biasNegMassQ,
          P3DeterministicAlgebra.weightQ, Bias.toRat, hb, abs_div, abs_of_nonneg hp]

theorem phase_one_absolute_mass (s t : AgentState L 256)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    |prePhase4Mass (Transition L 256 s t).1| +
        |prePhase4Mass (Transition L 256 s t).2| ≤
      |prePhase4Mass s| + |prePhase4Mass t| := by
  by_cases hmm : s.role = .main ∧ t.role = .main
  · rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs ht hmm.1 hmm.2]
    simpa [prePhase4Mass, AgentState.smallBiasInt, smallValue, hs, ht] using
      averaging_absolute_mass s.smallBias t.smallBias
  · have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1 s t hs ht
    have hpa : s.phase = ⟨1, by decide⟩ := Fin.ext hs
    have hactual : Transition L 256 s t =
        (finishPhase10Entry L 256 s (Phase1Transition L 256 s t).1,
         finishPhase10Entry L 256 t (Phase1Transition L 256 s t).2) := by
      unfold Transition
      rw [hepi]
      simp only [hpa]
    have hlocal := PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main s t hmm
    have hleft : (Transition L 256 s t).1.smallBias = s.smallBias := by
      rw [hactual, hlocal]
      simp only [finishPhase10Entry_smallBias, clockCounterStep_smallBias]
    have hright : (Transition L 256 s t).2.smallBias = t.smallBias := by
      rw [hactual, hlocal]
      simp only [finishPhase10Entry_smallBias, clockCounterStep_smallBias]
    have hel : (phaseEpidemicUpdate L 256 s t).1.phase.val < 2 := by
      simpa only [hepi] using (show s.phase.val < 2 from by omega)
    have hlcap := Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
      (L := L) (K := 256) s t hel hlno
    have hrcap := Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
      (L := L) (K := 256) s t hel hrno
    rw [mass_before_three (Transition L 256 s t).1 (by omega),
      mass_before_three (Transition L 256 s t).2 (by omega),
      mass_before_three s (by omega), mass_before_three t (by omega), hleft, hright] <;>
      exact le_rfl

/-- Actual mixed-phase pair nonincrease. No clock-height premise is needed:
the local Phase-3 counter step also preserves dyadic bias. -/
theorem transition_absolute_mass (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (hssafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hszero : s.role ≠ .main → s.smallBias.val = 3)
    (htzero : t.role ≠ .main → t.smallBias.val = 3)
    (hlno : (Transition L 256 s t).1.phase.val ≠ 10)
    (hrno : (Transition L 256 s t).2.phase.val ≠ 10) :
    |prePhase4Mass (Transition L 256 s t).1| +
        |prePhase4Mass (Transition L 256 s t).2| ≤
      |prePhase4Mass s| + |prePhase4Mass t| := by
  by_cases hones : s.phase.val = 1 ∧ t.phase.val = 1
  · exact phase_one_absolute_mass s t hones.1 hones.2 hlno hrno
  by_cases hmax : max s.phase.val t.phase.val ≤ 2
  · have hslo : s.phase.val ≤ 2 := (le_max_left _ _).trans hmax
    have htlo : t.phase.val ≤ 2 := (le_max_right _ _).trans hmax
    have hmaxeq : max s.phase.val t.phase.val = 2 := by omega
    have hmono := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := 256) s t
    have helge := phaseEpidemicUpdate_left_phase_ge_max (L := L) (K := 256) s t
    have hel : (phaseEpidemicUpdate L 256 s t).1.phase.val = 2 := by
      rcases phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := 256) s t hslo htlo with hp | hp
      · omega
      · have hb := (Transition L 256 s t).1.phase.isLt
        omega
    have hleft : (Transition L 256 s t).1.smallBias = s.smallBias :=
      (Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
        (L := L) (K := 256) s t (by omega)).trans
          (phaseEpidemicUpdate_preserves_smallBias L 256 s t).1
    have hright : (Transition L 256 s t).2.smallBias = t.smallBias :=
      (Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
        (L := L) (K := 256) s t (by omega)).trans
          (phaseEpidemicUpdate_preserves_smallBias L 256 s t).2
    have hcap : (Transition L 256 s t).1.phase.val ≤ 3 ∧
        (Transition L 256 s t).2.phase.val ≤ 3 := by
      by_cases hnew : 3 ≤ (Transition L 256 s t).1.phase.val ∨
          3 ≤ (Transition L 256 s t).2.phase.val
      · have h := first_phase_three_pair s t hslo htlo hlno hrno hnew
        exact ⟨le_of_eq h.1.1.1, le_of_eq h.2.1.1⟩
      · omega
    have hroles := PhaseTwoSeedProfile.mixed_transition_roles s t
      ⟨hs.1, hslo⟩ ⟨ht.1, htlo⟩ hcap.1 hcap.2
    have hfreshLeft : (Transition L 256 s t).1.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).1 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno (Or.inl (by omega))).1.1
    have hfreshRight : (Transition L 256 s t).2.phase.val = 3 →
        Phase3Pre3.Phase3EntryAgent (Transition L 256 s t).2 := by
      intro hp
      exact (first_phase_three_pair s t hslo htlo hlno hrno (Or.inr (by omega))).2.1
    rw [pending_mass_eq s _ hslo hcap.1 hroles.1 hleft hssafe hszero hfreshLeft,
      pending_mass_eq t _ htlo hcap.2 hroles.2 hright htsafe htzero hfreshRight] <;>
      exact le_rfl
  · have hmaxeq : max s.phase.val t.phase.val = 3 := by omega
    have hphase := epidemic_three_phases_of_success s t hs ht hmaxeq hlno hrno
    have hmass := epidemic_three_mass_eq s t hs ht hmaxeq hssafe htsafe hszero htzero
    rcases he : phaseEpidemicUpdate L 256 s t with ⟨a, b⟩
    have ha : a.phase.val = 3 := by simpa only [he] using hphase.1
    have hb : b.phase.val = 3 := by simpa only [he] using hphase.2
    have hamass : prePhase4Mass a = prePhase4Mass s := by simpa only [he] using hmass.1
    have hbmass : prePhase4Mass b = prePhase4Mass t := by simpa only [he] using hmass.2
    have hpa : a.phase = ⟨3, by decide⟩ := Fin.ext ha
    have hactual : Transition L 256 s t =
        (finishPhase10Entry L 256 a (Phase3Transition L 256 a b).1,
         finishPhase10Entry L 256 b (Phase3Transition L 256 a b).2) := by
      unfold Transition
      rw [he]
      simp only [hpa]
    have hmono := Phase3Transition_phase_nondec L 256 a b
    have hlge : 3 ≤ (Phase3Transition L 256 a b).1.phase.val := by omega
    have hrge : 3 ≤ (Phase3Transition L 256 a b).2.phase.val := by omega
    have hmleft : prePhase4Mass (Transition L 256 s t).1 =
        Bias.toRat (Phase3Transition L 256 a b).1.bias := by
      rw [hactual]
      rw [mass_after_three
        (finishPhase10Entry L 256 a (Phase3Transition L 256 a b).1)
        (by simpa only [finishPhase10Entry_phase_val] using hlge)]
      simp only [finishPhase10Entry_bias]
    have hmright : prePhase4Mass (Transition L 256 s t).2 =
        Bias.toRat (Phase3Transition L 256 a b).2.bias := by
      rw [hactual]
      rw [mass_after_three
        (finishPhase10Entry L 256 b (Phase3Transition L 256 a b).2)
        (by simpa only [finishPhase10Entry_phase_val] using hrge)]
      simp only [finishPhase10Entry_bias]
    have hpair := P3DeterministicAlgebra.p3_totalMass_pair_le a b ha hb
    rw [hmleft, hmright]
    calc
      |Bias.toRat (Phase3Transition L 256 a b).1.bias| +
          |Bias.toRat (Phase3Transition L 256 a b).2.bias| ≤
          |Bias.toRat a.bias| + |Bias.toRat b.bias| := by
        simpa only [P3DeterministicAlgebra.pairMassQ, dyadic_mass_eq_abs] using hpair
      _ = |prePhase4Mass s| + |prePhase4Mass t| := by
        rw [← mass_after_three a (by omega), ← mass_after_three b (by omega),
          hamass, hbmass]

def absoluteMass (c : Cfg L 256) : ℚ :=
  (c.map (fun a => |prePhase4Mass a|)).sum

theorem absoluteMass_add_pair (r : Cfg L 256) (s t : AgentState L 256) :
    absoluteMass (r + {s, t}) =
      absoluteMass r + (|prePhase4Mass s| + |prePhase4Mass t|) := by
  simp [absoluteMass, Multiset.map_add, Multiset.sum_add, add_assoc, add_left_comm]

theorem absolute_mass_step (c : Cfg L 256) (s t : AgentState L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hzero : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hno : ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L 256) c s t,
      a.phase.val ≠ 10) :
    absoluteMass (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) ≤
      absoluteMass c := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
        c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    have hlmem : (Transition L 256 s t).1 ∈
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by rw [hstep]; simp
    have hrmem : (Transition L 256 s t).2 ∈
        Protocol.stepOrSelf (NonuniformMajority L 256) c s t := by rw [hstep]; simp
    have hpair := transition_absolute_mass s t (hrange s hs) (hrange t ht)
      (hsafe s hs) (hsafe t ht) (hzero s hs) (hzero t ht)
      (hno _ hlmem) (hno _ hrmem)
    have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
      rw [Multiset.sub_add_cancel
        (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
    rw [hstep, absoluteMass_add_pair]
    conv_rhs => rw [hsplit]
    rw [absoluteMass_add_pair]
    exact add_le_add le_rfl hpair
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ] <;> exact le_rfl

theorem absolute_mass_draw (c : Cfg L 256) (d : Draw L 256)
    (hrange : ∀ a ∈ c, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ a ∈ c, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hzero : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3)
    (hno : ∀ a ∈ applyDraw c d, a.phase.val ≠ 10) :
    absoluteMass (applyDraw c d) ≤ absoluteMass c := by
  cases d with
  | none => exact le_rfl
  | some p => exact absolute_mass_step c p.1.1 p.2.1 hrange hsafe hzero hno

theorem absolute_mass_trace (init : Cfg L 256) (ω : Ω L 256) (s t : ℕ)
    (hst : s ≤ t)
    (hrange : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      1 ≤ a.phase.val ∧ a.phase.val ≤ 3)
    (hsafe : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hzero : ∀ u, s ≤ u → u ≤ t → ∀ a ∈ trace init ω u,
      a.role ≠ .main → a.smallBias.val = 3) :
    absoluteMass (trace init ω t) ≤ absoluteMass (trace init ω s) := by
  revert hrange hsafe hzero
  induction t, hst using Nat.le_induction with
  | base =>
      intro _ _ _
      exact le_rfl
  | succ t hst ih =>
      intro hrange hsafe hzero
      have hprevious := ih (fun u hsu hut => hrange u hsu (by omega))
        (fun u hsu hut => hsafe u hsu (by omega))
        (fun u hsu hut => hzero u hsu (by omega))
      have hnext : absoluteMass (trace init ω (t + 1)) ≤
          absoluteMass (trace init ω t) := by
        rw [TraceDrain.trace_succ]
        apply absolute_mass_draw _ (ω (t + 1)) (hrange t hst (by omega))
          (hsafe t hst (by omega)) (hzero t hst (by omega))
        intro a ha
        have ha' : a ∈ trace init ω (t + 1) := by
          simpa only [TraceDrain.trace_succ] using ha
        have hcap := (hrange (t + 1) (by omega) le_rfl a ha').2
        omega
      exact hnext.trans hprevious

theorem rational_natAbs (z : ℤ) : (z.natAbs : ℚ) = |(z : ℚ)| := by
  calc
    (z.natAbs : ℚ) = ((z.natAbs : ℤ) : ℚ) := by simp only [Int.cast_natCast]
    _ = ((|z| : ℤ) : ℚ) := by rw [Int.natCast_natAbs]
    _ = |(z : ℚ)| := by rw [Int.cast_abs]

theorem phase_one_mass_eq (c : Cfg L 256)
    (hone : ∀ a ∈ c, a.phase.val = 1)
    (hzero : ∀ a ∈ c, a.role ≠ .main → a.smallBias.val = 3) :
    absoluteMass c = (PhaseOneDrain.PhaseOneMass c : ℚ) := by
  revert hone hzero
  induction c using Multiset.induction_on with
  | empty =>
      intro _ _
      simp [absoluteMass, PhaseOneDrain.PhaseOneMass]
  | @cons a c ih =>
      intro hone hzero
      have ha : a ∈ a ::ₘ c := Multiset.mem_cons_self _ _
      have hvalue : prePhase4Mass a = (AveragingRate.biasZ a : ℚ) := by
        rw [mass_before_three a (by have := hone a ha; omega)]
        by_cases hm : a.role = .main
        · simp [smallValue, AveragingRate.biasZ, hm]
        · simp [smallValue, AveragingRate.biasZ, hm, hzero a ha hm]
      have habs : |prePhase4Mass a| = ((AveragingRate.biasZ a).natAbs : ℚ) := by
        rw [hvalue, rational_natAbs]
      have htail := ih
        (fun b hb => hone b (Multiset.mem_cons_of_mem hb))
        (fun b hb => hzero b (Multiset.mem_cons_of_mem hb))
      have hadd := congrArg₂ (fun x y : ℚ => x + y) habs htail
      simpa only [absoluteMass, PhaseOneDrain.PhaseOneMass,
        Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] using hadd

/-- The retained drained endpoint supplies sparseAsyncEntry for every already
produced actual AsyncEntry. No additional probability or height premise is
introduced by the sparse-mass extension. -/
theorem sparse_async_entry_of_drained {n : ℕ}
    (init : InputCfg n) (ω : InputLog n) (d s t : ℕ)
    (hready : PhaseOneDrainStopping.PhaseOneReadyProfile init (trace init ω d))
    (hds : d ≤ s) (hentry : StageEventSpec.AsyncEntry init ω s t) :
    StageEventSpec.sparseAsyncEntry init ω s t := by
  have hwindow (u : ℕ) (hdu : d ≤ u) (hut : u ≤ t) :
      ∀ a ∈ trace init ω u, 1 ≤ a.phase.val ∧ a.phase.val ≤ 3 := by
    have hlo := PhaseOneDrainStopping.phase_lower_reachable 1
      (trace init ω d) (trace init ω u) (trace_reachable init ω hdu)
      (fun a ha => le_of_eq (hready.all_one a ha).symm)
    have hhi := PhaseOneDrainStopping.phase_upper_reachable 3
      (trace init ω u) (trace init ω t) (trace_reachable init ω hut)
      (fun a ha => le_of_eq (hentry.advanced_profile.all_three a ha))
    exact fun a ha => ⟨hlo a ha, hhi a ha⟩
  have hsafe (u : ℕ) (hdu : d ≤ u) :
      ∀ a ∈ trace init ω u, a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    have h := PhaseTwoDrainedSafety.readyProfile_small_safe_future init ω d u hready hdu
    intro a ha
    have hb := h a ha
    change 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4 at hb
    have hc : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4 := by omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
  have hzero (u : ℕ) (hdu : d ≤ u) (hut : u ≤ t) :
      ∀ a ∈ trace init ω u, a.role ≠ .main → a.smallBias.val = 3 := by
    have hreach :
        (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
          init (trace init ω u) := by
      simpa only [TraceDrain.trace_zero] using
        (trace_reachable init ω (s := 0) (t := u) (Nat.zero_le u))
    have hroles := trace_final_roles_of_range init hready.valid_initial ω u (hwindow u hdu hut)
    have hz := reachable_nonMain_smallBias_zero init (trace init ω u)
      hready.valid_initial hreach
    intro a ha hm
    rcases hroles a ha with hmain | hc | hr
    · exact (hm hmain).elim
    · exact hz a ha (Or.inr hc)
    · exact hz a ha (Or.inl hr)
  have hseedCounts :=
    (PhaseTwoSeedProfile.seed_profile_and_counts_of_first_hit init ω d s hready
      hds hentry.seed_first (fun a ha => by
        have hcap := (hentry.seed_profile.phase_range a ha).2
        omega)).2
  have hmainSeed : timeMainCount (trace init ω s) =
      RoleSplitConcentration.mainCount (trace init ω d) := by
    simpa only [timeMainCount, RoleSplitConcentration.mainCount] using hseedCounts .main
  have hstartMass : absoluteMass (trace init ω d) =
      (PhaseOneDrain.PhaseOneMass (trace init ω d) : ℚ) :=
    phase_one_mass_eq _ hready.all_one hready.nonmain_zero
  have hstartBound :
      100 * (PhaseOneDrain.PhaseOneMass (trace init ω d) : ℚ) ≤
        3 * (RoleSplitConcentration.mainCount (trace init ω d) : ℚ) := by
    exact_mod_cast hready.drained.2.2
  refine ⟨hentry, ?_⟩
  intro u hsu hut
  have hdu : d ≤ u := hds.trans hsu
  have hmass := absolute_mass_trace init ω d u hdu
    (fun v hdv hvu => hwindow v hdv (hvu.trans hut))
    (fun v hdv hvu => hsafe v hdv)
    (fun v hdv hvu => hzero v hdv (hvu.trans hut))
  have hmain : timeMainCount (trace init ω u) =
      RoleSplitConcentration.mainCount (trace init ω d) :=
    (hentry.main_count u hsu hut).trans hmainSeed
  change 100 * absoluteMass (trace init ω u) ≤
    3 * (timeMainCount (trace init ω u) : ℚ)
  calc
    100 * absoluteMass (trace init ω u) ≤
        100 * absoluteMass (trace init ω d) :=
      mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ = 100 * (PhaseOneDrain.PhaseOneMass (trace init ω d) : ℚ) := by rw [hstartMass]
    _ ≤ 3 * (RoleSplitConcentration.mainCount (trace init ω d) : ℚ) := hstartBound
    _ = 3 * (timeMainCount (trace init ω u) : ℚ) := by rw [hmain]

end Ripple.PopulationProtocol.ExactMajority.PhaseTwoSparse
