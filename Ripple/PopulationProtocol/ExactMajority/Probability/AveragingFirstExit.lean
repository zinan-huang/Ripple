import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingEventInterface
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5To6FuelProducer

/-!
# Exact observable transport through the first Phase-4 seed

From an all-Phase-3 configuration, a selected pair can create Phase 4 only
in the Clock-Clock branch. That branch preserves both role and bias fields.
Consequently the complete multiset of role/bias pairs, and hence every
readout observable depending on those fields, is unchanged at the first
exit. No probability estimate is assumed or proved here.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingFirstExit

open TimeTheorem StageEventSpec

variable {L K n : ℕ}

def roleBias (a : AgentState L K) : Role × Bias L :=
  (a.role, a.bias)

theorem Transition_clock_pair_of_phase_three_exit (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hout : (Transition L K s t).1.phase.val = 4 ∨
      (Transition L K s t).2.phase.val = 4) :
    s.role = .clock ∧ t.role = .clock := by
  by_contra hclock
  have hleft : (Phase3Transition L K s t).1.phase = s.phase :=
    (Phase3Transition_left_output_eq_rule1 (L := L) (K := K) s t s (by simp [hclock])).2
  have hright : (Phase3Transition L K s t).2.phase = t.phase :=
    (Phase3Transition_right_output_eq_rule1 (L := L) (K := K) s t t (by simp [hclock])).2
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hp : (Transition L K s t).1.phase.val = s.phase.val ∧
      (Transition L K s t).2.phase.val = t.phase.val := by
    unfold Transition
    rw [hepi]
    simpa only [hsp, finishPhase10Entry_phase_val] using
      And.intro (congrArg Fin.val hleft) (congrArg Fin.val hright)
  rcases hout with hout | hout
  · have := hp.1
    omega
  · have := hp.2
    omega

theorem Transition_role_bias_of_phase_three_exit (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hout : (Transition L K s t).1.phase.val = 4 ∨
      (Transition L K s t).2.phase.val = 4) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).1.bias = s.bias ∧
      (Transition L K s t).2.role = t.role ∧
      (Transition L K s t).2.bias = t.bias := by
  have hclock := Transition_clock_pair_of_phase_three_exit s t hs ht hout
  have hnotmain : ¬ (s.role = .main ∧ t.role = .main) := by
    rintro ⟨hmain, _⟩
    rw [hclock.1] at hmain
    cases hmain
  have hr := Phase5To6FuelProducer.Phase3Transition_roles s t hs ht
  have hb := Phase5To6FuelProducer.Phase3Transition_biases_of_not_both_main
    s t hs ht hnotmain
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  unfold Transition
  rw [hepi]
  simpa only [hsp, finishPhase10Entry_role, finishPhase10Entry_bias] using
    And.intro hr.1 (And.intro hb.1 (And.intro hr.2 hb.2))

theorem roleBias_map_applyDraw_of_phase_three_exit (c : Cfg L K)
    (o : Draw L K) (hbefore : ∀ a ∈ c, a.phase.val = 3)
    (hafter : ∃ a ∈ applyDraw c o, a.phase.val = 4) :
    (applyDraw c o).map roleBias = c.map roleBias := by
  classical
  cases o with
  | none => rfl
  | some q =>
      change (Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1).map
        roleBias = c.map roleBias
      change ∃ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1,
        a.phase.val = 4 at hafter
      by_cases happ : Protocol.Applicable c q.1.1 q.2.1
      · have hs := hbefore q.1.1 (Multiset.mem_of_le happ (by simp))
        have ht := hbefore q.2.1 (Multiset.mem_of_le happ (by simp))
        have heq : Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1 =
            c - {q.1.1, q.2.1} +
              {(Transition L K q.1.1 q.2.1).1,
                (Transition L K q.1.1 q.2.1).2} := by
          unfold Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        have hout : (Transition L K q.1.1 q.2.1).1.phase.val = 4 ∨
            (Transition L K q.1.1 q.2.1).2.phase.val = 4 := by
          obtain ⟨a, ha, hfour⟩ := hafter
          rw [heq] at ha
          rcases Multiset.mem_add.mp ha with ha | ha
          · have hthree := hbefore a
              (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
            omega
          · have hcases : a = (Transition L K q.1.1 q.2.1).1 ∨
                a = (Transition L K q.1.1 q.2.1).2 := by
              simpa using ha
            rcases hcases with rfl | rfl
            · exact Or.inl hfour
            · exact Or.inr hfour
        have hf := Transition_role_bias_of_phase_three_exit q.1.1 q.2.1 hs ht hout
        have hpair :
            ({(Transition L K q.1.1 q.2.1).1,
                (Transition L K q.1.1 q.2.1).2} :
              Multiset (AgentState L K)).map roleBias =
            ({q.1.1, q.2.1} : Multiset (AgentState L K)).map roleBias := by
          simp [roleBias, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]
        rw [heq, Multiset.map_add, hpair, ← Multiset.map_add,
          Multiset.sub_add_cancel happ]
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem roleBias_map_at_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) :
    (trace init ω ρ).map roleBias =
      (trace init ω (ρ - 1)).map roleBias := by
  have hST := AveragingEventInterface.clockHistory_seed_lt_exit h
  have hpred : ρ - 1 + 1 = ρ := by omega
  have hstep : trace init ω ρ =
      applyDraw (trace init ω (ρ - 1)) (ω ρ) := by
    simpa only [hpred] using TimeTheorem.trace_succ init ω (ρ - 1)
  have hbefore : ∀ a ∈ trace init ω (ρ - 1), a.phase.val = 3 :=
    h.all_three (ρ - 1) (by omega) (by omega)
  have hafter : ∃ a ∈ applyDraw (trace init ω (ρ - 1)) (ω ρ),
      a.phase.val = 4 := by
    rw [← hstep]
    exact h.first_exit.1
  rw [hstep]
  exact roleBias_map_applyDraw_of_phase_three_exit _ _ hbefore hafter

theorem roleBias_property_at_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (P : Role → Bias (PhaseThreeModel.Numeric.hourIndex n) → Prop)
    (h : ClockHistory init ω S T ρ w)
    (hpre : ∀ a ∈ trace init ω (ρ - 1), P a.role a.bias) :
    ∀ a ∈ trace init ω ρ, P a.role a.bias := by
  intro a ha
  have hm : roleBias a ∈ (trace init ω ρ).map roleBias :=
    Multiset.mem_map.mpr ⟨a, ha, rfl⟩
  rw [roleBias_map_at_first_exit h] at hm
  obtain ⟨b, hb, heq⟩ := Multiset.mem_map.mp hm
  have hr : b.role = a.role := congrArg Prod.fst heq
  have hbi : b.bias = a.bias := congrArg Prod.snd heq
  simpa only [hr, hbi] using hpre b hb

theorem sum_roleBias_at_first_exit {A : Type*} [AddCommMonoid A]
    {init : InputCfg n} {ω : InputLog n} {S T ρ : ℕ} {w : ClockTimes init}
    (F : Role → Bias (PhaseThreeModel.Numeric.hourIndex n) → A)
    (h : ClockHistory init ω S T ρ w) :
    Config.sumOf (fun a => F a.role a.bias) (trace init ω ρ) =
      Config.sumOf (fun a => F a.role a.bias) (trace init ω (ρ - 1)) := by
  have heq := congrArg
    (fun d : Multiset (Role × Bias (PhaseThreeModel.Numeric.hourIndex n)) =>
      (d.map (fun x => F x.1 x.2)).sum)
    (roleBias_map_at_first_exit h)
  simpa only [Config.sumOf, Multiset.map_map, Function.comp_def, roleBias] using heq

theorem mainCount_first_exit_step {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) :
    timeMainCount (trace init ω ρ) = timeMainCount (trace init ω (ρ - 1)) := by
  classical
  have heq := congrArg
    (fun d : Multiset (Role × Bias (PhaseThreeModel.Numeric.hourIndex n)) =>
      d.countP (fun x => x.1 = Role.main))
    (roleBias_map_at_first_exit h)
  simpa only [Multiset.countP_map, ← Multiset.countP_eq_card_filter,
    roleBias, timeMainCount, AveragingEventInterface.countP_classical] using heq

theorem bandCount_first_exit_step {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (σ : Sign) (ell width : ℕ)
    (h : ClockHistory init ω S T ρ w) :
    bandCount σ ell width (trace init ω ρ) =
      bandCount σ ell width (trace init ω (ρ - 1)) := by
  classical
  have heq := congrArg
    (fun d : Multiset (Role × Bias (PhaseThreeModel.Numeric.hourIndex n)) =>
      d.countP (fun x => x.1 = Role.main ∧
        ∃ j, x.2 = Bias.dyadic σ j ∧ ell ≤ j.val ∧ j.val ≤ ell + width))
    (roleBias_map_at_first_exit h)
  simpa only [Multiset.countP_map, ← Multiset.countP_eq_card_filter,
    roleBias, bandCount, AveragingEventInterface.countP_classical] using heq

theorem signMass_first_exit_step {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (σ : Sign)
    (h : ClockHistory init ω S T ρ w) :
    signMass σ (trace init ω ρ) = signMass σ (trace init ω (ρ - 1)) := by
  classical
  simpa only [signMass, Config.sumOf] using
    sum_roleBias_at_first_exit
      (fun r b => if r = Role.main then
        match b with
        | .zero => (0 : ℚ)
        | .dyadic τ j => if τ = σ then (2 : ℚ) ^ (-(j.val : ℤ)) else 0
      else 0) h

theorem shallowMass_first_exit_step {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (ell : ℕ)
    (h : ClockHistory init ω S T ρ w) :
    shallowMass ell (trace init ω ρ) = shallowMass ell (trace init ω (ρ - 1)) := by
  classical
  simpa only [shallowMass, Config.sumOf] using
    sum_roleBias_at_first_exit
      (fun r b => if r = Role.main then
        match b with
        | .zero => (0 : ℚ)
        | .dyadic _ j => if j.val < ell then (2 : ℚ) ^ (-(j.val : ℤ)) else 0
      else 0) h

theorem shallowPotential_first_exit_step {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init} (ell : ℕ)
    (h : ClockHistory init ω S T ρ w) :
    shallowPotential ell (trace init ω ρ) =
      shallowPotential ell (trace init ω (ρ - 1)) := by
  classical
  simpa only [shallowPotential, Config.sumOf] using
    sum_roleBias_at_first_exit
      (fun r b => if r = Role.main then
        match b with
        | .zero => (0 : ℕ)
        | .dyadic _ j => if j.val < ell then 4 ^ (ell - j.val - 1) else 0
      else 0) h

theorem smallReadout_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ M ell : ℕ} {w : ClockTimes init} {σ : Sign}
    (h : ClockHistory init ω S T ρ w)
    (hpre : SmallReadout init M ell σ (trace init ω (ρ - 1))) :
    SmallReadout init M ell σ (trace init ω ρ) := by
  refine ⟨hpre.winning, hpre.nonzero, hpre.strictGap, hpre.levelLower,
    hpre.levelUpper, hpre.scaleLower, hpre.scaleUpper, ?_, ?_, ?_, ?_⟩
  · rw [bandCount_first_exit_step σ ell 2 h]
    exact hpre.majorityBand
  · rw [signMass_first_exit_step (oppositeSign σ) h]
    exact hpre.minority
  · rw [shallowMass_first_exit_step ell h]
    exact hpre.shallow
  · rw [shallowPotential_first_exit_step ell h]
    exact hpre.potential

theorem tieReadout_first_exit {init : InputCfg n} {ω : InputLog n}
    {S T ρ : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w)
    (hpre : tieReadout init (trace init ω (ρ - 1))) :
    tieReadout init (trace init ω ρ) := by
  refine ⟨hpre.1, ?_, ?_⟩
  · exact roleBias_property_at_first_exit
      (fun r b => r ≠ Role.main → b = Bias.zero) h hpre.2.1
  · exact roleBias_property_at_first_exit
      (fun r b => r = Role.main → ∀ σ j, b = Bias.dyadic σ j →
        j.val = PhaseThreeModel.Numeric.hourIndex n) h hpre.2.2

end Ripple.PopulationProtocol.ExactMajority.AveragingFirstExit

end
