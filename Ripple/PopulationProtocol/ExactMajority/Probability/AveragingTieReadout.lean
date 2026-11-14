import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingFirstExit

/-!
# Deterministic tie extinction readout

Zero integer shallow potential excludes every Main index below the cap.
The top-index and non-Main-zero properties are preserved by the actual
Phase-3/4 dispatcher. A clock history therefore converts any post-activation
zero-potential checkpoint into the literal tie readout at its first exit.

The probability of reaching such a checkpoint is a separate obligation.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingTieReadout

open TimeTheorem StageEventSpec
open Phase4Convergence Phase5To6FuelProducer

variable {L K n : ℕ}

def NonmainZero (a : AgentState L K) : Prop :=
  a.role ≠ .main → a.bias = Bias.zero

theorem phase3CancelSplit_noBigBias_pair (s t : AgentState L K)
    (hs : noBigBias s) (ht : noBigBias t) :
    noBigBias (phase3CancelSplit L K s t).1 ∧
      noBigBias (phase3CancelSplit L K s t).2 := by
  cases hsb : s.bias with
  | zero =>
      cases htb : t.bias with
      | zero =>
          simp [phase3CancelSplit, hsb, htb, noBigBias]
      | dyadic τ j =>
          have hj : ¬ j.val < L := by simpa [noBigBias, htb] using ht
          have hh := s.hour.isLt
          have hgt : ¬ s.hour.val > j.val := by omega
          simpa [phase3CancelSplit, hsb, htb, hgt, noBigBias] using And.intro hs ht
  | dyadic σ i =>
      cases htb : t.bias with
      | zero =>
          have hi : ¬ i.val < L := by simpa [noBigBias, hsb] using hs
          have hh := t.hour.isLt
          have hgt : ¬ t.hour.val > i.val := by omega
          simpa [phase3CancelSplit, hsb, htb, hgt, noBigBias] using And.intro hs ht
      | dyadic τ j =>
          cases σ <;> cases τ <;> by_cases hij : i.val = j.val <;>
            simp [phase3CancelSplit, hsb, htb, hij, noBigBias] at hs ht ⊢ <;>
            tauto

theorem Phase3Transition_noBigBias_pair (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsb : noBigBias s) (htb : noBigBias t) :
    noBigBias (Phase3Transition L K s t).1 ∧
      noBigBias (Phase3Transition L K s t).2 := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · simpa [Phase3Transition, hmain.1, hmain.2] using
      phase3CancelSplit_noBigBias_pair s t hsb htb
  · have hb := Phase3Transition_biases_of_not_both_main s t hs ht hmain
    simpa only [noBigBias, hb.1, hb.2] using And.intro hsb htb

theorem Transition_noBigBias_pair (s t : AgentState L K)
    (hs : InPhase34 s) (ht : InPhase34 t)
    (hsb : noBigBias s) (htb : noBigBias t) :
    noBigBias (Transition L K s t).1 ∧
      noBigBias (Transition L K s t).2 := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
    have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
    have hp := Phase3Transition_noBigBias_pair s t hs ht hsb htb
    unfold Transition
    rw [hepi]
    simpa only [hsp, noBigBias, finishPhase10Entry_bias] using hp
  · have hf := Transition_role_bias_of_three_four s t hs ht
    simpa only [noBigBias, hf.2.1, hf.2.2.2] using And.intro hsb htb
  · have hf := Transition_role_bias_of_four_three s t hs ht
    simpa only [noBigBias, hf.2.1, hf.2.2.2] using And.intro hsb htb
  · have hf := Transition_role_bias_of_four_four s t hs ht
    simpa only [noBigBias, hf.2.1, hf.2.2.2] using And.intro hsb htb

theorem Phase3Transition_nonmainZero_pair (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsz : NonmainZero s) (htz : NonmainZero t) :
    NonmainZero (Phase3Transition L K s t).1 ∧
      NonmainZero (Phase3Transition L K s t).2 := by
  have hr := Phase3Transition_roles s t hs ht
  by_cases hmain : s.role = .main ∧ t.role = .main
  · constructor
    · intro hnot
      exact (hnot (hr.1.trans hmain.1)).elim
    · intro hnot
      exact (hnot (hr.2.trans hmain.2)).elim
  · have hb := Phase3Transition_biases_of_not_both_main s t hs ht hmain
    simpa only [NonmainZero, hr.1, hr.2, hb.1, hb.2] using And.intro hsz htz

theorem Transition_nonmainZero_pair (s t : AgentState L K)
    (hs : InPhase34 s) (ht : InPhase34 t)
    (hsz : NonmainZero s) (htz : NonmainZero t) :
    NonmainZero (Transition L K s t).1 ∧
      NonmainZero (Transition L K s t).2 := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
    have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
    have hp := Phase3Transition_nonmainZero_pair s t hs ht hsz htz
    unfold Transition
    rw [hepi]
    simpa only [hsp, NonmainZero, finishPhase10Entry_role,
      finishPhase10Entry_bias] using hp
  · have hf := Transition_role_bias_of_three_four s t hs ht
    simpa only [NonmainZero, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2] using
      And.intro hsz htz
  · have hf := Transition_role_bias_of_four_three s t hs ht
    simpa only [NonmainZero, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2] using
      And.intro hsz htz
  · have hf := Transition_role_bias_of_four_four s t hs ht
    simpa only [NonmainZero, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2] using
      And.intro hsz htz

theorem property_applyDraw_of_phase_three_or_four
    (P : AgentState L K → Prop)
    (hpair : ∀ s t, InPhase34 s → InPhase34 t → P s → P t →
      P (Transition L K s t).1 ∧ P (Transition L K s t).2)
    (c : Cfg L K) (o : Draw L K) (hphase : AllPhase34 c)
    (hc : ∀ a ∈ c, P a) :
    ∀ a ∈ applyDraw c o, P a := by
  classical
  cases o with
  | none => exact hc
  | some q =>
      change ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1,
        P a
      by_cases happ : Protocol.Applicable c q.1.1 q.2.1
      · have hs : q.1.1 ∈ c := Multiset.mem_of_le happ (by simp)
        have ht : q.2.1 ∈ c := Multiset.mem_of_le happ (by simp)
        have hp := hpair q.1.1 q.2.1 (hphase q.1.1 hs) (hphase q.2.1 ht)
          (hc q.1.1 hs) (hc q.2.1 ht)
        have heq : Protocol.stepOrSelf (NonuniformMajority L K) c q.1.1 q.2.1 =
            c - {q.1.1, q.2.1} +
              {(Transition L K q.1.1 q.2.1).1,
                (Transition L K q.1.1 q.2.1).2} := by
          unfold Protocol.stepOrSelf
          rw [if_pos happ]
          rfl
        rw [heq]
        intro a ha
        rcases Multiset.mem_add.mp ha with ha | ha
        · exact hc a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
        · have hcases : a = (Transition L K q.1.1 q.2.1).1 ∨
              a = (Transition L K q.1.1 q.2.1).2 := by simpa using ha
          rcases hcases with rfl | rfl
          · exact hp.1
          · exact hp.2
      · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
        exact hc

theorem property_trace_of_phase_three_or_four
    (P : AgentState L K → Prop)
    (hpair : ∀ s t, InPhase34 s → InPhase34 t → P s → P t →
      P (Transition L K s t).1 ∧ P (Transition L K s t).2)
    (init : Cfg L K) (ω : Ω L K) {s t : ℕ} (hst : s ≤ t)
    (hwindow : ∀ u, s ≤ u → u < t → AllPhase34 (trace init ω u))
    (hstart : ∀ a ∈ trace init ω s, P a) :
    ∀ a ∈ trace init ω t, P a := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hst
  have haux : ∀ r : ℕ,
      (∀ u, s ≤ u → u < s + r → AllPhase34 (trace init ω u)) →
      ∀ a ∈ trace init ω (s + r), P a := by
    intro r
    induction r with
    | zero =>
        intro _
        simpa only [Nat.add_zero] using hstart
    | succ r ih =>
        intro hwin
        have hprevious := ih (fun u hu hut => hwin u hu (by omega))
        have hsource := hwin (s + r) (by omega) (by omega)
        rw [show s + (r + 1) = (s + r) + 1 by omega, TimeTheorem.trace_succ]
        exact property_applyDraw_of_phase_three_or_four P hpair _ _
          hsource hprevious
  exact haux q hwindow

theorem nonmainZero_of_clockHistory {init : InputCfg n} {ω : InputLog n}
    {S T ρ u : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) (hTu : T ≤ u) (huρ : u ≤ ρ) :
    ∀ a ∈ trace init ω u, NonmainZero a := by
  apply property_trace_of_phase_three_or_four NonmainZero
    Transition_nonmainZero_pair init ω hTu
  · intro v hTv hvu a ha
    exact Or.inl (h.all_three v hTv (by omega) a ha)
  · exact h.entry.advanced_profile.nonmain_bias

noncomputable def shallowAtom (ell : ℕ) (a : AgentState L K) : ℕ := by
  classical
  exact if a.role = .main then
    match a.bias with
    | .zero => 0
    | .dyadic _ j => if j.val < ell then 4 ^ (ell - j.val - 1) else 0
  else 0

theorem shallowAtom_eq_zero_iff (ell : ℕ) (a : AgentState L K) :
    shallowAtom ell a = 0 ↔
      (a.role = .main →
        ∀ σ j, a.bias = Bias.dyadic σ j → ell ≤ j.val) := by
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero => simp [shallowAtom, hm, hb]
    | dyadic σ j =>
        by_cases hj : j.val < ell
        · have hpos : 0 < (4 : ℕ) ^ (ell - j.val - 1) := by positivity
          constructor
          · intro hz
            have hz' : 4 ^ (ell - j.val - 1) = (0 : ℕ) := by
              simpa [shallowAtom, hm, hb, hj] using hz
            omega
          · intro h
            have hle := h hm σ j (by simp only [hb])
            omega
        · constructor
          · intro _ _ τ k hk
            try simp only [hb] at hk
            have hindex : j.val = k.val :=
              congrArg (fun b : Bias L =>
                match b with
                | .zero => 0
                | .dyadic _ i => i.val) hk
            omega
          · intro _
            simp [shallowAtom, hm, hb, hj]
  · simp [shallowAtom, hm]

/-- This is an equivalence for the exact N10 integer potential, with no
phase premise. It is the deterministic integer-extinction implication. -/
theorem shallowPotential_eq_zero_iff (ell : ℕ) (c : InputCfg n) :
    shallowPotential ell c = 0 ↔
      ∀ a ∈ c, a.role = .main →
        ∀ σ j, a.bias = Bias.dyadic σ j → ell ≤ j.val := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [shallowPotential]
  | cons a c ih =>
      have hcons : shallowPotential ell (a ::ₘ c) =
          shallowAtom ell a + shallowPotential ell c := by
        first
          | (simp only [shallowPotential, shallowAtom, Multiset.map_cons, Multiset.sum_cons]; done)
          | (unfold shallowPotential; rw [Multiset.map_cons, Multiset.sum_cons]; rfl)
          | (simp [shallowPotential, shallowAtom]; done)
          | (unfold shallowPotential; rw [Multiset.map_cons, Multiset.sum_cons]; congr 1;
             unfold shallowAtom; split_ifs <;> (cases hb : a.bias <;> simp))
      rw [hcons, Nat.add_eq_zero, shallowAtom_eq_zero_iff, ih]
      constructor
      · rintro ⟨ha, hc⟩ b hb
        rcases Multiset.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hc b hb
      · intro h
        exact ⟨h a (Multiset.mem_cons_self a c),
          fun b hb => h b (Multiset.mem_cons_of_mem hb)⟩

theorem noBigBias_of_zero_potential (c : InputCfg n)
    (hzero : shallowPotential (PhaseThreeModel.Numeric.hourIndex n) c = 0)
    (hnonmain : ∀ a ∈ c, NonmainZero a) :
    ∀ a ∈ c, noBigBias a := by
  have hindices := (shallowPotential_eq_zero_iff _ c).mp hzero
  intro a ha
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero => simp [noBigBias, hb]
    | dyadic σ j =>
        have hj := hindices a ha hm σ j hb
        simp only [noBigBias, hb]
        omega
  · have hb := hnonmain a ha hm
    simp [noBigBias, hb]

/-- The deterministic tie readout at the first exit follows from a
zero-potential checkpoint; the original-law checkpoint tail is separate. -/
theorem tieReadout_at_first_exit_of_zero_potential
    {init : InputCfg n} {ω : InputLog n} {S T ρ u : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hgap : initialGap init = 0) (hTu : T ≤ u) (huρ : u ≤ ρ)
    (hzero : shallowPotential (PhaseThreeModel.Numeric.hourIndex n)
      (trace init ω u) = 0) :
    tieReadout init (trace init ω ρ) := by
  have hnonmain := nonmainZero_of_clockHistory h hTu huρ
  have hstart := noBigBias_of_zero_potential _ hzero hnonmain
  have hcap : ∀ a ∈ trace init ω ρ, noBigBias a :=
    property_trace_of_phase_three_or_four noBigBias Transition_noBigBias_pair
      init ω huρ
      (by
        intro v huv hvρ a ha
        exact Or.inl (h.all_three v (by omega) hvρ a ha))
      hstart
  have hnonmainFinal := nonmainZero_of_clockHistory h
    (le_trans hTu huρ) le_rfl
  refine ⟨hgap, hnonmainFinal, ?_⟩
  intro a ha _ σ j hb
  have hbig := hcap a ha
  have hj := j.isLt
  simp only [noBigBias, hb] at hbig
  omega

theorem averageBy_of_tie_zero_potential {init : InputCfg n} {ω : InputLog n}
    {S T ρ u : ℕ} {w : ClockTimes init}
    (h : ClockHistory init ω S T ρ w) (hT : T ≤ earlyHorizon n)
    (hgap : initialGap init = 0) (hTu : T ≤ u) (huρ : u ≤ ρ)
    (hzero : shallowPotential (PhaseThreeModel.Numeric.hourIndex n)
      (trace init ω u) = 0) :
    ω ∈ averageBy (reviewedStageEvents n init) := by
  exact ⟨S, T, ρ, hT, h.entry, ⟨w, h⟩,
    Or.inl (tieReadout_at_first_exit_of_zero_potential h hgap hTu huρ hzero)⟩

end Ripple.PopulationProtocol.ExactMajority.AveragingTieReadout

end
