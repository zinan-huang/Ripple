-- Ripple/PopulationProtocol/ExactMajority/Probability/LateMixedFuelLedger.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5To6FuelProducer

/-!
# The exact mixed Phase-5/6 fuel ledger

After sampling completion, every Reserve is locked.  Hence a Phase-5 pair
preserves the role/bias/hour data seen by the Phase-6 pressure observables.
A mixed Phase-5/6 pair first runs the Phase-6 initializer on the lagging agent;
that initializer also preserves role, bias, and hour, after which the existing
Phase-6 pressure theorem applies.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFuelLedger

variable {L K : ℕ}

/-- The exact source window between completion and homogeneous Phase 6. -/
def MixedFiveSixWin (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 5 ∨ a.phase.val = 6

/-- The mixed window lies in the already-closed phase-at-least-five window. -/
theorem mixedFiveSixWin_phaseGE5
    (n : ℕ) (c : Config (AgentState L K))
    (h : MixedFiveSixWin n c) :
    ReserveSampling.PhaseGE5Win (L := L) (K := K) n c := by
  refine ⟨h.1, ?_⟩
  intro a ha
  rcases h.2 a ha with hp | hp <;> omega

private theorem not_unsampled_of_reserveSampled
    (c : Config (AgentState L K))
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (a : AgentState L K) (ha : a ∈ c) :
    ¬ ReserveSampling.unsampled (L := L) (K := K) a := by
  unfold ReserveSampling.ReserveSampled
    ReserveSampling.unsampledReserveU at hsampled
  rw [Multiset.countP_eq_zero] at hsampled
  exact hsampled a ha

/-! ## Pressure only sees role, bias, and Reserve hour -/

private theorem agentPressure_eq_of_static
    (i : Fin (L + 1)) (before after : AgentState L K)
    (hrole : after.role = before.role)
    (hbias : after.bias = before.bias)
    (hhour : before.role = Role.reserve → after.hour = before.hour) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i after =
      Phase6FuelLedger.agentPressure (L := L) (K := K) i before := by
  unfold Phase6FuelLedger.agentPressure Phase6FuelLedger.agentDebt
  rw [hrole, hbias]
  by_cases hreserve : before.role = Role.reserve
  · simp [Phase6FuelLedger.IsFuel, hreserve, hhour hreserve, hrole, hbias]
  · simp [Phase6FuelLedger.IsFuel, hreserve, hrole, hbias]

private theorem twoAgentPressure_eq_of_static
    (l : Fin (L + 1)) (before after : AgentState L K)
    (hrole : after.role = before.role)
    (hbias : after.bias = before.bias)
    (hhour : before.role = Role.reserve → after.hour = before.hour) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l after =
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l before := by
  unfold Phase6FuelLedger.twoAgentPressure Phase6FuelLedger.unionAgentDebt
  rw [hrole, hbias]
  by_cases hreserve : before.role = Role.reserve
  · simp [Phase6FuelLedger.IsTwoFuel, hreserve, hhour hreserve, hrole, hbias]
  · simp [Phase6FuelLedger.IsTwoFuel, hreserve, hrole, hbias]

@[simp] private theorem agentPressure_set_phase_eq
    (i : Fin (L + 1)) (a : AgentState L K) (p : Fin 11) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i {a with phase := p} =
      Phase6FuelLedger.agentPressure (L := L) (K := K) i a := by
  rfl

@[simp] private theorem twoAgentPressure_set_phase_eq
    (l : Fin (L + 1)) (a : AgentState L K) (p : Fin 11) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l {a with phase := p} =
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l a := by
  rfl

/-! ## Phase-6 entry initializer -/

/-- The exact state obtained by lifting one Phase-5 agent to Phase 6. -/
def phaseSixEntry (a : AgentState L K) : AgentState L K :=
  phaseInit L K ⟨6, by decide⟩ {a with phase := ⟨6, by decide⟩}

theorem phaseSixEntry_role (a : AgentState L K) :
    (phaseSixEntry (L := L) (K := K) a).role = a.role := by
  simpa [phaseSixEntry] using
    Phase5Convergence.phaseInit_role_ge_five
      (L := L) (K := K) (⟨6, by decide⟩ : Fin 11)
      ({a with phase := ⟨6, by decide⟩} : AgentState L K) (by decide)

theorem phaseSixEntry_bias (a : AgentState L K) :
    (phaseSixEntry (L := L) (K := K) a).bias = a.bias := by
  simpa [phaseSixEntry] using
    Phase5Convergence.phaseInit_bias_ge_five
      (L := L) (K := K) (⟨6, by decide⟩ : Fin 11)
      ({a with phase := ⟨6, by decide⟩} : AgentState L K) (by decide)

theorem phaseSixEntry_hour (a : AgentState L K) :
    (phaseSixEntry (L := L) (K := K) a).hour = a.hour := by
  simpa [phaseSixEntry] using
    ReserveSampling.phaseInit_hour_ge_six
      (L := L) (K := K) (⟨6, by decide⟩ : Fin 11)
      ({a with phase := ⟨6, by decide⟩} : AgentState L K) (by decide)

theorem phaseSixEntry_phase (a : AgentState L K) :
    (phaseSixEntry (L := L) (K := K) a).phase.val = 6 := by
  unfold phaseSixEntry
  exact ReserveSampling.phaseInit_phase_eq_of_six
    (L := L) (K := K) ({a with phase := ⟨6, by decide⟩} : AgentState L K)
    ⟨6, by decide⟩ (by decide) (by simp)

@[simp] theorem phaseSixEntry_agentPressure_eq
    (i : Fin (L + 1)) (a : AgentState L K) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i
        (phaseSixEntry (L := L) (K := K) a) =
      Phase6FuelLedger.agentPressure (L := L) (K := K) i a := by
  apply agentPressure_eq_of_static
  · exact phaseSixEntry_role a
  · exact phaseSixEntry_bias a
  · intro _
    exact phaseSixEntry_hour a

@[simp] theorem phaseSixEntry_twoAgentPressure_eq
    (l : Fin (L + 1)) (a : AgentState L K) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
        (phaseSixEntry (L := L) (K := K) a) =
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l a := by
  apply twoAgentPressure_eq_of_static
  · exact phaseSixEntry_role a
  · exact phaseSixEntry_bias a
  · intro _
    exact phaseSixEntry_hour a

/-! ## Locked Phase-5 pairs -/

private theorem phaseFive_agentPressure_fst_eq
    (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5)
    (hlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i
        (Phase5Transition L K s t).1 =
      Phase6FuelLedger.agentPressure (L := L) (K := K) i s := by
  apply agentPressure_eq_of_static
  · exact Phase5Convergence.Phase5Transition_fst_role_eq
      (L := L) (K := K) s t hs
  · exact Phase5Convergence.Phase5Transition_fst_bias_eq
      (L := L) (K := K) s t hs
  · intro hreserve
    apply Phase5Convergence.Phase5Transition_fst_hour_eq_of_reserve_ne_L
      (L := L) (K := K) s t hreserve
    intro heq
    exact hlocked ⟨hreserve, heq⟩

private theorem phaseFive_agentPressure_snd_eq
    (i : Fin (L + 1)) (s t : AgentState L K)
    (ht : t.phase.val = 5)
    (hlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i
        (Phase5Transition L K s t).2 =
      Phase6FuelLedger.agentPressure (L := L) (K := K) i t := by
  apply agentPressure_eq_of_static
  · exact Phase5Convergence.Phase5Transition_snd_role_eq
      (L := L) (K := K) s t ht
  · exact Phase5Convergence.Phase5Transition_snd_bias_eq
      (L := L) (K := K) s t ht
  · intro hreserve
    apply Phase5Convergence.Phase5Transition_snd_hour_eq_of_reserve_ne_L
      (L := L) (K := K) s t hreserve
    intro heq
    exact hlocked ⟨hreserve, heq⟩

private theorem phaseFive_twoAgentPressure_fst_eq
    (l : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5)
    (hlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
        (Phase5Transition L K s t).1 =
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l s := by
  apply twoAgentPressure_eq_of_static
  · exact Phase5Convergence.Phase5Transition_fst_role_eq
      (L := L) (K := K) s t hs
  · exact Phase5Convergence.Phase5Transition_fst_bias_eq
      (L := L) (K := K) s t hs
  · intro hreserve
    apply Phase5Convergence.Phase5Transition_fst_hour_eq_of_reserve_ne_L
      (L := L) (K := K) s t hreserve
    intro heq
    exact hlocked ⟨hreserve, heq⟩

private theorem phaseFive_twoAgentPressure_snd_eq
    (l : Fin (L + 1)) (s t : AgentState L K)
    (ht : t.phase.val = 5)
    (hlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
        (Phase5Transition L K s t).2 =
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l t := by
  apply twoAgentPressure_eq_of_static
  · exact Phase5Convergence.Phase5Transition_snd_role_eq
      (L := L) (K := K) s t ht
  · exact Phase5Convergence.Phase5Transition_snd_bias_eq
      (L := L) (K := K) s t ht
  · intro hreserve
    apply Phase5Convergence.Phase5Transition_snd_hour_eq_of_reserve_ne_L
      (L := L) (K := K) s t hreserve
    intro heq
    exact hlocked ⟨hreserve, heq⟩

theorem Transition_agentPressure_pair_eq_of_five_five
    (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5)
    (hslocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s)
    (htlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).1 +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).2 =
      Phase6FuelLedger.agentPressure (L := L) (K := K) i s +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i t := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  rw [phaseFive_agentPressure_fst_eq i s t hs hslocked,
      phaseFive_agentPressure_snd_eq i s t ht htlocked]

theorem Transition_twoAgentPressure_pair_eq_of_five_five
    (l : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5)
    (hslocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s)
    (htlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).1 +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).2 =
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l s +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l t := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  rw [phaseFive_twoAgentPressure_fst_eq l s t hs hslocked,
      phaseFive_twoAgentPressure_snd_eq l s t ht htlocked]

/-! ## Exact mixed epidemic and dispatcher reductions -/

theorem phaseEpidemicUpdate_eq_of_five_six
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 6) :
    phaseEpidemicUpdate L K s t =
      (phaseSixEntry (L := L) (K := K) s,
        {t with phase := ⟨6, by decide⟩}) := by
  have hsp : s.phase = ⟨5, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨6, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp]
  simp only [max_eq_right
    (by decide : (⟨5, by decide⟩ : Fin 11) ≤ ⟨6, by decide⟩)]
  unfold runInitsBetween
  have hFiveSix :
      (List.range 11).filter (fun k => 5 < k ∧ k ≤ 6) = [6] := by
    decide
  have hSixSix :
      (List.range 11).filter (fun k => 6 < k ∧ k ≤ 6) = [] := by
    decide
  rw [hFiveSix, hSixSix]
  simp only [List.foldl_cons, List.foldl_nil,
    show (6 < 11) from by decide, dite_true]
  by_cases hclock : s.role = Role.clock <;>
    simp [phaseSixEntry, phaseInit, hclock]

theorem phaseEpidemicUpdate_eq_of_six_five
    (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 5) :
    phaseEpidemicUpdate L K s t =
      ({s with phase := ⟨6, by decide⟩},
        phaseSixEntry (L := L) (K := K) t) := by
  have hsp : s.phase = ⟨6, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨5, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp]
  simp only [max_eq_left
    (by decide : (⟨5, by decide⟩ : Fin 11) ≤ ⟨6, by decide⟩)]
  unfold runInitsBetween
  have hSixSix :
      (List.range 11).filter (fun k => 6 < k ∧ k ≤ 6) = [] := by
    decide
  have hFiveSix :
      (List.range 11).filter (fun k => 5 < k ∧ k ≤ 6) = [6] := by
    decide
  rw [hSixSix, hFiveSix]
  simp only [List.foldl_cons, List.foldl_nil,
    show (6 < 11) from by decide, dite_true]
  by_cases hclock : t.role = Role.clock <;>
    simp [phaseSixEntry, phaseInit, hclock]

theorem Transition_eq_Phase6Transition_of_five_six
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 6) :
    Transition L K s t =
      Phase6Transition L K
        (phaseSixEntry (L := L) (K := K) s)
        {t with phase := ⟨6, by decide⟩} := by
  let sSix := phaseSixEntry (L := L) (K := K) s
  let tSix : AgentState L K := {t with phase := ⟨6, by decide⟩}
  have hepi : phaseEpidemicUpdate L K s t = (sSix, tSix) := by
    simpa [sSix, tSix] using
      phaseEpidemicUpdate_eq_of_five_six (L := L) (K := K) s t hs ht
  have hsSix : sSix.phase.val = 6 := by
    simpa [sSix] using phaseSixEntry_phase (L := L) (K := K) s
  have htSix : tSix.phase.val = 6 := by simp [tSix]
  obtain ⟨hleft, hright⟩ :=
    Phase6Convergence.Phase6Transition_phase_le_seven
      (L := L) (K := K) sSix tSix hsSix htSix
  have hsPhase : sSix.phase = ⟨6, by decide⟩ := Fin.ext hsSix
  unfold Transition
  rw [hepi]
  simp only [hsPhase]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) sSix _ (by omega),
      finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) tSix _ (by omega)]

theorem Transition_eq_Phase6Transition_of_six_five
    (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 5) :
    Transition L K s t =
      Phase6Transition L K
        {s with phase := ⟨6, by decide⟩}
        (phaseSixEntry (L := L) (K := K) t) := by
  let sSix : AgentState L K := {s with phase := ⟨6, by decide⟩}
  let tSix := phaseSixEntry (L := L) (K := K) t
  have hepi : phaseEpidemicUpdate L K s t = (sSix, tSix) := by
    simpa [sSix, tSix] using
      phaseEpidemicUpdate_eq_of_six_five (L := L) (K := K) s t hs ht
  have hsSix : sSix.phase.val = 6 := by simp [sSix]
  have htSix : tSix.phase.val = 6 := by
    simpa [tSix] using phaseSixEntry_phase (L := L) (K := K) t
  obtain ⟨hleft, hright⟩ :=
    Phase6Convergence.Phase6Transition_phase_le_seven
      (L := L) (K := K) sSix tSix hsSix htSix
  have hsPhase : sSix.phase = ⟨6, by decide⟩ := Fin.ext hsSix
  unfold Transition
  rw [hepi]
  simp only [hsPhase]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) sSix _ (by omega),
      finishPhase10Entry_eq_self_of_after_ne_10
        (L := L) (K := K) tSix _ (by omega)]

/-! ## Pairwise pressure inequalities for all mixed cases -/

theorem Transition_agentPressure_pair_le_of_five_six
    (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 6) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).1 +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).2 ≤
      Phase6FuelLedger.agentPressure (L := L) (K := K) i s +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i t := by
  rw [Transition_eq_Phase6Transition_of_five_six
    (L := L) (K := K) s t hs ht]
  let sSix := phaseSixEntry (L := L) (K := K) s
  let tSix : AgentState L K := {t with phase := ⟨6, by decide⟩}
  have hsSix : 6 ≤ sSix.phase.val := by
    rw [show sSix.phase.val = 6 by
      simpa [sSix] using phaseSixEntry_phase (L := L) (K := K) s]
  have htSix : 6 ≤ tSix.phase.val := by simp [tSix]
  calc
    _ ≤ Phase6FuelLedger.agentPressure (L := L) (K := K) i sSix +
          Phase6FuelLedger.agentPressure (L := L) (K := K) i tSix :=
      Phase6FuelLedger.Phase6Transition_agentPressure_pair_le
        (L := L) (K := K) i sSix tSix hsSix htSix
    _ = _ := by simp [sSix, tSix]

theorem Transition_agentPressure_pair_le_of_six_five
    (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 5) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).1 +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).2 ≤
      Phase6FuelLedger.agentPressure (L := L) (K := K) i s +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i t := by
  rw [Transition_eq_Phase6Transition_of_six_five
    (L := L) (K := K) s t hs ht]
  let sSix : AgentState L K := {s with phase := ⟨6, by decide⟩}
  let tSix := phaseSixEntry (L := L) (K := K) t
  have hsSix : 6 ≤ sSix.phase.val := by simp [sSix]
  have htSix : 6 ≤ tSix.phase.val := by
    rw [show tSix.phase.val = 6 by
      simpa [tSix] using phaseSixEntry_phase (L := L) (K := K) t]
  calc
    _ ≤ Phase6FuelLedger.agentPressure (L := L) (K := K) i sSix +
          Phase6FuelLedger.agentPressure (L := L) (K := K) i tSix :=
      Phase6FuelLedger.Phase6Transition_agentPressure_pair_le
        (L := L) (K := K) i sSix tSix hsSix htSix
    _ = _ := by simp [sSix, tSix]

theorem Transition_twoAgentPressure_pair_le_of_five_six
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 6) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).1 +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).2 ≤
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l s +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l t := by
  rw [Transition_eq_Phase6Transition_of_five_six
    (L := L) (K := K) s t hs ht]
  let sSix := phaseSixEntry (L := L) (K := K) s
  let tSix : AgentState L K := {t with phase := ⟨6, by decide⟩}
  have hsSix : 6 ≤ sSix.phase.val := by
    rw [show sSix.phase.val = 6 by
      simpa [sSix] using phaseSixEntry_phase (L := L) (K := K) s]
  have htSix : 6 ≤ tSix.phase.val := by simp [tSix]
  calc
    _ ≤ Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l sSix +
          Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l tSix :=
      Phase6FuelLedger.Phase6Transition_twoAgentPressure_pair_le
        (L := L) (K := K) l hl sSix tSix hsSix htSix
    _ = _ := by simp [sSix, tSix]

theorem Transition_twoAgentPressure_pair_le_of_six_five
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 5) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).1 +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).2 ≤
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l s +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l t := by
  rw [Transition_eq_Phase6Transition_of_six_five
    (L := L) (K := K) s t hs ht]
  let sSix : AgentState L K := {s with phase := ⟨6, by decide⟩}
  let tSix := phaseSixEntry (L := L) (K := K) t
  have hsSix : 6 ≤ sSix.phase.val := by simp [sSix]
  have htSix : 6 ≤ tSix.phase.val := by
    rw [show tSix.phase.val = 6 by
      simpa [tSix] using phaseSixEntry_phase (L := L) (K := K) t]
  calc
    _ ≤ Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l sSix +
          Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l tSix :=
      Phase6FuelLedger.Phase6Transition_twoAgentPressure_pair_le
        (L := L) (K := K) l hl sSix tSix hsSix htSix
    _ = _ := by simp [sSix, tSix]

theorem Transition_agentPressure_pair_le_of_five_or_six
    (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5 ∨ s.phase.val = 6)
    (ht : t.phase.val = 5 ∨ t.phase.val = 6)
    (hslocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s)
    (htlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).1 +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i
          (Transition L K s t).2 ≤
      Phase6FuelLedger.agentPressure (L := L) (K := K) i s +
        Phase6FuelLedger.agentPressure (L := L) (K := K) i t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact (Transition_agentPressure_pair_eq_of_five_five
      (L := L) (K := K) i s t hs ht hslocked htlocked).le
  · exact Transition_agentPressure_pair_le_of_five_six
      (L := L) (K := K) i s t hs ht
  · exact Transition_agentPressure_pair_le_of_six_five
      (L := L) (K := K) i s t hs ht
  · exact Phase6FuelLedger.Transition_agentPressure_pair_le_of_phase6
      (L := L) (K := K) i s t hs ht

theorem Transition_twoAgentPressure_pair_le_of_five_or_six
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 5 ∨ s.phase.val = 6)
    (ht : t.phase.val = 5 ∨ t.phase.val = 6)
    (hslocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s)
    (htlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).1 +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l
          (Transition L K s t).2 ≤
      Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l s +
        Phase6FuelLedger.twoAgentPressure (L := L) (K := K) l t := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact (Transition_twoAgentPressure_pair_eq_of_five_five
      (L := L) (K := K) l s t hs ht hslocked htlocked).le
  · exact Transition_twoAgentPressure_pair_le_of_five_six
      (L := L) (K := K) l hl s t hs ht
  · exact Transition_twoAgentPressure_pair_le_of_six_five
      (L := L) (K := K) l hl s t hs ht
  · exact Phase6FuelLedger.Transition_twoAgentPressure_pair_le_of_phase6
      (L := L) (K := K) l hl s t hs ht

/-! ## Lifting the pair inequalities to configurations -/

private theorem mem_of_app_left
    {c : Config (AgentState L K)} {s t : AgentState L K}
    (happ : Protocol.Applicable c s t) : s ∈ c :=
  Multiset.mem_of_le
    (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right
    {c : Config (AgentState L K)} {s t : AgentState L K}
    (happ : Protocol.Applicable c s t) : t ∈ c :=
  Multiset.mem_of_le
    (show ({s, t} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

theorem fuelPressure_stepOrSelf_le_of_mixed
    (i : Fin (L + 1)) (n : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin n c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (s t : AgentState L K) :
    Phase6FuelLedger.fuelPressure (L := L) (K := K) i
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      Phase6FuelLedger.fuelPressure (L := L) (K := K) i c := by
  by_cases happ : Protocol.Applicable c s t
  · have hsmem := mem_of_app_left happ
    have htmem := mem_of_app_right happ
    have hsphase := hwin.2 s hsmem
    have htphase := hwin.2 t htmem
    have hslocked := not_unsampled_of_reserveSampled c hsampled s hsmem
    have htlocked := not_unsampled_of_reserveSampled c hsampled t htmem
    have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsplit : c = (c - {s, t}) + {s, t} :=
      (tsub_add_cancel_of_le hsub).symm
    have hpair :
        Phase6FuelLedger.fuelPressure (L := L) (K := K) i
            ({(Transition L K s t).1, (Transition L K s t).2} :
              Config (AgentState L K)) ≤
          Phase6FuelLedger.fuelPressure (L := L) (K := K) i
            ({s, t} : Config (AgentState L K)) := by
      rw [Phase6FuelLedger.fuelPressure_pair,
          Phase6FuelLedger.fuelPressure_pair]
      exact Transition_agentPressure_pair_le_of_five_or_six
        (L := L) (K := K) i s t hsphase htphase hslocked htlocked
    rw [hstep, Phase6FuelLedger.fuelPressure_add]
    calc
      _ ≤ Phase6FuelLedger.fuelPressure (L := L) (K := K) i (c - {s, t}) +
            Phase6FuelLedger.fuelPressure (L := L) (K := K) i
              ({s, t} : Config (AgentState L K)) := by gcongr
      _ = Phase6FuelLedger.fuelPressure (L := L) (K := K) i
            ((c - {s, t}) + {s, t}) := by
              rw [Phase6FuelLedger.fuelPressure_add]
      _ = Phase6FuelLedger.fuelPressure (L := L) (K := K) i c := by
              rw [← hsplit]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem twoFuelPressure_stepOrSelf_le_of_mixed
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin n c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (s t : AgentState L K) :
    Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l c := by
  by_cases happ : Protocol.Applicable c s t
  · have hsmem := mem_of_app_left happ
    have htmem := mem_of_app_right happ
    have hsphase := hwin.2 s hsmem
    have htphase := hwin.2 t htmem
    have hslocked := not_unsampled_of_reserveSampled c hsampled s hsmem
    have htlocked := not_unsampled_of_reserveSampled c hsampled t htmem
    have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
    have hstep :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsplit : c = (c - {s, t}) + {s, t} :=
      (tsub_add_cancel_of_le hsub).symm
    have hpair :
        Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l
            ({(Transition L K s t).1, (Transition L K s t).2} :
              Config (AgentState L K)) ≤
          Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l
            ({s, t} : Config (AgentState L K)) := by
      rw [Phase6FuelLedger.twoFuelPressure_pair,
          Phase6FuelLedger.twoFuelPressure_pair]
      exact Transition_twoAgentPressure_pair_le_of_five_or_six
        (L := L) (K := K) l hl s t hsphase htphase hslocked htlocked
    rw [hstep, Phase6FuelLedger.twoFuelPressure_add]
    calc
      _ ≤ Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l (c - {s, t}) +
            Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l
              ({s, t} : Config (AgentState L K)) := by gcongr
      _ = Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l
            ((c - {s, t}) + {s, t}) := by
              rw [Phase6FuelLedger.twoFuelPressure_add]
      _ = Phase6FuelLedger.twoFuelPressure (L := L) (K := K) l c := by
              rw [← hsplit]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-! ## Ledger and sample-lock preservation -/

theorem fuelLedger_stepOrSelf_of_mixed
    (i : Fin (L + 1)) (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin n c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (hledger : Phase6FuelLedger.FuelLedger (L := L) (K := K) i K₀ c)
    (s t : AgentState L K) :
    Phase6FuelLedger.FuelLedger (L := L) (K := K) i K₀
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  rw [Phase6FuelLedger.fuelLedger_iff_pressure] at hledger ⊢
  have hpressure := fuelPressure_stepOrSelf_le_of_mixed
    (L := L) (K := K) i n c hwin hsampled s t
  have hcard := Protocol.stepOrSelf_card_eq
    (P := NonuniformMajority L K) c s t
  rw [hcard]
  omega

theorem unionFuelLedger_stepOrSelf_of_mixed
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin n c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (hledger : Phase6FuelLedger.UnionFuelLedger (L := L) (K := K) l K₀ c)
    (s t : AgentState L K) :
    Phase6FuelLedger.UnionFuelLedger (L := L) (K := K) l K₀
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  rw [Phase6FuelLedger.unionFuelLedger_iff_pressure] at hledger ⊢
  have hpressure := twoFuelPressure_stepOrSelf_le_of_mixed
    (L := L) (K := K) l hl n c hwin hsampled s t
  have hcard := Protocol.stepOrSelf_card_eq
    (P := NonuniformMajority L K) c s t
  rw [hcard]
  omega

/-- The requested mixed-window ledger theorem.  On the homogeneous-six
subcase it deliberately reuses the existing Phase-6 consumer; the genuinely
mixed subcase is discharged by the pressure lemmas above. -/
theorem twoLevelFuelLedger_stepOrSelf_of_mixed
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin n c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (hledger : Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) l K₀ c)
    (s t : AgentState L K) :
    Phase6FuelLedger.TwoLevelFuelLedger (L := L) (K := K) l K₀
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases hsix : Phase6Convergence.Phase6Win (L := L) (K := K) n c
  · exact Phase6FuelLedger.twoLevelFuelLedger_stepOrSelf
      (L := L) (K := K) l hl K₀ n c hsix hledger s t
  · rcases hledger with hlower | hunion
    · exact Or.inl (fuelLedger_stepOrSelf_of_mixed
        (L := L) (K := K) l K₀ n c hwin hsampled hlower s t)
    · exact Or.inr (unionFuelLedger_stepOrSelf_of_mixed
        (L := L) (K := K) l hl K₀ n c hwin hsampled hunion s t)

theorem reserveSampled_stepOrSelf_of_mixed
    (n : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin n c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (s t : AgentState L K) :
    ReserveSampling.ReserveSampled (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hle := ReserveSampling.unsampledReserveU_superStepOrSelf_le
    (L := L) (K := K) n c (mixedFiveSixWin_phaseGE5 n c hwin) s t
  unfold ReserveSampling.ReserveSampled at hsampled ⊢
  omega

theorem mixedFiveSix_step_preserves
    (l : Fin (L + 1)) (hl : l.val + 2 ≤ L)
    (K₀ n : ℕ) (c : Config (AgentState L K))
    (hwin : MixedFiveSixWin n c)
    (hledger : Phase6FuelLedger.TwoLevelFuelLedger
      (L := L) (K := K) l K₀ c)
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (s t : AgentState L K) :
    Phase6FuelLedger.TwoLevelFuelLedger (L := L) (K := K) l K₀
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ∧
      ReserveSampling.ReserveSampled (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  exact
    ⟨twoLevelFuelLedger_stepOrSelf_of_mixed
        (L := L) (K := K) l hl K₀ n c hwin hsampled hledger s t,
      reserveSampled_stepOrSelf_of_mixed
        (L := L) (K := K) n c hwin hsampled s t⟩

end Ripple.PopulationProtocol.ExactMajority.LateMixedFuelLedger

end
