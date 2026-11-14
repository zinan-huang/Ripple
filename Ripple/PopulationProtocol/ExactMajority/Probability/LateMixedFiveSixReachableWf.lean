-- Ripple/PopulationProtocol/ExactMajority/Probability/LateMixedFiveSixReachableWf.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFiveSixWindow
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceOvershootSource
import Ripple.PopulationProtocol.ExactMajority.Analysis.DeterministicChain

/-!
# Reachable well-formedness on the mixed Phase-5/6 window

`AdvanceNoOvershoot.Wf` is false on arbitrary configurations.  On the trace of
a valid initial configuration, however, every agent at a non-error phase at
least two has calibrated `smallBias` in `{2,3,4}`.  Reachable agent
well-formedness also excludes the `mcr` role at phases `1` through `9`.
Consequently every reachable configuration whose phases lie in `[2,9]` is
`AdvanceNoOvershoot.Wf`; in particular this holds at every source time and at
the homogeneous-six endpoint of `LateMixedFuel.MixedFiveSixPrefix`.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixReachableWf

open TimeTheorem
open LateMixedFuel

variable {L K n : ℕ}

/-- Unbounded Phase-2 calibration on the reachable set.  Once an agent has
reached phase two, its `smallBias` remains in `{2,3,4}` unless it is on the
Phase-10 error track. -/
theorem reachable_phase_ge_two_ne_ten_smallBias_noerror
    (init c : Config (AgentState L K))
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c) :
    ∀ a ∈ c, 2 ≤ a.phase.val → a.phase.val ≠ 10 →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  induction hreach with
  | refl =>
      intro a ha hge _
      have hphase := (hvalid a ha).1
      have hzero : a.phase.val = 0 := by simpa [hphase]
      omega
  | tail _ hstep ih =>
      rcases hstep with ⟨r₁, r₂, happ, hc'⟩
      dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
      have hr₁mem : r₁ ∈ _ := Multiset.mem_of_le happ (by simp)
      have hr₂mem : r₂ ∈ _ := Multiset.mem_of_le happ (by simp)
      rw [hc']
      intro a ha hge hne
      simp only [Multiset.mem_add, Multiset.mem_cons,
        Multiset.mem_singleton] at ha
      rcases ha with hold | hnew
      · exact ih a (Multiset.mem_of_le (Multiset.sub_le_self _ {r₁, r₂}) hold)
          hge hne
      · rcases hnew with hleft | hright
        · subst a
          by_cases hr₁ge : 2 ≤ r₁.phase.val
          · have hmono := Transition_phase_monotone
              (L := L) (K := K) r₁ r₂
            have hr₁ne : r₁.phase.val ≠ 10 := by
              intro hten
              have hout := (Transition L K r₁ r₂).1.phase.isLt
              have hle := hmono.1
              apply hne
              omega
            rw [Transition_left_preserves_smallBias_of_phase_ge_two
              (L := L) (K := K) r₁ r₂ hr₁ge]
            exact ih r₁ hr₁mem hr₁ge hr₁ne
          · push_neg at hr₁ge
            have hep_le :=
              (phaseEpidemicUpdate_phase_le_Transition_phase
                (L := L) (K := K) r₁ r₂).1
            by_cases hep_ge :
                2 ≤ (phaseEpidemicUpdate L K r₁ r₂).1.phase.val
            · have hep_ne :
                  (phaseEpidemicUpdate L K r₁ r₂).1.phase.val ≠ 10 := by
                intro hten
                have hout := (Transition L K r₁ r₂).1.phase.isLt
                apply hne
                omega
              rw [Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
                (L := L) (K := K) r₁ r₂ hep_ge]
              exact phaseEpidemicUpdate_left_smallBias_noerror_of_entered_not_ten
                (L := L) (K := K) r₁ r₂ hr₁ge hep_ge hep_ne
            · push_neg at hep_ge
              have hout_le :=
                Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
                  (L := L) (K := K) r₁ r₂ hep_ge hne
              have hout_eq : (Transition L K r₁ r₂).1.phase.val = 2 := by
                omega
              exact Transition_left_phase2_smallBias_noerror_of_input_lt_two
                (L := L) (K := K) r₁ r₂ hr₁ge hout_eq
        · subst a
          by_cases hr₂ge : 2 ≤ r₂.phase.val
          · have hmono := Transition_phase_monotone
              (L := L) (K := K) r₁ r₂
            have hr₂ne : r₂.phase.val ≠ 10 := by
              intro hten
              have hout := (Transition L K r₁ r₂).2.phase.isLt
              have hle := hmono.2
              apply hne
              omega
            rw [Transition_right_preserves_smallBias_of_phase_ge_two
              (L := L) (K := K) r₁ r₂ hr₂ge]
            exact ih r₂ hr₂mem hr₂ge hr₂ne
          · push_neg at hr₂ge
            have hep_le :=
              (phaseEpidemicUpdate_phase_le_Transition_phase
                (L := L) (K := K) r₁ r₂).2
            by_cases hep_ge :
                2 ≤ (phaseEpidemicUpdate L K r₁ r₂).2.phase.val
            · have hep_ne :
                  (phaseEpidemicUpdate L K r₁ r₂).2.phase.val ≠ 10 := by
                intro hten
                have hout := (Transition L K r₁ r₂).2.phase.isLt
                apply hne
                omega
              have hep_left_ge :
                  2 ≤ (phaseEpidemicUpdate L K r₁ r₂).1.phase.val := by
                by_contra h
                push_neg at h
                have hmax := phaseEpidemicUpdate_left_phase_ge_max
                  (L := L) (K := K) r₁ r₂
                have hr₁le : r₁.phase.val ≤ 2 := by
                  have hside := le_max_left r₁.phase.val r₂.phase.val
                  omega
                have hr₂le : r₂.phase.val ≤ 2 := by
                  have hside := le_max_right r₁.phase.val r₂.phase.val
                  omega
                have heq :=
                  phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
                    (L := L) (K := K) r₁ r₂ hr₁le hr₂le
                    (by omega) hep_ne
                omega
              rw [Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
                (L := L) (K := K) r₁ r₂ hep_left_ge]
              exact phaseEpidemicUpdate_right_smallBias_noerror_of_entered_not_ten
                (L := L) (K := K) r₁ r₂ hr₂ge hep_ge hep_ne
            · push_neg at hep_ge
              have hmax := phaseEpidemicUpdate_right_phase_ge_max
                (L := L) (K := K) r₁ r₂
              have hr₁lt : r₁.phase.val < 2 := by
                have hside := le_max_left r₁.phase.val r₂.phase.val
                omega
              have hr₂lt : r₂.phase.val < 2 := by
                have hside := le_max_right r₁.phase.val r₂.phase.val
                omega
              have hep_left_ne :
                  (phaseEpidemicUpdate L K r₁ r₂).1.phase.val ≠ 10 := by
                intro hten
                have hboth :=
                  (phaseEpidemicUpdate_phases_both_ten_or_neither
                    (L := L) (K := K) r₁ r₂ (by omega) (by omega)).mp hten
                omega
              have hep_left_lt :
                  (phaseEpidemicUpdate L K r₁ r₂).1.phase.val < 2 :=
                phaseEpidemicUpdate_left_phase_lt_two_of_both_lt_two_of_ne_ten
                  (L := L) (K := K) r₁ r₂ hr₁lt hr₂lt hep_left_ne
              have hout_le :=
                Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
                  (L := L) (K := K) r₁ r₂ hep_left_lt hne
              have hout_eq : (Transition L K r₁ r₂).2.phase.val = 2 := by
                omega
              exact Transition_right_phase2_smallBias_noerror_of_input_lt_two
                (L := L) (K := K) r₁ r₂ hr₂ge hout_eq

/-- Reachable-agent form of `AdvanceNoOvershoot.WfAgent`.  The phase interval
`[2,9]` excludes both role-error endpoints and the Phase-10 bias-error track. -/
theorem wfAgent_of_reachable_phase_range
    {init c : Config (AgentState L K)}
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    {a : AgentState L K} (ha : a ∈ c)
    (hlo : 2 ≤ a.phase.val) (hhi : a.phase.val ≤ 9) :
    AdvanceNoOvershoot.WfAgent a := by
  have hagent := reachable_preserves_well_formed_agents
    (L := L) (K := K) init c hvalid hreach a ha
  have hsmall := reachable_phase_ge_two_ne_ten_smallBias_noerror
    init c hvalid hreach a ha hlo (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsmall
  exact ⟨hagent.not_mcr_of_intermediate_phase (by omega) hhi,
    by omega, by omega⟩

/-- Every reachable configuration whose phases lie in `[2,9]` is `Wf`. -/
theorem wf_of_reachable_phase_range
    {init c : Config (AgentState L K)}
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hlo : ∀ a ∈ c, 2 ≤ a.phase.val)
    (hhi : ∀ a ∈ c, a.phase.val ≤ 9) :
    AdvanceNoOvershoot.Wf c := by
  intro a ha
  exact wfAgent_of_reachable_phase_range hvalid hreach ha
    (hlo a ha) (hhi a ha)

/-- Seam-shaped form.  On a reachable `p/p+1` configuration with
`2 ≤ p ≤ 8`, `Wf` is automatic. -/
theorem wf_of_reachable_seam_window
    {init c : Config (AgentState L K)}
    (hvalid : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    {p : ℕ} (hp : 2 ≤ p) (hpmax : p ≤ 8)
    (hge : ∀ a ∈ c, p ≤ a.phase.val)
    (hno : ∀ a ∈ c, a.phase.val < p + 2) :
    AdvanceNoOvershoot.Wf c := by
  apply wf_of_reachable_phase_range hvalid hreach
  · intro a ha
    exact hp.trans (hge a ha)
  · intro a ha
    have hupper := hno a ha
    omega

/-- Per-configuration mixed-5/6 form.  Cardinality is irrelevant to `Wf`; the
phase clause of `MixedFiveSixWin` and reachability are sufficient. -/
theorem wf_of_reachable_mixedFiveSixWin
    {init c : InputCfg n}
    (hvalid : validInitial init)
    (hreach :
      (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
        init c)
    (hwindow : LateMixedFuelLedger.MixedFiveSixWin n c) :
    AdvanceNoOvershoot.Wf c := by
  apply wf_of_reachable_seam_window hvalid hreach
    (p := 5) (by norm_num) (by norm_num)
  · intro a ha
    rcases hwindow.2 a ha with h | h <;> omega
  · intro a ha
    rcases hwindow.2 a ha with h | h <;> omega

private theorem trace_reachable_from_initial
    (init : InputCfg n) (ω : InputLog n) (t : ℕ) :
    (NonuniformMajority (PhaseThreeModel.Numeric.hourIndex n) 256).Reachable
      init (trace init ω t) := by
  simpa only [TimeTheorem.trace_zero] using
    (TimeTheorem.trace_reachable init ω
      (s := 0) (t := t) (Nat.zero_le t))

/-- The inclusive phase range of a genuine mixed-5/6 prefix.  Source times are
mixed 5/6; the endpoint is homogeneous Phase 6. -/
theorem mixedFiveSixPrefix_phase_range
    {init : InputCfg n} {ω : InputLog n} {u v t : ℕ}
    (hwindow : MixedFiveSixPrefix init ω u v)
    (hut : u ≤ t) (htv : t ≤ v) :
    ∀ a ∈ trace init ω t, 5 ≤ a.phase.val ∧ a.phase.val ≤ 6 := by
  intro a ha
  by_cases hsource : t < v
  · rcases (hwindow.source_window t hut hsource).2 a ha with h | h <;>
      omega
  · have ht : t = v := by omega
    subst t
    have hphase : a.phase.val = 6 := hwindow.endpoint_phase_six a ha
    omega

/-- Consumer-facing pathwise theorem: every source configuration in the actual
mixed Phase-5/6 window is reachable-`Wf`. -/
theorem mixedFiveSixPrefix_wf_source
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n} {u v : ℕ}
    (hwindow : MixedFiveSixPrefix init ω u v) :
    ∀ t, u ≤ t → t < v →
      AdvanceNoOvershoot.Wf (trace init ω t) := by
  intro t hut htv
  exact wf_of_reachable_mixedFiveSixWin hvalid
    (trace_reachable_from_initial init ω t)
    (hwindow.source_window t hut htv)

/-- Stronger closed-window form, including the homogeneous Phase-6 endpoint. -/
theorem mixedFiveSixPrefix_wf_closed
    {init : InputCfg n} (hvalid : validInitial init)
    {ω : InputLog n} {u v : ℕ}
    (hwindow : MixedFiveSixPrefix init ω u v) :
    ∀ t, u ≤ t → t ≤ v →
      AdvanceNoOvershoot.Wf (trace init ω t) := by
  intro t hut htv
  have hrange := mixedFiveSixPrefix_phase_range hwindow hut htv
  apply wf_of_reachable_phase_range hvalid
    (trace_reachable_from_initial init ω t)
  · intro a ha
    have h := (hrange a ha).1
    omega
  · intro a ha
    have h := (hrange a ha).2
    omega

/-!
THEOREM LIST
* `reachable_phase_ge_two_ne_ten_smallBias_noerror`
* `wfAgent_of_reachable_phase_range`
* `wf_of_reachable_phase_range`
* `wf_of_reachable_seam_window`
* `wf_of_reachable_mixedFiveSixWin`
* `mixedFiveSixPrefix_phase_range`
* `mixedFiveSixPrefix_wf_source`
* `mixedFiveSixPrefix_wf_closed`

CLOSES
* The reachable replacement for the false global `∀ c, Wf c` premise.
* Automatic `Wf` on every valid-initial reachable configuration with phases
  in `[2,9]`, hence on every mixed Phase-5/6 source configuration.
* The exact half-open theorem consumed by a mixed-window step argument, plus
  the stronger inclusive theorem through the homogeneous-six endpoint.

EXPLICIT INPUTS
* `validInitial init`; this is the standard good-input pathwise hypothesis.
* `MixedFiveSixPrefix init ω u v`, already produced by
  `LateMixedFiveSixWindow` from completion and the timer/epidemic race.

UNFINISHED
* Replacing the vacuous global `hWf : ∀ c, Wf c` field in downstream window
  tails by `mixedFiveSixPrefix_wf_source` is a separate wiring change.
* The original-law tail for `LateMixedFiveSixWindow.mixedFailure` remains the
  separate probabilistic item recorded by that module.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateMixedFiveSixReachableWf

end
