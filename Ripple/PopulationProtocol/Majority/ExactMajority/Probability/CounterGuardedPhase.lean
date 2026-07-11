import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealKernel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MarkovChain
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Scheduler

/-!
# Counter-guarded phase preservation (phases 5–8)

In the Doty et al. exact-majority protocol, throughout phases `N ∈ {5,6,7,8}` the
ONLY mechanism that advances an agent's phase is the clock **Standard Counter
Subroutine** `stdCounterSubroutine`: a `Role.clock` agent with `counter.val = 0`
runs `advancePhaseWithInit` (advancing the phase), while a clock with
`counter.val ≥ 1` merely decrements its counter (phase unchanged).  Non-clock
agents do not advance their phase within these phases — the phase-`N` payload
(`doSample` / `doSplit` / `cancelSplit` / `absorbConsume`) only edits
`hour` / `bias` / `role` / `full`, never `phase`.

The phase-epidemic pre-pass `phaseEpidemicUpdate` only raises an agent toward its
partner's phase (`max`), so on two agents that share phase `N` it is the identity;
`finishPhase10Entry` only acts on phase-10 entrants, so for an output that stays
at phase `N ≤ 8 ≠ 10` it is the identity.

**Conclusion (this file).**  If every agent of a config `c` is at phase `N` and
every `Role.clock` agent of `c` has `counter.val > 0`, then after one protocol
step every agent is still at phase `N`: no clock is at counter `0`, so nothing
advances.  This is `allPhaseN_preserved_of_counterPos`, proved generically in
`N ∈ {5,6,7,8}` via four per-phase per-pair lemmas.

Phase-8 subtlety: the destination phase-9 `phaseInit` carries a `|bias| > 1`
guard that could jump an advancing agent to phase 10 — but under the
counter-positive guard NO phase-8 clock advances at all (every clock just
decrements), so that guard is never reached and phase 8 is preserved cleanly.
-/

namespace ExactMajority
namespace CounterGuardedPhase

open Protocol ProbabilityTheory ClockRealKernel
open scoped ENNReal

variable {L K : ℕ}

/-! ### Standard counter subroutine: phase fixed while the counter is positive -/

/-- While the counter is positive, the standard counter subroutine leaves the
phase unchanged (it just decrements the counter, taking the non-advancing
branch). -/
theorem stdCounterSubroutine_phase_eq_of_pos
    (a : AgentState L K) (hpos : 0 < a.counter.val) :
    (stdCounterSubroutine L K a).phase.val = a.phase.val := by
  have hne : a.counter.val ≠ 0 := by omega
  simp [stdCounterSubroutine, hne]

/-- The clock-guarded output coordinate `if s1.role = clock then stdCSR s1 else s1`
stays at phase `N`, provided `s1` is already at phase `N`, and — when it is a
clock — has a positive counter (so the counter subroutine merely decrements). -/
theorem clockGuard_phase_eq
    (N : ℕ) (s1 : AgentState L K) (hphase : s1.phase.val = N)
    (hpos : s1.role = .clock → 0 < s1.counter.val) :
    (if s1.role = .clock then stdCounterSubroutine L K s1 else s1).phase.val = N := by
  by_cases hcl : s1.role = .clock
  · rw [if_pos hcl, stdCounterSubroutine_phase_eq_of_pos s1 (hpos hcl), hphase]
  · rw [if_neg hcl, hphase]

/-! ### Phase-epidemic pre-pass is the identity on a same-phase pair (5–8) -/

/-- For two agents sharing phase `N ≠ 10`, the phase-epidemic pre-pass is the
identity. -/
theorem phaseEpidemicUpdate_eq_self_of_phase_eq
    (s t : AgentState L K) (N : ℕ) (hN : N ≠ 10)
    (hs : s.phase.val = N) (ht : t.phase.val = N) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hst : s.phase = t.phase := by
    apply Fin.ext; rw [hs, ht]
  unfold phaseEpidemicUpdate
  rw [hst, max_self]
  simp only [runInitsBetween_self_api]
  have hne : ¬ (t.phase.val = 10) := by rw [ht]; exact hN
  rw [if_neg (by tauto)]
  cases s; cases t; simp_all

/-! ### Payload field-preservation lemmas (phase / role / counter)

The phase-`N` payloads `doSplit` / `cancelSplit` / `absorbConsume` are pure
record updates that never write `.phase`, `.counter`, nor (on the relevant
coordinate) `.role`.  We record the exact equalities we need. -/

@[simp] lemma doSplit_phase_fst (r m : AgentState L K) :
    (doSplit L K r m).1.phase = r.phase := by
  unfold doSplit; match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma doSplit_phase_snd (r m : AgentState L K) :
    (doSplit L K r m).2.phase = m.phase := by
  unfold doSplit; match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma doSplit_counter_fst (r m : AgentState L K) :
    (doSplit L K r m).1.counter = r.counter := by
  unfold doSplit; match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma doSplit_counter_snd (r m : AgentState L K) :
    (doSplit L K r m).2.counter = m.counter := by
  unfold doSplit; match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma doSplit_role_fst (r m : AgentState L K) :
    (doSplit L K r m).1.role = r.role ∨ (doSplit L K r m).1.role = Role.main := by
  unfold doSplit; match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_phase_fst (s t : AgentState L K) :
    (cancelSplit L K s t).1.phase = s.phase := by
  unfold cancelSplit; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_phase_snd (s t : AgentState L K) :
    (cancelSplit L K s t).2.phase = t.phase := by
  unfold cancelSplit; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_counter_fst (s t : AgentState L K) :
    (cancelSplit L K s t).1.counter = s.counter := by
  unfold cancelSplit; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_counter_snd (s t : AgentState L K) :
    (cancelSplit L K s t).2.counter = t.counter := by
  unfold cancelSplit; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma absorbConsume_phase_fst (s t : AgentState L K) :
    (absorbConsume L K s t).1.phase = s.phase := by
  unfold absorbConsume; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

@[simp] lemma absorbConsume_phase_snd (s t : AgentState L K) :
    (absorbConsume L K s t).2.phase = t.phase := by
  unfold absorbConsume; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

@[simp] lemma absorbConsume_counter_fst (s t : AgentState L K) :
    (absorbConsume L K s t).1.counter = s.counter := by
  unfold absorbConsume; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

@[simp] lemma absorbConsume_counter_snd (s t : AgentState L K) :
    (absorbConsume L K s t).2.counter = t.counter := by
  unfold absorbConsume; match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-! ### Per-phase per-pair core lemmas -/

/-- **Phase 5 per-pair.**  Two phase-5 agents, with every clock counter positive,
stay at phase 5 after the inner `Phase5Transition`. -/
theorem phase5Transition_pair_preserved (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5)
    (hs_pos : s.role = .clock → 0 < s.counter.val)
    (ht_pos : t.role = .clock → 0 < t.counter.val) :
    (Phase5Transition L K s t).1.phase.val = 5 ∧
      (Phase5Transition L K s t).2.phase.val = 5 := by
  unfold Phase5Transition
  dsimp only
  constructor
  · apply clockGuard_phase_eq 5
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl
      split_ifs with h1 h2 <;> intro hcl <;> simp_all
  · apply clockGuard_phase_eq 5
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl
      split_ifs with h1 h2 <;> intro hcl <;> simp_all

/-- **Phase 6 per-pair.** -/
theorem phase6Transition_pair_preserved (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6)
    (hs_pos : s.role = .clock → 0 < s.counter.val)
    (ht_pos : t.role = .clock → 0 < t.counter.val) :
    (Phase6Transition L K s t).1.phase.val = 6 ∧
      (Phase6Transition L K s t).2.phase.val = 6 := by
  unfold Phase6Transition
  dsimp only
  refine ⟨?_, ?_⟩
  · apply clockGuard_phase_eq 6
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl; split_ifs with h1 h2 <;> intro hcl
      · -- s1 = (doSplit s t).1, role ∈ {s.role, main}; but h1 forces s.role = reserve.
        rcases doSplit_role_fst s t with hr | hr <;> rw [hr] at hcl <;>
          simp_all
      · -- s1 = (doSplit t s).2, role = main (snd preserves m.role = s.role = main here).
        rw [doSplit_role_snd] at hcl; simp_all
      · exact hs_pos hcl
  · apply clockGuard_phase_eq 6
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl; split_ifs with h1 h2 <;> intro hcl
      · rw [doSplit_role_snd] at hcl; simp_all
      · rcases doSplit_role_fst t s with hr | hr <;> rw [hr] at hcl <;> simp_all
      · exact ht_pos hcl

/-- **Phase 7 per-pair.** -/
theorem phase7Transition_pair_preserved (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hs_pos : s.role = .clock → 0 < s.counter.val)
    (ht_pos : t.role = .clock → 0 < t.counter.val) :
    (Phase7Transition L K s t).1.phase.val = 7 ∧
      (Phase7Transition L K s t).2.phase.val = 7 := by
  unfold Phase7Transition
  dsimp only
  refine ⟨?_, ?_⟩
  · apply clockGuard_phase_eq 7
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
      · rw [cancelSplit_role_fst] at hcl; simp_all
      · exact hs_pos hcl
  · apply clockGuard_phase_eq 7
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
      · rw [cancelSplit_role_snd] at hcl; simp_all
      · exact ht_pos hcl

/-- **Phase 8 per-pair.**  Note: NO phase-8 clock advances here (counter
positive), so the destination phase-9 `phaseInit` `|bias|>1` guard is never
reached and phase 8 is preserved cleanly. -/
theorem phase8Transition_pair_preserved (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hs_pos : s.role = .clock → 0 < s.counter.val)
    (ht_pos : t.role = .clock → 0 < t.counter.val) :
    (Phase8Transition L K s t).1.phase.val = 8 ∧
      (Phase8Transition L K s t).2.phase.val = 8 := by
  unfold Phase8Transition
  dsimp only
  refine ⟨?_, ?_⟩
  · apply clockGuard_phase_eq 8
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
      · rw [absorbConsume_role_fst] at hcl; simp_all
      · exact hs_pos hcl
  · apply clockGuard_phase_eq 8
    · split_ifs <;> simp [hs, ht]
    · intro hcl; revert hcl; split_ifs with h1 <;> intro hcl
      · rw [absorbConsume_role_snd] at hcl; simp_all
      · exact ht_pos hcl

/-! ### Full `Transition` per-pair lemma (generic in `N ∈ {5,6,7,8}`) -/

/-- **Per-pair phase preservation, full dispatcher.**  For a same-phase pair at
phase `N ∈ {5,6,7,8}` with every clock counter positive, the full `Transition`
keeps both interacting agents at phase `N`.  Wraps the epidemic pre-pass
(identity on a same-phase pair), the matching inner `PhaseNTransition` lemma, and
the `finishPhase10Entry` finisher (identity since the output is `N ≠ 10`). -/
theorem transition_pair_phase_eq_of_counterPos
    (N : ℕ) (hN5 : 5 ≤ N) (hN8 : N ≤ 8) (s t : AgentState L K)
    (hs : s.phase.val = N) (ht : t.phase.val = N)
    (hs_pos : s.role = .clock → 0 < s.counter.val)
    (ht_pos : t.role = .clock → 0 < t.counter.val) :
    (Transition L K s t).1.phase.val = N ∧ (Transition L K s t).2.phase.val = N := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase_eq s t N (by omega) hs ht
  -- assemble: dispatcher matches on s'.phase = s.phase, then finishPhase10Entry is identity
  constructor
  · simp only [Transition, hepi]
    rw [finishPhase10Entry_phase_val]
    -- the dispatcher's match on `s.phase` (= the only phases in range) reduces
    have hcases : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 := by omega
    rcases hcases with h | h | h | h <;> subst h <;>
      (first
        | (rw [show s.phase = ⟨5, by decide⟩ from Fin.ext hs]; exact (phase5Transition_pair_preserved s t hs ht hs_pos ht_pos).1)
        | (rw [show s.phase = ⟨6, by decide⟩ from Fin.ext hs]; exact (phase6Transition_pair_preserved s t hs ht hs_pos ht_pos).1)
        | (rw [show s.phase = ⟨7, by decide⟩ from Fin.ext hs]; exact (phase7Transition_pair_preserved s t hs ht hs_pos ht_pos).1)
        | (rw [show s.phase = ⟨8, by decide⟩ from Fin.ext hs]; exact (phase8Transition_pair_preserved s t hs ht hs_pos ht_pos).1))
  · simp only [Transition, hepi]
    rw [finishPhase10Entry_phase_val]
    have hcases : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 := by omega
    rcases hcases with h | h | h | h <;> subst h <;>
      (first
        | (rw [show s.phase = ⟨5, by decide⟩ from Fin.ext hs]; exact (phase5Transition_pair_preserved s t hs ht hs_pos ht_pos).2)
        | (rw [show s.phase = ⟨6, by decide⟩ from Fin.ext hs]; exact (phase6Transition_pair_preserved s t hs ht hs_pos ht_pos).2)
        | (rw [show s.phase = ⟨7, by decide⟩ from Fin.ext hs]; exact (phase7Transition_pair_preserved s t hs ht hs_pos ht_pos).2)
        | (rw [show s.phase = ⟨8, by decide⟩ from Fin.ext hs]; exact (phase8Transition_pair_preserved s t hs ht hs_pos ht_pos).2))

/-! ### Support-point lift: one full kernel step preserves "all at phase `N`" -/

/-- **Counter-guarded phase preservation (the deliverable).**  For `N ∈ {5,6,7,8}`:
if every agent of `c` is at phase `N` and every `Role.clock` agent of `c` has
`counter.val > 0`, then every support point `c'` of one kernel step
(`stepDistOrSelf`) again has every agent at phase `N`.

No clock is at counter `0`, so the only phase-advancing mechanism never fires;
every output agent is either an untouched survivor (still phase `N` by `hphase`)
or one of the two interacting agents (phase `N` by
`transition_pair_phase_eq_of_counterPos`). -/
theorem allPhaseN_preserved_of_counterPos
    (N n : ℕ) (hN5 : 5 ≤ N) (hN8 : N ≤ 8)
    (c c' : Config (AgentState L K))
    (hcard : c.card = n)
    (hphase : ∀ a ∈ c, a.phase.val = N)
    (hpos : ∀ a ∈ c, a.role = Role.clock → 0 < a.counter.val)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ∀ a ∈ c', a.phase.val = N := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ :=
      Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    simp only [Protocol.scheduledStep]
    by_cases happ : Protocol.Applicable c r₁ r₂
    · have hmem1 : r₁ ∈ c := mem_of_applicable_left happ
      have hmem2 : r₂ ∈ c := mem_of_applicable_right happ
      have hc'eq : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
          = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
        unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
      -- per-pair phase preservation for the interacting pair
      have hpair := transition_pair_phase_eq_of_counterPos N hN5 hN8 r₁ r₂
        (hphase r₁ hmem1) (hphase r₂ hmem2) (hpos r₁ hmem1) (hpos r₂ hmem2)
      intro a ha
      rw [hc'eq] at ha
      rcases Multiset.mem_add.mp ha with hin | hin
      · -- survivor from `c`: phase `N` by `hphase`.
        exact hphase a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hin)
      · -- one of the two interaction outputs: phase `N` by `hpair`.
        rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0
            from rfl] at hin
        rcases Multiset.mem_cons.mp hin with rfl | hin
        · exact hpair.1
        · rcases Multiset.mem_cons.mp hin with rfl | hin
          · exact hpair.2
          · simp at hin
    · -- non-applicable pair: `stepOrSelf` is the identity, so `c' = c`.
      rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
      exact hphase
  · -- `card < 2`: `stepDistOrSelf` is `pure c`, so `c' = c`.
    rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact hphase

end CounterGuardedPhase
end ExactMajority
