/-
# Live fields of the Doty et al. protocol (state count)

The flat state `AgentState L K` carries every field in every phase, which gives the
`O((L+1)^4)` count of `state_count_eq`. The paper (§3.4, footnote 13) keeps `Θ(log n)` states
because each role reads at most one `Θ(log n)`-valued field in each phase. This file writes
down that table for the Lean transition `Transition` and the normal form it induces.

* `liveBias p r`, `liveHour p r z`, `liveMinute p r`, `liveCounter p r m`: whether the fields
  `bias`, `hour`, `minute`, `counter` are read by the transition for an agent in phase `p` with
  role `r` (with `z` = "bias is zero", `m` = "minute is at its maximum"). The eight remaining
  fields (`input`, `output`, `phase`, `role`, `assigned`, `smallBias`, `full`, `opinions`) have
  `O(1)` values and are always kept.
* `normalize a` resets every dead field to a default; `normalizeAt j a` does so as if the agent
  were in phase `j` (used along the Init chain of the phase epidemic, which sets the phase field
  before running the Inits of the phases in between).
* `Good a`: the one reachability invariant the count needs. A phase-3 Clock has `bias = 0` and,
  while its `minute` is below `K (L+1)`, its `counter` still has the Init value `50 (L+1)`
  (the paper initializes the counter only when the minute reaches its maximum, §3.4 Phase 3).

The table (read off `Protocol/Transition.lean`; `.` = dead):

| phase | Main | Reserve | Clock | MCR / CR |
|---|---|---|---|---|
| 0, 1 | . | . | counter | . |
| 2, 9, 10 | . | . | . | . |
| 3 | bias, and hour iff bias = 0 | bias | minute, counter iff minute = max | bias |
| 4 | bias | bias | bias | bias |
| 5, 6 | bias | hour (= sample) | counter | . |
| 7, 8 | bias | . | counter | . |

Reserve, MCR and CR keep `bias` in phase 3 only because the phase-4 rule reads the bias of
every role and phase 3 does not write it for them.
-/

import Ripple.PopulationProtocol.ExactMajority.Protocol.Transition

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- `bias` is read in phase 3 (every role but Clock), phase 4 (every role) and phases 5–8 (Main). -/
def liveBias (p : ℕ) (r : Role) : Prop :=
  (p = 3 ∧ r ≠ .clock) ∨ p = 4 ∨ (5 ≤ p ∧ p ≤ 8 ∧ r = .main)

instance (p : ℕ) (r : Role) : Decidable (liveBias p r) := by
  unfold liveBias; infer_instance

/-- `hour` is read by an unbiased Main in phase 3 and, as `sample`, by a Reserve in phases 5, 6. -/
def liveHour (p : ℕ) (r : Role) (biasZero : Prop) [Decidable biasZero] : Prop :=
  (p = 3 ∧ r = .main ∧ biasZero) ∨ ((p = 5 ∨ p = 6) ∧ r = .reserve)

instance (p : ℕ) (r : Role) (z : Prop) [Decidable z] : Decidable (liveHour p r z) := by
  unfold liveHour; infer_instance

/-- `minute` is read by a Clock in phase 3. -/
def liveMinute (p : ℕ) (r : Role) : Prop := p = 3 ∧ r = .clock

instance (p : ℕ) (r : Role) : Decidable (liveMinute p r) := by
  unfold liveMinute; infer_instance

/-- `counter` is read by a Clock in the timed phases 0, 1, 5, 6, 7, 8 and in phase 3 once the
minute has reached its maximum. -/
def liveCounter (p : ℕ) (r : Role) (minuteMax : Prop) [Decidable minuteMax] : Prop :=
  r = .clock ∧ (p = 0 ∨ p = 1 ∨ (p = 3 ∧ minuteMax) ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8)

instance (p : ℕ) (r : Role) (m : Prop) [Decidable m] : Decidable (liveCounter p r m) := by
  unfold liveCounter; infer_instance

/-- Default value of a dead `hour`. -/
def hourDefault : Fin (L + 1) := ⟨0, by omega⟩

/-- Default value of a dead `minute`. -/
def minuteDefault : Fin (K * (L + 1) + 1) := ⟨0, by omega⟩

/-- Default value of a dead `counter`: the Init value `50 (L+1)`, so that a phase-3 Clock whose
minute is still below the maximum normalizes to its actual state. -/
def counterDefault : Fin (50 * (L + 1) + 1) := ⟨50 * (L + 1), by omega⟩

/-- Reset the dead fields of an agent, reading the live table at phase `p`. -/
def normalizeAtVal (p : ℕ) (a : AgentState L K) : AgentState L K :=
  { a with
    bias := if liveBias p a.role then a.bias else .zero
    hour := if liveHour p a.role (a.bias = .zero) then a.hour else hourDefault
    minute := if liveMinute p a.role then a.minute else minuteDefault
    counter := if liveCounter p a.role (a.minute.val = K * (L + 1)) then a.counter
      else counterDefault }

/-- Normal form of an agent: dead fields at its own phase reset. -/
def normalize (a : AgentState L K) : AgentState L K := normalizeAtVal a.phase.val a

/-- Normal form read at phase `j` (the phase field is kept). -/
def normalizeAt (j : Fin 11) (a : AgentState L K) : AgentState L K := normalizeAtVal j.val a

/-- The phase-3 Clock invariant at phase index `j`. -/
def GoodAtVal (j : ℕ) (a : AgentState L K) : Prop :=
  j = 3 → a.role = .clock →
    a.bias = .zero ∧ (a.minute.val < K * (L + 1) → a.counter.val = 50 * (L + 1))

/-- The reachability invariant of the count: a phase-3 Clock has zero bias and the Init counter
until its minute reaches the maximum. -/
def Good (a : AgentState L K) : Prop := GoodAtVal a.phase.val a

/-- `GoodAtVal` read at a `Fin 11` index. -/
def GoodAt (j : Fin 11) (a : AgentState L K) : Prop := GoodAtVal j.val a

/-! ### Field lemmas -/

@[simp] lemma normalizeAtVal_input (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).input = a.input := rfl
@[simp] lemma normalizeAtVal_output (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).output = a.output := rfl
@[simp] lemma normalizeAtVal_phase (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).phase = a.phase := rfl
@[simp] lemma normalizeAtVal_role (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).role = a.role := rfl
@[simp] lemma normalizeAtVal_assigned (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).assigned = a.assigned := rfl
@[simp] lemma normalizeAtVal_smallBias (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).smallBias = a.smallBias := rfl
@[simp] lemma normalizeAtVal_full (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).full = a.full := rfl
@[simp] lemma normalizeAtVal_opinions (p : ℕ) (a : AgentState L K) :
    (normalizeAtVal p a).opinions = a.opinions := rfl

@[simp] lemma normalize_input (a : AgentState L K) : (normalize a).input = a.input := rfl
@[simp] lemma normalize_output (a : AgentState L K) : (normalize a).output = a.output := rfl
@[simp] lemma normalize_phase (a : AgentState L K) : (normalize a).phase = a.phase := rfl
@[simp] lemma normalize_role (a : AgentState L K) : (normalize a).role = a.role := rfl
@[simp] lemma normalize_assigned (a : AgentState L K) :
    (normalize a).assigned = a.assigned := rfl
@[simp] lemma normalize_smallBias (a : AgentState L K) :
    (normalize a).smallBias = a.smallBias := rfl
@[simp] lemma normalize_full (a : AgentState L K) : (normalize a).full = a.full := rfl
@[simp] lemma normalize_opinions (a : AgentState L K) :
    (normalize a).opinions = a.opinions := rfl

@[simp] lemma normalizeAt_phase (j : Fin 11) (a : AgentState L K) :
    (normalizeAt j a).phase = a.phase := rfl
@[simp] lemma normalizeAt_role (j : Fin 11) (a : AgentState L K) :
    (normalizeAt j a).role = a.role := rfl

lemma normalizeAt_self (a : AgentState L K) : normalizeAt a.phase a = normalize a := rfl

lemma normalize_eq_normalizeAt (a : AgentState L K) : normalize a = normalizeAt a.phase a := rfl

/-- At phase 10 every `Θ(log n)` field is dead: two agents with the same `O(1)` fields have the
same normal form. -/
lemma normalizeAtVal_ten_eq (a a' : AgentState L K)
    (hin : a.input = a'.input) (hout : a.output = a'.output) (hph : a.phase = a'.phase)
    (hrole : a.role = a'.role) (hasg : a.assigned = a'.assigned)
    (hsb : a.smallBias = a'.smallBias) (hfull : a.full = a'.full)
    (hop : a.opinions = a'.opinions) :
    normalizeAtVal 10 a = normalizeAtVal 10 a' := by
  rcases a with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  rcases a' with ⟨i', o', ph', r', g', b', sb', h', m', f', op', c'⟩
  simp only at hin hout hph hrole hasg hsb hfull hop
  subst hin hout hph hrole hasg hsb hfull hop
  cases r <;> simp [normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter]

/-- `normalizeAtVal` is idempotent at every phase index. -/
lemma normalizeAtVal_normalizeAtVal (p : ℕ) (a : AgentState L K) :
    normalizeAtVal p (normalizeAtVal p a) = normalizeAtVal p a := by
  rcases a with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  by_cases h3 : p = 3
  · subst h3
    cases r <;> simp [normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter] <;>
      intros <;> (try split_ifs) <;> simp_all
  · cases r <;> simp [normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter, h3] <;>
      intros <;> (try split_ifs) <;> simp_all <;> omega

lemma normalize_normalize (a : AgentState L K) : normalize (normalize a) = normalize a := by
  unfold normalize
  rw [normalizeAtVal_phase]
  exact normalizeAtVal_normalizeAtVal _ _

lemma normalizeAt_normalizeAt (j : Fin 11) (a : AgentState L K) :
    normalizeAt j (normalizeAt j a) = normalizeAt j a :=
  normalizeAtVal_normalizeAtVal _ _

/-- The normal form satisfies the invariant. -/
lemma goodAtVal_normalizeAtVal (p : ℕ) (a : AgentState L K) :
    GoodAtVal p (normalizeAtVal p a) := by
  intro h3 hr
  subst h3
  rcases a with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  simp only [normalizeAtVal_role] at hr
  subst hr
  refine ⟨?_, ?_⟩
  · simp [normalizeAtVal, liveBias]
  · intro hm
    simp only [normalizeAtVal, liveMinute, and_self, if_true] at hm
    have hne : ¬ m.val = K * (L + 1) := by omega
    simp [normalizeAtVal, liveCounter, hne, counterDefault]

lemma good_normalize (a : AgentState L K) : Good (normalize a) :=
  goodAtVal_normalizeAtVal _ _

lemma goodAt_normalizeAt (j : Fin 11) (a : AgentState L K) : GoodAt j (normalizeAt j a) :=
  goodAtVal_normalizeAtVal _ _

/-- On a good agent the normal form keeps the counter of a phase-3 Clock, whatever its minute. -/
lemma normalizeAtVal_counter_of_good (p : ℕ) (a : AgentState L K) (hg : GoodAtVal p a)
    (hc : a.role = .clock) (hp : p = 3) :
    (normalizeAtVal p a).counter.val = a.counter.val := by
  subst hp
  simp only [normalizeAtVal]
  split_ifs with h
  · rfl
  · have := (hg rfl hc).2
    simp only [liveCounter, hc, true_and] at h
    have hm : a.minute.val < K * (L + 1) := by
      have := a.minute.2
      omega
    simp [counterDefault, this hm]

/-- A good agent at phase 3 with role Clock has zero bias. -/
lemma bias_eq_zero_of_good (a : AgentState L K) (hg : Good a) (hp : a.phase.val = 3)
    (hc : a.role = .clock) : a.bias = .zero :=
  (hg hp hc).1

/-- A good phase-3 Clock whose minute is below the maximum has the Init counter. -/
lemma counter_eq_of_good (a : AgentState L K) (hg : Good a) (hp : a.phase.val = 3)
    (hc : a.role = .clock) (hm : a.minute.val < K * (L + 1)) :
    a.counter.val = 50 * (L + 1) :=
  (hg hp hc).2 hm

/-- `Good` only constrains phase-3 Clocks. -/
lemma good_of_phase_ne_three (a : AgentState L K) (h : a.phase.val ≠ 3) : Good a :=
  fun h3 => absurd h3 h

lemma good_of_role_ne_clock (a : AgentState L K) (h : a.role ≠ .clock) : Good a :=
  fun _ hc => absurd hc h

/-- From `normalizeAt j a = normalizeAt j a'` to `normalize a = normalize a'`, when the agents
are at phase `j` or have reached phase 10. -/
lemma normalize_eq_of_normalizeAt_eq (j : Fin 11) (a a' : AgentState L K)
    (h : normalizeAt j a = normalizeAt j a')
    (hph : a.phase.val = j.val ∨ a.phase.val = 10) :
    normalize a = normalize a' := by
  have hphase : a.phase = a'.phase := by
    have := congrArg AgentState.phase h
    simpa using this
  rcases hph with hj | h10
  · have hj' : a.phase = j := Fin.ext hj
    rw [normalize_eq_normalizeAt, normalize_eq_normalizeAt, ← hphase, hj']
    exact h
  · have hin : a.input = a'.input := by
      have := congrArg AgentState.input h; simpa [normalizeAt] using this
    have hout : a.output = a'.output := by
      have := congrArg AgentState.output h; simpa [normalizeAt] using this
    have hrole : a.role = a'.role := by
      have := congrArg AgentState.role h; simpa [normalizeAt] using this
    have hasg : a.assigned = a'.assigned := by
      have := congrArg AgentState.assigned h; simpa [normalizeAt] using this
    have hsb : a.smallBias = a'.smallBias := by
      have := congrArg AgentState.smallBias h; simpa [normalizeAt] using this
    have hfull : a.full = a'.full := by
      have := congrArg AgentState.full h; simpa [normalizeAt] using this
    have hop : a.opinions = a'.opinions := by
      have := congrArg AgentState.opinions h; simpa [normalizeAt] using this
    unfold normalize
    rw [← hphase, h10]
    exact normalizeAtVal_ten_eq a a' hin hout hphase hrole hasg hsb hfull hop

/-- `normalize` only depends on the normal form: `normalize (normalize a) = normalize a` is
`normalize_normalize`; this is the symmetric two-agent form used by the per-phase lemmas. -/
lemma normalize_eq_iff_normalizeAt (a a' : AgentState L K) (hph : a.phase = a'.phase) :
    normalize a = normalize a' ↔ normalizeAt a.phase a = normalizeAt a.phase a' := by
  rw [normalize_eq_normalizeAt, normalize_eq_normalizeAt a', hph]

end Compact

end Ripple.PopulationProtocol.ExactMajority
