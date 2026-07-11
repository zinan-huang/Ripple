/-
Transition function δ for the Doty et al. exact majority protocol.

The full δ is dispatched by phase: agents in different phases follow different
rules, plus an epidemic phase-update rule
  u.phase, v.phase ← max(u.phase, v.phase).
This file gives the dispatch shell and one concrete sub-transition per phase,
following §3.4 of the paper.

Reference: Doty et al., §3.4 (full pseudocode of all 11 phases).
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Basic.PopulationProtocol
import Ripple.PopulationProtocol.Majority.ExactMajority.Basic.AgentState
import Mathlib.Tactic

namespace ExactMajority

variable (L K : ℕ)

/-- Phase-10 index as a `Fin 11` constant, used by Init code that error-jumps
to the slow stable backup. -/
def phase10 : Fin 11 := ⟨10, by decide⟩

@[simp] lemma phase10_val : (phase10 : Fin 11).val = 10 := rfl

/-- Canonical entry into the slow Phase-10 backup protocol.

The Doty et al. Phase-10 Init is `output ← input, active ← True`.  In this
formalization the Phase-10 `active` flag is the `full` field. -/
def enterPhase10 (a : AgentState L K) : AgentState L K :=
  let out : Output := match a.input with | .A => .A | .B => .B
  { a with phase := phase10, output := out, full := true }

@[simp] lemma enterPhase10_input (a : AgentState L K) :
    (enterPhase10 L K a).input = a.input := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_phase (a : AgentState L K) :
    (enterPhase10 L K a).phase = phase10 := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_phase_val (a : AgentState L K) :
    (enterPhase10 L K a).phase.val = 10 := by
  simp [phase10]

@[simp] lemma enterPhase10_output (a : AgentState L K) :
    (enterPhase10 L K a).output =
      match a.input with | .A => .A | .B => .B := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_role (a : AgentState L K) :
    (enterPhase10 L K a).role = a.role := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_assigned (a : AgentState L K) :
    (enterPhase10 L K a).assigned = a.assigned := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_bias (a : AgentState L K) :
    (enterPhase10 L K a).bias = a.bias := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_smallBias (a : AgentState L K) :
    (enterPhase10 L K a).smallBias = a.smallBias := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_hour (a : AgentState L K) :
    (enterPhase10 L K a).hour = a.hour := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_minute (a : AgentState L K) :
    (enterPhase10 L K a).minute = a.minute := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_full (a : AgentState L K) :
    (enterPhase10 L K a).full = true := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_opinions (a : AgentState L K) :
    (enterPhase10 L K a).opinions = a.opinions := by
  simp [enterPhase10]

@[simp] lemma enterPhase10_counter (a : AgentState L K) :
    (enterPhase10 L K a).counter = a.counter := by
  simp [enterPhase10]

/-- Helper: clamped addition of two small-bias values (Fin 7 encoding −3..+3).
Returns the bias sum clamped to [−3, +3]. -/
def addSmallBias (x y : Fin 7) : Fin 7 :=
  ⟨(max (-3 : ℤ) (min (3 : ℤ) ((x.val : ℤ) + (y.val : ℤ) - 6)) + 3).toNat, by
    have h : ∀ (a b : Fin 7),
        (max (-3 : ℤ) (min (3 : ℤ) ((a.val : ℤ) + (b.val : ℤ) - 6)) + 3).toNat < 7 := by
      decide
    exact h x y⟩

def AgentState.smallBiasInt {L K : ℕ} (a : AgentState L K) : ℤ := (a.smallBias.val : ℤ) - 3

/-- Mixed mass used before Phase 5: before Phase 3 it reads the conserved
integer `smallBias`; from Phase 3 onward it reads the dyadic `bias` field. -/
def prePhase4Mass {L K : ℕ} (a : AgentState L K) : ℚ :=
  if a.phase.val < 3 then (AgentState.smallBiasInt a : ℚ)
  else Bias.toRat a.bias

/-- Helper: advance an agent's phase by 1, if not already at the maximum (10). -/
def advancePhase (a : AgentState L K) : AgentState L K :=
  if h : a.phase.val < 10 then
    { a with phase := ⟨a.phase.val.succ, by
      have hp : a.phase.val < 11 := a.phase.2
      omega⟩ }
  else
    a

lemma advancePhase_phase_nondec (a : AgentState L K) :
    a.phase.val ≤ (advancePhase L K a).phase.val := by
  unfold advancePhase
  split
  · exact Nat.le_succ _
  · rfl

/-- Per-phase Init function: invoked when an agent's phase advances to `p`.

Runs phase-`p`-specific initialization on the agent's state. Most phases just
return the agent unchanged in this scaffold; DeepSeek fills in the meaningful
per-phase logic (e.g., Phase 1 sets `phase ← 10` if `role = MCR`; Phase 2
checks `|bias| > 1`; Phase 10 sets `output ← input, active ← True`).

Init for Phase 0 is *not* dispatched here — it's part of the initial
configuration construction (every agent starts at phase 0). The dispatcher
only invokes `phaseInit` for phases the agent newly enters via the epidemic
phase update. -/
def phaseInit (p : Fin 11) (a : AgentState L K) : AgentState L K :=
  if h1 : p.val = 1 then
    -- Paper: if role = MCR, phase ← 10 (error); if role = CR, role ← Reserve;
    -- if role = Clock, counter ← c1 ln n.
    if a.role = .mcr then enterPhase10 L K a
    else if a.role = .cr then { a with role := .reserve }
    else if a.role = .clock then { a with counter := ⟨50 * (L + 1), by omega⟩ }
    else a
  else if h2 : p.val = 2 then
    -- Paper: if |bias| > 1, phase := 10 (error); else opinions := {sign(smallBias)}.
    let biasMagGT1 : Bool := a.smallBias.val ≤ 1 || a.smallBias.val ≥ 5
    if biasMagGT1 then enterPhase10 L K a
    else
      let initOpinions : Fin 8 :=
        if a.smallBias.val < 3 then ⟨1, by decide⟩
        else if a.smallBias.val = 3 then ⟨2, by decide⟩
        else ⟨4, by decide⟩
      { a with opinions := initOpinions }
  else if h3 : p.val = 3 then
    -- Phase 3 Init: convert smallBias to dyadic bias; reset hour/minute.
    let zeroFin : Fin (L + 1) := ⟨0, by omega⟩
    let zeroFinMin : Fin (K * (L + 1) + 1) := ⟨0, by omega⟩
    let newBias : Bias L :=
      if a.smallBias.val < 3 then .dyadic .neg zeroFin
      else if a.smallBias.val > 3 then .dyadic .pos zeroFin
      else .zero
    match a.role with
    | .main => { a with bias := newBias, hour := zeroFin }
    | .clock => { a with bias := .zero, minute := zeroFinMin }
    | _ => { a with bias := .zero }
  else if h4 : p.val = 4 then
    -- Paper Phase 4 Init: a configuration that remains in this phase reports tie.
    { a with output := .T }
  else if h5 : p.val = 5 then
    if a.role = .clock then { a with counter := ⟨50 * (L + 1), by omega⟩ } else a
  else if h6 : p.val = 6 then
    if a.role = .clock then { a with counter := ⟨50 * (L + 1), by omega⟩ } else a
  else if h7 : p.val = 7 then
    if a.role = .clock then { a with counter := ⟨50 * (L + 1), by omega⟩ } else a
  else if h8 : p.val = 8 then
    { a with full := false,
             counter := if a.role = .clock then ⟨50 * (L + 1), by omega⟩ else a.counter }
  else if h9 : p.val = 9 then
    let biasMagGT1 : Bool := a.smallBias.val ≤ 1 || a.smallBias.val ≥ 5
    if biasMagGT1 then enterPhase10 L K a
    else
      let initOpinions : Fin 8 :=
        if a.smallBias.val < 3 then ⟨1, by decide⟩
        else if a.smallBias.val = 3 then ⟨2, by decide⟩
        else ⟨4, by decide⟩
      { a with opinions := initOpinions }
  else if h10 : p.val = 10 then
    enterPhase10 L K a
  else
    a

@[simp] lemma phaseInit_input_eq (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).input = a.input := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  cases role <;> fin_cases p <;> simp [phaseInit, enterPhase10] <;>
    repeat' split_ifs <;> simp [enterPhase10]

/-- Entering Phase 4 via `phaseInit` sets the output to `.T` (tie). -/
@[simp] lemma phaseInit_four_output (a : AgentState L K)
    (p : Fin 11) (hp : p.val = 4) :
    (phaseInit L K p a).output = .T := by
  have h1 : ¬ p.val = 1 := by omega
  have h2 : ¬ p.val = 2 := by omega
  have h3 : ¬ p.val = 3 := by omega
  simp [phaseInit, h1, h2, h3, hp]

/-- `advancePhase` only touches the `phase` field, so it preserves `output`. -/
@[simp] lemma advancePhase_output (a : AgentState L K) :
    (advancePhase L K a).output = a.output := by
  unfold advancePhase; split <;> rfl

lemma phaseInit_phase_nondec (p : Fin 11) (a : AgentState L K) :
    a.phase.val ≤ (phaseInit L K p a).phase.val := by
  have h_le_10 : a.phase.val ≤ 10 := by
    have := a.phase.2
    omega
  rcases p with ⟨n, hn⟩
  match n, hn with
  | 0, _ => unfold phaseInit; simp
  | 1, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 2, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 3, _ =>
    unfold phaseInit; simp
    cases a.role <;> exact le_refl _
  | 4, _ => unfold phaseInit; simp
  | 5, _ =>
    unfold phaseInit; simp
    split_ifs <;> exact le_refl _
  | 6, _ =>
    unfold phaseInit; simp
    split_ifs <;> exact le_refl _
  | 7, _ =>
    unfold phaseInit; simp
    split_ifs <;> exact le_refl _
  | 8, _ => unfold phaseInit; simp
  | 9, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 10, _ =>
    unfold phaseInit
    simp [phase10]
    exact h_le_10
  | n + 11, _ => omega

lemma phaseInit_smallBias_eq (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).smallBias = a.smallBias := by
  fin_cases p
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp [enterPhase10_smallBias]
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h, enterPhase10_smallBias]
    · simp [h]
  · unfold phaseInit; simp; split <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h, enterPhase10_smallBias]
    · simp [h]
  · unfold phaseInit; simp [enterPhase10_smallBias]

lemma phaseInit_clock_role_eq
    (p : Fin 11) (a : AgentState L K) (ha : a.role = .clock) :
    (phaseInit L K p a).role = .clock := by
  fin_cases p <;> simp [phaseInit, enterPhase10, ha] <;>
    repeat' split_ifs <;> simp [enterPhase10, ha]

/-- Advance an agent's phase by one and immediately run the destination phase
Init block.  This is the timed-counter phase advance from Doty et al. §3.4. -/
def advancePhaseWithInit (a : AgentState L K) : AgentState L K :=
  let b := advancePhase L K a
  phaseInit L K b.phase b

lemma advancePhaseWithInit_phase_nondec (a : AgentState L K) :
    a.phase.val ≤ (advancePhaseWithInit L K a).phase.val := by
  unfold advancePhaseWithInit
  exact le_trans (advancePhase_phase_nondec L K a)
    (phaseInit_phase_nondec L K (advancePhase L K a).phase (advancePhase L K a))

lemma advancePhaseWithInit_clock_role_eq
    (a : AgentState L K) (ha : a.role = .clock) :
    (advancePhaseWithInit L K a).role = .clock := by
  unfold advancePhaseWithInit
  apply phaseInit_clock_role_eq
  unfold advancePhase
  split <;> simp [ha]

/-- Standard Counter Subroutine: decrement `counter`; if it hits 0, advance
phase to the next phase and run that phase's Init block. -/
def stdCounterSubroutine (a : AgentState L K) : AgentState L K :=
  if h : a.counter.val = 0 then
    advancePhaseWithInit L K a
  else
    { a with counter := ⟨a.counter.val - 1, by omega⟩ }

lemma stdCounterSubroutine_phase_nondec (a : AgentState L K) :
    a.phase.val ≤ (stdCounterSubroutine L K a).phase.val := by
  unfold stdCounterSubroutine
  split
  · apply advancePhaseWithInit_phase_nondec
  · rfl

/-- `phaseInit` changes the phase only by raising it to the error phase 10; in
particular, if its phase argument equals the agent's own phase, then a result
that is *not* in Phase 10 leaves the phase fixed. -/
lemma phaseInit_self_phase_eq_of_not_ten (a : AgentState L K)
    (hne : (phaseInit L K a.phase a).phase.val ≠ 10) :
    (phaseInit L K a.phase a).phase.val = a.phase.val := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;>
    cases role <;>
    simp_all [phaseInit, enterPhase10, phase10] <;>
    (try split_ifs at hne ⊢) <;>
    simp_all [enterPhase10, phase10]

/-- If `advancePhaseWithInit` lands in Phase 4, the output is `.T`. -/
lemma advancePhaseWithInit_output_T_of_phase_four (a : AgentState L K)
    (hres : (advancePhaseWithInit L K a).phase.val = 4) :
    (advancePhaseWithInit L K a).output = .T := by
  unfold advancePhaseWithInit at hres ⊢
  set b := advancePhase L K a with hb
  change (phaseInit L K b.phase b).phase.val = 4 at hres
  have hne : (phaseInit L K b.phase b).phase.val ≠ 10 := by omega
  have heq := phaseInit_self_phase_eq_of_not_ten (L := L) (K := K) b hne
  have hbphase : b.phase.val = 4 := by rw [← heq]; exact hres
  change (phaseInit L K b.phase b).output = .T
  exact phaseInit_four_output (L := L) (K := K) b b.phase hbphase

/-- If `stdCounterSubroutine` lands in Phase 4 from a phase `≠ 4`, the output is
`.T`: the only phase-advancing branch fires `advancePhaseWithInit`. -/
lemma stdCounterSubroutine_output_T_of_phase_four (a : AgentState L K)
    (ha : a.phase.val ≠ 4)
    (hres : (stdCounterSubroutine L K a).phase.val = 4) :
    (stdCounterSubroutine L K a).output = .T := by
  unfold stdCounterSubroutine at hres ⊢
  split at hres
  · rw [dif_pos]
    · exact advancePhaseWithInit_output_T_of_phase_four (L := L) (K := K) a hres
    · assumption
  · exact absurd hres ha

/-- Phase 0 transition: population splitting into Main / Reserve / Clock.

Implementing all five rules from §3.4 Phase 0 pseudocode. Each rule is an
independent `if` (not `if-else`) so multiple rules can fire on the same pair.
Each `let (x, y) := if ...` from the previous version is split into separate
`let x := ...; let y := ...` so that `split_ifs` can reach the conditions. -/
def Phase0Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  -- Rule 1: two MCR → one Main (absorbs bias), one CR (bias = 0)
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
              { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias }
            else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
              { t with role := .cr, smallBias := ⟨3, by decide⟩ }
            else t
  -- Rule 2: MCR + unassigned Main → Main absorbs MCR; MCR transitions to CR with zero bias
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
            else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
              { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
            else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
              { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
            else t1
  -- Rule 3: MCR + non-Main/MCR unassigned agent → assign partner, MCR becomes Main.
  -- (Paper lines 7-9: line 8 sets the PARTNER `j.assigned ← True`; line 9 sets only
  --  `i.role ← Main` for the fresh Main, which KEEPS `assigned = False` so it can later
  --  absorb an MCR via Rule 2.  Both branches share the `j.assigned = False` guard.)
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { s2 with role := .main }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { t2 with role := .main }
            else t2
  -- Rule 3' is now folded into Rule 3 above (preserving binding names for downstream).
  let s3' := s3
  let t3' := t3
  -- Rule 4: two CR → one Clock (counter init), one Reserve
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ }
            else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
              { t3' with role := .reserve }
            else t3'
  -- Rule 5: two Clock → run Standard Counter Subroutine on both
  let s5 := if s4.role = .clock ∧ t4.role = .clock then
              stdCounterSubroutine L K s4
            else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then
              stdCounterSubroutine L K t4
            else t4
  (s5, t5)

/-- Helper: integer averaging for two `Fin 7` values encoding biased ints −3..+3.
Returns `(⌊(i+j)/2⌋, ⌈(i+j)/2⌉)` in the same encoding, where `(x.val − 3)` is the
true integer.  The Fin‑7 encoding is 0→−3, 1→−2, 2→−1, 3→0, 4→+1, 5→+2, 6→+3.
For naturals `a, b` the floor of the true average equals `(a+b)/2` and the ceil
equals `(a+b+1)/2` (both stay ≤ 6 so the result is always a valid `Fin 7`). -/
def avgFin7 (x y : Fin 7) : Fin 7 × Fin 7 :=
  (⟨(x.val + y.val) / 2, by
    have hx : x.val < 7 := x.2
    have hy : y.val < 7 := y.2
    omega⟩,
  ⟨(x.val + y.val + 1) / 2, by
    have hx : x.val < 7 := x.2
    have hy : y.val < 7 := y.2
    omega⟩)

private lemma avgFin7_preserves_sum_transition (x y : Fin 7) :
    ((avgFin7 x y).1.val : ℤ) + ((avgFin7 x y).2.val : ℤ) =
      (x.val : ℤ) + (y.val : ℤ) := by
  unfold avgFin7
  have h : (x.val + y.val) / 2 + (x.val + y.val + 1) / 2 = x.val + y.val := by
    omega
  push_cast
  omega

/-- Run the timed-phase counter on a Clock agent and leave all other roles
unchanged. -/
def clockCounterStep (a : AgentState L K) : AgentState L K :=
  if a.role = .clock then stdCounterSubroutine L K a else a

lemma clockCounterStep_phase_nondec (a : AgentState L K) :
    a.phase.val ≤ (clockCounterStep L K a).phase.val := by
  unfold clockCounterStep
  split_ifs
  · exact stdCounterSubroutine_phase_nondec L K a
  · rfl

/-- Phase 1 transition: integer averaging on small biases in {-3,...,+3} via
i, j → ⌊(i+j)/2⌋, ⌈(i+j)/2⌉, while Clock agents run the standard counter
subroutine that eventually advances the population to Phase 2. -/
def Phase1Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let (s1, t1) :=
    if s.role = .main ∧ t.role = .main then
      let (b1, b2) := avgFin7 s.smallBias t.smallBias
      ({ s with smallBias := b1 }, { t with smallBias := b2 })
    else
      (s, t)
  (clockCounterStep L K s1, clockCounterStep L K t1)

/-- Bitwise union of two `Fin 8` opinion encodings (bit pattern `b_{−1}, b_0, b_{+1}`). -/
def opinionsUnion (x y : Fin 8) : Fin 8 :=
  ⟨x.val.lor y.val, by
    have hx : x.val < 2 ^ 3 := by
      simp
    have hy : y.val < 2 ^ 3 := by
      simp
    simpa using Nat.bitwise_lt_two_pow (f := Bool.or) hx hy⟩

/-- Does the opinion set contain −1 (bit 0 set)? -/
def hasMinusOne (o : Fin 8) : Bool :=
  match o.val with
  | 1 => true
  | 3 => true
  | 5 => true
  | 7 => true
  | _ => false

/-- Does the opinion set contain +1 (bit 2 set)? -/
def hasPlusOne (o : Fin 8) : Bool :=
  match o.val with
  | 4 => true
  | 5 => true
  | 6 => true
  | 7 => true
  | _ => false

/-- Phase-2/Phase-9 sign-support invariant: a positive small-bias carries a
`+1` opinion and a negative small-bias carries a `-1` opinion. -/
def phase2SignSupport {L K : ℕ} (a : AgentState L K) : Prop :=
  (3 < a.smallBias.val → hasPlusOne a.opinions = true) ∧
    (a.smallBias.val < 3 → hasMinusOne a.opinions = true)

theorem phaseInit_two_phase2SignSupport
    (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2) :
    phase2SignSupport (phaseInit L K ⟨2, by decide⟩ a) := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases smallBias <;>
    simp [phase2SignSupport, phaseInit, enterPhase10, hasPlusOne, hasMinusOne] at hphase ⊢

/-- Phase-2 initialization filters out the out-of-range small-bias values.

If Phase-2 Init returns an agent that is still in Phase 2, then the
`biasMagGT1` error guard did not fire, hence the encoded small bias is one of
`{-1,0,+1}`, represented by `2,3,4`. -/
theorem phaseInit_two_smallBias_noerror
    (a : AgentState L K)
    (hphase : (phaseInit L K ⟨2, by decide⟩ a).phase.val = 2) :
    (phaseInit L K ⟨2, by decide⟩ a).smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases smallBias <;>
    simp [phaseInit, enterPhase10] at hphase ⊢

/-- `advancePhaseWithInit` from Phase 2 lands in Phase 3 (success) or Phase 10
(error guard), never Phase 4. -/
lemma advancePhaseWithInit_phase_ne_four_of_phase_two (a : AgentState L K)
    (ha : a.phase.val = 2) :
    (advancePhaseWithInit L K a).phase.val ≠ 4 := by
  have hphase_eq : a.phase = ⟨2, by decide⟩ := Fin.ext ha
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  simp only at hphase_eq
  subst hphase_eq
  cases role <;>
    simp [advancePhaseWithInit, advancePhase, phaseInit, enterPhase10, phase10] <;>
    (try split_ifs) <;> simp_all [enterPhase10, phase10]

/-- Phase 2 transition: opinion propagation by epidemic on the set of remaining
opinion signs.

Both agents adopt the union of their opinion sets. Based on the resulting set,
either both advance to Phase 3 (both signs still present), or converge to a
consensus output (A / B / T) and stay in Phase 2. -/
def Phase2Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let univ := opinionsUnion s.opinions t.opinions
  let s' := { s with opinions := univ }
  let t' := { t with opinions := univ }
  if hasMinusOne univ && hasPlusOne univ then
    (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
  else if hasPlusOne univ then
    ({ s' with output := .A }, { t' with output := .A })
  else if hasMinusOne univ then
    ({ s' with output := .B }, { t' with output := .B })
  else if univ.val = 2 then
    ({ s' with output := .T }, { t' with output := .T })
  else
    (s', t')

/-- `Phase2Transition` never produces a Phase-4 left output from a Phase-2 input:
the only advancing branch fires `advancePhaseWithInit`, which from Phase 2 lands
in Phase 3 (or the error Phase 10). -/
lemma Phase2Transition_left_phase_ne_four_of_phase_two (s t : AgentState L K)
    (hs : s.phase.val = 2) :
    (Phase2Transition L K s t).1.phase.val ≠ 4 := by
  unfold Phase2Transition
  dsimp only
  split_ifs <;>
    first
    | (apply advancePhaseWithInit_phase_ne_four_of_phase_two; simpa using hs)
    | simpa using (by omega : s.phase.val ≠ 4)

/-- Right-agent version of `Phase2Transition_left_phase_ne_four_of_phase_two`. -/
lemma Phase2Transition_right_phase_ne_four_of_phase_two (s t : AgentState L K)
    (ht : t.phase.val = 2) :
    (Phase2Transition L K s t).2.phase.val ≠ 4 := by
  unfold Phase2Transition
  dsimp only
  split_ifs <;>
    first
    | (apply advancePhaseWithInit_phase_ne_four_of_phase_two; simpa using ht)
    | simpa using (by omega : t.phase.val ≠ 4)

/-- Phase 3 Rules 3+4 (cancel + split) helper: applies when both agents are Main.
Returns the updated pair (s3, t3). All branches modify only `bias` and `hour`,
never `input` or `phase`. -/
def phase3CancelSplit (L K : ℕ) (s2 t2 : AgentState L K) :
    AgentState L K × AgentState L K :=
  match s2.bias, t2.bias with
  -- Rule 3: Cancel (same exponent, opposite signs → both zero)
  | .dyadic .pos i, .dyadic .neg j =>
      if _h_eq : i.val = j.val then
        ({ s2 with bias := .zero, hour := i }, { t2 with bias := .zero, hour := j })
      else (s2, t2)
  | .dyadic .neg i, .dyadic .pos j =>
      if _h_eq : i.val = j.val then
        ({ s2 with bias := .zero, hour := i }, { t2 with bias := .zero, hour := j })
      else (s2, t2)
  -- Rule 4: Split (unbiased with |hour| > |exponent| + biased)
  | .zero, .dyadic sgn i =>
      if _h_gt : s2.hour.val > i.val then
        have hi_lt_L : i.val < L := by
          have h_hour_le_L : s2.hour.val ≤ L := by
            have : s2.hour.val < L + 1 := s2.hour.2; omega
          omega
        ({ s2 with bias := .dyadic sgn ⟨i.val + 1, by omega⟩ },
         { t2 with bias := .dyadic sgn ⟨i.val + 1, by omega⟩ })
      else (s2, t2)
  | .dyadic sgn i, .zero =>
      if _h_gt : t2.hour.val > i.val then
        have hi_lt_L : i.val < L := by
          have h_hour_le_L : t2.hour.val ≤ L := by
            have : t2.hour.val < L + 1 := t2.hour.2; omega
          omega
        ({ s2 with bias := .dyadic sgn ⟨i.val + 1, by omega⟩ },
         { t2 with bias := .dyadic sgn ⟨i.val + 1, by omega⟩ })
      else (s2, t2)
  | _, _ => (s2, t2)

lemma phase3CancelSplit_input_preserved (L K : ℕ) (s2 t2 : AgentState L K) :
    (phase3CancelSplit L K s2 t2).1.input = s2.input ∧
    (phase3CancelSplit L K s2 t2).2.input = t2.input := by
  unfold phase3CancelSplit
  match s2.bias, t2.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

lemma phase3CancelSplit_output_preserved (L K : ℕ) (s2 t2 : AgentState L K) :
    (phase3CancelSplit L K s2 t2).1.output = s2.output ∧
    (phase3CancelSplit L K s2 t2).2.output = t2.output := by
  unfold phase3CancelSplit
  match s2.bias, t2.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

lemma phase3CancelSplit_phase_nondec (L K : ℕ) (s2 t2 : AgentState L K) :
    s2.phase.val ≤ (phase3CancelSplit L K s2 t2).1.phase.val ∧
    t2.phase.val ≤ (phase3CancelSplit L K s2 t2).2.phase.val := by
  unfold phase3CancelSplit
  match s2.bias, t2.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

private lemma dyadic_split_pos_inv (n : ℕ) :
    ((2 : ℚ) ^ n)⁻¹ =
      ((2 : ℚ) ^ (n + 1))⁻¹ + ((2 : ℚ) ^ (n + 1))⁻¹ := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  rw [pow_succ]
  field_simp [pow_ne_zero n htwo]
  ring

private lemma dyadic_split_neg_inv (n : ℕ) :
    -(((2 : ℚ) ^ n)⁻¹) =
      -(((2 : ℚ) ^ (n + 1))⁻¹) + -(((2 : ℚ) ^ (n + 1))⁻¹) := by
  have h := dyadic_split_pos_inv n
  linarith

private lemma dyadic_split_pos_div (n : ℕ) :
    (1 : ℚ) / (2 ^ n) =
      (1 : ℚ) / (2 ^ (n + 1)) + (1 : ℚ) / (2 ^ (n + 1)) := by
  simpa [one_div] using dyadic_split_pos_inv n

private lemma dyadic_split_neg_div (n : ℕ) :
    -(1 : ℚ) / (2 ^ n) =
      -(1 : ℚ) / (2 ^ (n + 1)) + -(1 : ℚ) / (2 ^ (n + 1)) := by
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  rw [pow_succ]
  field_simp [pow_ne_zero n htwo]
  ring

theorem phase3CancelSplit_preserves_dyadicBiasSum_pair
    (s t : AgentState L K) :
    Bias.toRat (phase3CancelSplit L K s t).1.bias +
      Bias.toRat (phase3CancelSplit L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias := by
  cases hs : s.bias with
  | zero =>
      cases ht : t.bias with
      | zero =>
          simp [phase3CancelSplit, hs, ht, Bias.toRat]
      | dyadic sgn i =>
          cases sgn
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]
            split_ifs
            · simpa [Bias.toRat] using (dyadic_split_pos_div i.val).symm
            · simpa [hs, ht, Bias.toRat]
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]
            split_ifs
            · simpa [Bias.toRat] using (dyadic_split_neg_div i.val).symm
            · simpa [hs, ht, Bias.toRat]
  | dyadic sgn i =>
      cases ht : t.bias with
      | zero =>
          cases sgn
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]
            split_ifs
            · simpa [Bias.toRat] using (dyadic_split_pos_div i.val).symm
            · simpa [hs, ht, Bias.toRat]
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]
            split_ifs
            · simpa [Bias.toRat] using (dyadic_split_neg_div i.val).symm
            · simpa [hs, ht, Bias.toRat]
      | dyadic sgn' j =>
          cases sgn <;> cases sgn'
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]
            split_ifs with h
            · have hij : (i : ℕ) = (j : ℕ) := h
              rw [hij]
              ring_nf
            · simpa [hs, ht, Bias.toRat]
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]
            split_ifs with h
            · have hij : (i : ℕ) = (j : ℕ) := h
              rw [hij]
              ring_nf
            · simpa [hs, ht, Bias.toRat]
          · simp [phase3CancelSplit, hs, ht, Bias.toRat]

/-- Phase 3 transition: cancel and split reactions gated by hour/minute clock.

Four independent rule groups (the first is Clock-Clock, the rest apply when at
least one agent is Main):
1. Both Clock → epidemic (take max minute), drip (increment same minute), or
   counter subroutine (minute at max).
2. Unbiased Main + Clock → hour drag: Main's hour ← max(own hour, ⌊minute / K⌋).
3. Both Main, opposite signs, same exponent → cancel (both → unbiased, set hour).
4. Unbiased + biased Main, |hour| > |exponent| → split (unbiased takes sign,
   both exponents decrement). -/
def Phase3Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  -- Rule 1: Both Clock
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { s with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else
      stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { t with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      t
    else
      stdCounterSubroutine L K t
  else t
  -- Rule 2: Unbiased Main + Clock → hour drag
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  -- Rules 3 + 4: both Main. Delegated to `phase3CancelSplit` helper for proof tractability.
  if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
  else (s2, t2)

theorem Phase3Transition_preserves_dyadicBiasSum_pair_of_main
    (s t : AgentState L K) (hs : s.role = .main) (ht : t.role = .main) :
    Bias.toRat (Phase3Transition L K s t).1.bias +
      Bias.toRat (Phase3Transition L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias := by
  unfold Phase3Transition
  simp [hs, ht, phase3CancelSplit_preserves_dyadicBiasSum_pair]

theorem stdCounterSubroutine_preserves_bias_of_phase_three
    (a : AgentState L K) (ha : a.phase.val = 3) :
    (stdCounterSubroutine L K a).bias = a.bias := by
  unfold stdCounterSubroutine
  split_ifs with hcounter
  · unfold advancePhaseWithInit advancePhase
    simp [ha, phaseInit]
  · simp

theorem Phase3Transition_preserves_dyadicBiasSum_pair_of_phase_three
    (s t : AgentState L K) (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3) :
    Bias.toRat (Phase3Transition L K s t).1.bias +
      Bias.toRat (Phase3Transition L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { s with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else
      stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then
      let pmax := max s.minute t.minute
      { t with minute := pmax }
    else if h_max : s.minute.val < K * (L + 1) then
      t
    else
      stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.bias = s.bias := by
    dsimp [s1]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, hs_phase]
  have ht1 : t1.bias = t.bias := by
    dsimp [t1]
    split_ifs <;> simp [stdCounterSubroutine_preserves_bias_of_phase_three, ht_phase]
  have hs2 : s2.bias = s1.bias := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2 : t2.bias = t1.bias := by
    dsimp [t2]
    split_ifs <;> simp
  have hfinal :
      Bias.toRat (Phase3Transition L K s t).1.bias +
        Bias.toRat (Phase3Transition L K s t).2.bias =
      Bias.toRat s2.bias + Bias.toRat t2.bias := by
    unfold Phase3Transition
    change Bias.toRat
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
         else (s2, t2)).1.bias +
      Bias.toRat
        (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
         else (s2, t2)).2.bias =
      Bias.toRat s2.bias + Bias.toRat t2.bias
    by_cases hmain : s2.role = .main ∧ t2.role = .main
    · simpa [hmain] using
        phase3CancelSplit_preserves_dyadicBiasSum_pair (L := L) (K := K) s2 t2
    · simp [hmain]
  calc
    Bias.toRat (Phase3Transition L K s t).1.bias +
        Bias.toRat (Phase3Transition L K s t).2.bias
        = Bias.toRat s2.bias + Bias.toRat t2.bias := hfinal
    _ = Bias.toRat s1.bias + Bias.toRat t1.bias := by simp [hs2, ht2]
    _ = Bias.toRat s.bias + Bias.toRat t.bias := by simp [hs1, ht1]

lemma phase3CancelSplit_phase_preserved (L K : ℕ) (s2 t2 : AgentState L K) :
    (phase3CancelSplit L K s2 t2).1.phase = s2.phase ∧
    (phase3CancelSplit L K s2 t2).2.phase = t2.phase := by
  unfold phase3CancelSplit
  match s2.bias, t2.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- The left `output` of `Phase3Transition` equals the `output` of the Rule-1
result `s1` (Rules 2–4 and cancel/split only touch `hour`/`bias`). -/
lemma Phase3Transition_left_output_eq_rule1 (s t : AgentState L K)
    (s1 : AgentState L K)
    (hs1 : s1 =
      (if s.role = .clock ∧ t.role = .clock then
        if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
        else if h_max : s.minute.val < K * (L + 1) then
          { s with minute := ⟨s.minute.val + 1, by omega⟩ }
        else stdCounterSubroutine L K s
      else s)) :
    (Phase3Transition L K s t).1.output = s1.output ∧
      (Phase3Transition L K s t).1.phase = s1.phase := by
  subst hs1
  unfold Phase3Transition
  dsimp only
  -- Bind the Rule-1 right result `t1` and the Rule-2 left result `s2`.
  set t1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t
    else t) with ht1def
  set s1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s
    else s) with hs1def
  set s2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
        { s1 with hour :=
            ⟨max s1.hour.val (min L (t1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
      else s1) with hs2def
  set t2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
        { t1 with hour :=
            ⟨max t1.hour.val (min L (s1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else t1) with ht2def
  have hs2_out : s2.output = s1.output := by
    rw [hs2def]; split_ifs <;> rfl
  have hs2_phase : s2.phase = s1.phase := by
    rw [hs2def]; split_ifs <;> rfl
  change
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).1.output = s1.output ∧
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).1.phase = s1.phase
  split_ifs with hmain
  · refine ⟨?_, ?_⟩
    · rw [(phase3CancelSplit_output_preserved (L := L) (K := K) s2 t2).1, hs2_out]
    · rw [(phase3CancelSplit_phase_preserved (L := L) (K := K) s2 t2).1, hs2_phase]
  · exact ⟨hs2_out, hs2_phase⟩

/-- Right-agent version of `Phase3Transition_left_output_eq_rule1`. -/
lemma Phase3Transition_right_output_eq_rule1 (s t : AgentState L K)
    (t1 : AgentState L K)
    (ht1 : t1 =
      (if s.role = .clock ∧ t.role = .clock then
        if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
        else if h_max : s.minute.val < K * (L + 1) then t
        else stdCounterSubroutine L K t
      else t)) :
    (Phase3Transition L K s t).2.output = t1.output ∧
      (Phase3Transition L K s t).2.phase = t1.phase := by
  subst ht1
  unfold Phase3Transition
  dsimp only
  set s1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s
    else s) with hs1def
  set t1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t
    else t) with ht1def
  set s2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
        { s1 with hour :=
            ⟨max s1.hour.val (min L (t1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
      else s1) with hs2def
  set t2 : AgentState L K :=
    (if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
      else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
        { t1 with hour :=
            ⟨max t1.hour.val (min L (s1.minute.val / K)), by
              exact (Nat.max_lt).mpr
                ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩⟩ }
      else t1) with ht2def
  have ht2_out : t2.output = t1.output := by
    rw [ht2def]; split_ifs <;> rfl
  have ht2_phase : t2.phase = t1.phase := by
    rw [ht2def]; split_ifs <;> rfl
  change
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).2.output = t1.output ∧
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).2.phase = t1.phase
  split_ifs with hmain
  · refine ⟨?_, ?_⟩
    · rw [(phase3CancelSplit_output_preserved (L := L) (K := K) s2 t2).2, ht2_out]
    · rw [(phase3CancelSplit_phase_preserved (L := L) (K := K) s2 t2).2, ht2_phase]
  · exact ⟨ht2_out, ht2_phase⟩

/-- Right-agent version of `Phase3Transition_left_output_T_of_phase_four`. -/
lemma Phase3Transition_right_output_T_of_phase_four
    (s t : AgentState L K) (ht_phase : t.phase.val = 3)
    (hres : (Phase3Transition L K s t).2.phase.val = 4) :
    (Phase3Transition L K s t).2.output = .T := by
  set t1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then t
      else stdCounterSubroutine L K t
    else t) with ht1def
  rcases Phase3Transition_right_output_eq_rule1 (L := L) (K := K) s t t1 ht1def with ⟨ho, hp⟩
  rw [ho]
  rw [hp] at hres
  rw [ht1def] at hres ⊢
  split_ifs at hres ⊢ with hclock hne hmax
  · exfalso; simp only [ht_phase] at hres; omega
  · exfalso; simp only [ht_phase] at hres; omega
  · exact stdCounterSubroutine_output_T_of_phase_four (L := L) (K := K) t (by omega) hres
  · exfalso; simp only [ht_phase] at hres; omega

/-- Within Phase 3 the only phase-advancing branch is the clock-counter
(`stdCounterSubroutine`) of Rule 1; Rules 2–4 and the cancel/split helper never
change the phase or the output.  Hence if the left output of `Phase3Transition`
lands in Phase 4, it was produced by `advancePhaseWithInit`, which runs
`phaseInit ⟨4⟩` and sets the output to `.T`. -/
lemma Phase3Transition_left_output_T_of_phase_four
    (s t : AgentState L K) (hs_phase : s.phase.val = 3)
    (hres : (Phase3Transition L K s t).1.phase.val = 4) :
    (Phase3Transition L K s t).1.output = .T := by
  set s1 : AgentState L K :=
    (if s.role = .clock ∧ t.role = .clock then
      if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
      else if h_max : s.minute.val < K * (L + 1) then
        { s with minute := ⟨s.minute.val + 1, by omega⟩ }
      else stdCounterSubroutine L K s
    else s) with hs1def
  rcases Phase3Transition_left_output_eq_rule1 (L := L) (K := K) s t s1 hs1def with ⟨ho, hp⟩
  rw [ho]
  rw [hp] at hres
  rw [hs1def] at hres ⊢
  split_ifs at hres ⊢ with hclock hne hmax
  · exfalso; simp only [hs_phase] at hres; omega
  · exfalso; simp only [hs_phase] at hres; omega
  · exact stdCounterSubroutine_output_T_of_phase_four (L := L) (K := K) s (by omega) hres
  · exfalso; simp only [hs_phase] at hres; omega

/-- Phase 4 transition: untimed tie detection by checking for any nonzero bias
or any exponent ≠ −L.

If either agent has a dyadic bias with magnitude strictly larger than `2^(−L)`
(i.e. bias exponent `i` satisfies `i < L`), advance both agents' phases.
Otherwise stay in Phase 4 (tie case). -/
def Phase4Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let hasBigBias (a : AgentState L K) : Bool :=
    match a.bias with
    | .zero => false
    | .dyadic _ i => if i.val < L then true else false
  if hasBigBias s || hasBigBias t then
    (advancePhase L K s, advancePhase L K t)
  else
    (s, t)

theorem Phase4Transition_preserves_dyadicBiasSum_pair
    (s t : AgentState L K) :
    Bias.toRat (Phase4Transition L K s t).1.bias +
      Bias.toRat (Phase4Transition L K s t).2.bias =
    Bias.toRat s.bias + Bias.toRat t.bias := by
  have advancePhase_bias (a : AgentState L K) :
      (advancePhase L K a).bias = a.bias := by
    unfold advancePhase
    split_ifs <;> rfl
  unfold Phase4Transition
  dsimp
  split_ifs <;> simp [advancePhase_bias]

/-- If `Phase4Transition` keeps the left agent in Phase 4, it was the identity
(the big-bias branch advances both to Phase 5), so the output is preserved. -/
lemma Phase4Transition_left_output_eq_of_phase_four
    (s t : AgentState L K) (hs_phase : s.phase.val = 4)
    (hres : (Phase4Transition L K s t).1.phase.val = 4) :
    (Phase4Transition L K s t).1.output = s.output := by
  unfold Phase4Transition at hres ⊢
  dsimp at hres ⊢
  split_ifs at hres ⊢ with hbig
  · -- big-bias branch advances to Phase 5, contradicting `hres`
    exfalso
    simp only [advancePhase, hs_phase] at hres
    norm_num at hres
  · rfl

/-- Right-agent version of `Phase4Transition_left_output_eq_of_phase_four`. -/
lemma Phase4Transition_right_output_eq_of_phase_four
    (s t : AgentState L K) (ht_phase : t.phase.val = 4)
    (hres : (Phase4Transition L K s t).2.phase.val = 4) :
    (Phase4Transition L K s t).2.output = t.output := by
  unfold Phase4Transition at hres ⊢
  dsimp at hres ⊢
  split_ifs at hres ⊢ with hbig
  · exfalso
    simp only [advancePhase, ht_phase] at hres
    norm_num at hres
  · rfl

def exponentOf (b : Bias L) : Fin (L + 1) :=
  match b with
  | .zero => sampleUnset
  | .dyadic _ i => i

/-- Phase 5 transition: Reserve agents sample the exponent of the first biased
Main agent they encounter.

Reserve + Main (biased) pair: if the Reserve has not yet sampled (`hour = L`),
it records the Main's exponent in `hour`. Clock agents run the counter
subroutine. -/
def Phase5Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  -- doSample uses `exponentOf` to flatten the inner match on `m.bias` — when
  -- `m.bias = .zero`, exponentOf returns `sampleUnset = ⟨L, _⟩`, and since the
  -- guard already forces `r.hour.val = L`, `{ r with hour := exponentOf .zero }`
  -- is equal to `r`. So no inner match is needed and downstream proofs avoid
  -- the dependent-type explosion from `Bias L`.
  let doSample (r m : AgentState L K) : AgentState L K × AgentState L K :=
    if r.hour.val = L then ({ r with hour := exponentOf L m.bias }, m)
    else (r, m)
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSample s t).1
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSample t s).2
  else s
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSample s t).2
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSample t s).1
  else t
  (if s1.role = .clock then stdCounterSubroutine L K s1 else s1,
   if t1.role = .clock then stdCounterSubroutine L K t1 else t1)

/-- Local Phase-5 clock progress: once two Phase-5 clocks with zero counters
interact, the standard counter subroutine advances both to Phase 6. -/
theorem Phase5Transition_clock_zero_advances
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 5) (ht_phase : t.phase.val = 5)
    (hs_clock : s.role = .clock) (ht_clock : t.role = .clock)
    (hs_counter : s.counter.val = 0) (ht_counter : t.counter.val = 0) :
    (Phase5Transition L K s t).1.phase.val = 6 ∧
      (Phase5Transition L K s t).2.phase.val = 6 := by
  unfold Phase5Transition stdCounterSubroutine advancePhaseWithInit advancePhase phaseInit
  simp [hs_clock, ht_clock, hs_counter, ht_counter, hs_phase, ht_phase]

/-- Phase 6 `doSplit`: Reserve splits with a biased Main (paper §7 "Phase 6
Reserve Splits", pseudocode lines 1-4).

Paper guard (line 2): `r.sample ≠ ⊥ and r.sample < m.exponent`.  In the Lean
encoding, `bias = ±2^{−j}` so the dyadic index `j = −exponent` and the Reserve's
sampled index `r.hour = −sample`; the unset sentinel `⊥` is `hour = L`.  Hence
`r.sample ≠ ⊥` ↦ `r.hour.val ≠ L` and `r.sample < m.exponent` ↦ `r.hour.val > j.val`.

Paper action (line 4): `r.exponent, m.exponent ← m.exponent − 1`.  Decrementing the
(negative) exponent by 1 means *increasing* the dyadic index by 1 (mass halves):
`j ↦ j+1` for BOTH agents.  This requires `j+1 ≤ L`, i.e. the index bound `j.val < L`
(a Main already at the minimal exponent −L cannot split further).  The Reserve `r`
becomes Main with `m.opinion` (paper line 3; `sgn` carried through).
Returns `(updatedReserve, updatedMain)`. -/
def doSplit (L K : ℕ) (r m : AgentState L K) : AgentState L K × AgentState L K :=
  match m.bias with
  | .dyadic sgn j =>
      if r.hour.val ≠ L ∧ r.hour.val > j.val then
        if h : j.val < L then
          let newExp : Fin (L + 1) := ⟨j.val + 1, by omega⟩
          ({ r with role := .main, bias := .dyadic sgn newExp },
           { m with bias := .dyadic sgn newExp })
        else (r, m)
      else (r, m)
  | .zero => (r, m)

lemma doSplit_input_preserved (L K : ℕ) (r m : AgentState L K) :
    (doSplit L K r m).1.input = r.input ∧ (doSplit L K r m).2.input = m.input := by
  unfold doSplit
  match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma doSplit_hour_fst (L K : ℕ) (r m : AgentState L K) :
    (doSplit L K r m).1.hour = r.hour := by
  unfold doSplit
  match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma doSplit_hour_snd (L K : ℕ) (r m : AgentState L K) :
    (doSplit L K r m).2.hour = m.hour := by
  unfold doSplit
  match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma doSplit_role_snd (L K : ℕ) (r m : AgentState L K) :
    (doSplit L K r m).2.role = m.role := by
  unfold doSplit
  match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

lemma doSplit_phase_nondec (L K : ℕ) (r m : AgentState L K) :
    r.phase.val ≤ (doSplit L K r m).1.phase.val ∧
    m.phase.val ≤ (doSplit L K r m).2.phase.val := by
  unfold doSplit
  match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

/-- Phase 6 transition: Reserve-fueled splits for high-bias agents.

Reserve + Main (biased) pair where the Reserve's sampled exponent is *below*
the Main's exponent (paper guard `r.sample < m.exponent`, i.e. Lean index
`r.hour > j`): the Reserve becomes Main with the same opinion, and both agents'
exponents are decremented by 1 (Lean dyadic index `j ↦ j+1`, mass halved).
Clock agents run the counter subroutine. -/
def Phase6Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let s1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSplit L K s t).1
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSplit L K t s).2
  else s
  let t1 := if s.role = .reserve ∧ t.role = .main ∧ (t.bias ≠ .zero) then
    (doSplit L K s t).2
  else if t.role = .reserve ∧ s.role = .main ∧ (s.bias ≠ .zero) then
    (doSplit L K t s).1
  else t
  (if s1.role = .clock then stdCounterSubroutine L K s1 else s1,
   if t1.role = .clock then stdCounterSubroutine L K t1 else t1)

/-- Phase 7 `cancelSplit`: Two Main agents with opposite biases. Cases depending on exponent gap:
- Same exponent → both unbiased (cancel).
- Gap-1 → less-negative agent decrements, other unbiased.
- Gap-2 → less-negative decrements, more-negative takes less-negative's opinion.
Returns `(updatedS, updatedT)`. -/
def cancelSplit (L K : ℕ) (s t : AgentState L K) : AgentState L K × AgentState L K :=
  match s.bias, t.bias with
  | .dyadic sgn_s i, .dyadic sgn_t j =>
      if sgn_s ≠ sgn_t then
        if h_eq : i.val = j.val then
          ({ s with bias := .zero }, { t with bias := .zero })
        else if h_g1 : i.val + 1 = j.val then
          have hi : i.val < L := by
            have hj : j.val < L + 1 := j.2; omega
          ({ s with bias := .dyadic sgn_s ⟨i.val + 1, by omega⟩ },
           { t with bias := .zero })
        else if h_g1' : j.val + 1 = i.val then
          have hj : j.val < L := by
            have hi : i.val < L + 1 := i.2; omega
          ({ s with bias := .zero },
           { t with bias := .dyadic sgn_t ⟨j.val + 1, by omega⟩ })
        else if h_g2 : i.val + 2 = j.val then
          have hi : i.val + 1 < L + 1 := by
            have hj : j.val < L + 1 := j.2; omega
          ({ s with bias := .dyadic sgn_s ⟨i.val + 1, hi⟩ },
           { t with bias := .dyadic sgn_s ⟨i.val + 2, by
             have hj : j.val < L + 1 := j.2; omega⟩ })
        else if h_g2' : j.val + 2 = i.val then
          have hj : j.val + 1 < L + 1 := by
            have hi : i.val < L + 1 := i.2; omega
          ({ s with bias := .dyadic sgn_t ⟨j.val + 2, by
             have hi : i.val < L + 1 := i.2; omega⟩ },
           { t with bias := .dyadic sgn_t ⟨j.val + 1, hj⟩ })
        else (s, t)
      else (s, t)
  | _, _ => (s, t)

lemma cancelSplit_input_preserved (L K : ℕ) (s t : AgentState L K) :
    (cancelSplit L K s t).1.input = s.input ∧ (cancelSplit L K s t).2.input = t.input := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic sgn_s i, .dyadic sgn_t j => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_role_fst (L K : ℕ) (s t : AgentState L K) :
    (cancelSplit L K s t).1.role = s.role := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_role_snd (L K : ℕ) (s t : AgentState L K) :
    (cancelSplit L K s t).2.role = t.role := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_hour_fst (L K : ℕ) (s t : AgentState L K) :
    (cancelSplit L K s t).1.hour = s.hour := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

@[simp] lemma cancelSplit_hour_snd (L K : ℕ) (s t : AgentState L K) :
    (cancelSplit L K s t).2.hour = t.hour := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

lemma cancelSplit_phase_nondec (L K : ℕ) (s t : AgentState L K) :
    s.phase.val ≤ (cancelSplit L K s t).1.phase.val ∧
    t.phase.val ≤ (cancelSplit L K s t).2.phase.val := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic sgn_s i, .dyadic sgn_t j => simp; split_ifs <;> simp

/-- Phase 7 transition: extended cancel/split between exponents up to two apart.

Two Main agents with opposite biases. Three cases depending on exponent gap:
- Same exponent: both become unbiased (cancel).
- Gap-1: the less-negative exponent agent decrements its exponent, the other
  becomes unbiased.
- Gap-2: the less-negative agent decrements its exponent; the more-negative
  agent takes the less-negative's opinion and keeps its original exponent.
Clock agents run the counter subroutine. -/
def Phase7Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let s1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).1 else s
  let t1 := if s.role = .main ∧ t.role = .main then (cancelSplit L K s t).2 else t
  (if s1.role = .clock then stdCounterSubroutine L K s1 else s1,
   if t1.role = .clock then stdCounterSubroutine L K t1 else t1)

/-- Phase 8 `absorbConsume`: Two Main agents with opposite biases (±1). The agent with
the higher exponent (smaller |bias|) absorbs the other, marking itself `full` and
setting the other to unbiased (`bias := 0`).
Returns `(updatedS, updatedT)`. -/
def absorbConsume (L K : ℕ) (s t : AgentState L K) : AgentState L K × AgentState L K :=
  match s.bias, t.bias with
  | .dyadic .pos i, .dyadic .neg j =>
      if i.val > j.val ∧ ¬ s.full then
        ({ s with full := true }, { t with bias := .zero })
      else if j.val > i.val ∧ ¬ t.full then
        ({ s with bias := .zero }, { t with full := true })
      else (s, t)
  | .dyadic .neg i, .dyadic .pos j =>
      if i.val > j.val ∧ ¬ s.full then
        ({ s with full := true }, { t with bias := .zero })
      else if j.val > i.val ∧ ¬ t.full then
        ({ s with bias := .zero }, { t with full := true })
      else (s, t)
  | _, _ => (s, t)

lemma absorbConsume_input_preserved (L K : ℕ) (s t : AgentState L K) :
    (absorbConsume L K s t).1.input = s.input ∧ (absorbConsume L K s t).2.input = t.input := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos i, .dyadic .neg j => simp; split_ifs <;> simp
  | .dyadic .neg i, .dyadic .pos j => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

lemma absorbConsume_phase_nondec (L K : ℕ) (s t : AgentState L K) :
    s.phase.val ≤ (absorbConsume L K s t).1.phase.val ∧
    t.phase.val ≤ (absorbConsume L K s t).2.phase.val := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos i, .dyadic .neg j => simp; split_ifs <;> simp
  | .dyadic .neg i, .dyadic .pos j => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

@[simp] lemma absorbConsume_role_fst (L K : ℕ) (s t : AgentState L K) :
    (absorbConsume L K s t).1.role = s.role := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

@[simp] lemma absorbConsume_role_snd (L K : ℕ) (s t : AgentState L K) :
    (absorbConsume L K s t).2.role = t.role := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

@[simp] lemma absorbConsume_hour_fst (L K : ℕ) (s t : AgentState L K) :
    (absorbConsume L K s t).1.hour = s.hour := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

@[simp] lemma absorbConsume_hour_snd (L K : ℕ) (s t : AgentState L K) :
    (absorbConsume L K s t).2.hour = t.hour := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- Phase 8 transition: consumption reactions with `full` flag.

Two Main agents with opposite biases (±1): the agent with the higher exponent
(smaller |bias|) absorbs the other, marking itself `full` and setting the other
to unbiased (`bias := 0`). Clock agents run the counter subroutine. -/
def Phase8Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let s1 := if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).1 else s
  let t1 := if s.role = .main ∧ t.role = .main then (absorbConsume L K s t).2 else t
  -- Clock counter subroutine runs independently
  (if s1.role = .clock then stdCounterSubroutine L K s1 else s1,
   if t1.role = .clock then stdCounterSubroutine L K t1 else t1)

/-- Phase 9 transition: identical to Phase 2, opinion-presence check. -/
def Phase9Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  Phase2Transition L K s t

/-- Phase 10 transition: slow stable backup protocol of [22]/[33,41].

Two independent rule blocks (not `else if`):
1. Both agents are active → cancel (A+B→T+T) or biased agent converts T agent.
2. One active, one passive → active converts passive.

`active` is an alias for `full` (Phase 8 and Phase 10 never coexist). -/
def Phase10Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  -- Block 1: both active. Refactored from product-let to simple-let so that
  -- `split_ifs` can drive proofs to completion.
  let s1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { s with output := .T }
      else if s.output = .T ∧ (t.output = .A ∨ t.output = .B) then
        { s with output := t.output, full := false }
      else s
    else s
  let t1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { t with output := .T }
      else if t.output = .T ∧ (s.output = .A ∨ s.output = .B) then
        { t with output := s.output, full := false }
      else t
    else t
  -- Block 2: active converts passive
  if s1.full ∧ ¬ t1.full then
    ({ s1 with output := s1.output }, { t1 with output := s1.output })
  else if ¬ s1.full ∧ t1.full then
    ({ s1 with output := t1.output }, { t1 with output := t1.output })
  else
    (s1, t1)

/-- Phase 10 preserves a unanimous output on the interacting pair. -/
theorem Phase10Transition_preserves_same_output
    (s t : AgentState L K) (o : Output)
    (hs : s.output = o) (ht : t.output = o) :
    (Phase10Transition L K s t).1.output = o ∧
      (Phase10Transition L K s t).2.output = o := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  cases o <;> simp at hs ht
  all_goals
    subst soutput
    subst toutput
    simp [Phase10Transition]

/-- Run `phaseInit` sequentially for all phases in the half-open interval
`(oldP, newP]`, leaving phases `≤ oldP` and `> newP` untouched. Used by the
phase-epidemic dispatcher when an agent jumps multiple phases. -/
def runInitsBetween (oldP newP : ℕ) (a : AgentState L K) : AgentState L K :=
  ((List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)).foldl
    (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a

theorem runInitsBetween_self_api (p : ℕ) (a : AgentState L K) :
    runInitsBetween L K p p a = a := by
  unfold runInitsBetween
  have hlist :
      (List.range 11).filter (fun k => p < k ∧ k ≤ p) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k _ hk
    simp only [decide_eq_true_eq] at hk
    exact Nat.not_lt_of_ge hk.2 hk.1
  rw [hlist]
  rfl

theorem runInitsBetween_phase2SignSupport
    (a : AgentState L K) (oldP : ℕ) (hOld : oldP ≤ 1)
    (hResult : (runInitsBetween L K oldP 2 a).phase.val = 2) :
    phase2SignSupport (runInitsBetween L K oldP 2 a) := by
  interval_cases oldP
  · unfold runInitsBetween at hResult ⊢
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
    rw [hlist] at hResult ⊢
    simpa using
      phaseInit_two_phase2SignSupport (L := L) (K := K)
        (phaseInit L K ⟨1, by decide⟩ a) hResult
  · unfold runInitsBetween at hResult ⊢
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
    rw [hlist] at hResult ⊢
    simpa using
      phaseInit_two_phase2SignSupport (L := L) (K := K) a hResult

theorem runInitsBetween_phase2_smallBias_noerror
    (a : AgentState L K) (oldP : ℕ) (hOld : oldP ≤ 1)
    (hResult : (runInitsBetween L K oldP 2 a).phase.val = 2) :
    (runInitsBetween L K oldP 2 a).smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  interval_cases oldP
  · unfold runInitsBetween at hResult ⊢
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
    rw [hlist] at hResult ⊢
    simpa using
      phaseInit_two_smallBias_noerror (L := L) (K := K)
        (phaseInit L K ⟨1, by decide⟩ a) hResult
  · unfold runInitsBetween at hResult ⊢
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
    rw [hlist] at hResult ⊢
    simpa using
      phaseInit_two_smallBias_noerror (L := L) (K := K) a hResult

set_option maxHeartbeats 1200000 in
theorem runInitsBetween_smallBias_noerror_of_crosses_phase2_to_four
    (oldP newP : ℕ) (a : AgentState L K)
    (hold : oldP < 2) (hnew_ge : 2 ≤ newP) (hnew_le : newP ≤ 4)
    (ha : a.phase.val = newP)
    (hResult_le : (runInitsBetween L K oldP newP a).phase.val ≤ 4) :
    (runInitsBetween L K oldP newP a).smallBias.val ∈
      ({2, 3, 4} : Finset ℕ) := by
  interval_cases oldP <;> interval_cases newP
  · unfold runInitsBetween at hResult_le ⊢
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by
      decide
    rw [hlist] at hResult_le ⊢
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at ha hResult_le ⊢ <;> omega
  · unfold runInitsBetween at hResult_le ⊢
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by
      decide
    rw [hlist] at hResult_le ⊢
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at ha hResult_le ⊢ <;> omega
  · unfold runInitsBetween at hResult_le ⊢
    have hlist :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by
      decide
    rw [hlist] at hResult_le ⊢
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at ha hResult_le ⊢ <;> omega
  · unfold runInitsBetween at hResult_le ⊢
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by
      decide
    rw [hlist] at hResult_le ⊢
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at ha hResult_le ⊢ <;> omega
  · unfold runInitsBetween at hResult_le ⊢
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by
      decide
    rw [hlist] at hResult_le ⊢
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at ha hResult_le ⊢ <;> omega
  · unfold runInitsBetween at hResult_le ⊢
    have hlist :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by
      decide
    rw [hlist] at hResult_le ⊢
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at ha hResult_le ⊢ <;> omega

/-- Initialize an agent exactly when it newly enters Phase 10. -/
def canonicalPhase10Entry (before after : AgentState L K) : AgentState L K :=
  if before.phase.val < 10 ∧ after.phase.val = 10 then
    enterPhase10 L K after
  else
    after

/-- Phase-epidemic entry into the slow backup protocol.

When either participant newly reaches Phase 10 during the epidemic/init stage,
both participants must be placed on the Phase-10 backup track.  Participants
that were already in Phase 10 are not reinitialized, since the backup protocol
uses passive and `T` states after entry. -/
def phase10EpidemicEntry (before after : AgentState L K) : AgentState L K :=
  if before.phase.val < 10 then
    enterPhase10 L K after
  else
    after

@[simp] lemma canonicalPhase10Entry_input
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).input = after.input := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_phase_val
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).phase.val = after.phase.val := by
  unfold canonicalPhase10Entry
  split_ifs with h <;> simp_all [phase10]

@[simp] lemma canonicalPhase10Entry_smallBias
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).smallBias = after.smallBias := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_role
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).role = after.role := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_assigned
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).assigned = after.assigned := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_bias
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).bias = after.bias := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_hour
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).hour = after.hour := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_minute
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).minute = after.minute := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_opinions
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).opinions = after.opinions := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma canonicalPhase10Entry_counter
    (before after : AgentState L K) :
    (canonicalPhase10Entry L K before after).counter = after.counter := by
  unfold canonicalPhase10Entry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_input
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).input = after.input := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_phase_val_of_before_lt_10
    (before after : AgentState L K) (hbefore : before.phase.val < 10) :
    (phase10EpidemicEntry L K before after).phase.val = 10 := by
  simp [phase10EpidemicEntry, hbefore]

@[simp] lemma phase10EpidemicEntry_phase_val_of_before_not_lt_10
    (before after : AgentState L K) (hbefore : ¬ before.phase.val < 10) :
    (phase10EpidemicEntry L K before after).phase.val = after.phase.val := by
  simp [phase10EpidemicEntry, hbefore]

@[simp] lemma phase10EpidemicEntry_smallBias
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).smallBias = after.smallBias := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_role
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).role = after.role := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_assigned
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).assigned = after.assigned := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_bias
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).bias = after.bias := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_hour
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).hour = after.hour := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_minute
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).minute = after.minute := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_opinions
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).opinions = after.opinions := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

@[simp] lemma phase10EpidemicEntry_counter
    (before after : AgentState L K) :
    (phase10EpidemicEntry L K before after).counter = after.counter := by
  unfold phase10EpidemicEntry
  split_ifs <;> simp

/-- Epidemic phase update: both agents jump to `max(s.phase, t.phase)`,
running per-phase Inits for each phase newly entered.

If a lower-phase interaction sends either agent into the Phase-10 backup track,
both agents enter the backup track in that same interaction.  Agents that were
already in Phase 10 are not reinitialized, since the backup protocol itself
uses `output = T` and passive states after its initial reactions. -/
def phaseEpidemicUpdate (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let p := max s.phase t.phase
  let s' := runInitsBetween L K s.phase.val p.val { s with phase := p }
  let t' := runInitsBetween L K t.phase.val p.val { t with phase := p }
  if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s'.phase.val = 10 ∨ t'.phase.val = 10) then
    (phase10EpidemicEntry L K s s', phase10EpidemicEntry L K t t')
  else
    (s', t')

theorem phaseEpidemicUpdate_opinions_eq_of_same_phase
    (s t : AgentState L K) (h : s.phase = t.phase) :
    (phaseEpidemicUpdate L K s t).1.opinions = s.opinions ∧
      (phaseEpidemicUpdate L K s t).2.opinions = t.opinions := by
  have hp_left : max s.phase t.phase = s.phase := by
    rw [h, max_self]
  have hp_right : max s.phase t.phase = t.phase := by
    rw [← h, max_self]
  unfold phaseEpidemicUpdate
  simp [hp_left, hp_right, runInitsBetween_self_api, h]
  by_cases h10 : t.phase.val < 10 ∧ t.phase.val = 10
  · omega
  · simp [h10]

private lemma runInitsBetween_phase_nondec_api
    (oldP newP : ℕ) (a : AgentState L K) :
    a.phase.val ≤ (runInitsBetween L K oldP newP a).phase.val := by
  unfold runInitsBetween
  let lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  have h_ind : ∀ (a' : AgentState L K), a'.phase.val ≤
      (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a').phase.val := by
    induction lst with
    | nil => exact fun a' => le_refl _
    | cons k l IH =>
      intro a'
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk]
        have h1 : a'.phase.val ≤ (phaseInit L K ⟨k, hk⟩ a').phase.val :=
          phaseInit_phase_nondec L K ⟨k, hk⟩ a'
        have h2 : (phaseInit L K ⟨k, hk⟩ a').phase.val ≤
          (l.foldl (fun (acc : AgentState L K) (k : ℕ) =>
            if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
            (phaseInit L K ⟨k, hk⟩ a')).phase.val :=
          IH (phaseInit L K ⟨k, hk⟩ a')
        exact le_trans h1 h2
      · simp [hk]
        exact IH a'
  exact h_ind a

lemma phaseEpidemicUpdate_left_phase_ge_max_api
    (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  generalize hs0 :
      runInitsBetween L K s.phase.val p.val ({ s with phase := p }) = s0
  generalize ht0 :
      runInitsBetween L K t.phase.val p.val ({ t with phase := p }) = t0
  have hs_ge : p.val ≤ s0.phase.val := by
    calc
      p.val = ({ s with phase := p } : AgentState L K).phase.val := by simp
      _ ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val :=
        runInitsBetween_phase_nondec_api L K s.phase.val p.val ({ s with phase := p })
      _ = s0.phase.val := by rw [hs0]
  have hp_eq : max s.phase.val t.phase.val = p.val := by rw [hp]; rfl
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hp_le : p.val ≤ 10 := by
      have hp_bound := p.2
      omega
    by_cases hs_lt : s.phase.val < 10
    · simpa [h10, hp_eq, hs0, ht0, hs_lt] using hp_le
    · have ht_lt : t.phase.val < 10 := by
        rcases h10.1 with hs | ht
        · exact False.elim (hs_lt hs)
        · exact ht
      simpa [h10, hp_eq, hs0, ht0, hs_lt, ht_lt] using hs_ge
  · simpa [h10, hp_eq, hs0, ht0] using hs_ge

lemma phaseEpidemicUpdate_right_phase_ge_max_api
    (s t : AgentState L K) :
    max s.phase.val t.phase.val ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase with hp
  generalize hs0 :
      runInitsBetween L K s.phase.val p.val ({ s with phase := p }) = s0
  generalize ht0 :
      runInitsBetween L K t.phase.val p.val ({ t with phase := p }) = t0
  have ht_ge : p.val ≤ t0.phase.val := by
    calc
      p.val = ({ t with phase := p } : AgentState L K).phase.val := by simp
      _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
        runInitsBetween_phase_nondec_api L K t.phase.val p.val ({ t with phase := p })
      _ = t0.phase.val := by rw [ht0]
  have hp_eq : max s.phase.val t.phase.val = p.val := by rw [hp]; rfl
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hp_le : p.val ≤ 10 := by
      have hp_bound := p.2
      omega
    by_cases ht_lt : t.phase.val < 10
    · simpa [h10, hp_eq, hs0, ht0, ht_lt] using hp_le
    · have hs_lt : s.phase.val < 10 := by
        rcases h10.1 with hs | ht
        · exact hs
        · exact False.elim (ht_lt ht)
      simpa [h10, hp_eq, hs0, ht0, hs_lt, ht_lt] using ht_ge
  · simpa [h10, hp_eq, hs0, ht0] using ht_ge

private theorem phaseEpidemicUpdate_left_opinions_of_phase2_right_le_two_api
    (s t : AgentState L K) (hs : s.phase.val = 2) (ht : t.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).1.opinions = s.opinions := by
  rcases ht_cases : t.phase with ⟨n, hn⟩
  have hnle : n ≤ 2 := by simpa [ht_cases] using ht
  have hs_phase : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  interval_cases n
  · have h02 :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h02, h22]
    split_ifs <;> simp [phase10EpidemicEntry, hs]
  · have h12 :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h12, h22]
    split_ifs <;> simp [phase10EpidemicEntry, hs]
  · have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, hs_phase, ht_cases, runInitsBetween, h22]

private theorem phaseEpidemicUpdate_right_opinions_of_phase2_left_le_two_api
    (s t : AgentState L K) (ht : t.phase.val = 2) (hs : s.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).2.opinions = t.opinions := by
  rcases hs_cases : s.phase with ⟨n, hn⟩
  have hnle : n ≤ 2 := by simpa [hs_cases] using hs
  have ht_phase : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  interval_cases n
  · have h02 :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h02, h22]
    split_ifs <;> simp [phase10EpidemicEntry, ht]
  · have h12 :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by
      decide
    have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h12, h22]
    split_ifs <;> simp [phase10EpidemicEntry, ht]
  · have h22 :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by
      decide
    simp [phaseEpidemicUpdate, ht_phase, hs_cases, runInitsBetween, h22]

theorem phaseEpidemicUpdate_left_opinions_preserved_of_phase2
    (s t : AgentState L K)
    (hs : s.phase.val = 2) :
    (phaseEpidemicUpdate L K s t).1.opinions = s.opinions ∨
      3 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
  by_cases ht : t.phase.val ≤ 2
  · exact Or.inl
      (phaseEpidemicUpdate_left_opinions_of_phase2_right_le_two_api
        (L := L) (K := K) s t hs ht)
  · have hge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    exact Or.inr (by omega)

theorem phaseEpidemicUpdate_right_opinions_preserved_of_phase2
    (s t : AgentState L K)
    (ht : t.phase.val = 2) :
    (phaseEpidemicUpdate L K s t).2.opinions = t.opinions ∨
      3 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  by_cases hs : s.phase.val ≤ 2
  · exact Or.inl
      (phaseEpidemicUpdate_right_opinions_of_phase2_left_le_two_api
        (L := L) (K := K) s t ht hs)
  · have hge := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    exact Or.inr (by omega)

private theorem phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
    (before after : AgentState L K) (hbefore : before.phase.val < 10) :
    (phase10EpidemicEntry L K before after).phase.val = 10 := by
  unfold phase10EpidemicEntry
  simp [hbefore, enterPhase10_phase_val]

private theorem runInitsBetween_phase2SignSupport_of_entered
    (oldP : ℕ) (p : Fin 11) (a : AgentState L K)
    (hold : oldP < 2) (hp : p.val ≤ 2)
    (hResult : (runInitsBetween L K oldP p.val ({ a with phase := p })).phase.val = 2) :
    phase2SignSupport (runInitsBetween L K oldP p.val ({ a with phase := p })) := by
  rcases p with ⟨pn, hp_bound⟩
  simp only at hp hResult
  interval_cases oldP <;> interval_cases pn
  · simp [runInitsBetween_self_api] at hResult
  · unfold runInitsBetween at hResult
    have h01 :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
    rw [h01] at hResult
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> simp [phaseInit, enterPhase10, phase10] at hResult
  · have hpfin : (⟨2, hp_bound⟩ : Fin 11) = ⟨2, by decide⟩ := Fin.ext rfl
    simpa [hpfin] using
      runInitsBetween_phase2SignSupport (L := L) (K := K)
        ({ a with phase := ⟨2, by decide⟩ }) 0 (by decide) hResult
  · unfold runInitsBetween at hResult
    have h11 :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 0) = [] := by decide
    rw [h11] at hResult
    simp at hResult
  · simp [runInitsBetween_self_api] at hResult
  · have hpfin : (⟨2, hp_bound⟩ : Fin 11) = ⟨2, by decide⟩ := Fin.ext rfl
    simpa [hpfin] using
      runInitsBetween_phase2SignSupport (L := L) (K := K)
        ({ a with phase := ⟨2, by decide⟩ }) 1 (by decide) hResult

private theorem runInitsBetween_phase2_smallBias_noerror_of_entered
    (oldP : ℕ) (p : Fin 11) (a : AgentState L K)
    (hold : oldP < 2) (hp : p.val ≤ 2)
    (hResult : (runInitsBetween L K oldP p.val ({ a with phase := p })).phase.val = 2) :
    (runInitsBetween L K oldP p.val ({ a with phase := p })).smallBias.val ∈
      ({2, 3, 4} : Finset ℕ) := by
  rcases p with ⟨pn, hp_bound⟩
  simp only at hp hResult
  interval_cases oldP <;> interval_cases pn
  · simp [runInitsBetween_self_api] at hResult
  · unfold runInitsBetween at hResult
    have h01 :
        (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
    rw [h01] at hResult
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> simp [phaseInit, enterPhase10, phase10] at hResult
  · have hpfin : (⟨2, hp_bound⟩ : Fin 11) = ⟨2, by decide⟩ := Fin.ext rfl
    simpa [hpfin] using
      runInitsBetween_phase2_smallBias_noerror (L := L) (K := K)
        ({ a with phase := ⟨2, by decide⟩ }) 0 (by decide) hResult
  · unfold runInitsBetween at hResult
    have h11 :
        (List.range 11).filter (fun k => 1 < k ∧ k ≤ 0) = [] := by decide
    rw [h11] at hResult
    simp at hResult
  · simp [runInitsBetween_self_api] at hResult
  · have hpfin : (⟨2, hp_bound⟩ : Fin 11) = ⟨2, by decide⟩ := Fin.ext rfl
    simpa [hpfin] using
      runInitsBetween_phase2_smallBias_noerror (L := L) (K := K)
        ({ a with phase := ⟨2, by decide⟩ }) 1 (by decide) hResult

theorem phaseEpidemicUpdate_left_phase2SignSupport_of_entered
    (s t : AgentState L K)
    (hs : s.phase.val < 2)
    (hout : (phaseEpidemicUpdate L K s t).1.phase.val = 2) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).1 := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have hs_before : s.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) s s0 hs_before
      have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have hs0_phase : s0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have hs_ge : p.val ≤ s0.phase.val := by
        calc
          p.val = ({ s with phase := p } : AgentState L K).phase.val := by simp
          _ ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val :=
            runInitsBetween_phase_nondec_api L K s.phase.val p.val ({ s with phase := p })
          _ = s0.phase.val := by rfl
      omega
  have hs0_support : phase2SignSupport s0 := by
    apply runInitsBetween_phase2SignSupport_of_entered
      (L := L) (K := K) s.phase.val p s hs hp_le
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have hs_before : s.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) s s0 hs_before
      have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · simpa [h10, s0, t0] using hout
  by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_before : s.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
      (L := L) (K := K) s s0 hs_before
    have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
      simpa [h10, s0, t0] using hout
    omega
  · simpa [h10, s0, t0] using hs0_support

theorem phaseEpidemicUpdate_right_phase2SignSupport_of_entered
    (s t : AgentState L K)
    (ht : t.phase.val < 2)
    (hout : (phaseEpidemicUpdate L K s t).2.phase.val = 2) :
    phase2SignSupport (phaseEpidemicUpdate L K s t).2 := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have ht_before : t.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) t t0 ht_before
      have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have ht0_phase : t0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have ht_ge : p.val ≤ t0.phase.val := by
        calc
          p.val = ({ t with phase := p } : AgentState L K).phase.val := by simp
          _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
            runInitsBetween_phase_nondec_api L K t.phase.val p.val ({ t with phase := p })
          _ = t0.phase.val := by rfl
      omega
  have ht0_support : phase2SignSupport t0 := by
    apply runInitsBetween_phase2SignSupport_of_entered
      (L := L) (K := K) t.phase.val p t ht hp_le
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have ht_before : t.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) t t0 ht_before
      have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · simpa [h10, s0, t0] using hout
  by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have ht_before : t.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
      (L := L) (K := K) t t0 ht_before
    have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
      simpa [h10, s0, t0] using hout
    omega
  · simpa [h10, s0, t0] using ht0_support

theorem phaseEpidemicUpdate_left_smallBias_noerror_of_entered
    (s t : AgentState L K)
    (hs : s.phase.val < 2)
    (hout : (phaseEpidemicUpdate L K s t).1.phase.val = 2) :
    (phaseEpidemicUpdate L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have hs_before : s.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) s s0 hs_before
      have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have hs0_phase : s0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have hs_ge : p.val ≤ s0.phase.val := by
        calc
          p.val = ({ s with phase := p } : AgentState L K).phase.val := by simp
          _ ≤ (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).phase.val :=
            runInitsBetween_phase_nondec_api L K s.phase.val p.val ({ s with phase := p })
          _ = s0.phase.val := by rfl
      omega
  have hs0_noerror :
      s0.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    apply runInitsBetween_phase2_smallBias_noerror_of_entered
      (L := L) (K := K) s.phase.val p s hs hp_le
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have hs_before : s.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) s s0 hs_before
      have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · simpa [h10, s0, t0] using hout
  by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_before : s.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
      (L := L) (K := K) s s0 hs_before
    have htwo : (phase10EpidemicEntry L K s s0).phase.val = 2 := by
      simpa [h10, s0, t0] using hout
    omega
  · simpa [h10, s0, t0] using hs0_noerror

theorem phaseEpidemicUpdate_right_smallBias_noerror_of_entered
    (s t : AgentState L K)
    (ht : t.phase.val < 2)
    (hout : (phaseEpidemicUpdate L K s t).2.phase.val = 2) :
    (phaseEpidemicUpdate L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  unfold phaseEpidemicUpdate at hout ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have ht_before : t.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) t t0 ht_before
      have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · have ht0_phase : t0.phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      have ht_ge : p.val ≤ t0.phase.val := by
        calc
          p.val = ({ t with phase := p } : AgentState L K).phase.val := by simp
          _ ≤ (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).phase.val :=
            runInitsBetween_phase_nondec_api L K t.phase.val p.val ({ t with phase := p })
          _ = t0.phase.val := by rfl
      omega
  have ht0_noerror :
      t0.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    apply runInitsBetween_phase2_smallBias_noerror_of_entered
      (L := L) (K := K) t.phase.val p t ht hp_le
    by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
          (s0.phase.val = 10 ∨ t0.phase.val = 10)
    · have ht_before : t.phase.val < 10 := by omega
      have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) t t0 ht_before
      have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
        simpa [h10, s0, t0] using hout
      omega
    · simpa [h10, s0, t0] using hout
  by_cases h10 :
        (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have ht_before : t.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
      (L := L) (K := K) t t0 ht_before
    have htwo : (phase10EpidemicEntry L K t t0).phase.val = 2 := by
      simpa [h10, s0, t0] using hout
    omega
  · simpa [h10, s0, t0] using ht0_noerror

set_option maxHeartbeats 800000 in
theorem runInitsBetween_phase_le_two_or_ten_of_le_two
    (oldP newP : ℕ) (a : AgentState L K)
    (hold : oldP ≤ 2) (hnew : newP ≤ 2) (ha : a.phase.val = newP) :
    (runInitsBetween L K oldP newP a).phase.val ≤ 2 ∨
      (runInitsBetween L K oldP newP a).phase.val = 10 := by
  interval_cases oldP <;> interval_cases newP
  · have hlist :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k = 0)) = [] := by decide
    simp [runInitsBetween, hlist, ha] <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 1)) = [1] := by decide
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [runInitsBetween, hlist, phaseInit, enterPhase10, phase10] at ha ⊢ <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by decide
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [runInitsBetween, hlist, phaseInit, enterPhase10, phase10] at ha ⊢ <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k = 0)) = [] := by decide
    simp [runInitsBetween, hlist, ha] <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 1)) = [] := by decide
    simp [runInitsBetween, hlist, ha] <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by decide
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [runInitsBetween, hlist, phaseInit, enterPhase10, phase10] at ha ⊢ <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k = 0)) = [] := by decide
    simp [runInitsBetween, hlist, ha] <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 1)) = [] := by decide
    simp [runInitsBetween, hlist, ha] <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by decide
    simp [runInitsBetween, hlist, ha] <;> omega

theorem phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
    (s t : AgentState L K)
    (hs : s.phase.val ≤ 2) (ht : t.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).1.phase.val ≤ 2 ∨
      (phaseEpidemicUpdate L K s t).1.phase.val = 10 := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    dsimp [p]
    exact max_le hs ht
  have hs0 :
      s0.phase.val ≤ 2 ∨ s0.phase.val = 10 := by
    dsimp [s0]
    exact runInitsBetween_phase_le_two_or_ten_of_le_two
      (L := L) (K := K) s.phase.val p.val ({ s with phase := p }) hs hp_le (by simp)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · right
    have hs_lt_ten : s.phase.val < 10 := by omega
    simpa [h10, s0, t0] using
      phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) s s0 hs_lt_ten
  · simpa [h10, s0, t0] using hs0

theorem phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
    (s t : AgentState L K)
    (hs : s.phase.val ≤ 2) (ht : t.phase.val ≤ 2) :
    (phaseEpidemicUpdate L K s t).2.phase.val ≤ 2 ∨
      (phaseEpidemicUpdate L K s t).2.phase.val = 10 := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    dsimp [p]
    exact max_le hs ht
  have ht0 :
      t0.phase.val ≤ 2 ∨ t0.phase.val = 10 := by
    dsimp [t0]
    exact runInitsBetween_phase_le_two_or_ten_of_le_two
      (L := L) (K := K) t.phase.val p.val ({ t with phase := p }) ht hp_le (by simp)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · right
    have ht_lt_ten : t.phase.val < 10 := by omega
    simpa [h10, s0, t0] using
      phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) t t0 ht_lt_ten
  · simpa [h10, s0, t0] using ht0

set_option maxHeartbeats 800000 in
theorem runInitsBetween_phase_eq_target_or_ten_of_le_two
    (oldP newP : ℕ) (a : AgentState L K)
    (hold : oldP ≤ 2) (hnew : newP ≤ 2) (ha : a.phase.val = newP) :
    (runInitsBetween L K oldP newP a).phase.val = newP ∨
      (runInitsBetween L K oldP newP a).phase.val = 10 := by
  interval_cases oldP <;> interval_cases newP
  · have hlist :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k = 0)) = [] := by decide
    simp [runInitsBetween, hlist, ha]
  · have hlist :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 1)) = [1] := by decide
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [runInitsBetween, hlist, phaseInit, enterPhase10, phase10] at ha ⊢ <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (0 < k) && decide (k ≤ 2)) = [1, 2] := by decide
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [runInitsBetween, hlist, phaseInit, enterPhase10, phase10] at ha ⊢ <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k = 0)) = [] := by decide
    simp [runInitsBetween, hlist, ha]
  · have hlist :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 1)) = [] := by decide
    simp [runInitsBetween, hlist, ha]
  · have hlist :
        (List.range 11).filter (fun k => decide (1 < k) && decide (k ≤ 2)) = [2] := by decide
    rcases a with
      ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
    cases role <;> fin_cases smallBias <;>
      simp [runInitsBetween, hlist, phaseInit, enterPhase10, phase10] at ha ⊢ <;> omega
  · have hlist :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k = 0)) = [] := by decide
    simp [runInitsBetween, hlist, ha]
  · have hlist :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 1)) = [] := by decide
    simp [runInitsBetween, hlist, ha]
  · have hlist :
        (List.range 11).filter (fun k => decide (2 < k) && decide (k ≤ 2)) = [] := by decide
    simp [runInitsBetween, hlist, ha]

theorem phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
    (s t : AgentState L K)
    (hs : s.phase.val ≤ 2) (ht : t.phase.val ≤ 2)
    (hout1 : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10)
    (hout2 : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).1.phase.val =
      (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate at hout1 hout2 ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hp_le : p.val ≤ 2 := by
    dsimp [p]
    exact max_le hs ht
  have hs0_phase :
      s0.phase.val = p.val ∨ s0.phase.val = 10 := by
    dsimp [s0]
    exact runInitsBetween_phase_eq_target_or_ten_of_le_two
      (L := L) (K := K) s.phase.val p.val ({ s with phase := p }) hs hp_le (by simp)
  have ht0_phase :
      t0.phase.val = p.val ∨ t0.phase.val = 10 := by
    dsimp [t0]
    exact runInitsBetween_phase_eq_target_or_ten_of_le_two
      (L := L) (K := K) t.phase.val p.val ({ t with phase := p }) ht hp_le (by simp)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_lt_ten : s.phase.val < 10 := by omega
    have ht_lt_ten : t.phase.val < 10 := by omega
    have hsout10 :
        (phase10EpidemicEntry L K s s0).phase.val = 10 :=
      phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) s s0 hs_lt_ten
    have htout10 :
        (phase10EpidemicEntry L K t t0).phase.val = 10 :=
      phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
        (L := L) (K := K) t t0 ht_lt_ten
    have hbad : (phase10EpidemicEntry L K s s0).phase.val ≠ 10 := by
      simpa [h10, s0, t0] using hout1
    exact False.elim (hbad hsout10)
  · have hsout : s0.phase.val = p.val := by
      rcases hs0_phase with hs_eq | hs_ten
      · exact hs_eq
      · have hbad : s0.phase.val ≠ 10 := by
          simpa [h10, s0, t0] using hout1
        exact False.elim (hbad hs_ten)
    have htout : t0.phase.val = p.val := by
      rcases ht0_phase with ht_eq | ht_ten
      · exact ht_eq
      · have hbad : t0.phase.val ≠ 10 := by
          simpa [h10, s0, t0] using hout2
        exact False.elim (hbad ht_ten)
    have heq : s0.phase.val = t0.phase.val := by
      rw [hsout, htout]
    simpa [h10, s0, t0] using heq

theorem phaseEpidemicUpdate_left_smallBias_noerror_of_entered_to_four
    (s t : AgentState L K)
    (hs : s.phase.val < 2)
    (hphase : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val)
    (hphase_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4) :
    (phaseEpidemicUpdate L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  unfold phaseEpidemicUpdate at hphase hphase_le ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_lt_ten : s.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
      (L := L) (K := K) s s0 hs_lt_ten
    have hle : (phase10EpidemicEntry L K s s0).phase.val ≤ 4 := by
      simpa [h10, s0, t0] using hphase_le
    omega
  · have hs0_ge : 2 ≤ s0.phase.val := by
      simpa [h10, s0, t0] using hphase
    have hs0_le : s0.phase.val ≤ 4 := by
      simpa [h10, s0, t0] using hphase_le
    have hp_le : p.val ≤ 4 := by
      have hnondec : p.val ≤ s0.phase.val := by
        dsimp [s0]
        simpa using
          runInitsBetween_phase_nondec_api L K s.phase.val p.val ({ s with phase := p })
      omega
    by_cases hp_ge : 2 ≤ p.val
    · have hno :=
        runInitsBetween_smallBias_noerror_of_crosses_phase2_to_four
          (L := L) (K := K) s.phase.val p.val ({ s with phase := p })
          hs hp_ge hp_le (by simp) hs0_le
      simpa [h10, s0, t0] using hno
    · have hp_le_two : p.val ≤ 2 := by omega
      have hs_le_two : s.phase.val ≤ 2 := by omega
      have hs0_phase :
          s0.phase.val = p.val ∨ s0.phase.val = 10 := by
        dsimp [s0]
        exact runInitsBetween_phase_eq_target_or_ten_of_le_two
          (L := L) (K := K) s.phase.val p.val ({ s with phase := p })
          hs_le_two hp_le_two (by simp)
      rcases hs0_phase with hs0_eq | hs0_ten
      · omega
      · exact False.elim (h10 ⟨Or.inl (by omega), Or.inl hs0_ten⟩)

/-- phaseInit(2) on bad smallBias gives phase 10. -/
theorem phaseInit_two_phase_ten_of_bad_smallBias
    (a : AgentState L K)
    (hbad : a.smallBias.val ∉ ({2, 3, 4} : Finset ℕ)) :
    (phaseInit L K ⟨2, by decide⟩ a).phase.val = 10 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hbad
  push_neg at hbad
  simp only [phaseInit, enterPhase10, phase10]
  have : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5 := by omega
  simp_all

theorem phaseEpidemicUpdate_right_smallBias_noerror_of_entered_to_four
    (s t : AgentState L K)
    (ht : t.phase.val < 2)
    (hphase : 2 ≤ (phaseEpidemicUpdate L K s t).2.phase.val)
    (hphase_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4) :
    (phaseEpidemicUpdate L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  unfold phaseEpidemicUpdate at hphase hphase_le ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have ht_lt_ten : t.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_eq_ten_of_before_lt_ten
      (L := L) (K := K) t t0 ht_lt_ten
    have hle : (phase10EpidemicEntry L K t t0).phase.val ≤ 4 := by
      simpa [h10, s0, t0] using hphase_le
    omega
  · have ht0_ge : 2 ≤ t0.phase.val := by
      simpa [h10, s0, t0] using hphase
    have ht0_le : t0.phase.val ≤ 4 := by
      simpa [h10, s0, t0] using hphase_le
    have hp_le : p.val ≤ 4 := by
      have hnondec : p.val ≤ t0.phase.val := by
        dsimp [t0]
        simpa using
          runInitsBetween_phase_nondec_api L K t.phase.val p.val ({ t with phase := p })
      omega
    by_cases hp_ge : 2 ≤ p.val
    · have hno :=
        runInitsBetween_smallBias_noerror_of_crosses_phase2_to_four
          (L := L) (K := K) t.phase.val p.val ({ t with phase := p })
          ht hp_ge hp_le (by simp) ht0_le
      simpa [h10, s0, t0] using hno
    · have hp_le_two : p.val ≤ 2 := by omega
      have ht_le_two : t.phase.val ≤ 2 := by omega
      have ht0_phase :
          t0.phase.val = p.val ∨ t0.phase.val = 10 := by
        dsimp [t0]
        exact runInitsBetween_phase_eq_target_or_ten_of_le_two
          (L := L) (K := K) t.phase.val p.val ({ t with phase := p })
          ht_le_two hp_le_two (by simp)
      rcases ht0_phase with ht0_eq | ht0_ten
      · omega
      · exact False.elim (h10 ⟨Or.inl (by omega), Or.inr ht0_ten⟩)

lemma smallBias_update_phase (a : AgentState L K) (ph : Fin 11) :
    ({ a with phase := ph }).smallBias = a.smallBias := by
  simp

lemma smallBias_update_role (a : AgentState L K) (rl : Role) :
    ({ a with role := rl }).smallBias = a.smallBias := by
  simp

@[simp] lemma advancePhase_smallBias (a : AgentState L K) :
    (advancePhase L K a).smallBias = a.smallBias := by
  unfold advancePhase
  split_ifs <;> simp

@[simp] lemma advancePhaseWithInit_smallBias (a : AgentState L K) :
    (advancePhaseWithInit L K a).smallBias = a.smallBias := by
  unfold advancePhaseWithInit
  simp [phaseInit_smallBias_eq, advancePhase_smallBias]

@[simp] lemma stdCounterSubroutine_smallBias (a : AgentState L K) :
    (stdCounterSubroutine L K a).smallBias = a.smallBias := by
  unfold stdCounterSubroutine
  split_ifs <;> simp [advancePhaseWithInit_smallBias]

@[simp] lemma clockCounterStep_smallBias (a : AgentState L K) :
    (clockCounterStep L K a).smallBias = a.smallBias := by
  unfold clockCounterStep
  split_ifs <;> simp [stdCounterSubroutine_smallBias]

lemma phaseInit_preserves_smallBias (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).smallBias = a.smallBias := by
  exact phaseInit_smallBias_eq L K p a

lemma runInitsBetween_preserves_smallBias (oldP newP : ℕ) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).smallBias = a.smallBias := by
  unfold runInitsBetween
  have h_fold : ∀ (lst : List ℕ) (a' : AgentState L K),
      (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a').smallBias = a'.smallBias := by
    intro lst
    induction lst with
    | nil => intro a'; rfl
    | cons k l IH =>
      intro a'
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk, phaseInit_preserves_smallBias, IH (phaseInit L K ⟨k, hk⟩ a')]
      · simp [hk, IH a']
  exact h_fold ((List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)) a

lemma phaseEpidemicUpdate_preserves_smallBias (s t : AgentState L K) :
    (phaseEpidemicUpdate L K s t).1.smallBias = s.smallBias ∧
    (phaseEpidemicUpdate L K s t).2.smallBias = t.smallBias := by
  unfold phaseEpidemicUpdate
  dsimp
  generalize hs0 :
    runInitsBetween L K s.phase.val (max s.phase.val t.phase.val)
      ({ s with phase := max s.phase t.phase }) = s0
  generalize ht0 :
    runInitsBetween L K t.phase.val (max s.phase.val t.phase.val)
      ({ t with phase := max s.phase t.phase }) = t0
  have hs0_small : s0.smallBias = s.smallBias := by
    calc
      s0.smallBias =
          (runInitsBetween L K s.phase.val (max s.phase.val t.phase.val)
            ({ s with phase := max s.phase t.phase })).smallBias := by rw [hs0]
      _ = ({ s with phase := max s.phase t.phase }).smallBias :=
        runInitsBetween_preserves_smallBias L K s.phase.val (max s.phase.val t.phase.val) _
      _ = s.smallBias := by simp
  have ht0_small : t0.smallBias = t.smallBias := by
    calc
      t0.smallBias =
          (runInitsBetween L K t.phase.val (max s.phase.val t.phase.val)
            ({ t with phase := max s.phase t.phase })).smallBias := by rw [ht0]
      _ = ({ t with phase := max s.phase t.phase }).smallBias :=
        runInitsBetween_preserves_smallBias L K t.phase.val (max s.phase.val t.phase.val) _
      _ = t.smallBias := by simp
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · by_cases hs_phase : s.phase.val = 10
    · by_cases ht_phase : t.phase.val = 10
      · have hnot : ¬ (s.phase.val < 10 ∨ t.phase.val < 10) := by
          intro hlt
          rcases hlt with hlt | hlt <;> omega
        exact False.elim (hnot h10.1)
      · constructor
        · by_cases ht_lt : t.phase.val < 10
          · simp [h10, hs_phase, ht_lt, hs0_small]
          · simp [h10, hs_phase, ht_lt, hs0_small]
        · by_cases ht_lt : t.phase.val < 10
          · simp [h10, hs_phase, ht_phase, ht_lt, enterPhase10_smallBias, ht0_small]
          · simp [h10, hs_phase, ht_lt, ht0_small]
    · by_cases ht_phase : t.phase.val = 10
      · constructor
        · by_cases hs_lt : s.phase.val < 10
          · simp [h10, hs_phase, ht_phase, hs_lt, enterPhase10_smallBias, hs0_small]
          · simp [h10, ht_phase, hs_lt, hs0_small]
        · by_cases hs_lt : s.phase.val < 10
          · simp [h10, ht_phase, hs_lt, ht0_small]
          · simp [h10, ht_phase, hs_lt, ht0_small]
      · constructor <;> simp [h10, hs_phase, ht_phase, enterPhase10_smallBias,
          hs0_small, ht0_small]
  · constructor <;> simp [h10, hs0_small, ht0_small]

/-- Once phase = 10, the phaseInit foldl preserves phase = 10. -/
private lemma foldl_phaseInit_phase_ten_aux
    (lst : List ℕ) (a : AgentState L K) (ha : a.phase.val = 10) :
    (lst.foldl
      (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).phase.val = 10 := by
  induction lst generalizing a with
  | nil => exact ha
  | cons k l ih =>
    simp only [List.foldl]
    by_cases hk : k < 11
    · rw [dif_pos hk]
      apply ih
      have hnd := phaseInit_phase_nondec L K ⟨k, hk⟩ a
      have h_le_10 : (phaseInit L K ⟨k, hk⟩ a).phase.val ≤ 10 := by
        have := (phaseInit L K ⟨k, hk⟩ a).phase.2; omega
      omega
    · rw [dif_neg hk]
      exact ih a ha

/-- If `2 ∈ lst` and start has bad smallBias, foldl phaseInit ends at phase 10. -/
private lemma foldl_phaseInit_phase_ten_of_two_mem_bad_aux
    (lst : List ℕ) (a : AgentState L K)
    (h2 : 2 ∈ lst) (hbad : a.smallBias.val ∉ ({2, 3, 4} : Finset ℕ)) :
    (lst.foldl
      (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).phase.val = 10 := by
  induction lst generalizing a with
  | nil => cases h2
  | cons k l ih =>
    rcases List.mem_cons.mp h2 with heq | h2_in_l
    · subst heq
      have h_lt : (2 : ℕ) < 11 := by decide
      simp only [List.foldl, dif_pos h_lt]
      exact foldl_phaseInit_phase_ten_aux L K l _
        (phaseInit_two_phase_ten_of_bad_smallBias L K a hbad)
    · simp only [List.foldl]
      by_cases hk : k < 11
      · rw [dif_pos hk]
        exact ih (phaseInit L K ⟨k, hk⟩ a) h2_in_l
          (by rw [phaseInit_smallBias_eq]; exact hbad)
      · rw [dif_neg hk]
        exact ih a h2_in_l hbad

/-- runInits crossing phase 2 from bad smallBias yields phase 10. -/
private lemma runInitsBetween_phase_ten_of_smallBias_bad_aux
    (oldP newP : ℕ) (a : AgentState L K)
    (hold : oldP < 2) (hnew : 2 ≤ newP)
    (hbad : a.smallBias.val ∉ ({2, 3, 4} : Finset ℕ)) :
    (runInitsBetween L K oldP newP a).phase.val = 10 := by
  unfold runInitsBetween
  apply foldl_phaseInit_phase_ten_of_two_mem_bad_aux L K _ a _ hbad
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨by decide, hold, hnew⟩

/-- Generalized noerror: epidemic output phase ≠ 10 suffices (not just ≤ 4).
The proof chain: epidemic preserves smallBias (preserves_smallBias), so it suffices
to show s.smallBias ∈ {2,3,4}. By contradiction, if s.smallBias is bad, runInits
crossing phase 2 yields phase 10, which contradicts hphase_ne10. -/
theorem phaseEpidemicUpdate_left_smallBias_noerror_of_entered_not_ten
    (s t : AgentState L K)
    (hs : s.phase.val < 2)
    (hphase : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val)
    (hphase_ne10 : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  rw [(phaseEpidemicUpdate_preserves_smallBias L K s t).1]
  by_contra h_s_bad
  apply hphase_ne10
  unfold phaseEpidemicUpdate at hphase ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p }) with hs0_def
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p }) with ht0_def
  have hs_lt10 : s.phase.val < 10 := by omega
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · -- h10: phase10EpidemicEntry s s0 → phase 10.
    have hgoal : (phase10EpidemicEntry L K s s0).phase.val = 10 := by
      unfold phase10EpidemicEntry
      rw [if_pos hs_lt10]
      simp [enterPhase10, phase10]
    simpa [h10, s0, t0] using hgoal
  · -- ¬h10: epidemic.1 = s0.
    have hphase' : 2 ≤ s0.phase.val := by simpa [h10, s0, t0] using hphase
    have hgoal : s0.phase.val = 10 := by
      by_cases hp_ge_2 : 2 ≤ p.val
      · have h_init_bad : ({s with phase := p} : AgentState L K).smallBias.val ∉
            ({2, 3, 4} : Finset ℕ) := by simpa using h_s_bad
        rw [hs0_def]
        exact runInitsBetween_phase_ten_of_smallBias_bad_aux L K
          s.phase.val p.val ({s with phase := p}) hs (by omega) h_init_bad
      · push_neg at hp_ge_2
        have hp_le_1 : p.val ≤ 1 := by omega
        have h_eq_or_ten := runInitsBetween_phase_eq_target_or_ten_of_le_two
          (L := L) (K := K) s.phase.val p.val ({s with phase := p})
          (by omega) (by omega) (by simp)
        rcases h_eq_or_ten with h_eq | h_ten
        · exfalso
          have hs0_le_1 : s0.phase.val ≤ 1 := by
            rw [hs0_def]
            rw [h_eq]
            omega
          omega
        · rw [hs0_def]; exact h_ten
    simpa [h10, s0, t0] using hgoal

theorem phaseEpidemicUpdate_right_smallBias_noerror_of_entered_not_ten
    (s t : AgentState L K)
    (ht : t.phase.val < 2)
    (hphase : 2 ≤ (phaseEpidemicUpdate L K s t).2.phase.val)
    (hphase_ne10 : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  rw [(phaseEpidemicUpdate_preserves_smallBias L K s t).2]
  by_contra h_t_bad
  apply hphase_ne10
  unfold phaseEpidemicUpdate at hphase ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p }) with hs0_def
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p }) with ht0_def
  have ht_lt10 : t.phase.val < 10 := by omega
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hgoal : (phase10EpidemicEntry L K t t0).phase.val = 10 := by
      unfold phase10EpidemicEntry
      rw [if_pos ht_lt10]
      simp [enterPhase10, phase10]
    simpa [h10, s0, t0] using hgoal
  · have hphase' : 2 ≤ t0.phase.val := by simpa [h10, s0, t0] using hphase
    have hgoal : t0.phase.val = 10 := by
      by_cases hp_ge_2 : 2 ≤ p.val
      · have h_init_bad : ({t with phase := p} : AgentState L K).smallBias.val ∉
            ({2, 3, 4} : Finset ℕ) := by simpa using h_t_bad
        rw [ht0_def]
        exact runInitsBetween_phase_ten_of_smallBias_bad_aux L K
          t.phase.val p.val ({t with phase := p}) ht (by omega) h_init_bad
      · push_neg at hp_ge_2
        have hp_le_1 : p.val ≤ 1 := by omega
        have h_eq_or_ten := runInitsBetween_phase_eq_target_or_ten_of_le_two
          (L := L) (K := K) t.phase.val p.val ({t with phase := p})
          (by omega) (by omega) (by simp)
        rcases h_eq_or_ten with h_eq | h_ten
        · exfalso
          have ht0_le_1 : t0.phase.val ≤ 1 := by
            rw [ht0_def]
            rw [h_eq]
            omega
          omega
        · rw [ht0_def]; exact h_ten
    simpa [h10, s0, t0] using hgoal

/-- Final Phase-10 entry guard after a phase-specific transition.

Some phase transitions advance a lower-phase agent to Phase 10 internally
(notably Phase 9's opinion check).  Such newly entering agents must run the
Phase-10 Init exactly once.  Agents that were already in Phase 10 are left
untouched, since the backup protocol uses passive and `T` states. -/
def finishPhase10Entry (before after : AgentState L K) : AgentState L K :=
  canonicalPhase10Entry L K before after

@[simp] lemma finishPhase10Entry_eq_self_of_before_not_lt_10
    (before after : AgentState L K) (hbefore : ¬ before.phase.val < 10) :
    finishPhase10Entry L K before after = after := by
  unfold finishPhase10Entry canonicalPhase10Entry
  simp [hbefore]

@[simp] lemma finishPhase10Entry_eq_self_of_after_ne_10
    (before after : AgentState L K) (hafter : after.phase.val ≠ 10) :
    finishPhase10Entry L K before after = after := by
  unfold finishPhase10Entry canonicalPhase10Entry
  simp [hafter]

@[simp] lemma finishPhase10Entry_input
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).input = after.input := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_output_of_after_ne_10
    (before after : AgentState L K) (hafter : after.phase.val ≠ 10) :
    (finishPhase10Entry L K before after).output = after.output := by
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) before after hafter]

@[simp] lemma finishPhase10Entry_phase_val
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).phase.val = after.phase.val := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_smallBias
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).smallBias = after.smallBias := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_role
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).role = after.role := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_assigned
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).assigned = after.assigned := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_bias
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).bias = after.bias := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_hour
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).hour = after.hour := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_minute
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).minute = after.minute := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_opinions
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).opinions = after.opinions := by
  simp [finishPhase10Entry]

@[simp] lemma finishPhase10Entry_counter
    (before after : AgentState L K) :
    (finishPhase10Entry L K before after).counter = after.counter := by
  simp [finishPhase10Entry]

/-- Combined transition function: first run the phase epidemic, then dispatch
to the phase-specific transition, then initialize any agent newly entering
Phase 10 during that phase-specific step. -/
def Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let (s', t') := phaseEpidemicUpdate L K s t
  let out :=
    match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')
  (finishPhase10Entry L K s' out.1, finishPhase10Entry L K t' out.2)

/-- Once both interacting agents are already in Phase 10 and report the same
output, the full transition dispatcher preserves that unanimous output. -/
theorem Transition_preserves_same_output_of_phase10
    (s t : AgentState L K) (o : Output)
    (hs_phase : s.phase.val = 10) (ht_phase : t.phase.val = 10)
    (hs_out : s.output = o) (ht_out : t.output = o) :
    (Transition L K s t).1.output = o ∧
      (Transition L K s t).2.output = o := by
  have hs_phase_eq : s.phase = phase10 := by
    apply Fin.ext
    simp [phase10, hs_phase]
  have ht_phase_eq : t.phase = phase10 := by
    apply Fin.ext
    simp [phase10, ht_phase]
  have hfilter :
      (List.range 11).filter (fun k => decide (10 < k) && decide (k ≤ 10)) = [] := by
    decide
  simpa [Transition, phaseEpidemicUpdate, runInitsBetween, hs_phase_eq,
    ht_phase_eq, phase10, hfilter] using
    Phase10Transition_preserves_same_output (L := L) (K := K)
      ({ s with phase := phase10 }) ({ t with phase := phase10 }) o
      (by simpa using hs_out) (by simpa using ht_out)

/-- The Doty et al. exact-majority population protocol, indexed by population
parameters `L = ⌈log₂ n⌉` and `K = minutes per hour`. -/
def NonuniformMajority (L K : ℕ) : Protocol (AgentState L K) where
  δ := Transition L K

/-! ### Per-phase invariant helpers

`PhaseNTransition_input_preserved` says no phase ever writes the read-only
`input` field. The proofs are uniform: unfold, split all ifs, finish by
record-update simp lemmas.

`PhaseNTransition_phase_nondec` says no phase decreases the agent's phase.
Proofs unfold and rely on `advancePhase_phase_nondec` /
`stdCounterSubroutine_phase_nondec` for the phases that advance.

These templates were discharged phase by phase after the bottleneck called out
in HANDOFF/inbox/20260428-2030.
-/

lemma advancePhase_input_eq (a : AgentState L K) : (advancePhase L K a).input = a.input := by
  unfold advancePhase; split <;> simp

lemma advancePhaseWithInit_input_eq (a : AgentState L K) :
    (advancePhaseWithInit L K a).input = a.input := by
  unfold advancePhaseWithInit
  simp [advancePhase_input_eq]

lemma stdCounterSubroutine_input_eq (a : AgentState L K) :
    (stdCounterSubroutine L K a).input = a.input := by
  unfold stdCounterSubroutine; split <;> simp [advancePhaseWithInit_input_eq]

lemma clockCounterStep_input_eq (a : AgentState L K) :
    (clockCounterStep L K a).input = a.input := by
  unfold clockCounterStep
  split_ifs <;> simp [stdCounterSubroutine_input_eq]

-- Phase 1 (template, proved)
theorem Phase1Transition_input_preserved (s t : AgentState L K) :
    (Phase1Transition L K s t).1.input = s.input ∧
    (Phase1Transition L K s t).2.input = t.input := by
  unfold Phase1Transition
  split_ifs <;> simp [clockCounterStep_input_eq]

theorem Phase1Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase1Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase1Transition L K s t).2.phase.val := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · constructor
    · simpa [Phase1Transition, hmain] using
        (clockCounterStep_phase_nondec (L := L) (K := K)
          ({ s with smallBias := (avgFin7 s.smallBias t.smallBias).1 }))
    · simpa [Phase1Transition, hmain] using
        (clockCounterStep_phase_nondec (L := L) (K := K)
          ({ t with smallBias := (avgFin7 s.smallBias t.smallBias).2 }))
  · constructor
    · simpa [Phase1Transition, hmain] using
        (clockCounterStep_phase_nondec (L := L) (K := K) s)
    · simpa [Phase1Transition, hmain] using
        (clockCounterStep_phase_nondec (L := L) (K := K) t)

-- Phase 2 (proved via simple-let pattern)
theorem Phase2Transition_input_preserved (s t : AgentState L K) :
    (Phase2Transition L K s t).1.input = s.input ∧
    (Phase2Transition L K s t).2.input = t.input := by
  unfold Phase2Transition
  dsimp
  split
  · simp [advancePhaseWithInit_input_eq]
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩

theorem Phase2Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase2Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase2Transition L K s t).2.phase.val := by
  unfold Phase2Transition
  dsimp
  split
  · constructor
    · simpa using
        advancePhaseWithInit_phase_nondec (L := L) (K := K)
          ({ s with opinions := opinionsUnion s.opinions t.opinions })
    · simpa using
        advancePhaseWithInit_phase_nondec (L := L) (K := K)
          ({ t with opinions := opinionsUnion s.opinions t.opinions })
  · split
    · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · split
      · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · split
        · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
        · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem Phase2Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase2Transition L K s t).1.smallBias = s.smallBias ∧
    (Phase2Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase2Transition
  dsimp
  split_ifs <;> simp [advancePhaseWithInit_smallBias]

-- Phase 0, 3, 5-8, 10: per-phase helper lemmas blocked by product-`let` in transition defs.
theorem Phase0Transition_input_preserved (s t : AgentState L K) :
    (Phase0Transition L K s t).1.input = s.input ∧
    (Phase0Transition L K s t).2.input = t.input := by
  -- Replicate the 5-rule let cascade from Phase0Transition's body. Since each rule
  -- only writes role / smallBias / assigned / counter / hour / phase, never input,
  -- each step preserves .input. The final pair (s5, t5) is `Phase0Transition L K s t`
  -- by defeq, so the goal closes by chaining the per-step .input equalities.
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have hs1 : s1.input = s.input := by dsimp [s1]; split_ifs <;> rfl
  have ht1 : t1.input = t.input := by dsimp [t1]; split_ifs <;> rfl
  have hs2 : s2.input = s1.input := by dsimp [s2]; split_ifs <;> rfl
  have ht2 : t2.input = t1.input := by dsimp [t2]; split_ifs <;> rfl
  have hs3 : s3.input = s2.input := by dsimp [s3]; split_ifs <;> rfl
  have ht3 : t3.input = t2.input := by dsimp [t3]; split_ifs <;> rfl
  have hs3' : s3'.input = s3.input := by dsimp [s3']
  have ht3' : t3'.input = t3.input := by dsimp [t3']
  have hs4 : s4.input = s3'.input := by dsimp [s4]; split_ifs <;> rfl
  have ht4 : t4.input = t3'.input := by dsimp [t4]; split_ifs <;> rfl
  have hs5 : s5.input = s4.input := by
    dsimp [s5]; split_ifs <;> [exact stdCounterSubroutine_input_eq L K s4; rfl]
  have ht5 : t5.input = t4.input := by
    dsimp [t5]; split_ifs <;> [exact stdCounterSubroutine_input_eq L K t4; rfl]
  refine ⟨?_, ?_⟩
  · change s5.input = s.input
    rw [hs5, hs4, hs3', hs3, hs2, hs1]
  · change t5.input = t.input
    rw [ht5, ht4, ht3', ht3, ht2, ht1]

theorem Phase0Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase0Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase0Transition L K s t).2.phase.val := by
  -- Same per-let cascade. None of the 5 rules modifies `phase`; only `stdCounterSubroutine`
  -- can change it (via `advancePhase`), and that only non-decreases.
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have hs1 : s.phase.val = s1.phase.val := by dsimp [s1]; split_ifs <;> rfl
  have ht1 : t.phase.val = t1.phase.val := by dsimp [t1]; split_ifs <;> rfl
  have hs2 : s1.phase.val = s2.phase.val := by dsimp [s2]; split_ifs <;> rfl
  have ht2 : t1.phase.val = t2.phase.val := by dsimp [t2]; split_ifs <;> rfl
  have hs3 : s2.phase.val = s3.phase.val := by dsimp [s3]; split_ifs <;> rfl
  have ht3 : t2.phase.val = t3.phase.val := by dsimp [t3]; split_ifs <;> rfl
  have hs3' : s3.phase.val = s3'.phase.val := by dsimp [s3']
  have ht3' : t3.phase.val = t3'.phase.val := by dsimp [t3']
  have hs4 : s3'.phase.val = s4.phase.val := by dsimp [s4]; split_ifs <;> rfl
  have ht4 : t3'.phase.val = t4.phase.val := by dsimp [t4]; split_ifs <;> rfl
  have hs5 : s4.phase.val ≤ s5.phase.val := by
    dsimp [s5]; split_ifs <;> [exact stdCounterSubroutine_phase_nondec L K s4; exact le_refl _]
  have ht5 : t4.phase.val ≤ t5.phase.val := by
    dsimp [t5]; split_ifs <;> [exact stdCounterSubroutine_phase_nondec L K t4; exact le_refl _]
  refine ⟨?_, ?_⟩
  · change s.phase.val ≤ s5.phase.val
    calc s.phase.val
        = s1.phase.val := hs1
      _ = s2.phase.val := hs2
      _ = s3.phase.val := hs3
      _ = s3'.phase.val := hs3'
      _ = s4.phase.val := hs4
      _ ≤ s5.phase.val := hs5
  · change t.phase.val ≤ t5.phase.val
    calc t.phase.val
        = t1.phase.val := ht1
      _ = t2.phase.val := ht2
      _ = t3.phase.val := ht3
      _ = t3'.phase.val := ht3'
      _ = t4.phase.val := ht4
      _ ≤ t5.phase.val := ht5

theorem Phase3Transition_input_preserved (s t : AgentState L K) :
    (Phase3Transition L K s t).1.input = s.input ∧
    (Phase3Transition L K s t).2.input = t.input := by
  -- Inline cascade for Rule 1 (Clock-Clock) and Rule 2 (hour drag) lets, then
  -- delegate Rules 3+4 to phase3CancelSplit_input_preserved.
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.input = s.input := by
    dsimp [s1]; split_ifs <;>
      first | rfl | exact stdCounterSubroutine_input_eq L K s
  have ht1 : t1.input = t.input := by
    dsimp [t1]; split_ifs <;>
      first | rfl | exact stdCounterSubroutine_input_eq L K t
  have hs2 : s2.input = s1.input := by dsimp [s2]; split_ifs <;> rfl
  have ht2 : t2.input = t1.input := by dsimp [t2]; split_ifs <;> rfl
  rcases phase3CancelSplit_input_preserved L K s2 t2 with ⟨h_cs_s, h_cs_t⟩
  refine ⟨?_, ?_⟩
  · change (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).1.input = s.input
    split_ifs
    · rw [h_cs_s, hs2, hs1]
    · change s2.input = s.input; rw [hs2, hs1]
  · change (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).2.input = t.input
    split_ifs
    · rw [h_cs_t, ht2, ht1]
    · change t2.input = t.input; rw [ht2, ht1]

theorem Phase3Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase3Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase3Transition L K s t).2.phase.val := by
  -- Same cascade as input_preserved, but conclusion is `≤`. Rule 1's stdCounterSubroutine
  -- branch uses stdCounterSubroutine_phase_nondec; everything else is equality.
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s.phase.val ≤ s1.phase.val := by
    dsimp [s1]; split_ifs <;>
      first | exact le_refl _ | exact stdCounterSubroutine_phase_nondec L K s
  have ht1 : t.phase.val ≤ t1.phase.val := by
    dsimp [t1]; split_ifs <;>
      first | exact le_refl _ | exact stdCounterSubroutine_phase_nondec L K t
  have hs2 : s1.phase.val = s2.phase.val := by dsimp [s2]; split_ifs <;> rfl
  have ht2 : t1.phase.val = t2.phase.val := by dsimp [t2]; split_ifs <;> rfl
  rcases phase3CancelSplit_phase_nondec L K s2 t2 with ⟨h_cs_s, h_cs_t⟩
  refine ⟨?_, ?_⟩
  · change s.phase.val ≤ (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).1.phase.val
    split_ifs
    · calc s.phase.val ≤ s1.phase.val := hs1
        _ = s2.phase.val := hs2
        _ ≤ (phase3CancelSplit L K s2 t2).1.phase.val := h_cs_s
    · change s.phase.val ≤ s2.phase.val
      calc s.phase.val ≤ s1.phase.val := hs1
        _ = s2.phase.val := hs2
  · change t.phase.val ≤ (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).2.phase.val
    split_ifs
    · calc t.phase.val ≤ t1.phase.val := ht1
        _ = t2.phase.val := ht2
        _ ≤ (phase3CancelSplit L K s2 t2).2.phase.val := h_cs_t
    · change t.phase.val ≤ t2.phase.val
      calc t.phase.val ≤ t1.phase.val := ht1
        _ = t2.phase.val := ht2

theorem Phase4Transition_input_preserved (s t : AgentState L K) :
    (Phase4Transition L K s t).1.input = s.input ∧
    (Phase4Transition L K s t).2.input = t.input := by
  unfold Phase4Transition; dsimp
  split_ifs <;>
    first
      | exact ⟨advancePhase_input_eq L K s, advancePhase_input_eq L K t⟩
      | exact ⟨rfl, rfl⟩

theorem Phase4Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase4Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase4Transition L K s t).2.phase.val := by
  unfold Phase4Transition; dsimp; split_ifs <;>
    first
      | exact ⟨advancePhase_phase_nondec L K s, advancePhase_phase_nondec L K t⟩
      | exact ⟨le_refl _, le_refl _⟩

theorem Phase4Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase4Transition L K s t).1.smallBias = s.smallBias ∧
    (Phase4Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase4Transition; dsimp
  constructor
  · split_ifs <;> simp [advancePhase_smallBias]
  · split_ifs <;> simp [advancePhase_smallBias]

theorem Phase5Transition_input_preserved (s t : AgentState L K) :
    (Phase5Transition L K s t).1.input = s.input ∧
    (Phase5Transition L K s t).2.input = t.input := by
  unfold Phase5Transition
  refine ⟨?_, ?_⟩ <;> repeat' split_ifs <;> simp_all [stdCounterSubroutine_input_eq]

theorem Phase5Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase5Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase5Transition L K s t).2.phase.val := by
  unfold Phase5Transition
  refine ⟨?_, ?_⟩ <;> repeat' split_ifs <;>
    first
      | exact stdCounterSubroutine_phase_nondec L K _
      | exact le_refl _
      | simp_all

theorem Phase6Transition_input_preserved (s t : AgentState L K) :
    (Phase6Transition L K s t).1.input = s.input ∧
    (Phase6Transition L K s t).2.input = t.input := by
  unfold Phase6Transition; dsimp
  rcases doSplit_input_preserved L K s t with ⟨h_s, h_t⟩
  rcases doSplit_input_preserved L K t s with ⟨h_ts, h_tt⟩
  split_ifs <;> simp [h_s, h_t, h_ts, h_tt, stdCounterSubroutine_input_eq]

theorem Phase6Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase6Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase6Transition L K s t).2.phase.val := by
  unfold Phase6Transition; dsimp
  rcases doSplit_phase_nondec L K s t with ⟨h_s, h_t⟩
  rcases doSplit_phase_nondec L K t s with ⟨h_ts, h_tt⟩
  refine ⟨?_, ?_⟩ <;>
    (split_ifs <;>
      first
        | exact le_trans (by assumption) (stdCounterSubroutine_phase_nondec _ _ _)
        | exact stdCounterSubroutine_phase_nondec _ _ _
        | assumption
        | exact le_refl _)

theorem Phase7Transition_input_preserved (s t : AgentState L K) :
    (Phase7Transition L K s t).1.input = s.input ∧
    (Phase7Transition L K s t).2.input = t.input := by
  unfold Phase7Transition; dsimp
  rcases cancelSplit_input_preserved L K s t with ⟨h_s, h_t⟩
  split_ifs <;> simp [h_s, h_t, stdCounterSubroutine_input_eq]

theorem Phase7Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase7Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase7Transition L K s t).2.phase.val := by
  unfold Phase7Transition; dsimp
  rcases cancelSplit_phase_nondec L K s t with ⟨h_s, h_t⟩
  refine ⟨?_, ?_⟩ <;>
    (split_ifs <;>
      first
        | exact le_trans (by assumption) (stdCounterSubroutine_phase_nondec _ _ _)
        | exact stdCounterSubroutine_phase_nondec _ _ _
        | assumption
        | exact le_refl _)

theorem Phase8Transition_input_preserved (s t : AgentState L K) :
    (Phase8Transition L K s t).1.input = s.input ∧
    (Phase8Transition L K s t).2.input = t.input := by
  unfold Phase8Transition; dsimp
  rcases absorbConsume_input_preserved L K s t with ⟨h_s, h_t⟩
  split_ifs <;> simp [h_s, h_t, stdCounterSubroutine_input_eq]

theorem Phase8Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase8Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase8Transition L K s t).2.phase.val := by
  unfold Phase8Transition; dsimp
  rcases absorbConsume_phase_nondec L K s t with ⟨h_s, h_t⟩
  refine ⟨?_, ?_⟩ <;>
    (split_ifs <;>
      first
        | exact le_trans (by assumption) (stdCounterSubroutine_phase_nondec _ _ _)
        | exact stdCounterSubroutine_phase_nondec _ _ _
        | assumption
        | exact le_refl _)

theorem Phase9Transition_input_preserved (s t : AgentState L K) :
    (Phase9Transition L K s t).1.input = s.input ∧
    (Phase9Transition L K s t).2.input = t.input := by
  unfold Phase9Transition; apply Phase2Transition_input_preserved

theorem Phase9Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase9Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase9Transition L K s t).2.phase.val := by
  unfold Phase9Transition; apply Phase2Transition_phase_nondec

theorem Phase9Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase9Transition L K s t).1.smallBias = s.smallBias ∧
    (Phase9Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase9Transition; apply Phase2Transition_preserves_smallBias

theorem Phase10Transition_input_preserved (s t : AgentState L K) :
    (Phase10Transition L K s t).1.input = s.input ∧
    (Phase10Transition L K s t).2.input = t.input := by
  unfold Phase10Transition
  dsimp only
  refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all

theorem Phase10Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase10Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase10Transition L K s t).2.phase.val := by
  unfold Phase10Transition
  dsimp only
  refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all

theorem Phase10Transition_phase_eq (s t : AgentState L K) :
    (Phase10Transition L K s t).1.phase = s.phase ∧
    (Phase10Transition L K s t).2.phase = t.phase := by
  unfold Phase10Transition
  dsimp only
  refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all

theorem Phase10Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase10Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase10Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase10Transition
  dsimp only
  refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all

private lemma phase3CancelSplit_preserves_smallBias (s t : AgentState L K) :
    (phase3CancelSplit L K s t).1.smallBias = s.smallBias ∧
      (phase3CancelSplit L K s t).2.smallBias = t.smallBias := by
  unfold phase3CancelSplit
  match s.bias, t.bias with
  | .zero, .zero => simp
  | .zero, .dyadic _ _ => simp; split_ifs <;> simp
  | .dyadic _ _, .zero => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .neg _ => simp

theorem Phase3Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase3Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase3Transition L K s t).2.smallBias = t.smallBias := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.smallBias = s.smallBias := by
    dsimp [s1]
    split_ifs <;> simp [stdCounterSubroutine_smallBias]
  have ht1 : t1.smallBias = t.smallBias := by
    dsimp [t1]
    split_ifs <;> simp [stdCounterSubroutine_smallBias]
  have hs2 : s2.smallBias = s1.smallBias := by
    dsimp [s2]
    split_ifs <;> simp
  have ht2 : t2.smallBias = t1.smallBias := by
    dsimp [t2]
    split_ifs <;> simp
  rcases phase3CancelSplit_preserves_smallBias (L := L) (K := K) s2 t2 with
    ⟨hcs_s, hcs_t⟩
  unfold Phase3Transition
  change
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).1.smallBias = s.smallBias ∧
    (if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
      else (s2, t2)).2.smallBias = t.smallBias
  by_cases hmain : s2.role = .main ∧ t2.role = .main
  · simp [hmain, hcs_s, hcs_t, hs2, ht2, hs1, ht1]
  · simp [hmain, hs2, ht2, hs1, ht1]

private lemma doSplit_preserves_smallBias (r m : AgentState L K) :
    (doSplit L K r m).1.smallBias = r.smallBias ∧
      (doSplit L K r m).2.smallBias = m.smallBias := by
  unfold doSplit
  match m.bias with
  | .zero => simp
  | .dyadic _ _ => simp; split_ifs <;> simp

private lemma cancelSplit_preserves_smallBias (s t : AgentState L K) :
    (cancelSplit L K s t).1.smallBias = s.smallBias ∧
      (cancelSplit L K s t).2.smallBias = t.smallBias := by
  unfold cancelSplit
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic _ _, .zero => simp
  | .dyadic _ _, .dyadic _ _ => simp; split_ifs <;> simp

private lemma absorbConsume_preserves_smallBias (s t : AgentState L K) :
    (absorbConsume L K s t).1.smallBias = s.smallBias ∧
      (absorbConsume L K s t).2.smallBias = t.smallBias := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos _, .dyadic .neg _ => simp; split_ifs <;> simp
  | .dyadic .neg _, .dyadic .pos _ => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

theorem Phase5Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase5Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase5Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase5Transition
  dsimp only
  constructor <;> split_ifs <;> simp [stdCounterSubroutine_smallBias]

theorem Phase6Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase6Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase6Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase6Transition
  dsimp only
  constructor <;> split_ifs <;>
    simp [stdCounterSubroutine_smallBias, doSplit_preserves_smallBias]

theorem Phase7Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase7Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase7Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase7Transition
  dsimp only
  constructor <;> split_ifs <;>
    simp [stdCounterSubroutine_smallBias, cancelSplit_preserves_smallBias]

theorem Phase8Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase8Transition L K s t).1.smallBias = s.smallBias ∧
      (Phase8Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase8Transition
  dsimp only
  constructor <;> split_ifs <;>
    simp [stdCounterSubroutine_smallBias, absorbConsume_preserves_smallBias]

private lemma prePhase4Mass_phaseInit_three_of_wf
    (a : AgentState L K)
    (hphase : a.phase.val = 3)
    (hmcr : a.role ≠ .mcr)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hsmall : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4) :
    prePhase4Mass (phaseInit L K ⟨3, by decide⟩ a) =
      (AgentState.smallBiasInt a : ℚ) := by
  rcases hsmall with h2 | h34
  · cases hrole : a.role <;>
      simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
        hphase, hrole, h2] at hmcr hcarrier ⊢
  · rcases h34 with h3 | h4
    · cases hrole : a.role <;>
        simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
          hphase, hrole, h3] at hmcr hcarrier ⊢
    · cases hrole : a.role <;>
        simp [prePhase4Mass, phaseInit, AgentState.smallBiasInt, Bias.toRat,
          hphase, hrole, h4] at hmcr hcarrier ⊢

set_option maxHeartbeats 4000000 in
private lemma runInitsBetween_update_phase_preserves_prePhase4Mass_to_four
    (a : AgentState L K) (p : Fin 11)
    (hle : a.phase.val ≤ p.val)
    (hp : p.val ≤ 4)
    (hres_le :
      (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val ≤ 4)
    (hmcr : a.role ≠ .mcr)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hnoerr : 2 ≤ a.phase.val →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    prePhase4Mass
        (runInitsBetween L K a.phase.val p.val ({ a with phase := p })) =
      prePhase4Mass a := by
  by_cases hsame : p = a.phase
  · subst p
    simp [runInitsBetween_self_api]
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;> fin_cases p
  all_goals
    simp at hsame hle hp hres_le hmcr hcarrier hnoerr ⊢
  all_goals
    try contradiction
    try omega
  all_goals
    unfold runInitsBetween at hres_le ⊢
    first
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 4) = [3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 3 < k ∧ k ≤ 4) = [4] := by decide
        rw [hlist] at hres_le ⊢
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, prePhase4Mass, AgentState.smallBiasInt,
        Bias.toRat, enterPhase10, phase10] at hres_le hmcr hcarrier hnoerr ⊢ <;>
      omega

set_option maxHeartbeats 4000000 in
private lemma runInitsBetween_update_phase_wf_to_four
    (a : AgentState L K) (p : Fin 11)
    (hle : a.phase.val ≤ p.val)
    (hp : p.val ≤ 4)
    (hres_le :
      (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val ≤ 4)
    (hmcr : a.role ≠ .mcr)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hnoerr : 2 ≤ a.phase.val →
      a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).role ≠ .mcr ∧
      ((runInitsBetween L K a.phase.val p.val ({ a with phase := p })).role ≠ .main →
        (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).smallBias.val = 3) ∧
      (2 ≤ (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val →
        (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).smallBias.val ∈
          ({2, 3, 4} : Finset ℕ)) := by
  by_cases hsame : p = a.phase
  · subst p
    simp [runInitsBetween_self_api]
    constructor
    · exact hmcr
    constructor
    · exact hcarrier
    · intro hphase
      simpa using hnoerr hphase
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;> fin_cases p
  all_goals
    simp at hsame hle hp hres_le hmcr hcarrier hnoerr ⊢
  all_goals
    try contradiction
    try omega
  all_goals
    unfold runInitsBetween at hres_le ⊢
    first
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 4) = [3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 3 < k ∧ k ≤ 4) = [4] := by decide
        rw [hlist] at hres_le ⊢
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at hres_le hmcr hcarrier hnoerr ⊢ <;>
      omega

-- If the epidemic re-initialization carries an agent (with its phase first set
-- to the synchronized target `p`) up to a configuration whose phase is exactly 4,
-- then its `output` is `.T`.  Either the agent crossed into Phase 4 (the last
-- `phaseInit` run is `phaseInit ⟨4⟩`, which sets `output := .T`), or it was
-- already in Phase 4 (run is identity and `hout` supplies `.T`).
-- maxHeartbeats raised like the sibling `runInitsBetween_update_phase_wf_to_four`.
set_option maxHeartbeats 1600000 in
private lemma runInitsBetween_update_output_T_of_phase_four
    (a : AgentState L K) (p : Fin 11)
    (hle : a.phase.val ≤ p.val)
    (hp : p.val ≤ 4)
    (hres :
      (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = 4)
    (hout : a.phase.val = 4 → a.output = .T) :
    (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).output = .T := by
  by_cases hsame : p = a.phase
  · subst p
    have hphase4 : a.phase.val = 4 := by
      simpa [runInitsBetween_self_api] using hres
    simp [runInitsBetween_self_api]
    exact hout hphase4
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;> fin_cases p
  all_goals
    simp at hsame hle hp hres hout ⊢
  all_goals
    try contradiction
    try omega
  all_goals
    unfold runInitsBetween at hres ⊢
    first
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 4) = [3, 4] := by decide
        rw [hlist] at hres ⊢
      | have hlist :
          (List.range 11).filter (fun k => 3 < k ∧ k ≤ 4) = [4] := by decide
        rw [hlist] at hres ⊢
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at hres ⊢ <;>
      first | rfl | omega

private lemma prePhase4Mass_advancePhaseWithInit_of_phase_two_wf
    (a : AgentState L K)
    (hphase : a.phase.val = 2)
    (hmcr : a.role ≠ .mcr)
    (hcarrier : a.role ≠ .main → a.smallBias.val = 3)
    (hsmall : a.smallBias.val = 2 ∨ a.smallBias.val = 3 ∨ a.smallBias.val = 4) :
    prePhase4Mass (advancePhaseWithInit L K a) =
      (AgentState.smallBiasInt a : ℚ) := by
  have hphase_eq : a.phase = ⟨2, by decide⟩ := Fin.ext hphase
  have hphase' :
      ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).phase.val = 3 := by
    rfl
  have hmcr' :
      ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).role ≠ .mcr := by
    simpa using hmcr
  have hcarrier' :
      ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).role ≠ .main →
        ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).smallBias.val = 3 := by
    simpa using hcarrier
  have hsmall' :
      ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).smallBias.val = 2 ∨
        ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).smallBias.val = 3 ∨
        ({ a with phase := ⟨3, by decide⟩ } : AgentState L K).smallBias.val = 4 := by
    simpa using hsmall
  have hinit :=
    prePhase4Mass_phaseInit_three_of_wf
      (L := L) (K := K) ({ a with phase := ⟨3, by decide⟩ } : AgentState L K)
      hphase' hmcr' hcarrier' hsmall'
  simpa [advancePhaseWithInit, advancePhase, hphase_eq, AgentState.smallBiasInt]
    using hinit

theorem Phase2Transition_preserves_prePhase4Mass_pair_of_phase_two_wf
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 2) (ht_phase : t.phase.val = 2)
    (hs_mcr : s.role ≠ .mcr) (ht_mcr : t.role ≠ .mcr)
    (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (hs_small : s.smallBias.val = 2 ∨ s.smallBias.val = 3 ∨ s.smallBias.val = 4)
    (ht_small : t.smallBias.val = 2 ∨ t.smallBias.val = 3 ∨ t.smallBias.val = 4) :
    prePhase4Mass (Phase2Transition L K s t).1 +
      prePhase4Mass (Phase2Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  let univ := opinionsUnion s.opinions t.opinions
  let s' : AgentState L K := { s with opinions := univ }
  let t' : AgentState L K := { t with opinions := univ }
  have hs'_phase : s'.phase.val = 2 := by simp [s', hs_phase]
  have ht'_phase : t'.phase.val = 2 := by simp [t', ht_phase]
  have hs'_mcr : s'.role ≠ .mcr := by simpa [s'] using hs_mcr
  have ht'_mcr : t'.role ≠ .mcr := by simpa [t'] using ht_mcr
  have hs'_carrier : s'.role ≠ .main → s'.smallBias.val = 3 := by
    simpa [s'] using hs_carrier
  have ht'_carrier : t'.role ≠ .main → t'.smallBias.val = 3 := by
    simpa [t'] using ht_carrier
  have hs'_small :
      s'.smallBias.val = 2 ∨ s'.smallBias.val = 3 ∨ s'.smallBias.val = 4 := by
    simpa [s'] using hs_small
  have ht'_small :
      t'.smallBias.val = 2 ∨ t'.smallBias.val = 3 ∨ t'.smallBias.val = 4 := by
    simpa [t'] using ht_small
  have hs_pre : prePhase4Mass s = (AgentState.smallBiasInt s : ℚ) := by
    simp [prePhase4Mass, hs_phase]
  have ht_pre : prePhase4Mass t = (AgentState.smallBiasInt t : ℚ) := by
    simp [prePhase4Mass, ht_phase]
  have hs'_pre : prePhase4Mass s' = (AgentState.smallBiasInt s : ℚ) := by
    simp [prePhase4Mass, s', hs_phase, AgentState.smallBiasInt]
  have ht'_pre : prePhase4Mass t' = (AgentState.smallBiasInt t : ℚ) := by
    simp [prePhase4Mass, t', ht_phase, AgentState.smallBiasInt]
  have hs_adv :
      prePhase4Mass (advancePhaseWithInit L K s') =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa [s', AgentState.smallBiasInt] using
      prePhase4Mass_advancePhaseWithInit_of_phase_two_wf
        (L := L) (K := K) s' hs'_phase hs'_mcr hs'_carrier hs'_small
  have ht_adv :
      prePhase4Mass (advancePhaseWithInit L K t') =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa [t', AgentState.smallBiasInt] using
      prePhase4Mass_advancePhaseWithInit_of_phase_two_wf
        (L := L) (K := K) t' ht'_phase ht'_mcr ht'_carrier ht'_small
  have hs'_A_pre :
      prePhase4Mass ({ s' with output := .A } : AgentState L K) =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa using hs'_pre
  have ht'_A_pre :
      prePhase4Mass ({ t' with output := .A } : AgentState L K) =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa using ht'_pre
  have hs'_B_pre :
      prePhase4Mass ({ s' with output := .B } : AgentState L K) =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa using hs'_pre
  have ht'_B_pre :
      prePhase4Mass ({ t' with output := .B } : AgentState L K) =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa using ht'_pre
  have hs'_T_pre :
      prePhase4Mass ({ s' with output := .T } : AgentState L K) =
        (AgentState.smallBiasInt s : ℚ) := by
    simpa using hs'_pre
  have ht'_T_pre :
      prePhase4Mass ({ t' with output := .T } : AgentState L K) =
        (AgentState.smallBiasInt t : ℚ) := by
    simpa using ht'_pre
  unfold Phase2Transition
  change
    prePhase4Mass
        (if hasMinusOne univ && hasPlusOne univ then
          (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
        else if hasPlusOne univ then
          ({ s' with output := .A }, { t' with output := .A })
        else if hasMinusOne univ then
          ({ s' with output := .B }, { t' with output := .B })
        else if univ.val = 2 then
          ({ s' with output := .T }, { t' with output := .T })
        else (s', t')).1 +
      prePhase4Mass
        (if hasMinusOne univ && hasPlusOne univ then
          (advancePhaseWithInit L K s', advancePhaseWithInit L K t')
        else if hasPlusOne univ then
          ({ s' with output := .A }, { t' with output := .A })
        else if hasMinusOne univ then
          ({ s' with output := .B }, { t' with output := .B })
        else if univ.val = 2 then
          ({ s' with output := .T }, { t' with output := .T })
        else (s', t')).2 =
      prePhase4Mass s + prePhase4Mass t
  cases hminus : hasMinusOne univ <;> cases hplus : hasPlusOne univ
  · by_cases htie : univ.val = 2
    · simp [hminus, hplus, htie, hs'_T_pre, ht'_T_pre, hs_pre, ht_pre]
    · simp [hminus, hplus, htie, hs'_pre, ht'_pre, hs_pre, ht_pre]
  · simp [hminus, hplus, hs'_A_pre, ht'_A_pre, hs_pre, ht_pre]
  · simp [hminus, hplus, hs'_B_pre, ht'_B_pre, hs_pre, ht_pre]
  · simp [hminus, hplus, hs_adv, ht_adv, hs_pre, ht_pre]

theorem Phase3Transition_preserves_prePhase4Mass_pair_of_phase_three
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 3) (ht_phase : t.phase.val = 3) :
    prePhase4Mass (Phase3Transition L K s t).1 +
      prePhase4Mass (Phase3Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  have hpair :=
    Phase3Transition_preserves_dyadicBiasSum_pair_of_phase_three
      (L := L) (K := K) s t hs_phase ht_phase
  have hmono := Phase3Transition_phase_nondec (L := L) (K := K) s t
  have hs_not : ¬ s.phase.val < 3 := by omega
  have ht_not : ¬ t.phase.val < 3 := by omega
  have hs_out_not : ¬ (Phase3Transition L K s t).1.phase.val < 3 := by
    omega
  have ht_out_not : ¬ (Phase3Transition L K s t).2.phase.val < 3 := by
    omega
  simpa [prePhase4Mass, hs_not, ht_not, hs_out_not, ht_out_not] using hpair

theorem Phase4Transition_preserves_prePhase4Mass_pair_of_phase_four
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 4) (ht_phase : t.phase.val = 4) :
    prePhase4Mass (Phase4Transition L K s t).1 +
      prePhase4Mass (Phase4Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  have hpair := Phase4Transition_preserves_dyadicBiasSum_pair
    (L := L) (K := K) s t
  have hmono := Phase4Transition_phase_nondec (L := L) (K := K) s t
  have hs_not : ¬ s.phase.val < 3 := by omega
  have ht_not : ¬ t.phase.val < 3 := by omega
  have hs_out_not : ¬ (Phase4Transition L K s t).1.phase.val < 3 := by
    omega
  have ht_out_not : ¬ (Phase4Transition L K s t).2.phase.val < 3 := by
    omega
  simpa [prePhase4Mass, hs_not, ht_not, hs_out_not, ht_out_not] using hpair

set_option maxHeartbeats 4000000 in
private theorem Phase0Transition_preserves_prePhase4Mass_pair_of_phase_zero_no_mcr
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 0) (ht_phase : t.phase.val = 0)
    (hs_mcr : s.role ≠ .mcr) (ht_mcr : t.role ≠ .mcr) :
    prePhase4Mass (Phase0Transition L K s t).1 +
      prePhase4Mass (Phase0Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  fin_cases sphase <;> fin_cases tphase <;>
    simp at hs_phase ht_phase hs_mcr ht_mcr ⊢
  cases srole <;> cases trole <;>
    simp at hs_mcr ht_mcr
  all_goals try contradiction
  all_goals
    fin_cases ssmallBias <;> fin_cases tsmallBias <;>
    simp [Phase0Transition, prePhase4Mass, AgentState.smallBiasInt,
      clockCounterStep, stdCounterSubroutine, advancePhaseWithInit,
      advancePhase, phaseInit, enterPhase10, phase10] <;>
    repeat' split_ifs <;>
    simp [prePhase4Mass, AgentState.smallBiasInt, phaseInit, enterPhase10, phase10] <;>
    first | norm_num | omega

set_option maxHeartbeats 4000000 in
private theorem Phase1Transition_preserves_prePhase4Mass_pair_of_phase_one_wf
    (s t : AgentState L K)
    (hs_phase : s.phase.val = 1) (ht_phase : t.phase.val = 1)
    (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (hout1 : (Phase1Transition L K s t).1.phase.val ≤ 4)
    (hout2 : (Phase1Transition L K s t).2.phase.val ≤ 4) :
    prePhase4Mass (Phase1Transition L K s t).1 +
      prePhase4Mass (Phase1Transition L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · have hs_out :
        prePhase4Mass (Phase1Transition L K s t).1 =
          (((avgFin7 s.smallBias t.smallBias).1.val : ℤ) - 3 : ℚ) := by
      simp [Phase1Transition, hmain, hmain.1, hmain.2, clockCounterStep,
        prePhase4Mass, hs_phase, AgentState.smallBiasInt]
    have ht_out :
        prePhase4Mass (Phase1Transition L K s t).2 =
          (((avgFin7 s.smallBias t.smallBias).2.val : ℤ) - 3 : ℚ) := by
      simp [Phase1Transition, hmain, hmain.1, hmain.2, clockCounterStep,
        prePhase4Mass, ht_phase, AgentState.smallBiasInt]
    have hs_in :
        prePhase4Mass s = ((s.smallBias.val : ℤ) - 3 : ℚ) := by
      simp [prePhase4Mass, hs_phase, AgentState.smallBiasInt]
    have ht_in :
        prePhase4Mass t = ((t.smallBias.val : ℤ) - 3 : ℚ) := by
      simp [prePhase4Mass, ht_phase, AgentState.smallBiasInt]
    have hsumZ := avgFin7_preserves_sum_transition s.smallBias t.smallBias
    have hsumQ :
        ((avgFin7 s.smallBias t.smallBias).1.val : ℚ) +
          ((avgFin7 s.smallBias t.smallBias).2.val : ℚ) =
        (s.smallBias.val : ℚ) + (t.smallBias.val : ℚ) := by
      exact_mod_cast hsumZ
    rw [hs_out, ht_out, hs_in, ht_in]
    ring_nf
    simpa [add_assoc, add_comm, add_left_comm] using
      congrArg (fun q : ℚ => -6 + q) hsumQ
  · rcases s with
      ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
        shour, sminute, sfull, sopinions, scounter⟩
    rcases t with
      ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
        thour, tminute, tfull, topinions, tcounter⟩
    fin_cases sphase <;> fin_cases tphase <;>
      simp at hs_phase ht_phase hmain hs_carrier ht_carrier hout1 hout2 ⊢
    cases srole <;> cases trole <;>
      simp at hmain hs_carrier ht_carrier
    all_goals try contradiction
    all_goals
      fin_cases ssmallBias <;> fin_cases tsmallBias <;>
      simp [Phase1Transition, prePhase4Mass, clockCounterStep,
        stdCounterSubroutine, advancePhaseWithInit, advancePhase, phaseInit,
        enterPhase10, phase10, AgentState.smallBiasInt, Bias.toRat,
        avgFin7] at hs_carrier ht_carrier hout1 hout2 ⊢ <;>
      repeat' split_ifs at * <;>
      simp_all [prePhase4Mass, AgentState.smallBiasInt, phaseInit, enterPhase10,
        phase10, Bias.toRat] <;>
      first | norm_num | omega

theorem phaseEpidemicUpdate_preserves_prePhase4Mass_pair
    (s t : AgentState L K)
    (hs_mcr : s.role ≠ .mcr) (ht_mcr : t.role ≠ .mcr)
    (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (hs_noerr : 2 ≤ s.phase.val →
      s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (ht_noerr : 2 ≤ t.phase.val →
      t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hout1_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4)
    (hout2_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4) :
    prePhase4Mass (phaseEpidemicUpdate L K s t).1 +
      prePhase4Mass (phaseEpidemicUpdate L K s t).2 =
    prePhase4Mass s + prePhase4Mass t := by
  have hmax_le : max s.phase.val t.phase.val ≤ 4 := by
    exact le_trans (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t)
      hout1_le
  unfold phaseEpidemicUpdate at hout1_le hout2_le ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).1.phase.val ≤ 4 at hout1_le
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).2.phase.val ≤ 4 at hout2_le
  change prePhase4Mass
        (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
            (s0.phase.val = 10 ∨ t0.phase.val = 10) then
          (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
        else (s0, t0)).1 +
      prePhase4Mass
        (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
            (s0.phase.val = 10 ∨ t0.phase.val = 10) then
          (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
        else (s0, t0)).2 =
    prePhase4Mass s + prePhase4Mass t
  have hp_le : p.val ≤ 4 := by
    simpa [p] using hmax_le
  have hs_le_p : s.phase.val ≤ p.val := by
    simpa [p] using (le_max_left s.phase.val t.phase.val)
  have ht_le_p : t.phase.val ≤ p.val := by
    simpa [p] using (le_max_right s.phase.val t.phase.val)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_lt : s.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := K) s s0 hs_lt
    have hle : (phase10EpidemicEntry L K s s0).phase.val ≤ 4 := by
      simpa [h10] using hout1_le
    omega
  · have hs0_le : s0.phase.val ≤ 4 := by
      simpa [h10] using hout1_le
    have ht0_le : t0.phase.val ≤ 4 := by
      simpa [h10] using hout2_le
    have hs_mass : prePhase4Mass s0 = prePhase4Mass s := by
      dsimp [s0]
      exact
        runInitsBetween_update_phase_preserves_prePhase4Mass_to_four
          (L := L) (K := K) s p hs_le_p hp_le
          (by simpa [s0] using hs0_le) hs_mcr hs_carrier hs_noerr
    have ht_mass : prePhase4Mass t0 = prePhase4Mass t := by
      dsimp [t0]
      exact
        runInitsBetween_update_phase_preserves_prePhase4Mass_to_four
          (L := L) (K := K) t p ht_le_p hp_le
          (by simpa [t0] using ht0_le) ht_mcr ht_carrier ht_noerr
    simpa [h10, hs_mass, ht_mass]

-- Re-initializing from a phase `≤ p ≤ 4` up to the synchronized target `p`
-- either lands at `p` (`≤ 4`) or hits the error Phase 10 — no other value.
set_option maxHeartbeats 4000000 in
private lemma runInitsBetween_update_phase_le_four_or_ten
    (a : AgentState L K) (p : Fin 11)
    (hle : a.phase.val ≤ p.val)
    (hp : p.val ≤ 4) :
    (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val ≤ 4 ∨
      (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val = 10 := by
  by_cases hsame : p = a.phase
  · subst p
    left; simp [runInitsBetween_self_api]; omega
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;> fin_cases p
  all_goals
    simp at hsame hle hp ⊢
  all_goals
    try contradiction
    try omega
  all_goals
    unfold runInitsBetween
    first
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 4) = [3, 4] := by decide
        rw [hlist]
      | have hlist :
          (List.range 11).filter (fun k => 3 < k ∧ k ≤ 4) = [4] := by decide
        rw [hlist]
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] <;>
      omega

set_option maxHeartbeats 4000000 in
private lemma runInitsBetween_update_phase_eq_target_of_le_four
    (a : AgentState L K) (p : Fin 11)
    (hle : a.phase.val ≤ p.val)
    (hp : p.val ≤ 4)
    (hres_le :
      (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase.val ≤ 4) :
    (runInitsBetween L K a.phase.val p.val ({ a with phase := p })).phase = p := by
  by_cases hsame : p = a.phase
  · subst p
    simp [runInitsBetween_self_api]
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  fin_cases phase <;> fin_cases p
  all_goals
    simp at hsame hle hp hres_le ⊢
  all_goals
    try contradiction
    try omega
  all_goals
    unfold runInitsBetween at hres_le ⊢
    first
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 2) = [1, 2] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 3) = [1, 2, 3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 0 < k ∧ k ≤ 4) = [1, 2, 3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 2) = [2] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 3) = [2, 3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 1 < k ∧ k ≤ 4) = [2, 3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 3) = [3] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 2 < k ∧ k ≤ 4) = [3, 4] := by decide
        rw [hlist] at hres_le ⊢
      | have hlist :
          (List.range 11).filter (fun k => 3 < k ∧ k ≤ 4) = [4] := by decide
        rw [hlist] at hres_le ⊢
    cases role <;> fin_cases smallBias <;>
      simp [phaseInit, enterPhase10, phase10] at hres_le ⊢ <;>
      omega

theorem phaseEpidemicUpdate_phases_eq_of_outputs_le_four
    (s t : AgentState L K)
    (hout1_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4)
    (hout2_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4) :
    (phaseEpidemicUpdate L K s t).1.phase =
      (phaseEpidemicUpdate L K s t).2.phase := by
  have hmax_le : max s.phase.val t.phase.val ≤ 4 := by
    exact le_trans (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t)
      hout1_le
  unfold phaseEpidemicUpdate at hout1_le hout2_le ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).1.phase.val ≤ 4 at hout1_le
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).2.phase.val ≤ 4 at hout2_le
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).1.phase =
      (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).2.phase
  have hp_le : p.val ≤ 4 := by
    simpa [p] using hmax_le
  have hs_le_p : s.phase.val ≤ p.val := by
    simpa [p] using (le_max_left s.phase.val t.phase.val)
  have ht_le_p : t.phase.val ≤ p.val := by
    simpa [p] using (le_max_right s.phase.val t.phase.val)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_lt : s.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := K) s s0 hs_lt
    have hle : (phase10EpidemicEntry L K s s0).phase.val ≤ 4 := by
      simpa [h10] using hout1_le
    omega
  · have hs0_le : s0.phase.val ≤ 4 := by
      simpa [h10] using hout1_le
    have ht0_le : t0.phase.val ≤ 4 := by
      simpa [h10] using hout2_le
    have hs0_phase : s0.phase = p := by
      dsimp [s0]
      exact runInitsBetween_update_phase_eq_target_of_le_four
        (L := L) (K := K) s p hs_le_p hp_le (by simpa [s0] using hs0_le)
    have ht0_phase : t0.phase = p := by
      dsimp [t0]
      exact runInitsBetween_update_phase_eq_target_of_le_four
        (L := L) (K := K) t p ht_le_p hp_le (by simpa [t0] using ht0_le)
    have hp_ne_ten : ¬ p.val = 10 := by omega
    simp [hs0_phase, ht0_phase, hp_ne_ten]

/-- If the *right* epidemic output is in a phase `≤ 4`, so is the left one (when
neither hits Phase 10, both equal the synchronized target). -/
theorem phaseEpidemicUpdate_left_phase_le_four_of_right_le_four
    (s t : AgentState L K)
    (hout2_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4) :
    (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4 := by
  have hmax_le : max s.phase.val t.phase.val ≤ 4 :=
    le_trans (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t) hout2_le
  unfold phaseEpidemicUpdate at hout2_le ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).2.phase.val ≤ 4 at hout2_le
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).1.phase.val ≤ 4
  have hp_le : p.val ≤ 4 := by simpa [p] using hmax_le
  have hs_le_p : s.phase.val ≤ p.val := by
    simpa [p] using (le_max_left s.phase.val t.phase.val)
  have ht_le_p : t.phase.val ≤ p.val := by
    simpa [p] using (le_max_right s.phase.val t.phase.val)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have ht_lt : t.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := K) t t0 ht_lt
    have hle : (phase10EpidemicEntry L K t t0).phase.val ≤ 4 := by
      simpa [h10] using hout2_le
    omega
  · -- In the no-Phase-10 branch, both s,t are below 10, so `h10` being false
    -- forces `s0.phase ≠ 10`; combined with the dichotomy, `s0.phase ≤ 4`.
    have hs_lt_ten : s.phase.val < 10 := by omega
    have hs0_ne_ten : s0.phase.val ≠ 10 := by
      by_contra hc
      exact h10 ⟨Or.inl hs_lt_ten, Or.inl hc⟩
    have hs0_dich :
        s0.phase.val ≤ 4 ∨ s0.phase.val = 10 := by
      dsimp [s0]
      exact runInitsBetween_update_phase_le_four_or_ten
        (L := L) (K := K) s p hs_le_p hp_le
    have hs0_le : s0.phase.val ≤ 4 := by
      rcases hs0_dich with h | h
      · exact h
      · exact absurd h hs0_ne_ten
    simpa [h10] using hs0_le

theorem phaseEpidemicUpdate_phase_le_Transition_phase
    (s t : AgentState L K) :
    (phaseEpidemicUpdate L K s t).1.phase.val ≤ (Transition L K s t).1.phase.val ∧
      (phaseEpidemicUpdate L K s t).2.phase.val ≤ (Transition L K s t).2.phase.val := by
  unfold Transition
  rcases hpe : phaseEpidemicUpdate L K s t with ⟨s', t'⟩
  simp only [hpe]
  let out :=
    match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')
  change s'.phase.val ≤ (finishPhase10Entry L K s' out.1).phase.val ∧
    t'.phase.val ≤ (finishPhase10Entry L K t' out.2).phase.val
  have hdispatch : s'.phase.val ≤ out.1.phase.val ∧ t'.phase.val ≤ out.2.phase.val := by
    dsimp [out]
    rcases h_phase : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ => simpa [h_phase] using Phase0Transition_phase_nondec L K s' t'
    | 1, _ => simpa [h_phase] using Phase1Transition_phase_nondec L K s' t'
    | 2, _ => simpa [h_phase] using Phase2Transition_phase_nondec L K s' t'
    | 3, _ => simpa [h_phase] using Phase3Transition_phase_nondec L K s' t'
    | 4, _ => simpa [h_phase] using Phase4Transition_phase_nondec L K s' t'
    | 5, _ => simpa [h_phase] using Phase5Transition_phase_nondec L K s' t'
    | 6, _ => simpa [h_phase] using Phase6Transition_phase_nondec L K s' t'
    | 7, _ => simpa [h_phase] using Phase7Transition_phase_nondec L K s' t'
    | 8, _ => simpa [h_phase] using Phase8Transition_phase_nondec L K s' t'
    | 9, _ => simpa [h_phase] using Phase9Transition_phase_nondec L K s' t'
    | 10, _ => simpa [h_phase] using Phase10Transition_phase_nondec L K s' t'
    | n + 11, hn => omega
  constructor
  · simpa using hdispatch.1
  · simpa using hdispatch.2

set_option maxHeartbeats 4000000 in
private theorem phaseEpidemicUpdate_left_wf_to_four
    (s t : AgentState L K)
    (hs_mcr : s.role ≠ .mcr)
    (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (hs_noerr : 2 ≤ s.phase.val →
      s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hout_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4) :
    (phaseEpidemicUpdate L K s t).1.role ≠ .mcr ∧
      ((phaseEpidemicUpdate L K s t).1.role ≠ .main →
        (phaseEpidemicUpdate L K s t).1.smallBias.val = 3) ∧
      (2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val →
        (phaseEpidemicUpdate L K s t).1.smallBias.val ∈
          ({2, 3, 4} : Finset ℕ)) := by
  have hmax_le : max s.phase.val t.phase.val ≤ 4 := by
    exact le_trans (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t)
      hout_le
  unfold phaseEpidemicUpdate at hout_le ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).1.phase.val ≤ 4 at hout_le
  have hp_le : p.val ≤ 4 := by
    simpa [p] using hmax_le
  have hs_le_p : s.phase.val ≤ p.val := by
    simpa [p] using (le_max_left s.phase.val t.phase.val)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_lt : s.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := K) s s0 hs_lt
    have hle : (phase10EpidemicEntry L K s s0).phase.val ≤ 4 := by
      simpa [h10] using hout_le
    omega
  · have hs0_le : s0.phase.val ≤ 4 := by
      simpa [h10] using hout_le
    simpa [h10, s0, t0] using
      runInitsBetween_update_phase_wf_to_four
        (L := L) (K := K) s p hs_le_p hp_le (by simpa [s0] using hs0_le)
        hs_mcr hs_carrier hs_noerr

set_option maxHeartbeats 4000000 in
private theorem phaseEpidemicUpdate_right_wf_to_four
    (s t : AgentState L K)
    (ht_mcr : t.role ≠ .mcr)
    (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (ht_noerr : 2 ≤ t.phase.val →
      t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hout_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4) :
    (phaseEpidemicUpdate L K s t).2.role ≠ .mcr ∧
      ((phaseEpidemicUpdate L K s t).2.role ≠ .main →
        (phaseEpidemicUpdate L K s t).2.smallBias.val = 3) ∧
      (2 ≤ (phaseEpidemicUpdate L K s t).2.phase.val →
        (phaseEpidemicUpdate L K s t).2.smallBias.val ∈
          ({2, 3, 4} : Finset ℕ)) := by
  have hmax_le : max s.phase.val t.phase.val ≤ 4 := by
    exact le_trans (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t)
      hout_le
  unfold phaseEpidemicUpdate at hout_le ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).2.phase.val ≤ 4 at hout_le
  have hp_le : p.val ≤ 4 := by
    simpa [p] using hmax_le
  have ht_le_p : t.phase.val ≤ p.val := by
    simpa [p] using (le_max_right s.phase.val t.phase.val)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have ht_lt : t.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := K) t t0 ht_lt
    have hle : (phase10EpidemicEntry L K t t0).phase.val ≤ 4 := by
      simpa [h10] using hout_le
    omega
  · have ht0_le : t0.phase.val ≤ 4 := by
      simpa [h10] using hout_le
    simpa [h10, s0, t0] using
      runInitsBetween_update_phase_wf_to_four
        (L := L) (K := K) t p ht_le_p hp_le (by simpa [t0] using ht0_le)
        ht_mcr ht_carrier ht_noerr

-- The epidemic phase update gives the left output `.T` whenever its phase is 4.
set_option maxHeartbeats 4000000 in
theorem phaseEpidemicUpdate_left_output_T_of_phase_four
    (s t : AgentState L K)
    (hs_out : s.phase.val = 4 → s.output = .T)
    (hphase : (phaseEpidemicUpdate L K s t).1.phase.val = 4) :
    (phaseEpidemicUpdate L K s t).1.output = .T := by
  have hout_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4 := by omega
  have hmax_le : max s.phase.val t.phase.val ≤ 4 := by
    exact le_trans (phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t)
      hout_le
  unfold phaseEpidemicUpdate at hphase ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).1.phase.val = 4 at hphase
  have hp_le : p.val ≤ 4 := by
    simpa [p] using hmax_le
  have hs_le_p : s.phase.val ≤ p.val := by
    simpa [p] using (le_max_left s.phase.val t.phase.val)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have hs_lt : s.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := K) s s0 hs_lt
    have heq : (phase10EpidemicEntry L K s s0).phase.val = 4 := by
      simpa [h10] using hphase
    omega
  · have hs0_phase : s0.phase.val = 4 := by
      simpa [h10] using hphase
    have hkey :
        (runInitsBetween L K s.phase.val p.val ({ s with phase := p })).output = .T :=
      runInitsBetween_update_output_T_of_phase_four
        (L := L) (K := K) s p hs_le_p hp_le
        (by simpa [s0] using hs0_phase) hs_out
    rw [if_neg h10]
    exact hkey

-- The epidemic phase update gives the right output `.T` whenever its phase is 4.
set_option maxHeartbeats 4000000 in
theorem phaseEpidemicUpdate_right_output_T_of_phase_four
    (s t : AgentState L K)
    (ht_out : t.phase.val = 4 → t.output = .T)
    (hphase : (phaseEpidemicUpdate L K s t).2.phase.val = 4) :
    (phaseEpidemicUpdate L K s t).2.output = .T := by
  have hout_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4 := by omega
  have hmax_le : max s.phase.val t.phase.val ≤ 4 := by
    exact le_trans (phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t)
      hout_le
  unfold phaseEpidemicUpdate at hphase ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else (s0, t0)).2.phase.val = 4 at hphase
  have hp_le : p.val ≤ 4 := by
    simpa [p] using hmax_le
  have ht_le_p : t.phase.val ≤ p.val := by
    simpa [p] using (le_max_right s.phase.val t.phase.val)
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · have ht_lt : t.phase.val < 10 := by omega
    have hten := phase10EpidemicEntry_phase_val_of_before_lt_10
      (L := L) (K := K) t t0 ht_lt
    have heq : (phase10EpidemicEntry L K t t0).phase.val = 4 := by
      simpa [h10] using hphase
    omega
  · have ht0_phase : t0.phase.val = 4 := by
      simpa [h10] using hphase
    have hkey :
        (runInitsBetween L K t.phase.val p.val ({ t with phase := p })).output = .T :=
      runInitsBetween_update_output_T_of_phase_four
        (L := L) (K := K) t p ht_le_p hp_le
        (by simpa [t0] using ht0_phase) ht_out
    rw [if_neg h10]
    exact hkey

set_option maxHeartbeats 8000000 in
theorem Transition_preserves_prePhase4Mass_pair
    (s t : AgentState L K)
    (hs_mcr : s.role ≠ .mcr) (ht_mcr : t.role ≠ .mcr)
    (hs_carrier : s.role ≠ .main → s.smallBias.val = 3)
    (ht_carrier : t.role ≠ .main → t.smallBias.val = 3)
    (hs_noerr : 2 ≤ s.phase.val →
      s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (ht_noerr : 2 ≤ t.phase.val →
      t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hout1 : (Transition L K s t).1.phase.val ≤ 4)
    (hout2 : (Transition L K s t).2.phase.val ≤ 4) :
    prePhase4Mass (Transition L K s t).1 + prePhase4Mass (Transition L K s t).2 =
      prePhase4Mass s + prePhase4Mass t := by
  have hmono := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t
  have hep1_le : (phaseEpidemicUpdate L K s t).1.phase.val ≤ 4 :=
    le_trans hmono.1 hout1
  have hep2_le : (phaseEpidemicUpdate L K s t).2.phase.val ≤ 4 :=
    le_trans hmono.2 hout2
  have hep_mass :=
    phaseEpidemicUpdate_preserves_prePhase4Mass_pair
      (L := L) (K := K) s t hs_mcr ht_mcr hs_carrier ht_carrier
      hs_noerr ht_noerr hep1_le hep2_le
  have hep_phase_eq :=
    phaseEpidemicUpdate_phases_eq_of_outputs_le_four
      (L := L) (K := K) s t hep1_le hep2_le
  have hwf_left :=
    phaseEpidemicUpdate_left_wf_to_four
      (L := L) (K := K) s t hs_mcr hs_carrier hs_noerr hep1_le
  have hwf_right :=
    phaseEpidemicUpdate_right_wf_to_four
      (L := L) (K := K) s t ht_mcr ht_carrier ht_noerr hep2_le
  unfold Transition at hout1 hout2 ⊢
  generalize he : phaseEpidemicUpdate L K s t = ep
  rcases ep with ⟨s', t'⟩
  simp only [he] at hout1 hout2 ⊢
  let out :=
    match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')
  change
    prePhase4Mass (finishPhase10Entry L K s' out.1) +
        prePhase4Mass (finishPhase10Entry L K t' out.2) =
      prePhase4Mass s + prePhase4Mass t
  change (finishPhase10Entry L K s' out.1).phase.val ≤ 4 at hout1
  change (finishPhase10Entry L K t' out.2).phase.val ≤ 4 at hout2
  have hout1_out : out.1.phase.val ≤ 4 := by
    simpa using hout1
  have hout2_out : out.2.phase.val ≤ 4 := by
    simpa using hout2
  have hfinish1 : finishPhase10Entry L K s' out.1 = out.1 := by
    apply finishPhase10Entry_eq_self_of_after_ne_10
    omega
  have hfinish2 : finishPhase10Entry L K t' out.2 = out.2 := by
    apply finishPhase10Entry_eq_self_of_after_ne_10
    omega
  have hs'_mcr : s'.role ≠ .mcr := by
    simpa [he] using hwf_left.1
  have ht'_mcr : t'.role ≠ .mcr := by
    simpa [he] using hwf_right.1
  have hs'_carrier : s'.role ≠ .main → s'.smallBias.val = 3 := by
    simpa [he] using hwf_left.2.1
  have ht'_carrier : t'.role ≠ .main → t'.smallBias.val = 3 := by
    simpa [he] using hwf_right.2.1
  have hs'_noerr : 2 ≤ s'.phase.val →
      s'.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    simpa [he] using hwf_left.2.2
  have ht'_noerr : 2 ≤ t'.phase.val →
      t'.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    simpa [he] using hwf_right.2.2
  have hphase_eq : s'.phase = t'.phase := by
    simpa [he] using hep_phase_eq
  have hdispatch :
      prePhase4Mass out.1 + prePhase4Mass out.2 =
        prePhase4Mass s' + prePhase4Mass t' := by
    dsimp [out]
    rcases hsp : s'.phase with ⟨n, hn⟩
    match n, hn with
    | 0, _ =>
        have hs_phase : s'.phase.val = 0 := by simpa [hsp]
        have ht_phase : t'.phase.val = 0 := by
          rw [← hphase_eq, hsp]
        simpa [hsp] using
          Phase0Transition_preserves_prePhase4Mass_pair_of_phase_zero_no_mcr
            (L := L) (K := K) s' t' hs_phase ht_phase hs'_mcr ht'_mcr
    | 1, _ =>
        have hs_phase : s'.phase.val = 1 := by simpa [hsp]
        have ht_phase : t'.phase.val = 1 := by
          rw [← hphase_eq, hsp]
        have hout1_phase1 : (Phase1Transition L K s' t').1.phase.val ≤ 4 := by
          simpa [hsp, out] using hout1_out
        have hout2_phase1 : (Phase1Transition L K s' t').2.phase.val ≤ 4 := by
          simpa [hsp, out] using hout2_out
        simpa [hsp] using
          Phase1Transition_preserves_prePhase4Mass_pair_of_phase_one_wf
            (L := L) (K := K) s' t' hs_phase ht_phase
            hs'_carrier ht'_carrier hout1_phase1 hout2_phase1
    | 2, _ =>
        have hs_phase : s'.phase.val = 2 := by simpa [hsp]
        have ht_phase : t'.phase.val = 2 := by
          rw [← hphase_eq, hsp]
        have hs_small : s'.smallBias.val = 2 ∨ s'.smallBias.val = 3 ∨
            s'.smallBias.val = 4 := by
          simpa using hs'_noerr (by omega)
        have ht_small : t'.smallBias.val = 2 ∨ t'.smallBias.val = 3 ∨
            t'.smallBias.val = 4 := by
          simpa using ht'_noerr (by omega)
        simpa [hsp] using
          Phase2Transition_preserves_prePhase4Mass_pair_of_phase_two_wf
            (L := L) (K := K) s' t' hs_phase ht_phase
            hs'_mcr ht'_mcr hs'_carrier ht'_carrier
            hs_small ht_small
    | 3, _ =>
        have hs_phase : s'.phase.val = 3 := by simpa [hsp]
        have ht_phase : t'.phase.val = 3 := by
          rw [← hphase_eq, hsp]
        simpa [hsp] using
          Phase3Transition_preserves_prePhase4Mass_pair_of_phase_three
            (L := L) (K := K) s' t' hs_phase ht_phase
    | 4, _ =>
        have hs_phase : s'.phase.val = 4 := by simpa [hsp]
        have ht_phase : t'.phase.val = 4 := by
          rw [← hphase_eq, hsp]
        simpa [hsp] using
          Phase4Transition_preserves_prePhase4Mass_pair_of_phase_four
            (L := L) (K := K) s' t' hs_phase ht_phase
    | 5, _ =>
        have hs_phase : s'.phase.val = 5 := by simpa [hsp]
        have hle : (Phase5Transition L K s' t').1.phase.val ≤ 4 := by
          simpa [hsp, out] using hout1_out
        have hge := (Phase5Transition_phase_nondec (L := L) (K := K) s' t').1
        omega
    | 6, _ =>
        have hs_phase : s'.phase.val = 6 := by simpa [hsp]
        have hle : (Phase6Transition L K s' t').1.phase.val ≤ 4 := by
          simpa [hsp, out] using hout1_out
        have hge := (Phase6Transition_phase_nondec (L := L) (K := K) s' t').1
        omega
    | 7, _ =>
        have hs_phase : s'.phase.val = 7 := by simpa [hsp]
        have hle : (Phase7Transition L K s' t').1.phase.val ≤ 4 := by
          simpa [hsp, out] using hout1_out
        have hge := (Phase7Transition_phase_nondec (L := L) (K := K) s' t').1
        omega
    | 8, _ =>
        have hs_phase : s'.phase.val = 8 := by simpa [hsp]
        have hle : (Phase8Transition L K s' t').1.phase.val ≤ 4 := by
          simpa [hsp, out] using hout1_out
        have hge := (Phase8Transition_phase_nondec (L := L) (K := K) s' t').1
        omega
    | 9, _ =>
        have hs_phase : s'.phase.val = 9 := by simpa [hsp]
        have hle : (Phase9Transition L K s' t').1.phase.val ≤ 4 := by
          simpa [hsp, out] using hout1_out
        have hge := (Phase9Transition_phase_nondec (L := L) (K := K) s' t').1
        omega
    | 10, _ =>
        have hs_phase : s'.phase.val = 10 := by simpa [hsp]
        have hle : (Phase10Transition L K s' t').1.phase.val ≤ 4 := by
          simpa [hsp, out] using hout1_out
        have hge := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').1
        omega
    | n + 11, hn => omega
  calc
    prePhase4Mass (finishPhase10Entry L K s' out.1) +
        prePhase4Mass (finishPhase10Entry L K t' out.2)
        = prePhase4Mass out.1 + prePhase4Mass out.2 := by
          simp [hfinish1, hfinish2]
    _ = prePhase4Mass s' + prePhase4Mass t' := hdispatch
    _ = prePhase4Mass s + prePhase4Mass t := by
          simpa [he] using hep_mass

theorem Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
    (s t : AgentState L K) :
    let ep := phaseEpidemicUpdate L K s t
    2 ≤ ep.1.phase.val →
    (Transition L K s t).1.smallBias = ep.1.smallBias := by
  dsimp
  intro hphase
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hphase
  dsimp
  change
    (finishPhase10Entry L K s'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1).smallBias = s'.smallBias
  have hs_ge : 2 ≤ s'.phase.val := by
    simpa using hphase
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    omega
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    omega
  · have hsmall := (Phase2Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase3Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase4Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase5Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase6Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase7Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase8Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase9Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase10Transition_preserves_smallBias L K s' t').1
    simpa [hp, finishPhase10Entry_smallBias, hsmall]

theorem Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
    (s t : AgentState L K) :
    let ep := phaseEpidemicUpdate L K s t
    2 ≤ ep.1.phase.val →
    (Transition L K s t).2.smallBias = ep.2.smallBias := by
  dsimp
  intro hphase
  unfold Transition
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hphase
  dsimp
  change
    (finishPhase10Entry L K t'
      (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2).smallBias = t'.smallBias
  have hs_ge : 2 ≤ s'.phase.val := by
    simpa using hphase
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    omega
  · have hpval : s'.phase.val = 1 := by simpa [hp]
    omega
  · have hsmall := (Phase2Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase3Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase4Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase5Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase6Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase7Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase8Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase9Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]
  · have hsmall := (Phase10Transition_preserves_smallBias L K s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hsmall]

/-! ### Clock-role preservation

The full protocol can change non-clock roles after Phase 0, for example a
Reserve may become Main in Phase 6.  The clock role itself is preserved by
every phase-specific transition in phases 1 through 10, by phase initialization,
and by the dispatcher once the interacting agents are already past Phase 0.
-/

@[simp] lemma advancePhase_role (a : AgentState L K) :
    (advancePhase L K a).role = a.role := by
  unfold advancePhase
  split <;> simp

@[simp] lemma stdCounterSubroutine_clock_role_eq
    (a : AgentState L K) (ha : a.role = .clock) :
    (stdCounterSubroutine L K a).role = .clock := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_clock_role_eq L K a ha
  · simp [ha]

@[simp] lemma clockCounterStep_role_eq (a : AgentState L K) :
    (clockCounterStep L K a).role = a.role := by
  unfold clockCounterStep
  by_cases h : a.role = .clock
  · simp [h]
  · simp [h]

@[simp] lemma finishPhase10Entry_role_eq (before after : AgentState L K) :
    (finishPhase10Entry L K before after).role = after.role := by
  simp [finishPhase10Entry]

theorem Phase1Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase1Transition L K s t).1.role = .clock := by
  simp [Phase1Transition, clockCounterStep, hs]

theorem Phase1Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase1Transition L K s t).2.role = .clock := by
  simp [Phase1Transition, clockCounterStep, ht]

theorem Phase2Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase2Transition L K s t).1.role = .clock := by
  unfold Phase2Transition
  dsimp
  split
  · simp [advancePhaseWithInit_clock_role_eq, hs]
  · split
    · simp [hs]
    · split
      · simp [hs]
      · split <;> simp [hs]

theorem Phase2Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase2Transition L K s t).2.role = .clock := by
  unfold Phase2Transition
  dsimp
  split
  · simp [advancePhaseWithInit_clock_role_eq, ht]
  · split
    · simp [ht]
    · split
      · simp [ht]
      · split <;> simp [ht]

theorem Phase3Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase3Transition L K s t).1.role = .clock := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have hs1 : s1.role = .clock := by
    dsimp [s1]
    split_ifs <;> simp [hs]
  have hs2 : s2.role = .clock := by
    dsimp [s2]
    split_ifs <;> simp_all
  change (if s2.role = .main ∧ t2.role = .main then
      phase3CancelSplit L K s2 t2 else (s2, t2)).1.role = .clock
  simp [hs2]

theorem Phase3Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase3Transition L K s t).2.role = .clock := by
  let s1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { s with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then
      { s with minute := ⟨s.minute.val + 1, by omega⟩ }
    else stdCounterSubroutine L K s
  else s
  let t1 := if s.role = .clock ∧ t.role = .clock then
    if s.minute ≠ t.minute then { t with minute := max s.minute t.minute }
    else if _h : s.minute.val < K * (L + 1) then t
    else stdCounterSubroutine L K t
  else t
  let s2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    let hVal := max s1.hour.val (min L (t1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨s1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := max t1.hour.val (min L (s1.minute.val / K))
    have h_hour_lt : hVal < L + 1 := by
      exact (Nat.max_lt).mpr
        ⟨t1.hour.2, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  have ht1 : t1.role = .clock := by
    dsimp [t1]
    split_ifs <;> simp [ht]
  have ht2 : t2.role = .clock := by
    dsimp [t2]
    split_ifs <;> simp_all
  change (if s2.role = .main ∧ t2.role = .main then
      phase3CancelSplit L K s2 t2 else (s2, t2)).2.role = .clock
  simp [ht2]

theorem Phase4Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase4Transition L K s t).1.role = .clock := by
  unfold Phase4Transition
  dsimp
  split <;> simp [hs]

theorem Phase4Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase4Transition L K s t).2.role = .clock := by
  unfold Phase4Transition
  dsimp
  split <;> simp [ht]

theorem Phase5Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase5Transition L K s t).1.role = .clock := by
  simp [Phase5Transition, hs]

theorem Phase5Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase5Transition L K s t).2.role = .clock := by
  simp [Phase5Transition, ht]

theorem Phase6Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase6Transition L K s t).1.role = .clock := by
  simp [Phase6Transition, hs]

theorem Phase6Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase6Transition L K s t).2.role = .clock := by
  simp [Phase6Transition, ht]

theorem Phase7Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase7Transition L K s t).1.role = .clock := by
  simp [Phase7Transition, hs]

theorem Phase7Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase7Transition L K s t).2.role = .clock := by
  simp [Phase7Transition, ht]

theorem Phase8Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase8Transition L K s t).1.role = .clock := by
  simp [Phase8Transition, hs]

theorem Phase8Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase8Transition L K s t).2.role = .clock := by
  simp [Phase8Transition, ht]

theorem Phase9Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase9Transition L K s t).1.role = .clock := by
  unfold Phase9Transition
  exact Phase2Transition_preserves_clock_role L K s t hs

theorem Phase9Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase9Transition L K s t).2.role = .clock := by
  unfold Phase9Transition
  exact Phase2Transition_second_preserves_clock_role L K s t ht

theorem Phase10Transition_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (Phase10Transition L K s t).1.role = .clock := by
  let s1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { s with output := .T }
      else if s.output = .T ∧ (t.output = .A ∨ t.output = .B) then
        { s with output := t.output, full := false }
      else s
    else s
  let t1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { t with output := .T }
      else if t.output = .T ∧ (s.output = .A ∨ s.output = .B) then
        { t with output := s.output, full := false }
      else t
    else t
  have hs1 : s1.role = .clock := by
    dsimp [s1]
    split_ifs <;> simp [hs]
  change (if s1.full ∧ ¬ t1.full then
      ({ s1 with output := s1.output }, { t1 with output := s1.output })
    else if ¬ s1.full ∧ t1.full then
      ({ s1 with output := t1.output }, { t1 with output := t1.output })
    else
      (s1, t1)).1.role = .clock
  split_ifs <;> simp [hs1]

theorem Phase10Transition_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (Phase10Transition L K s t).2.role = .clock := by
  let s1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { s with output := .T }
      else if s.output = .T ∧ (t.output = .A ∨ t.output = .B) then
        { s with output := t.output, full := false }
      else s
    else s
  let t1 :=
    if s.full ∧ t.full then
      if (s.output = .A ∧ t.output = .B) ∨ (s.output = .B ∧ t.output = .A) then
        { t with output := .T }
      else if t.output = .T ∧ (s.output = .A ∨ s.output = .B) then
        { t with output := s.output, full := false }
      else t
    else t
  have ht1 : t1.role = .clock := by
    dsimp [t1]
    split_ifs <;> simp [ht]
  change (if s1.full ∧ ¬ t1.full then
      ({ s1 with output := s1.output }, { t1 with output := s1.output })
    else if ¬ s1.full ∧ t1.full then
      ({ s1 with output := t1.output }, { t1 with output := t1.output })
    else
      (s1, t1)).2.role = .clock
  split_ifs <;> simp [ht1]

theorem phaseInit_preserves_clock_role
    (p : Fin 11) (a : AgentState L K) (ha : a.role = .clock) :
    (phaseInit L K p a).role = .clock := by
  fin_cases p <;> unfold phaseInit <;> simp [ha] <;>
    split_ifs <;> simp [ha]

private lemma phaseInit_phase_nondec_for_clock_role
    (p : Fin 11) (a : AgentState L K) :
    a.phase.val ≤ (phaseInit L K p a).phase.val := by
  have h_le_10 : a.phase.val ≤ 10 := by
    have := a.phase.2
    omega
  rcases p with ⟨n, hn⟩
  match n, hn with
  | 0, _ => unfold phaseInit; simp
  | 1, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 2, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 3, _ =>
    unfold phaseInit; simp
    cases a.role <;> exact le_refl _
  | 4, _ => unfold phaseInit; simp
  | 5, _ =>
    unfold phaseInit; simp
    split_ifs <;> exact le_refl _
  | 6, _ =>
    unfold phaseInit; simp
    split_ifs <;> exact le_refl _
  | 7, _ =>
    unfold phaseInit; simp
    split_ifs <;> exact le_refl _
  | 8, _ => unfold phaseInit; simp
  | 9, _ =>
    unfold phaseInit; simp
    split_ifs <;> first | exact h_le_10 | exact le_refl _
  | 10, _ =>
    unfold phaseInit
    simp [phase10]
    exact h_le_10
  | n + 11, _ => omega

theorem runInitsBetween_preserves_clock_role
    (oldP newP : ℕ) (a : AgentState L K) (ha : a.role = .clock) :
    (runInitsBetween L K oldP newP a).role = .clock := by
  unfold runInitsBetween
  have h_fold : ∀ (lst : List ℕ) (a' : AgentState L K),
      a'.role = .clock →
      (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a').role = .clock := by
    intro lst
    induction lst with
    | nil =>
        intro a' ha'
        exact ha'
    | cons k ks ih =>
        intro a' ha'
        simp [List.foldl]
        by_cases hk : k < 11
        · simpa [hk] using ih (phaseInit L K ⟨k, hk⟩ a')
            (phaseInit_preserves_clock_role L K ⟨k, hk⟩ a' ha')
        · simpa [hk] using ih a' ha'
  exact h_fold ((List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)) a ha

private lemma runInitsBetween_phase_nondec_for_clock_role
    (oldP newP : ℕ) (a : AgentState L K) :
    a.phase.val ≤ (runInitsBetween L K oldP newP a).phase.val := by
  unfold runInitsBetween
  let lst := (List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)
  have h_ind : ∀ (a' : AgentState L K), a'.phase.val ≤
      (lst.foldl (fun (acc : AgentState L K) (k : ℕ) =>
        if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a').phase.val := by
    induction lst with
    | nil => exact fun a' => le_refl _
    | cons k l ih =>
      intro a'
      simp [List.foldl]
      by_cases hk : k < 11
      · simp [hk]
        have h1 : a'.phase.val ≤ (phaseInit L K ⟨k, hk⟩ a').phase.val :=
          phaseInit_phase_nondec_for_clock_role L K ⟨k, hk⟩ a'
        have h2 : (phaseInit L K ⟨k, hk⟩ a').phase.val ≤
            (l.foldl (fun (acc : AgentState L K) (k : ℕ) =>
              if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc)
              (phaseInit L K ⟨k, hk⟩ a')).phase.val :=
          ih (phaseInit L K ⟨k, hk⟩ a')
        exact le_trans h1 h2
      · simp [hk]
        exact ih a'
  exact h_ind a

theorem phaseEpidemicUpdate_first_preserves_clock_role
    (s t : AgentState L K) (hs : s.role = .clock) :
    (phaseEpidemicUpdate L K s t).1.role = .clock := by
  unfold phaseEpidemicUpdate
  dsimp
  let p := max s.phase t.phase
  let s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  let t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hs0_clock : s0.role = .clock := by
    dsimp [s0, p]
    exact runInitsBetween_preserves_clock_role L K s.phase.val
      (max s.phase.val t.phase.val) ({ s with phase := max s.phase t.phase })
      (by simpa using hs)
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else
      (s0, t0)).1.role = .clock
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · simp [h10, hs0_clock]
  · simp [h10, hs0_clock]

theorem phaseEpidemicUpdate_second_preserves_clock_role
    (s t : AgentState L K) (ht : t.role = .clock) :
    (phaseEpidemicUpdate L K s t).2.role = .clock := by
  unfold phaseEpidemicUpdate
  dsimp
  let p := max s.phase t.phase
  let s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  let t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have ht0_clock : t0.role = .clock := by
    dsimp [t0, p]
    exact runInitsBetween_preserves_clock_role L K t.phase.val
      (max s.phase.val t.phase.val) ({ t with phase := max s.phase t.phase })
      (by simpa using ht)
  change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else
      (s0, t0)).2.role = .clock
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · simp [h10, ht0_clock]
  · simp [h10, ht0_clock]

private lemma phaseEpidemicUpdate_first_phase_ge_of_left_phase_ge
    (s t : AgentState L K) (hs : 1 ≤ s.phase.val) :
    1 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
  unfold phaseEpidemicUpdate
  dsimp
  let p := max s.phase t.phase
  let s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  let t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have hs0_ge : 1 ≤ s0.phase.val := by
    dsimp [s0, p]
    have hmax : s.phase.val ≤ (max s.phase t.phase).val := by
      simp
    exact le_trans hs (le_trans hmax
      (runInitsBetween_phase_nondec_for_clock_role L K s.phase.val
        (max s.phase.val t.phase.val) ({ s with phase := max s.phase t.phase })))
  change 1 ≤ (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else
      (s0, t0)).1.phase.val
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · by_cases hslt : s.phase.val < 10
    · simp [h10, phase10EpidemicEntry, hslt, phase10]
    · by_cases htlt : t.phase.val < 10
      · simp [h10, phase10EpidemicEntry, hslt, htlt, hs0_ge]
      · simp [h10, phase10EpidemicEntry, hslt, htlt, hs0_ge]
  · simp [h10, hs0_ge]

private lemma phaseEpidemicUpdate_second_phase_ge_of_right_phase_ge
    (s t : AgentState L K) (ht : 1 ≤ t.phase.val) :
    1 ≤ (phaseEpidemicUpdate L K s t).2.phase.val := by
  unfold phaseEpidemicUpdate
  dsimp
  let p := max s.phase t.phase
  let s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  let t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  have ht0_ge : 1 ≤ t0.phase.val := by
    dsimp [t0, p]
    have hmax : t.phase.val ≤ (max s.phase t.phase).val := by
      simp
    exact le_trans ht (le_trans hmax
      (runInitsBetween_phase_nondec_for_clock_role L K t.phase.val
        (max s.phase.val t.phase.val) ({ t with phase := max s.phase t.phase })))
  change 1 ≤ (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10) then
      (phase10EpidemicEntry L K s s0, phase10EpidemicEntry L K t t0)
    else
      (s0, t0)).2.phase.val
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · by_cases hslt : s.phase.val < 10
    · by_cases htlt : t.phase.val < 10
      · simp [h10, phase10EpidemicEntry, hslt, htlt, phase10]
      · simp [h10, phase10EpidemicEntry, hslt, htlt, ht0_ge]
    · by_cases htlt : t.phase.val < 10
      · simp [h10, phase10EpidemicEntry, hslt, htlt, phase10]
      · simp [h10, phase10EpidemicEntry, hslt, htlt, ht0_ge]
  · simp [h10, ht0_ge]

theorem Transition_preserves_clock_role_of_phase_ge_1
    (a b : AgentState L K) (ha : 1 ≤ a.phase.val) (_hb : 1 ≤ b.phase.val)
    (ha_clock : a.role = .clock) :
    (Transition L K a b).1.role = .clock := by
  unfold Transition
  generalize he : phaseEpidemicUpdate L K a b = e
  rcases e with ⟨a', b'⟩
  have ha'_clock : a'.role = .clock := by
    simpa [he] using phaseEpidemicUpdate_first_preserves_clock_role
      (L := L) (K := K) a b ha_clock
  have ha'_ge : 1 ≤ a'.phase.val := by
    simpa [he] using phaseEpidemicUpdate_first_phase_ge_of_left_phase_ge
      (L := L) (K := K) a b ha
  change (finishPhase10Entry L K a'
    (match a'.phase with
    | ⟨0, _⟩ => Phase0Transition L K a' b'
    | ⟨1, _⟩ => Phase1Transition L K a' b'
    | ⟨2, _⟩ => Phase2Transition L K a' b'
    | ⟨3, _⟩ => Phase3Transition L K a' b'
    | ⟨4, _⟩ => Phase4Transition L K a' b'
    | ⟨5, _⟩ => Phase5Transition L K a' b'
    | ⟨6, _⟩ => Phase6Transition L K a' b'
    | ⟨7, _⟩ => Phase7Transition L K a' b'
    | ⟨8, _⟩ => Phase8Transition L K a' b'
    | ⟨9, _⟩ => Phase9Transition L K a' b'
    | ⟨10, _⟩ => Phase10Transition L K a' b'
    | _ => (a', b')).1).role = .clock
  generalize hphase : a'.phase = p
  fin_cases p <;>
    simp at ha'_ge ⊢
  · have hp0 : a'.phase.val = 0 := by
      simpa using congrArg Fin.val hphase
    omega
  · simpa [ha'_clock] using
      Phase1Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase2Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase3Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase4Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase5Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase6Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase7Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase8Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase9Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock
  · simpa [ha'_clock] using
      Phase10Transition_preserves_clock_role (L := L) (K := K) a' b' ha'_clock

theorem Transition_second_preserves_clock_role_of_phase_ge_1
    (a b : AgentState L K) (ha : 1 ≤ a.phase.val) (hb : 1 ≤ b.phase.val)
    (hb_clock : b.role = .clock) :
    (Transition L K a b).2.role = .clock := by
  unfold Transition
  generalize he : phaseEpidemicUpdate L K a b = e
  rcases e with ⟨a', b'⟩
  have hb'_clock : b'.role = .clock := by
    simpa [he] using phaseEpidemicUpdate_second_preserves_clock_role
      (L := L) (K := K) a b hb_clock
  have hb'_ge : 1 ≤ b'.phase.val := by
    simpa [he] using phaseEpidemicUpdate_second_phase_ge_of_right_phase_ge
      (L := L) (K := K) a b hb
  have ha'_ge : 1 ≤ a'.phase.val := by
    simpa [he] using phaseEpidemicUpdate_first_phase_ge_of_left_phase_ge
      (L := L) (K := K) a b ha
  change (finishPhase10Entry L K b'
    (match a'.phase with
    | ⟨0, _⟩ => Phase0Transition L K a' b'
    | ⟨1, _⟩ => Phase1Transition L K a' b'
    | ⟨2, _⟩ => Phase2Transition L K a' b'
    | ⟨3, _⟩ => Phase3Transition L K a' b'
    | ⟨4, _⟩ => Phase4Transition L K a' b'
    | ⟨5, _⟩ => Phase5Transition L K a' b'
    | ⟨6, _⟩ => Phase6Transition L K a' b'
    | ⟨7, _⟩ => Phase7Transition L K a' b'
    | ⟨8, _⟩ => Phase8Transition L K a' b'
    | ⟨9, _⟩ => Phase9Transition L K a' b'
    | ⟨10, _⟩ => Phase10Transition L K a' b'
    | _ => (a', b')).2).role = .clock
  generalize hphase : a'.phase = p
  fin_cases p <;> simp at ⊢
  · have ha0 : a'.phase.val = 0 := by
      simpa using congrArg Fin.val hphase
    omega
  · simpa [hb'_clock] using
      Phase1Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase2Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase3Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase4Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase5Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase6Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase7Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase8Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase9Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock
  · simpa [hb'_clock] using
      Phase10Transition_second_preserves_clock_role (L := L) (K := K) a' b' hb'_clock

private lemma phaseInit_phase_eq_or_ten (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).phase.val = a.phase.val ∨
    (phaseInit L K p a).phase.val = 10 := by
  rcases p with ⟨n, hn⟩
  match n, hn with
  | 0, _ => left; unfold phaseInit; simp
  | 1, _ =>
    unfold phaseInit; simp
    split_ifs
    · right; simp [enterPhase10]
    · left; rfl
    · left; rfl
    · left; rfl
  | 2, _ =>
    unfold phaseInit; simp
    split_ifs
    · right; simp [enterPhase10]
    · left; rfl
    · left; rfl
    · left; rfl
  | 3, _ =>
    unfold phaseInit; simp
    cases a.role <;> left <;> rfl
  | 4, _ => left; unfold phaseInit; simp
  | 5, _ =>
    unfold phaseInit; simp
    split_ifs <;> left <;> rfl
  | 6, _ =>
    unfold phaseInit; simp
    split_ifs <;> left <;> rfl
  | 7, _ =>
    unfold phaseInit; simp
    split_ifs <;> left <;> rfl
  | 8, _ => left; unfold phaseInit; simp
  | 9, _ =>
    unfold phaseInit; simp
    split_ifs
    · right; simp [enterPhase10]
    · left; rfl
    · left; rfl
    · left; rfl
  | 10, _ => right; unfold phaseInit; simp [enterPhase10]
  | n + 11, _ => omega

private lemma clockCounterStep_phase_le_succ_or_ten (a : AgentState L K) :
    (clockCounterStep L K a).phase.val ≤ a.phase.val + 1 ∨
    (clockCounterStep L K a).phase.val = 10 := by
  simp only [clockCounterStep]
  split_ifs with hclock
  · simp only [stdCounterSubroutine]
    split_ifs with hctr
    · simp only [advancePhaseWithInit]
      have hadv : (advancePhase L K a).phase.val = a.phase.val + 1 ∨
          a.phase.val = 10 := by
        simp only [advancePhase]
        split_ifs with hlt
        · left; simp
        · right; have := a.phase.2; omega
      rcases hadv with hadv | hadv
      · have hpi_or := phaseInit_phase_eq_or_ten L K (advancePhase L K a).phase (advancePhase L K a)
        rcases hpi_or with hpi_eq | hpi_ten
        · left; rw [hpi_eq, hadv]
        · right; exact hpi_ten
      · left; have := a.phase.2; omega
    · exact Or.inl (Nat.le_succ _)
  · exact Or.inl (Nat.le_succ _)

set_option maxHeartbeats 800000 in
theorem Transition_left_phase_le_two_of_epidemic_phase_lt_two
    (s t : AgentState L K)
    (hepi_lt2 : (phaseEpidemicUpdate L K s t).1.phase.val < 2)
    (hout_le4 : (Transition L K s t).1.phase.val ≤ 4) :
    (Transition L K s t).1.phase.val ≤ 2 := by
  unfold Transition at hout_le4 ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hout_le4 ⊢
  rcases e with ⟨s', t'⟩
  have hs'_lt2 : s'.phase.val < 2 := by simpa [he] using hepi_lt2
  rcases hsp : s'.phase with ⟨n, hn⟩
  simp only [hsp] at hs'_lt2
  have hs'_val : s'.phase.val = n := by rw [hsp]
  interval_cases n
  · -- Phase 0: Phase0Transition then finishPhase10Entry.
    -- Phase0Transition output.1 has phase ≤ s'.phase + 1 = 1 or = 10.
    -- finishPhase10Entry either keeps or sets 10.
    -- With overall output ≤ 4: phase ≤ 1 ≤ 2.
    simp only [hsp] at hout_le4 ⊢
    simp only [finishPhase10Entry_phase_val] at hout_le4 ⊢
    let s1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { s' with role := .main, smallBias := addSmallBias s'.smallBias t'.smallBias } else s'
    let t1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { t' with role := .cr, smallBias := ⟨3, by decide⟩ } else t'
    let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
      else s1
    let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else t1
    let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { s2 with role := .main }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { s2 with assigned := true } else s2
    let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { t2 with assigned := true }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { t2 with role := .main }
      else t2
    let s3' := s3
    let t3' := t3
    let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
    let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { t3' with role := .reserve } else t3'
    let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
    let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
    have hs1 : s'.phase.val = s1.phase.val := by dsimp [s1]; split_ifs <;> rfl
    have hs2 : s1.phase.val = s2.phase.val := by dsimp [s2]; split_ifs <;> rfl
    have hs3 : s2.phase.val = s3.phase.val := by dsimp [s3]; split_ifs <;> rfl
    have hs3' : s3.phase.val = s3'.phase.val := by dsimp [s3']
    have hs4 : s3'.phase.val = s4.phase.val := by dsimp [s4]; split_ifs <;> rfl
    have hs4_eq : s4.phase.val = 0 := by
      rw [← hs4, ← hs3', ← hs3, ← hs2, ← hs1]; simp [hsp]
    change s5.phase.val ≤ 2
    change s5.phase.val ≤ 4 at hout_le4
    have hs5_bound : s5.phase.val ≤ 1 ∨ s5.phase.val = 10 := by
      dsimp [s5]; split_ifs with hclock
      · have hrole : s4.role = .clock := hclock.1
        have hccs := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K) s4
        have hccs_eq : clockCounterStep L K s4 = stdCounterSubroutine L K s4 := by
          unfold clockCounterStep; simp [hrole]
        rw [hccs_eq] at hccs
        rcases hccs with hle | heq10
        · left; omega
        · right; exact heq10
      · left; omega
    rcases hs5_bound with hle | heq10
    · omega
    · omega
  · -- Phase 1: Phase1Transition = avg + clockCounterStep.
    simp only [hsp] at hout_le4 ⊢
    have hccs1 := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K)
    simp only [finishPhase10Entry_phase_val] at hout_le4 ⊢
    by_cases hmain : s'.role = .main ∧ t'.role = .main
    · have hkey : (Phase1Transition L K s' t').1.phase.val =
          (clockCounterStep L K
            ({ s' with smallBias := (avgFin7 s'.smallBias t'.smallBias).1 })).phase.val := by
        simp [Phase1Transition, hmain]
      have hphase_eq : ({ s' with smallBias := (avgFin7 s'.smallBias t'.smallBias).1 } :
          AgentState L K).phase.val = s'.phase.val := rfl
      rcases hccs1 ({ s' with smallBias := (avgFin7 s'.smallBias t'.smallBias).1 } :
          AgentState L K) with hle | heq10
      · rw [hphase_eq] at hle; omega
      · rw [hkey] at hout_le4; omega
    · have hkey : (Phase1Transition L K s' t').1.phase.val =
          (clockCounterStep L K s').phase.val := by
        simp [Phase1Transition, hmain]
      rcases hccs1 s' with hle | heq10
      · omega
      · rw [hkey] at hout_le4; omega
  all_goals omega

set_option maxHeartbeats 800000 in
theorem Transition_right_phase_le_two_of_epidemic_phase_lt_two
    (s t : AgentState L K)
    (hepi_lt2 : (phaseEpidemicUpdate L K s t).1.phase.val < 2)
    (hout_le4 : (Transition L K s t).2.phase.val ≤ 4) :
    (Transition L K s t).2.phase.val ≤ 2 := by
  unfold Transition at hout_le4 ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hout_le4 ⊢
  rcases e with ⟨s', t'⟩
  have hs'_lt2 : s'.phase.val < 2 := by simpa [he] using hepi_lt2
  rcases hsp : s'.phase with ⟨n, hn⟩
  simp only [hsp] at hs'_lt2
  have hs'_val : s'.phase.val = n := by rw [hsp]
  interval_cases n
  · simp only [hsp] at hout_le4 ⊢
    simp only [finishPhase10Entry_phase_val] at hout_le4 ⊢
    have ht'_le4 : t'.phase.val ≤ 4 :=
      le_trans (Phase0Transition_phase_nondec L K s' t').2 hout_le4
    have hmax_le : max s.phase.val t.phase.val ≤ 1 := by
      have := phaseEpidemicUpdate_left_phase_ge_max_api L K s t
      simp [he] at this; omega
    have hphases_eq := phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
      L K s t (by omega) (by omega) (by simp [he]; omega) (by simp [he]; omega)
    simp [he] at hphases_eq
    have ht'_lt2 : t'.phase.val < 2 := by omega
    let s1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { s' with role := .main, smallBias := addSmallBias s'.smallBias t'.smallBias } else s'
    let t1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { t' with role := .cr, smallBias := ⟨3, by decide⟩ } else t'
    let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
      else s1
    let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else t1
    let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { s2 with role := .main }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { s2 with assigned := true } else s2
    let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { t2 with assigned := true }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { t2 with role := .main }
      else t2
    let s3' := s3
    let t3' := t3
    let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
    let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { t3' with role := .reserve } else t3'
    let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
    let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
    have ht1 : t'.phase.val = t1.phase.val := by dsimp [t1]; split_ifs <;> rfl
    have ht2 : t1.phase.val = t2.phase.val := by dsimp [t2]; split_ifs <;> rfl
    have ht3 : t2.phase.val = t3.phase.val := by dsimp [t3]; split_ifs <;> rfl
    have ht3' : t3.phase.val = t3'.phase.val := by dsimp [t3']
    have ht4 : t3'.phase.val = t4.phase.val := by dsimp [t4]; split_ifs <;> rfl
    have ht4_lt2 : t4.phase.val < 2 := by
      rw [← ht4, ← ht3', ← ht3, ← ht2, ← ht1]; exact ht'_lt2
    change t5.phase.val ≤ 2
    change t5.phase.val ≤ 4 at hout_le4
    have ht5_bound : t5.phase.val ≤ t4.phase.val + 1 ∨ t5.phase.val = 10 := by
      dsimp [t5]; split_ifs with hclock
      · have hrole : t4.role = .clock := hclock.2
        have hccs := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K) t4
        have hccs_eq : clockCounterStep L K t4 = stdCounterSubroutine L K t4 := by
          unfold clockCounterStep; simp [hrole]
        rw [hccs_eq] at hccs; exact hccs
      · left; omega
    rcases ht5_bound with hle | heq10
    · omega
    · omega
  · simp only [hsp] at hout_le4 ⊢
    simp only [finishPhase10Entry_phase_val] at hout_le4 ⊢
    have ht'_le4 : t'.phase.val ≤ 4 :=
      le_trans (Phase1Transition_phase_nondec L K s' t').2 hout_le4
    have hmax_le : max s.phase.val t.phase.val ≤ 1 := by
      have := phaseEpidemicUpdate_left_phase_ge_max_api L K s t
      simp [he] at this; omega
    have hphases_eq := phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
      L K s t (by omega) (by omega) (by simp [he]; omega) (by simp [he]; omega)
    simp [he] at hphases_eq
    have ht'_lt2 : t'.phase.val < 2 := by omega
    have hccs := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K)
    by_cases hmain : s'.role = .main ∧ t'.role = .main
    · have hkey : (Phase1Transition L K s' t').2.phase.val =
          (clockCounterStep L K
            ({ t' with smallBias := (avgFin7 s'.smallBias t'.smallBias).2 })).phase.val := by
        simp [Phase1Transition, hmain]
      have hphase_eq : ({ t' with smallBias := (avgFin7 s'.smallBias t'.smallBias).2 } :
          AgentState L K).phase.val = t'.phase.val := rfl
      rcases hccs ({ t' with smallBias := (avgFin7 s'.smallBias t'.smallBias).2 } :
          AgentState L K) with hle | heq10
      · rw [hphase_eq] at hle; omega
      · rw [hkey] at hout_le4; omega
    · have hkey : (Phase1Transition L K s' t').2.phase.val =
          (clockCounterStep L K t').phase.val := by
        simp [Phase1Transition, hmain]
      rcases hccs t' with hle | heq10
      · omega
      · rw [hkey] at hout_le4; omega
  all_goals omega

set_option maxHeartbeats 800000 in
/-- Variant of `Transition_left_phase_le_two_of_epidemic_phase_lt_two` accepting
the weaker hypothesis `output.phase ≠ 10` (sufficient to rule out the Phase-10
entry branch).  Useful when only the upper bound `≤ 9` is known. -/
theorem Transition_left_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (s t : AgentState L K)
    (hepi_lt2 : (phaseEpidemicUpdate L K s t).1.phase.val < 2)
    (hout_ne10 : (Transition L K s t).1.phase.val ≠ 10) :
    (Transition L K s t).1.phase.val ≤ 2 := by
  unfold Transition at hout_ne10 ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hout_ne10 ⊢
  rcases e with ⟨s', t'⟩
  have hs'_lt2 : s'.phase.val < 2 := by simpa [he] using hepi_lt2
  rcases hsp : s'.phase with ⟨n, hn⟩
  simp only [hsp] at hs'_lt2
  have hs'_val : s'.phase.val = n := by rw [hsp]
  interval_cases n
  · simp only [hsp] at hout_ne10 ⊢
    simp only [finishPhase10Entry_phase_val] at hout_ne10 ⊢
    let s1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { s' with role := .main, smallBias := addSmallBias s'.smallBias t'.smallBias } else s'
    let t1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { t' with role := .cr, smallBias := ⟨3, by decide⟩ } else t'
    let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
      else s1
    let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else t1
    let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { s2 with role := .main }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { s2 with assigned := true } else s2
    let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { t2 with assigned := true }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { t2 with role := .main }
      else t2
    let s3' := s3
    let t3' := t3
    let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
    let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { t3' with role := .reserve } else t3'
    let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
    let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
    have hs1 : s'.phase.val = s1.phase.val := by dsimp [s1]; split_ifs <;> rfl
    have hs2 : s1.phase.val = s2.phase.val := by dsimp [s2]; split_ifs <;> rfl
    have hs3 : s2.phase.val = s3.phase.val := by dsimp [s3]; split_ifs <;> rfl
    have hs3' : s3.phase.val = s3'.phase.val := by dsimp [s3']
    have hs4 : s3'.phase.val = s4.phase.val := by dsimp [s4]; split_ifs <;> rfl
    have hs4_eq : s4.phase.val = 0 := by
      rw [← hs4, ← hs3', ← hs3, ← hs2, ← hs1]; simp [hsp]
    change s5.phase.val ≤ 2
    change s5.phase.val ≠ 10 at hout_ne10
    have hs5_bound : s5.phase.val ≤ 1 ∨ s5.phase.val = 10 := by
      dsimp [s5]; split_ifs with hclock
      · have hrole : s4.role = .clock := hclock.1
        have hccs := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K) s4
        have hccs_eq : clockCounterStep L K s4 = stdCounterSubroutine L K s4 := by
          unfold clockCounterStep; simp [hrole]
        rw [hccs_eq] at hccs
        rcases hccs with hle | heq10
        · left; omega
        · right; exact heq10
      · left; omega
    rcases hs5_bound with hle | heq10
    · omega
    · exact absurd heq10 hout_ne10
  · simp only [hsp] at hout_ne10 ⊢
    have hccs1 := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K)
    simp only [finishPhase10Entry_phase_val] at hout_ne10 ⊢
    by_cases hmain : s'.role = .main ∧ t'.role = .main
    · have hkey : (Phase1Transition L K s' t').1.phase.val =
          (clockCounterStep L K
            ({ s' with smallBias := (avgFin7 s'.smallBias t'.smallBias).1 })).phase.val := by
        simp [Phase1Transition, hmain]
      have hphase_eq : ({ s' with smallBias := (avgFin7 s'.smallBias t'.smallBias).1 } :
          AgentState L K).phase.val = s'.phase.val := rfl
      rcases hccs1 ({ s' with smallBias := (avgFin7 s'.smallBias t'.smallBias).1 } :
          AgentState L K) with hle | heq10
      · rw [hphase_eq] at hle; omega
      · rw [hkey] at hout_ne10; exact absurd heq10 hout_ne10
    · have hkey : (Phase1Transition L K s' t').1.phase.val =
          (clockCounterStep L K s').phase.val := by
        simp [Phase1Transition, hmain]
      rcases hccs1 s' with hle | heq10
      · omega
      · rw [hkey] at hout_ne10; exact absurd heq10 hout_ne10
  all_goals omega

set_option maxHeartbeats 800000 in
theorem Transition_right_phase_le_two_of_epidemic_phase_lt_two_of_ne_ten
    (s t : AgentState L K)
    (hepi_lt2 : (phaseEpidemicUpdate L K s t).1.phase.val < 2)
    (hout_ne10 : (Transition L K s t).2.phase.val ≠ 10) :
    (Transition L K s t).2.phase.val ≤ 2 := by
  -- Derive epidemic.2.phase ≠ 10 from hout_ne10 via the monotonicity
  -- phaseEpidemicUpdate_phase_le_Transition_phase.
  have hep_le_T :=
    (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).2
  have hep2_ne10 : (phaseEpidemicUpdate L K s t).2.phase.val ≠ 10 := by
    intro hep2_eq
    apply hout_ne10
    have : (Transition L K s t).2.phase.val ≥ 10 := by
      rw [← hep2_eq]; exact hep_le_T
    have hub : (Transition L K s t).2.phase.val < 11 :=
      (Transition L K s t).2.phase.isLt
    omega
  unfold Transition at hout_ne10 ⊢
  generalize he : phaseEpidemicUpdate L K s t = e at hout_ne10 hep2_ne10 ⊢
  rcases e with ⟨s', t'⟩
  have hs'_lt2 : s'.phase.val < 2 := by simpa [he] using hepi_lt2
  have ht'_ne10 : t'.phase.val ≠ 10 := by simpa [he] using hep2_ne10
  have hs'_ne10 : s'.phase.val ≠ 10 := by omega
  rcases hsp : s'.phase with ⟨n, hn⟩
  simp only [hsp] at hs'_lt2
  have hs'_val : s'.phase.val = n := by rw [hsp]
  interval_cases n
  · simp only [hsp] at hout_ne10 ⊢
    simp only [finishPhase10Entry_phase_val] at hout_ne10 ⊢
    have hmax_le : max s.phase.val t.phase.val ≤ 1 := by
      have := phaseEpidemicUpdate_left_phase_ge_max_api L K s t
      simp [he] at this; omega
    have hphases_eq := phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
      L K s t (by omega) (by omega) (by simpa [he] using hs'_ne10)
      (by simpa [he] using ht'_ne10)
    simp [he] at hphases_eq
    have ht'_lt2 : t'.phase.val < 2 := by omega
    let s1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { s' with role := .main, smallBias := addSmallBias s'.smallBias t'.smallBias } else s'
    let t1 := if s'.role = .mcr ∧ t'.role = .mcr then
      { t' with role := .cr, smallBias := ⟨3, by decide⟩ } else t'
    let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
      else s1
    let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
      { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
      else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
      { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
      else t1
    let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { s2 with role := .main }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { s2 with assigned := true } else s2
    let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
      { t2 with assigned := true }
      else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
      { t2 with role := .main }
      else t2
    let s3' := s3
    let t3' := t3
    let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
    let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
      { t3' with role := .reserve } else t3'
    let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
    let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
    have ht1 : t'.phase.val = t1.phase.val := by dsimp [t1]; split_ifs <;> rfl
    have ht2 : t1.phase.val = t2.phase.val := by dsimp [t2]; split_ifs <;> rfl
    have ht3 : t2.phase.val = t3.phase.val := by dsimp [t3]; split_ifs <;> rfl
    have ht3' : t3.phase.val = t3'.phase.val := by dsimp [t3']
    have ht4 : t3'.phase.val = t4.phase.val := by dsimp [t4]; split_ifs <;> rfl
    have ht4_lt2 : t4.phase.val < 2 := by
      rw [← ht4, ← ht3', ← ht3, ← ht2, ← ht1]; exact ht'_lt2
    change t5.phase.val ≤ 2
    change t5.phase.val ≠ 10 at hout_ne10
    have ht5_bound : t5.phase.val ≤ t4.phase.val + 1 ∨ t5.phase.val = 10 := by
      dsimp [t5]; split_ifs with hclock
      · have hrole : t4.role = .clock := hclock.2
        have hccs := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K) t4
        have hccs_eq : clockCounterStep L K t4 = stdCounterSubroutine L K t4 := by
          unfold clockCounterStep; simp [hrole]
        rw [hccs_eq] at hccs; exact hccs
      · left; omega
    rcases ht5_bound with hle | heq10
    · omega
    · exact absurd heq10 hout_ne10
  · simp only [hsp] at hout_ne10 ⊢
    simp only [finishPhase10Entry_phase_val] at hout_ne10 ⊢
    have hmax_le : max s.phase.val t.phase.val ≤ 1 := by
      have := phaseEpidemicUpdate_left_phase_ge_max_api L K s t
      simp [he] at this; omega
    have hphases_eq := phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
      L K s t (by omega) (by omega) (by simpa [he] using hs'_ne10)
      (by simpa [he] using ht'_ne10)
    simp [he] at hphases_eq
    have ht'_lt2 : t'.phase.val < 2 := by omega
    have hccs := clockCounterStep_phase_le_succ_or_ten (L := L) (K := K)
    by_cases hmain : s'.role = .main ∧ t'.role = .main
    · have hkey : (Phase1Transition L K s' t').2.phase.val =
          (clockCounterStep L K
            ({ t' with smallBias := (avgFin7 s'.smallBias t'.smallBias).2 })).phase.val := by
        simp [Phase1Transition, hmain]
      have hphase_eq : ({ t' with smallBias := (avgFin7 s'.smallBias t'.smallBias).2 } :
          AgentState L K).phase.val = t'.phase.val := rfl
      rcases hccs ({ t' with smallBias := (avgFin7 s'.smallBias t'.smallBias).2 } :
          AgentState L K) with hle | heq10
      · rw [hphase_eq] at hle; omega
      · rw [hkey] at hout_ne10; exact absurd heq10 hout_ne10
    · have hkey : (Phase1Transition L K s' t').2.phase.val =
          (clockCounterStep L K t').phase.val := by
        simp [Phase1Transition, hmain]
      rcases hccs t' with hle | heq10
      · omega
      · rw [hkey] at hout_ne10; exact absurd heq10 hout_ne10
  all_goals omega

/-- Convenience: from `s.phase ≥ 2`, the left output of `Transition` preserves
the input `smallBias`.  Derived from `Transition_preserves_epidemic_smallBias_left
_of_phase_ge_two` plus the smallBias-preservation of `phaseEpidemicUpdate`. -/
theorem Transition_left_preserves_smallBias_of_phase_ge_two
    (s t : AgentState L K) (hs : 2 ≤ s.phase.val) :
    (Transition L K s t).1.smallBias = s.smallBias := by
  have hep_ge : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
    have hmax := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    omega
  have hep_eq := Transition_preserves_epidemic_smallBias_left_of_phase_ge_two
    (L := L) (K := K) s t hep_ge
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).1
  rw [hep_eq, hsmall]

/-- Convenience: from `t.phase ≥ 2`, the right output of `Transition` preserves
the input `smallBias`. -/
theorem Transition_right_preserves_smallBias_of_phase_ge_two
    (s t : AgentState L K) (ht : 2 ≤ t.phase.val) :
    (Transition L K s t).2.smallBias = t.smallBias := by
  have hep_ge : 2 ≤ (phaseEpidemicUpdate L K s t).1.phase.val := by
    have hmax := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    omega
  have hep_eq := Transition_preserves_epidemic_smallBias_right_of_dispatch_phase_ge_two
    (L := L) (K := K) s t hep_ge
  have hsmall := (phaseEpidemicUpdate_preserves_smallBias L K s t).2
  rw [hep_eq, hsmall]

/-- Helper: when the clock-counter step lifts an agent from phase 1 to phase 2
without error, the resulting `smallBias` is in `{2,3,4}` (noerror set). -/
private theorem clockCounterStep_phase2_smallBias_noerror_pub
    (a : AgentState L K)
    (hphase : a.phase.val = 1)
    (hout : (clockCounterStep L K a).phase.val = 2) :
    (clockCounterStep L K a).smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  have hphase_eq : phase = ⟨1, by decide⟩ := Fin.ext hphase
  subst phase
  cases role
  · simp [clockCounterStep] at hout
  · simp [clockCounterStep] at hout
  · by_cases hcounter : counter.val = 0
    · let a2 : AgentState L K :=
        { input := input, output := output, phase := ⟨2, by decide⟩,
          role := Role.clock, assigned := assigned, bias := bias,
          smallBias := smallBias, hour := hour, minute := minute,
          full := full, opinions := opinions, counter := counter }
      have hinit_phase : (phaseInit L K ⟨2, by decide⟩ a2).phase.val = 2 := by
        simpa [a2, clockCounterStep, stdCounterSubroutine, advancePhaseWithInit,
          advancePhase, hcounter] using hout
      have hno := phaseInit_two_smallBias_noerror (L := L) (K := K) a2 hinit_phase
      simpa [a2, clockCounterStep, stdCounterSubroutine, advancePhaseWithInit,
        advancePhase, hcounter] using hno
    · simp [clockCounterStep, stdCounterSubroutine, hcounter] at hout
  · simp [clockCounterStep] at hout
  · simp [clockCounterStep] at hout

private theorem advancePhaseWithInit_phase_ne_two_of_phase_zero_pub
    (a : AgentState L K) (ha : a.phase.val = 0) :
    (advancePhaseWithInit L K a).phase.val ≠ 2 := by
  intro hphase
  rcases a with
    ⟨input, output, phase, role, assigned, bias, smallBias,
      hour, minute, full, opinions, counter⟩
  rcases phase with ⟨p, hp⟩
  simp only at ha
  subst p
  cases role <;>
    simp [advancePhaseWithInit, advancePhase, phaseInit, enterPhase10, phase10] at hphase

private theorem stdCounterSubroutine_phase_ne_two_of_phase_zero_pub
    (a : AgentState L K) (ha : a.phase.val = 0) :
    (stdCounterSubroutine L K a).phase.val ≠ 2 := by
  intro hphase
  unfold stdCounterSubroutine at hphase
  split_ifs at hphase
  · exact advancePhaseWithInit_phase_ne_two_of_phase_zero_pub
      (L := L) (K := K) a ha hphase
  · simp [ha] at hphase

theorem Phase0Transition_left_phase_ne_two_of_phase_zero
    (s t : AgentState L K) (hs : s.phase.val = 0) :
    (Phase0Transition L K s t).1.phase.val ≠ 2 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let s5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K s4 else s4
  have hs1 : s.phase.val = s1.phase.val := by dsimp [s1]; split_ifs <;> rfl
  have hs2 : s1.phase.val = s2.phase.val := by dsimp [s2]; split_ifs <;> rfl
  have hs3 : s2.phase.val = s3.phase.val := by dsimp [s3]; split_ifs <;> rfl
  have hs3' : s3.phase.val = s3'.phase.val := by dsimp [s3']
  have hs4 : s3'.phase.val = s4.phase.val := by dsimp [s4]; split_ifs <;> rfl
  have hs4_zero : s4.phase.val = 0 := by
    rw [← hs4, ← hs3', ← hs3, ← hs2, ← hs1]; exact hs
  change s5.phase.val ≠ 2
  dsimp [s5]
  split_ifs
  · exact stdCounterSubroutine_phase_ne_two_of_phase_zero_pub
      (L := L) (K := K) s4 hs4_zero
  · omega

theorem Phase0Transition_right_phase_ne_two_of_phase_zero
    (s t : AgentState L K) (ht : t.phase.val = 0) :
    (Phase0Transition L K s t).2.phase.val ≠ 2 := by
  let s1 := if s.role = .mcr ∧ t.role = .mcr then
    { s with role := .main, smallBias := addSmallBias s.smallBias t.smallBias } else s
  let t1 := if s.role = .mcr ∧ t.role = .mcr then
    { t with role := .cr, smallBias := ⟨3, by decide⟩ } else t
  let s2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { s1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { s1 with assigned := true, smallBias := addSmallBias t1.smallBias s1.smallBias }
    else s1
  let t2 := if s1.role = .mcr ∧ t1.role = .main ∧ ¬ t1.assigned then
    { t1 with assigned := true, smallBias := addSmallBias s1.smallBias t1.smallBias }
    else if t1.role = .mcr ∧ s1.role = .main ∧ ¬ s1.assigned then
    { t1 with role := .cr, smallBias := ⟨3, by decide⟩ }
    else t1
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { s2 with role := .main }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { t2 with role := .main }
    else t2
  let s3' := s3
  let t3' := t3
  let s4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { s3' with role := .clock, counter := ⟨50 * (L + 1), by omega⟩ } else s3'
  let t4 := if s3'.role = .cr ∧ t3'.role = .cr then
    { t3' with role := .reserve } else t3'
  let t5 := if s4.role = .clock ∧ t4.role = .clock then stdCounterSubroutine L K t4 else t4
  have ht1 : t.phase.val = t1.phase.val := by dsimp [t1]; split_ifs <;> rfl
  have ht2 : t1.phase.val = t2.phase.val := by dsimp [t2]; split_ifs <;> rfl
  have ht3 : t2.phase.val = t3.phase.val := by dsimp [t3]; split_ifs <;> rfl
  have ht3' : t3.phase.val = t3'.phase.val := by dsimp [t3']
  have ht4 : t3'.phase.val = t4.phase.val := by dsimp [t4]; split_ifs <;> rfl
  have ht4_zero : t4.phase.val = 0 := by
    rw [← ht4, ← ht3', ← ht3, ← ht2, ← ht1]; exact ht
  change t5.phase.val ≠ 2
  dsimp [t5]
  split_ifs
  · exact stdCounterSubroutine_phase_ne_two_of_phase_zero_pub
      (L := L) (K := K) t4 ht4_zero
  · omega

/-- If `s.phase = 1` and the Phase-1 transition lifts the left output to phase 2,
the resulting `smallBias` is in the noerror set `{2,3,4}`. -/
theorem Phase1Transition_left_phase2_smallBias_noerror
    (s t : AgentState L K)
    (hs : s.phase.val = 1)
    (hphase : (Phase1Transition L K s t).1.phase.val = 2) :
    (Phase1Transition L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · set s' : AgentState L K :=
      { s with smallBias := (avgFin7 s.smallBias t.smallBias).1 } with hs'_def
    have hs'_phase : s'.phase.val = 1 := by simpa [s'] using hs
    have hcc : (clockCounterStep L K s').phase.val = 2 := by
      simpa [Phase1Transition, hmain, s'] using hphase
    have hres := clockCounterStep_phase2_smallBias_noerror_pub
      (L := L) (K := K) s' hs'_phase hcc
    simpa [Phase1Transition, hmain, s'] using hres
  · have hcc : (clockCounterStep L K s).phase.val = 2 := by
      simpa [Phase1Transition, hmain] using hphase
    have hres := clockCounterStep_phase2_smallBias_noerror_pub
      (L := L) (K := K) s hs hcc
    simpa [Phase1Transition, hmain] using hres

/-- Structural fact: if neither input is already in Phase 10, the two outputs of
`phaseEpidemicUpdate` agree on whether their phase equals 10. -/
theorem phaseEpidemicUpdate_phases_both_ten_or_neither
    (s t : AgentState L K)
    (hs_lt10 : s.phase.val < 10) (ht_lt10 : t.phase.val < 10) :
    ((phaseEpidemicUpdate L K s t).1.phase.val = 10 ↔
      (phaseEpidemicUpdate L K s t).2.phase.val = 10) := by
  unfold phaseEpidemicUpdate
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p })
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p })
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · rw [if_pos h10]
    constructor
    · intro _
      simp [phase10EpidemicEntry, ht_lt10, enterPhase10, phase10]
    · intro _
      simp [phase10EpidemicEntry, hs_lt10, enterPhase10, phase10]
  · rw [if_neg h10]
    have hcond1 : s.phase.val < 10 ∨ t.phase.val < 10 := Or.inl hs_lt10
    have hcond2 : ¬(s0.phase.val = 10 ∨ t0.phase.val = 10) := fun hor =>
      h10 ⟨hcond1, hor⟩
    push_neg at hcond2
    constructor
    · intro h_s0_ten
      exact absurd h_s0_ten hcond2.1
    · intro h_t0_ten
      exact absurd h_t0_ten hcond2.2

/-- Structural fact: when both inputs have phase below 2 and the left epidemic
output is not in Phase 10, that output's phase is also below 2.  This follows
from `runInitsBetween_phase_eq_target_or_ten_of_le_two` (target = `max ≤ 1`). -/
theorem phaseEpidemicUpdate_left_phase_lt_two_of_both_lt_two_of_ne_ten
    (s t : AgentState L K)
    (hs_lt2 : s.phase.val < 2) (ht_lt2 : t.phase.val < 2)
    (hne10 : (phaseEpidemicUpdate L K s t).1.phase.val ≠ 10) :
    (phaseEpidemicUpdate L K s t).1.phase.val < 2 := by
  have hs_lt10 : s.phase.val < 10 := by omega
  have ht_lt10 : t.phase.val < 10 := by omega
  unfold phaseEpidemicUpdate at hne10 ⊢
  set p := max s.phase t.phase
  set s0 := runInitsBetween L K s.phase.val p.val ({ s with phase := p }) with hs0_def
  set t0 := runInitsBetween L K t.phase.val p.val ({ t with phase := p }) with ht0_def
  have hp_lt2 : p.val < 2 := by
    show (max s.phase t.phase).val < 2
    have h1 : s.phase ≤ max s.phase t.phase := le_max_left _ _
    have h2 : t.phase ≤ max s.phase t.phase := le_max_right _ _
    have hub : max s.phase t.phase = s.phase ∨ max s.phase t.phase = t.phase := by
      by_cases h : s.phase ≤ t.phase
      · right; exact max_eq_right h
      · push_neg at h; left; exact max_eq_left h.le
    rcases hub with hub | hub <;> rw [hub] <;> omega
  by_cases h10 :
      (s.phase.val < 10 ∨ t.phase.val < 10) ∧
      (s0.phase.val = 10 ∨ t0.phase.val = 10)
  · exfalso
    apply hne10
    rw [if_pos h10]
    simp [phase10EpidemicEntry, hs_lt10, enterPhase10, phase10]
  · rw [if_neg h10]
    -- ep.1 = s0.  s0.phase = p or = 10.  With ¬h10 and s.phase < 10:
    -- s0.phase ≠ 10, so s0.phase = p < 2.
    have hcond1 : s.phase.val < 10 ∨ t.phase.val < 10 := Or.inl hs_lt10
    have hcond2 : ¬(s0.phase.val = 10 ∨ t0.phase.val = 10) := fun hor =>
      h10 ⟨hcond1, hor⟩
    push_neg at hcond2
    have hs0_eq_or_ten := runInitsBetween_phase_eq_target_or_ten_of_le_two
      (L := L) (K := K) s.phase.val p.val ({ s with phase := p })
      (by omega) (by omega) (by simp)
    rcases hs0_eq_or_ten with hs0_eq | hs0_ten
    · show s0.phase.val < 2
      rw [hs0_def, hs0_eq]
      omega
    · exact absurd hs0_ten hcond2.1

/-- Specialized version of `Transition_left_phase2_smallBias_noerror` that
assumes `s.phase < 2` (so the symmetric Phase-2 → Phase-2 preservation branch is
vacuous). -/
theorem Transition_left_phase2_smallBias_noerror_of_input_lt_two
    (s t : AgentState L K)
    (hs_lt2 : s.phase.val < 2)
    (hphase : (Transition L K s t).1.phase.val = 2) :
    (Transition L K s t).1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have hmax_le : max s.phase.val t.phase.val ≤ 2 := by
    have hep_ge := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    have hep_le := (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).1
    omega
  have ht_le : t.phase.val ≤ 2 := le_trans (le_max_right _ _) hmax_le
  have hphase_orig := hphase
  unfold Transition at hphase ⊢
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hphase
  have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
    simpa [he] using
      phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t (by omega) ht_le
  have hs'_entered :
      s'.phase.val = 2 → s'.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro hs'_phase
    simpa [he] using
      phaseEpidemicUpdate_left_smallBias_noerror_of_entered
        (L := L) (K := K) s t hs_lt2 (by simpa [he] using hs'_phase)
  change (finishPhase10Entry L K s'
    (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).1).smallBias.val ∈ ({2, 3, 4} : Finset ℕ)
  generalize hp : s'.phase = p
  fin_cases p
  · have hpval : s'.phase.val = 0 := by simpa [hp]
    have hlocal : (Phase0Transition L K s' t').1.phase.val = 2 := by
      simpa [hp] using hphase
    exact False.elim
      (Phase0Transition_left_phase_ne_two_of_phase_zero
        (L := L) (K := K) s' t' hpval hlocal)
  · have hlocal := Phase1Transition_left_phase2_smallBias_noerror
      (L := L) (K := K) s' t' (by simpa [hp]) (by simpa [hp] using hphase)
    simpa [hp, finishPhase10Entry_smallBias] using hlocal
  · have hp_eq2 : s'.phase.val = 2 := by simpa [hp]
    have hsmall_pre := hs'_entered hp_eq2
    have hpres := (Phase2Transition_preserves_smallBias L K s' t').1
    have hsmall : (Phase2Transition L K s' t').1.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      rw [hpres]; exact hsmall_pre
    simpa [hp, finishPhase10Entry_smallBias] using hsmall
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 9 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 10 := by simpa [hp]
    have hmono := (Phase10Transition_phase_nondec (L := L) (K := K) s' t').1
    have hout : (Phase10Transition L K s' t').1.phase.val = 2 := by
      simpa [hp] using hphase
    omega

/-- If `t.phase = 1` and the Phase-1 transition lifts the right output to phase 2,
the resulting `smallBias` is in the noerror set `{2,3,4}`. -/
theorem Phase1Transition_right_phase2_smallBias_noerror
    (s t : AgentState L K)
    (ht : t.phase.val = 1)
    (hphase : (Phase1Transition L K s t).2.phase.val = 2) :
    (Phase1Transition L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  by_cases hmain : s.role = .main ∧ t.role = .main
  · set t' : AgentState L K :=
      { t with smallBias := (avgFin7 s.smallBias t.smallBias).2 } with ht'_def
    have ht'_phase : t'.phase.val = 1 := by simpa [t'] using ht
    have hcc : (clockCounterStep L K t').phase.val = 2 := by
      simpa [Phase1Transition, hmain, t'] using hphase
    have hres := clockCounterStep_phase2_smallBias_noerror_pub
      (L := L) (K := K) t' ht'_phase hcc
    simpa [Phase1Transition, hmain, t'] using hres
  · have hcc : (clockCounterStep L K t).phase.val = 2 := by
      simpa [Phase1Transition, hmain] using hphase
    have hres := clockCounterStep_phase2_smallBias_noerror_pub
      (L := L) (K := K) t ht hcc
    simpa [Phase1Transition, hmain] using hres

/-- Specialized right version of `Transition_*_phase2_smallBias_noerror` assuming
`t.phase < 2`. -/
theorem Transition_right_phase2_smallBias_noerror_of_input_lt_two
    (s t : AgentState L K)
    (ht_lt2 : t.phase.val < 2)
    (hphase : (Transition L K s t).2.phase.val = 2) :
    (Transition L K s t).2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
  have hmax_le : max s.phase.val t.phase.val ≤ 2 := by
    have hep_ge := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    have hep_le := (phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) s t).2
    omega
  have hs_le : s.phase.val ≤ 2 := le_trans (le_max_left _ _) hmax_le
  have hphase_orig := hphase
  unfold Transition at hphase ⊢
  generalize he : phaseEpidemicUpdate L K s t = e
  rcases e with ⟨s', t'⟩
  rw [he] at hphase
  have ht'_not_high : t'.phase.val ≤ 2 ∨ t'.phase.val = 10 := by
    simpa [he] using
      phaseEpidemicUpdate_right_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs_le (by omega)
  have hs'_not_high : s'.phase.val ≤ 2 ∨ s'.phase.val = 10 := by
    simpa [he] using
      phaseEpidemicUpdate_left_phase_le_two_or_ten_of_phases_le_two
        (L := L) (K := K) s t hs_le (by omega)
  have ht'_entered :
      t'.phase.val = 2 → t'.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
    intro ht'_phase
    simpa [he] using
      phaseEpidemicUpdate_right_smallBias_noerror_of_entered
        (L := L) (K := K) s t ht_lt2 (by simpa [he] using ht'_phase)
  change (finishPhase10Entry L K t'
    (match s'.phase with
    | ⟨0, _⟩ => Phase0Transition L K s' t'
    | ⟨1, _⟩ => Phase1Transition L K s' t'
    | ⟨2, _⟩ => Phase2Transition L K s' t'
    | ⟨3, _⟩ => Phase3Transition L K s' t'
    | ⟨4, _⟩ => Phase4Transition L K s' t'
    | ⟨5, _⟩ => Phase5Transition L K s' t'
    | ⟨6, _⟩ => Phase6Transition L K s' t'
    | ⟨7, _⟩ => Phase7Transition L K s' t'
    | ⟨8, _⟩ => Phase8Transition L K s' t'
    | ⟨9, _⟩ => Phase9Transition L K s' t'
    | ⟨10, _⟩ => Phase10Transition L K s' t'
    | _ => (s', t')).2).smallBias.val ∈ ({2, 3, 4} : Finset ℕ)
  generalize hp : s'.phase = p
  fin_cases p
  · have hs0 : s'.phase.val = 0 := by simpa [hp]
    have hlocal : (Phase0Transition L K s' t').2.phase.val = 2 := by
      simpa [hp] using hphase
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase0Transition_phase_nondec (L := L) (K := K) s' t').2
      omega
    have hs'_not_ten : s'.phase.val ≠ 10 := by omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
        (L := L) (K := K) s t hs_le (by omega)
        (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
    have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
    have ht0 : t'.phase.val = 0 := by omega
    exact False.elim
      (Phase0Transition_right_phase_ne_two_of_phase_zero
        (L := L) (K := K) s' t' ht0 hlocal)
  · have hs1 : s'.phase.val = 1 := by simpa [hp]
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase1Transition_phase_nondec (L := L) (K := K) s' t').2
      have hlocal : (Phase1Transition L K s' t').2.phase.val = 2 := by
        simpa [hp] using hphase
      omega
    have hs'_not_ten : s'.phase.val ≠ 10 := by omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
        (L := L) (K := K) s t hs_le (by omega)
        (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
    have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
    have ht1 : t'.phase.val = 1 := by omega
    have hlocal := Phase1Transition_right_phase2_smallBias_noerror
      (L := L) (K := K) s' t' ht1 (by simpa [hp] using hphase)
    simpa [hp, finishPhase10Entry_smallBias] using hlocal
  · have hp_eq2 : s'.phase.val = 2 := by simpa [hp]
    have ht'_not_ten : t'.phase.val ≠ 10 := by
      intro ht_ten
      have hmono := (Phase2Transition_phase_nondec (L := L) (K := K) s' t').2
      have hlocal : (Phase2Transition L K s' t').2.phase.val = 2 := by
        simpa [hp] using hphase
      omega
    have hs'_not_ten : s'.phase.val ≠ 10 := by omega
    have hsync :=
      phaseEpidemicUpdate_phases_eq_of_phases_le_two_not_ten
        (L := L) (K := K) s t hs_le (by omega)
        (by simpa [he] using hs'_not_ten) (by simpa [he] using ht'_not_ten)
    have hsync' : s'.phase.val = t'.phase.val := by simpa [he] using hsync
    have ht2 : t'.phase.val = 2 := by omega
    have hsmall_pre := ht'_entered ht2
    have hpres := (Phase2Transition_preserves_smallBias L K s' t').2
    have hsmall : (Phase2Transition L K s' t').2.smallBias.val ∈ ({2, 3, 4} : Finset ℕ) := by
      rw [hpres]; exact hsmall_pre
    simpa [hp, finishPhase10Entry_smallBias] using hsmall
  · have hpval : s'.phase.val = 3 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 4 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 5 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 6 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 7 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 8 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 9 := by simpa [hp]
    rcases hs'_not_high with hle | hten <;> omega
  · have hpval : s'.phase.val = 10 := by simpa [hp]
    have hout : (Phase10Transition L K s' t').2.phase.val = 2 := by
      simpa [hp, finishPhase10Entry_phase_val] using hphase
    have hphase_eq := (Phase10Transition_phase_eq (L := L) (K := K) s' t').2
    have ht2 : t'.phase.val = 2 := by
      rw [hphase_eq] at hout; exact hout
    have hsmall_pre := ht'_entered ht2
    have hpres := (Phase10Transition_preserves_smallBias (L := L) (K := K) s' t').2
    simpa [hp, finishPhase10Entry_smallBias, hpres] using hsmall_pre

/-! ### Bias/role preservation for phase ≥ 9

Phase 9 = Phase2Transition (opinions epidemic) and Phase 10 (slow backup)
both leave `.bias` and `.role` untouched. Combined with `phaseEpidemicUpdate`
(which runs `runInitsBetween` + possibly `enterPhase10`, all bias/role-preserving),
the full `Transition` preserves bias and role when both agents start at phase ≥ 9. -/

set_option maxHeartbeats 800000 in
private lemma Phase10Transition_role_bias_preserved
    (s t : AgentState L K) :
    (Phase10Transition L K s t).1.role = s.role ∧
      (Phase10Transition L K s t).1.bias = s.bias ∧
      (Phase10Transition L K s t).2.role = t.role ∧
      (Phase10Transition L K s t).2.bias = t.bias := by
  unfold Phase10Transition
  constructor <;> [skip; constructor <;> [skip; constructor]]
  all_goals (simp only; split_ifs <;> rfl)

set_option maxHeartbeats 800000 in
private lemma advancePhaseWithInit_role_of_ge_nine
    (a : AgentState L K) (ha : 9 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = a.role := by
  simp only [advancePhaseWithInit]
  have h10 : (advancePhase L K a).phase = ⟨10, by decide⟩ := by
    ext; unfold advancePhase; split <;> (simp; have := a.phase.2; omega)
  have hrole : (advancePhase L K a).role = a.role := by
    unfold advancePhase; split <;> rfl
  rw [h10]; simp [phaseInit]

set_option maxHeartbeats 800000 in
private lemma advancePhaseWithInit_bias_of_ge_nine
    (a : AgentState L K) (ha : 9 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).bias = a.bias := by
  simp only [advancePhaseWithInit]
  have h10 : (advancePhase L K a).phase = ⟨10, by decide⟩ := by
    ext; unfold advancePhase; split <;> (simp; have := a.phase.2; omega)
  have hbias : (advancePhase L K a).bias = a.bias := by
    unfold advancePhase; split <;> rfl
  rw [h10]; simp [phaseInit]; exact hbias

set_option maxHeartbeats 1600000 in
private lemma Phase9Transition_role_bias_preserved_of_phase_ge_nine
    (s t : AgentState L K)
    (hs : 9 ≤ s.phase.val) (ht : 9 ≤ t.phase.val) :
    (Phase9Transition L K s t).1.role = s.role ∧
      (Phase9Transition L K s t).1.bias = s.bias ∧
      (Phase9Transition L K s t).2.role = t.role ∧
      (Phase9Transition L K s t).2.bias = t.bias := by
  unfold Phase9Transition Phase2Transition
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only []; split_ifs <;> first
      | rfl
      | exact advancePhaseWithInit_role_of_ge_nine (L := L) (K := K) _ hs
      | exact advancePhaseWithInit_bias_of_ge_nine (L := L) (K := K) _ hs
      | exact advancePhaseWithInit_role_of_ge_nine (L := L) (K := K) _ ht
      | exact advancePhaseWithInit_bias_of_ge_nine (L := L) (K := K) _ ht)

private lemma runInitsBetween_bias_of_ge_nine (oldP newP : ℕ)
    (hold : 9 ≤ oldP) (hold' : oldP ≤ 10) (hnew : 9 ≤ newP) (hnew' : newP ≤ 10)
    (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).bias = a.bias := by
  have : oldP = 9 ∨ oldP = 10 := by omega
  have : newP = 9 ∨ newP = 10 := by omega
  rcases ‹oldP = 9 ∨ _› with rfl | rfl <;> rcases ‹newP = 9 ∨ _› with rfl | rfl
  · exact congrArg AgentState.bias (runInitsBetween_self_api (L := L) (K := K) 9 a)
  · show (runInitsBetween L K 9 10 a).bias = a.bias
    unfold runInitsBetween
    have : (List.range 11).filter (fun k => 9 < k ∧ k ≤ 10) = [10] := by decide
    rw [this]; simp [phaseInit, enterPhase10]
  · show (runInitsBetween L K 10 9 a).bias = a.bias
    unfold runInitsBetween
    have : (List.range 11).filter (fun k => 10 < k ∧ k ≤ 9) = [] := by decide
    rw [this]; rfl
  · exact congrArg AgentState.bias (runInitsBetween_self_api (L := L) (K := K) 10 a)

private lemma runInitsBetween_role_of_ge_nine (oldP newP : ℕ)
    (hold : 9 ≤ oldP) (hold' : oldP ≤ 10) (hnew : 9 ≤ newP) (hnew' : newP ≤ 10)
    (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).role = a.role := by
  have : oldP = 9 ∨ oldP = 10 := by omega
  have : newP = 9 ∨ newP = 10 := by omega
  rcases ‹oldP = 9 ∨ _› with rfl | rfl <;> rcases ‹newP = 9 ∨ _› with rfl | rfl
  · exact congrArg AgentState.role (runInitsBetween_self_api (L := L) (K := K) 9 a)
  · show (runInitsBetween L K 9 10 a).role = a.role
    unfold runInitsBetween
    have : (List.range 11).filter (fun k => 9 < k ∧ k ≤ 10) = [10] := by decide
    rw [this]; simp [phaseInit, enterPhase10]
  · show (runInitsBetween L K 10 9 a).role = a.role
    unfold runInitsBetween
    have : (List.range 11).filter (fun k => 10 < k ∧ k ≤ 9) = [] := by decide
    rw [this]; rfl
  · exact congrArg AgentState.role (runInitsBetween_self_api (L := L) (K := K) 10 a)

set_option maxHeartbeats 800000 in
private lemma phaseEpidemicUpdate_role_bias_preserved_of_phase_ge_nine
    (s t : AgentState L K)
    (hs : 9 ≤ s.phase.val) (ht : 9 ≤ t.phase.val) :
    (phaseEpidemicUpdate L K s t).1.role = s.role ∧
      (phaseEpidemicUpdate L K s t).1.bias = s.bias ∧
      (phaseEpidemicUpdate L K s t).2.role = t.role ∧
      (phaseEpidemicUpdate L K s t).2.bias = t.bias := by
  have hs' : s.phase.val ≤ 10 := by have := s.phase.2; omega
  have ht' : t.phase.val ≤ 10 := by have := t.phase.2; omega
  have hs_cases : s.phase.val = 9 ∨ s.phase.val = 10 := by omega
  have ht_cases : t.phase.val = 9 ∨ t.phase.val = 10 := by omega
  have hmax_val : (max s.phase t.phase).val = max s.phase.val t.phase.val := by
    simp only [max_def, Fin.le_def]
    split_ifs <;> rfl
  have hmax_ge : 9 ≤ (max s.phase t.phase).val := by
    rw [hmax_val]; exact le_max_of_le_left hs
  have hmax_le : (max s.phase t.phase).val ≤ 10 := by
    rw [hmax_val]; exact max_le hs' ht'
  have hrib_s_bias := runInitsBetween_bias_of_ge_nine (L := L) (K := K)
    s.phase.val _ hs hs' hmax_ge hmax_le ({ s with phase := max s.phase t.phase })
  have hrib_t_bias := runInitsBetween_bias_of_ge_nine (L := L) (K := K)
    t.phase.val _ ht ht' hmax_ge hmax_le ({ t with phase := max s.phase t.phase })
  have hrib_s_role := runInitsBetween_role_of_ge_nine (L := L) (K := K)
    s.phase.val _ hs hs' hmax_ge hmax_le ({ s with phase := max s.phase t.phase })
  have hrib_t_role := runInitsBetween_role_of_ge_nine (L := L) (K := K)
    t.phase.val _ ht ht' hmax_ge hmax_le ({ t with phase := max s.phase t.phase })
  unfold phaseEpidemicUpdate
  simp only
  split_ifs with hcond
  · simp only [phase10EpidemicEntry_role, phase10EpidemicEntry_bias]
    exact ⟨hrib_s_role, hrib_s_bias, hrib_t_role, hrib_t_bias⟩
  · exact ⟨hrib_s_role, hrib_s_bias, hrib_t_role, hrib_t_bias⟩

set_option maxHeartbeats 800000 in
theorem Transition_role_bias_preserved_of_phase_ge_nine
    (s t : AgentState L K) (hs : 9 ≤ s.phase.val) (ht : 9 ≤ t.phase.val) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).1.bias = s.bias ∧
      (Transition L K s t).2.role = t.role ∧
      (Transition L K s t).2.bias = t.bias := by
  have hep := phaseEpidemicUpdate_role_bias_preserved_of_phase_ge_nine
    (L := L) (K := K) s t hs ht
  unfold Transition
  generalize hep_gen : phaseEpidemicUpdate L K s t = ep
  obtain ⟨s', t'⟩ := ep
  have hs'r : s'.role = s.role := by have := hep.1; rw [hep_gen] at this; exact this
  have hs'b : s'.bias = s.bias := by have := hep.2.1; rw [hep_gen] at this; exact this
  have ht'r : t'.role = t.role := by have := hep.2.2.1; rw [hep_gen] at this; exact this
  have ht'b : t'.bias = t.bias := by have := hep.2.2.2; rw [hep_gen] at this; exact this
  have hs'_ge : 9 ≤ s'.phase.val := by
    have := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans hs (le_trans (le_max_left _ _) this)
  have ht'_ge : 9 ≤ t'.phase.val := by
    have := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans ht (le_trans (le_max_right _ _) this)
  have hs'_le : s'.phase.val ≤ 10 := by have := s'.phase.2; omega
  rcases (show s'.phase.val = 9 ∨ s'.phase.val = 10 by omega) with h9 | h10
  · have hph : s'.phase = ⟨9, by decide⟩ := Fin.ext h9
    have hdisp := Phase9Transition_role_bias_preserved_of_phase_ge_nine
      (L := L) (K := K) s' t' hs'_ge ht'_ge
    simp only [hph]
    simp only [finishPhase10Entry_role, finishPhase10Entry_bias,
      hdisp.1, hdisp.2.1, hdisp.2.2.1, hdisp.2.2.2]
    exact ⟨hs'r, hs'b, ht'r, ht'b⟩
  · have hph : s'.phase = ⟨10, by decide⟩ := Fin.ext h10
    have hdisp := Phase10Transition_role_bias_preserved (L := L) (K := K) s' t'
    simp only [hph]
    simp only [finishPhase10Entry_role, finishPhase10Entry_bias,
      hdisp.1, hdisp.2.1, hdisp.2.2.1, hdisp.2.2.2]
    exact ⟨hs'r, hs'b, ht'r, ht'b⟩

/-! ### Phase ≥ 5 infrastructure: phaseInit preserves bias, role, hour

Phases 5–10 never touch `bias`, `role`, or `hour` (they only modify
`counter`, `full`, `opinions`, `output`, or call `enterPhase10` which
also preserves these three fields).  These lemmas let us lift the
preservation through `runInitsBetween` and `phaseEpidemicUpdate`. -/

private lemma phaseInit_bias_of_ge_five (p : Fin 11) (a : AgentState L K)
    (hp : 5 ≤ p.val) :
    (phaseInit L K p a).bias = a.bias := by
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

private lemma phaseInit_role_of_ge_five (p : Fin 11) (a : AgentState L K)
    (hp : 5 ≤ p.val) :
    (phaseInit L K p a).role = a.role := by
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

private lemma phaseInit_hour_of_ge_five (p : Fin 11) (a : AgentState L K)
    (hp : 5 ≤ p.val) :
    (phaseInit L K p a).hour = a.hour := by
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

private lemma foldl_phaseInit_bias (l : List ℕ) (a : AgentState L K)
    (hl : ∀ k ∈ l, 5 ≤ k ∧ k < 11) :
    (l.foldl (fun (acc : AgentState L K) (k : ℕ) =>
      if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).bias = a.bias := by
  induction l generalizing a with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    have hk := hl k List.mem_cons_self
    simp only [dif_pos hk.2]
    rw [ih (phaseInit L K ⟨k, hk.2⟩ a) (fun k' hk' => hl k' (List.mem_cons_of_mem k hk'))]
    exact phaseInit_bias_of_ge_five L K ⟨k, hk.2⟩ a hk.1

private lemma foldl_phaseInit_role (l : List ℕ) (a : AgentState L K)
    (hl : ∀ k ∈ l, 5 ≤ k ∧ k < 11) :
    (l.foldl (fun (acc : AgentState L K) (k : ℕ) =>
      if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).role = a.role := by
  induction l generalizing a with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    have hk := hl k List.mem_cons_self
    simp only [dif_pos hk.2]
    rw [ih (phaseInit L K ⟨k, hk.2⟩ a) (fun k' hk' => hl k' (List.mem_cons_of_mem k hk'))]
    exact phaseInit_role_of_ge_five L K ⟨k, hk.2⟩ a hk.1

private lemma foldl_phaseInit_hour (l : List ℕ) (a : AgentState L K)
    (hl : ∀ k ∈ l, 5 ≤ k ∧ k < 11) :
    (l.foldl (fun (acc : AgentState L K) (k : ℕ) =>
      if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).hour = a.hour := by
  induction l generalizing a with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldl_cons]
    have hk := hl k List.mem_cons_self
    simp only [dif_pos hk.2]
    rw [ih (phaseInit L K ⟨k, hk.2⟩ a) (fun k' hk' => hl k' (List.mem_cons_of_mem k hk'))]
    exact phaseInit_hour_of_ge_five L K ⟨k, hk.2⟩ a hk.1

private lemma runInitsBetween_bias_of_ge_five (oldP newP : ℕ)
    (hold : 5 ≤ oldP) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).bias = a.bias := by
  unfold runInitsBetween
  exact foldl_phaseInit_bias L K _ a (fun k hk => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    exact ⟨by omega, hk.1⟩)

private lemma runInitsBetween_role_of_ge_five (oldP newP : ℕ)
    (hold : 5 ≤ oldP) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).role = a.role := by
  unfold runInitsBetween
  exact foldl_phaseInit_role L K _ a (fun k hk => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    exact ⟨by omega, hk.1⟩)

private lemma runInitsBetween_hour_of_ge_five (oldP newP : ℕ)
    (hold : 5 ≤ oldP) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).hour = a.hour := by
  unfold runInitsBetween
  exact foldl_phaseInit_hour L K _ a (fun k hk => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    exact ⟨by omega, hk.1⟩)

private lemma phaseEpidemicUpdate_preserves_fields_of_ge_five
    (s t : AgentState L K) (hs : 5 ≤ s.phase.val) (ht : 5 ≤ t.phase.val) :
    (phaseEpidemicUpdate L K s t).1.bias = s.bias ∧
    (phaseEpidemicUpdate L K s t).1.role = s.role ∧
    (phaseEpidemicUpdate L K s t).1.hour = s.hour ∧
    (phaseEpidemicUpdate L K s t).2.bias = t.bias ∧
    (phaseEpidemicUpdate L K s t).2.role = t.role ∧
    (phaseEpidemicUpdate L K s t).2.hour = t.hour := by
  unfold phaseEpidemicUpdate
  simp only
  split_ifs with hcond
  · simp only [phase10EpidemicEntry_bias, phase10EpidemicEntry_role,
      phase10EpidemicEntry_hour]
    exact ⟨runInitsBetween_bias_of_ge_five L K _ _ hs _,
           runInitsBetween_role_of_ge_five L K _ _ hs _,
           runInitsBetween_hour_of_ge_five L K _ _ hs _,
           runInitsBetween_bias_of_ge_five L K _ _ ht _,
           runInitsBetween_role_of_ge_five L K _ _ ht _,
           runInitsBetween_hour_of_ge_five L K _ _ ht _⟩
  · exact ⟨runInitsBetween_bias_of_ge_five L K _ _ hs _,
           runInitsBetween_role_of_ge_five L K _ _ hs _,
           runInitsBetween_hour_of_ge_five L K _ _ hs _,
           runInitsBetween_bias_of_ge_five L K _ _ ht _,
           runInitsBetween_role_of_ge_five L K _ _ ht _,
           runInitsBetween_hour_of_ge_five L K _ _ ht _⟩

private lemma advancePhaseWithInit_bias_of_ge_five (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).bias = a.bias := by
  unfold advancePhaseWithInit
  have h_adv_bias : (advancePhase L K a).bias = a.bias := by
    unfold advancePhase; split <;> rfl
  have h_adv_phase : 5 ≤ (advancePhase L K a).phase.val :=
    le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_bias_of_ge_five L K _ _ h_adv_phase, h_adv_bias]

private lemma stdCounterSubroutine_bias_of_ge_five (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).bias = a.bias := by
  unfold stdCounterSubroutine; split_ifs
  · exact advancePhaseWithInit_bias_of_ge_five L K a ha
  · rfl

/-! ### Phase 8 bias sign preservation (structured)

`absorbConsume` only acts on opposite-sign bias pairs (`.pos` vs `.neg`).
When neither input has `.neg` bias, all non-trivial branches are
unreachable and the function returns its inputs unchanged. Combined with
`stdCounterSubroutine` bias preservation (phase ≥ 5) and the existing
phase ≥ 9 results, this gives the full phase ≥ 8 theorem. -/

set_option maxHeartbeats 3200000 in
theorem Transition_preserves_no_neg_bias_of_phase_ge_eight
    (s t : AgentState L K)
    (hs : 8 ≤ s.phase.val) (ht : 8 ≤ t.phase.val)
    (hs_bias : ∀ i, s.bias ≠ .dyadic .neg i)
    (ht_bias : ∀ i, t.bias ≠ .dyadic .neg i) :
    (∀ i, (Transition L K s t).1.bias ≠ .dyadic .neg i) ∧
    (∀ i, (Transition L K s t).2.bias ≠ .dyadic .neg i) := by
  have hep := phaseEpidemicUpdate_preserves_fields_of_ge_five
    (L := L) (K := K) s t (by omega) (by omega)
  unfold Transition
  generalize hep_gen : phaseEpidemicUpdate L K s t = ep
  obtain ⟨s', t'⟩ := ep
  have hs'b : s'.bias = s.bias := by have := hep.1; rw [hep_gen] at this; exact this
  have ht'b : t'.bias = t.bias := by
    have := hep.2.2.2.1; rw [hep_gen] at this; exact this
  have hs'_ge : 8 ≤ s'.phase.val := by
    have := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans hs (le_trans (le_max_left _ _) this)
  have hs'_le : s'.phase.val ≤ 10 := by have := s'.phase.2; omega
  have ht'_ge : 8 ≤ t'.phase.val := by
    have := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans ht (le_trans (le_max_right _ _) this)
  have hs'_nn : ∀ i, s'.bias ≠ .dyadic .neg i := hs'b ▸ hs_bias
  have ht'_nn : ∀ i, t'.bias ≠ .dyadic .neg i := ht'b ▸ ht_bias
  simp only [finishPhase10Entry_bias]
  rcases (show s'.phase.val = 8 ∨ s'.phase.val = 9 ∨ s'.phase.val = 10 by omega)
    with h8 | h9 | h10
  · simp only [show s'.phase = ⟨8, by decide⟩ from Fin.ext h8]
    have hsc_sb := stdCounterSubroutine_bias_of_ge_five L K s' (show 5 ≤ s'.phase.val by omega)
    have hsc_tb := stdCounterSubroutine_bias_of_ge_five L K t' (show 5 ≤ t'.phase.val by omega)
    have : ∀ i, s'.bias = .dyadic .neg i → False := fun i h => hs'_nn i h
    have : ∀ i, t'.bias = .dyadic .neg i → False := fun i h => ht'_nn i h
    rcases hs'b : s'.bias with _ | ⟨(_ | _), _⟩ <;>
    rcases ht'b : t'.bias with _ | ⟨(_ | _), _⟩ <;>
    simp_all (config := { decide := false }) <;>
    (unfold Phase8Transition absorbConsume; simp only;
     split_ifs <;> simp_all)
  · simp only [show s'.phase = ⟨9, by decide⟩ from Fin.ext h9]
    have hb : (Phase9Transition L K s' t').1.bias = s'.bias ∧
              (Phase9Transition L K s' t').2.bias = t'.bias := by
      unfold Phase9Transition Phase2Transition
      refine ⟨?_, ?_⟩ <;>
        (simp only []; split_ifs <;> first
          | rfl
          | (exact advancePhaseWithInit_bias_of_ge_five L K _ (by simp_all <;> omega)))
    exact ⟨fun i => by rw [hb.1]; exact hs'_nn i,
           fun i => by rw [hb.2]; exact ht'_nn i⟩
  · simp only [show s'.phase = ⟨10, by decide⟩ from Fin.ext h10]
    have hd := Phase10Transition_role_bias_preserved (L := L) (K := K) s' t'
    exact ⟨fun i => by rw [hd.2.1]; exact hs'_nn i,
           fun i => by rw [hd.2.2.2]; exact ht'_nn i⟩

/-! ### Reserve-hour < L preservation (structured)

For phases 5–10, `role = .reserve → hour < L` is absorbing.
`phaseInit`/`advancePhaseWithInit`/`stdCounterSubroutine` all preserve
role and hour at phase ≥ 5, so the clock-counter step is harmless.
Per-phase dispatch: Phases 5–8 only modify main×main or reserve→main
pairs, and Phases 9–10 fully preserve role/hour. -/

private lemma advancePhaseWithInit_role_of_ge_five (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = a.role := by
  unfold advancePhaseWithInit
  have h_adv_role : (advancePhase L K a).role = a.role := by
    unfold advancePhase; split <;> rfl
  have h_adv_phase : 5 ≤ (advancePhase L K a).phase.val :=
    le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_role_of_ge_five L K _ _ h_adv_phase, h_adv_role]

private lemma advancePhaseWithInit_hour_of_ge_five (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).hour = a.hour := by
  unfold advancePhaseWithInit
  have h_adv_hour : (advancePhase L K a).hour = a.hour := by
    unfold advancePhase; split <;> rfl
  have h_adv_phase : 5 ≤ (advancePhase L K a).phase.val :=
    le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_hour_of_ge_five L K _ _ h_adv_phase, h_adv_hour]

private lemma stdCounterSubroutine_role_of_ge_five (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).role = a.role := by
  unfold stdCounterSubroutine; split_ifs
  · exact advancePhaseWithInit_role_of_ge_five L K a ha
  · rfl

private lemma stdCounterSubroutine_hour_of_ge_five (a : AgentState L K)
    (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).hour = a.hour := by
  unfold stdCounterSubroutine; split_ifs
  · exact advancePhaseWithInit_hour_of_ge_five L K a ha
  · rfl

set_option maxHeartbeats 3200000 in
theorem Transition_preserves_reserve_hour_lt_L_of_phase_ge_five
    (s t : AgentState L K)
    (hs_phase : 5 ≤ s.phase.val) (ht_phase : 5 ≤ t.phase.val)
    (hs_prop : s.role = .reserve → s.hour.val < L)
    (ht_prop : t.role = .reserve → t.hour.val < L) :
    ((Transition L K s t).1.role = .reserve → (Transition L K s t).1.hour.val < L) ∧
    ((Transition L K s t).2.role = .reserve → (Transition L K s t).2.hour.val < L) := by
  have hep := phaseEpidemicUpdate_preserves_fields_of_ge_five
    (L := L) (K := K) s t hs_phase ht_phase
  unfold Transition
  generalize hep_gen : phaseEpidemicUpdate L K s t = ep
  obtain ⟨s', t'⟩ := ep
  have hs'r : s'.role = s.role := by have := hep.2.1; rw [hep_gen] at this; exact this
  have hs'h : s'.hour = s.hour := by have := hep.2.2.1; rw [hep_gen] at this; exact this
  have ht'r : t'.role = t.role := by have := hep.2.2.2.2.1; rw [hep_gen] at this; exact this
  have ht'h : t'.hour = t.hour := by have := hep.2.2.2.2.2; rw [hep_gen] at this; exact this
  have hs'p : s'.role = .reserve → s'.hour.val < L := by rw [hs'r, hs'h]; exact hs_prop
  have ht'p : t'.role = .reserve → t'.hour.val < L := by rw [ht'r, ht'h]; exact ht_prop
  have hs'_ge : 5 ≤ s'.phase.val := by
    have := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans hs_phase (le_trans (le_max_left _ _) this)
  have ht'_ge : 5 ≤ t'.phase.val := by
    have := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans ht_phase (le_trans (le_max_right _ _) this)
  have hs'_le : s'.phase.val ≤ 10 := by have := s'.phase.2; omega
  rcases (show s'.phase.val = 5 ∨ s'.phase.val = 6 ∨ s'.phase.val = 7 ∨
    s'.phase.val = 8 ∨ s'.phase.val = 9 ∨ s'.phase.val = 10 by omega) with
    hp | hp | hp | hp | hp | hp <;>
  (simp only [show s'.phase = ⟨_, by decide⟩ from Fin.ext hp,
    finishPhase10Entry_role, finishPhase10Entry_hour])
  -- Rotate so Phase 9/10 goals come first (rcases order is 5,6,7,8,9,10)
  rotate_left 4
  -- Phase 9: role + hour fully preserved (Phase9Transition = Phase2Transition)
  · have hrp : (Phase9Transition L K s' t').1.role = s'.role ∧
               (Phase9Transition L K s' t').2.role = t'.role := by
      unfold Phase9Transition Phase2Transition
      refine ⟨?_, ?_⟩ <;>
        (simp only []; split_ifs <;> first
          | rfl
          | exact advancePhaseWithInit_role_of_ge_five L K _ (by omega)
          | exact advancePhaseWithInit_role_of_ge_five L K _ (by omega))
    have hhp : (Phase9Transition L K s' t').1.hour = s'.hour ∧
               (Phase9Transition L K s' t').2.hour = t'.hour := by
      unfold Phase9Transition Phase2Transition
      refine ⟨?_, ?_⟩ <;>
        (simp only []; split_ifs <;> first
          | rfl
          | exact advancePhaseWithInit_hour_of_ge_five L K _ (by omega)
          | exact advancePhaseWithInit_hour_of_ge_five L K _ (by omega))
    exact ⟨fun hr => by rw [hrp.1] at hr; rw [hhp.1]; exact hs'p hr,
           fun hr => by rw [hrp.2] at hr; rw [hhp.2]; exact ht'p hr⟩
  -- Phase 10: role + hour fully preserved
  · have hd := Phase10Transition_role_bias_preserved (L := L) (K := K) s' t'
    have hh : (Phase10Transition L K s' t').1.hour = s'.hour ∧
        (Phase10Transition L K s' t').2.hour = t'.hour := by
      unfold Phase10Transition; simp only; constructor <;> (split_ifs <;> rfl)
    exact ⟨fun hr => by rw [hd.1] at hr; rw [hh.1]; exact hs'p hr,
           fun hr => by rw [hd.2.2.1] at hr; rw [hh.2]; exact ht'p hr⟩
  -- Phases 5–8: clock counter preserves role/hour (phase ≥ 5), and the main
  -- dispatch only affects main×main or reserve→main pairs.
  all_goals {
    have h5_st1 : 5 ≤ (doSplit L K s' t').1.phase.val :=
      le_trans hs'_ge (doSplit_phase_nondec L K s' t').1
    have h5_st2 : 5 ≤ (doSplit L K s' t').2.phase.val :=
      le_trans ht'_ge (doSplit_phase_nondec L K s' t').2
    have h5_ts1 : 5 ≤ (doSplit L K t' s').1.phase.val :=
      le_trans ht'_ge (doSplit_phase_nondec L K t' s').1
    have h5_ts2 : 5 ≤ (doSplit L K t' s').2.phase.val :=
      le_trans hs'_ge (doSplit_phase_nondec L K t' s').2
    refine ⟨fun hr => ?_, fun hr => ?_⟩ <;>
    (simp only [Phase5Transition, Phase6Transition, Phase7Transition,
      Phase8Transition, stdCounterSubroutine,
      doSplit_hour_fst, doSplit_hour_snd, doSplit_role_snd,
      cancelSplit_hour_fst, cancelSplit_hour_snd,
      cancelSplit_role_fst, cancelSplit_role_snd] at hr ⊢;
     split_ifs at hr ⊢ <;>
       first
       | simp_all [advancePhaseWithInit_role_of_ge_five,
           advancePhaseWithInit_hour_of_ge_five]
       | (simp only [advancePhaseWithInit_role_of_ge_five,
            advancePhaseWithInit_hour_of_ge_five,
            stdCounterSubroutine_role_of_ge_five,
            stdCounterSubroutine_hour_of_ge_five] at *;
          first | exact hs'p ‹_› | exact ht'p ‹_› | omega)) }

end ExactMajority
