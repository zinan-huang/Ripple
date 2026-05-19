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

/-- Helper: clamped addition of two small-bias values (Fin 7 encoding −3..+3).
Returns the bias sum clamped to [−3, +3]. -/
def addSmallBias (x y : Fin 7) : Fin 7 :=
  ⟨(max (-3 : ℤ) (min (3 : ℤ) ((x.val : ℤ) + (y.val : ℤ) - 6)) + 3).toNat, by
    have h : ∀ (a b : Fin 7), (max (-3 : ℤ) (min (3 : ℤ) ((a.val : ℤ) + (b.val : ℤ) - 6)) + 3).toNat < 7 := by
      decide
    exact h x y⟩

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

/-- Standard Counter Subroutine: decrement `counter`; if it hits 0, advance
phase to the next phase. -/
def stdCounterSubroutine (a : AgentState L K) : AgentState L K :=
  if h : a.counter.val = 0 then
    advancePhase L K a
  else
    { a with counter := ⟨a.counter.val - 1, by omega⟩ }

lemma stdCounterSubroutine_phase_nondec (a : AgentState L K) :
    a.phase.val ≤ (stdCounterSubroutine L K a).phase.val := by
  unfold stdCounterSubroutine
  split
  · apply advancePhase_phase_nondec
  · rfl

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
  -- Rule 3: MCR + non-Main non-MCR unassigned agent → CR assigns, MCR becomes Main
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then s2
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
              { s2 with assigned := true }
            else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
              { t2 with assigned := true }
            else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then t2
            else t2
  -- Apply the Main-promotion effect for Rule 3 separately (the MCR becomes Main)
  let s3' := if s3.role = .mcr ∧ t3.role = .cr then
               { s3 with role := .main, assigned := true }
             else if t3.role = .mcr ∧ s3.role = .cr then s3
             else s3
  let t3' := if s3.role = .mcr ∧ t3.role = .cr then t3
             else if t3.role = .mcr ∧ s3.role = .cr then
               { t3 with role := .main, assigned := true }
             else t3
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

/-- Phase 1 transition: integer averaging on small biases in {-3,...,+3} via
i, j → ⌊(i+j)/2⌋, ⌈(i+j)/2⌉. -/
def Phase1Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  if h : s.role = .main ∧ t.role = .main then
    let (b1, b2) := avgFin7 s.smallBias t.smallBias
    ({ s with smallBias := b1 }, { t with smallBias := b2 })
  else
    (s, t)

/-- Bitwise union of two `Fin 8` opinion encodings (bit pattern `b_{−1}, b_0, b_{+1}`). -/
def opinionsUnion (x y : Fin 8) : Fin 8 :=
  ⟨x.val.lor y.val, by
    have h : ∀ (x y : Fin 8), x.val.lor y.val < 8 := by decide
    exact h x y⟩

/-- Does the opinion set contain −1 (bit 0 set)? -/
def hasMinusOne (o : Fin 8) : Bool := o.val % 2 = 1

/-- Does the opinion set contain +1 (bit 2 set)? -/
def hasPlusOne (o : Fin 8) : Bool := o.val ≥ 4

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
    (advancePhase L K s', advancePhase L K t')
  else if hasPlusOne univ then
    ({ s' with output := .A }, { t' with output := .A })
  else if hasMinusOne univ then
    ({ s' with output := .B }, { t' with output := .B })
  else if univ.val = 2 then
    ({ s' with output := .T }, { t' with output := .T })
  else
    (s', t')

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
    let hVal := min L (t1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := by
      apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then
    t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := min L (s1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := by
      apply Nat.lt_succ_of_le; exact Nat.min_le_left _ _
    { t1 with hour := ⟨hVal, h_hour_lt⟩ }
  else t1
  -- Rules 3 + 4: both Main. Delegated to `phase3CancelSplit` helper for proof tractability.
  if s2.role = .main ∧ t2.role = .main then phase3CancelSplit L K s2 t2
  else (s2, t2)

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

/-- Phase 6 `doSplit`: Reserve splits with a biased Main, both decrementing their bias
exponent. Returns `(updatedReserve, updatedMain)`. -/
def doSplit (L K : ℕ) (r m : AgentState L K) : AgentState L K × AgentState L K :=
  match m.bias with
  | .dyadic sgn j =>
      if r.hour.val ≠ L ∧ r.hour.val > j.val then
        if h : j.val > 0 then
          let newExp : Fin (L + 1) := ⟨j.val - 1, by omega⟩
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

lemma doSplit_phase_nondec (L K : ℕ) (r m : AgentState L K) :
    r.phase.val ≤ (doSplit L K r m).1.phase.val ∧
    m.phase.val ≤ (doSplit L K r m).2.phase.val := by
  unfold doSplit
  match m.bias with
  | Bias.zero => simp
  | Bias.dyadic _ _ => simp; split_ifs <;> simp

/-- Phase 6 transition: Reserve-fueled splits for high-bias agents.

Reserve + Main (biased) pair where the Reserve's sampled exponent is *higher*
than the Main's exponent (i.e., Reserve has more negative paper exponent):
the Reserve becomes Main with the same opinion, and both agents' exponents are
decremented by 1. Clock agents run the counter subroutine. -/
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

/-- Phase-10 index as a `Fin 11` constant, used by Init code that error-jumps
to the slow stable backup. -/
def phase10 : Fin 11 := ⟨10, by decide⟩

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
    if a.role = .mcr then { a with phase := phase10 }
    else if a.role = .cr then { a with role := .reserve }
    else a
  else if h2 : p.val = 2 then
    -- Paper: if |bias| > 1, phase := 10 (error); else opinions := {sign(smallBias)}.
    let biasMagGT1 : Bool := a.smallBias.val ≤ 1 || a.smallBias.val ≥ 5
    if biasMagGT1 then { a with phase := phase10 }
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
    | .clock => { a with minute := zeroFinMin }
    | _ => a
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
    if biasMagGT1 then { a with phase := phase10 }
    else
      let initOpinions : Fin 8 :=
        if a.smallBias.val < 3 then ⟨1, by decide⟩
        else if a.smallBias.val = 3 then ⟨2, by decide⟩
        else ⟨4, by decide⟩
      { a with opinions := initOpinions }
  else if h10 : p.val = 10 then
    let out : Output := match a.input with | .A => .A | .B => .B
    { a with output := out, full := true }
  else
    a

/-- Run `phaseInit` sequentially for all phases in the half-open interval
`(oldP, newP]`, leaving phases `≤ oldP` and `> newP` untouched. Used by the
phase-epidemic dispatcher when an agent jumps multiple phases. -/
def runInitsBetween (oldP newP : ℕ) (a : AgentState L K) : AgentState L K :=
  ((List.range 11).filter (fun k => oldP < k ∧ k ≤ newP)).foldl
    (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a

/-- Epidemic phase update: both agents jump to `max(s.phase, t.phase)`,
running per-phase Inits for each phase newly entered. -/
def phaseEpidemicUpdate (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let p := max s.phase t.phase
  let s' := runInitsBetween L K s.phase.val p.val { s with phase := p }
  let t' := runInitsBetween L K t.phase.val p.val { t with phase := p }
  (s', t')

lemma smallBias_update_phase (a : AgentState L K) (ph : Fin 11) : ({ a with phase := ph }).smallBias = a.smallBias := by
  simp

lemma smallBias_update_role (a : AgentState L K) (rl : Role) : ({ a with role := rl }).smallBias = a.smallBias := by
  simp

lemma stdCounterSubroutine_smallBias (a : AgentState L K) : (stdCounterSubroutine L K a).smallBias = a.smallBias := by
  unfold stdCounterSubroutine; split_ifs <;> simp [advancePhase]; split_ifs <;> simp

lemma phaseInit_preserves_smallBias (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).smallBias = a.smallBias := by
  fin_cases p
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h]
    · simp [h]
  · unfold phaseInit; simp; split <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h]
    · simp [h]
  · unfold phaseInit; simp

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
  have h_eq : phaseEpidemicUpdate L K s t = (
    runInitsBetween L K s.phase.val (max s.phase.val t.phase.val) ({ s with phase := max s.phase t.phase }),
    runInitsBetween L K t.phase.val (max s.phase.val t.phase.val) ({ t with phase := max s.phase t.phase })) := by
    unfold phaseEpidemicUpdate; rfl
  rw [h_eq]; constructor
  · calc
      (runInitsBetween L K s.phase.val (max s.phase.val t.phase.val) ({ s with phase := max s.phase t.phase })).smallBias
          = ({ s with phase := max s.phase t.phase }).smallBias :=
        runInitsBetween_preserves_smallBias L K s.phase.val (max s.phase.val t.phase.val) _
      _ = s.smallBias := by simp
  · calc
      (runInitsBetween L K t.phase.val (max s.phase.val t.phase.val) ({ t with phase := max s.phase t.phase })).smallBias
          = ({ t with phase := max s.phase t.phase }).smallBias :=
        runInitsBetween_preserves_smallBias L K t.phase.val (max s.phase.val t.phase.val) _
      _ = t.smallBias := by simp

/-- Combined transition function: first run the phase epidemic, then dispatch
to the phase-specific transition. -/
def Transition (s t : AgentState L K) : AgentState L K × AgentState L K :=
  let (s', t') := phaseEpidemicUpdate L K s t
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

lemma stdCounterSubroutine_input_eq (a : AgentState L K) : (stdCounterSubroutine L K a).input = a.input := by
  unfold stdCounterSubroutine; split <;> simp [advancePhase_input_eq]

-- Phase 1 (template, proved)
theorem Phase1Transition_input_preserved (s t : AgentState L K) :
    (Phase1Transition L K s t).1.input = s.input ∧
    (Phase1Transition L K s t).2.input = t.input := by
  unfold Phase1Transition; split_ifs <;> simp

theorem Phase1Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase1Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase1Transition L K s t).2.phase.val := by
  unfold Phase1Transition; split_ifs <;> simp

-- Phase 2 (proved via simple-let pattern)
theorem Phase2Transition_input_preserved (s t : AgentState L K) :
    (Phase2Transition L K s t).1.input = s.input ∧
    (Phase2Transition L K s t).2.input = t.input := by
  simp only [Phase2Transition, advancePhase, stdCounterSubroutine, opinionsUnion, hasMinusOne, hasPlusOne]
  split_ifs <;> simp_all

theorem Phase2Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase2Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase2Transition L K s t).2.phase.val := by
  simp only [Phase2Transition, advancePhase, stdCounterSubroutine, opinionsUnion, hasMinusOne, hasPlusOne]
  split_ifs <;> simp_all

theorem Phase2Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase2Transition L K s t).1.smallBias = s.smallBias ∧
    (Phase2Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase2Transition; dsimp; split_ifs <;> simp [advancePhase]; split_ifs <;> simp

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
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then s2
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then t2
    else t2
  let s3' := if s3.role = .mcr ∧ t3.role = .cr then
    { s3 with role := .main, assigned := true }
    else if t3.role = .mcr ∧ s3.role = .cr then s3 else s3
  let t3' := if s3.role = .mcr ∧ t3.role = .cr then t3
    else if t3.role = .mcr ∧ s3.role = .cr then
    { t3 with role := .main, assigned := true } else t3
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
  have hs3' : s3'.input = s3.input := by dsimp [s3']; split_ifs <;> rfl
  have ht3' : t3'.input = t3.input := by dsimp [t3']; split_ifs <;> rfl
  have hs4 : s4.input = s3'.input := by dsimp [s4]; split_ifs <;> rfl
  have ht4 : t4.input = t3'.input := by dsimp [t4]; split_ifs <;> rfl
  have hs5 : s5.input = s4.input := by
    dsimp [s5]; split_ifs <;> [exact stdCounterSubroutine_input_eq L K s4; rfl]
  have ht5 : t5.input = t4.input := by
    dsimp [t5]; split_ifs <;> [exact stdCounterSubroutine_input_eq L K t4; rfl]
  refine ⟨?_, ?_⟩
  · show s5.input = s.input
    rw [hs5, hs4, hs3', hs3, hs2, hs1]
  · show t5.input = t.input
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
  let s3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then s2
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then
    { s2 with assigned := true } else s2
  let t3 := if s2.role = .mcr ∧ t2.role ≠ .main ∧ t2.role ≠ .mcr ∧ ¬ t2.assigned then
    { t2 with assigned := true }
    else if t2.role = .mcr ∧ s2.role ≠ .main ∧ s2.role ≠ .mcr ∧ ¬ s2.assigned then t2
    else t2
  let s3' := if s3.role = .mcr ∧ t3.role = .cr then
    { s3 with role := .main, assigned := true }
    else if t3.role = .mcr ∧ s3.role = .cr then s3 else s3
  let t3' := if s3.role = .mcr ∧ t3.role = .cr then t3
    else if t3.role = .mcr ∧ s3.role = .cr then
    { t3 with role := .main, assigned := true } else t3
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
  have hs3' : s3.phase.val = s3'.phase.val := by dsimp [s3']; split_ifs <;> rfl
  have ht3' : t3.phase.val = t3'.phase.val := by dsimp [t3']; split_ifs <;> rfl
  have hs4 : s3'.phase.val = s4.phase.val := by dsimp [s4]; split_ifs <;> rfl
  have ht4 : t3'.phase.val = t4.phase.val := by dsimp [t4]; split_ifs <;> rfl
  have hs5 : s4.phase.val ≤ s5.phase.val := by
    dsimp [s5]; split_ifs <;> [exact stdCounterSubroutine_phase_nondec L K s4; exact le_refl _]
  have ht5 : t4.phase.val ≤ t5.phase.val := by
    dsimp [t5]; split_ifs <;> [exact stdCounterSubroutine_phase_nondec L K t4; exact le_refl _]
  refine ⟨?_, ?_⟩
  · show s.phase.val ≤ s5.phase.val
    calc s.phase.val
        = s1.phase.val := hs1
      _ = s2.phase.val := hs2
      _ = s3.phase.val := hs3
      _ = s3'.phase.val := hs3'
      _ = s4.phase.val := hs4
      _ ≤ s5.phase.val := hs5
  · show t.phase.val ≤ t5.phase.val
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
    let hVal := min L (t1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := Nat.lt_succ_of_le (Nat.min_le_left _ _)
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := min L (s1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := Nat.lt_succ_of_le (Nat.min_le_left _ _)
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
  · show (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).1.input = s.input
    split_ifs
    · rw [h_cs_s, hs2, hs1]
    · show s2.input = s.input; rw [hs2, hs1]
  · show (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).2.input = t.input
    split_ifs
    · rw [h_cs_t, ht2, ht1]
    · show t2.input = t.input; rw [ht2, ht1]

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
    let hVal := min L (t1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := Nat.lt_succ_of_le (Nat.min_le_left _ _)
    { s1 with hour := ⟨hVal, h_hour_lt⟩ }
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then s1
  else s1
  let t2 := if s1.role = .main ∧ s1.bias = .zero ∧ t1.role = .clock then t1
  else if t1.role = .main ∧ t1.bias = .zero ∧ s1.role = .clock then
    let hVal := min L (s1.minute.val / K)
    have h_hour_lt : hVal < L + 1 := Nat.lt_succ_of_le (Nat.min_le_left _ _)
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
  · show s.phase.val ≤ (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).1.phase.val
    split_ifs
    · calc s.phase.val ≤ s1.phase.val := hs1
        _ = s2.phase.val := hs2
        _ ≤ (phase3CancelSplit L K s2 t2).1.phase.val := h_cs_s
    · show s.phase.val ≤ s2.phase.val
      calc s.phase.val ≤ s1.phase.val := hs1
        _ = s2.phase.val := hs2
  · show t.phase.val ≤ (if s2.role = .main ∧ t2.role = .main then
            phase3CancelSplit L K s2 t2 else (s2, t2)).2.phase.val
    split_ifs
    · calc t.phase.val ≤ t1.phase.val := ht1
        _ = t2.phase.val := ht2
        _ ≤ (phase3CancelSplit L K s2 t2).2.phase.val := h_cs_t
    · show t.phase.val ≤ t2.phase.val
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
    first | exact ⟨advancePhase_phase_nondec L K s, advancePhase_phase_nondec L K t⟩ | exact ⟨le_refl _, le_refl _⟩

theorem Phase4Transition_preserves_smallBias (s t : AgentState L K) :
    (Phase4Transition L K s t).1.smallBias = s.smallBias ∧
    (Phase4Transition L K s t).2.smallBias = t.smallBias := by
  unfold Phase4Transition; dsimp
  constructor
  · split_ifs <;> simp [advancePhase]; split_ifs <;> simp
  · split_ifs <;> simp [advancePhase]; split_ifs <;> simp

theorem Phase5Transition_input_preserved (s t : AgentState L K) :
    (Phase5Transition L K s t).1.input = s.input ∧
    (Phase5Transition L K s t).2.input = t.input := by
  unfold Phase5Transition
  dsimp only [stdCounterSubroutine, advancePhase]
  refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all

theorem Phase5Transition_phase_nondec (s t : AgentState L K) :
    s.phase.val ≤ (Phase5Transition L K s t).1.phase.val ∧
    t.phase.val ≤ (Phase5Transition L K s t).2.phase.val := by
  unfold Phase5Transition
  dsimp only [stdCounterSubroutine, advancePhase]
  refine ⟨?_, ?_⟩ <;> split_ifs <;> simp_all

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

end ExactMajority
