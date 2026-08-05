/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineAdaptive
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Statement interface for Theorem 4

The Byzantine theorem cannot assert exact all-`X` consensus of the physical
population: Byzantine molecules remain present and can keep exact physical
consensus false when `b ≥ 2`.  The paper target is therefore the relaxed
`X`-consensus region `x + 8b ≥ n`, recorded in subtraction-free form as
`n ≤ x + 8*b`.

The theorem also has two time conclusions.  First, the process enters the
relaxed target within `C * γ * n * lg n` interactions.  Second, after entry it
stays in that relaxed region for the following `n^γ` interactions, up to the
same polynomially small failure scale.  The definitions below keep those two
failure events separate and then record the union-bound form.
-/

namespace Tri

open scoped ENNReal

/-- The paper's initial hypotheses for Theorem 4, in subtraction-free form. -/
def Theorem4PaperInitial (n γ x₀ y₀ b d : ℕ) : Prop :=
  x₀ + y₀ + b = n ∧
    n + d = 2 * x₀ ∧
      γ * n * Nat.log 2 n ≤ d ^ 2 ∧
        16 * b < d

/-- The paper's Byzantine budget premise is equivalent to the printed
`X`-majority-with-Byzantine-buffer inequality. -/
theorem theorem4_budget_gap_equiv
    {n x₀ y₀ b d : ℕ}
    (hmass : x₀ + y₀ + b = n)
    (hgap : n + d = 2 * x₀) :
    16 * b < d ↔ y₀ + 17 * b < x₀ := by
  omega

/-- The physical initial state determined by the paper's natural-number data. -/
noncomputable def theorem4InitialState
    (n x₀ y₀ b : ℕ) (hmass : x₀ + y₀ + b = n) :
    Byzantine.State n b := by
  refine ⟨(⟨x₀, ?_⟩, ⟨b, ?_⟩), ?_⟩
  · omega
  · omega
  · change x₀ + b ≤ n
    omega

namespace Byzantine

instance relaxedXConsensusDecidable (s : State n B) :
    Decidable (RelaxedXConsensus s) := by
  unfold RelaxedXConsensus
  infer_instance

/-- The complement of relaxed `X`-consensus, again subtraction-free. -/
def RelaxedXFailure (s : State n B) : Prop :=
  State.x s + 8 * State.z s < n

instance relaxedXFailureDecidable (s : State n B) :
    Decidable (RelaxedXFailure s) := by
  unfold RelaxedXFailure
  infer_instance

/-- Total wrapper for the adaptive law.  On the theorem's `n ≥ 3` regime this
is definitionally the genuine history-dependent physical law. -/
noncomputable def theorem4ControlledLaw
    (σ : Strategy n B) (T : ℕ)
    (hist : History n B) (s₀ : State n B) : PMF (State n B) :=
  if h3 : 3 ≤ n then controlledLaw σ h3 T hist s₀ else PMF.pure s₀

/-- Entry failure mass at a terminal time for a history-dependent Byzantine
strategy: the mass still OUTSIDE the relaxed target at time `T`.

**Do not use this for the entry statement.**  It measures OCCUPANCY at the
terminal time under the UNFROZEN law, whereas the Phase-I/Phase-II machinery
proves a stopped REACHED-BY-DEADLINE event.  Relaxed consensus is not absorbing
and the printed preservation clause is false (see the section below), so a path
may enter the target and leave again before `T`; there is therefore no sound
implication from the stopped hitting theorem to terminal occupancy.  Kept only
because it is the literal reading of "the mass outside the target at time T". -/
noncomputable def theorem4EntryFailureMass
    (σ : Strategy n B) (T : ℕ)
    (hist : History n B) (s₀ : State n B) : ℝ≥0∞ :=
  ∑' s, if RelaxedXConsensus s then 0
    else theorem4ControlledLaw σ T hist s₀ s

/-- The adaptive physical law frozen as soon as it ENTERS the relaxed target.
Terminal mass outside the target for this law is exactly the finite-horizon
event "never reached the target by time `T`". -/
noncomputable def theorem4ControlledFrozenLaw
    (σ : Strategy n B) :
    ℕ → History n B → State n B → PMF (State n B)
  | 0, _, s => PMF.pure s
  | T + 1, hist, s =>
      if RelaxedXConsensus s then PMF.pure s
      else
        if h3 : 3 ≤ n then
          (adaptiveEventStep σ hist s h3).bind
            (fun e =>
              theorem4ControlledFrozenLaw
                σ T (e :: hist) e.after)
        else
          PMF.pure s

/-- Entry failure mass as a HITTING event: the mass that has not reached the
relaxed target at any time up to `T`.  This is what the machinery proves, and
what the entry clause must state.  The target is frozen, so once a path reaches
the relaxed region it is counted as a success even if the unfrozen process
would later leave. -/
noncomputable def theorem4EntryHittingFailureMass
    (σ : Strategy n B) (T : ℕ)
    (hist : History n B) (s₀ : State n B) : ℝ≥0∞ :=
  ∑' s, if RelaxedXConsensus s then 0
    else theorem4ControlledFrozenLaw σ T hist s₀ s

/-- The adaptive physical law stopped as soon as it leaves the relaxed target.
Terminal mass in `RelaxedXFailure` for this law is the finite-horizon path
event that some time in the interval has left the relaxed region. -/
noncomputable def relaxedFailureStoppedLaw
    (σ : Strategy n B) :
    ℕ → History n B → State n B → PMF (State n B)
  | 0, _, s => PMF.pure s
  | T + 1, hist, s =>
      if RelaxedXFailure s then
        PMF.pure s
      else
        if h3 : 3 ≤ n then
          (adaptiveEventStep σ hist s h3).bind
            (fun e => relaxedFailureStoppedLaw σ T (e :: hist) e.after)
        else
          PMF.pure s

/-- Path/interval failure mass for the preservation part of Theorem 4. -/
noncomputable def theorem4PreservationFailureMass
    (σ : Strategy n B) (T : ℕ)
    (hist : History n B) (s₀ : State n B) : ℝ≥0∞ :=
  ∑' s, if RelaxedXFailure s then
    relaxedFailureStoppedLaw σ T hist s₀ s else 0

/-- Worst-case post-entry preservation failure over the arbitrary history and
entry state produced by the entry phase. -/
noncomputable def theorem4WorstPreservationFailure
    (σ : Strategy n B) (γ : ℕ) : ℝ≥0∞ :=
  ⨆ hist : History n B,
    ⨆ s₁ : State n B,
      if RelaxedXConsensus s₁ then
        theorem4PreservationFailureMass σ (n ^ γ) hist s₁
      else 0

end Byzantine

/-! ### The entry clause is a HITTING statement, not an occupancy one

`Theorem4_entry_statement` measures `theorem4EntryHittingFailureMass`: the mass that has NOT
REACHED the relaxed target at any time up to the deadline. It deliberately does not use
`theorem4EntryFailureMass`, which is terminal OCCUPANCY under the unfrozen law.

The reason is forced. Relaxed consensus is not absorbing, and the printed preservation clause
is false (see the warning below), so a path may enter the target and leave again before the
terminal time. The Phase-I and Phase-II machinery proves a stopped reached-by-deadline event,
and there is no sound implication from that to terminal occupancy. Stating the occupancy form
would make the clause unprovable by this route — and, given that preservation genuinely fails,
unprovable by any route that does not first repair preservation.

This is a semantic correction to our own earlier statement, found by auditing the statement
against the machinery BEFORE attempting the assembly.
-/

/-! ### The entry clause carries one side condition the paper does not print

Phase II of Theorem 4's proof rests on paper Lemma 10, which is only asymptotically valid:
its proof says "for `n` sufficiently large", and a uniform sufficient condition is
`γ · lg n < 3n/68`.  The repo's `PaperLemma10.lemma10_effectiveFireRate_cross` concludes the
STRICT inequality `68 * (γ * Nat.log 2 n) < 3 * n`, so a non-strict hypothesis is not enough
(equality is arithmetically possible).  We therefore carry the subtraction-free strict form
`68 * γ * Nat.log 2 n + 1 ≤ 3 * n`.

This is NOT implied by the standing hypothesis `6 * γ * Nat.log 2 n ≤ n`, and — crucially —
it is not an `n`-largeness condition that a leading `∃ n₀` could absorb: `γ` may grow with
`n`. At the extreme `γ = n / (6 lg n)` permitted by the standing hypothesis one gets
`γ lg n = n/6 = 11.33 n/68 > 3n/68`, and this fails at EVERY `n` (checked at `n = 2^20` and
`2^40`). So the condition must appear in the statement.

Recording it here is the same discipline used for Theorem 5's headline: we do not silently
inherit a step the printed proof leaves unjustified. It is filed as a (U)-class item in
ERRATA.tex — a side condition the paper's proof needs but its theorem does not state, the
same pattern as Theorem 1's unstated `γ lg n ≤ n/6`.
-/

/-- The entry-time clause of Theorem 4, as a Prop-valued statement. -/
def Theorem4_entry_statement : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        n₀ ≤ n → 1 ≤ γ → 6 * γ * Nat.log 2 n ≤ n →
        68 * γ * Nat.log 2 n + 1 ≤ 3 * n →
        ∀ x₀ y₀ b d : ℕ,
          (hinit : Theorem4PaperInitial n γ x₀ y₀ b d) →
          ∀ σ : Byzantine.Strategy n b,
            let s₀ :=
              theorem4InitialState n x₀ y₀ b hinit.1
            Byzantine.theorem4EntryHittingFailureMass σ
                (C * γ * n * Nat.log 2 n) [] s₀
              ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

/-! ### ⚠ THE PRESERVATION CLAUSE IS FALSE AS PRINTED — do not attempt to prove it

An independent audit (2026-07-30), whose counterexample the coordinator re-verified, shows
that paper Theorem 4's polynomial preservation clause is an (E)-class statement-level error,
not a proof gap. Take `z = 2` Byzantine molecules, `γ = 17`, and the state
`(x, y, z) = (n − 16, 14, 2)`, which lies exactly on the printed relaxed-consensus boundary
`x = n − 8z` and satisfies both theorem hypotheses for all large `n`
(`Δ₀ = n − 32`, and `(n−32)² ≥ 17 n lg n`, `2 < (n−32)/16`).
Under the paper's own declared worst response (Byzantine molecules always favour `Y` — a
FIXED, non-adaptive adversary, so adaptivity cannot rescue the claim), partition the raw
timeline into blocks of `29n²` interactions. From any `0 ≤ y ≤ 14`, one block reaches
`y = 15` — i.e. exits the relaxed guard — with probability at least `c·n^(−14)`,
`c = 1/(2·4^14·6^14)`: drive `y` down to `0`, nucleate `y = 1` from a `{X,B,B}` triple whose
two Byzantine molecules both present `Y` (so `X + Y + Y → 3Y`), then take fourteen
prescribed up-steps each costing at most `1/(6n)`. There are `Θ(n^15)` blocks in `n^17`
interactions, so
`P(no exit by n^17) ≤ (1 − c n^(−14))^(Θ(n^15)) ≤ exp(−Θ(n)) → 0`,
whereas the theorem claims exit probability `exp(−Ω(γ lg n)) → 0`. The crossover is at
`n ≈ 1.2 × 10^21` (verified), which is far below the `n₀` at which this repository's other
headline theorems even apply, so the asymptotic refutation is legitimate.

Root cause: the dynamics do not depend on the confidence parameter `γ`, while the window
length `n^γ` does. With `z` a fixed constant, escaping the buffer costs `n^(−O(z))` per
attempt, and a window of unbounded polynomial degree overwhelms it. No choice of hidden
constant repairs this.

Consequently the two definitions below — `Theorem4_preservation_statement` and the union
form `Theorem4_statement` — are recorded for faithfulness to the printed claim and are
KNOWN TO BE FALSE. Do not attempt to prove them, and do not weaken them silently: the
provable content is `Theorem4_entry_statement` (unaffected) plus a preservation claim whose
window is tied to the Byzantine count, or which guards a buffered predicate. See ERRATA.tex.
-/

/-- The post-entry preservation clause of Theorem 4, as a Prop-valued
path/interval statement.  The history is quantified because the entry time may
leave the adversary with an arbitrary prior transcript. -/
def Theorem4_preservation_statement : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        n₀ ≤ n → 1 ≤ γ → 6 * γ * Nat.log 2 n ≤ n →
        ∀ b : ℕ,
          ∀ σ : Byzantine.Strategy n b,
            ∀ hist : Byzantine.History n b,
              ∀ s₁ : Byzantine.State n b,
                Byzantine.RelaxedXConsensus s₁ →
                  Byzantine.theorem4PreservationFailureMass σ
                      (n ^ γ) hist s₁
                    ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

/-- The union-bound form of the full Theorem 4 statement.  It combines the
terminal entry failure with the worst-case post-entry path failure. -/
def Theorem4_statement : Prop :=
  ∃ C n₀ : ℕ, ∃ c : ℝ,
    0 < C ∧ 0 < c ∧ 3 ≤ n₀ ∧
      ∀ n γ : ℕ,
        n₀ ≤ n → 1 ≤ γ → 6 * γ * Nat.log 2 n ≤ n →
        ∀ x₀ y₀ b d : ℕ,
          (hinit : Theorem4PaperInitial n γ x₀ y₀ b d) →
          ∀ σ : Byzantine.Strategy n b,
            let s₀ :=
              theorem4InitialState n x₀ y₀ b hinit.1
            Byzantine.theorem4EntryFailureMass σ
                (C * γ * n * Nat.log 2 n) [] s₀ +
              Byzantine.theorem4WorstPreservationFailure σ γ
              ≤ (n : ℝ≥0∞)⁻¹ ^ (c * (γ : ℝ))

end Tri

#print axioms Tri.theorem4_budget_gap_equiv
#print axioms Tri.Theorem4_entry_statement
#print axioms Tri.Theorem4_preservation_statement
#print axioms Tri.Theorem4_statement
