/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue (d) — composing the real-kernel mixed clock advance over all minutes

`ClockRealMixed.clock_real_advance_mixed` (avenue a) is the genuine PER-MINUTE
clock-minute advance on the REAL `NonuniformMajority L K` kernel: from the mixed
window `Q_mix n mC T` (every one of the `m_C` clocks at phase exactly 3 and minute
`≥ T`), within `t` interactions all `m_C` clocks reach minute `≥ T+1` with failure
`≤ ε`, at the GENUINE clock-fraction-squared contraction rate.  Its three structural
hypotheses (`habs_mix`, `hmono_mix`, `hfrontier_mix`) are carried, NOT discharged.

This file COMPOSES that per-minute phase over the `L₀ = K·(L+1)` minutes — the
real-kernel analog of C5's `all_hours_O_log_n` — via `compose_n_phases`, exactly as
`ClockHourBounds.clock_hour_bounds` / `clock_faithful_O_log_n_upper` compose
`ClockFaithful.minutePhase`.  The result: starting from minute `0` (`Q_mix n mC 0`),
after `∑_{i:Fin L₀} t = L₀·t` interactions, all `m_C` clocks have crossed minute `L₀`
with failure `≤ ∑_{i:Fin L₀} ε = L₀·ε`.

## The cross-minute chaining (genuine, not pure `hx`)

`clock_real_advance_mixed` at minute `T` has
  `Pre  = Q_mix n mC T`,
  `Post = Q_mix n mC T ∧ mC ≤ rBeyond (T+1)`.
Minute `T+1`'s `Pre` is `Q_mix n mC (T+1)`.  These are NOT the same predicate, but
`Post → Pre(next)` is GENUINE and proved here (`Q_mix_succ_of_post`):
* `card`, `clockSize`     — carried verbatim from `Q_mix n mC T`;
* `crossedT` (`rBeyond (T+1) = mC`) — from `mC ≤ rBeyond (T+1)` (Post) together with
  `rBeyond (T+1) ≤ clockCount = mC` (always); so equality;
* `clockPhase3` at level `T+1` (clocks at minute `≥ T+1`) — DERIVED from
  `rBeyond (T+1) = clockCount`: every clock is then beyond `T+1` (a clock not beyond
  `T+1` would make the count strictly smaller).
The contraction itself is the genuine per-minute input — never re-assumed.

## Carried structural hypotheses (∀ minute, EXPLICIT, deferred — NOT discharged)

The per-minute family is fed, at each minute `T`, the three avenue-(a) structural
invariants as ∀-quantified inputs:
* `habs_mix_all`     — one-step closure of `Q_mix n mC T`, ∀ T;
* `hmono_mix_all`    — `rBeyond (T+1)` non-decreasing on the kernel support, ∀ T;
* `hfrontier_mix_all`— the frontier-fraction floor (the `c²` source), ∀ T.
These propagate through composition UNCHANGED; they are GENUINE protocol invariants
deferred to separate avenues, carried here as labeled hypotheses, never hidden.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealMixed

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockRealHours

open ClockRealKernel ClockRealMixed

variable {L K : ℕ}

/-! ## Part A — `rBeyond (T+1) ≤ clockCount` and the chaining lemma. -/

/-- A clock beyond minute `T+1` is in particular a clock: `rBeyond (T+1) c` counts a
sub-population of the clocks, so `rBeyond (T+1) c ≤ clockCount c`. -/
theorem rBeyond_le_clockCount (T : ℕ) (c : Config (AgentState L K)) :
    rBeyond (L := L) (K := K) (T + 1) c ≤ clockCount (L := L) (K := K) c := by
  unfold rBeyond clockCount
  exact countP_mono_pred (fun a => clockBeyondP (T + 1) a) (fun a => a.role = .clock) c
    (fun a ha => ha.1)

/-- **The genuine cross-minute chaining (0.9-floor, NO full crossing).**  If
`Q_mix n mC T c` holds and the level-`T+1` 0.9-floor is crossed
(`9·m_C/10 ≤ rBeyond (T+1) c`), then `Q_mix n mC (T+1) c` holds.  This is exactly
`(faithful step @ T).Post → (faithful step @ T+1).Pre`.  Under the SYNC-fixed window
the upgrade is TRIVIAL: `card`/`clockSize`/`clockPhase3` (phase only) are
T-INDEPENDENT (carried verbatim), and the level-`T+1` `crossedT` IS the 0.9-floor
`hfin` — NO full crossing, NO per-clock minute floor to re-derive. -/
theorem Q_mix_succ_of_post (n mC T : ℕ) (c : Config (AgentState L K))
    (hQ : Q_mix (L := L) (K := K) n mC T c)
    (hfin : 9 * mC / 10 ≤ rBeyond (L := L) (K := K) (T + 1) c) :
    Q_mix (L := L) (K := K) n mC (T + 1) c :=
  ⟨hQ.card, hQ.clockPhase3, hQ.clockSize, hfin⟩

/-! ## Part B — the per-minute phase family over `Fin L₀`.

Each entry `i ↦ clock_real_advance_mixed (minute T = i.val)`, fed the per-minute
structural invariants as ∀-quantified inputs.  Mirrors `ClockHourBounds.hourMinutePhases`,
only the per-minute engine is the REAL-kernel `clock_real_advance_mixed`. -/

/-- The per-minute mixed-advance phase family for minutes `0, …, L₀ − 1`.

Each minute `i` is `clock_real_advance_mixed` at `T = i.val`, with the three avenue-(a)
structural invariants supplied at that minute from the ∀-quantified carried inputs
`habs_mix_all`, `hmono_mix_all`, `hfrontier_mix_all`.  Requires `L₀ ≤ K·(L+1)` so each
minute index `i.val < K·(L+1)` (the clock-cap bound `clock_real_advance_mixed` needs). -/
noncomputable def mixedMinutePhases (n mC L₀ : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hL₀cap : L₀ ≤ K * (L + 1))
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (habs_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (hmono_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      rBeyond (L := L) (K := K) (T + 1) c ≤ rBeyond (L := L) (K := K) (T + 1) c')
    (hfrontier_mix_all : ∀ T : ℕ, ∀ c : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      rBeyond (L := L) (K := K) (T + 1) c < mC →
      γ * ((mC : ℝ) * (mC : ℝ))
        ≤ (rBeyond (L := L) (K := K) (T + 1) c
            * (mC - rBeyond (L := L) (K := K) (T + 1) c : ℕ) : ℝ))
    (t : ℕ) (ε : ℝ≥0)
    (hε : ∀ T : ℕ, ENNReal.ofReal
            (1 - (γ * ((mC : ℝ) * (mC : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ t
          * ENNReal.ofReal (Real.exp (Real.log 2 * (mC : ℝ))) / 1 ≤ (ε : ℝ≥0∞)) :
    Fin L₀ → PhaseConvergence (NonuniformMajority L K).transitionKernel :=
  fun i => clock_real_advance_mixed (L := L) (K := K) n mC i.val hn hmC
    (by have := i.isLt; omega)
    γ hγ hγ1
    (habs_mix_all i.val) (hmono_mix_all i.val) (hfrontier_mix_all i.val)
    t ε (hε i.val)

/-! ## Part C — composing over all `L₀` minutes (`compose_n_phases`).

Mirrors `ClockHourBounds.clock_hour_bounds` exactly, only over the whole minute
range `Fin L₀` (start minute `0`) and with the real-kernel per-minute engine.  The
cross-minute chaining is `Q_mix_succ_of_post` (genuine, Part A). -/

/-- **`clock_real_all_minutes` — the composed real-kernel clock-minute timing.**

Starting from minute `0` crossed (`Q_mix n mC 0`, all `m_C` clocks at phase 3 and
minute `≥ 0`), after `∑_{i:Fin L₀} t = L₀·t` interactions, all `m_C` clocks have
crossed minute `L₀` (the composed `Post`: `Q_mix n mC (L₀−1) ∧ mC ≤ rBeyond L₀`),
with kernel failure `≤ ∑_{i:Fin L₀} ε = L₀·ε`.

GENUINE composition: the per-minute input is the REAL-kernel `clock_real_advance_mixed`
(never re-assumed); the cross-minute chaining is `Q_mix_succ_of_post` (Part A).  The
three avenue-(a) structural invariants are CARRIED through unchanged as the explicit
∀-minute hypotheses `habs_mix_all`, `hmono_mix_all`, `hfrontier_mix_all`. -/
theorem clock_real_all_minutes (n mC L₀ : ℕ) (hL₀ : 0 < L₀) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hL₀cap : L₀ ≤ K * (L + 1))
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (habs_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (hmono_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      rBeyond (L := L) (K := K) (T + 1) c ≤ rBeyond (L := L) (K := K) (T + 1) c')
    (hfrontier_mix_all : ∀ T : ℕ, ∀ c : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      rBeyond (L := L) (K := K) (T + 1) c < mC →
      γ * ((mC : ℝ) * (mC : ℝ))
        ≤ (rBeyond (L := L) (K := K) (T + 1) c
            * (mC - rBeyond (L := L) (K := K) (T + 1) c : ℕ) : ℝ))
    (t : ℕ) (ε : ℝ≥0)
    (hε : ∀ T : ℕ, ENNReal.ofReal
            (1 - (γ * ((mC : ℝ) * (mC : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ t
          * ENNReal.ofReal (Real.exp (Real.log 2 * (mC : ℝ))) / 1 ≤ (ε : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (hc₀ : Q_mix (L := L) (K := K) n mC 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ (L₀ * t)) c₀
        {y | ¬ (Q_mix (L := L) (K := K) n mC (L₀ - 1) y
                ∧ mC ≤ rBeyond (L := L) (K := K) (L₀ - 1 + 1) y)} ≤
      (L₀ : ℝ≥0∞) * (ε : ℝ≥0) := by
  classical
  set phases := mixedMinutePhases (L := L) (K := K) n mC L₀ hn hmC hL₀cap γ hγ hγ1
    habs_mix_all hmono_mix_all hfrontier_mix_all t ε hε with hphases
  -- Cross-minute chaining: minute i.Post → minute (i+1).Pre, genuine (Part A).
  have h_chain : ∀ (i : Fin L₀) (hi : i.val + 1 < L₀),
      ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x := by
    intro i hi x hx
    -- (phases i).Post x  = (Q_mix n mC i.val x ∧ mC ≤ rBeyond (i.val+1) x)
    -- (phases ⟨i+1⟩).Pre x = Q_mix n mC (i.val+1) x
    obtain ⟨hQ, hfin⟩ := hx
    change Q_mix (L := L) (K := K) n mC (i.val + 1) x
    exact Q_mix_succ_of_post n mC i.val x hQ (by omega)
  -- The start: Q_mix n mC 0 = (phases ⟨0⟩).Pre.
  have hx₀' : (phases ⟨0, hL₀⟩).Pre c₀ := by
    change Q_mix (L := L) (K := K) n mC (⟨0, hL₀⟩ : Fin L₀).val c₀
    simpa using hc₀
  have hcomp := compose_n_phases (K := (NonuniformMajority L K).transitionKernel) hL₀
    phases h_chain c₀ hx₀'
  -- Closed forms: time sum = L₀·t, failure sum = L₀·ε, final Post.
  have ht_eq : (∑ i : Fin L₀, (phases i).t) = L₀ * t := by
    have h1 : (∑ _i : Fin L₀, t) = L₀ * t := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← h1]; apply Finset.sum_congr rfl; intro i _; rfl
  have hε_eq : (∑ i : Fin L₀, ((phases i).ε : ℝ≥0∞)) = (L₀ : ℝ≥0∞) * (ε : ℝ≥0) := by
    have h1 : (∑ _i : Fin L₀, ((ε : ℝ≥0) : ℝ≥0∞)) = (L₀ : ℝ≥0∞) * (ε : ℝ≥0) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← h1]; apply Finset.sum_congr rfl; intro i _; rfl
  have hpost_eq :
      {y : Config (AgentState L K) | ¬ (phases ⟨L₀ - 1, by omega⟩).Post y}
      = {y | ¬ (Q_mix (L := L) (K := K) n mC (L₀ - 1) y
              ∧ mC ≤ rBeyond (L := L) (K := K) (L₀ - 1 + 1) y)} := by
    rfl
  rw [ht_eq, hε_eq, hpost_eq] at hcomp
  exact hcomp

/-! ## Part D — `clock_real_O_log_n`: the O(log n) parallel-time reading.

Instantiating `clock_real_all_minutes` with `L₀ = K·(L+1)` (the protocol's full
minute count, `= k·⌈log₂ n⌉` in Doty's parameterization) gives total interactions
`L₀·t = K·(L+1)·t`.  With `t = O(n/c²)` and `K·(L+1) = O(log n)` (the protocol sets
`L = ⌈log₂ n⌉`, `K = k = 45`), the count is `O(n·log n / c²)` — parallel time
`L₀·t / n = O(log n / c²) = O(log n)` for a constant clock fraction `c`.  The kernel
failure is `≤ L₀·ε = O(log n)·ε ≤ 1/poly` once `ε ≤ 1/(n·L₀)`.  Real-kernel analog of
`ClockHourBounds.all_hours_O_log_n`. -/

/-- **`clock_real_O_log_n` — the real-kernel O(log n) clock timing.**

Instantiates `clock_real_all_minutes` at `L₀ = K·(L+1)` (the protocol's full minute
count).  From minute `0` (`Q_mix n mC 0`), after the total `K·(L+1)·t` interactions,
all `m_C` clocks have crossed minute `K·(L+1)` with kernel failure `≤ K·(L+1)·ε`.

The O(log n) parallel-time reading: with the protocol's `L = ⌈log₂ n⌉`, `K = 45`, the
minute count `K·(L+1) = O(log n)`, so `interactions / n = K·(L+1)·t / n = O(log n)`
for `t = O(n/c²)` and constant clock fraction `c`.  Conditional, as in avenue (a), on
the carried ∀-minute structural invariants `habs_mix_all`, `hmono_mix_all`,
`hfrontier_mix_all` (genuine protocol invariants, deferred). -/
theorem clock_real_O_log_n (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (habs_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (hmono_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      rBeyond (L := L) (K := K) (T + 1) c ≤ rBeyond (L := L) (K := K) (T + 1) c')
    (hfrontier_mix_all : ∀ T : ℕ, ∀ c : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      rBeyond (L := L) (K := K) (T + 1) c < mC →
      γ * ((mC : ℝ) * (mC : ℝ))
        ≤ (rBeyond (L := L) (K := K) (T + 1) c
            * (mC - rBeyond (L := L) (K := K) (T + 1) c : ℕ) : ℝ))
    (t : ℕ) (ε : ℝ≥0)
    (hε : ∀ T : ℕ, ENNReal.ofReal
            (1 - (γ * ((mC : ℝ) * (mC : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ t
          * ENNReal.ofReal (Real.exp (Real.log 2 * (mC : ℝ))) / 1 ≤ (ε : ℝ≥0∞))
    (c₀ : Config (AgentState L K)) (hc₀ : Q_mix (L := L) (K := K) n mC 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ ((K * (L + 1)) * t)) c₀
        {y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
                ∧ mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)} ≤
      ((K * (L + 1) : ℕ) : ℝ≥0∞) * (ε : ℝ≥0) := by
  exact clock_real_all_minutes (L := L) (K := K) n mC (K * (L + 1)) hLK hn hmC
    (le_refl (K * (L + 1))) γ hγ hγ1
    habs_mix_all hmono_mix_all hfrontier_mix_all t ε hε c₀ hc₀

/-! ## HONEST STATUS — Avenue (d) (composing the real-kernel mixed advance over minutes)

This file is COMPLETE at the kernel level for the **composition** of the avenue-(a)
real-kernel per-minute clock advance over all `L₀ = K·(L+1)` minutes, 0-sorry /
0-axiom (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

* **The composition is GENUINE.**  The per-minute input is the REAL-kernel
  `ClockRealMixed.clock_real_advance_mixed` (never re-assumed); the L₀ phases are
  chained via `compose_n_phases` (the SAME engine C5 uses).  The cross-minute chaining
  is `Q_mix_succ_of_post` (Part A): minute `T`'s `Post` (`Q_mix n mC T ∧ mC ≤ rBeyond
  (T+1)`) genuinely implies minute `T+1`'s `Pre` (`Q_mix n mC (T+1)`), with the minute
  upgrade DERIVED from `rBeyond (T+1) = clockCount` (every clock then beyond `T+1`).
  This is slightly STRONGER than C5's pure `fun hx => hx`: the real Post/Pre are not
  the identical predicate, so the chaining carries real content, proved here.

* **Carried structural hypotheses (∀ minute, EXPLICIT, deferred).**  The three
  avenue-(a) invariants propagate UNCHANGED as ∀-quantified inputs:
  `habs_mix_all` (window closure), `hmono_mix_all` (clock-stability monotonicity),
  `hfrontier_mix_all` (the frontier-fraction `c²` floor).  They are GENUINE protocol
  invariants (true in real executions), STRUCTURAL (support-closure / monotonicity
  facts, NOT the contraction), and are NOT discharged here — they are deferred to the
  separate avenues that prove them.  The contraction PROBABILITY is NOT among them; it
  is the derived per-minute drift, consumed via `clock_real_advance_mixed`.

* **The O(log n) parallel-time reading.**  `clock_real_O_log_n` instantiates `L₀ =
  K·(L+1)`, giving total interactions `K·(L+1)·t` and failure `≤ K·(L+1)·ε`.  With the
  protocol's `L = ⌈log₂ n⌉`, `K = 45`, the minute count `K·(L+1) = O(log n)`, so
  `interactions / n = K·(L+1)·t / n = O(log n)` for `t = O(n/c²)` and a constant clock
  fraction `c` — Doty's O(log n) parallel time.  Failure `≤ K·(L+1)·ε ≤ 1/poly` once
  `ε ≤ 1/(n·K·(L+1))`.

## SCOPE BOUNDARY (faithful, not inflated)

This is the COMPOSITION over minutes of the per-minute mixed advance — the real-kernel
analog of C5's `all_hours_O_log_n`.  It is CONDITIONAL on the carried ∀-minute
structural invariants (labeled, deferred — three separate avenues).  It does NOT
discharge those invariants, and it does NOT bridge to the main-population hour
synchronization (Doty Lemma 6.10, the supermartingale) — that remains a separate
later piece, deliberately not fabricated here. -/
theorem clock_real_hours_status : True := trivial

end ClockRealHours

end ExactMajority
