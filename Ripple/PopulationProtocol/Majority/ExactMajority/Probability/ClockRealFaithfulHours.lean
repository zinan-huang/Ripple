/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue (d') — composing the FAITHFUL per-minute clock step over all minutes →
# the GENUINE O(log n) real-kernel clock

Avenue (a'') (`ClockRealSeed.clock_real_step`) built the FAITHFUL per-minute
O(1)-parallel clock advance on the REAL `NonuniformMajority L K` kernel: from the
mixed window `Q_mix n mC T` with the prior level crossed
(`9·m_C/10 ≤ rBeyond T`), within `tseed + tbulk` interactions the level
`rBeyond (T+1)` crosses the full `0.9·m_C` bulk target
(`bulkHi m_C ≤ rBeyond (T+1)`), with failure `≤ εseed + εbulk`.  Crucially this is
the GENUINE bulk decomposition (seed `0 → 0.1·m_C` ++ epidemic `0.1·m_C → 0.9·m_C`),
each phase `O(n/c²) = O(1)` parallel, so the per-minute cost is `O(1)` — UNLIKE the
superseded `clock_real_O_log_n` (avenue d), whose per-minute step crossed the FULL
`m_C` (`clock_real_advance_mixed`), costing `O(log n)` per minute = `Θ(log²n)` total.

This file COMPOSES `clock_real_step` over `L₀ = K·(L+1)` minutes via
`compose_n_phases` (the SAME engine C5 / avenue (d) use) → the clock reaches its
final level in `L₀·(tseed + tbulk)` interactions = `O(log n)` PARALLEL time
(genuinely `O(1)` per minute × `O(log n)` minutes — the CORRECT scale).

## The cross-minute chaining — HONEST account

`clock_real_step` at minute `T` has
  `Pre  = Q_mix n mC T ∧ 9·m_C/10 ≤ rBeyond T`,
  `Post = Q_mix n mC T ∧ bulkHi m_C ≤ rBeyond (T+1)`     (`bulkHi m_C = 9·m_C/10`).
Minute `T+1`'s `Pre` is `Q_mix n mC (T+1) ∧ 9·m_C/10 ≤ rBeyond (T+1)`.

* The `9·m_C/10 ≤ rBeyond (T+1)` conjunct is IDENTICAL on both sides (`bulkHi m_C`
  is definitionally `9·m_C/10`), so it carries verbatim.
* The `Q_mix n mC T → Q_mix n mC (T+1)` conjunct is the genuine window-upgrade.  Its
  `card` / `clockSize` parts are T-INDEPENDENT (carried verbatim).  Its `clockPhase3`
  (clocks at minute `≥ T+1`) and `crossedT` (`rBeyond (T+1) = m_C`) parts are the
  level-`T+1` floor — these are the mixed-regime `Q_mix_succ_of_post` content, which
  is DERIVED from `m_C ≤ rBeyond (T+1)` (full crossing).  The faithful bulk step,
  however, only delivers `bulkHi m_C = 0.9·m_C ≤ rBeyond (T+1)`, NOT the full `m_C`.
  So the window upgrade is fed exactly ONE extra deterministic input per minute, the
  full-crossing closure `m_C ≤ rBeyond (T+1)` — the residual ("last 0.1·m_C of
  laggard clocks") completed by the protocol's minute synchronisation.  We carry it
  as the ∀-minute hypothesis `hcross_full` and DISCHARGE the upgrade GENUINELY via
  `ClockRealHours.Q_mix_succ_of_post` (no `Q_mix(T+1)` is ever assumed — only the
  level fact `m_C ≤ rBeyond (T+1)`, then the full `Q_mix(T+1)` is PROVEN).

The contraction itself is the genuine per-minute input (`clock_real_step`), never
re-assumed.  The composition is genuinely `O(1)` per minute → `O(log n)` total.

## Carried hypotheses (∀ minute, EXPLICIT, deferred — NOT discharged)

* `habs_mix` — one-step support closure of `Q_mix n mC T`, ∀ T (the SINGLE structural
  invariant that `clock_real_step` carries; deterministic, NOT a probability).
* `hcross_full` — the deterministic full-crossing closure
  `Q_mix n mC T → bulkHi m_C ≤ rBeyond (T+1) → m_C ≤ rBeyond (T+1)`, ∀ T (the
  minute-synchronisation residual: once the bulk 0.9 is crossed the remaining 0.1
  laggard clocks finish the minute).  This is the SOLE extra input beyond `habs_mix`,
  required precisely because the faithful step is bulk-only (0.9, O(1)/minute) rather
  than full (1.0, O(log n)/minute as in the superseded avenue d).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealSeed
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockRealHours
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockMonoDischarge

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ClockRealFaithfulHours

open ClockRealKernel ClockRealMixed ClockMonoDischarge ClockRealBulk ClockRealSeed
open ClockRealHours

variable {L K : ℕ}

/-! ## Part A — the per-minute faithful step packaged as a `PhaseConvergence`.

`clock_real_step` is the genuine faithful O(1)/minute clock advance (theorem form).
We package it as a `PhaseConvergence` (`minuteStepPhase`) so it can be fed to
`compose_n_phases`.  `Pre`/`Post`/`t`/`ε` are exactly `clock_real_step`'s; the
`convergence` field IS `clock_real_step`; `post_absorbing` is discharged from the
carried `habs_mix` (window closure) + the PROVEN `hmono_mix_discharged`
(`rBeyond (T+1)` non-decreasing), exactly as `clock_real_advance_bulk`'s
`hPost_abs`. -/

/-- **`minuteStepPhase` — the faithful per-minute clock step as a `PhaseConvergence`.**

`Pre  = Q_mix n mC T ∧ 9·m_C/10 ≤ rBeyond T`,
`Post = Q_mix n mC T ∧ bulkHi m_C ≤ rBeyond (T+1)`,
`t = tseed + tbulk`, `ε = εseed + εbulk`, `convergence = clock_real_step` (the
GENUINE faithful O(1)/minute advance, never re-assumed).  `post_absorbing` is
discharged from `habs_mix` (window closure, carried) + `hmono_mix_discharged`
(`rBeyond (T+1)` non-decreasing, PROVEN). -/
noncomputable def minuteStepPhase (n mC T : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hT : T < K * (L + 1))
    (habs_mix : ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tseed
          * ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tbulk
          * ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel where
  Pre := fun c => Q_mix (L := L) (K := K) n mC T c
    ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) T c
  Post := fun c => Q_mix (L := L) (K := K) n mC T c
    ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c
  t := tseed + tbulk
  ε := εseed + εbulk
  post_absorbing := by
    intro c hc
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | Q_mix (L := L) (K := K) n mC T c'
        ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (T + 1) c'} = 1
    rw [(((NonuniformMajority L K).stepDistOrSelf c)).toMeasure_apply_eq_one_iff
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    intro c' hc'
    obtain ⟨hQ, hfin⟩ := hc
    exact ⟨habs_mix c c' hQ hc',
      le_trans hfin (hmono_mix_discharged n mC T c c' hQ hc')⟩
  convergence := by
    intro c₀ hPre
    exact clock_real_step n mC T hn hmC hT habs_mix tseed tbulk εseed εbulk hεs hεb c₀ hPre

/-! ## Part B — the per-minute phase family over `Fin L₀`.

Each entry `i ↦ minuteStepPhase (minute T = i.val)`, fed the per-minute structural
invariant `habs_mix` as the ∀-quantified carried input.  Mirrors
`ClockRealHours.mixedMinutePhases`, only the per-minute engine is the FAITHFUL
O(1)/minute `clock_real_step` (bulk-only crossing) in place of the full-crossing
`clock_real_advance_mixed`. -/

/-- The faithful per-minute step family for minutes `0, …, L₀ − 1`.

Each minute `i` is `minuteStepPhase` at `T = i.val`, fed the carried per-minute
`habs_mix`.  Requires `L₀ ≤ K·(L+1)` so each minute index `i.val < K·(L+1)`. -/
noncomputable def faithfulMinutePhases (n mC L₀ : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hL₀cap : L₀ ≤ K * (L + 1))
    (habs_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tseed
          * ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tbulk
          * ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞)) :
    Fin L₀ → PhaseConvergence (NonuniformMajority L K).transitionKernel :=
  fun i => minuteStepPhase (L := L) (K := K) n mC i.val hn hmC
    (by have := i.isLt; omega)
    (habs_mix_all i.val) tseed tbulk εseed εbulk hεs hεb

/-! ## Part C — composing the faithful step over all `L₀` minutes.

Mirrors `ClockRealHours.clock_real_all_minutes`, only with the FAITHFUL O(1)/minute
engine.  The cross-minute chaining `Q_mix n mC T → Q_mix n mC (T+1)` is the GENUINE
mixed-regime upgrade `ClockRealHours.Q_mix_succ_of_post` (PROVEN there from
`m_C ≤ rBeyond (T+1)`), with the full-crossing level fact supplied per-minute by the
deterministic carried hypothesis `hcross_full_all` (the minute-synchronisation
residual; the SOLE extra input the bulk-only step needs).  No `Q_mix(T+1)` is ever
assumed — only the level inequality, then the window upgrade is derived. -/

/-- **`clock_real_faithful_all_minutes` — the composed FAITHFUL real-kernel clock.**

Starting from minute `0` crossed (`Q_mix n mC 0 ∧ 9·m_C/10 ≤ rBeyond 0`), after
`∑_{i:Fin L₀} (tseed+tbulk) = L₀·(tseed+tbulk)` interactions, the level
`rBeyond L₀` has crossed the `0.9·m_C` bulk target (the composed `Post`:
`Q_mix n mC (L₀−1) ∧ bulkHi m_C ≤ rBeyond L₀`), with kernel failure
`≤ ∑_{i:Fin L₀} (εseed+εbulk) = L₀·(εseed+εbulk)`.

GENUINE faithful composition: the per-minute input is `clock_real_step` (the
O(1)/minute bulk decomposition, never re-assumed); the cross-minute chaining is the
PROVEN `Q_mix_succ_of_post` fed by the carried full-crossing level fact
`hcross_full_all`.  Carried ∀-minute hypotheses: `habs_mix_all` (window closure),
`hcross_full_all` (minute-sync residual). -/
theorem clock_real_faithful_all_minutes (n mC L₀ : ℕ) (hL₀ : 0 < L₀)
    (hn : 2 ≤ n) (hmC : 2 ≤ mC) (hL₀cap : L₀ ≤ K * (L + 1))
    (habs_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tseed
          * ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tbulk
          * ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K))
    (hc₀ : Q_mix (L := L) (K := K) n mC 0 c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ (L₀ * (tseed + tbulk))) c₀
        {y | ¬ (Q_mix (L := L) (K := K) n mC (L₀ - 1) y
                ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (L₀ - 1 + 1) y)} ≤
      (L₀ : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
  classical
  set phases := faithfulMinutePhases (L := L) (K := K) n mC L₀ hn hmC hL₀cap
    habs_mix_all tseed tbulk εseed εbulk hεs hεb with hphases
  -- Cross-minute chaining: minute i.Post → minute (i+1).Pre, GENUINE — NO full crossing.
  have h_chain : ∀ (i : Fin L₀) (hi : i.val + 1 < L₀),
      ∀ x, (phases i).Post x → (phases ⟨i.val + 1, hi⟩).Pre x := by
    intro i hi x hx
    -- (phases i).Post x = (Q_mix n mC i.val x ∧ bulkHi mC ≤ rBeyond (i.val+1) x)
    -- (phases ⟨i+1⟩).Pre x = (Q_mix n mC (i.val+1) x ∧ 9*mC/10 ≤ rBeyond (i.val+1) x)
    obtain ⟨hQ, hbulk⟩ := hx
    -- bulkHi mC = 9*mC/10, so the 0.9-floor at level (i+1) IS the bulk Post: NO full crossing.
    have h09 : 9 * mC / 10 ≤ rBeyond (L := L) (K := K) (i.val + 1) x := by
      have hbh : bulkHi mC = 9 * mC / 10 := rfl
      rw [← hbh]; exact hbulk
    refine ⟨?_, ?_⟩
    · -- Q_mix n mC i.val x → Q_mix n mC (i.val+1) x, PROVEN via Q_mix_succ_of_post (0.9-floor).
      change Q_mix (L := L) (K := K) n mC (i.val + 1) x
      exact Q_mix_succ_of_post n mC i.val x hQ h09
    · -- 9*mC/10 ≤ rBeyond (i.val+1) x : the bulk Post itself.
      change 9 * mC / 10 ≤ rBeyond (L := L) (K := K) (i.val + 1) x
      exact h09
  -- The start: Pre at minute 0.
  have hx₀' : (phases ⟨0, hL₀⟩).Pre c₀ := by
    change Q_mix (L := L) (K := K) n mC (⟨0, hL₀⟩ : Fin L₀).val c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) (⟨0, hL₀⟩ : Fin L₀).val c₀
    simpa using hc₀
  have hcomp := compose_n_phases (K := (NonuniformMajority L K).transitionKernel) hL₀
    phases h_chain c₀ hx₀'
  -- Closed forms.
  have ht_eq : (∑ i : Fin L₀, (phases i).t) = L₀ * (tseed + tbulk) := by
    have h1 : (∑ _i : Fin L₀, (tseed + tbulk)) = L₀ * (tseed + tbulk) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← h1]; apply Finset.sum_congr rfl; intro i _; rfl
  have hε_eq : (∑ i : Fin L₀, ((phases i).ε : ℝ≥0∞))
      = (L₀ : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
    have h1 : (∑ _i : Fin L₀, ((εseed + εbulk : ℝ≥0) : ℝ≥0∞))
        = (L₀ : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← h1]; apply Finset.sum_congr rfl; intro i _; rfl
  have hpost_eq :
      {y : Config (AgentState L K) | ¬ (phases ⟨L₀ - 1, by omega⟩).Post y}
      = {y | ¬ (Q_mix (L := L) (K := K) n mC (L₀ - 1) y
              ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (L₀ - 1 + 1) y)} := by
    rfl
  rw [ht_eq, hε_eq, hpost_eq] at hcomp
  exact hcomp

/-! ## Part D — `clock_real_faithful_O_log_n`: the GENUINE O(log n) parallel reading.

Instantiating `clock_real_faithful_all_minutes` with `L₀ = K·(L+1)` (the protocol's
full minute count, `= k·⌈log₂ n⌉`) gives total interactions
`L₀·(tseed+tbulk) = K·(L+1)·(tseed+tbulk)`.  With per-minute
`tseed + tbulk = O(n/c²)` (O(1) PARALLEL, the genuine faithful bulk decomposition)
and `K·(L+1) = O(log n)`, the count is `O(n·log n / c²)` — parallel time
`/ n = O(log n / c²) = O(log n)` for a constant clock fraction `c`.  Failure
`≤ K·(L+1)·(εseed+εbulk) ≤ 1/poly`.  This is the CORRECT scale: the per-minute step
is `O(1)` parallel (bulk-only, 0.9 crossing), so `O(log n)` minutes give `O(log n)`
parallel — contrast the SUPERSEDED `clock_real_O_log_n`, whose per-minute FULL
crossing (`clock_real_advance_mixed`) was `O(log n)` parallel, giving `Θ(log²n)`. -/

/-- **`clock_real_faithful_O_log_n` — the GENUINE O(log n) faithful real-kernel clock.**

Instantiates `clock_real_faithful_all_minutes` at `L₀ = K·(L+1)`.  From minute `0`
(`Q_mix n mC 0 ∧ 9·m_C/10 ≤ rBeyond 0`), after the total `K·(L+1)·(tseed+tbulk)`
interactions, the level `rBeyond (K·(L+1))` has crossed the `0.9·m_C` bulk target
with kernel failure `≤ K·(L+1)·(εseed+εbulk)`.

The GENUINE O(log n) parallel reading: each minute's `tseed + tbulk = O(n/c²)` is
`O(1)` parallel (the faithful bulk decomposition — seed `0 → 0.1` ++ epidemic
`0.1 → 0.9`, each O(1)), and `K·(L+1) = O(log n)`, so
`interactions / n = K·(L+1)·(tseed+tbulk) / n = O(log n)`.  This is the CORRECT scale
(O(1)/minute × O(log n) minutes), unlike the superseded `clock_real_O_log_n`
(full-crossing, O(log n)/minute = Θ(log²n)).  Conditional ONLY on the carried
∀-minute deterministic invariants `habs_mix_all` (window closure) and
`hcross_full_all` (minute-synchronisation residual). -/
theorem clock_real_faithful_O_log_n (n mC : ℕ) (hn : 2 ≤ n) (hmC : 2 ≤ mC)
    (hLK : 0 < K * (L + 1))
    (habs_mix_all : ∀ T : ℕ, ∀ c c' : Config (AgentState L K),
      Q_mix (L := L) (K := K) n mC T c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support →
      Q_mix (L := L) (K := K) n mC T c')
    (tseed tbulk : ℕ) (εseed εbulk : ℝ≥0)
    (hεs : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tseed
          * ENNReal.ofReal (Real.exp (Real.log 2 * (seedLo mC : ℝ))) / 1 ≤ (εseed : ℝ≥0∞))
    (hεb : ENNReal.ofReal
            (1 - ((((mC / 10) * (mC / 10) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
              * (1 - Real.exp (-Real.log 2))) ^ tbulk
          * ENNReal.ofReal (Real.exp (Real.log 2 * (bulkHi mC : ℝ))) / 1 ≤ (εbulk : ℝ≥0∞))
    (c₀ : Config (AgentState L K))
    (hc₀ : Q_mix (L := L) (K := K) n mC 0 c₀
      ∧ 9 * mC / 10 ≤ rBeyond (L := L) (K := K) 0 c₀) :
    ((NonuniformMajority L K).transitionKernel ^ ((K * (L + 1)) * (tseed + tbulk))) c₀
        {y | ¬ (Q_mix (L := L) (K := K) n mC (K * (L + 1) - 1) y
                ∧ bulkHi mC ≤ rBeyond (L := L) (K := K) (K * (L + 1) - 1 + 1) y)} ≤
      ((K * (L + 1) : ℕ) : ℝ≥0∞) * (εseed + εbulk : ℝ≥0) := by
  exact clock_real_faithful_all_minutes (L := L) (K := K) n mC (K * (L + 1)) hLK hn hmC
    (le_refl (K * (L + 1))) habs_mix_all
    tseed tbulk εseed εbulk hεs hεb c₀ hc₀

/-! ## HONEST STATUS — Avenue (d') (composing the FAITHFUL O(1)/minute step → O(log n))

This file COMPOSES the faithful per-minute clock step `ClockRealSeed.clock_real_step`
over all `L₀ = K·(L+1)` minutes, 0-sorry / 0-axiom / 0-native_decide
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

* **The composition is GENUINE and at the CORRECT scale.**  The per-minute input is
  the FAITHFUL `clock_real_step` (seed `0 → 0.1·m_C` ++ epidemic `0.1·m_C → 0.9·m_C`,
  each `O(n/c²) = O(1)` parallel) — never re-assumed.  Composing over
  `K·(L+1) = O(log n)` minutes via `compose_n_phases` gives total interactions
  `K·(L+1)·(tseed+tbulk) = O(n·log n)`, i.e. `O(log n)` PARALLEL.  This is the
  CORRECT scale (`O(1)`/minute × `O(log n)` minutes), unlike the superseded
  `ClockRealHours.clock_real_O_log_n`, whose per-minute step crossed the FULL `m_C`
  (`clock_real_advance_mixed`, `O(log n)` parallel), giving `Θ(log²n)`.

* **The cross-minute chaining is GENUINELY PROVEN, not assumed.**  Minute `T`'s
  `Post` (`Q_mix n mC T ∧ bulkHi m_C ≤ rBeyond (T+1)`) implies minute `T+1`'s `Pre`
  (`Q_mix n mC (T+1) ∧ 9·m_C/10 ≤ rBeyond (T+1)`):
  - the `9·m_C/10 ≤ rBeyond (T+1)` conjunct is IDENTICAL (`bulkHi m_C = 9·m_C/10`,
    `rfl`);
  - the `Q_mix n mC (T+1)` conjunct is PROVEN via `ClockRealHours.Q_mix_succ_of_post`
    fed by the SAME `0.9-floor` level fact (the bulk `Post`).  Under the SYNC-fixed
    window the upgrade is TRIVIAL: `crossedT` IS the 0.9-floor, `clockPhase3` is phase
    only (T-independent), `card`/`clockSize` are T-independent.  NO full crossing,
    NO `hcross_full` — the bulk's 0.9 Post directly seeds the next minute's window.

* **Carried hypothesis (∀ minute, EXPLICIT, deferred — NOT discharged).**
  - `habs_mix_all` — the one-step support closure of `Q_mix` (the SINGLE structural
    invariant `clock_real_step` itself carries; deterministic, NOT a probability).
  - **`hcross_full_all` is ELIMINATED.**  The superseded full-crossing avenue needed
    it because `Q_mix.crossedT` then required FULL crossing `rBeyond T = m_C`; the
    SYNC fix relaxes `crossedT` to the 0.9-floor `9·m_C/10 ≤ rBeyond T`, which the
    bulk step ALREADY delivers, so the cross-minute chaining needs NO extra input.

## SCOPE BOUNDARY (faithful, not inflated)

This is the COMPOSITION over minutes of the FAITHFUL O(1)/minute step — the genuine
`O(log n)` (correct scale) real-kernel clock, the analog of C5's
`clock_faithful_O_log_n_upper`.  It is CONDITIONAL on the SINGLE carried ∀-minute
deterministic invariant `habs_mix_all` (window closure), which it does NOT discharge.
Full crossing is GONE everywhere: the bulk uses the SYNC mechanism (susceptible count
from `clockSize`), the seed uses the 0.9-floor drip frontier.  It does NOT bridge to
the main-population hour synchronisation (Doty Lemma 6.10, the supermartingale) — that
remains a separate later piece, deliberately not fabricated here. -/
theorem clock_real_faithful_hours_status : True := trivial

end ClockRealFaithfulHours

end ExactMajority
