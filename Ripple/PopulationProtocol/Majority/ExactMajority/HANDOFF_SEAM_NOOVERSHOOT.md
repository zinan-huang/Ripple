# HANDOFF: hNoOvershoot via seam-generalized Phase0Window (family3 letter, task f68ca4be, 2026-06-10)

Source: ChatGPT Pro (family3, Ripple connector on opus-wip). Delivered 20,641 B via bridge (sync path). Verbatim answer below.

---

I’ll check the frozen transition rule first, then trace how SeamEpidemics, Phase0Window, and CounterTimeout expect the no-overshoot tail to be packaged.

The transition mechanism is now clear enough to rule out the “any participation increments counter” interpretation: counters decrement only through stdCounterSubroutine, and in timed work phases that is applied only to Clock-role agents. Phase 3 additionally gates counter decrement by a clock-clock pair at max minute.

The seam file confirms another integration issue: seamEpidemicW currently budgets εovershoot but its convergence proof only uses hDrift; the exact-window bridge still wants a pointwise no-overshoot predicate. So the discharge should either strengthen the seam Post or add a probabilistic exactification phase.

1. Exact transition mechanism: the important corrections

The counter does not climb from 0 to counterMax. It counts down. The frozen rule is:

lean
def stdCounterSubroutine (a : AgentState L K) : AgentState L K :=
  if h : a.counter.val = 0 then
    advancePhaseWithInit L K a
  else
    { a with counter := ⟨a.counter.val - 1, by omega⟩ }

So to advance from phase q to q+1, a clock must first be driven down to counter 0; the next call to stdCounterSubroutine advances it via advancePhaseWithInit. 

Transition

advancePhaseWithInit is only

lean
let b := advancePhase L K a
phaseInit L K b.phase b

so the normal counter-driven move is a one-phase advance followed by the destination phase’s initialization. There is no direct q → q+2 branch inside stdCounterSubroutine. 

Transition

However, two caveats matter for hNoOvershoot.

First, the global dispatcher starts with the phase epidemic:

lean
let p := max s.phase t.phase
let s' := runInitsBetween L K s.phase.val p.val { s with phase := p }
let t' := runInitsBetween L K t.phase.val p.val { t with phase := p }

so an already-existing phase p+2 agent would immediately spread p+2 by max-phase epidemic. Thus hNoOvershoot must be formulated as “no first local creation of phase ≥ p+2 occurs,” not merely “no agent copies it.” 

Transition

Second, phaseInit can send bad configurations to phase 10; the repo already treats phase 10 as an error/backup phase. So NoOvershoot p := ∀ a∈c, a.phase.val < p+2 also excludes accidental phase-10 entry during the seam.

The tick mechanism is not uniform across all phases:

Phase 0: a fresh Clock is created by CR–CR with counter 50*(L+1), and the counter subroutine runs only on Clock–Clock pairs. 

Transition

Phase 1: clockCounterStep runs stdCounterSubroutine on a Clock and leaves non-Clocks unchanged; Phase 1 applies it to both agents after averaging. Thus a Clock ticks whenever it participates in a Phase-1 interaction, not only Clock–Clock. 

Transition

Phase 3: the minute clock is special. Clock–Clock pairs first synchronize minutes, then increment minutes up to K*(L+1), and only at the hour boundary do both clocks run stdCounterSubroutine. 

Transition

Phases 5–8: after the phase-specific work rule, Clock agents run stdCounterSubroutine directly. For example Phase 5 does this on both outputs, and Phase 5’s zero-counter clocks advance to Phase 6. 

Transition

 Phase 6/7/8 follow the same “if role is clock, run the counter subroutine” pattern. 

Transition

 

Transition

 

Transition

So the honest correction is:

For phases 1,5,6,7,8:
  a risky clock tick is dominated by “this clock participates”.

For phase 3:
  a risky clock tick is much rarer, gated by the minute/hour mechanism,
  but participation domination is still a valid upper bound.

For phase 0:
  Phase0Window already proves the corresponding early-exit pattern.

Also, 50*(L+1) is not a constant in n in the intended nonuniform setting; L ≈ log₂ n, so the counter height is Θ(log n). The bare participation tail is therefore viable when the seam length is ≤ C·n·(L+1) with C well below the counter constant 50.

2. Which existing engine should discharge hNoOvershoot?

Use the Phase0Window early-time potential pattern, not CounterTimeout.

CounterTimeout.lean is the finish-time wrapper: it proves that a phase finishes within C·n log n interactions from a per-block failure contraction. Its central theorem is:

lean
theorem counterTimeout_tail
    ...
    (hblock : ∀ b ∈ (Doneᶜ : Set Ω), (K ^ s) b Doneᶜ ≤ q)
    ...
    (K ^ (numBlocks * s)) c₀ Doneᶜ ≤ q ^ numBlocks

That is the wrong direction for hNoOvershoot; hNoOvershoot is an early finish is unlikely statement. 

CounterTimeout

The right pattern is Phase0Window.lean. It already explains the intended early-time proof:

Φ_s c := ∑_{a clock} exp(−s · a.counter)

and uses the fact that one tick multiplies the summand by e^s, yielding an affine drift of the form

∫ Φ_s dK(c) ≤ (1 + 2(e^s − 1)/n) · Φ_s c + fresh

The file states exactly this mechanism and its numerics: with s = 1, t ≤ n*(L+1), and initial potential ≤ n*exp(-50*(L+1)), the tail is at most exp(-45*(L+1)). 

Phase0Window

The already-proved affine drift theorem is Phase-0-specific:

lean
theorem clockCounterPotential_drift_affine
    ...
    ∫⁻ c', clockCounterPotential s c' ∂K c
      ≤ ofReal (1 + 2 * (exp s - 1) / n) * clockCounterPotential s c
        + ofReal (exp (-(s * (50 * (L + 1)))))

Phase0Window

and the generic affine tail wrapper is:

lean
theorem phase0_window_tail_affine
    ...
    (P.transitionKernel ^ t) c₀ {c | ¬ Post c}
      ≤ (a ^ t * Φ c₀ + b * ∑ i ∈ Finset.range t, a ^ i) / θ

Phase0Window

So the design should be a generic seam-counter analogue of Phase0Window, not a new binomial library and not the finish-time CounterTimeout wrapper.

3. Does this consume a width event? Usually no.

For the hNoOvershoot tail, do not consume the phase-clock width machinery unless you want a sharper, paper-faithful Phase-3-only proof.

A safe and simpler domination is:

actual counter decrement ⊆ clock participation

For phases 1,5,6,7,8 this is essentially tight: a Clock ticks when it participates in that phase’s transition. For Phase 3, the actual counter decrement is rarer because it waits for the hour boundary; bounding it by participation is conservative but sufficient if the seam horizon constant is small compared with 50.

This avoids a dependency cycle with the §6 width/front machinery. The seam Pre does not need to carry a clock-width event merely to prove no overshoot. Width remains part of Phase 3’s own work-phase convergence, not the seam timing separation.

The only real quantitative condition needed by this route is the same shape as DotyTimeHeadline already abstracts:

lean
(phases i).t ≤ Cphase i * n * (L + 1)

For the seam-corrected headline, the 21-instance theorem abstracts all times by Cphase : Fin 21 → ℕ and concludes total time ≤ 21*C0*n*(L+1) if every Cphase i ≤ C0; it does not hard-code a numeric seam length in the file. 

DotyTimeHeadline

So the honest constants should be packaged as a hypothesis:

lean
ht_seam : tseam ≤ Cseam * n * (L + 1)
hCseam : Cseam ≤ Csafe

where Csafe is the arithmetic constant for the no-overshoot tail. If you want to reuse Phase0Window’s existing numeric lemma directly, take the clean special case:

lean
ht_seam : tseam ≤ n * (L + 1)

because phase0_numerics_real already closes that case to exp(-45*(L+1)). 

Phase0Window

That tail is far smaller than a per-seam O(1/n²) budget once L+1 dominates log n; union over 10 seams or even 21 instances is harmless.

4. Integration issue in the current seam file

SeamEpidemics.seamEpidemicW currently includes εovershoot in the declared error:

lean
ε := εepidemic + εovershoot

but the convergence proof only uses hDrift to bound failure of allPhaseGe (p+1). The εovershoot is added by le_self_add; no hNoOvershoot tail is consumed there. 

SeamEpidemics

Then the exact-work bridge still expects a pointwise no-overshoot input:

lean
theorem seam_into_exact_work
    {p n : ℕ} (hno : ∀ c,
        allPhaseGe (p + 1) n c → ∀ a ∈ c, a.phase.val < p + 2) :
    ∀ c, allPhaseGe (p + 1) n c →
      allPhaseEq (p + 1) n c

SeamEpidemics

So there is a small architectural fix needed. The cleanest one is to define a strengthened seam whose Post includes no-overshoot:

lean
Post c :=
  allPhaseGe (p+1) n c ∧ NoOvershoot p c

and prove its convergence by union bound:

P(¬(allPhaseGe ∧ NoOvershoot))
  ≤ P(¬ allPhaseGe) + P(¬ NoOvershoot)
  ≤ εepidemic + εovershoot.

Then seam_into_exact_work becomes pointwise from the strengthened Post.

5. Target definitions

I would add these to SeamEpidemics.lean or a new file Probability/SeamNoOvershoot.lean.

lean
namespace ExactMajority
namespace SeamNoOvershoot

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-- No agent has run ahead two phases during the seam from `p` to `p+1`. -/
def NoOvershoot (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val < p + 2

/-- The dangerous precursor: an at-risk clock in the new phase already has counter zero. -/
def AtRiskClockZero (p : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∃ a ∈ c, a.role = .clock ∧ a.phase.val = p + 1 ∧ a.counter.val = 0

/-- At-risk clock-counter summand for the seam from `p` to `p+1`. -/
noncomputable def seamClockSummand (p : ℕ) (s : ℝ) (a : AgentState L K) : ℝ≥0∞ :=
  if a.role = .clock ∧ a.phase.val = p + 1 then
    ENNReal.ofReal (Real.exp (-(s * (a.counter.val : ℝ))))
  else
    0

/-- At-risk clock-counter potential. -/
noncomputable def seamClockPotential (p : ℕ) (s : ℝ)
    (c : Config (AgentState L K)) : ℝ≥0∞ :=
  Config.sumOf (seamClockSummand (L := L) (K := K) p s) c

The threshold link is the direct analogue of Phase0Window:

lean
theorem seamClockPotential_ge_one_of_atRiskClockZero
    (p : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (h : AtRiskClockZero (L := L) (K := K) p c) :
    1 ≤ seamClockPotential (L := L) (K := K) p s c := by
  -- same proof shape as
  -- Phase0Window.clockCounterPotential_ge_one_of_clock_counter_zero
  sorry

The proof should literally clone clockCounterPotential_ge_one_of_clock_counter_zero, changing the summand predicate from “role is clock” to “role is clock and phase is p+1.” The original threshold lemma is already proved for phase 0. 

Phase0Window

6. Deterministic bridge: overshoot requires a zero-risk clock, except for named untimed/error guards

For timed seams, the key deterministic target is:

lean
/--
If a one-step update from a no-overshoot seam state creates an agent at phase ≥ p+2,
then before the step there was an at-risk phase-(p+1) clock with counter zero.

This is the seam analogue of `Phase0Window.det_phase0_exit`.
-/
theorem det_seam_overshoot_of_atRiskClockZero
    (p : ℕ) (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hno : NoOvershoot (L := L) (K := K) p c)
    (hge : SeamEpidemics.allPhaseGe (L := L) (K := K) p (Multiset.card c) c)
    (hexit : ¬ NoOvershoot (L := L) (K := K) p
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)) :
    AtRiskClockZero (L := L) (K := K) p c := by
  -- Reduce to the first output whose phase is ≥ p+2.
  -- Use:
  --   stdCounterSubroutine: zero branch is the only counter-driven advance.
  --   advancePhaseWithInit: advances by one before init.
  --   phaseEpidemicUpdate: max-copy cannot create p+2 unless p+2 already existed,
  --     which hno excludes.
  sorry

This is the exact analogue of the existing Phase-0 deterministic bridge:

lean
theorem det_phase0_exit
    ...
    (hexit : ¬ allPhase0 (Protocol.stepOrSelf ... c r₁ r₂)) :
    ¬ noClockAtZero c

Phase0Window

But I would not pretend this theorem is universally true for every p without side conditions. Phase 2 can advance to Phase 3 by its opinion-union rule, not by a counter, and Phase 4 can advance by the big-bias rule. Phase 2’s transition explicitly advances both agents to Phase 3 when both signs are still present. 

Transition

 Phase 4 advances both agents when a big bias is detected. 

Transition

So the theorem should either be restricted to timed destination phases:

lean
def CounterTimedPhase (q : ℕ) : Prop :=
  q = 1 ∨ q = 3 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8

or carry a named hypothesis excluding untimed local-advance guards:

lean
UntimedNoLocalAdvance p c

For the time-half campaign, I recommend the first route: discharge hNoOvershoot by this counter argument only for seams whose destination work phase is counter-timed; handle Phase-2/4/9 seams with their specific work-phase guard facts, not with the clock-counter lemma.

7. Probabilistic tail target

The drift lemma should be the seam analogue of clockCounterPotential_drift_affine:

lean
/--
One-step affine drift for the at-risk seam counter potential.

`fresh` accounts for a phase-p Clock being infected by the phase-(p+1)
epidemic and entering phase p+1 with a full counter.  A safe bound is
`2 * exp(-s * 50(L+1))`; it can likely be sharpened to `1 * ...`.
-/
theorem seamClockPotential_drift_affine
    (p : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (n : ℕ) (c : Config (AgentState L K))
    (hcard : Multiset.card c = n) (hc2 : 2 ≤ Multiset.card c)
    (hwin : SeamEpidemics.allPhaseGe (L := L) (K := K) p n c)
    (hno : NoOvershoot (L := L) (K := K) p c) :
    ∫⁻ c', seamClockPotential (L := L) (K := K) p s c'
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal (1 + 2 * (Real.exp s - 1) / (n : ℝ))
          * seamClockPotential (L := L) (K := K) p s c
        + ENNReal.ofReal (2 * Real.exp (-(s * (50 * (L + 1) : ℕ)))) := by
  -- Clone Phase0Window.clockCounterPotential_drift_affine.
  -- The pair-sum infrastructure already exists:
  --   Phase0Window.lintegral_transitionKernel_eq_sum
  -- The per-pair lemma is new:
  --   seamClockPotential_stepOrSelf_le
  sorry

This proof should reuse the pair-sum infrastructure from Phase0Window:

lean
lintegral_transitionKernel_eq_sum

which expands one-step expectation as a finite ordered-pair sum. 

Phase0Window

Then state the tail:

lean
/--
Early-overshoot precursor tail: probability of seeing an at-risk zero clock
within the seam.
-/
theorem seam_atRiskClockZero_tail
    (p n tseam : ℕ) (s : ℝ)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (hn : 1 ≤ n)
    (ht : tseam ≤ n * (L + 1))
    {c₀ : Config (AgentState L K)}
    (hcard₀ : Multiset.card c₀ = n)
    (hpre₀ : SeamEpidemics.allPhaseGe (L := L) (K := K) p n c₀)
    (hno₀ : NoOvershoot (L := L) (K := K) p c₀)
    (hinitΦ :
      seamClockPotential (L := L) (K := K) p 1 c₀
        ≤ (n : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(50 * (L + 1) : ℕ)))) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
      {c | AtRiskClockZero (L := L) (K := K) p c}
      ≤ ENNReal.ofReal (Real.exp (-(40 * (L + 1) : ℕ))) := by
  -- Use Phase0Window.phase0_window_tail_affine with:
  --   Φ := seamClockPotential p 1
  --   Post := fun c => ¬ AtRiskClockZero p c
  --   θ := 1
  --   a := ofReal (1 + 2*(exp 1 - 1)/n)
  --   b := ofReal (2*exp(-50*(L+1)))
  -- Then discharge arithmetic with a new numerics lemma.
  sorry

I used 40 instead of 45 because the seam version has possible epidemic “fresh clock” immigration; the exact exponent depends on whether the per-pair fresh term is 1*M or 2*M. The existing Phase-0 arithmetic closes 45; the seam version should get something like 40 without stress.

Name the new arithmetic target explicitly:

lean
theorem seam_noOvershoot_numerics_real
    (n L tseam : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (ht : tseam ≤ n * (L + 1)) :
    -- affine tail expression with b = 2*exp(-50(L+1))
    ... ≤ Real.exp (-(40 * (L + 1 : ℕ))) := by
  -- clone Phase0Window.phase0_numerics_real, with the extra affine immigration sum
  sorry

The existing numeric lemma to clone is phase0_numerics_real. 

Phase0Window

Finally, convert zero-clock precursor to actual no-overshoot:

lean
/--
Terminal no-overshoot tail for one seam.
Because phase is monotone, any terminal overshoot has a first step;
the first-step bridge turns that step into an earlier `AtRiskClockZero`.
-/
theorem seam_noOvershoot_tail
    (p n tseam : ℕ)
    (hCounterTimed : CounterTimedSeam p)
    (hlog : Real.log (n : ℝ) ≤ (L + 1 : ℕ))
    (hn : 1 ≤ n)
    (ht : tseam ≤ n * (L + 1))
    {c₀ : Config (AgentState L K)}
    (hpre₀ : SeamEpidemics.allPhaseGe (L := L) (K := K) p n c₀)
    (hno₀ : NoOvershoot (L := L) (K := K) p c₀)
    (hinitΦ : ... ) :
    ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
      {c | ¬ NoOvershoot (L := L) (K := K) p c}
      ≤ ENNReal.ofReal (Real.exp (-(39 * (L + 1 : ℕ)))) := by
  -- prefix-union from first overshoot step
  -- + seam_atRiskClockZero_tail at each prefix time
  -- or use killed-gate version to avoid explicit prefix sum.
  sorry

For the final hNoOvershoot budget consumed by the 21-instance headline, wrap it as:

lean
theorem hNoOvershoot_one_seam
    (p n tseam : ℕ)
    (εovershoot : ℝ≥0)
    ...
    (hε :
      ENNReal.ofReal (Real.exp (-(39 * (L + 1 : ℕ)))
        ≤ (εovershoot : ℝ≥0∞)) :
    ∀ c₀,
      SeamEpidemics.allPhaseGe (L := L) (K := K) p n c₀ →
      NoOvershoot (L := L) (K := K) p c₀ →
      ((NonuniformMajority L K).transitionKernel ^ tseam) c₀
        {c | ¬ NoOvershoot (L := L) (K := K) p c}
        ≤ (εovershoot : ℝ≥0∞) := by
  intro c₀ hge hno
  exact le_trans (seam_noOvershoot_tail ... hge hno ...)
    hε
8. Strengthened seam instance to actually consume hNoOvershoot

I would replace or supplement seamEpidemicW with:

lean
noncomputable def seamEpidemicExactW
    (p n tseam : ℕ) (εepidemic εovershoot : ℝ≥0)
    (hDrift : ∀ c,
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'}
          ≤ (εepidemic : ℝ≥0∞))
    (hNoOvershoot : ∀ c,
        (SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
          SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c) →
        ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ NoOvershoot (L := L) (K := K) p c'}
          ≤ (εovershoot : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c =>
    SeamEpidemics.allPhaseGe (L := L) (K := K) p n c ∧
      SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c
  Post := fun c =>
    SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
      NoOvershoot (L := L) (K := K) p c
  t := tseam
  ε := εepidemic + εovershoot
  convergence := by
    intro c hPre
    have hA := hDrift c hPre
    have hB := hNoOvershoot c hPre
    -- {¬ (A ∧ B)} ⊆ {¬A} ∪ {¬B}
    calc
      ((NonuniformMajority L K).transitionKernel ^ tseam) c
          {c' | ¬ (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c' ∧
                   NoOvershoot (L := L) (K := K) p c')}
        ≤ ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c'} +
          ((NonuniformMajority L K).transitionKernel ^ tseam) c
            {c' | ¬ NoOvershoot (L := L) (K := K) p c'} := by
          exact measure_mono_union_not_and -- new tiny set lemma, or inline `measure_union_le`
      _ ≤ (εepidemic : ℝ≥0∞) + (εovershoot : ℝ≥0∞) := by
          gcongr
      _ = ((εepidemic + εovershoot : ℝ≥0) : ℝ≥0∞) := by
          push_cast; rfl

Then the bridge becomes deterministic:

lean
theorem seamExact_into_exact_work
    {p n : ℕ} :
    ∀ c,
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (p + 1) n c ∧
        NoOvershoot (L := L) (K := K) p c) →
      SeamEpidemics.allPhaseEq (L := L) (K := K) (p + 1) n c :=
  fun c h =>
    SeamEpidemics.allPhaseEq_of_ge_and_no_overshoot h.1 h.2

This aligns with the doty_time_headline_W2 description: the corrected 21-instance interleave uses seam phases; seam-to-work exactness relies on no overshoot; and εovershoot/hNoOvershoot is supposed to be folded into the seam instance. 

DotyTimeHeadline

Final recommendation

Discharge hNoOvershoot with a seam-generalized Phase0Window, not with the finish-time CounterTimeout engine and not with a phase-clock width dependency.

The minimal new atoms are:

NoOvershoot, AtRiskClockZero, seamClockPotential.

seamClockPotential_drift_affine, cloned from clockCounterPotential_drift_affine.

det_seam_overshoot_of_atRiskClockZero, cloned conceptually from det_phase0_exit, but restricted to counter-timed seams or guarded against untimed local-advance phases.

seam_noOvershoot_numerics_real, cloned from phase0_numerics_real.

seamEpidemicExactW, so the probabilistic hNoOvershoot is actually consumed by the seam convergence, rather than appearing only as an unused εovershoot plus a pointwise bridge assumption.

---

## STATUS — DELIVERED 2026-06-10 (opus, single-line)

`Probability/SeamNoOvershoot.lean` built (uisai2 /dev/shm, lean v4.30.0, single-file
EXIT_0); every headline `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`;
0 sorry / 0 admit / 0 native_decide / 0 added axiom.  Five stages, one commit each
(951472b, 7895564, b0d472b, a37968e, 637a0a9 on `main`; mirrored to opus-wip).

DELIVERED (all 0-sorry, axiom-clean):
- **Stage 1**: `NoOvershoot`, `AtRiskClockZero`, `seamClockSummand`,
  `seamClockPotential`, `seamClockPotential_ge_one_of_atRiskClockZero` (threshold,
  predicate = clock ∧ phase = p+1).
- **Stage 2**: `CounterTimedPhase` (HONEST set, see correction below),
  `DetSeamOvershootBridge` (deterministic overshoot→at-risk bridge, carried as a named
  structural fact + kernel-form `transitionKernel_not_noOvershoot_eq_zero`).
- **Stage 3**: `seamClockPotential_{eq_base_add_pair, stepOrSelf_eq_base_add_pair,
  stepOrSelf_le}`, `seamClockPotential_drift_affine` (affine drift, clone of
  `clockCounterPotential_drift_affine` via `lintegral_transitionKernel_eq_sum` +
  `sum_fst/snd_interactionProb`; per-pair output bound carried as `hpair`).
- **Stage 4**: `seam_noOvershoot_numerics_real` (e^{−40(L+1)} with the 2M immigration
  sum), `cardWindow_absorbing`, `seam_atRiskClockZero_tail` (wires
  `phase0_window_tail_affine`: Φ = seamClockPotential p 1, Post = ¬AtRiskClockZero,
  θ = 1, card-n absorbing window).
- **Stage 5**: `noOvershoot_window_le_prefix_sum` (via `prefix_union_first_exit`),
  `seam_noOvershoot_tail` (t·e^{−40(L+1)}), `hNoOvershoot_one_seam` (budget wrapper),
  **`seamEpidemicExactW`** (THE INTEGRATION FIX: Post = allPhaseGe (p+1) ∧ NoOvershoot,
  ε = εepidemic + εovershoot consumed by union bound), `seamExact_into_exact_work`
  (deterministic, no per-seam side input).

### Blueprint claims wrong vs repo (verified against FROZEN `Transition.lean`)

1. **`CounterTimedPhase` is `{1,5,6,7,8}`, NOT `{1,3,5,6,7,8}`.**  Phase 3 IS
   counter-timed, but `phaseInit 3` does NOT reset the clock counter on entry (it sets
   `minute`), so a fresh phase-3 clock can enter with counter 0 (summand up to 1, not
   M = e^{−s·50(L+1)}), breaking the affine immigration tail.  `phaseInit` resets the
   counter to full exactly for `{1,5,6,7,8}`.  Phase 3's no-overshoot must come from the
   minute/hour width machinery, not this generic clock-counter lemma.
2. **The deterministic bridge is FALSE without a well-formedness side condition
   (error-to-10 path).**  `phaseInit 1` sends an `mcr` agent to phase 10
   (`enterPhase10`); an `mcr` epidemic-dragged into phase 1 overshoots to phase 10 ≥ p+2
   with NO counter-0 clock involved.  The honest bridge needs the seam Pre's
   well-formedness (no remaining `mcr`, in-range biases) so `phaseInit` does not error —
   exactly the `validInitial`/quota invariants from the Analysis layer.  `DetSeamOvershootBridge`
   is carried as a named hypothesis to be discharged per-seam from those invariants
   (full per-phase upper-bound case analysis through epidemic + 11-phase dispatcher +
   finishPhase10Entry is the same magnitude as the existing `Transition_*_phase_le_two_*`
   lemmas and is out of scope for this seam file).

### How phases 2/3/4/9/10 seams are left

- **Phases 2, 4, 9** (untimed: opinion-union / big-bias advance): EXCLUDED from
  `CounterTimedPhase`; their seam no-overshoot is handled by their own work-phase
  guards, not this lemma.
- **Phase 3** (counter-timed but no counter reset on entry): EXCLUDED; needs the
  minute/hour width machinery (`ClockOLogN`/`ClockReal*`).
- **Phase 10** (backup, no phase advance): not a seam destination in this scheme.

### Two named carried facts (after a real attack, per discipline)

- `hpair` (per-pair output bound, seam analogue of `clockSummand_pair_le`): the
  protocol-structural per-pair fact for a counter-RESET destination phase; supplied to
  the drift/tail.  Discharging it = the seam analogue of Phase0Window's
  `clockSummand_pair_le` case analysis restricted to `{1,5,6,7,8}`.
- `DetSeamOvershootBridge p` (deterministic overshoot bridge): carried for the reason
  in claim 2 above (needs well-formedness; full dispatcher case analysis out of scope).

Everything else (the affine drift engine, the numerics, the prefix-union tail
assembly, the union-bound integration fix, the deterministic exact-work bridge) is
fully proven and consumable.  The integration bug (`seamEpidemicW`'s unused
`εovershoot`) is FIXED by `seamEpidemicExactW`.

---

## STATUS UPDATE 2026-06-10 — `hpair` protocol-core BUILT in `Probability/SeamPairBound.lean` (0-sorry, axiom-clean)

The protocol-structural core behind the carried `hpair` is now proven (new file only; no edit to
`SeamNoOvershoot.lean`). All headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`,
no `native_decide`/`sorry`. See `DOTY_POST63_CAMPAIGN.md §SeamPairBound` for the full lemma list.

**Headline proven:** `seamClockSummand_Transition_left_le_of_ep_at_dest` — the honest per-side output
bound in the no-advance regime: `summand((Transition a b).1) ≤ eˢ · (summand(a) + freshVal)`, via the full
chain (finishPhase10-strip → dispatch decrement → epidemic immigration). Supporting: the decrement bound,
the epidemic immigration summand bound (`runInitsBetween` reset through the fold), the counter-advance
immigration reset, and the per-phase dispatch left-clock reductions for `{1,5,6,7,8}`.

**TWO FINDINGS (genuine attack — both AMEND this blueprint):**

1. **The carried `hpair` constant `2·freshVal` is FALSE for `s > 0`.** A fresh epidemic-dragged clock
   enters `p+1` at FULL counter and is DECREMENTED by the same-step dispatch to `full−1`; its summand is
   `eˢ·freshVal`, not `freshVal`. Honest per-pair immigration ceiling = `2·eˢ·freshVal`. Downstream-benign:
   `seam_noOvershoot_numerics_real` has `e^{−45}+e^{−43}→e^{−40}` slack, so `b = 2·e·freshVal` still closes.
   **Action item:** re-state `hpair` (and `seamClockPotential_stepOrSelf_le` / `…_drift_affine` /
   `seam_atRiskClockZero_tail`) with `2·eˢ·freshVal`.

2. **Phase 5 must be EXCLUDED too (parallels phase 3).** `Phase4Transition` advances clocks via
   `advancePhase` (NO `phaseInit`, NO counter reset), so a clock counter-advanced from phase 4 into phase 5
   keeps its old counter (summand up to 1, not `freshVal`), breaking the immigration tail. **The fully-honest
   counter-reset destination set is `{1,6,7,8}`, NOT `{1,5,6,7,8}`** (blueprint's `CounterTimedPhase`).
   Phase 5's no-overshoot, like phase 3's, must come from the minute/hour width machinery.

**Residual (precisely isolated):** the phase-ADVANCE-regime per-side bound for `{1,6,7,8}` needs the
`Phase0Transition` left-clock reduction packaged (Phase{5,6,7} are done; the advance-reset lemma
`seamClockSummand_stdCounterSubroutine_advance` is proven). The full exact-`hpair` adapter is NOT
deliverable as stated (findings 1+2); the honest adapter targets `2·eˢ·freshVal` over `{1,6,7,8}`.

## STATUS UPDATE 2026-06-10 — `SeamPairAdapter.lean` COMPLETE (Stages 1–4, 0-sorry, axiom-clean)

The honest adapter is fully built in `Probability/SeamPairAdapter.lean` (append-only; NO edit to
`SeamNoOvershoot.lean` or `SeamPairBound.lean`). Single-file `lake env lean … SeamPairAdapter.lean`
EXIT 0; all headlines `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; no
`native_decide`/`sorry`/`admit`/`axiom`. Both findings above are now DISCHARGED honestly.

- **Stage 1** (commit a4c7e477): ADVANCE-regime dispatch reductions for `{1,6,7,8}`
  (`Phase0Transition_{left,right}_clock_eq`, `Phase{5,6,7,8}Transition_right_clock`, the per-side
  advance bounds `seamClockSummand_Transition_{left,right}_le_of_ep_advance`, the RIGHT no-advance
  bound `…_right_le_of_ep_at_dest`, RIGHT epidemic immigration).
- **Stage 2** (commit d3c1cc22): the HONEST two-sided pair bound
  `seamClockSummand_Transition_pair_le`:
  `summand₁' + summand₂' ≤ eˢ·(summand₁+summand₂) + 2·(eˢ·freshVal)` — finding 1 corrected.
  Universal per-side bounds (`…_{left,right}_le_univ`) cover no-advance/advance/zero;
  `SeamRegimeDispatch p` packages the per-pair regime facts (the structural input).
- **Stage 3** (commit ab0fab2f): the HONEST config-level drift
  `seamClockPotential_drift_affine_honest`:
  `∫ Φ dK(c) ≤ ofReal(1+2(eˢ−1)/n)·Φ + 2·(eˢ·freshVal)`. Generic-immigration clones
  (`…_stepOrSelf_le_gen`, `…_drift_affine_gen`) reuse the public base-split +
  `lintegral_transitionKernel_eq_sum` infrastructure verbatim; instantiated at the Stage-2 constant.
- **Stage 4** (commit 1d347fad): the HONEST numerics `seam_noOvershoot_numerics_honest` (immigration
  `2·e·e^{−50(L+1)}`) STILL closes to **`e^{−40(L+1)}`** (predecessor optimism VERIFIED — the extra
  `e` factor moves term-2 from `−43(L+1)` to `−42(L+1)`, absorbed by the `−50→target` slack; the
  `2 ≤ e^{2(L+1)}` combine is unchanged). End-to-end: `seam_atRiskClockZero_tail_honest` (≤ e^{−40(L+1)}),
  `seam_noOvershoot_tail_honest`, `hNoOvershoot_one_seam_honest` — plugs into the SAME
  `seamEpidemicExactW` integration point with the corrected constant and the SAME bound.

**Finding 2 discharge:** `CounterResetDest q := q ∈ {1,6,7,8}` (the `def` in the adapter) is the honest
counter-reset set; `CounterTimedPhase_of_CounterResetDest` proves `{1,6,7,8} ⊆ {1,5,6,7,8}`. Excluded:
`{2,4,9}` untimed (opinion-union/big-bias), `{3,5}` counter-timed-but-no-reset (phase-3 init sets `minute`;
phase-5 predecessor `Phase4Transition` uses `advancePhase`). Their no-overshoot comes from the work-phase /
big-bias / minute-hour-width guards, NOT this clock-counter tail — documented in named doc sections, not faked.

**Honest two-sided constant proved:** `2·eˢ·freshVal` (per pair). **Numerics landed:** `e^{−40(L+1)}`
(no weakening needed). **Final hypothesis surface** (`hNoOvershoot_one_seam_honest`): seam `Pre` (threaded
to `NoOvershoot`-start + `card = n`) + `tseam ≤ n(L+1)` + `log n ≤ L+1` + initial-potential bound +
`CounterResetDest (p+1)` / `SeamRegimeDispatch p` / `DetSeamOvershootBridge p` structural guards + arithmetic.

---

## UPDATE (2026-06-10): `DetSeamOvershootBridge p` DISCHARGED under well-formedness `W`

`Probability/SeamOvershootBridge.lean` (append-only; imports `SeamPairAdapter`) PROVES the
deterministic bridge that the no-overshoot chain carried as the named guard `hdet`.

**The well-formedness predicate `W` (minimal, sufficient).**
`WfAgent a := a.role ≠ .mcr ∧ 2 ≤ a.smallBias.val ∧ a.smallBias.val ≤ 4`;
`Wf c := ∀ a ∈ c, WfAgent a`.  This closes EVERY `phaseInit` error-to-`10` branch on the
seam region: the only `enterPhase10` paths for `q ≤ 9` are `q=1 ∧ mcr` and
`q∈{2,9} ∧ (smallBias ≤ 1 ∨ ≥ 5)` (verified against FROZEN `phaseInit`), all excluded by
`WfAgent`; `phaseInit 10` is never invoked on a seam to `p+1 ≤ 8`.  `W` is one-step
preserved (`phaseInit_preserves_wf`, `runInitsBetween_preserves_wf`,
`phaseEpidemicUpdate_{left,right}_preserves_wf`): `phaseInit` preserves `smallBias`
(`phaseInit_smallBias_eq`) and never creates an `mcr` (its only role write is `cr→reserve`).
Provenance: phase-0 EXIT `RoleSplitStage2Good` gives `mcr = 0`, no rule re-creates `mcr` or
pushes `smallBias` out of `{2,3,4}`.

**The proof (honest per-phase case analysis, 0-sorry, axiom-clean).**
1. Per-phase LEFT/RIGHT `+1` bounds for phases `0–8` (`PhaseQTransition_{left,right}_phase_le_succ…`),
   threaded through `stdCounterSubroutine`/`advancePhaseWithInit`/`clockCounterStep` `≤ +1`
   (`…_of_wf` using `phaseInit_phase_eq_of_wf`, plus a clock-safe `…_of_clock` for the
   `cr→clock` Rule-5/Rule-1 advances at phases `0,3`).
2. Epidemic no-error phase identity under `W`: `ep.s.phase = max(a,b) ≤ p+1`
   (`phaseEpidemicUpdate_{left,right}_phase_eq_max_of_wf`).
3. Dispatcher `+1` bound: `(Transition a b).s.phase ≤ max(a,b)+1`
   (`Transition_{left,right}_phase_le_ep_succ_of_wf`, `interval_cases` on `ep.1.phase`).
4. Advance characterization for `CounterResetDest (p+1) = {1,6,7,8}`: an output beyond
   `p+1` ⟹ `ep.s` is a clock at `p+1` with `counter = 0` (`dispatch_{left,right}_clock_eq_std`
   + `…_not_clock_phase_eq` + `stdCounterSubroutine_phase_eq_of_counter_ne_zero`).
5. Source-tracing: `ep.s` clock@`p+1` counter `0` ⟹ the SOURCE `rᵢ` is already a clock@`p+1`
   with counter `0` (`ep_{left,right}_clock_zero_imp_source`; an epidemic-dragged immigrant
   would be reset to FULL counter `≠ 0`, so a zero-counter `ep.s` was not dragged).

**Headlines.**
* `det_seam_overshoot_bridge_of_wf p hq c r₁ r₂ (Wf c) hno hexit : AtRiskClockZero p c` —
  the bridge under `Wf c` and `CounterResetDest (p+1)`.
* `detSeamOvershootBridge_of_wf p hq (hWf : ∀ c, Wf c) : DetSeamOvershootBridge p` — the
  wire-up that ELIMINATES `hdet`, given the seam-region `W` (from the Analysis invariants).
* `hNoOvershoot_one_seam_wf` — the budget wrapper with `W` + `CounterResetDest` supplied.

**Final hypothesis surface (with the bridge eliminated):** seam timing/initial-potential
(folded into `hbound`) + seam-region `Wf` (`∀ c, Wf c`, from the Analysis-layer reachability
invariants) + `CounterResetDest (p+1)` + arithmetic.  The previously-carried
`DetSeamOvershootBridge p` is now a THEOREM, not an assumption.  Axiom audit: every headline
`⊆ [propext, Classical.choice, Quot.sound]`; no `sorry`/`native_decide`.
