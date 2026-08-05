/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBCreationStep

/-!
# The creation budget: what makes the fair-walk tail usable

`Tri/SingleBCreationStep.lean` closed the supermartingale step for the
compensated creation potential, with contraction factor exactly `1`. That is
correct for a fair walk and it is also why the tail is useless on its own: a
fair walk with an unbounded number of steps crosses every fixed boundary, so
`creationG_markov` says nothing until the creation count `CX + CY` is bounded.

That bound is what this file supplies, in two independent forms.

## The horizon bound, stated generically

Each event increments at most ONE of the four oriented counters, and by one.
So `CX + CY` grows by at most one per step, and after `T` steps it is at most
its starting value plus `T`.

This is not Single-B-specific, so it is proved generically:

```text
(∀ s z, K s z ≠ 0 → m z ≤ m s + 1)  →  iter K T s z ≠ 0 → m z ≤ m s + T
```

Any counter that a step can advance by at most one is bounded by its start
plus the horizon. `iter_support_closed` cannot deliver this — its invariant
must be preserved exactly, whereas this one degrades by one per step — so the
induction is done directly, mirroring that lemma's shape.

## The structural bound: the ledger's own blank invariant

The oriented ledger has an exact blank identity of its own, finer than
`SingleTrace.BlankLedger`:

```text
CX + CY + b₀ = b + RX + RY
```

Read left to right: every creation makes a blank, every resolution consumes
one, and the current blank count is the difference. This is exact, needs no
horizon, and bounds the creation count by `b + RX + RY` — which is the sharper
bound the paper's argument wants, since `b ≤ n`.

The two bounds are complementary: the horizon bound is unconditional but grows
with `T`; the structural one is tight but expressed through the resolution
count.
-/

namespace Tri

open scoped ENNReal

/-- **A counter that advances by at most one per step is bounded by its start
plus the horizon.**

The companion to `iter_support_closed`, for quantities that degrade rather than
being preserved. -/
theorem iter_support_counter_le {α : Type*} (K : α → PMF α) (m : α → ℕ)
    (hstep : ∀ s z, K s z ≠ 0 → m z ≤ m s + 1) :
    ∀ T s z, iter K T s z ≠ 0 → m z ≤ m s + T := by
  intro T
  induction T with
  | zero =>
      intro s z hz
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = s
      · rw [h]; omega
      · simp [h] at hz
  | succ T ih =>
      intro s z hz
      rw [iter_succ, PMF.bind_apply] at hz
      rw [Ne, ENNReal.tsum_eq_zero] at hz
      push Not at hz
      obtain ⟨a, ha⟩ := hz
      rw [mul_ne_zero_iff] at ha
      have h1 : m a ≤ m s + 1 := hstep s a ha.1
      have h2 : m z ≤ m a + T := ih a z ha.2
      omega

/-- One oriented event advances the creation count by at most one: the two
creation increments are on distinct constructors, so they never both fire. -/
theorem nextSingleLedger_creation_le {n : ℕ} (q : SingleLedger n)
    (k : SingleComp) :
    (SingleComp.nextSingleLedger q k).cx
        + (SingleComp.nextSingleLedger q k).cy
      ≤ q.cx + q.cy + 1 := by
  unfold SingleComp.nextSingleLedger
  split_ifs with hw
  · omega
  · cases k <;>
      simp only [SingleComp.cxInc, SingleComp.cyInc] <;> omega

/-- The same for the kernel: every state in the step's support has creation
count at most one more. -/
theorem singleLedgerStep_creation_le {n : ℕ} (hn : 2 ≤ n) (q z : SingleLedger n)
    (hqz : singleLedgerStep n hn q z ≠ 0) :
    z.cx + z.cy ≤ q.cx + q.cy + 1 := by
  unfold singleLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · rw [hzk]
    exact nextSingleLedger_creation_le q k
  · exact absurd rfl hk

/-- **The horizon budget.**  After `T` oriented events the creation count has
grown by at most `T`.

This is the `H` that `creationG_markov` needs in order to say anything: with
`CX + CY ≤ H` the threshold `θ = ofReal (exp (λ·D − (λ²/2)·H))` is dominated by
every ledger whose imbalance has reached `D`. -/
theorem singleLedger_creation_budget {n T : ℕ} (hn : 2 ≤ n)
    (q z : SingleLedger n)
    (hz : iter (singleLedgerStep n hn) T q z ≠ 0) :
    z.cx + z.cy ≤ q.cx + q.cy + T :=
  iter_support_counter_le (singleLedgerStep n hn)
    (fun w => w.cx + w.cy)
    (fun s w hsw => singleLedgerStep_creation_le hn s w hsw) T q z hz

/-- Started from a fresh ledger, the budget is the horizon itself. -/
theorem singleLedger_creation_budget_fresh {n T : ℕ} (hn : 2 ≤ n)
    (s : SingleState n) (z : SingleLedger n)
    (hz : iter (singleLedgerStep n hn) T ⟨s, 0, 0, 0, 0⟩ z ≠ 0) :
    z.cx + z.cy ≤ T := by
  have h := singleLedger_creation_budget hn ⟨s, 0, 0, 0, 0⟩ z hz
  simpa using h

/-! ### The structural bound -/

/-- **The oriented ledger's blank identity.**  Every creation makes a blank,
every resolution consumes one, and the current blank count is the difference.

Finer than `SingleTrace.BlankLedger`, which cannot see the orientation. -/
def SingleLedger.BlankLedger {n : ℕ} (initialBlank : ℕ) (q : SingleLedger n) :
    Prop :=
  q.cx + q.cy + initialBlank = q.cfg.1.b + q.rx + q.ry

theorem SingleLedger.initial_blankLedger {n : ℕ} (s : SingleState n) :
    SingleLedger.BlankLedger s.1.b ⟨s, 0, 0, 0, 0⟩ := by
  simp [SingleLedger.BlankLedger]

theorem SingleComp.nextSingleLedger_blankLedger
    {n initialBlank : ℕ} (q : SingleLedger n) (k : SingleComp)
    (hq : q.BlankLedger initialBlank)
    (hw : SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0) :
    (SingleComp.nextSingleLedger q k).BlankLedger initialBlank := by
  unfold SingleComp.nextSingleLedger
  rw [dif_neg hw]
  simp only [SingleLedger.BlankLedger] at hq ⊢
  cases k <;>
    simp only [SingleComp.cxInc, SingleComp.cyInc, SingleComp.rxInc,
      SingleComp.ryInc, SingleComp.next, SingleComp.weight] at hw ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hw; omega)

theorem singleLedgerStep_blankLedger_of_apply_ne_zero
    {n initialBlank : ℕ} (hn : 2 ≤ n) (q : SingleLedger n)
    (hq : q.BlankLedger initialBlank) (z : SingleLedger n)
    (hqz : singleLedgerStep n hn q z ≠ 0) :
    z.BlankLedger initialBlank := by
  unfold singleLedgerStep at hqz
  rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
  push Not at hqz
  obtain ⟨k, hk⟩ := hqz
  split_ifs at hk with hzk
  · have hw :
        SingleComp.weight q.cfg.1.x q.cfg.1.y q.cfg.1.b k ≠ 0 :=
      fun hw => hk (singleCompPMF_zero_of_weight_zero hw)
    rw [hzk]
    exact SingleComp.nextSingleLedger_blankLedger q k hq hw
  · exact absurd rfl hk

/-- The oriented blank identity holds along every finite trajectory. -/
theorem singleLedger_iter_blankLedger
    {n initialBlank T : ℕ} (hn : 2 ≤ n) (q z : SingleLedger n)
    (hq : q.BlankLedger initialBlank)
    (hz : iter (singleLedgerStep n hn) T q z ≠ 0) :
    z.BlankLedger initialBlank :=
  iter_support_closed
    (singleLedgerStep n hn) (SingleLedger.BlankLedger initialBlank)
    (fun a ha z haz =>
      singleLedgerStep_blankLedger_of_apply_ne_zero hn a ha z haz)
    T q z hq hz

/-- **The structural budget.**  The creation count is bounded by the current
blank count plus the resolutions — no horizon needed.

Since `b ≤ n` on every configuration, this gives `CX + CY ≤ n + RX + RY`, which
is the sharper bound when resolutions are themselves controlled. -/
theorem singleLedger_creation_le_blank_add_resolve
    {n initialBlank : ℕ} (q : SingleLedger n)
    (hq : q.BlankLedger initialBlank) :
    q.cx + q.cy ≤ q.cfg.1.b + q.rx + q.ry := by
  simp only [SingleLedger.BlankLedger] at hq
  omega

/-- And `b` is at most `n`, so the structural budget is uniform in the
population. -/
theorem singleLedger_creation_le_of_blankLedger
    {n initialBlank : ℕ} (q : SingleLedger n)
    (hq : q.BlankLedger initialBlank) :
    q.cx + q.cy ≤ n + q.rx + q.ry := by
  have hb : q.cfg.1.b ≤ n := by
    have hinv := q.cfg.2
    simp only [BiCfg.DoubleInv] at hinv
    omega
  have h := singleLedger_creation_le_blank_add_resolve q hq
  omega

/-- **The counter bound survives freezing**, for any frozen set.  A frozen step
either holds still (the counter does not move) or takes a real step (the counter
advances by at most one), so the horizon bound is unaffected.

This is what makes `H = T` the canonical budget: it holds on the support of the
frozen chain too, whatever the freezing set is. -/
theorem iter_freeze_support_counter_le {α : Type*} (K : α → PMF α) (m : α → ℕ)
    (B : α → Prop) [DecidablePred B]
    (hstep : ∀ s z, K s z ≠ 0 → m z ≤ m s + 1) :
    ∀ T s z, iter (freeze B K) T s z ≠ 0 → m z ≤ m s + T := by
  refine iter_support_counter_le (freeze B K) m ?_
  intro s z hsz
  unfold freeze at hsz
  by_cases hs : B s
  · rw [if_pos hs, PMF.pure_apply] at hsz
    by_cases h : z = s
    · rw [h]; omega
    · simp [h] at hsz
  · rw [if_neg hs] at hsz
    exact hstep s z hsz

/-- **The connection between the budget and the horizon**, for the Single-B
ledger and any frozen set: after `T` events from a fresh ledger the creation
count is at most `T`, so instantiating the tail's budget at `H = T` is not an
extra restriction — it is automatic.

Without this a caller could instantiate the tail's `H` inconsistently with the
horizon and obtain a true but meaningless bound. -/
theorem singleLedger_freeze_creation_budget {n T : ℕ} (hn : 2 ≤ n)
    (B : SingleLedger n → Prop) [DecidablePred B]
    (s : SingleState n) (z : SingleLedger n)
    (hz : iter (freeze B (singleLedgerStep n hn)) T
      (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) z ≠ 0) :
    z.cx + z.cy ≤ T := by
  have h := iter_freeze_support_counter_le (singleLedgerStep n hn)
    (fun w => w.cx + w.cy) B
    (fun a w haw => singleLedgerStep_creation_le hn a w haw) T
    (⟨s, 0, 0, 0, 0⟩ : SingleLedger n) z hz
  simpa using h

end Tri

#print axioms Tri.iter_support_counter_le
#print axioms Tri.singleLedgerStep_creation_le
#print axioms Tri.singleLedger_creation_budget
#print axioms Tri.singleLedger_creation_budget_fresh
#print axioms Tri.singleLedger_iter_blankLedger
#print axioms Tri.singleLedger_creation_le_of_blankLedger
#print axioms Tri.iter_freeze_support_counter_le
#print axioms Tri.singleLedger_freeze_creation_budget
