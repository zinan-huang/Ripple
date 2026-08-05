/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Ruin

/-!
# Freezing, hitting probabilities, and Feller's Lemma 1

The previous file proved a *terminal-state* ruin bound: the level is low **at
time `T`**. The paper's Lemma 1 is stronger — it bounds the probability that the
deficit is **ever** `b`, over an arbitrarily long run. This file closes that gap.

The bridge is the freeze construction. Freezing the chain on the bad set makes
that set absorbing, so for the frozen chain

    "ever entered the bad set by time `T`"  =  "in the bad set at time `T`",

and the left-hand side is monotone in `T`. Taking the supremum over `T` therefore
turns a family of terminal-state bounds, *uniform in `T`*, into a genuine
unbounded-horizon statement. No trajectory measure, no stopping time, and no
monotone-convergence machinery beyond `iSup` of a monotone family is needed.

This is the design's freeze device in its honest minimal form: only the concrete
terminal-state comparison is used, never a general prefix-measurable transfer.

## Main results

* `freeze` — the chain stopped on a decidable bad set; `freeze_absorbing`.
* `hitProb` — the probability of being in the bad set at time `T`, for the
  frozen chain; equivalently of having entered it by time `T`.
* `hitProb_mono` — monotone in `T`, because the bad set is absorbing.
* `feller_ruin` — **Lemma 1.** With a geometric potential conserved off the bad
  set, the probability that the level *ever* drops `b` below the start is at
  most `ρ⁻¹ ^ b`, uniformly over all horizons.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Lemma 1 (Feller XIV.2).
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- Peeling a step off the *end* rather than the front. Needed because
monotonicity of the hitting probability is naturally an argument about the last
step. -/
theorem iter_succ' (K : α → PMF α) (n : ℕ) (s : α) :
    iter K (n + 1) s = (iter K n s).bind K := by
  induction n generalizing s with
  | zero => simp [iter, PMF.pure_bind, PMF.bind_pure]
  | succ t ih =>
    show (K s).bind (iter K (t + 1)) = (iter K (t + 1) s).bind K
    calc (K s).bind (iter K (t + 1))
        = (K s).bind (fun a => (iter K t a).bind K) := congrArg _ (funext ih)
      _ = ((K s).bind (iter K t)).bind K := (PMF.bind_bind _ _ _).symm
      _ = (iter K (t + 1) s).bind K := rfl

/-- The chain stopped on `B`: inside `B` nothing moves. -/
noncomputable def freeze (B : α → Prop) [DecidablePred B] (K : α → PMF α) :
    α → PMF α := fun s => if B s then PMF.pure s else K s

variable {B : α → Prop} [DecidablePred B] {K : α → PMF α}

@[simp] theorem freeze_of_mem (s : α) (hs : B s) : freeze B K s = PMF.pure s := by
  simp [freeze, hs]

@[simp] theorem freeze_of_not_mem (s : α) (hs : ¬ B s) : freeze B K s = K s := by
  simp [freeze, hs]

/-- The indicator of the bad set, as a potential. -/
noncomputable def ind (B : α → Prop) [DecidablePred B] : α → ℝ≥0∞ :=
  fun z => if B z then 1 else 0

/-- The probability that the frozen chain sits in `B` at time `T`. Because `B`
is absorbing for the frozen chain, this is exactly the probability that the
original chain has entered `B` at some time `≤ T`. -/
noncomputable def hitProb (B : α → Prop) [DecidablePred B] (K : α → PMF α)
    (T : ℕ) (s₀ : α) : ℝ≥0∞ :=
  expect (iter (freeze B K) T s₀) (ind B)

/-- One step of the frozen chain cannot decrease the indicator of `B`: states in
`B` stay put, and states outside contribute nothing to begin with. This is
absorbency, stated in the form the monotonicity argument consumes. -/
theorem expect_freeze_ind_ge (a : α) :
    ind B a ≤ expect (freeze B K a) (ind B) := by
  by_cases ha : B a
  · simp [freeze_of_mem a ha, ind, ha]
  · simp [ind, ha]

/-- **The hitting probability is monotone in the horizon.** -/
theorem hitProb_mono (s₀ : α) : Monotone (fun T => hitProb B K T s₀) := by
  refine monotone_nat_of_le_succ fun T => ?_
  show expect (iter (freeze B K) T s₀) (ind B)
      ≤ expect (iter (freeze B K) (T + 1) s₀) (ind B)
  rw [iter_succ', expect_bind]
  unfold expect
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (expect_freeze_ind_ge a) _

/-- **The frozen conservation bridge.**

To use `feller_ruin` one must show the potential is conserved by the *frozen*
chain. That reduces to conservation off the bad set alone: on the bad set the
frozen step is `pure`, so the potential is preserved exactly.

Note what this makes unnecessary: **region invariance is not a separate
obligation.** One might worry that the chain could wander out of the region where
the drift estimate holds. It cannot matter — freezing makes the bad set
absorbing, so the chain never has to stay in the region on its own, and the
hypothesis is only ever consulted off the bad set. -/
theorem freeze_conserve {V : α → ℝ≥0∞}
    (h : ∀ s, ¬ B s → expect (K s) V ≤ V s) :
    ∀ s, expect (freeze B K s) V ≤ V s := by
  intro s
  by_cases hs : B s
  · rw [freeze_of_mem s hs, expect_pure]
  · rw [freeze_of_not_mem s hs]; exact h s hs

/-- **Feller's Lemma 1**, unbounded horizon.

`level` measures progress and `V = ρ⁻¹ ^ level` is the geometric potential, with
`1 ≤ ρ`. Suppose `V` is conserved in expectation by the *frozen* chain — which at
the harmonic base `ρ = p/(1-p)` is exactly `bracket_harmonic`, since off the bad
set the chain is unchanged and on it the step is `pure`.

Then, starting from level `m + b`, the probability that the level *ever* drops to
`m` or below — over **any** horizon — is at most `ρ⁻¹ ^ b`.

This is the paper's "the probability that the number of failures ever exceeds the
number of successes by `b` is at most `((1-p)/p)^b`". The supremum over `T` is a
genuine unbounded statement: the bound holds uniformly in `T`, so it holds for
the whole run. -/
theorem feller_ruin (level : α → ℕ) (m b : ℕ)
    (ρ : ℝ≥0∞) (hρ1 : 1 ≤ ρ) (hρtop : ρ ≠ ⊤)
    (V : α → ℝ≥0∞) (hV : ∀ s, V s = ρ⁻¹ ^ (level s))
    (hfroz : ∀ s, expect (freeze (fun z => level z ≤ m) K s) V ≤ V s)
    (s₀ : α) (hs₀ : level s₀ = m + b) :
    ⨆ T : ℕ, hitProb (fun z => level z ≤ m) K T s₀ ≤ ρ⁻¹ ^ b := by
  refine iSup_le fun T => ?_
  -- `hitProb` is the tsum of the indicator, which is the ruin event of `ruin_le`
  have hrewrite : hitProb (fun z => level z ≤ m) K T s₀
      = ∑' z, (if level z ≤ m then iter (freeze (fun z => level z ≤ m) K) T s₀ z else 0) := by
    unfold hitProb expect ind
    congr 1; ext z
    by_cases hz : level z ≤ m <;> simp [hz]
  rw [hrewrite]
  exact ruin_le (freeze (fun z => level z ≤ m) K) level ρ hρ1 hρtop V hV hfroz T m b s₀ hs₀

/-- **`u`-form of the ruin bound.** Same content as `Tri.ruin_le`, but stated with
the potential base `u ≤ 1` directly rather than as `ρ⁻¹` for `ρ ≥ 1`.

Call sites that arrive with a natural base — such as the Tri chain, whose base is
the ratio `bHi/aLo ≤ 1` coming from `Tri.odds_uniform` — would otherwise have to
invert a ratio in `ℝ≥0∞` at every use. This form removes that friction. -/
theorem ruin_le_u (K : α → PMF α) (level : α → ℕ) (u : ℝ≥0∞) (hu1 : u ≤ 1) (hu0 : u ≠ 0)
    (V : α → ℝ≥0∞) (hV : ∀ s, V s = u ^ (level s))
    (hK : ∀ s, expect (K s) V ≤ V s)
    (T m b : ℕ) (s₀ : α) (hs₀ : level s₀ = m + b) :
    ∑' z, (if level z ≤ m then iter K T s₀ z else 0) ≤ u ^ b := by
  have hutop : u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  set θ : ℝ≥0∞ := u ^ m with hθdef
  have hθ : θ ≠ 0 := pow_ne_zero _ hu0
  have htop : θ ≠ ⊤ := ENNReal.pow_ne_top hutop
  have hsub : ∀ z, (if level z ≤ m then iter K T s₀ z else 0)
      ≤ (if θ ≤ V z then iter K T s₀ z else 0) := by
    intro z
    by_cases hz : level z ≤ m
    · have : θ ≤ V z := by
        rw [hV z, hθdef]; exact pow_le_pow_right_of_le_one' hu1 hz
      simp [hz, this]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (supermartingale_tail K V hK T s₀ θ hθ htop) ?_
  rw [hV s₀, hs₀, hθdef, pow_add, mul_comm, mul_div_assoc,
    ENNReal.div_self hθ htop, mul_one]

/-- **Feller's Lemma 1 in `u`-form**, unbounded horizon. -/
theorem feller_ruin_u (level : α → ℕ) (m b : ℕ)
    (u : ℝ≥0∞) (hu1 : u ≤ 1) (hu0 : u ≠ 0)
    (V : α → ℝ≥0∞) (hV : ∀ s, V s = u ^ (level s))
    (hfroz : ∀ s, expect (freeze (fun z => level z ≤ m) K s) V ≤ V s)
    (s₀ : α) (hs₀ : level s₀ = m + b) :
    ⨆ T : ℕ, hitProb (fun z => level z ≤ m) K T s₀ ≤ u ^ b := by
  refine iSup_le fun T => ?_
  have hrewrite : hitProb (fun z => level z ≤ m) K T s₀
      = ∑' z, (if level z ≤ m then iter (freeze (fun z => level z ≤ m) K) T s₀ z else 0) := by
    unfold hitProb expect ind
    congr 1; ext z
    by_cases hz : level z ≤ m <;> simp [hz]
  rw [hrewrite]
  exact ruin_le_u (freeze (fun z => level z ≤ m) K) level u hu1 hu0 V hV hfroz T m b s₀ hs₀


section NonVacuity

/-! ## Non-vacuity of `feller_ruin`'s hypotheses

The playbook's "clean-3" standard demands no unsatisfiable hypotheses and no
dangling premises: a theorem whose premise set cannot be met is vacuously true
and proves nothing. `feller_ruin` carries a nontrivial conservation hypothesis
`hfroz`, so satisfiability is checked here rather than assumed.

`feller_ruin_hypotheses_satisfiable` exhibits an explicit instantiation in which
every hypothesis holds and the conclusion is a genuine statement — the level
starts at `m + b` with `b` arbitrary, so the bound `ρ⁻¹ ^ b` is not degenerate.
-/

/-- The hypothesis set of `feller_ruin` is satisfiable: here is an instance.

The witness is deliberately the simplest chain for which conservation is exact,
which makes the check independent of any drift estimate. Note this is a
*satisfiability* witness only: it certifies that `feller_ruin` is not vacuously
true. The intended nondegenerate instance is the biased walk at the harmonic
base, whose one-step conservation is exactly `Tri.bracket_harmonic`; wiring that
walk in is the next step and is not claimed here. -/
theorem feller_ruin_hypotheses_satisfiable (m b : ℕ) :
    ∃ (K : ℕ → PMF ℕ) (ρ : ℝ≥0∞) (V : ℕ → ℝ≥0∞) (s₀ : ℕ),
      1 ≤ ρ ∧ ρ ≠ ⊤ ∧
      (∀ s, V s = ρ⁻¹ ^ s) ∧
      (∀ s, expect (freeze (fun z => z ≤ m) K s) V ≤ V s) ∧
      s₀ = m + b := by
  refine ⟨PMF.pure, 2, fun s => (2 : ℝ≥0∞)⁻¹ ^ s, m + b, by norm_num, by norm_num,
    fun s => rfl, fun s => ?_, rfl⟩
  have hfz : freeze (fun z => z ≤ m) PMF.pure s = PMF.pure s := by
    unfold freeze; split <;> rfl
  simp [hfz]

end NonVacuity

end Tri
