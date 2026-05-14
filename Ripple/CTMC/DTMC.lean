/-
  Ripple.CTMC.DTMC — Discrete-Time Markov Chains (Countable State Space)

  A DTMC on a countable state space S is specified by a transition kernel
  K : S → PMF S (each row is a probability mass function).

  Uses Mathlib's PMF infrastructure throughout.
-/

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.Operations

namespace Ripple.CTMC

open PMF
open scoped ENNReal

/-- A discrete-time Markov chain on a countable state space S,
specified by a transition kernel K : S → PMF S. -/
structure DTMC (S : Type*) [Countable S] where
  step : S → PMF S

variable {S : Type*} [Countable S]

/-- The n-step transition kernel K^n, defined by iterated bind. -/
noncomputable def DTMC.stepN (mc : DTMC S) : ℕ → S → PMF S
  | 0 => PMF.pure
  | n + 1 => fun s => (mc.stepN n s).bind mc.step

@[simp]
theorem DTMC.stepN_zero (mc : DTMC S) (s : S) :
    mc.stepN 0 s = PMF.pure s := rfl

@[simp]
theorem DTMC.stepN_one (mc : DTMC S) (s : S) :
    mc.stepN 1 s = mc.step s := by
  simp [DTMC.stepN, PMF.pure_bind]

/-- The n-step transition probability from s to t. -/
noncomputable def DTMC.prob (mc : DTMC S) (n : ℕ) (s t : S) : ℝ≥0∞ :=
  (mc.stepN n s) t

/-- Chapman-Kolmogorov: K^{m+n} = K^m ∘_bind K^n. -/
theorem DTMC.chapman_kolmogorov (mc : DTMC S) (m n : ℕ) (s : S) :
    mc.stepN (m + n) s = (mc.stepN m s).bind (mc.stepN n) := by
  induction n with
  | zero => simp [DTMC.stepN, PMF.bind_pure]
  | succ n ih =>
    change mc.stepN (m + n + 1) s = _
    simp only [DTMC.stepN]
    conv_lhs => rw [show mc.stepN (m + n) s = (mc.stepN m s).bind (mc.stepN n) from ih]
    exact PMF.bind_bind (mc.stepN m s) (mc.stepN n) mc.step

/-- State t is reachable from s if K^n(s,t) > 0 for some n. -/
def DTMC.Reachable (mc : DTMC S) (s t : S) : Prop :=
  ∃ n, mc.prob n s t ≠ 0

/-- States s and t communicate if each is reachable from the other. -/
def DTMC.Communicates (mc : DTMC S) (s t : S) : Prop :=
  mc.Reachable s t ∧ mc.Reachable t s

/-- The chain is irreducible if all states communicate. -/
def DTMC.Irreducible (mc : DTMC S) : Prop :=
  ∀ s t, mc.Communicates s t

theorem DTMC.communicates_refl (mc : DTMC S) (s : S) :
    mc.Communicates s s :=
  ⟨⟨0, by simp [DTMC.prob, DTMC.stepN, PMF.pure_apply]⟩,
   ⟨0, by simp [DTMC.prob, DTMC.stepN, PMF.pure_apply]⟩⟩

theorem DTMC.communicates_symm (mc : DTMC S) {s t : S}
    (h : mc.Communicates s t) : mc.Communicates t s :=
  ⟨h.2, h.1⟩

/-- Reachability is transitive: if s → u in m steps and u → t in n steps,
then s → t in m+n steps. -/
theorem DTMC.reachable_trans (mc : DTMC S) {s u t : S}
    (hsu : mc.Reachable s u) (hut : mc.Reachable u t) :
    mc.Reachable s t := by
  obtain ⟨m, hm⟩ := hsu
  obtain ⟨n, hn⟩ := hut
  refine ⟨m + n, ?_⟩
  simp only [prob]
  rw [mc.chapman_kolmogorov m n s]
  simp only [PMF.bind_apply]
  apply ne_of_gt
  calc
    0 < (mc.stepN m s) u * (mc.stepN n u) t :=
      ENNReal.mul_pos hm hn
    _ ≤ ∑' v, (mc.stepN m s) v * (mc.stepN n v) t :=
      ENNReal.le_tsum u

theorem DTMC.communicates_trans (mc : DTMC S) {s u t : S}
    (hsu : mc.Communicates s u) (hut : mc.Communicates u t) :
    mc.Communicates s t :=
  ⟨mc.reachable_trans hsu.1 hut.1, mc.reachable_trans hut.2 hsu.2⟩

/-- The set of return times to state s. -/
def DTMC.returnTimes (mc : DTMC S) (s : S) : Set ℕ :=
  { n | 0 < n ∧ mc.prob n s s ≠ 0 }

/-- A state has a self-loop iff K(s,s) > 0. -/
def DTMC.HasSelfLoop (mc : DTMC S) (s : S) : Prop :=
  mc.step s s ≠ 0

/-- Self-loop return time: 1 is a return time when K(s,s) > 0. -/
theorem DTMC.HasSelfLoop.one_mem_returnTimes (mc : DTMC S) {s : S}
    (h : mc.HasSelfLoop s) : 1 ∈ mc.returnTimes s := by
  refine ⟨Nat.one_pos, ?_⟩
  simp only [prob, stepN_one]
  exact h

/-- A self-loop implies the state is reachable from itself in 1 step. -/
theorem DTMC.HasSelfLoop.reachable_self (mc : DTMC S) {s : S}
    (h : mc.HasSelfLoop s) : mc.Reachable s s :=
  ⟨1, by simp only [prob, stepN_one, ne_eq]; exact h⟩

/-- The one-step matrix applied twice: K^2(s,t) = ∑_u K(s,u) K(u,t). -/
theorem DTMC.stepN_two (mc : DTMC S) (s : S) :
    mc.stepN 2 s = (mc.step s).bind mc.step := by
  simp [DTMC.stepN, PMF.pure_bind]

/-- Probability from s to s in 0 steps is 1. -/
theorem DTMC.prob_zero_self (mc : DTMC S) (s : S) :
    mc.prob 0 s s = 1 := by
  simp [DTMC.prob, DTMC.stepN, PMF.pure_apply]

/-- Probability from s to t in 0 steps is 0 when s ≠ t. -/
theorem DTMC.prob_zero_ne (mc : DTMC S) {s t : S} (hst : s ≠ t) :
    mc.prob 0 s t = 0 := by
  simp only [DTMC.prob, DTMC.stepN, PMF.pure_apply, ite_eq_right_iff]
  intro h
  exact absurd h.symm hst

/-- One-step probability equals the kernel value. -/
theorem DTMC.prob_one (mc : DTMC S) (s t : S) :
    mc.prob 1 s t = mc.step s t := by
  simp [DTMC.prob]

/-- Chapman-Kolmogorov in probability form:
K^{m+n}(s,t) = ∑_v K^m(s,v) · K^n(v,t). -/
theorem DTMC.prob_add (mc : DTMC S) (m n : ℕ) (s t : S) :
    mc.prob (m + n) s t = ∑' v, mc.prob m s v * mc.prob n v t := by
  simp only [prob]
  rw [mc.chapman_kolmogorov m n s]
  simp [PMF.bind_apply]

/-- Transition probabilities sum to 1 over target states. -/
theorem DTMC.prob_sum (mc : DTMC S) (n : ℕ) (s : S) :
    ∑' t, mc.prob n s t = 1 :=
  (mc.stepN n s).tsum_coe

/-- Reachability in 0 steps implies s = t. -/
theorem DTMC.reachable_zero_eq (mc : DTMC S) {s t : S}
    (h : mc.prob 0 s t ≠ 0) : s = t := by
  by_contra hne
  exact h (mc.prob_zero_ne hne)

end Ripple.CTMC
