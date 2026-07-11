/-
Ripple.BoundedUniversality.Core.DiscreteSource
--------------------------
A fuel-based discrete source whose halting predicate is undecidable,
derived from Mathlib's `ComputablePred.halting_problem`.
-/

import Mathlib.Computability.Halting
import Ripple.BoundedUniversality.Core.Computability

open Nat.Partrec (Code)
open Nat.Partrec.Code
open Encodable Denumerable

namespace Ripple.BoundedUniversality.Core

/-! ### Generalized no-decider bridge -/

/-- No computable Bool decider exists for a predicate on an arbitrary `Primcodable` type. -/
def NoComputableBoolDeciderOn (α : Type*) [Primcodable α] (halts : α → Prop) : Prop :=
  ¬ ∃ f : α → Bool, Computable f ∧ ∀ a, f a = true ↔ halts a

/-- If a predicate is not `ComputablePred`, then no computable Bool function decides it. -/
theorem noBoolDeciderOn_of_not_computablePred {α : Type*} [Primcodable α]
    {p : α → Prop} (h : ¬ ComputablePred p) :
    NoComputableBoolDeciderOn α p := by
  intro ⟨f, hf, hiff⟩
  apply h
  have heq : p = fun a => (f a : Prop) := by
    ext a; exact (hiff a).symm
  rw [ComputablePred.computable_iff]
  exact ⟨f, hf, heq⟩

/-! ### Code-level halting -/

/-- Whether Code `c` halts on input `n` (i.e., `eval c n` has a value). -/
def CodeHaltsAt (n : ℕ) (c : Code) : Prop := (eval c n).Dom

/-- No computable Bool function decides which Codes halt on a fixed input. -/
theorem codeHaltsAt_noBoolDeciderOn (n : ℕ) :
    NoComputableBoolDeciderOn Code (CodeHaltsAt n) :=
  noBoolDeciderOn_of_not_computablePred (ComputablePred.halting_problem n)

/-! ### Pull back to ℕ via Encodable -/

/-- Whether the Code encoded by natural number `k` halts on input `0`. -/
def NatCodeHaltsAt (k : ℕ) : Prop :=
  CodeHaltsAt 0 (ofNat Code k)

/-- No computable Bool function decides `NatCodeHaltsAt`. -/
theorem natCodeHaltsAt_noBoolDecider : NoComputableBoolDecider NatCodeHaltsAt := by
  intro ⟨f, hf, hbool⟩
  have h0 : NoComputableBoolDeciderOn Code (CodeHaltsAt 0) := codeHaltsAt_noBoolDeciderOn 0
  apply h0
  refine ⟨fun c => f (Encodable.encode c), hf.comp Computable.encode, fun c => ?_⟩
  have := hbool (Encodable.encode c)
  simp only [NatCodeHaltsAt, CodeHaltsAt, Denumerable.ofNat_encode] at this
  exact this

/-! ### Fuel-based discrete source -/

/-- Configuration: (program code as ℕ, fuel). -/
abbrev SourceCfg := ℕ × ℕ

/-- Initial configuration: start with fuel = 0. -/
def initCfg (n : ℕ) : SourceCfg := (n, 0)

/-- Step: increment fuel. -/
def stepCfg (q : SourceCfg) : SourceCfg := (q.1, q.2.succ)

/-- Halted: `evaln` returns `some` on the current fuel. -/
def haltedCfg (q : SourceCfg) : Bool :=
  (evaln q.2 (ofNat Code q.1) 0).isSome

theorem computable_initCfg : Computable initCfg :=
  Computable.pair Computable.id (Computable.const 0)

theorem computable_stepCfg : Computable stepCfg :=
  Computable.pair Computable.fst (Computable.succ.comp Computable.snd)

theorem computable_haltedCfg : Computable haltedCfg := by
  unfold haltedCfg
  exact (Primrec.option_isSome.to_comp).comp
    (Code.primrec_evaln.to_comp.comp
      (Computable.pair
        (Computable.pair Computable.snd ((Computable.ofNat Code).comp Computable.fst))
        (Computable.const 0)))

/-- The source halts on input `n` iff there exists a fuel level at which `evaln` succeeds. -/
def sourceHalts (n : ℕ) : Prop :=
  ∃ k : ℕ, haltedCfg (stepCfg^[k] (initCfg n)) = true

/-- Iterating `stepCfg` from `initCfg n` gives `(n, k)`. -/
theorem iterate_stepCfg (n k : ℕ) :
    stepCfg^[k] (initCfg n) = (n, k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply, ih, stepCfg]

/-- Source halts iff `NatCodeHaltsAt`. -/
theorem sourceHalts_iff_natCodeHaltsAt (n : ℕ) :
    sourceHalts n ↔ NatCodeHaltsAt n := by
  simp only [sourceHalts, NatCodeHaltsAt, CodeHaltsAt]
  constructor
  · rintro ⟨k, hk⟩
    rw [iterate_stepCfg] at hk
    simp only [haltedCfg] at hk
    rw [Option.isSome_iff_exists] at hk
    obtain ⟨x, hx⟩ := hk
    exact Part.dom_iff_mem.mpr ⟨x, evaln_sound (Option.mem_def.mpr hx)⟩
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨x, hx⟩ := hdom
    rw [evaln_complete] at hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    rw [iterate_stepCfg]
    simp only [haltedCfg]
    rw [Option.isSome_iff_exists]
    exact ⟨x, Option.mem_def.mp hk⟩

/-- The halting predicate of the discrete source is not computable. -/
theorem sourceHalts_noBoolDecider : NoComputableBoolDecider sourceHalts := by
  intro ⟨f, hf, hbool⟩
  apply natCodeHaltsAt_noBoolDecider
  exact ⟨f, hf, fun n => (hbool n).trans (sourceHalts_iff_natCodeHaltsAt n)⟩

end Ripple.BoundedUniversality.Core
