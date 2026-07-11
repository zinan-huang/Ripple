import Ripple.BoundedUniversality.BGP.Interfaces
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
Ripple.BoundedUniversality.BGP.UniversalMachine
---------------------------

Thin wrapper around Mathlib's `Turing.PartrecToTM2.tr` universal TM2 machine.

Mathlib already supplies the machine and its correctness theorem:

```
Turing.PartrecToTM2.tr_eval :
  StateTransition.eval (TM2.step tr) (init c v) = halt <$> Code.eval c v
```

The direct control-label type `Λ'` is intentionally infinite, so this file does
not assert the finite-range state-coordinate hypothesis needed by
`main_assembled`; see `HANDOFF/u2-findings.md`.
-/

namespace Ripple.BoundedUniversality.BGP
namespace UniversalMachine

open Turing
open Turing.PartrecToTM2

/-- Mathlib's simplified partial-recursive code type used by `PartrecToTM2`. -/
abbrev Code : Type :=
  Turing.ToPartrec.Code

/-- Stack index type of Mathlib's universal TM2 machine. -/
abbrev StackIndex : Type :=
  K'

/-- Stack alphabet of Mathlib's universal TM2 machine. -/
abbrev Alphabet : Type :=
  Γ'

/-- Control-label type of Mathlib's universal TM2 machine. This type is infinite. -/
abbrev Label : Type :=
  Λ'

/-- Local variable type of Mathlib's universal TM2 machine. -/
abbrev Var : Type :=
  Option Γ'

/-- Configuration type of Mathlib's universal TM2 machine. -/
abbrev Cfg : Type :=
  Cfg'

/-- One partial TM2 transition, as supplied by Mathlib. -/
def stepOpt : Cfg → Option Cfg :=
  TM2.step tr

/--
Absorbing total-step adapter: halted configurations (`l = none`) stay fixed,
and running configurations take the Mathlib TM2 step.
-/
def step (c : Cfg) : Cfg :=
  (stepOpt c).getD c

/-- Local halted test. -/
def halted (c : Cfg) : Bool :=
  c.l.isNone

@[simp] theorem halted_eq_true_iff (c : Cfg) :
    halted c = true ↔ c.l = none := by
  cases c with
  | mk l var stk =>
      cases l <;> simp [halted]

@[simp] theorem step_halted (c : Cfg) (h : halted c = true) :
    step c = c := by
  rw [halted_eq_true_iff] at h
  cases c with
  | mk l var stk =>
      cases h
      rfl

/-- Mathlib's initial configuration for code `c` and input vector/list `v`. -/
def init (c : Code) (v : List Nat) : Cfg :=
  PartrecToTM2.init c v

/-- The raw correctness theorem from Mathlib, restated under the local names. -/
theorem eval_eq_halt_map (c : Code) (v : List Nat) :
    StateTransition.eval stepOpt (init c v) = halt <$> c.eval v := by
  exact PartrecToTM2.tr_eval c v

/--
The universal TM2 machine halts from `init c v` exactly when the simplified
partial-recursive code `c` is defined at `v`.
-/
theorem eval_dom_iff_code_dom (c : Code) (v : List Nat) :
    (StateTransition.eval stepOpt (init c v)).Dom ↔ (c.eval v).Dom := by
  rw [eval_eq_halt_map]
  rfl

/-- Alias for the domain statement in the requested `halts iff dom` direction. -/
theorem U_halts_iff_dom (c : Code) (v : List Nat) :
    (StateTransition.eval stepOpt (init c v)).Dom ↔ (c.eval v).Dom :=
  eval_dom_iff_code_dom c v

/-! ## Diagonal `ToPartrec` code -/

/--
The usual diagonal partial function for Mathlib's `Nat.Partrec.Code`
interpreter, reindexed through the canonical denumerable enumeration of codes.
-/
noncomputable def diagonalEval : ℕ →. ℕ :=
  fun n => (Denumerable.ofNat Nat.Partrec.Code n).eval n

private theorem diagonalEval_partrec : Partrec diagonalEval := by
  exact Nat.Partrec.Code.eval_part.comp
    (Computable.ofNat Nat.Partrec.Code) Computable.id

private theorem diagonalEval_partrec' :
    Nat.Partrec' (fun v : List.Vector ℕ 1 => diagonalEval v.head) := by
  exact Nat.Partrec'.part_iff₁.mpr diagonalEval_partrec

/-- A `ToPartrec.Code` computing the diagonal evaluator on one input. -/
noncomputable def c_f : Code :=
  (Turing.ToPartrec.Code.exists_code diagonalEval_partrec').choose

theorem c_f_eval (n : ℕ) :
    c_f.eval [n] = pure <$> diagonalEval n := by
  have h := (Turing.ToPartrec.Code.exists_code diagonalEval_partrec').choose_spec
  specialize h (⟨[n], by simp⟩ : List.Vector ℕ 1)
  simpa [c_f, diagonalEval] using h

/-- The compiled `ToPartrec` diagonal code is defined exactly when the diagonal is. -/
theorem c_f_dom (n : ℕ) :
    (c_f.eval [n]).Dom ↔ (diagonalEval n).Dom := by
  rw [c_f_eval n]
  rfl

/-! ## Local coding instances for the wrapped Mathlib machine -/

deriving instance Fintype for K'

private def kEquivFin4 : K' ≃ Fin 4 where
  toFun
    | K'.main => 0
    | K'.rev => 1
    | K'.aux => 2
    | K'.stack => 3
  invFun i :=
    match i.1 with
    | 0 => K'.main
    | 1 => K'.rev
    | 2 => K'.aux
    | _ => K'.stack
  left_inv k := by cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Primcodable K' :=
  Primcodable.ofEquiv (Fin 4) kEquivFin4

private def gammaEquivFin4 : Γ' ≃ Fin 4 where
  toFun
    | Γ'.consₗ => 0
    | Γ'.cons => 1
    | Γ'.bit0 => 2
    | Γ'.bit1 => 3
  invFun i :=
    match i.1 with
    | 0 => Γ'.consₗ
    | 1 => Γ'.cons
    | 2 => Γ'.bit0
    | _ => Γ'.bit1
  left_inv g := by cases g <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Primcodable Γ' :=
  Primcodable.ofEquiv (Fin 4) gammaEquivFin4

deriving instance Countable for Turing.ToPartrec.Code

private def codeFixTower : Nat → Turing.ToPartrec.Code
  | 0 => Turing.ToPartrec.Code.zero'
  | n + 1 => Turing.ToPartrec.Code.fix (codeFixTower n)

private theorem codeFixTower_injective : Function.Injective codeFixTower := by
  intro a b h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b => simp [codeFixTower] at h
  | succ a ih =>
      cases b with
      | zero => simp [codeFixTower] at h
      | succ b =>
          simp [codeFixTower] at h
          exact congrArg Nat.succ (ih h)

instance : Infinite Turing.ToPartrec.Code :=
  Infinite.of_injective codeFixTower codeFixTower_injective

noncomputable instance : Encodable Turing.ToPartrec.Code :=
  Encodable.ofCountable _

noncomputable instance : Denumerable Turing.ToPartrec.Code :=
  Denumerable.ofEncodableOfInfinite _

noncomputable instance : Primcodable Turing.ToPartrec.Code :=
  Primcodable.ofDenumerable _

deriving instance Countable for Cont'

private def contCons₂Tower : Nat → Cont'
  | 0 => Cont'.halt
  | n + 1 => Cont'.cons₂ (contCons₂Tower n)

private theorem contCons₂Tower_injective : Function.Injective contCons₂Tower := by
  intro a b h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b => simp [contCons₂Tower] at h
  | succ a ih =>
      cases b with
      | zero => simp [contCons₂Tower] at h
      | succ b =>
          simp [contCons₂Tower] at h
          exact congrArg Nat.succ (ih h)

instance : Infinite Cont' :=
  Infinite.of_injective contCons₂Tower contCons₂Tower_injective

noncomputable instance : Encodable Cont' :=
  Encodable.ofCountable _

noncomputable instance : Denumerable Cont' :=
  Denumerable.ofEncodableOfInfinite _

noncomputable instance : Primcodable Cont' :=
  Primcodable.ofDenumerable _

/--
`Λ'` has one constructor containing a finite-domain function
`Option Γ' → Λ'`.  This private presentation replaces that field by its five
values, which lets the standard countability derivation see the recursive
structure.
-/
private inductive LabelCode where
  | move (p : Γ' → Bool) (k₁ k₂ : K') (q : LabelCode)
  | clear (p : Γ' → Bool) (k : K') (q : LabelCode)
  | copy (q : LabelCode)
  | push (k : K') (s : Option Γ' → Option Γ') (q : LabelCode)
  | read (q₀ q₁ q₂ q₃ q₄ : LabelCode)
  | succ (q : LabelCode)
  | pred (q₁ q₂ : LabelCode)
  | ret (k : Cont')

deriving instance Countable for LabelCode

private def labelCodeCopyTower : Nat → LabelCode
  | 0 => LabelCode.ret Cont'.halt
  | n + 1 => LabelCode.copy (labelCodeCopyTower n)

private theorem labelCodeCopyTower_injective :
    Function.Injective labelCodeCopyTower := by
  intro a b h
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b => simp [labelCodeCopyTower] at h
  | succ a ih =>
      cases b with
      | zero => simp [labelCodeCopyTower] at h
      | succ b =>
          simp [labelCodeCopyTower] at h
          exact congrArg Nat.succ (ih h)

instance : Infinite LabelCode :=
  Infinite.of_injective labelCodeCopyTower labelCodeCopyTower_injective

noncomputable instance : Encodable LabelCode :=
  Encodable.ofCountable _

noncomputable instance : Denumerable LabelCode :=
  Denumerable.ofEncodableOfInfinite _

noncomputable instance : Primcodable LabelCode :=
  Primcodable.ofDenumerable _

private def labelToCode : Λ' → LabelCode
  | Λ'.move p k₁ k₂ q => LabelCode.move p k₁ k₂ (labelToCode q)
  | Λ'.clear p k q => LabelCode.clear p k (labelToCode q)
  | Λ'.copy q => LabelCode.copy (labelToCode q)
  | Λ'.push k s q => LabelCode.push k s (labelToCode q)
  | Λ'.read f =>
      LabelCode.read
        (labelToCode (f none))
        (labelToCode (f (some Γ'.consₗ)))
        (labelToCode (f (some Γ'.cons)))
        (labelToCode (f (some Γ'.bit0)))
        (labelToCode (f (some Γ'.bit1)))
  | Λ'.succ q => LabelCode.succ (labelToCode q)
  | Λ'.pred q₁ q₂ => LabelCode.pred (labelToCode q₁) (labelToCode q₂)
  | Λ'.ret k => LabelCode.ret k

private def codeToLabel : LabelCode → Λ'
  | LabelCode.move p k₁ k₂ q => Λ'.move p k₁ k₂ (codeToLabel q)
  | LabelCode.clear p k q => Λ'.clear p k (codeToLabel q)
  | LabelCode.copy q => Λ'.copy (codeToLabel q)
  | LabelCode.push k s q => Λ'.push k s (codeToLabel q)
  | LabelCode.read q₀ q₁ q₂ q₃ q₄ =>
      Λ'.read fun
        | none => codeToLabel q₀
        | some Γ'.consₗ => codeToLabel q₁
        | some Γ'.cons => codeToLabel q₂
        | some Γ'.bit0 => codeToLabel q₃
        | some Γ'.bit1 => codeToLabel q₄
  | LabelCode.succ q => Λ'.succ (codeToLabel q)
  | LabelCode.pred q₁ q₂ => Λ'.pred (codeToLabel q₁) (codeToLabel q₂)
  | LabelCode.ret k => Λ'.ret k

private theorem codeToLabel_labelToCode :
    ∀ q : Λ', codeToLabel (labelToCode q) = q := by
  intro q
  induction q with
  | move p k₁ k₂ q ih => simp [labelToCode, codeToLabel, ih]
  | clear p k q ih => simp [labelToCode, codeToLabel, ih]
  | copy q ih => simp [labelToCode, codeToLabel, ih]
  | push k s q ih => simp [labelToCode, codeToLabel, ih]
  | read f ih =>
      simp [labelToCode, codeToLabel]
      funext s
      cases s with
      | none => exact ih none
      | some g =>
          cases g <;> simp [ih]
  | succ q ih => simp [labelToCode, codeToLabel, ih]
  | pred q₁ q₂ ih₁ ih₂ => simp [labelToCode, codeToLabel, ih₁, ih₂]
  | ret k => rfl

private theorem labelToCode_codeToLabel :
    ∀ q : LabelCode, labelToCode (codeToLabel q) = q := by
  intro q
  induction q with
  | move p k₁ k₂ q ih => simp [labelToCode, codeToLabel, ih]
  | clear p k q ih => simp [labelToCode, codeToLabel, ih]
  | copy q ih => simp [labelToCode, codeToLabel, ih]
  | push k s q ih => simp [labelToCode, codeToLabel, ih]
  | read q₀ q₁ q₂ q₃ q₄ ih₀ ih₁ ih₂ ih₃ ih₄ =>
      simp [labelToCode, codeToLabel, ih₀, ih₁, ih₂, ih₃, ih₄]
  | succ q ih => simp [labelToCode, codeToLabel, ih]
  | pred q₁ q₂ ih₁ ih₂ => simp [labelToCode, codeToLabel, ih₁, ih₂]
  | ret k => rfl

private def labelEquivCode : Λ' ≃ LabelCode where
  toFun := labelToCode
  invFun := codeToLabel
  left_inv := codeToLabel_labelToCode
  right_inv := labelToCode_codeToLabel

noncomputable instance : Primcodable Λ' :=
  Primcodable.ofEquiv LabelCode labelEquivCode

abbrev StackTuple :=
  List Γ' × List Γ' × List Γ' × List Γ'

def stackEquivTuple : (K' → List Γ') ≃ StackTuple where
  toFun S := (S K'.main, S K'.rev, S K'.aux, S K'.stack)
  invFun t := K'.elim t.1 t.2.1 t.2.2.1 t.2.2.2
  left_inv S := by
    funext k
    cases k <;> rfl
  right_inv t := by
    rcases t with ⟨main, rev, aux, stack⟩
    rfl

private def cfgEquivTuple :
    Cfg' ≃ Option Λ' × Option Γ' × StackTuple where
  toFun c := (c.l, c.var, stackEquivTuple c.stk)
  invFun t := ⟨t.1, t.2.1, stackEquivTuple.symm t.2.2⟩
  left_inv c := by
    cases c with
    | mk l var stk =>
        change (⟨l, var,
          K'.elim (stk K'.main) (stk K'.rev) (stk K'.aux) (stk K'.stack)⟩ : Cfg') =
            ⟨l, var, stk⟩
        rw [show K'.elim (stk K'.main) (stk K'.rev) (stk K'.aux) (stk K'.stack) = stk by
          funext k
          cases k <;> rfl]
  right_inv t := by
    rcases t with ⟨l, var, stk⟩
    simp [stackEquivTuple]

noncomputable instance : Primcodable Cfg' :=
  Primcodable.ofEquiv (Option Λ' × Option Γ' × StackTuple) cfgEquivTuple

/-! ## A direct one-step implementation

The Mathlib `TM2.step` executes a whole finite statement tree until a `goto`
or `halt`.  For the `PartrecToTM2.tr` statement trees this is still bounded
casework: one pop/peek/load/branch sequence and then either the next label or
halt.  The following definition spells that out directly so computability can
be attacked over the tuple/label presentation rather than through `Stmt`.
-/

private def setStack (S : K' → List Γ') (k : K') (v : List Γ') :
    K' → List Γ' :=
  Function.update S k v

private def pushStack (S : K' → List Γ') (k : K') (g : Γ') :
    K' → List Γ' :=
  setStack S k (g :: S k)

private def popStack (S : K' → List Γ') (k : K') :
    Option Γ' × (K' → List Γ') :=
  ((S k).head?, setStack S k (S k).tail)

/-- Direct casework implementation of `TM2.step tr`. -/
def stepImpl : Cfg' → Option Cfg'
  | ⟨none, _, _⟩ => none
  | ⟨some (Λ'.move p k₁ k₂ q), _, S⟩ =>
      let sS := popStack S k₁
      let s := sS.1
      let S₁ := sS.2
      if s.elim true p then
        some ⟨some q, s, S₁⟩
      else
        some ⟨some (Λ'.move p k₁ k₂ q), s, pushStack S₁ k₂ (s.getD default)⟩
  | ⟨some (Λ'.clear p k q), _, S⟩ =>
      let sS := popStack S k
      let s := sS.1
      let S₁ := sS.2
      if s.elim true p then
        some ⟨some q, s, S₁⟩
      else
        some ⟨some (Λ'.clear p k q), s, S₁⟩
  | ⟨some (Λ'.copy q), _, S⟩ =>
      let sS := popStack S K'.rev
      let s := sS.1
      let S₁ := sS.2
      if s.isSome then
        some ⟨some (Λ'.copy q), s,
          pushStack (pushStack S₁ K'.main (s.getD default)) K'.stack (s.getD default)⟩
      else
        some ⟨some q, s, S₁⟩
  | ⟨some (Λ'.push k f q), v, S⟩ =>
      if (f v).isSome then
        some ⟨some q, v, pushStack S k ((f v).getD default)⟩
      else
        some ⟨some q, v, S⟩
  | ⟨some (Λ'.read q), v, S⟩ =>
      some ⟨some (q v), v, S⟩
  | ⟨some (Λ'.succ q), _, S⟩ =>
      let sS := popStack S K'.main
      let s := sS.1
      let S₁ := sS.2
      if s = some Γ'.bit1 then
        some ⟨some (Λ'.succ q), s, pushStack S₁ K'.rev Γ'.bit0⟩
      else if s = some Γ'.cons then
        some ⟨some (unrev q), s,
          pushStack (pushStack S₁ K'.main Γ'.cons) K'.main Γ'.bit1⟩
      else
        some ⟨some (unrev q), s, pushStack S₁ K'.main Γ'.bit1⟩
  | ⟨some (Λ'.pred q₁ q₂), _, S⟩ =>
      let sS := popStack S K'.main
      let s := sS.1
      let S₁ := sS.2
      if s = some Γ'.bit0 then
        some ⟨some (Λ'.pred q₁ q₂), s, pushStack S₁ K'.rev Γ'.bit1⟩
      else if natEnd (s.getD default) then
        some ⟨some q₁, s, S₁⟩
      else
        let t := (S₁ K'.main).head?
        if natEnd (t.getD default) then
          some ⟨some (unrev q₂), t, S₁⟩
        else
          some ⟨some (unrev q₂), t, pushStack S₁ K'.rev Γ'.bit0⟩
  | ⟨some (Λ'.ret (Cont'.cons₁ fs k)), v, S⟩ =>
      some ⟨some
        (move₂ (fun _ => false) K'.main K'.aux <|
          move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
            move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)),
        v, S⟩
  | ⟨some (Λ'.ret (Cont'.cons₂ k)), v, S⟩ =>
      some ⟨some (head K'.stack <| Λ'.ret k), v, S⟩
  | ⟨some (Λ'.ret (Cont'.comp f k)), v, S⟩ =>
      some ⟨some (trNormal f k), v, S⟩
  | ⟨some (Λ'.ret (Cont'.fix f k)), _, S⟩ =>
      let sS := popStack S K'.main
      let s := sS.1
      let S₁ := sS.2
      if natEnd (s.getD default) then
        some ⟨some (Λ'.ret k), s, S₁⟩
      else
        some ⟨some (Λ'.clear natEnd K'.main <| trNormal f (Cont'.fix f k)), s, S₁⟩
  | ⟨some (Λ'.ret Cont'.halt), _, S⟩ =>
      some ⟨none, none, S⟩

theorem stepImpl_eq : stepImpl = stepOpt := by
  funext c
  cases c with
  | mk l var stk =>
      cases l with
      | none => rfl
      | some l =>
          cases l with
          | move p k₁ k₂ q =>
              simp [stepImpl, stepOpt, tr, pop', push', popStack, pushStack, setStack]
              split <;> (try simp_all) <;> rfl
          | clear p k q =>
              simp [stepImpl, stepOpt, tr, pop', popStack, setStack]
              split <;> (try simp_all) <;> rfl
          | copy q =>
              simp [stepImpl, stepOpt, tr, pop', push', popStack, pushStack, setStack]
              cases hrev : stk K'.rev <;> simp [hrev] <;> rfl
          | push k f q =>
              simp [stepImpl, stepOpt, tr, pushStack, setStack]
              split <;> (try simp_all) <;> rfl
          | read q =>
              rfl
          | succ q =>
              simp [stepImpl, stepOpt, tr, pop', unrev, popStack, pushStack, setStack]
              by_cases h₁ : (stk K'.main).head? = some Γ'.bit1
              · simp [h₁]
                rfl
              · simp [h₁]
                by_cases h₂ : (stk K'.main).head? = some Γ'.cons
                · simp [h₂]
                  rfl
                · simp [h₂]
                  rfl
          | pred q₁ q₂ =>
              simp [stepImpl, stepOpt, tr, pop', peek', unrev, popStack, pushStack, setStack]
              by_cases h₁ : (stk K'.main).head? = some Γ'.bit0
              · simp [h₁]
                rfl
              · simp [h₁]
                by_cases h₂ : natEnd ((stk K'.main).head?.getD Γ'.consₗ) = true
                · simp [natEnd] at h₂
                  simp [h₂]
                  rfl
                · simp [natEnd] at h₂
                  simp [h₂]
                  by_cases h₃ : natEnd ((stk K'.main)[1]?.getD Γ'.consₗ) = true
                  · simp [natEnd] at h₃
                    simp [h₃]
                    rfl
                  · simp [natEnd] at h₃
                    simp [h₃]
                    rfl
          | ret k =>
              cases k with
              | halt =>
                  rfl
              | cons₁ fs k =>
                  rfl
              | cons₂ k =>
                  rfl
              | comp f k =>
                  rfl
              | fix f k =>
                  simp [stepImpl, stepOpt, tr, pop', popStack, setStack]
                  split <;> (try simp_all) <;> rfl

/-! ## Finite support submachine

For a fixed `ToPartrec.Code`, Mathlib's `codeSupp` theorem bounds all control
labels reachable from the corresponding initial label.  The following
definitions package that finite-control submachine without introducing any
global numeric encoding of the infinite `Λ'` type.
-/

/-- The finite support set for a fixed code started with the halting continuation. -/
noncomputable def supportSet (c : Code) : Finset Λ' :=
  codeSupp c Cont'.halt

/-- Control labels restricted to the finite support set. -/
abbrev SuppLabel (c : Code) : Type :=
  {l : Λ' // l ∈ supportSet c}

noncomputable instance (c : Code) : Primcodable (SuppLabel c) :=
  Primcodable.ofEquiv (Fin (Fintype.card (SuppLabel c)))
    (Fintype.equivFin (SuppLabel c))

/-- Tuple-shaped configurations for the finite support submachine. -/
abbrev FinConf (c : Code) : Type :=
  Option (SuppLabel c) × Option Γ' × StackTuple

noncomputable instance (c : Code) : Primcodable (FinConf c) := by
  unfold FinConf
  infer_instance

/-- Embed a finite-support configuration into Mathlib's full TM2 configuration type. -/
def toCfg {c : Code} (fc : FinConf c) : Cfg' :=
  ⟨fc.1.map Subtype.val, fc.2.1, stackEquivTuple.symm fc.2.2⟩

/-- Lift a full configuration whose label is in the finite support back to `FinConf`. -/
def fromCfg {c : Code} (cfg : Cfg')
    (h : cfg.l ∈ Finset.insertNone (supportSet c)) : FinConf c :=
  (match hl : cfg.l with
    | none => none
    | some l =>
        some ⟨l, by
          have hsome : some l ∈ Finset.insertNone (supportSet c) := by
            simpa [hl] using h
          exact Finset.some_mem_insertNone.mp hsome⟩,
    cfg.var,
    stackEquivTuple cfg.stk)

@[simp] theorem toCfg_label_none {c : Code} (v : Option Γ') (S : StackTuple) :
    (toCfg (c := c) (none, v, S)).l = none := rfl

@[simp] theorem toCfg_label_some {c : Code} (l : SuppLabel c)
    (v : Option Γ') (S : StackTuple) :
    (toCfg (c := c) (some l, v, S)).l = some l.1 := rfl

/-- Every embedded finite configuration has a label in the Mathlib support shape. -/
theorem toCfg_label_mem {c : Code} (fc : FinConf c) :
    (toCfg fc).l ∈ Finset.insertNone (supportSet c) := by
  rcases fc with ⟨l, v, S⟩
  cases l with
  | none =>
      simpa [toCfg] using (Finset.none_mem_insertNone (s := supportSet c))
  | some l =>
      exact Finset.some_mem_insertNone.mpr l.2

@[simp] theorem toCfg_fromCfg {c : Code} (cfg : Cfg')
    (h : cfg.l ∈ Finset.insertNone (supportSet c)) :
    toCfg (fromCfg (c := c) cfg h) = cfg := by
  cases cfg with
  | mk l var stk =>
      cases l with
      | none =>
          change (⟨none, var,
            K'.elim (stk K'.main) (stk K'.rev) (stk K'.aux) (stk K'.stack)⟩ : Cfg') =
              ⟨none, var, stk⟩
          rw [show K'.elim (stk K'.main) (stk K'.rev) (stk K'.aux) (stk K'.stack) = stk by
            funext k
            cases k <;> rfl]
      | some l =>
          change (⟨some l, var,
            K'.elim (stk K'.main) (stk K'.rev) (stk K'.aux) (stk K'.stack)⟩ : Cfg') =
              ⟨some l, var, stk⟩
          rw [show K'.elim (stk K'.main) (stk K'.rev) (stk K'.aux) (stk K'.stack) = stk by
            funext k
            cases k <;> rfl]

@[simp] theorem fromCfg_toCfg {c : Code} (fc : FinConf c)
    (h : (toCfg fc).l ∈ Finset.insertNone (supportSet c)) :
    fromCfg (c := c) (toCfg fc) h = fc := by
  rcases fc with ⟨l, v, S⟩
  cases l with
  | none =>
      simp [fromCfg, toCfg]
  | some l =>
      simp [fromCfg, toCfg]

/-- One full-machine step from the support stays in the support. -/
theorem stepOpt_support_mem {c : Code} {cfg cfg' : Cfg'}
    (hcfg : cfg.l ∈ Finset.insertNone (supportSet c))
    (hstep : cfg' ∈ stepOpt cfg) :
    cfg'.l ∈ Finset.insertNone (supportSet c) := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  exact TM2.step_supports tr (tr_supports c Cont'.halt) hstep hcfg

/-- The absorbing full-machine step preserves the finite support. -/
theorem step_support_mem {c : Code} (fc : FinConf c) :
    (step (toCfg fc)).l ∈ Finset.insertNone (supportSet c) := by
  unfold step
  cases h : stepOpt (toCfg fc) with
  | none =>
      simpa [h] using toCfg_label_mem fc
  | some cfg' =>
      have hmem : cfg' ∈ stepOpt (toCfg fc) := by
        exact Option.mem_def.mpr h
      simpa [h] using stepOpt_support_mem (c := c) (toCfg_label_mem fc) hmem

/-- Total absorbing step of the finite support submachine. -/
def finStep {c : Code} (fc : FinConf c) : FinConf c :=
  fromCfg (c := c) (step (toCfg fc)) (step_support_mem fc)

@[simp] theorem toCfg_finStep {c : Code} (fc : FinConf c) :
    toCfg (finStep fc) = step (toCfg fc) := by
  simp [finStep]

/-- Halting test for finite-support configurations. -/
def finHalted {c : Code} (fc : FinConf c) : Bool :=
  fc.1.isNone

@[simp] theorem finHalted_eq_true_iff {c : Code} (fc : FinConf c) :
    finHalted fc = true ↔ fc.1 = none := by
  rcases fc with ⟨l, v, S⟩
  cases l <;> simp [finHalted]

@[simp] theorem finStep_halted {c : Code} (fc : FinConf c)
    (h : finHalted fc = true) :
    finStep fc = fc := by
  rcases fc with ⟨l, v, S⟩
  rw [finHalted_eq_true_iff] at h
  cases h
  unfold finStep step
  have hs : stepOpt (toCfg (c := c) (none, v, S)) = none := by
    rw [← stepImpl_eq]
    rfl
  simp [hs]

/-! ## Computability helpers banked for the finite instance -/

private def listDispatch {A B C : Type} [DecidableEq A]
    (xs : List A) (default : B → C) (f : A → B → C) : A → B → C :=
  match xs with
  | [] => fun _ b => default b
  | x :: xs => fun a b =>
      if a = x then f x b else listDispatch xs default f a b

private theorem computable_eq_bool {A : Type} [Primcodable A]
    [DecidableEq A] (x : A) :
    Computable (fun a : A => decide (a = x)) := by
  exact (PrimrecPred.decide
    (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const x))).to_comp

private theorem listDispatch_computable
    {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    [DecidableEq A] (xs : List A) (default : B → C) (f : A → B → C)
    (hdefault : Computable default) (hf : ∀ a, Computable (f a)) :
    Computable₂ (listDispatch xs default f) := by
  induction xs with
  | nil =>
      exact Computable₂.mk (hdefault.comp Computable.snd)
  | cons x xs ih =>
      refine Computable₂.mk ?_
      have hc : Computable (fun p : A × B => decide (p.1 = x)) :=
        (computable_eq_bool x).comp Computable.fst
      have hthen : Computable (fun p : A × B => f x p.2) :=
        (hf x).comp Computable.snd
      have helse : Computable
          (fun p : A × B => listDispatch xs default f p.1 p.2) := ih
      exact (Computable.cond hc hthen helse).of_eq fun p => by
        rcases p with ⟨a, b⟩
        by_cases h : a = x <;> simp [listDispatch, h]

private theorem listDispatch_eq_of_mem {A B C : Type} [DecidableEq A]
    (xs : List A) (default : B → C) (f : A → B → C)
    {a : A} (ha : a ∈ xs) (b : B) :
    listDispatch xs default f a b = f a b := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [listDispatch]
      · by_cases h : a = x
        · simp [listDispatch, h]
        · simp [listDispatch, h, ih ha]

/--
Finite dispatch for a binary computable function.  The caller supplies a
computable default branch, which is extensionally unreachable after dispatch
over `Finset.univ`.
-/
private theorem finite_dispatch_computable₂
    {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    [Fintype A] [DecidableEq A] (default : B → C)
    (hdefault : Computable default) {f : A → B → C}
    (hf : ∀ a, Computable (f a)) :
    Computable₂ (fun a b => f a b) := by
  let xs := (Finset.univ : Finset A).toList
  refine (listDispatch_computable xs default f hdefault hf).of_eq ?_
  intro p
  rcases p with ⟨a, b⟩
  exact listDispatch_eq_of_mem xs default f (by simp [xs]) b

private theorem computable_of_fintype
    {A B : Type} [Primcodable A] [Primcodable B] [Fintype A]
    [DecidableEq A] [Inhabited A] (f : A → B) :
    Computable f := by
  have h₂ : Computable₂ (fun a (_ : Unit) => f a) :=
    finite_dispatch_computable₂ (A := A) (B := Unit) (C := B)
      (fun _ => f default) (Computable.const (f default))
      (f := fun a _ => f a) (fun a => Computable.const (f a))
  simpa using h₂.comp Computable.id (Computable.const ())

def emptyStackTuple : StackTuple :=
  ([], [], [], [])

def stackGet (S : StackTuple) : K' → List Γ'
  | K'.main => S.1
  | K'.rev => S.2.1
  | K'.aux => S.2.2.1
  | K'.stack => S.2.2.2

theorem stackGet_computable (k : K') :
    Computable (fun S : StackTuple => stackGet S k) := by
  cases k <;> simp [stackGet]
  · exact Computable.fst
  · exact Computable.fst.comp Computable.snd
  · exact Computable.fst.comp (Computable.snd.comp Computable.snd)
  · exact Computable.snd.comp (Computable.snd.comp Computable.snd)

def stackSet (S : StackTuple) (k : K') (v : List Γ') : StackTuple :=
  match k with
  | K'.main => (v, S.2.1, S.2.2.1, S.2.2.2)
  | K'.rev => (S.1, v, S.2.2.1, S.2.2.2)
  | K'.aux => (S.1, S.2.1, v, S.2.2.2)
  | K'.stack => (S.1, S.2.1, S.2.2.1, v)

theorem stackSet_get (S : StackTuple) (k : K') (v : List Γ') (j : K') :
    stackGet (stackSet S k v) j =
      if j = k then v else stackGet S j := by
  cases k <;> cases j <;> rfl

theorem stackSet_get_self (S : StackTuple) (k : K') (v : List Γ') :
    stackGet (stackSet S k v) k = v := by
  cases k <;> rfl

theorem stackSet_get_other (S : StackTuple) {k j : K'} (v : List Γ')
    (h : j ≠ k) :
    stackGet (stackSet S k v) j = stackGet S j := by
  cases k
  · cases j
    · exact False.elim (h rfl)
    · rfl
    · rfl
    · rfl
  · cases j
    · rfl
    · exact False.elim (h rfl)
    · rfl
    · rfl
  · cases j
    · rfl
    · rfl
    · exact False.elim (h rfl)
    · rfl
  · cases j
    · rfl
    · rfl
    · rfl
    · exact False.elim (h rfl)

theorem stackSet_computable (k : K') :
    Computable₂ (fun S : StackTuple => stackSet S k) := by
  refine Computable₂.mk ?_
  cases k <;> simp [stackSet]
  · exact Computable.pair Computable.snd
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.pair
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))))
  · exact Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair Computable.snd
        (Computable.pair
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))))
  · exact Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.pair Computable.snd
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))))
  · exact Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (Computable.pair
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          Computable.snd))

def stackPush (S : StackTuple) (k : K') (g : Γ') :=
  stackSet S k (g :: stackGet S k)

theorem stackPush_get (S : StackTuple) (k : K') (g : Γ') (j : K') :
    stackGet (stackPush S k g) j =
      if j = k then g :: stackGet S k else stackGet S j := by
  cases k <;> cases j <;> rfl

theorem stackPush_get_self (S : StackTuple) (k : K') (g : Γ') :
    stackGet (stackPush S k g) k = g :: stackGet S k := by
  cases k <;> rfl

theorem stackPush_get_other (S : StackTuple) {k j : K'} (g : Γ')
    (h : j ≠ k) :
    stackGet (stackPush S k g) j = stackGet S j := by
  cases k
  · cases j
    · exact False.elim (h rfl)
    · rfl
    · rfl
    · rfl
  · cases j
    · rfl
    · exact False.elim (h rfl)
    · rfl
    · rfl
  · cases j
    · rfl
    · rfl
    · exact False.elim (h rfl)
    · rfl
  · cases j
    · rfl
    · rfl
    · rfl
    · exact False.elim (h rfl)

theorem stackPush_computable {α : Type} [Primcodable α]
    {S : α → StackTuple} {g : α → Γ'} (k : K')
    (hS : Computable S) (hg : Computable g) :
    Computable (fun a => stackPush (S a) k (g a)) := by
  exact (stackSet_computable k).comp hS
    (Computable.list_cons.comp hg ((stackGet_computable k).comp hS))

def stackPop (S : StackTuple) (k : K') :
    Option Γ' × StackTuple :=
  ((stackGet S k).head?, stackSet S k (stackGet S k).tail)

theorem stackPop_head (S : StackTuple) (k : K') :
    (stackPop S k).1 = (stackGet S k).head? := by
  rfl

theorem stackPop_get (S : StackTuple) (k : K') (j : K') :
    stackGet (stackPop S k).2 j =
      if j = k then (stackGet S k).tail else stackGet S j := by
  cases k <;> cases j <;> rfl

theorem stackPop_get_self (S : StackTuple) (k : K') :
    stackGet (stackPop S k).2 k = (stackGet S k).tail := by
  cases k <;> rfl

theorem stackPop_get_other (S : StackTuple) {k j : K'} (h : j ≠ k) :
    stackGet (stackPop S k).2 j = stackGet S j := by
  cases k
  · cases j
    · exact False.elim (h rfl)
    · rfl
    · rfl
    · rfl
  · cases j
    · rfl
    · exact False.elim (h rfl)
    · rfl
    · rfl
  · cases j
    · rfl
    · rfl
    · exact False.elim (h rfl)
    · rfl
  · cases j
    · rfl
    · rfl
    · rfl
    · exact False.elim (h rfl)

theorem stackPop_computable (k : K') :
    Computable (fun S : StackTuple => stackPop S k) := by
  have hget := stackGet_computable k
  have hhead : Computable (fun S : StackTuple => (stackGet S k).head?) :=
    (Primrec.list_head? (α := Γ')).to_comp.comp hget
  have htail : Computable (fun S : StackTuple => (stackGet S k).tail) :=
    (Primrec.list_tail (α := Γ')).to_comp.comp hget
  exact Computable.pair hhead ((stackSet_computable k).comp Computable.id htail)

private theorem finConf_computable {α : Type} [Primcodable α] {c : Code}
    {l : α → Option (SuppLabel c)} {v : α → Option Γ'} {S : α → StackTuple}
    (hl : Computable l) (hv : Computable v) (hS : Computable S) :
    Computable (fun a => ((l a, v a, S a) : FinConf c)) :=
  Computable.pair hl (Computable.pair hv hS)

private theorem finConf_constLabel_computable {α : Type} [Primcodable α] {c : Code}
    (l : Option (SuppLabel c)) {v : α → Option Γ'} {S : α → StackTuple}
    (hv : Computable v) (hS : Computable S) :
    Computable (fun a => ((l, v a, S a) : FinConf c)) :=
  finConf_computable (Computable.const l) hv hS

private theorem optionIsSome_computable {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → Option β} (hf : Computable f) :
    Computable (fun a => (f a).isSome) :=
  (Primrec.option_isSome.to_comp).comp hf

private theorem optionGetDDefault_computable {α β : Type} [Primcodable α] [Primcodable β]
    [Inhabited β] {f : α → Option β} (hf : Computable f) :
    Computable (fun a => (f a).getD default) :=
  (Primrec.option_getD_default.to_comp).comp hf

private theorem eqConst_computable {α β : Type} [Primcodable α] [Primcodable β]
    [DecidableEq β] (b : β) {f : α → β} (hf : Computable f) :
    Computable (fun a => decide (f a = b)) :=
  (computable_eq_bool b).comp hf

private theorem computable_if_bool {α β : Type} [Primcodable α] [Primcodable β]
    {c : α → Bool} {f g : α → β}
    (hc : Computable c) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if c a then f a else g a) :=
  (Computable.cond hc hf hg).of_eq fun a => by
    by_cases h : c a = true <;> simp [h]

private def supportLabelOfStep {c : Code} (fc : FinConf c) (q : Λ')
    (h : (step (toCfg fc)).l = some q) : SuppLabel c :=
  ⟨q, by
    have hmem := step_support_mem fc
    rw [h] at hmem
    exact Finset.some_mem_insertNone.mp hmem⟩

private theorem fromCfg_irrel {c : Code} (cfg : Cfg')
    (h₁ h₂ : cfg.l ∈ Finset.insertNone (supportSet c)) :
    fromCfg (c := c) cfg h₁ = fromCfg (c := c) cfg h₂ := by
  cases cfg with
  | mk l var stk =>
      cases l <;> simp [fromCfg]

private theorem toCfg_injective {c : Code} :
    Function.Injective (@toCfg c) := by
  intro a b h
  rcases a with ⟨la, va, Sa⟩
  rcases b with ⟨lb, vb, Sb⟩
  change (⟨la.map Subtype.val, va, stackEquivTuple.symm Sa⟩ : Cfg') =
      ⟨lb.map Subtype.val, vb, stackEquivTuple.symm Sb⟩ at h
  injection h with hl hv hS
  have hSt : Sa = Sb := stackEquivTuple.symm.injective hS
  cases la with
  | none =>
      cases lb with
      | none => simp [hv, hSt]
      | some lb => cases hl
  | some la =>
      cases lb with
      | none => cases hl
      | some lb =>
          have hlabel : la = lb := Subtype.ext (Option.some.inj hl)
          simp [hlabel, hv, hSt]

def finStepBranch {c : Code}
    (ol : Option (SuppLabel c)) (rest : Option Γ' × StackTuple) : FinConf c :=
  match ol with
  | none => (none, rest.1, rest.2)
  | some ⟨Λ'.move p k₁ k₂ q, hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.move p k₁ k₂ q, hmem⟩
      let q' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
          cases k₁ <;>
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
              stackEquivTuple, popStack, setStack])
      let sS := stackPop rest.2 k₁
      let s := sS.1
      let S₁ := sS.2
      if s.elim true p then
        (some q', s, S₁)
      else
        (some self, s, stackPush S₁ k₂ (s.getD default))
  | some ⟨Λ'.clear p k q, hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.clear p k q, hmem⟩
      let q' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
          cases k <;>
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
              stackEquivTuple, popStack, setStack])
      let sS := stackPop rest.2 k
      let s := sS.1
      let S₁ := sS.2
      if s.elim true p then
        (some q', s, S₁)
      else
        (some self, s, S₁)
  | some ⟨Λ'.copy q, hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.copy q, hmem⟩
      let q' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
          simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
            stackEquivTuple, popStack, setStack])
      let sS := stackPop rest.2 K'.rev
      let s := sS.1
      let S₁ := sS.2
      if s.isSome then
        (some self, s,
          stackPush (stackPush S₁ K'.main (s.getD default)) K'.stack (s.getD default))
      else
        (some q', s, S₁)
  | some ⟨Λ'.push k f q, hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.push k f q, hmem⟩
      let q' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
          by_cases hf : (f none).isSome = true
          · simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
              stackEquivTuple, pushStack, setStack, hf]
          · simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
              stackEquivTuple, pushStack, setStack, hf])
      if (f rest.1).isSome then
        (some q', rest.1, stackPush rest.2 k ((f rest.1).getD default))
      else
        (some q', rest.1, rest.2)
  | some ⟨Λ'.read q, hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.read q, hmem⟩
      let q' : Option Γ' → SuppLabel c := fun v =>
        supportLabelOfStep (c := c) (some self, v, emptyStackTuple) (q v) (by
          simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple, stackEquivTuple])
      (some (q' rest.1), rest.1, rest.2)
  | some ⟨Λ'.succ q, hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.succ q, hmem⟩
      let uq : SuppLabel c :=
        supportLabelOfStep (c := c)
          (some self, none, ([Γ'.cons], [], [], [])) (unrev q) (by
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, stackEquivTuple, stackGet, stackSet,
              popStack, pushStack, setStack, unrev])
      let sS := stackPop rest.2 K'.main
      let s := sS.1
      let S₁ := sS.2
      if s = some Γ'.bit1 then
        (some self, s, stackPush S₁ K'.rev Γ'.bit0)
      else if s = some Γ'.cons then
        (some uq, s, stackPush (stackPush S₁ K'.main Γ'.cons) K'.main Γ'.bit1)
      else
        (some uq, s, stackPush S₁ K'.main Γ'.bit1)
  | some ⟨Λ'.pred q₁ q₂, hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.pred q₁ q₂, hmem⟩
      let q₁' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q₁ (by
          simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
            stackEquivTuple, popStack, setStack])
      let uq₂ : SuppLabel c :=
        supportLabelOfStep (c := c)
          (some self, none, ([Γ'.bit1], [], [], [])) (unrev q₂) (by
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, stackEquivTuple, stackGet, stackSet,
              popStack, pushStack, setStack, unrev, natEnd])
      let sS := stackPop rest.2 K'.main
      let s := sS.1
      let S₁ := sS.2
      if s = some Γ'.bit0 then
        (some self, s, stackPush S₁ K'.rev Γ'.bit1)
      else if natEnd (s.getD default) then
        (some q₁', s, S₁)
      else
        let t := (stackGet S₁ K'.main).head?
        if natEnd (t.getD default) then
          (some uq₂, t, S₁)
        else
          (some uq₂, t, stackPush S₁ K'.rev Γ'.bit0)
  | some ⟨Λ'.ret (Cont'.cons₁ fs k), hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.ret (Cont'.cons₁ fs k), hmem⟩
      let q' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
          (move₂ (fun _ => false) K'.main K'.aux <|
            move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
              move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) (by
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple, stackEquivTuple])
      (some q', rest.1, rest.2)
  | some ⟨Λ'.ret (Cont'.cons₂ k), hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.ret (Cont'.cons₂ k), hmem⟩
      let q' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
          (head K'.stack <| Λ'.ret k) (by
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple, stackEquivTuple])
      (some q', rest.1, rest.2)
  | some ⟨Λ'.ret (Cont'.comp f k), hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.ret (Cont'.comp f k), hmem⟩
      let q' : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
          (trNormal f k) (by
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple, stackEquivTuple])
      (some q', rest.1, rest.2)
  | some ⟨Λ'.ret (Cont'.fix f k), hmem⟩ =>
      let self : SuppLabel c := ⟨Λ'.ret (Cont'.fix f k), hmem⟩
      let rk : SuppLabel c :=
        supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
          (Λ'.ret k) (by
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
              stackEquivTuple, popStack, setStack])
      let cf : SuppLabel c :=
        supportLabelOfStep (c := c)
          (some self, none, ([Γ'.bit1], [], [], []))
          (Λ'.clear natEnd K'.main <| trNormal f (Cont'.fix f k)) (by
            simp [step, ← stepImpl_eq, stepImpl, toCfg, self, stackEquivTuple, stackGet, stackSet,
              popStack, setStack, natEnd])
      let sS := stackPop rest.2 K'.main
      let s := sS.1
      let S₁ := sS.2
      if natEnd (s.getD default) then
        (some rk, s, S₁)
      else
        (some cf, s, S₁)
  | some ⟨Λ'.ret Cont'.halt, _⟩ =>
      (none, none, rest.2)

theorem finStepBranch_computable {c : Code}
    (ol : Option (SuppLabel c)) :
    Computable (finStepBranch (c := c) ol) := by
  cases ol with
  | none =>
      simpa [finStepBranch] using
        (finConf_constLabel_computable (c := c) (α := Option Γ' × StackTuple)
          none Computable.fst Computable.snd)
  | some l =>
      rcases l with ⟨lv, hmem⟩
      cases lv with
      | move p k₁ k₂ q =>
          let self : SuppLabel c := ⟨Λ'.move p k₁ k₂ q, hmem⟩
          let q' : SuppLabel c :=
            supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
              cases k₁ <;>
                simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                  stackEquivTuple, popStack, setStack])
          have hpop : Computable (fun rest : Option Γ' × StackTuple => stackPop rest.2 k₁) :=
            (stackPop_computable k₁).comp Computable.snd
          have hs : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 k₁).1) := Computable.fst.comp hpop
          have hS₁ : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 k₁).2) := Computable.snd.comp hpop
          have hc : Computable (fun rest : Option Γ' × StackTuple =>
              ((stackPop rest.2 k₁).1).elim true p) :=
            (computable_of_fintype (fun s : Option Γ' => s.elim true p)).comp hs
          have hthen : Computable (fun rest : Option Γ' × StackTuple =>
              ((some q', (stackPop rest.2 k₁).1, (stackPop rest.2 k₁).2) : FinConf c)) :=
            finConf_constLabel_computable (some q') hs hS₁
          have hval : Computable (fun rest : Option Γ' × StackTuple =>
              ((stackPop rest.2 k₁).1).getD default) :=
            optionGetDDefault_computable hs
          have hpush : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPop rest.2 k₁).2 k₂ (((stackPop rest.2 k₁).1).getD default)) :=
            stackPush_computable k₂ hS₁ hval
          have helse : Computable (fun rest : Option Γ' × StackTuple =>
              ((some self, (stackPop rest.2 k₁).1,
                stackPush (stackPop rest.2 k₁).2 k₂ (((stackPop rest.2 k₁).1).getD default)) :
                FinConf c)) :=
            finConf_constLabel_computable (some self) hs hpush
          simpa [finStepBranch, self, q', stackPop] using computable_if_bool hc hthen helse
      | clear p k q =>
          let self : SuppLabel c := ⟨Λ'.clear p k q, hmem⟩
          let q' : SuppLabel c :=
            supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
              cases k <;>
                simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                  stackEquivTuple, popStack, setStack])
          have hpop : Computable (fun rest : Option Γ' × StackTuple => stackPop rest.2 k) :=
            (stackPop_computable k).comp Computable.snd
          have hs : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 k).1) := Computable.fst.comp hpop
          have hS₁ : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 k).2) := Computable.snd.comp hpop
          have hc : Computable (fun rest : Option Γ' × StackTuple =>
              ((stackPop rest.2 k).1).elim true p) :=
            (computable_of_fintype (fun s : Option Γ' => s.elim true p)).comp hs
          have hthen : Computable (fun rest : Option Γ' × StackTuple =>
              ((some q', (stackPop rest.2 k).1, (stackPop rest.2 k).2) : FinConf c)) :=
            finConf_constLabel_computable (some q') hs hS₁
          have helse : Computable (fun rest : Option Γ' × StackTuple =>
              ((some self, (stackPop rest.2 k).1, (stackPop rest.2 k).2) : FinConf c)) :=
            finConf_constLabel_computable (some self) hs hS₁
          simpa [finStepBranch, self, q', stackPop] using computable_if_bool hc hthen helse
      | copy q =>
          let self : SuppLabel c := ⟨Λ'.copy q, hmem⟩
          let q' : SuppLabel c :=
            supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
              simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                stackEquivTuple, popStack, setStack])
          have hpop : Computable (fun rest : Option Γ' × StackTuple => stackPop rest.2 K'.rev) :=
            (stackPop_computable K'.rev).comp Computable.snd
          have hs : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 K'.rev).1) := Computable.fst.comp hpop
          have hS₁ : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 K'.rev).2) := Computable.snd.comp hpop
          have hc : Computable (fun rest : Option Γ' × StackTuple =>
              ((stackPop rest.2 K'.rev).1).isSome) := optionIsSome_computable hs
          have hval : Computable (fun rest : Option Γ' × StackTuple =>
              ((stackPop rest.2 K'.rev).1).getD default) :=
            optionGetDDefault_computable hs
          have hmain : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPop rest.2 K'.rev).2 K'.main
                (((stackPop rest.2 K'.rev).1).getD default)) :=
            stackPush_computable K'.main hS₁ hval
          have hboth : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush
                (stackPush (stackPop rest.2 K'.rev).2 K'.main
                  (((stackPop rest.2 K'.rev).1).getD default))
                K'.stack (((stackPop rest.2 K'.rev).1).getD default)) :=
            stackPush_computable K'.stack hmain hval
          have hthen : Computable (fun rest : Option Γ' × StackTuple =>
              ((some self, (stackPop rest.2 K'.rev).1,
                stackPush
                  (stackPush (stackPop rest.2 K'.rev).2 K'.main
                    (((stackPop rest.2 K'.rev).1).getD default))
                  K'.stack (((stackPop rest.2 K'.rev).1).getD default)) : FinConf c)) :=
            finConf_constLabel_computable (some self) hs hboth
          have helse : Computable (fun rest : Option Γ' × StackTuple =>
              ((some q', (stackPop rest.2 K'.rev).1, (stackPop rest.2 K'.rev).2) :
                FinConf c)) :=
            finConf_constLabel_computable (some q') hs hS₁
          exact (computable_if_bool hc hthen helse).of_eq fun rest => by
            by_cases h : ((stackPop rest.2 K'.rev).1).isSome = true
            · simp [finStepBranch, self, q', stackPop, h]
            · simp [finStepBranch, self, q', stackPop, h]
      | push k f q =>
          let self : SuppLabel c := ⟨Λ'.push k f q, hmem⟩
          let q' : SuppLabel c :=
            supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q (by
              by_cases hf : (f none).isSome = true
              · simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                  stackEquivTuple, pushStack, setStack, hf]
              · simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                  stackEquivTuple, pushStack, setStack, hf])
          have hf : Computable (fun rest : Option Γ' × StackTuple => f rest.1) :=
            (computable_of_fintype f).comp Computable.fst
          have hc : Computable (fun rest : Option Γ' × StackTuple => (f rest.1).isSome) :=
            optionIsSome_computable hf
          have hval : Computable (fun rest : Option Γ' × StackTuple =>
              (f rest.1).getD default) := optionGetDDefault_computable hf
          have hpush : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush rest.2 k ((f rest.1).getD default)) :=
            stackPush_computable k Computable.snd hval
          have hthen : Computable (fun rest : Option Γ' × StackTuple =>
              ((some q', rest.1, stackPush rest.2 k ((f rest.1).getD default)) : FinConf c)) :=
            finConf_constLabel_computable (some q') Computable.fst hpush
          have helse : Computable (fun rest : Option Γ' × StackTuple =>
              ((some q', rest.1, rest.2) : FinConf c)) :=
            finConf_constLabel_computable (some q') Computable.fst Computable.snd
          simpa [finStepBranch, self, q'] using computable_if_bool hc hthen helse
      | read q =>
          let self : SuppLabel c := ⟨Λ'.read q, hmem⟩
          let q' : Option Γ' → SuppLabel c := fun v =>
            supportLabelOfStep (c := c) (some self, v, emptyStackTuple) (q v) (by
              simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                stackEquivTuple])
          have hlabel : Computable (fun rest : Option Γ' × StackTuple => some (q' rest.1)) :=
            Computable.option_some.comp ((computable_of_fintype q').comp Computable.fst)
          simpa [finStepBranch, self, q'] using
            (finConf_computable (c := c) hlabel Computable.fst Computable.snd)
      | succ q =>
          let self : SuppLabel c := ⟨Λ'.succ q, hmem⟩
          let uq : SuppLabel c :=
            supportLabelOfStep (c := c)
              (some self, none, ([Γ'.cons], [], [], [])) (unrev q) (by
                simp [step, ← stepImpl_eq, stepImpl, toCfg, self, stackEquivTuple, stackGet, stackSet,
              popStack, pushStack, setStack, unrev])
          have hpop : Computable (fun rest : Option Γ' × StackTuple => stackPop rest.2 K'.main) :=
            (stackPop_computable K'.main).comp Computable.snd
          have hs : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 K'.main).1) := Computable.fst.comp hpop
          have hS₁ : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 K'.main).2) := Computable.snd.comp hpop
          have hbit1 : Computable (fun rest : Option Γ' × StackTuple =>
              decide ((stackPop rest.2 K'.main).1 = some Γ'.bit1)) :=
            eqConst_computable (some Γ'.bit1) hs
          have hcons : Computable (fun rest : Option Γ' × StackTuple =>
              decide ((stackPop rest.2 K'.main).1 = some Γ'.cons)) :=
            eqConst_computable (some Γ'.cons) hs
          have hrev0 : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit0) :=
            stackPush_computable K'.rev hS₁ (Computable.const Γ'.bit0)
          have hmainCons : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPop rest.2 K'.main).2 K'.main Γ'.cons) :=
            stackPush_computable K'.main hS₁ (Computable.const Γ'.cons)
          have hmainConsBit : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPush (stackPop rest.2 K'.main).2 K'.main Γ'.cons)
                K'.main Γ'.bit1) :=
            stackPush_computable K'.main hmainCons (Computable.const Γ'.bit1)
          have hmainBit : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPop rest.2 K'.main).2 K'.main Γ'.bit1) :=
            stackPush_computable K'.main hS₁ (Computable.const Γ'.bit1)
          have hthen : Computable (fun rest : Option Γ' × StackTuple =>
              ((some self, (stackPop rest.2 K'.main).1,
                stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit0) : FinConf c)) :=
            finConf_constLabel_computable (some self) hs hrev0
          have hconsBranch : Computable (fun rest : Option Γ' × StackTuple =>
              ((some uq, (stackPop rest.2 K'.main).1,
                stackPush (stackPush (stackPop rest.2 K'.main).2 K'.main Γ'.cons)
                  K'.main Γ'.bit1) : FinConf c)) :=
            finConf_constLabel_computable (some uq) hs hmainConsBit
          have helseBranch : Computable (fun rest : Option Γ' × StackTuple =>
              ((some uq, (stackPop rest.2 K'.main).1,
                stackPush (stackPop rest.2 K'.main).2 K'.main Γ'.bit1) : FinConf c)) :=
            finConf_constLabel_computable (some uq) hs hmainBit
          have helse : Computable (fun rest : Option Γ' × StackTuple =>
              if decide ((stackPop rest.2 K'.main).1 = some Γ'.cons) then
                ((some uq, (stackPop rest.2 K'.main).1,
                  stackPush (stackPush (stackPop rest.2 K'.main).2 K'.main Γ'.cons)
                    K'.main Γ'.bit1) : FinConf c)
              else
                ((some uq, (stackPop rest.2 K'.main).1,
                  stackPush (stackPop rest.2 K'.main).2 K'.main Γ'.bit1) : FinConf c)) :=
            computable_if_bool hcons hconsBranch helseBranch
          have hall := computable_if_bool hbit1 hthen helse
          exact hall.of_eq fun rest => by
            by_cases h₁ : (stackPop rest.2 K'.main).1 = some Γ'.bit1
            · simp [finStepBranch, self, uq, stackPop, h₁]
            · by_cases h₂ : (stackPop rest.2 K'.main).1 = some Γ'.cons
              · simp [finStepBranch, self, uq, stackPop, h₁, h₂]
              · simp [finStepBranch, self, uq, stackPop, h₁, h₂]
      | pred q₁ q₂ =>
          let self : SuppLabel c := ⟨Λ'.pred q₁ q₂, hmem⟩
          let q₁' : SuppLabel c :=
            supportLabelOfStep (c := c) (some self, none, emptyStackTuple) q₁ (by
              simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                stackEquivTuple, popStack, setStack])
          let uq₂ : SuppLabel c :=
            supportLabelOfStep (c := c)
              (some self, none, ([Γ'.bit1], [], [], [])) (unrev q₂) (by
                simp [step, ← stepImpl_eq, stepImpl, toCfg, self, stackEquivTuple, stackGet, stackSet,
              popStack, pushStack, setStack, unrev, natEnd])
          have hpop : Computable (fun rest : Option Γ' × StackTuple => stackPop rest.2 K'.main) :=
            (stackPop_computable K'.main).comp Computable.snd
          have hs : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 K'.main).1) := Computable.fst.comp hpop
          have hS₁ : Computable (fun rest : Option Γ' × StackTuple =>
              (stackPop rest.2 K'.main).2) := Computable.snd.comp hpop
          have hbit0 : Computable (fun rest : Option Γ' × StackTuple =>
              decide ((stackPop rest.2 K'.main).1 = some Γ'.bit0)) :=
            eqConst_computable (some Γ'.bit0) hs
          have hsDefault : Computable (fun rest : Option Γ' × StackTuple =>
              ((stackPop rest.2 K'.main).1).getD default) :=
            optionGetDDefault_computable hs
          have hnatS : Computable (fun rest : Option Γ' × StackTuple =>
              natEnd (((stackPop rest.2 K'.main).1).getD default)) :=
            (computable_of_fintype natEnd).comp hsDefault
          have hmainHead : Computable (fun rest : Option Γ' × StackTuple =>
              (stackGet (stackPop rest.2 K'.main).2 K'.main).head?) :=
            (Primrec.list_head? (α := Γ')).to_comp.comp
              ((stackGet_computable K'.main).comp hS₁)
          have htDefault : Computable (fun rest : Option Γ' × StackTuple =>
              ((stackGet (stackPop rest.2 K'.main).2 K'.main).head?).getD default) :=
            optionGetDDefault_computable hmainHead
          have hnatT : Computable (fun rest : Option Γ' × StackTuple =>
              natEnd (((stackGet (stackPop rest.2 K'.main).2 K'.main).head?).getD default)) :=
            (computable_of_fintype natEnd).comp htDefault
          have hrev1 : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit1) :=
            stackPush_computable K'.rev hS₁ (Computable.const Γ'.bit1)
          have hrev0 : Computable (fun rest : Option Γ' × StackTuple =>
              stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit0) :=
            stackPush_computable K'.rev hS₁ (Computable.const Γ'.bit0)
          have hloop : Computable (fun rest : Option Γ' × StackTuple =>
              ((some self, (stackPop rest.2 K'.main).1,
                stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit1) : FinConf c)) :=
            finConf_constLabel_computable (some self) hs hrev1
          have hq₁ : Computable (fun rest : Option Γ' × StackTuple =>
              ((some q₁', (stackPop rest.2 K'.main).1, (stackPop rest.2 K'.main).2) :
                FinConf c)) :=
            finConf_constLabel_computable (some q₁') hs hS₁
          have htNoPush : Computable (fun rest : Option Γ' × StackTuple =>
              ((some uq₂, (stackGet (stackPop rest.2 K'.main).2 K'.main).head?,
                (stackPop rest.2 K'.main).2) : FinConf c)) :=
            finConf_constLabel_computable (some uq₂) hmainHead hS₁
          have htPush : Computable (fun rest : Option Γ' × StackTuple =>
              ((some uq₂, (stackGet (stackPop rest.2 K'.main).2 K'.main).head?,
                stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit0) : FinConf c)) :=
            finConf_constLabel_computable (some uq₂) hmainHead hrev0
          have htBranch : Computable (fun rest : Option Γ' × StackTuple =>
              if natEnd (((stackGet (stackPop rest.2 K'.main).2 K'.main).head?).getD default) then
                ((some uq₂, (stackGet (stackPop rest.2 K'.main).2 K'.main).head?,
                  (stackPop rest.2 K'.main).2) : FinConf c)
              else
                ((some uq₂, (stackGet (stackPop rest.2 K'.main).2 K'.main).head?,
                  stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit0) : FinConf c)) :=
            computable_if_bool hnatT htNoPush htPush
          have hnotNatBranch : Computable (fun rest : Option Γ' × StackTuple =>
              if natEnd (((stackPop rest.2 K'.main).1).getD default) then
                ((some q₁', (stackPop rest.2 K'.main).1, (stackPop rest.2 K'.main).2) :
                  FinConf c)
              else
                if natEnd (((stackGet (stackPop rest.2 K'.main).2 K'.main).head?).getD default) then
                  ((some uq₂, (stackGet (stackPop rest.2 K'.main).2 K'.main).head?,
                    (stackPop rest.2 K'.main).2) : FinConf c)
                else
                  ((some uq₂, (stackGet (stackPop rest.2 K'.main).2 K'.main).head?,
                    stackPush (stackPop rest.2 K'.main).2 K'.rev Γ'.bit0) : FinConf c)) :=
            computable_if_bool hnatS hq₁ htBranch
          have hall := computable_if_bool hbit0 hloop hnotNatBranch
          exact hall.of_eq fun rest => by
            by_cases h₀ : (stackPop rest.2 K'.main).1 = some Γ'.bit0
            · simp [finStepBranch, self, q₁', uq₂, stackPop, h₀]
            · by_cases hsN : natEnd (((stackPop rest.2 K'.main).1).getD default) = true
              · simp [finStepBranch, self, q₁', uq₂, stackPop, h₀, hsN]
              · by_cases htN :
                    natEnd (((stackGet (stackPop rest.2 K'.main).2 K'.main).head?).getD default) =
                      true
                · simp [finStepBranch, self, q₁', uq₂, stackPop, h₀, hsN, htN]
                · simp [finStepBranch, self, q₁', uq₂, stackPop, h₀, hsN, htN]
      | ret k =>
          cases k with
          | cons₁ fs k =>
              let self : SuppLabel c := ⟨Λ'.ret (Cont'.cons₁ fs k), hmem⟩
              let q' : SuppLabel c :=
                supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
                  (move₂ (fun _ => false) K'.main K'.aux <|
                    move₂ (fun s => s = Γ'.consₗ) K'.stack K'.main <|
                      move₂ (fun _ => false) K'.aux K'.stack <| trNormal fs (Cont'.cons₂ k)) (by
                    simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                      stackEquivTuple])
              simpa [finStepBranch, self, q'] using
                (finConf_constLabel_computable (c := c) (α := Option Γ' × StackTuple)
                  (some q') Computable.fst Computable.snd)
          | cons₂ k =>
              let self : SuppLabel c := ⟨Λ'.ret (Cont'.cons₂ k), hmem⟩
              let q' : SuppLabel c :=
                supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
                  (head K'.stack <| Λ'.ret k) (by
                    simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                      stackEquivTuple])
              simpa [finStepBranch, self, q'] using
                (finConf_constLabel_computable (c := c) (α := Option Γ' × StackTuple)
                  (some q') Computable.fst Computable.snd)
          | comp f k =>
              let self : SuppLabel c := ⟨Λ'.ret (Cont'.comp f k), hmem⟩
              let q' : SuppLabel c :=
                supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
                  (trNormal f k) (by
                    simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                      stackEquivTuple])
              simpa [finStepBranch, self, q'] using
                (finConf_constLabel_computable (c := c) (α := Option Γ' × StackTuple)
                  (some q') Computable.fst Computable.snd)
          | fix f k =>
              let self : SuppLabel c := ⟨Λ'.ret (Cont'.fix f k), hmem⟩
              let rk : SuppLabel c :=
                supportLabelOfStep (c := c) (some self, none, emptyStackTuple)
                  (Λ'.ret k) (by
                    simp [step, ← stepImpl_eq, stepImpl, toCfg, self, emptyStackTuple,
                      stackEquivTuple, popStack, setStack])
              let cf : SuppLabel c :=
                supportLabelOfStep (c := c)
                  (some self, none, ([Γ'.bit1], [], [], []))
                  (Λ'.clear natEnd K'.main <| trNormal f (Cont'.fix f k)) (by
                    simp [step, ← stepImpl_eq, stepImpl, toCfg, self, stackEquivTuple, stackGet, stackSet,
              popStack, setStack, natEnd])
              have hpop : Computable (fun rest : Option Γ' × StackTuple =>
                  stackPop rest.2 K'.main) :=
                (stackPop_computable K'.main).comp Computable.snd
              have hs : Computable (fun rest : Option Γ' × StackTuple =>
                  (stackPop rest.2 K'.main).1) := Computable.fst.comp hpop
              have hS₁ : Computable (fun rest : Option Γ' × StackTuple =>
                  (stackPop rest.2 K'.main).2) := Computable.snd.comp hpop
              have hsDefault : Computable (fun rest : Option Γ' × StackTuple =>
                  ((stackPop rest.2 K'.main).1).getD default) :=
                optionGetDDefault_computable hs
              have hnatS : Computable (fun rest : Option Γ' × StackTuple =>
                  natEnd (((stackPop rest.2 K'.main).1).getD default)) :=
                (computable_of_fintype natEnd).comp hsDefault
              have hthen : Computable (fun rest : Option Γ' × StackTuple =>
                  ((some rk, (stackPop rest.2 K'.main).1, (stackPop rest.2 K'.main).2) :
                    FinConf c)) :=
                finConf_constLabel_computable (some rk) hs hS₁
              have helse : Computable (fun rest : Option Γ' × StackTuple =>
                  ((some cf, (stackPop rest.2 K'.main).1, (stackPop rest.2 K'.main).2) :
                    FinConf c)) :=
                finConf_constLabel_computable (some cf) hs hS₁
              simpa [finStepBranch, self, rk, cf, stackPop] using
                computable_if_bool hnatS hthen helse
          | halt =>
              simpa [finStepBranch] using
                (finConf_constLabel_computable (c := c) (α := Option Γ' × StackTuple)
                  none (Computable.const none) Computable.snd)

theorem toCfg_finStepBranch {c : Code} (fc : FinConf c) :
    toCfg (finStepBranch (c := c) fc.1 fc.2) = step (toCfg fc) := by
  rcases fc with ⟨ol, v, S⟩
  cases ol with
  | none =>
      simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg]
  | some l =>
      rcases l with ⟨lv, hmem⟩
      cases lv with
      | move p k₁ k₂ q =>
          cases k₁ <;> cases k₂ <;>
            simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
              stackEquivTuple, stackGet, stackSet, stackPop, stackPush, popStack, pushStack, setStack] <;>
            repeat (first | split | simp_all | rfl)
      | clear p k q =>
          cases k <;>
            simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
              stackEquivTuple, stackGet, stackSet, stackPop, popStack, setStack] <;>
            repeat (first | split | simp_all | rfl)
      | copy q =>
          simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
            stackEquivTuple, stackGet, stackSet, stackPop, stackPush, popStack, pushStack, setStack] <;>
          repeat (first | split | simp_all | rfl)
      | push k f q =>
          cases k <;>
            simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
              stackEquivTuple, stackGet, stackSet, stackPush, pushStack, setStack] <;>
            repeat (first | split | simp_all | rfl)
      | read q =>
          simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
            stackEquivTuple]
      | succ q =>
          simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
            stackEquivTuple, stackGet, stackSet, stackPop, stackPush, popStack, pushStack, setStack, unrev] <;>
          repeat (first | split | simp_all | rfl)
      | pred q₁ q₂ =>
          simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
            stackEquivTuple, stackGet, stackSet, stackPop, stackPush, stackGet, popStack, pushStack, setStack,
            unrev, natEnd] <;>
          repeat (first | split | simp_all | rfl)
      | ret k =>
          cases k with
          | cons₁ fs k =>
              simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
                stackEquivTuple]
          | cons₂ k =>
              simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
                stackEquivTuple]
          | comp f k =>
              simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
                stackEquivTuple]
          | fix f k =>
              simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, supportLabelOfStep,
                stackEquivTuple, stackGet, stackSet, stackPop, popStack, setStack, natEnd] <;>
              repeat (first | split | simp_all | rfl)
          | halt =>
              simp [finStepBranch, step, ← stepImpl_eq, stepImpl, toCfg, stackEquivTuple]

theorem finStepBranch_eq_finStep {c : Code} (fc : FinConf c) :
    finStepBranch (c := c) fc.1 fc.2 = finStep fc :=
  toCfg_injective (by rw [toCfg_finStepBranch, toCfg_finStep])

theorem finStep_computable :
    Computable (finStep (c := c_f)) := by
  let defaultBranch : Option Γ' × StackTuple → FinConf c_f :=
    fun rest => (none, rest.1, rest.2)
  have hdefault : Computable defaultBranch :=
    finConf_constLabel_computable (c := c_f) (α := Option Γ' × StackTuple)
      none Computable.fst Computable.snd
  have hdispatch : Computable₂ (fun ol rest => finStepBranch (c := c_f) ol rest) :=
    finite_dispatch_computable₂
      (A := Option (SuppLabel c_f)) (B := Option Γ' × StackTuple) (C := FinConf c_f)
      defaultBranch hdefault (f := fun ol rest => finStepBranch (c := c_f) ol rest)
      (finStepBranch_computable (c := c_f))
  exact (hdispatch.comp Computable.fst Computable.snd).of_eq fun fc =>
    finStepBranch_eq_finStep fc

private noncomputable def finInitLabel : SuppLabel c_f :=
  ⟨trNormal c_f Cont'.halt, by
    change trNormal c_f Cont'.halt ∈ codeSupp c_f Cont'.halt
    exact codeSupp_self c_f Cont'.halt (trStmts₁_self _)⟩

noncomputable def finInit (n : ℕ) : FinConf c_f :=
  (some finInitLabel, none, (trList [n], [], [], []))

private theorem toCfg_finInit (n : ℕ) :
    toCfg (finInit n) = init c_f [n] := by
  simp [finInit, finInitLabel, init, PartrecToTM2.init, toCfg, stackEquivTuple]


private theorem trNat_bit (b : Bool) (n : ℕ)
    (h : b = true ∨ n ≠ 0) :
    trNat (Nat.bit b n) =
      (if b then Γ'.bit1 else Γ'.bit0) :: trNat n := by
  unfold trNat
  rw [← Num.ofNat'_eq (Nat.bit b n), Num.ofNat'_bit, Num.ofNat'_eq n]
  cases b
  · simp only [Bool.false_eq_true, false_or] at h
    have hnNum : (n : Num) ≠ 0 := by
      intro hz
      have hzNat := congrArg (fun x : Num => (x : ℕ)) hz
      exact h (by simpa [Num.to_of_nat] using hzNat)
    cases hn : (n : Num) with
    | zero => exact (hnNum hn).elim
    | pos _ => simp [trNum, Num.bit0, trPosNum]
  · cases hn : (n : Num) <;> simp [trNum, Num.bit1, trPosNum]

private theorem trNat_rec (n : ℕ) :
    trNat n = if n = 0 then [] else
      (if n.bodd then Γ'.bit1 else Γ'.bit0) :: trNat n.div2 := by
  by_cases hn : n = 0
  · simp [hn, trNat_zero]
  · simp [hn]
    conv_lhs => rw [← Nat.bit_bodd_div2 n]
    rw [trNat_bit]
    by_cases hb : n.bodd = true
    · left; exact hb
    · right
      intro hd
      have hbf : n.bodd = false := by
        cases hbn : n.bodd
        · rfl
        · exact (hb hbn).elim
      have : n = 0 := by
        rw [← Nat.bit_bodd_div2 n, hbf, hd]
        rfl
      exact hn this

private def trNatRecStep (_ : Unit) (L : List (List Γ')) :
    Option (List Γ') :=
  let n := L.length
  some <| if n = 0 then [] else
    (if n.bodd then Γ'.bit1 else Γ'.bit0) :: (L[n.div2]?.getD [])

private theorem trNatRecStep_spec (u : Unit) (n : ℕ) :
    trNatRecStep u ((List.range n).map trNat) = some (trNat n) := by
  by_cases hn : n = 0
  · simp [trNatRecStep, hn, trNat_zero]
  · have hdivlt : n.div2 < n := by
      rw [Nat.div2_val]
      omega
    have hget : ((List.range n).map trNat)[n.div2]? =
        some (trNat n.div2) := by
      simp [hdivlt]
    rw [trNat_rec n]
    simp [trNatRecStep, hn, hget]

private theorem trNatRecStep_computable : Computable₂ trNatRecStep := by
  refine Computable₂.mk ?_
  let len : Unit × List (List Γ') → ℕ := fun p => p.2.length
  have hlen : Computable len := Computable.list_length.comp Computable.snd
  have hzero : Computable (fun p : Unit × List (List Γ') => (len p == 0)) :=
    Primrec.beq.to_comp.comp hlen (Computable.const 0)
  have hbodd : Computable (fun p : Unit × List (List Γ') => (len p).bodd) :=
    Computable.nat_bodd.comp hlen
  have hidx : Computable (fun p : Unit × List (List Γ') => (len p).div2) :=
    Computable.nat_div2.comp hlen
  have hgetOpt : Computable
      (fun p : Unit × List (List Γ') => p.2[(len p).div2]?) :=
    Computable.list_getElem?.comp Computable.snd hidx
  have htail : Computable
      (fun p : Unit × List (List Γ') => (p.2[(len p).div2]?).getD []) :=
    Computable.option_getD hgetOpt (Computable.const [])
  have hbit0 : Computable
      (fun p : Unit × List (List Γ') =>
        Γ'.bit0 :: (p.2[(len p).div2]?).getD []) :=
    Computable.list_cons.comp (Computable.const Γ'.bit0) htail
  have hbit1 : Computable
      (fun p : Unit × List (List Γ') =>
        Γ'.bit1 :: (p.2[(len p).div2]?).getD []) :=
    Computable.list_cons.comp (Computable.const Γ'.bit1) htail
  have hnonzero : Computable
      (fun p : Unit × List (List Γ') => cond ((len p).bodd)
        (Γ'.bit1 :: (p.2[(len p).div2]?).getD [])
        (Γ'.bit0 :: (p.2[(len p).div2]?).getD [])) :=
    Computable.cond hbodd hbit1 hbit0
  have hall : Computable
      (fun p : Unit × List (List Γ') => cond (len p == 0) []
        (cond ((len p).bodd)
          (Γ'.bit1 :: (p.2[(len p).div2]?).getD [])
          (Γ'.bit0 :: (p.2[(len p).div2]?).getD []))) :=
    Computable.cond hzero (Computable.const []) hnonzero
  exact (Computable.option_some.comp hall).of_eq fun p => by
    rcases p with ⟨_, L⟩
    by_cases hnil : L = []
    · simp [trNatRecStep, len, hnil]
    · have hlen_ne : L.length ≠ 0 := by
        intro hz
        exact hnil (List.length_eq_zero_iff.mp hz)
      have hbeq : (L.length == 0) = false := by
        cases hb : (L.length == 0)
        · rfl
        · exact (hlen_ne (beq_iff_eq.mp hb)).elim
      simp [trNatRecStep, len, hbeq, hnil]
      cases L.length.bodd <;> rfl

private theorem trNat_computable : Computable trNat := by
  have h₂ : Computable₂ (fun _ : Unit => trNat) :=
    Computable.nat_strong_rec (α := Unit) (σ := List Γ')
      (fun _ n => trNat n) (g := trNatRecStep)
      trNatRecStep_computable trNatRecStep_spec
  exact h₂.comp (Computable.const ()) Computable.id

private theorem trList_singleton_computable :
    Computable (fun n : ℕ => trList [n]) := by
  have hcons : Computable
      (fun n : ℕ => trNat n ++ Γ'.cons :: ([] : List Γ')) :=
    Computable.list_append.comp trNat_computable
      (Computable.const [Γ'.cons])
  exact hcons.of_eq fun n => by simp [trList]

private theorem finInit_computable : Computable finInit := by
  have hS : Computable (fun n : ℕ => ((trList [n], [], [], []) : StackTuple)) :=
    Computable.pair trList_singleton_computable
      (Computable.pair (Computable.const [])
        (Computable.pair (Computable.const []) (Computable.const [])))
  exact finConf_constLabel_computable (c := c_f) (α := ℕ)
    (some finInitLabel) (Computable.const none) hS

private theorem finHalted_computable :
    Computable (finHalted (c := c_f)) := by
  unfold finHalted
  exact (computable_of_fintype (fun ol : Option (SuppLabel c_f) => ol.isNone)).comp
    Computable.fst

noncomputable def discreteMachine : DiscreteMachine (FinConf c_f) where
  step := finStep
  halted := finHalted
  halted_absorbing := finStep_halted
  init := finInit
  step_computable := finStep_computable
  halted_computable := finHalted_computable
  init_computable := finInit_computable

private theorem finHalted_toCfg (fc : FinConf c_f) :
    finHalted fc = true ↔ halted (toCfg fc) = true := by
  rcases fc with ⟨ol, v, S⟩
  cases ol <;> simp [finHalted, halted, toCfg]

private theorem toCfg_iterate_finStep (n w : ℕ) :
    toCfg ((finStep (c := c_f))^[n] (finInit w)) =
      step^[n] (init c_f [w]) := by
  induction n with
  | zero => simp [toCfg_finInit]
  | succ n ih =>
      rw [Function.iterate_succ', Function.iterate_succ']
      simp [ih, toCfg_finStep]

private theorem stepOpt_none_iff_halted (cfg : Cfg) :
    stepOpt cfg = none ↔ halted cfg = true := by
  cases cfg with
  | mk l var stk =>
      cases l <;> simp [halted, stepOpt, ← stepImpl_eq, stepImpl] <;> rfl

private theorem reaches_exists_total_iterate {a b : Cfg}
    (h : StateTransition.Reaches stepOpt a b) :
    ∃ n, step^[n] a = b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | @head a c hstep _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      rw [Function.iterate_succ]
      have hsome : stepOpt a = some c := Option.mem_def.mp hstep
      simp [step, hsome, hn]

private theorem total_halt_reaches_terminal (a : Cfg) :
    ∀ n, halted (step^[n] a) = true →
      ∃ b, StateTransition.Reaches stepOpt a b ∧ stepOpt b = none
  | 0, hhalt =>
      ⟨a, Relation.ReflTransGen.refl, (stepOpt_none_iff_halted a).2 hhalt⟩
  | n + 1, hhalt =>
      by
        by_cases ha : halted a = true
        · exact ⟨a, Relation.ReflTransGen.refl, (stepOpt_none_iff_halted a).2 ha⟩
        · have hsome : ∃ a', stepOpt a = some a' := by
            cases h : stepOpt a with
            | none =>
                have : halted a = true := (stepOpt_none_iff_halted a).1 h
                exact (ha this).elim
            | some a' => exact ⟨a', by simpa using h.symm⟩
          obtain ⟨a', ha'⟩ := hsome
          have hstep : step a = a' := by simp [step, ha']
          have htail : halted (step^[n] a') = true := by
            simpa [Function.iterate_succ', hstep] using hhalt
          obtain ⟨b, hb, hb0⟩ := total_halt_reaches_terminal a' n htail
          exact ⟨b, Relation.ReflTransGen.head (Option.mem_def.mpr ha') hb, hb0⟩

private theorem total_halts_iff_eval_dom (a : Cfg) :
    (∃ n, halted (step^[n] a) = true) ↔ (StateTransition.eval stepOpt a).Dom := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨b, hb, hb0⟩ := total_halt_reaches_terminal a n hn
    exact Part.dom_iff_mem.mpr ⟨b, StateTransition.mem_eval.2 ⟨hb, hb0⟩⟩
  · rw [Part.dom_iff_mem]
    rintro ⟨b, hbmem⟩
    obtain ⟨hb, hb0⟩ := StateTransition.mem_eval.1 hbmem
    obtain ⟨n, hn⟩ := reaches_exists_total_iterate hb
    exact ⟨n, by rw [hn]; exact (stepOpt_none_iff_halted b).1 hb0⟩

theorem haltsOn_iff_dom (n : ℕ) :
    discreteMachine.haltsOn n ↔ (diagonalEval n).Dom := by
  unfold DiscreteMachine.haltsOn discreteMachine
  constructor
  · rintro ⟨k, hk⟩
    have hfull : halted (step^[k] (init c_f [n])) = true := by
      rw [← toCfg_iterate_finStep k n]
      exact (finHalted_toCfg _).1 hk
    have hdomEval : (StateTransition.eval stepOpt (init c_f [n])).Dom :=
      (total_halts_iff_eval_dom (init c_f [n])).1 ⟨k, hfull⟩
    exact (c_f_dom n).1 ((U_halts_iff_dom c_f [n]).1 hdomEval)
  · intro hdom
    have hdomEval : (StateTransition.eval stepOpt (init c_f [n])).Dom :=
      (U_halts_iff_dom c_f [n]).2 ((c_f_dom n).2 hdom)
    obtain ⟨k, hk⟩ := (total_halts_iff_eval_dom (init c_f [n])).2 hdomEval
    refine ⟨k, ?_⟩
    apply (finHalted_toCfg _).2
    rwa [toCfg_iterate_finStep k n]

private theorem diagonalEval_noBoolDecider :
    Ripple.BoundedUniversality.Core.NoComputableBoolDecider (fun n => (diagonalEval n).Dom) := by
  intro ⟨f, hf, hiff⟩
  have h0 := Ripple.BoundedUniversality.Core.codeHaltsAt_noBoolDeciderOn 0
  apply h0
  let codeOf (c : Nat.Partrec.Code) : Nat.Partrec.Code :=
    Nat.Partrec.Code.comp c (Nat.Partrec.Code.const 0)
  have hcodeOf : Computable codeOf :=
    (Nat.Partrec.Code.primrec₂_comp.to_comp).comp Computable.id
      (Computable.const (Nat.Partrec.Code.const 0))
  refine ⟨fun c => f (Encodable.encode (codeOf c)), hf.comp (Computable.encode.comp hcodeOf),
    fun c => ?_⟩
  have h := hiff (Encodable.encode (codeOf c))
  change f (Encodable.encode (codeOf c)) = true ↔ (diagonalEval (Encodable.encode (codeOf c))).Dom at h
  simpa [diagonalEval, codeOf, Ripple.BoundedUniversality.Core.CodeHaltsAt, Nat.Partrec.Code.eval] using h

noncomputable def undecidableMachine : UndecidableMachine (FinConf c_f) where
  toDiscreteMachine := discreteMachine
  undecidable := by
    intro ⟨f, hf, hiff⟩
    apply diagonalEval_noBoolDecider
    exact ⟨f, hf, fun n => (hiff n).trans (haltsOn_iff_dom n)⟩


end UniversalMachine
end Ripple.BoundedUniversality.BGP
