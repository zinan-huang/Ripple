import Ripple.BoundedUniversality.BGP.UniversalMachine
import Ripple.BoundedUniversality.BGP.SelectorGates
import Ripple.BoundedUniversality.BGP.SelectorAtoms
import Ripple.BoundedUniversality.BGP.StackEncoding
import Ripple.BoundedUniversality.BGP.RobustStepContract
import Ripple.BoundedUniversality.BGP.ContractMain
import Ripple.BoundedUniversality.BGP.ContractSchedules

/-!
Ripple.BoundedUniversality.BGP.MachineInstance
--------------------------

Concrete instance-layer data for the finite-support universal machine
`UniversalMachine.discreteMachine`.

The GEN2 robust-step framework exposes an explicit machine stack count.  This
file instantiates the concrete six-coordinate/four-stack encoding, banks the
finite local-view data for the actual universal machine, and states the bridge
points needed by the dimension-generic framework instance.
-/

namespace Ripple.BoundedUniversality.BGP
namespace MachineInstance

open UniversalMachine
open Turing.PartrecToTM2

noncomputable section

local instance : Fintype (SuppLabel c_f) := by
  unfold SuppLabel
  infer_instance

/-- The fixed finite-support configuration type for the chosen diagonal code. -/
abbrev UConf : Type :=
  FinConf c_f

/-- The concrete universal-machine encoding has four stacks, control, and halt flag. -/
def d_U : ℕ := 6

/-- Base for the four-symbol stack alphabet, with sentinel digit `4` and missing digit `5`. -/
def B_U : ℕ := 6

theorem B_U_eq : B_U = 6 := rfl

theorem B_U_ge_four : 4 ≤ B_U := by
  decide

/-- Coordinate for the `main` stack. -/
def mainStackCoordU : Fin d_U := ⟨0, by decide⟩

/-- Coordinate for the `rev` stack. -/
def revStackCoordU : Fin d_U := ⟨1, by decide⟩

/-- Coordinate for the `aux` stack. -/
def auxStackCoordU : Fin d_U := ⟨2, by decide⟩

/-- Coordinate for the `stack` stack. -/
def dataStackCoordU : Fin d_U := ⟨3, by decide⟩

/-- Coordinate for the finite support control label. -/
def ctrlCoordU : Fin d_U := ⟨4, by decide⟩

/-- Coordinate for the absorbing halt flag. -/
def haltCoordU : Fin d_U := ⟨5, by decide⟩

/-- Coordinate map for Mathlib's four stack indices. -/
def stackCoordU : K' → Fin d_U
  | K'.main => mainStackCoordU
  | K'.rev => revStackCoordU
  | K'.aux => auxStackCoordU
  | K'.stack => dataStackCoordU

/-- Four-stack coordinate classifier for the concrete universal encoding. -/
def coordStackKindU (i : Fin d_U) : Option K' :=
  if i = mainStackCoordU then
    some K'.main
  else if i = revStackCoordU then
    some K'.rev
  else if i = auxStackCoordU then
    some K'.aux
  else if i = dataStackCoordU then
    some K'.stack
  else
    none

@[simp] theorem coordStackKindU_stack (k : K') :
    coordStackKindU (stackCoordU k) = some k := by
  cases k <;> simp [coordStackKindU, stackCoordU, mainStackCoordU, revStackCoordU,
    auxStackCoordU, dataStackCoordU]

@[simp] theorem coordStackKindU_ctrl :
    coordStackKindU ctrlCoordU = none := by
  simp [coordStackKindU, mainStackCoordU, revStackCoordU, auxStackCoordU,
    dataStackCoordU, ctrlCoordU]

@[simp] theorem coordStackKindU_halt :
    coordStackKindU haltCoordU = none := by
  simp [coordStackKindU, mainStackCoordU, revStackCoordU, auxStackCoordU,
    dataStackCoordU, haltCoordU]

/-- Digit embedding for the concrete four-symbol alphabet. -/
def gammaDigit : Γ' → ℕ
  | Γ'.consₗ => 0
  | Γ'.cons => 1
  | Γ'.bit0 => 2
  | Γ'.bit1 => 3

theorem gammaDigit_lt_sentinel (g : Γ') : gammaDigit g < bot B_U := by
  cases g <;> decide

theorem gammaDigit_injective : Function.Injective gammaDigit := by
  intro a b h
  cases a <;> cases b <;> simp [gammaDigit] at h ⊢

/--
Stack encoding over the universal-machine alphabet.  Lists are top-first;
`[]` is encoded by the sentinel digit `(B - 2) / B`.
-/
def stackCodeU (B : ℕ) (dig : Γ' → ℕ) : List Γ' → ℚ
  | [] => ((bot B : ℕ) : ℚ) / (B : ℚ)
  | a :: L => ((dig a : ℚ) + stackCodeU B dig L) / (B : ℚ)

@[simp] theorem stackCodeU_nil (B : ℕ) (dig : Γ' → ℕ) :
    stackCodeU B dig [] = ((bot B : ℕ) : ℚ) / (B : ℚ) := rfl

theorem stackCodeU_push (B : ℕ) (dig : Γ' → ℕ) (a : Γ')
    (L : List Γ') :
    stackCodeU B dig (a :: L) =
      ((dig a : ℚ) + stackCodeU B dig L) / (B : ℚ) := by
  rfl

theorem stackCodeU_pop (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ)
    (a : Γ') (L : List Γ') :
    (B : ℚ) * stackCodeU B dig (a :: L) - (dig a : ℚ) =
      stackCodeU B dig L := by
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 4) hB))
  rw [stackCodeU]
  field_simp [hB0]
  ring

private theorem base_pos_rat (B : ℕ) (hB : 4 ≤ B) : (0 : ℚ) < (B : ℚ) := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)

private theorem bot_pos_of_ge_four (B : ℕ) (hB : 4 ≤ B) : 0 < bot B := by
  unfold bot
  omega

private theorem bot_lt_base_of_ge_four (B : ℕ) (hB : 4 ≤ B) : bot B < B := by
  unfold bot
  omega

private theorem bot_div_base_lt_one (B : ℕ) (hB : 4 ≤ B) :
    ((bot B : ℕ) : ℚ) / (B : ℚ) < 1 := by
  have hBpos := base_pos_rat B hB
  rw [div_lt_one hBpos]
  exact_mod_cast bot_lt_base_of_ge_four B hB

theorem stackCodeU_pos (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ)
    (_hdig : ∀ a, dig a < bot B) :
    ∀ L : List Γ', 0 < stackCodeU B dig L := by
  intro L
  induction L with
  | nil =>
      exact div_pos (by exact_mod_cast bot_pos_of_ge_four B hB) (base_pos_rat B hB)
  | cons a L ih =>
      exact div_pos (add_pos_of_nonneg_of_pos (by positivity) ih) (base_pos_rat B hB)

theorem stackCodeU_le_bot_div_base (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ)
    (hdig : ∀ a, dig a < bot B) :
    ∀ L : List Γ', stackCodeU B dig L ≤ ((bot B : ℕ) : ℚ) / (B : ℚ) := by
  intro L
  induction L with
  | nil => rfl
  | cons a L ih =>
      have hBpos := base_pos_rat B hB
      have htail_lt_one : stackCodeU B dig L < 1 :=
        lt_of_le_of_lt ih (bot_div_base_lt_one B hB)
      have hdig_le : (dig a : ℚ) ≤ ((bot B : ℕ) : ℚ) - 1 := by
        have hle : dig a + 1 ≤ bot B := Nat.succ_le_of_lt (hdig a)
        have hleQ : ((dig a + 1 : ℕ) : ℚ) ≤ ((bot B : ℕ) : ℚ) := by
          exact_mod_cast hle
        norm_num at hleQ ⊢
        linarith
      rw [stackCodeU]
      rw [div_le_div_iff₀ hBpos hBpos]
      nlinarith

theorem stackCodeU_lt_missing_digit (B : ℕ) (hB : 4 ≤ B)
    (dig : Γ' → ℕ) (hdig : ∀ a, dig a < bot B) (L : List Γ') :
    stackCodeU B dig L < ((B - 1 : ℕ) : ℚ) / (B : ℚ) := by
  have hle := stackCodeU_le_bot_div_base B hB dig hdig L
  have hlt : ((bot B : ℕ) : ℚ) / (B : ℚ) <
      ((B - 1 : ℕ) : ℚ) / (B : ℚ) := by
    have hBpos := base_pos_rat B hB
    unfold bot
    have hn : B - 2 < B - 1 := by omega
    exact div_lt_div_of_pos_right
      (by exact_mod_cast hn : ((B - 2 : ℕ) : ℚ) < ((B - 1 : ℕ) : ℚ)) hBpos
  exact lt_of_le_of_lt hle hlt

theorem stackCodeU_mem_gap_range (L : List Γ') :
    0 < stackCodeU B_U gammaDigit L ∧
      stackCodeU B_U gammaDigit L ≤ ((bot B_U : ℕ) : ℚ) / (B_U : ℚ) ∧
      stackCodeU B_U gammaDigit L < ((B_U - 1 : ℕ) : ℚ) / (B_U : ℚ) := by
  exact ⟨stackCodeU_pos B_U B_U_ge_four gammaDigit gammaDigit_lt_sentinel L,
    stackCodeU_le_bot_div_base B_U B_U_ge_four gammaDigit gammaDigit_lt_sentinel L,
    stackCodeU_lt_missing_digit B_U B_U_ge_four gammaDigit gammaDigit_lt_sentinel L⟩

/-- First stack in the concrete tuple. -/
def mainStackU (c : UConf) : List Γ' :=
  c.2.2.1

/-- Reversal stack in the concrete tuple. -/
def revStackU (c : UConf) : List Γ' :=
  c.2.2.2.1

/-- Auxiliary stack in the concrete tuple. -/
def auxStackU (c : UConf) : List Γ' :=
  c.2.2.2.2.1

/-- Data stack in the concrete tuple. -/
def dataStackU (c : UConf) : List Γ' :=
  c.2.2.2.2.2

/-- Support-label control code with margin-two integer levels. -/
def ctrlCodeU : Option (SuppLabel c_f) → ℤ
  | none => 0
  | some l => (2 + 2 * ((Fintype.equivFin (SuppLabel c_f)) l).val : ℕ)

/-- Packed finite control/variable code with integer separation. -/
def ctrlVarCodeU (q : Option (SuppLabel c_f)) (v : Option Γ') : ℤ :=
  (2 * ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q, v)).val : ℕ)

theorem ctrlVarCodeU_injective :
    Function.Injective (fun p : Option (SuppLabel c_f) × Option Γ' =>
      ctrlVarCodeU p.1 p.2) := by
  intro p p' h
  rcases p with ⟨q, v⟩
  rcases p' with ⟨q', v'⟩
  unfold ctrlVarCodeU at h
  change
      (2 * ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q, v)).val : ℤ) =
        (2 * ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q', v')).val : ℤ) at h
  have hnat :
      2 * ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q, v)).val =
        2 * ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q', v')).val := by
    exact_mod_cast h
  have hval :
      ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q, v)).val =
        ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q', v')).val := by
    omega
  exact (Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')).injective
    (Fin.ext hval)

theorem ctrlVarCodeU_margin {p p' : Option (SuppLabel c_f) × Option Γ'}
    (h : ctrlVarCodeU p.1 p.2 ≠ ctrlVarCodeU p'.1 p'.2) :
    (1 : ℝ) ≤ |(ctrlVarCodeU p.1 p.2 : ℝ) -
      (ctrlVarCodeU p'.1 p'.2 : ℝ)| := by
  have hz : ctrlVarCodeU p.1 p.2 - ctrlVarCodeU p'.1 p'.2 ≠ 0 := sub_ne_zero.mpr h
  have hint : (1 : ℤ) ≤ |ctrlVarCodeU p.1 p.2 - ctrlVarCodeU p'.1 p'.2| :=
    Int.one_le_abs hz
  have hcast :
      (1 : ℝ) ≤ (|(ctrlVarCodeU p.1 p.2 - ctrlVarCodeU p'.1 p'.2)| : ℝ) := by
    exact_mod_cast hint
  simpa [Int.cast_sub] using hcast

/-- Halt flag as a rational coordinate. -/
def haltFlagU (c : UConf) : ℚ :=
  if finHalted c then 1 else 0

/-- Six-coordinate rational encoding for the concrete finite universal machine. -/
def confEncU (c : UConf) : Fin d_U → ℚ :=
  fun i =>
    if i = mainStackCoordU then
      stackCodeU B_U gammaDigit (mainStackU c)
    else if i = revStackCoordU then
      stackCodeU B_U gammaDigit (revStackU c)
    else if i = auxStackCoordU then
      stackCodeU B_U gammaDigit (auxStackU c)
    else if i = dataStackCoordU then
      stackCodeU B_U gammaDigit (dataStackU c)
    else if i = ctrlCoordU then
      (ctrlVarCodeU c.1 c.2.1 : ℚ)
    else
      haltFlagU c

/-- Raw tuple presentation of a finite universal-machine configuration. -/
abbrev RawCfgU : Type :=
  Option (SuppLabel c_f) × Option Γ' × StackTuple

/-- Encoding on raw tuple data, separated from later subtype-level branch wrappers. -/
def encRawU (c : RawCfgU) : Fin d_U → ℚ :=
  confEncU c

theorem confEncU_eq_encRaw (c : UConf) (i : Fin d_U) :
    confEncU c i = encRawU c i := by
  rfl

@[simp] theorem confEncU_main (c : UConf) :
    confEncU c mainStackCoordU = stackCodeU B_U gammaDigit (mainStackU c) := by
  simp [confEncU]

@[simp] theorem confEncU_rev (c : UConf) :
    confEncU c revStackCoordU = stackCodeU B_U gammaDigit (revStackU c) := by
  simp [confEncU, mainStackCoordU, revStackCoordU]

@[simp] theorem confEncU_aux (c : UConf) :
    confEncU c auxStackCoordU = stackCodeU B_U gammaDigit (auxStackU c) := by
  simp [confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU]

@[simp] theorem confEncU_data (c : UConf) :
    confEncU c dataStackCoordU = stackCodeU B_U gammaDigit (dataStackU c) := by
  simp [confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU]

@[simp] theorem confEncU_ctrl (c : UConf) :
    confEncU c ctrlCoordU = (ctrlVarCodeU c.1 c.2.1 : ℚ) := by
  simp [confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU]

@[simp] theorem confEncU_halt (c : UConf) :
    confEncU c haltCoordU = haltFlagU c := by
  simp [confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU, haltCoordU]

theorem encRawU_update_self
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple)
    (k : K') (L : List Γ') :
    encRawU (ol, v, stackSet S k L) (stackCoordU k) =
      stackCodeU B_U gammaDigit L := by
  cases k <;> rfl

theorem encRawU_update_other
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple)
    {k j : K'} (L : List Γ') (h : j ≠ k) :
    encRawU (ol, v, stackSet S k L) (stackCoordU j) =
      encRawU (ol, v, S) (stackCoordU j) := by
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

theorem encRawU_push_self
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple)
    (k : K') (g : Γ') :
    encRawU (ol, v, stackPush S k g) (stackCoordU k) =
      stackCodeU B_U gammaDigit (g :: stackGet S k) := by
  cases k <;> rfl

theorem encRawU_push_other
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple)
    {k j : K'} (g : Γ') (h : j ≠ k) :
    encRawU (ol, v, stackPush S k g) (stackCoordU j) =
      encRawU (ol, v, S) (stackCoordU j) := by
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

theorem encRawU_pop_self
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple) (k : K') :
    encRawU (ol, v, (stackPop S k).2) (stackCoordU k) =
      stackCodeU B_U gammaDigit (stackGet S k).tail := by
  cases k <;> rfl

theorem encRawU_pop_other
    (ol : Option (SuppLabel c_f)) (v : Option Γ') (S : StackTuple)
    {k j : K'} (h : j ≠ k) :
    encRawU (ol, v, (stackPop S k).2) (stackCoordU j) =
      encRawU (ol, v, S) (stackCoordU j) := by
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

theorem ctrlCodeU_margin {q q' : Option (SuppLabel c_f)}
    (h : ctrlCodeU q ≠ ctrlCodeU q') :
    (1 : ℝ) ≤ |(ctrlCodeU q : ℝ) - (ctrlCodeU q' : ℝ)| := by
  have hz : ctrlCodeU q - ctrlCodeU q' ≠ 0 := sub_ne_zero.mpr h
  have hint : (1 : ℤ) ≤ |ctrlCodeU q - ctrlCodeU q'| := Int.one_le_abs hz
  have hcast : (1 : ℝ) ≤ (|(ctrlCodeU q - ctrlCodeU q')| : ℝ) := by
    exact_mod_cast hint
  simpa [Int.cast_sub] using hcast

theorem haltFlagU_sticky (c : UConf) (h : haltFlagU c = 1) :
    haltFlagU (finStep c) = 1 := by
  unfold haltFlagU at h ⊢
  by_cases hc : finHalted c = true
  · have hnext : finHalted (finStep c) = true := by
      rw [finStep_halted c hc]
      exact hc
    simp [hnext]
  · simp [hc] at h

/-! ## Dimension-six contract encoding -/

/-- The fixed universal machine as a `DiscreteMachine` over `UConf`. -/
abbrev M_U : DiscreteMachine UConf :=
  discreteMachine

/-- Contract stack index for the four Mathlib universal-machine stacks. -/
def stackIndexU : K' → Fin 4
  | K'.main => ⟨0, by decide⟩
  | K'.rev => ⟨1, by decide⟩
  | K'.aux => ⟨2, by decide⟩
  | K'.stack => ⟨3, by decide⟩

/-- Inverse presentation of a contract stack index as a Mathlib stack kind. -/
def stackKindOfIndexU (s : Fin 4) : K' :=
  match s.val with
  | 0 => K'.main
  | 1 => K'.rev
  | 2 => K'.aux
  | _ => K'.stack

@[simp] theorem stackIndexU_kindOfIndex (s : Fin 4) :
    stackIndexU (stackKindOfIndexU s) = s := by
  fin_cases s <;> rfl

@[simp] theorem stackKindOfIndexU_stackIndex (k : K') :
    stackKindOfIndexU (stackIndexU k) = k := by
  cases k <;> rfl

/-- Contract coordinate map for all four universal-machine stacks. -/
def stackCoordFinU (s : Fin 4) : Fin d_U :=
  stackCoordU (stackKindOfIndexU s)

/-- GEN2 inverse classifier: coordinates `0..3` are stacks, `4,5` are reset coordinates. -/
def coordStackIndexU (i : Fin d_U) : Option (Fin 4) :=
  (coordStackKindU i).map stackIndexU

@[simp] theorem coordStackIndexU_stack (s : Fin 4) :
    coordStackIndexU (stackCoordFinU s) = some s := by
  simp [coordStackIndexU, stackCoordFinU]

@[simp] theorem coordStackIndexU_ctrl :
    coordStackIndexU ctrlCoordU = none := by
  simp [coordStackIndexU]

@[simp] theorem coordStackIndexU_halt :
    coordStackIndexU haltCoordU = none := by
  simp [coordStackIndexU]

@[simp] theorem coordStackIndexU_stackKind (k : K') :
    coordStackIndexU (stackCoordU k) = some (stackIndexU k) := by
  simp [coordStackIndexU]

@[simp] theorem coordStackIndexU_main :
    coordStackIndexU mainStackCoordU = some (stackIndexU K'.main) := by
  simpa [stackCoordU] using coordStackIndexU_stackKind K'.main

@[simp] theorem coordStackIndexU_rev :
    coordStackIndexU revStackCoordU = some (stackIndexU K'.rev) := by
  simpa [stackCoordU] using coordStackIndexU_stackKind K'.rev

@[simp] theorem coordStackIndexU_aux :
    coordStackIndexU auxStackCoordU = some (stackIndexU K'.aux) := by
  simpa [stackCoordU] using coordStackIndexU_stackKind K'.aux

@[simp] theorem coordStackIndexU_data :
    coordStackIndexU dataStackCoordU = some (stackIndexU K'.stack) := by
  simpa [stackCoordU] using coordStackIndexU_stackKind K'.stack

/-- The concrete stack carried by one of the four contract-level stack indices. -/
def indexedStackU (c : UConf) (s : Fin 4) : List Γ' :=
  match stackKindOfIndexU s with
  | K'.main => mainStackU c
  | K'.rev => revStackU c
  | K'.aux => auxStackU c
  | K'.stack => dataStackU c

def stackMoveForListsU (before after : List Γ') : StackMove :=
  by
    classical
    exact
      if ∃ a : Γ', after = a :: before then
        StackMove.push
      else if ∃ a : Γ', ∃ L : List Γ', before = a :: L ∧ after = L then
        StackMove.pop
      else
        StackMove.stay

theorem stackMoveForListsU_self (L : List Γ') :
    stackMoveForListsU L L = StackMove.stay := by
  classical
  have hpush : ¬ ∃ a : Γ', L = a :: L := by
    rintro ⟨a, h⟩
    have hlen := congrArg List.length h
    simp at hlen
  have hpop : ¬ ∃ a : Γ', ∃ M : List Γ', L = a :: M ∧ L = M := by
    rintro ⟨a, M, hL, hM⟩
    rw [hM] at hL
    have hlen := congrArg List.length hL
    simp at hlen
  simp [stackMoveForListsU, hpush, hpop]

theorem stackMoveForListsU_push (a : Γ') (L : List Γ') :
    stackMoveForListsU L (a :: L) = StackMove.push := by
  classical
  simp [stackMoveForListsU]

theorem stackMoveForListsU_pop (a : Γ') (L : List Γ') :
    stackMoveForListsU (a :: L) L = StackMove.pop := by
  classical
  have hpush : ¬ ∃ b : Γ', L = b :: a :: L := by
    rintro ⟨b, h⟩
    have hlen := congrArg List.length h
    simp at hlen
    omega
  simp [stackMoveForListsU, hpush]

theorem list_ne_cons_cons_self (a b : Γ') (L : List Γ') :
    L ≠ a :: b :: L := by
  intro h
  have hlen := congrArg List.length h
  simp at hlen
  omega

/--
Move type inferred extensionally from the before/after stack lists.  The
contract record only needs this exponent data; exact branch matching is supplied
separately by selector branch hypotheses below.
-/
def moveTypeStackU (c : UConf) (s : Fin 4) : StackMove :=
  stackMoveForListsU (indexedStackU c s) (indexedStackU (finStep c) s)

/-- Integer halt flag used as the state-code coordinate. -/
def haltCodeU (c : UConf) : ℤ :=
  if finHalted c then 1 else 0

private theorem stack_real_le_contract_gap (c : UConf) (k : K') :
    (confEncU c (stackCoordU k) : ℝ) ≤
      ((B_U : ℝ) - 2) / ((B_U : ℝ) - 1) := by
  have hleQ :
      confEncU c (stackCoordU k) ≤ ((bot B_U : ℕ) : ℚ) / (B_U : ℚ) := by
    cases k <;> simp [stackCoordU, stackCodeU_mem_gap_range]
  have hleR :
      (confEncU c (stackCoordU k) : ℝ) ≤
        ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast hleQ
  have hgap :
      ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ) : ℚ) : ℝ) ≤
        ((B_U : ℝ) - 2) / ((B_U : ℝ) - 1) := by
    norm_num [B_U, bot]
  exact hleR.trans hgap

private theorem int_code_margin {q q' : ℤ} (h : q ≠ q') :
    (1 : ℝ) ≤ |(q : ℝ) - (q' : ℝ)| := by
  have hz : q - q' ≠ 0 := sub_ne_zero.mpr h
  have hint : (1 : ℤ) ≤ |q - q'| := Int.one_le_abs hz
  have hcast : (1 : ℝ) ≤ (|(q - q')| : ℝ) := by
    exact_mod_cast hint
  simpa [Int.cast_sub] using hcast

/-- The six-coordinate/four-stack `StackMachineEncoding` consumed by the generic contract chain. -/
def stackMachineEncodingU : StackMachineEncoding d_U 4 M_U where
  enc := fun c i => (confEncU c i : ℝ)
  stackCoord := stackCoordFinU
  symbolCoord := ctrlCoordU
  stateCoord := haltCoordU
  coordStackIndex := coordStackIndexU
  coordStackIndex_stack := coordStackIndexU_stack
  k := B_U
  hk := B_U_ge_four
  moveType := moveTypeStackU
  stack_nonneg := by
    intro c s
    fin_cases s <;>
      exact le_of_lt (by
        simp [stackCoordFinU, stackKindOfIndexU, stackCoordU, stackCodeU_mem_gap_range])
  stack_le_missingDigit := by
    intro c s
    fin_cases s
    · simpa [stackCoordFinU, stackKindOfIndexU, stackCoordU] using
        stack_real_le_contract_gap c K'.main
    · simpa [stackCoordFinU, stackKindOfIndexU, stackCoordU] using
        stack_real_le_contract_gap c K'.rev
    · simpa [stackCoordFinU, stackKindOfIndexU, stackCoordU] using
        stack_real_le_contract_gap c K'.aux
    · simpa [stackCoordFinU, stackKindOfIndexU, stackCoordU] using
        stack_real_le_contract_gap c K'.stack
  symbolCode := fun c => ctrlVarCodeU c.1 c.2.1
  stateCode := haltCodeU
  symbol_enc := by
    intro c
    exact_mod_cast confEncU_ctrl c
  state_enc := by
    intro c
    rw [confEncU_halt]
    unfold haltCodeU haltFlagU
    by_cases h : finHalted c = true <;> simp [h]
  symbol_margin := by
    intro c c' h
    exact ctrlVarCodeU_margin (p := (c.1, c.2.1)) (p' := (c'.1, c'.2.1)) h
  state_margin := by
    intro c c' h
    exact int_code_margin h

theorem stackMachineEncodingU_enc_eq (c : UConf) (i : Fin d_U) :
    stackMachineEncodingU.enc c i = (confEncU c i : ℝ) := rfl

/-- Halt-flag package for the absorbing flag coordinate `5`. -/
def haltFlagPackageU : HaltFlagPackage stackMachineEncodingU haltCoordU where
  flagMargin := (1 : ℝ) / 4
  margin_pos := by norm_num
  margin_le_quarter := by rfl
  halted_flag := by
    intro c h
    rw [stackMachineEncodingU_enc_eq, confEncU_halt]
    have hfin : finHalted c = true := by
      simpa [M_U, discreteMachine] using h
    unfold haltFlagU
    simp [hfin]
  running_flag := by
    intro c h
    rw [stackMachineEncodingU_enc_eq, confEncU_halt]
    have hfin : finHalted c = false := by
      simpa [M_U, discreteMachine] using h
    unfold haltFlagU
    simp [hfin]
  flag_reset := by
    simp [stackMachineEncodingU]

/-- Sup-coordinate tube around the six-coordinate universal encoding. -/
def UTube (rho : ℝ) (c : UConf) (x : Fin d_U → ℝ) : Prop :=
  ∀ i, |x i - (confEncU c i : ℝ)| ≤ rho

/-- The checked tube/range fact for every concrete stack coordinate. -/
theorem confEncU_stack_gap_range (c : UConf) (k : K') :
    0 < confEncU c (stackCoordU k) ∧
      confEncU c (stackCoordU k) ≤ ((bot B_U : ℕ) : ℚ) / (B_U : ℚ) ∧
      confEncU c (stackCoordU k) < ((B_U - 1 : ℕ) : ℚ) / (B_U : ℚ) := by
  cases k <;> simp [stackCoordU, stackCodeU_mem_gap_range]

/-- A radius-zero tube pins every encoded coordinate exactly. -/
theorem confEncU_tube_zero_eq {c : UConf} {x : Fin d_U → ℝ}
    (hx : UTube 0 c x) :
    x = fun i => (confEncU c i : ℝ) := by
  funext i
  have hi := hx i
  have hzero : |x i - (confEncU c i : ℝ)| = 0 := le_antisymm hi (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Top symbol of a concrete universal-machine stack. -/
def stackTopU : List Γ' → Option Γ'
  | [] => none
  | a :: _ => some a

/-- Second symbol of a stack, needed by the `pred` branch after its pop. -/
def stackSecondU : List Γ' → Option Γ'
  | _ :: b :: _ => some b
  | _ => none

private theorem stackCodeU_tail_le_real6 (L : List Γ') :
    (((stackCodeU 6 gammaDigit L : ℚ) : ℝ)) ≤ (2 : ℝ) / 3 := by
  have hq := (stackCodeU_mem_gap_range L).2.1
  norm_num [B_U, bot] at hq
  have hr :
      (((stackCodeU 6 gammaDigit L : ℚ) : ℝ)) ≤ (((2 / 3 : ℚ) : ℝ)) := by
    exact_mod_cast hq
  norm_num at hr
  exact hr

private theorem stackCodeU_tail_pos_real6 (L : List Γ') :
    (0 : ℝ) < (((stackCodeU 6 gammaDigit L : ℚ) : ℝ)) := by
  have hq := (stackCodeU_mem_gap_range L).1
  norm_num [B_U] at hq
  exact_mod_cast hq

/-! ### Concrete control point-atom -/

/-- Slab point-atom on the control coordinate, codes `ctrlVarCodeU (label, var)`. -/
noncomputable def controlAtomSlab (eta : ℚ) (heta : 0 < eta) :
    SlabAtomicSelectorData d_U (Option (SuppLabel c_f) × Option Γ') :=
  finiteCoordinateAtoms ctrlCoordU
    (fun p => (ctrlVarCodeU p.1 p.2 : ℝ))
    (by
      intro a b hab
      apply ctrlVarCodeU_margin
      intro heq
      exact hab (ctrlVarCodeU_injective heq))
    (2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1)
    (by positivity)
    (by
      intro p
      have hlt :
          ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (p.1, p.2)).val <
            Fintype.card (Option (SuppLabel c_f) × Option Γ') :=
        (Fintype.equivFin (Option (SuppLabel c_f) × Option Γ') (p.1, p.2)).isLt
      have hnn : (0 : ℝ) ≤ (ctrlVarCodeU p.1 p.2 : ℝ) := by
        unfold ctrlVarCodeU; positivity
      rw [abs_of_nonneg hnn]
      unfold ctrlVarCodeU
      push_cast
      have hle : (((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (p.1, p.2)).val : ℝ) ≤
          (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
        exact_mod_cast hlt.le
      linarith [hle])
    (1 / 4) eta (by norm_num) (by norm_num) heta

/-- The ℤ-coded control atom, relabeled along `ctrlVarCodeU`. -/
noncomputable def controlAtom (eta : ℚ) (heta : 0 < eta) : CoordAtomData d_U ℤ :=
  ((controlAtomSlab eta heta).toCoordAtomData).relabel
    (fun p => ctrlVarCodeU p.1 p.2) ctrlVarCodeU_injective

/-! ### Stack-top digit-interval geometry -/

/-- Left endpoint of the interval occupied by stack code with top symbol `o`. -/
def topLoU : Option Γ' → ℝ
  | none => ((bot B_U : ℕ) : ℝ) / (B_U : ℝ)
  | some a => (gammaDigit a : ℝ) / (B_U : ℝ)

/-- Right endpoint of the interval occupied by stack code with top symbol `o`. -/
def topHiU : Option Γ' → ℝ
  | none => ((bot B_U : ℕ) : ℝ) / (B_U : ℝ)
  | some a => (gammaDigit a : ℝ) / (B_U : ℝ) + ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) ^ 2

/-- Separation gap between distinct stack-top intervals. -/
def topGapU : ℝ := 2 / (B_U : ℝ) ^ 2

/-- The stack code of `L` lies in the interval determined by its top symbol. -/
theorem stackCodeU_mem_topInterval (L : List Γ') :
    topLoU (stackTopU L) ≤ ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ∧
      ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ≤ topHiU (stackTopU L) := by
  have hBpos : (0 : ℝ) < (B_U : ℝ) := by norm_num [B_U]
  cases L with
  | nil =>
      simp only [stackTopU, topLoU, topHiU, stackCodeU_nil]
      push_cast
      constructor <;> norm_num
  | cons a T =>
      have hgap := stackCodeU_mem_gap_range T
      have hy0 : (0 : ℝ) < ((stackCodeU B_U gammaDigit T : ℚ) : ℝ) := by
        exact_mod_cast hgap.1
      have hyle : ((stackCodeU B_U gammaDigit T : ℚ) : ℝ) ≤
          ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) := by
        calc ((stackCodeU B_U gammaDigit T : ℚ) : ℝ)
            ≤ (((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℚ) : ℝ) := by exact_mod_cast hgap.2.1
          _ = ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) := by push_cast; ring
      have hval : ((stackCodeU B_U gammaDigit (a :: T) : ℚ) : ℝ) =
          ((gammaDigit a : ℝ) + ((stackCodeU B_U gammaDigit T : ℚ) : ℝ)) / (B_U : ℝ) := by
        rw [stackCodeU_push]
        push_cast
        ring
      have htop : stackTopU (a :: T) = some a := rfl
      rw [htop]
      simp only [topLoU, topHiU]
      rw [hval]
      constructor
      · gcongr
        linarith [hy0.le]
      · rw [add_div]
        have hkey : ((stackCodeU B_U gammaDigit T : ℚ) : ℝ) / (B_U : ℝ) ≤
            ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) ^ 2 := by
          calc ((stackCodeU B_U gammaDigit T : ℚ) : ℝ) / (B_U : ℝ)
              ≤ (((bot B_U : ℕ) : ℝ) / (B_U : ℝ)) / (B_U : ℝ) := by gcongr
            _ = ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) ^ 2 := by ring
        linarith [hkey]

/-- Distinct stack-top intervals are separated by at least `topGapU`. -/
theorem topInterval_sep (o o' : Option Γ') (h : o ≠ o') :
    topHiU o + topGapU ≤ topLoU o' ∨ topHiU o' + topGapU ≤ topLoU o := by
  have hb : ((bot B_U : ℕ) : ℝ) = 4 := by norm_num [bot, B_U]
  have hB6 : (B_U : ℝ) = 6 := by norm_num [B_U]
  rcases o with _ | a <;> rcases o' with _ | b
  · exact absurd rfl h
  · right
    cases b <;> simp only [topLoU, topHiU, topGapU, gammaDigit, hB6, hb] <;> norm_num
  · left
    cases a <;> simp only [topLoU, topHiU, topGapU, gammaDigit, hB6, hb] <;> norm_num
  · cases a <;> cases b <;>
      simp only [topLoU, topHiU, topGapU, gammaDigit, hB6, hb] <;>
      first
        | exact absurd rfl h
        | (left; norm_num; done)
        | (right; norm_num; done)

/--
Top-digit separation for the concrete universal stack code.  The legal top
intervals are separated by `1/18`, so the looser `1/50` threshold covers both
the direct extraction tube and the multiplied-tail tube used for `mainSecond`.
-/
theorem stackCodeU_top_eq_of_close {L M : List Γ'}
    (h :
      |((stackCodeU B_U gammaDigit L : ℚ) : ℝ) -
        ((stackCodeU B_U gammaDigit M : ℚ) : ℝ)| ≤ (1 : ℝ) / 50) :
    stackTopU L = stackTopU M := by
  cases L with
  | nil =>
      cases M with
      | nil => rfl
      | cons b T =>
          let y : ℝ := (((stackCodeU 6 gammaDigit T : ℚ) : ℝ))
          have hTle : y ≤ (2 : ℝ) / 3 := by
            simpa [y] using stackCodeU_tail_le_real6 T
          have h' := abs_le.mp h
          cases b <;>
            norm_num [stackCodeU, B_U, gammaDigit, bot, y] at h' ⊢ <;>
            nlinarith
  | cons a Ltail =>
      cases M with
      | nil =>
          let y : ℝ := (((stackCodeU 6 gammaDigit Ltail : ℚ) : ℝ))
          have hTle : y ≤ (2 : ℝ) / 3 := by
            simpa [y] using stackCodeU_tail_le_real6 Ltail
          have h' := abs_le.mp h
          cases a <;>
            norm_num [stackCodeU, B_U, gammaDigit, bot, y] at h' ⊢ <;>
            nlinarith
      | cons b Mtail =>
          cases a <;> cases b <;> try rfl
          all_goals
            let x : ℝ := (((stackCodeU 6 gammaDigit Ltail : ℚ) : ℝ))
            let y : ℝ := (((stackCodeU 6 gammaDigit Mtail : ℚ) : ℝ))
            have hxle : x ≤ (2 : ℝ) / 3 := by
              simpa [x] using stackCodeU_tail_le_real6 Ltail
            have hyle : y ≤ (2 : ℝ) / 3 := by
              simpa [y] using stackCodeU_tail_le_real6 Mtail
            have hxpos : 0 < x := by
              simpa [x] using stackCodeU_tail_pos_real6 Ltail
            have hypos : 0 < y := by
              simpa [y] using stackCodeU_tail_pos_real6 Mtail
            have h' := abs_le.mp h
            norm_num [stackCodeU, B_U, gammaDigit, bot, x, y] at h' ⊢ <;>
              nlinarith

private theorem stackCodeU_tail_close_after_mul (a : Γ') {L : List Γ'} {x : ℝ}
    (h :
      |x - ((stackCodeU B_U gammaDigit (a :: L) : ℚ) : ℝ)| ≤ ((1 : ℝ) / 1000)) :
    |(6 : ℝ) * x - (gammaDigit a : ℝ) -
        ((stackCodeU B_U gammaDigit L : ℚ) : ℝ)| ≤
      (6 : ℝ) * ((1 : ℝ) / 1000) := by
  calc
    |(6 : ℝ) * x - (gammaDigit a : ℝ) -
        ((stackCodeU B_U gammaDigit L : ℚ) : ℝ)|
        = (6 : ℝ) *
            |x - ((stackCodeU B_U gammaDigit (a :: L) : ℚ) : ℝ)| := by
          rw [← abs_of_pos (by norm_num : (0 : ℝ) < 6), ← abs_mul]
          congr 1
          cases a <;> norm_num [stackCodeU, B_U, gammaDigit] <;> ring
    _ ≤ (6 : ℝ) * ((1 : ℝ) / 1000) := by
      exact mul_le_mul_of_nonneg_left h (by norm_num)

private theorem abs_sub_le_common_left (a b y : ℝ) :
    |a - b| ≤ |y - a| + |y - b| := by
  have h0 := abs_add_le (y - a) (-(y - b))
  have heq : (y - a) + -(y - b) = b - a := by ring
  rw [heq] at h0
  rw [abs_sub_comm b a] at h0
  simpa [abs_neg, abs_sub_comm] using h0

theorem stackCodeU_top_eq_of_same_tube {L M : List Γ'} {x : ℝ}
    (hL : |x - ((stackCodeU B_U gammaDigit L : ℚ) : ℝ)| ≤ ((1 : ℝ) / 1000))
    (hM : |x - ((stackCodeU B_U gammaDigit M : ℚ) : ℝ)| ≤ ((1 : ℝ) / 1000)) :
    stackTopU L = stackTopU M := by
  apply stackCodeU_top_eq_of_close
  calc
    |((stackCodeU B_U gammaDigit L : ℚ) : ℝ) -
        ((stackCodeU B_U gammaDigit M : ℚ) : ℝ)|
        ≤ |x - ((stackCodeU B_U gammaDigit L : ℚ) : ℝ)| +
          |x - ((stackCodeU B_U gammaDigit M : ℚ) : ℝ)| :=
            abs_sub_le_common_left _ _ _
    _ ≤ ((1 : ℝ) / 1000) + ((1 : ℝ) / 1000) := add_le_add hL hM
    _ ≤ (1 : ℝ) / 50 := by
      norm_num

theorem stackCodeU_second_eq_of_same_tube {L M : List Γ'} {x : ℝ}
    (hL : |x - ((stackCodeU B_U gammaDigit L : ℚ) : ℝ)| ≤ ((1 : ℝ) / 1000))
    (hM : |x - ((stackCodeU B_U gammaDigit M : ℚ) : ℝ)| ≤ ((1 : ℝ) / 1000)) :
    stackSecondU L = stackSecondU M := by
  have htop := stackCodeU_top_eq_of_same_tube hL hM
  cases L with
  | nil =>
      cases M with
      | nil => rfl
      | cons b T => simp [stackTopU] at htop
  | cons a Lt =>
      cases M with
      | nil => simp [stackTopU] at htop
      | cons b Mt =>
          simp [stackTopU] at htop
          subst b
          have hLt := stackCodeU_tail_close_after_mul a hL
          have hMt := stackCodeU_tail_close_after_mul a hM
          have htaildist :
              |((stackCodeU B_U gammaDigit Lt : ℚ) : ℝ) -
                ((stackCodeU B_U gammaDigit Mt : ℚ) : ℝ)| ≤
                (1 : ℝ) / 50 := by
            calc
              |((stackCodeU B_U gammaDigit Lt : ℚ) : ℝ) -
                ((stackCodeU B_U gammaDigit Mt : ℚ) : ℝ)|
                  ≤ |(6 : ℝ) * x - (gammaDigit a : ℝ) -
                        ((stackCodeU B_U gammaDigit Lt : ℚ) : ℝ)| +
                    |(6 : ℝ) * x - (gammaDigit a : ℝ) -
                        ((stackCodeU B_U gammaDigit Mt : ℚ) : ℝ)| :=
                      abs_sub_le_common_left _ _ _
              _ ≤ (6 : ℝ) * ((1 : ℝ) / 1000) + (6 : ℝ) * ((1 : ℝ) / 1000) :=
                    add_le_add hLt hMt
              _ ≤ (1 : ℝ) / 50 := by
                    norm_num
          have htailtop := stackCodeU_top_eq_of_close htaildist
          cases Lt <;> cases Mt <;> simpa [stackSecondU, stackTopU] using htailtop

/--
Finite local view for the concrete universal machine.

It records the finite control label, current variable, the four stack tops, and
the second `main` symbol used by the `pred` case after popping the first symbol.
-/
structure UniversalLocalView where
  label : Option (SuppLabel c_f)
  var : Option Γ'
  mainTop : Option Γ'
  mainSecond : Option Γ'
  revTop : Option Γ'
  auxTop : Option Γ'
  dataTop : Option Γ'
  deriving DecidableEq

private abbrev UniversalLocalViewTuple :=
  Option (SuppLabel c_f) × Option Γ' × Option Γ' × Option Γ' ×
    Option Γ' × Option Γ' × Option Γ'

private def universalLocalViewEquiv :
    UniversalLocalView ≃ UniversalLocalViewTuple where
  toFun v :=
    (v.label, v.var, v.mainTop, v.mainSecond, v.revTop, v.auxTop, v.dataTop)
  invFun t :=
    { label := t.1
      var := t.2.1
      mainTop := t.2.2.1
      mainSecond := t.2.2.2.1
      revTop := t.2.2.2.2.1
      auxTop := t.2.2.2.2.2.1
      dataTop := t.2.2.2.2.2.2 }
  left_inv v := by
    cases v
    rfl
  right_inv t := by
    rcases t with ⟨a, b, c, d, e, f, g⟩
    rfl

instance : Fintype UniversalLocalView :=
  Fintype.ofEquiv UniversalLocalViewTuple universalLocalViewEquiv.symm

/-- Default view used outside the configured extraction tube. -/
def defaultLocalViewU : UniversalLocalView where
  label := none
  var := none
  mainTop := none
  mainSecond := none
  revTop := none
  auxTop := none
  dataTop := none

/-- Exact local view of a finite-support universal-machine configuration. -/
def localViewU (c : UConf) : UniversalLocalView where
  label := c.1
  var := c.2.1
  mainTop := stackTopU (mainStackU c)
  mainSecond := stackSecondU (mainStackU c)
  revTop := stackTopU (revStackU c)
  auxTop := stackTopU (auxStackU c)
  dataTop := stackTopU (dataStackU c)

/-- Positive local-extraction radius left for the analytic extractor layer. -/
def r_LE_U : ℝ := (1 : ℝ) / 1000

theorem r_LE_U_pos : 0 < r_LE_U := by
  norm_num [r_LE_U]

/--
Noncomputable local-view extractor from a positive tube.  If several
configurations fit the same tube point, the theorem below requires the
instance-level separation fact that they have the same finite local view.
-/
def localExtractU (_mu : ℝ) (x : Fin d_U → ℝ) : UniversalLocalView :=
  by
    classical
    exact
      if h : ∃ c : UConf, UTube r_LE_U c x then
        localViewU (Classical.choose h)
      else
        defaultLocalViewU

/--
Positive-radius tube extraction, parameterized by the missing separation lemma:
every configuration whose encoding lies in the same `r_LE_U` tube has the same
finite local view.  This is the exact hook needed by the selector sharpness
layer.
-/
theorem localExtractU_tube
    {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ}
    (hx : UTube r_LE_U c x)
    (huniq : ∀ c' : UConf, UTube r_LE_U c' x → localViewU c' = localViewU c) :
    localExtractU mu x = localViewU c := by
  unfold localExtractU
  classical
  have hex : ∃ c' : UConf, UTube r_LE_U c' x := ⟨c, hx⟩
  rw [dif_pos hex]
  exact huniq (Classical.choose hex) (Classical.choose_spec hex)

private theorem confEncU_dist_le_of_tubes {c c' : UConf} {x : Fin d_U → ℝ}
    (hx : UTube r_LE_U c x) (hy : UTube r_LE_U c' x) (i : Fin d_U) :
    |(confEncU c' i : ℝ) - (confEncU c i : ℝ)| ≤ (1 : ℝ) / 500 := by
  calc
    |(confEncU c' i : ℝ) - (confEncU c i : ℝ)|
        ≤ |x i - (confEncU c' i : ℝ)| + |x i - (confEncU c i : ℝ)| :=
          abs_sub_le_common_left _ _ _
    _ ≤ r_LE_U + r_LE_U := add_le_add (hy i) (hx i)
    _ = (1 : ℝ) / 500 := by
      norm_num [r_LE_U]

theorem hlocal_unique
    {c : UConf} {x : Fin d_U → ℝ}
    (htube : EncodingTube stackMachineEncodingU r_LE_U c x) :
    ∀ c' : UConf, UTube r_LE_U c' x → localViewU c' = localViewU c := by
  intro c' hc'
  have hc : UTube r_LE_U c x := by
    intro i
    simpa [EncodingTube, stackMachineEncodingU] using htube i
  have hctrlDist := confEncU_dist_le_of_tubes hc hc' ctrlCoordU
  have hpair : (c'.1, c'.2.1) = (c.1, c.2.1) := by
    by_contra hne
    have hcode_ne :
        ctrlVarCodeU c'.1 c'.2.1 ≠ ctrlVarCodeU c.1 c.2.1 := by
      intro hcode
      exact hne (ctrlVarCodeU_injective hcode)
    have hmargin :=
      ctrlVarCodeU_margin (p := (c'.1, c'.2.1)) (p' := (c.1, c.2.1)) hcode_ne
    rw [confEncU_ctrl, confEncU_ctrl] at hctrlDist
    norm_num at hctrlDist
    linarith
  have hlabel : c'.1 = c.1 :=
    congrArg (fun p : Option (SuppLabel c_f) × Option Γ' => p.1) hpair
  have hvar : c'.2.1 = c.2.1 :=
    congrArg (fun p : Option (SuppLabel c_f) × Option Γ' => p.2) hpair
  have hmain :
      stackTopU (mainStackU c') = stackTopU (mainStackU c) := by
    exact stackCodeU_top_eq_of_same_tube
      (by simpa [r_LE_U] using hc' mainStackCoordU)
      (by simpa [r_LE_U] using hc mainStackCoordU)
  have hmainSecond :
      stackSecondU (mainStackU c') = stackSecondU (mainStackU c) := by
    exact stackCodeU_second_eq_of_same_tube
      (by simpa [r_LE_U] using hc' mainStackCoordU)
      (by simpa [r_LE_U] using hc mainStackCoordU)
  have hrev :
      stackTopU (revStackU c') = stackTopU (revStackU c) := by
    exact stackCodeU_top_eq_of_same_tube
      (by simpa [r_LE_U] using hc' revStackCoordU)
      (by simpa [r_LE_U] using hc revStackCoordU)
  have haux :
      stackTopU (auxStackU c') = stackTopU (auxStackU c) := by
    exact stackCodeU_top_eq_of_same_tube
      (by simpa [r_LE_U] using hc' auxStackCoordU)
      (by simpa [r_LE_U] using hc auxStackCoordU)
  have hdata :
      stackTopU (dataStackU c') = stackTopU (dataStackU c) := by
    exact stackCodeU_top_eq_of_same_tube
      (by simpa [r_LE_U] using hc' dataStackCoordU)
      (by simpa [r_LE_U] using hc dataStackCoordU)
  cases c with
  | mk l rest =>
      cases c' with
      | mk l' rest' =>
          cases rest with
          | mk v S =>
              cases rest' with
              | mk v' S' =>
                  simp [localViewU, mainStackU, revStackU, auxStackU, dataStackU] at hlabel hvar hmain hmainSecond hrev haux hdata
                  simp [localViewU, mainStackU, revStackU, auxStackU, dataStackU]
                  exact ⟨hlabel, hvar, hmain, hmainSecond, hrev, haux, hdata⟩

/-- Abstract six-coordinate branch datum used at this instance boundary. -/
structure BranchDataU where
  evalBranch : (Fin d_U → ℚ) → Fin d_U → ℚ

/--
The concrete branch datum available without a dimension-generic selector layer:
it is indexed by a configuration and returns the exact next encoding.
-/
def exactBranchDataU (c : UConf) : BranchDataU where
  evalBranch := fun _ => confEncU (finStep c)

/-- Step consistency for the concrete universal-machine branch datum. -/
theorem exactBranchDataU_step_consistency (c : UConf) :
    (exactBranchDataU c).evalBranch (confEncU c) = confEncU (finStep c) := by
  rfl

theorem exactBranchDataU_step_consistency_real (c : UConf) :
    (fun i => ((exactBranchDataU c).evalBranch (confEncU c) i : ℝ)) =
      fun i => (confEncU (finStep c) i : ℝ) := by
  funext i
  simp [exactBranchDataU_step_consistency c]

/-! ## Affine branch synthesis for the universal machine -/

private def shortStackU (top second : Option Γ') : List Γ' :=
  match top with
  | none => []
  | some a =>
      match second with
      | none => [a]
      | some b => [a, b]

@[simp] private theorem shortStackU_head?_stack (L : List Γ') :
    (shortStackU (stackTopU L) (stackSecondU L)).head? = stackTopU L := by
  cases L with
  | nil => rfl
  | cons a L =>
      cases L <;> rfl

@[simp] private theorem shortStackU_head?_top (L : List Γ') :
    (shortStackU (stackTopU L) none).head? = stackTopU L := by
  cases L <;> rfl

private def localViewConfU (v : UniversalLocalView) : UConf :=
  (v.label, v.var,
    (shortStackU v.mainTop v.mainSecond,
      shortStackU v.revTop none,
      shortStackU v.auxTop none,
      shortStackU v.dataTop none))

private def stackActionU (before after : List Γ') : BranchAction :=
  match after with
  | a :: rest =>
      if rest = before then
        BranchAction.push B_U (gammaDigit a)
      else
        match before with
        | b :: L =>
            if after = L then
              BranchAction.pop B_U (gammaDigit b)
            else if after = before then
              BranchAction.stay
            else
              match after with
              | c :: M =>
                  if M = L then
                    BranchAction.replace
                      (((gammaDigit c : ℚ) - (gammaDigit b : ℚ)) / (B_U : ℚ))
                  else
                    BranchAction.const (stackCodeU B_U gammaDigit after)
              | [] => BranchAction.const (stackCodeU B_U gammaDigit after)
        | [] =>
            if after = before then
              BranchAction.stay
            else
              BranchAction.const (stackCodeU B_U gammaDigit after)
  | [] =>
      match before with
      | b :: L =>
          if after = L then
            BranchAction.pop B_U (gammaDigit b)
          else
            BranchAction.const (stackCodeU B_U gammaDigit after)
      | [] => BranchAction.stay

private theorem eval_stack_push_actionU (a : Γ') (L : List Γ') :
    BranchAction.evalQ B_U (BranchAction.push B_U (gammaDigit a))
        (stackCodeU B_U gammaDigit L) =
      stackCodeU B_U gammaDigit (a :: L) := by
  simp [BranchAction.evalQ, BranchAction.push, BranchAction.affine, stackCodeU]
  norm_num [B_U]
  ring

private theorem eval_stack_pop_actionU (a : Γ') (L : List Γ') :
    BranchAction.evalQ B_U (BranchAction.pop B_U (gammaDigit a))
        (stackCodeU B_U gammaDigit (a :: L)) =
      stackCodeU B_U gammaDigit L := by
  rw [BranchAction.evalQ, BranchAction.pop, BranchAction.affine]
  change (B_U : ℚ) * stackCodeU B_U gammaDigit (a :: L) + -(gammaDigit a : ℚ) =
    stackCodeU B_U gammaDigit L
  rw [← sub_eq_add_neg]
  exact stackCodeU_pop B_U B_U_ge_four gammaDigit a L

private theorem eval_stack_replace_actionU (a b : Γ') (L : List Γ') :
    BranchAction.evalQ B_U
        (BranchAction.replace (((gammaDigit b : ℚ) - (gammaDigit a : ℚ)) / (B_U : ℚ)))
        (stackCodeU B_U gammaDigit (a :: L)) =
      stackCodeU B_U gammaDigit (b :: L) := by
  simp [BranchAction.evalQ, BranchAction.replace, BranchAction.affine, stackCodeU]
  norm_num [B_U]
  ring

private theorem eval_stack_stay_actionU (L : List Γ') :
    BranchAction.evalQ B_U BranchAction.stay (stackCodeU B_U gammaDigit L) =
      stackCodeU B_U gammaDigit L := by
  simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine]

private theorem eval_stack_const_actionU (before after : List Γ') :
    BranchAction.evalQ B_U (BranchAction.const (stackCodeU B_U gammaDigit after))
        (stackCodeU B_U gammaDigit before) =
      stackCodeU B_U gammaDigit after := by
  simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine]

private theorem eval_stackActionU (before after : List Γ') :
    BranchAction.evalQ B_U (stackActionU before after)
        (stackCodeU B_U gammaDigit before) =
      stackCodeU B_U gammaDigit after := by
  unfold stackActionU
  cases after with
  | nil =>
      cases before with
      | nil =>
          exact eval_stack_stay_actionU []
      | cons b L =>
          by_cases hL : L = []
          · subst hL
            simp [eval_stack_pop_actionU]
          · simp [hL, BranchAction.evalQ, BranchAction.const, BranchAction.affine]
  | cons a rest =>
      by_cases hrest : rest = before
      · simp [hrest, eval_stack_push_actionU]
      · simp [hrest]
        cases before with
        | nil =>
            exact eval_stack_const_actionU [] (a :: rest)
        | cons b L =>
            by_cases hpop : a :: rest = L
            · simp [hpop, eval_stack_pop_actionU]
            · by_cases hstay : a :: rest = b :: L
              · simp [hpop, hstay, eval_stack_stay_actionU]
              · simp [hpop, hstay]
                by_cases htail : rest = L
                · subst htail
                  simp [eval_stack_replace_actionU]
                · simp [htail, eval_stack_const_actionU]

private theorem stackActionU_self (L : List Γ') :
    stackActionU L L = BranchAction.stay := by
  unfold stackActionU
  cases L with
  | nil => rfl
  | cons a L =>
      simp

private theorem eval_stackActionU_short_top_self_full (L : List Γ') :
    BranchAction.evalQ B_U
        (stackActionU (shortStackU (stackTopU L) none)
          (shortStackU (stackTopU L) none))
        (stackCodeU B_U gammaDigit L) =
      stackCodeU B_U gammaDigit L := by
  rw [stackActionU_self]
  simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine]

private theorem eval_stackActionU_short_stack_self_full (L : List Γ') :
    BranchAction.evalQ B_U
        (stackActionU (shortStackU (stackTopU L) (stackSecondU L))
          (shortStackU (stackTopU L) (stackSecondU L)))
        (stackCodeU B_U gammaDigit L) =
      stackCodeU B_U gammaDigit L := by
  rw [stackActionU_self]
  simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine]

private theorem stackActionU_push_cons (a : Γ') (L : List Γ') :
    stackActionU L (a :: L) = BranchAction.push B_U (gammaDigit a) := by
  unfold stackActionU
  simp

private theorem stackActionU_pop_cons (a : Γ') (L : List Γ') :
    stackActionU (a :: L) L = BranchAction.pop B_U (gammaDigit a) := by
  unfold stackActionU
  cases L with
  | nil => simp
  | cons b L =>
      have hne : L ≠ a :: b :: L := by
        intro h
        have hlen := congrArg List.length h
        simp at hlen
        omega
      simp [hne]

private theorem stackActionU_replace_cons (a b : Γ') (L : List Γ') :
    stackActionU (a :: L) (b :: L) =
      if b = a then BranchAction.stay
      else BranchAction.replace
        (((gammaDigit b : ℚ) - (gammaDigit a : ℚ)) / (B_U : ℚ)) := by
  unfold stackActionU
  by_cases hba : b = a
  · subst hba
    simp
  · simp [hba]

private def stackActionDeltaU (before after : List Γ') : ℤ :=
  match after with
  | _ :: rest =>
      if rest = before then
        -1
      else
        match before with
        | _ :: L => if after = L then 1 else 0
        | [] => 0
  | [] =>
      match before with
      | _ :: L => if after = L then 1 else 0
      | [] => 0

private def branchActionForCoordU (v : UniversalLocalView) (i : Fin d_U) :
    BranchAction :=
  let c := localViewConfU v
  let c' := finStep c
  if i = mainStackCoordU then
    stackActionU (mainStackU c) (mainStackU c')
  else if i = revStackCoordU then
    stackActionU (revStackU c) (revStackU c')
  else if i = auxStackCoordU then
    stackActionU (auxStackU c) (auxStackU c')
  else if i = dataStackCoordU then
    stackActionU (dataStackU c) (dataStackU c')
  else if i = ctrlCoordU then
    BranchAction.const (confEncU c' ctrlCoordU)
  else
    BranchAction.const (confEncU c' haltCoordU)

/-- View-indexed affine branch family for the universal-machine selector. -/
def branchU (v : UniversalLocalView) : BranchData d_U B_U where
  action := branchActionForCoordU v

private theorem branchActionForCoordU_main (v : UniversalLocalView) :
    branchActionForCoordU v mainStackCoordU =
      stackActionU (mainStackU (localViewConfU v))
        (mainStackU (finStep (localViewConfU v))) := by
  rfl

private theorem branchActionForCoordU_rev (v : UniversalLocalView) :
    branchActionForCoordU v revStackCoordU =
      stackActionU (revStackU (localViewConfU v))
        (revStackU (finStep (localViewConfU v))) := by
  simp only [branchActionForCoordU]
  norm_num [mainStackCoordU, revStackCoordU]

private theorem branchActionForCoordU_aux (v : UniversalLocalView) :
    branchActionForCoordU v auxStackCoordU =
      stackActionU (auxStackU (localViewConfU v))
        (auxStackU (finStep (localViewConfU v))) := by
  simp only [branchActionForCoordU]
  norm_num [mainStackCoordU, revStackCoordU, auxStackCoordU]

private theorem branchActionForCoordU_data (v : UniversalLocalView) :
    branchActionForCoordU v dataStackCoordU =
      stackActionU (dataStackU (localViewConfU v))
        (dataStackU (finStep (localViewConfU v))) := by
  simp only [branchActionForCoordU]
  norm_num [mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU]

private theorem branchActionForCoordU_ctrl (v : UniversalLocalView) :
    branchActionForCoordU v ctrlCoordU =
      BranchAction.const (confEncU (finStep (localViewConfU v)) ctrlCoordU) := by
  simp only [branchActionForCoordU]
  norm_num [mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU]

private theorem branchActionForCoordU_halt (v : UniversalLocalView) :
    branchActionForCoordU v haltCoordU =
      BranchAction.const (confEncU (finStep (localViewConfU v)) haltCoordU) := by
  simp only [branchActionForCoordU]
  norm_num [mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU, haltCoordU]

/-- The universal branch writes the halt coordinate by a constant action, so
the halt-coordinate affine scale is zero for every local view. -/
theorem branchU_halt_scale_eq_zero (v : UniversalLocalView) :
    (((branchU v).action haltCoordU).scale : ℝ) = 0 := by
  simp [branchU, branchActionForCoordU_halt, BranchAction.const, BranchAction.affine]

/-- The synthesized universal branch writes a Boolean halt target at the halt
coordinate, independently of the analog input vector. -/
theorem branchU_halt_target_eq_zero_or_one
    (v : UniversalLocalView) (u : Fin d_U → ℝ) :
    BranchData.evalBranch (branchU v) u haltCoordU = 0 ∨
      BranchData.evalBranch (branchU v) u haltCoordU = 1 := by
  by_cases hhalt : finHalted (finStep (localViewConfU v)) = true
  · right
    simp [BranchData.evalBranch, branchU, branchActionForCoordU_halt,
      BranchAction.evalReal, BranchAction.const, BranchAction.affine,
      confEncU_halt, haltFlagU, hhalt]
  · left
    simp [BranchData.evalBranch, branchU, branchActionForCoordU_halt,
      BranchAction.evalReal, BranchAction.const, BranchAction.affine,
      confEncU_halt, haltFlagU, hhalt]

#print axioms branchU_halt_target_eq_zero_or_one

/-- Halt-coordinate targets of all universal-machine branch actions lie in the
flag interval `[0,1]`. -/
theorem branchU_halt_target_mem_Icc
    (v : UniversalLocalView) (u : Fin d_U → ℝ) :
    BranchData.evalBranch (branchU v) u haltCoordU ∈ Set.Icc (0 : ℝ) 1 := by
  rcases branchU_halt_target_eq_zero_or_one v u with hzero | hone
  · rw [hzero]
    constructor <;> norm_num
  · rw [hone]
    constructor <;> norm_num

#print axioms branchU_halt_target_mem_Icc

/-- The default halted local view writes the halt target `1`, independently of
the analog input vector. -/
theorem branchU_defaultLocalView_halt_target_one (u : Fin d_U → ℝ) :
    BranchData.evalBranch (branchU defaultLocalViewU) u haltCoordU = 1 := by
  simp [BranchData.evalBranch, branchU, branchActionForCoordU_halt,
    BranchAction.evalReal, BranchAction.const, BranchAction.affine,
    confEncU_halt, haltFlagU, defaultLocalViewU, localViewConfU]

/-- Any halt-coordinate spread bound below `1` is false for the default halted
view: the selected branch value itself already has magnitude `1`. -/
theorem not_branchU_defaultLocalView_halt_BranchSpread_lt_one
    {u : Fin d_U → ℝ} {R : ℝ} (hR : R < 1) :
    ¬ BranchSpread branchU u defaultLocalViewU haltCoordU R := by
  intro hspread
  have hle : (1 : ℝ) ≤ R := by
    simpa [branchU_defaultLocalView_halt_target_one u] using hspread.1
  linarith

/-- In particular, the old global `BranchSpread ≤ exp(-μ)` shape cannot hold
at the halt coordinate once `μ > 0`. -/
theorem not_branchU_defaultLocalView_halt_BranchSpread_exp
    {u : Fin d_U → ℝ} {mu : ℝ} (hmu : 0 < mu) :
    ¬ BranchSpread branchU u defaultLocalViewU haltCoordU (Real.exp (-mu)) := by
  exact not_branchU_defaultLocalView_halt_BranchSpread_lt_one
    (by
      exact Real.exp_lt_one_iff.mpr (by linarith))

#print axioms branchU_defaultLocalView_halt_target_one
#print axioms not_branchU_defaultLocalView_halt_BranchSpread_lt_one
#print axioms not_branchU_defaultLocalView_halt_BranchSpread_exp

def finStepRawU (ol : Option (SuppLabel c_f))
    (rest : Option Γ' × StackTuple) : RawCfgU :=
  finStepBranch (c := c_f) ol rest

theorem finStepBranch_eq_rawU
    (ol : Option (SuppLabel c_f)) (rest : Option Γ' × StackTuple) :
    (finStepBranch (c := c_f) ol rest : RawCfgU) = finStepRawU ol rest := by
  rfl

theorem confEncU_finStepBranch_raw
    (ol : Option (SuppLabel c_f)) (rest : Option Γ' × StackTuple)
    (i : Fin d_U) :
    confEncU (finStepBranch (c := c_f) ol rest) i =
      encRawU (finStepRawU ol rest) i := by
  rfl

private theorem finStep_eq_finStepBranch_U (fc : UConf) :
    finStep fc = finStepBranch (c := c_f) fc.1 fc.2 :=
  (finStepBranch_eq_finStep fc).symm

private theorem branchU_move_main_source_exact
    (p : Γ' → Bool) (k₂ : K') (q : Λ')
    (hmem : Λ'.move p K'.main k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p K'.main k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p K'.main k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p K'.main k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases M with
  | nil =>
      cases k₂ <;>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
          stackPush, stackGet, stackSet, stackActionU, BranchAction.evalQ,
          BranchAction.stay, BranchAction.affine]
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases k₂ <;> by_cases hp : p a = true
          all_goals
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
              stackPush, stackGet, stackSet, stackActionU, hp,
              eval_stack_pop_actionU, eval_stack_stay_actionU]
      | cons b Mt =>
          cases k₂ <;> by_cases hp : p a = true
          all_goals
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
              stackPush, stackGet, stackSet, stackActionU, hp,
              eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem branchU_move_rev_source_exact
    (p : Γ' → Bool) (k₂ : K') (q : Λ')
    (hmem : Λ'.move p K'.rev k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p K'.rev k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p K'.rev k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p K'.rev k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases R with
  | nil =>
      cases k₂ <;>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
          stackPush, stackGet, stackSet, stackActionU, BranchAction.evalQ,
          BranchAction.stay, BranchAction.affine]
  | cons a Rt =>
      cases k₂ <;> by_cases hp : p a = true
      all_goals
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
          stackPush, stackGet, stackSet, stackActionU, hp,
          eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem branchU_move_aux_source_exact
    (p : Γ' → Bool) (k₂ : K') (q : Λ')
    (hmem : Λ'.move p K'.aux k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p K'.aux k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p K'.aux k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p K'.aux k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases A with
  | nil =>
      cases k₂ <;>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
          stackPush, stackGet, stackSet, stackActionU, BranchAction.evalQ,
          BranchAction.stay, BranchAction.affine]
  | cons a At =>
      cases k₂ <;> by_cases hp : p a = true
      all_goals
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
          stackPush, stackGet, stackSet, stackActionU, hp,
          eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem branchU_move_data_source_exact
    (p : Γ' → Bool) (k₂ : K') (q : Λ')
    (hmem : Λ'.move p K'.stack k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p K'.stack k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p K'.stack k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p K'.stack k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases D with
  | nil =>
      cases k₂ <;>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
          stackPush, stackGet, stackSet, stackActionU, BranchAction.evalQ,
          BranchAction.stay, BranchAction.affine]
  | cons a Dt =>
      cases k₂ <;> by_cases hp : p a = true
      all_goals
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
          stackPush, stackGet, stackSet, stackActionU, hp,
          eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem mainStack_finStep_move_rev_main_empty_repr
    (p : Γ' → Bool) (q : Λ')
    (hmem : Λ'.move p K'.rev K'.main q ∈ supportSet c_f)
    (v : Option Γ') (M A D : List Γ') :
    mainStackU
        (finStep
          (localViewConfU
            (localViewU
              (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩,
                v, (M, [], A, D))))) =
      shortStackU (stackTopU M) (stackSecondU M) := by
  simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
    localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
    stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]

private theorem mainStack_finStep_move_rev_main_cons_repr
    (p : Γ' → Bool) (q : Λ')
    (hmem : Λ'.move p K'.rev K'.main q ∈ supportSet c_f)
    (v : Option Γ') (a : Γ') (M R A D : List Γ') :
    mainStackU
        (finStep
          (localViewConfU
            (localViewU
              (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩,
                v, (M, a :: R, A, D))))) =
      if p a = true then
        shortStackU (stackTopU M) (stackSecondU M)
      else
        a :: shortStackU (stackTopU M) (stackSecondU M) := by
  by_cases hp : p a = true
  · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
      localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
      stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU, hp]
  · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
      localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
      stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
      dataStackU, hp]

private theorem branchU_eval_main_exact (c : UConf) :
    BranchData.evalBranchQ (branchU (localViewU c)) (confEncU c)
        mainStackCoordU =
      BranchAction.evalQ B_U
        (stackActionU
          (mainStackU (localViewConfU (localViewU c)))
          (mainStackU (finStep (localViewConfU (localViewU c)))))
        (confEncU c mainStackCoordU) := by
  rfl

private theorem branchU_eval_rev_exact (c : UConf) :
    BranchData.evalBranchQ (branchU (localViewU c)) (confEncU c)
        revStackCoordU =
      BranchAction.evalQ B_U
        (stackActionU
          (revStackU (localViewConfU (localViewU c)))
          (revStackU (finStep (localViewConfU (localViewU c)))))
        (confEncU c revStackCoordU) := by
  simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev]

private theorem branchU_move_main_dest_exact
    (p : Γ' → Bool) (q : Λ')
    (hmem : Λ'.move p K'.rev K'.main q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases R with
  | nil =>
      rw [branchU_eval_main_exact]
      rw [mainStack_finStep_move_rev_main_empty_repr]
      change
        BranchAction.evalQ B_U
          (stackActionU (shortStackU (stackTopU M) (stackSecondU M))
            (shortStackU (stackTopU M) (stackSecondU M)))
          (confEncU
            (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v, (M, [], A, D))
            mainStackCoordU) =
        confEncU
          (finStep
            (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v, (M, [], A, D)))
          mainStackCoordU
      rw [stackActionU_self]
      simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
        finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
        stackGet, mainStackU]
  | cons a Rt =>
      rw [branchU_eval_main_exact]
      rw [mainStack_finStep_move_rev_main_cons_repr]
      by_cases hp : p a = true
      · rw [if_pos hp]
        change
          BranchAction.evalQ B_U
            (stackActionU (shortStackU (stackTopU M) (stackSecondU M))
              (shortStackU (stackTopU M) (stackSecondU M)))
            (confEncU
              (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v,
                (M, a :: Rt, A, D))
              mainStackCoordU) =
          confEncU
            (finStep
              (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v,
                (M, a :: Rt, A, D)))
            mainStackCoordU
        rw [stackActionU_self]
        simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
          stackGet, mainStackU, hp]
      · rw [if_neg hp]
        change
          BranchAction.evalQ B_U
            (stackActionU (shortStackU (stackTopU M) (stackSecondU M))
              (a :: shortStackU (stackTopU M) (stackSecondU M)))
            (confEncU
              (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v,
                (M, a :: Rt, A, D))
              mainStackCoordU) =
          confEncU
            (finStep
              (some ⟨Λ'.move p K'.rev K'.main q, hmem⟩, v,
                (M, a :: Rt, A, D)))
            mainStackCoordU
        rw [stackActionU_push_cons]
        simp [BranchAction.evalQ, BranchAction.push, BranchAction.affine,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
          stackSet, stackGet, mainStackU, hp, stackCodeU]
        norm_num [B_U]
        ring

private theorem branchU_move_main_dest_all_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hdst : k₂ = K'.main) (hsrc : k₁ ≠ K'.main)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  subst hdst
  rw [branchU_eval_main_exact]
  cases k₁
  · exact False.elim (hsrc rfl)
  · cases R with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          stackSecondU, finStep_eq_finStepBranch_U, finStepBranch, stackPop,
          stackSet, stackGet, mainStackU, revStackU] using
          eval_stackActionU_short_stack_self_full M
    | cons a Rt =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, revStackU, hp] using
            eval_stackActionU_short_stack_self_full M
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackPush, stackSet, stackGet, mainStackU, revStackU,
            hp, stackActionU_push_cons] using
            eval_stack_push_actionU a M
  · cases A with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          stackSecondU, finStep_eq_finStepBranch_U, finStepBranch, stackPop,
          stackSet, stackGet, mainStackU, auxStackU] using
          eval_stackActionU_short_stack_self_full M
    | cons a At =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, auxStackU, hp] using
            eval_stackActionU_short_stack_self_full M
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackPush, stackSet, stackGet, mainStackU, auxStackU,
            hp, stackActionU_push_cons] using
            eval_stack_push_actionU a M
  · cases D with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          stackSecondU, finStep_eq_finStepBranch_U, finStepBranch, stackPop,
          stackSet, stackGet, mainStackU, dataStackU] using
          eval_stackActionU_short_stack_self_full M
    | cons a Dt =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, dataStackU, hp] using
            eval_stackActionU_short_stack_self_full M
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackPush, stackSet, stackGet, mainStackU, dataStackU,
            hp, stackActionU_push_cons] using
            eval_stack_push_actionU a M

private theorem branchU_move_ctrl_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  cases k₁
  · cases M with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackPush, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine]
        | cons b Mt =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackPush, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine]
  · cases R with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine]
    | cons a Rt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
            stackPush, stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine]
  · cases A with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine]
    | cons a At =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
            stackPush, stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine]
  · cases D with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine]
    | cons a Dt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
            stackPush, stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine]

private theorem branchU_move_halt_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  cases k₁
  · cases M with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine, haltFlagU, finHalted]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackPush, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                haltFlagU, finHalted]
        | cons b Mt =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackPush, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                haltFlagU, finHalted]
  · cases R with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine, haltFlagU, finHalted]
    | cons a Rt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
            stackPush, stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine, haltFlagU, finHalted]
  · cases A with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine, haltFlagU, finHalted]
    | cons a At =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
            stackPush, stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine, haltFlagU, finHalted]
  · cases D with
    | nil =>
        cases k₂ <;>
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
            stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
            BranchAction.affine, haltFlagU, finHalted]
    | cons a Dt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
            stackPush, stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine, haltFlagU, finHalted]

private theorem mainStack_finStep_move_untouched_repr
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hsrc : k₁ ≠ K'.main) (hdst : k₂ ≠ K'.main)
    (v : Option Γ') (M R A D : List Γ') :
    mainStackU
        (finStep
          (localViewConfU
            (localViewU
              (some ⟨Λ'.move p k₁ k₂ q, hmem⟩,
                v, (M, R, A, D))))) =
      shortStackU (stackTopU M) (stackSecondU M) := by
  cases k₁
  · exact False.elim (hsrc rfl)
  · cases R with
    | nil =>
        cases k₂
        · exact False.elim (hdst rfl)
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
    | cons a Rt =>
        cases k₂
        · exact False.elim (hdst rfl)
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
  · cases A with
    | nil =>
        cases k₂
        · exact False.elim (hdst rfl)
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
    | cons a At =>
        cases k₂
        · exact False.elim (hdst rfl)
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
  · cases D with
    | nil =>
        cases k₂
        · exact False.elim (hdst rfl)
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
        · simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
            stackSet, stackGet, mainStackU, revStackU, auxStackU, dataStackU]
    | cons a Dt =>
        cases k₂
        · exact False.elim (hdst rfl)
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]
        · by_cases hp : p a = true <;>
            simp [finStep_eq_finStepBranch_U, finStepBranch, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU, stackPop,
              stackPush, stackSet, stackGet, mainStackU, revStackU, auxStackU,
              dataStackU, hp]

private theorem branchU_move_main_untouched_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hsrc : k₁ ≠ K'.main) (hdst : k₂ ≠ K'.main)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  rw [branchU_eval_main_exact]
  rw [mainStack_finStep_move_untouched_repr
    (p := p) (k₁ := k₁) (k₂ := k₂) (q := q)
    (hmem := hmem) hsrc hdst]
  change
    BranchAction.evalQ B_U
      (stackActionU (shortStackU (stackTopU M) (stackSecondU M))
        (shortStackU (stackTopU M) (stackSecondU M)))
      (confEncU
        (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))
        mainStackCoordU) =
    confEncU
      (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
      mainStackCoordU
  rw [stackActionU_self]
  cases k₁
  · exact False.elim (hsrc rfl)
  · cases R with
    | nil =>
        cases k₂
        · exact False.elim (hdst rfl)
        all_goals
          simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, mainStackU]
    | cons a Rt =>
        cases k₂
        · exact False.elim (hdst rfl)
        all_goals
          by_cases hp : p a = true
          all_goals
            simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, mainStackU, hp]
  · cases A with
    | nil =>
        cases k₂
        · exact False.elim (hdst rfl)
        all_goals
          simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, mainStackU]
    | cons a At =>
        cases k₂
        · exact False.elim (hdst rfl)
        all_goals
          by_cases hp : p a = true
          all_goals
            simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, mainStackU, hp]
  · cases D with
    | nil =>
        cases k₂
        · exact False.elim (hdst rfl)
        all_goals
          simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, mainStackU]
    | cons a Dt =>
        cases k₂
        · exact False.elim (hdst rfl)
        all_goals
          by_cases hp : p a = true
          all_goals
            simp [BranchAction.evalQ, BranchAction.stay, BranchAction.affine,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, mainStackU, hp]

private theorem branchU_move_main_all_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  by_cases hsrc : k₁ = K'.main
  · subst hsrc
    exact branchU_move_main_source_exact p k₂ q hmem v M R A D
  · by_cases hdst : k₂ = K'.main
    · exact branchU_move_main_dest_all_exact p k₁ k₂ q hmem hdst hsrc v M R A D
    · exact branchU_move_main_untouched_exact p k₁ k₂ q hmem hsrc hdst v M R A D

private theorem branchU_move_rev_dest_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hdst : k₂ = K'.rev) (hsrc : k₁ ≠ K'.rev)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  subst hdst
  rw [branchU_eval_rev_exact]
  cases k₁
  · cases M with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          stackSecondU, finStep_eq_finStepBranch_U, finStepBranch, stackPop,
          stackSet, stackGet, mainStackU, revStackU] using
          eval_stackActionU_short_top_self_full R
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackSet, stackGet, mainStackU, revStackU, hp] using
                eval_stackActionU_short_top_self_full R
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackPush, stackSet, stackGet, mainStackU, revStackU,
                hp, stackActionU_push_cons] using
                eval_stack_push_actionU a R
        | cons b Mt =>
            by_cases hp : p a = true
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackSet, stackGet, mainStackU, revStackU, hp] using
                eval_stackActionU_short_top_self_full R
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackPush, stackSet, stackGet, mainStackU, revStackU,
                hp, stackActionU_push_cons] using
                eval_stack_push_actionU a R
  · exact False.elim (hsrc rfl)
  · cases A with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
          stackGet, revStackU, auxStackU] using
          eval_stackActionU_short_top_self_full R
    | cons a At =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, auxStackU, hp] using
            eval_stackActionU_short_top_self_full R
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
            stackSet, stackGet, revStackU, auxStackU, hp,
            stackActionU_push_cons] using
            eval_stack_push_actionU a R
  · cases D with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
          stackGet, revStackU, dataStackU] using
          eval_stackActionU_short_top_self_full R
    | cons a Dt =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, dataStackU, hp] using
            eval_stackActionU_short_top_self_full R
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
            stackSet, stackGet, revStackU, dataStackU, hp,
            stackActionU_push_cons] using
            eval_stack_push_actionU a R

private theorem branchU_move_rev_untouched_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hsrc : k₁ ≠ K'.rev) (hdst : k₂ ≠ K'.rev)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  rw [branchU_eval_rev_exact]
  cases k₁
  · cases M with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, revStackU] using
            eval_stackActionU_short_top_self_full R
        · exact False.elim (hdst rfl)
        all_goals
          simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, revStackU] using
            eval_stackActionU_short_top_self_full R
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  revStackU, hp] using
                  eval_stackActionU_short_top_self_full R
            · exact False.elim (hdst rfl)
            all_goals
              by_cases hp : p a = true
              all_goals
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  revStackU, hp] using
                  eval_stackActionU_short_top_self_full R
        | cons b Mt =>
            cases k₂
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  revStackU, hp] using
                  eval_stackActionU_short_top_self_full R
            · exact False.elim (hdst rfl)
            all_goals
              by_cases hp : p a = true
              all_goals
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  revStackU, hp] using
                  eval_stackActionU_short_top_self_full R
  · exact False.elim (hsrc rfl)
  · cases A with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, auxStackU] using
            eval_stackActionU_short_top_self_full R
        · exact False.elim (hdst rfl)
        all_goals
          simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, auxStackU] using
            eval_stackActionU_short_top_self_full R
    | cons a At =>
        cases k₂
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, auxStackU, hp] using
              eval_stackActionU_short_top_self_full R
        · exact False.elim (hdst rfl)
        all_goals
          by_cases hp : p a = true
          all_goals
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, auxStackU, hp] using
              eval_stackActionU_short_top_self_full R
  · cases D with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, dataStackU] using
            eval_stackActionU_short_top_self_full R
        · exact False.elim (hdst rfl)
        all_goals
          simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, dataStackU] using
            eval_stackActionU_short_top_self_full R
    | cons a Dt =>
        cases k₂
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full R
        · exact False.elim (hdst rfl)
        all_goals
          by_cases hp : p a = true
          all_goals
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full R

private theorem branchU_move_rev_all_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  by_cases hsrc : k₁ = K'.rev
  · subst hsrc
    exact branchU_move_rev_source_exact p k₂ q hmem v M R A D
  · by_cases hdst : k₂ = K'.rev
    · exact branchU_move_rev_dest_exact p k₁ k₂ q hmem hdst hsrc v M R A D
    · exact branchU_move_rev_untouched_exact p k₁ k₂ q hmem hsrc hdst v M R A D

private theorem branchU_eval_aux_exact (c : UConf) :
    BranchData.evalBranchQ (branchU (localViewU c)) (confEncU c)
        auxStackCoordU =
      BranchAction.evalQ B_U
        (stackActionU
          (auxStackU (localViewConfU (localViewU c)))
          (auxStackU (finStep (localViewConfU (localViewU c)))))
        (confEncU c auxStackCoordU) := by
  simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux]

private theorem branchU_move_aux_dest_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hdst : k₂ = K'.aux) (hsrc : k₁ ≠ K'.aux)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  subst hdst
  rw [branchU_eval_aux_exact]
  cases k₁
  · cases M with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          stackSecondU, finStep_eq_finStepBranch_U, finStepBranch, stackPop,
          stackSet, stackGet, mainStackU, auxStackU] using
          eval_stackActionU_short_top_self_full A
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackSet, stackGet, mainStackU, auxStackU, hp] using
                eval_stackActionU_short_top_self_full A
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackPush, stackSet, stackGet, mainStackU, auxStackU,
                hp, stackActionU_push_cons] using
                eval_stack_push_actionU a A
        | cons b Mt =>
            by_cases hp : p a = true
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackSet, stackGet, mainStackU, auxStackU, hp] using
                eval_stackActionU_short_top_self_full A
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackPush, stackSet, stackGet, mainStackU, auxStackU,
                hp, stackActionU_push_cons] using
                eval_stack_push_actionU a A
  · cases R with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
          stackGet, revStackU, auxStackU] using
          eval_stackActionU_short_top_self_full A
    | cons a Rt =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, auxStackU, hp] using
            eval_stackActionU_short_top_self_full A
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
            stackSet, stackGet, revStackU, auxStackU, hp,
            stackActionU_push_cons] using
            eval_stack_push_actionU a A
  · exact False.elim (hsrc rfl)
  · cases D with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
          stackGet, auxStackU, dataStackU] using
          eval_stackActionU_short_top_self_full A
    | cons a Dt =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU, hp] using
            eval_stackActionU_short_top_self_full A
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
            stackSet, stackGet, auxStackU, dataStackU, hp,
            stackActionU_push_cons] using
            eval_stack_push_actionU a A

private theorem branchU_move_aux_untouched_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hsrc : k₁ ≠ K'.aux) (hdst : k₂ ≠ K'.aux)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  rw [branchU_eval_aux_exact]
  cases k₁
  · cases M with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, auxStackU] using
            eval_stackActionU_short_top_self_full A
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, auxStackU] using
            eval_stackActionU_short_top_self_full A
        · exact False.elim (hdst rfl)
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, auxStackU] using
            eval_stackActionU_short_top_self_full A
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  auxStackU, hp] using
                  eval_stackActionU_short_top_self_full A
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  auxStackU, hp] using
                  eval_stackActionU_short_top_self_full A
            · exact False.elim (hdst rfl)
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  auxStackU, hp] using
                  eval_stackActionU_short_top_self_full A
        | cons b Mt =>
            cases k₂
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  auxStackU, hp] using
                  eval_stackActionU_short_top_self_full A
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  auxStackU, hp] using
                  eval_stackActionU_short_top_self_full A
            · exact False.elim (hdst rfl)
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  auxStackU, hp] using
                  eval_stackActionU_short_top_self_full A
  · cases R with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, auxStackU] using
            eval_stackActionU_short_top_self_full A
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, auxStackU] using
            eval_stackActionU_short_top_self_full A
        · exact False.elim (hdst rfl)
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, auxStackU] using
            eval_stackActionU_short_top_self_full A
    | cons a Rt =>
        cases k₂
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, auxStackU, hp] using
              eval_stackActionU_short_top_self_full A
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, auxStackU, hp] using
              eval_stackActionU_short_top_self_full A
        · exact False.elim (hdst rfl)
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, auxStackU, hp] using
              eval_stackActionU_short_top_self_full A
  · exact False.elim (hsrc rfl)
  · cases D with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU] using
            eval_stackActionU_short_top_self_full A
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU] using
            eval_stackActionU_short_top_self_full A
        · exact False.elim (hdst rfl)
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU] using
            eval_stackActionU_short_top_self_full A
    | cons a Dt =>
        cases k₂
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, auxStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full A
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, auxStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full A
        · exact False.elim (hdst rfl)
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, auxStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full A

private theorem branchU_move_aux_all_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  by_cases hsrc : k₁ = K'.aux
  · subst hsrc
    exact branchU_move_aux_source_exact p k₂ q hmem v M R A D
  · by_cases hdst : k₂ = K'.aux
    · exact branchU_move_aux_dest_exact p k₁ k₂ q hmem hdst hsrc v M R A D
    · exact branchU_move_aux_untouched_exact p k₁ k₂ q hmem hsrc hdst v M R A D

private theorem branchU_eval_data_exact (c : UConf) :
    BranchData.evalBranchQ (branchU (localViewU c)) (confEncU c)
        dataStackCoordU =
      BranchAction.evalQ B_U
        (stackActionU
          (dataStackU (localViewConfU (localViewU c)))
          (dataStackU (finStep (localViewConfU (localViewU c)))))
        (confEncU c dataStackCoordU) := by
  simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data]

private theorem branchU_move_data_dest_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hdst : k₂ = K'.stack) (hsrc : k₁ ≠ K'.stack)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  subst hdst
  rw [branchU_eval_data_exact]
  cases k₁
  · cases M with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          stackSecondU, finStep_eq_finStepBranch_U, finStepBranch, stackPop,
          stackSet, stackGet, mainStackU, dataStackU] using
          eval_stackActionU_short_top_self_full D
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackSet, stackGet, mainStackU, dataStackU, hp] using
                eval_stackActionU_short_top_self_full D
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackPush, stackSet, stackGet, mainStackU,
                dataStackU, hp, stackActionU_push_cons] using
                eval_stack_push_actionU a D
        | cons b Mt =>
            by_cases hp : p a = true
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackSet, stackGet, mainStackU, dataStackU, hp] using
                eval_stackActionU_short_top_self_full D
            · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                stackPop, stackPush, stackSet, stackGet, mainStackU,
                dataStackU, hp, stackActionU_push_cons] using
                eval_stack_push_actionU a D
  · cases R with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
          stackGet, revStackU, dataStackU] using
          eval_stackActionU_short_top_self_full D
    | cons a Rt =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, dataStackU, hp] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
            stackSet, stackGet, revStackU, dataStackU, hp,
            stackActionU_push_cons] using
            eval_stack_push_actionU a D
  · cases A with
    | nil =>
        simpa [localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
          stackGet, auxStackU, dataStackU] using
          eval_stackActionU_short_top_self_full D
    | cons a At =>
        by_cases hp : p a = true
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU, hp] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
            stackSet, stackGet, auxStackU, dataStackU, hp,
            stackActionU_push_cons] using
            eval_stack_push_actionU a D
  · exact False.elim (hsrc rfl)

private theorem branchU_move_data_untouched_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (hsrc : k₁ ≠ K'.stack) (hdst : k₂ ≠ K'.stack)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  rw [branchU_eval_data_exact]
  cases k₁
  · cases M with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
            stackPop, stackSet, stackGet, mainStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · exact False.elim (hdst rfl)
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  dataStackU, hp] using
                  eval_stackActionU_short_top_self_full D
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  dataStackU, hp] using
                  eval_stackActionU_short_top_self_full D
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  dataStackU, hp] using
                  eval_stackActionU_short_top_self_full D
            · exact False.elim (hdst rfl)
        | cons b Mt =>
            cases k₂
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  dataStackU, hp] using
                  eval_stackActionU_short_top_self_full D
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  dataStackU, hp] using
                  eval_stackActionU_short_top_self_full D
            · by_cases hp : p a = true <;>
                simpa [localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  stackPop, stackPush, stackSet, stackGet, mainStackU,
                  dataStackU, hp] using
                  eval_stackActionU_short_top_self_full D
            · exact False.elim (hdst rfl)
  · cases R with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, revStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · exact False.elim (hdst rfl)
    | cons a Rt =>
        cases k₂
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full D
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full D
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, revStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full D
        · exact False.elim (hdst rfl)
  · cases A with
    | nil =>
        cases k₂
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · simpa [localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackSet,
            stackGet, auxStackU, dataStackU] using
            eval_stackActionU_short_top_self_full D
        · exact False.elim (hdst rfl)
    | cons a At =>
        cases k₂
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, auxStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full D
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, auxStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full D
        · by_cases hp : p a = true <;>
            simpa [localViewU, localViewConfU, shortStackU, stackTopU,
              finStep_eq_finStepBranch_U, finStepBranch, stackPop, stackPush,
              stackSet, stackGet, auxStackU, dataStackU, hp] using
              eval_stackActionU_short_top_self_full D
        · exact False.elim (hdst rfl)
  · exact False.elim (hsrc rfl)

private theorem branchU_move_data_all_exact
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  by_cases hsrc : k₁ = K'.stack
  · subst hsrc
    exact branchU_move_data_source_exact p k₂ q hmem v M R A D
  · by_cases hdst : k₂ = K'.stack
    · exact branchU_move_data_dest_exact p k₁ k₂ q hmem hdst hsrc v M R A D
    · exact branchU_move_data_untouched_exact p k₁ k₂ q hmem hsrc hdst v M R A D

private theorem stackActionU_multiplier_le_moveType
    (before after : List Γ') :
    BranchAction.multiplier B_U (stackActionU before after) ≤
      (B_U : ℝ) ^ (stackMoveForListsU before after).delta := by
  classical
  by_cases hpush : ∃ a : Γ', after = a :: before
  · rcases hpush with ⟨a, rfl⟩
    have hmove : stackMoveForListsU before (a :: before) = StackMove.push := by
      unfold stackMoveForListsU
      rw [if_pos ⟨a, rfl⟩]
    rw [hmove, stackActionU_push_cons]
    norm_num [BranchAction.multiplier, BranchAction.push, BranchAction.affine,
      StackMove.delta, B_U]
  · by_cases hpop : ∃ a : Γ', ∃ L : List Γ', before = a :: L ∧ after = L
    · rcases hpop with ⟨a, L, hbefore, hafter⟩
      subst before
      subst after
      have hmove : stackMoveForListsU (a :: L) L = StackMove.pop := by
        have hpopWitness :
            ∃ x : Γ', ∃ M : List Γ', a :: L = x :: M ∧ L = M :=
          ⟨a, L, rfl, rfl⟩
        unfold stackMoveForListsU
        rw [if_neg hpush, if_pos hpopWitness]
      rw [hmove, stackActionU_pop_cons]
      norm_num [BranchAction.multiplier, BranchAction.pop, BranchAction.affine,
        StackMove.delta, B_U]
    · have hmove : stackMoveForListsU before after = StackMove.stay := by
        unfold stackMoveForListsU
        rw [if_neg hpush, if_neg hpop]
      rw [hmove]
      unfold stackActionU
      cases after with
      | nil =>
          cases before with
          | nil =>
              norm_num [BranchAction.multiplier, BranchAction.stay,
                BranchAction.affine, StackMove.delta, B_U]
          | cons b L =>
              have hL : L ≠ [] := by
                intro hnil
                apply hpop
                exact ⟨b, [], by simp [hnil]⟩
              simp [hL, BranchAction.multiplier, BranchAction.const,
                BranchAction.affine, StackMove.delta, B_U]
      | cons a rest =>
          have hrest : rest ≠ before := by
            intro hr
            apply hpush
            exact ⟨a, by simp [hr]⟩
          cases before with
          | nil =>
              simp [hrest, BranchAction.multiplier, BranchAction.const,
                BranchAction.affine, StackMove.delta, B_U]
          | cons b L =>
              have hpop' : a :: rest ≠ L := by
                intro hp
                apply hpop
                exact ⟨b, L, by simp [hp]⟩
              by_cases hstay : a :: rest = b :: L
              · simp [hrest, hpop', hstay, BranchAction.multiplier,
                  BranchAction.stay, BranchAction.affine, StackMove.delta, B_U]
              · by_cases htail : rest = L
                · by_cases hab : a = b
                  · simp [hab, htail, BranchAction.multiplier, BranchAction.stay,
                      BranchAction.affine, StackMove.delta, B_U]
                  · simp [hab, htail, BranchAction.multiplier, BranchAction.replace,
                      BranchAction.affine, StackMove.delta, B_U]
                · simp [hrest, hpop', hstay, htail, BranchAction.multiplier,
                    BranchAction.const, BranchAction.affine, StackMove.delta, B_U]

private theorem branchU_reset_multiplier_le (c : UConf) :
    (∀ i, i = ctrlCoordU ∨ i = haltCoordU →
      BranchAction.multiplier B_U ((branchU (localViewU c)).action i) ≤
        stackMachineEncodingU.coordMultiplier c i) := by
  intro i hi
  rcases hi with rfl | rfl
  · simp [branchU, branchActionForCoordU_ctrl, BranchAction.multiplier,
      BranchAction.const, BranchAction.affine, stackMachineEncodingU,
      StackMachineEncoding.coordMultiplier, coordStackIndexU]
  · simp [branchU, branchActionForCoordU_halt, BranchAction.multiplier,
      BranchAction.const, BranchAction.affine, stackMachineEncodingU,
      StackMachineEncoding.coordMultiplier, coordStackIndexU]

private theorem branchU_clause_move_exact_next
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
          i =
        stackMachineEncodingU.enc
          (M_U.step
            (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))
          i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_move_main_all_exact p k₁ k₂ q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_move_rev_all_exact p k₁ k₂ q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_move_aux_all_exact p k₁ k₂ q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_move_data_all_exact p k₁ k₂ q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_move_ctrl_exact p k₁ k₂ q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_move_halt_exact p k₁ k₂ q hmem v M R A D)

private theorem branchU_move_main_multiplier_le
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))
        mainStackCoordU := by
  cases k₁
  · cases k₂ <;>
      cases M with
      | nil =>
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            stackPop, stackPush, stackSet, stackGet, stackActionU, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
      | cons a Mt =>
          cases Mt with
          | nil =>
              by_cases hp : p a = true
              all_goals
                simp [branchU, branchActionForCoordU_main, localViewU,
                  localViewConfU, shortStackU, stackTopU, stackSecondU,
                  finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                  StackMachineEncoding.coordMultiplier,
                  StackMachineEncoding.stackMultiplier,
                  StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
                  stackMoveForListsU, mainStackU, stackPop, stackPush, stackSet,
                  stackGet, stackActionU, stackActionU_self, BranchAction.multiplier,
                  BranchAction.stay, BranchAction.const, BranchAction.pop,
                  BranchAction.push, BranchAction.affine, StackMove.delta, B_U, hp]
          | cons b Mt =>
              have hcycle : Mt ≠ a :: b :: Mt := by
                intro h
                have hlen := congrArg List.length h
                simp at hlen
                omega
              by_cases hp : p a = true
              all_goals
                simp [hcycle, branchU, branchActionForCoordU_main, localViewU,
                  localViewConfU, shortStackU, stackTopU, stackSecondU,
                  finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                  StackMachineEncoding.coordMultiplier,
                  StackMachineEncoding.stackMultiplier,
                  StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
                  stackMoveForListsU, mainStackU, stackPop, stackPush, stackSet,
                  stackGet, stackActionU, stackActionU_self, BranchAction.multiplier,
                  BranchAction.stay, BranchAction.const, BranchAction.pop,
                  BranchAction.push, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases R with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            revStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Rt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            revStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]
  · cases A with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            auxStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a At =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            auxStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]
  · cases D with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Dt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]

private theorem branchU_move_rev_multiplier_le
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))
        revStackCoordU := by
  cases k₁
  · cases M with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            revStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_rev, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                revStackU, stackPop, stackPush, stackSet, stackGet,
                stackActionU_self, stackActionU_push_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, hp]
        | cons b Mt =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_rev, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                revStackU, stackPop, stackPush, stackSet, stackGet,
                stackActionU_self, stackActionU_push_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, hp]
  · cases k₂ <;>
      cases R with
      | nil =>
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            stackPop, stackPush, stackSet, stackGet, stackActionU, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
      | cons a Rt =>
          have hnoPushCycle : ¬ ∃ x : Γ', Rt = x :: a :: Rt := by
            rintro ⟨x, hx⟩
            have hlen := congrArg List.length hx
            simp at hlen
            omega
          by_cases hp : p a = true
          all_goals
            simp [hnoPushCycle, branchU, branchActionForCoordU_rev, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
              StackMachineEncoding.coordMultiplier,
              StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
              moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
              stackPop, stackPush, stackSet, stackGet, stackActionU, stackActionU_self,
              BranchAction.multiplier, BranchAction.stay, BranchAction.const,
              BranchAction.pop, BranchAction.push, BranchAction.affine,
              StackMove.delta, B_U, hp]
  · cases A with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            auxStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a At =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            auxStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]
  · cases D with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Dt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]

private theorem branchU_move_aux_multiplier_le
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))
        auxStackCoordU := by
  cases k₁
  · cases M with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            auxStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_aux, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                auxStackU, stackPop, stackPush, stackSet, stackGet,
                stackActionU_self, stackActionU_push_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, hp]
        | cons b Mt =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_aux, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                auxStackU, stackPop, stackPush, stackSet, stackGet,
                stackActionU_self, stackActionU_push_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, hp]
  · cases R with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            auxStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Rt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            auxStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]
  · cases k₂ <;>
      cases A with
      | nil =>
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            stackPop, stackPush, stackSet, stackGet, stackActionU, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
      | cons a At =>
          have hnoPushCycle : ¬ ∃ x : Γ', At = x :: a :: At := by
            rintro ⟨x, hx⟩
            have hlen := congrArg List.length hx
            simp at hlen
            omega
          by_cases hp : p a = true
          all_goals
            simp [hnoPushCycle, branchU, branchActionForCoordU_aux, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
              StackMachineEncoding.coordMultiplier,
              StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
              moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
              stackPop, stackPush, stackSet, stackGet, stackActionU, stackActionU_self,
              BranchAction.multiplier, BranchAction.stay, BranchAction.const,
              BranchAction.pop, BranchAction.push, BranchAction.affine,
              StackMove.delta, B_U, hp]
  · cases D with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Dt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]

private theorem branchU_move_data_multiplier_le
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))
        dataStackCoordU := by
  cases k₁
  · cases M with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_data, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                dataStackU, stackPop, stackPush, stackSet, stackGet,
                stackActionU_self, stackActionU_push_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, hp]
        | cons b Mt =>
            cases k₂ <;> by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_data, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                dataStackU, stackPop, stackPush, stackSet, stackGet,
                stackActionU_self, stackActionU_push_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, hp]
  · cases R with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a Rt =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]
  · cases A with
    | nil =>
        cases k₂ <;>
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
    | cons a At =>
        cases k₂ <;> by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            dataStackU, stackPop, stackPush, stackSet, stackGet,
            stackActionU_self, stackActionU_push_cons,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U, hp]
  · cases k₂ <;>
      cases D with
      | nil =>
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, dataStackU,
            stackPop, stackPush, stackSet, stackGet, stackActionU, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.push, BranchAction.affine,
            StackMove.delta, B_U]
      | cons a Dt =>
          have hnoPushCycle : ¬ ∃ x : Γ', Dt = x :: a :: Dt := by
            rintro ⟨x, hx⟩
            have hlen := congrArg List.length hx
            simp at hlen
            omega
          by_cases hp : p a = true
          all_goals
            simp [hnoPushCycle, branchU, branchActionForCoordU_data, localViewU,
              localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
              StackMachineEncoding.coordMultiplier,
              StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
              moveTypeStackU, indexedStackU, stackMoveForListsU, dataStackU,
              stackPop, stackPush, stackSet, stackGet, stackActionU, stackActionU_self,
              BranchAction.multiplier, BranchAction.stay, BranchAction.const,
              BranchAction.pop, BranchAction.push, BranchAction.affine,
              StackMove.delta, B_U, hp]

private theorem branchU_clause_move_multiplier_le
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · exact branchU_move_main_multiplier_le p k₁ k₂ q hmem v M R A D
  · exact branchU_move_rev_multiplier_le p k₁ k₂ q hmem v M R A D
  · exact branchU_move_aux_multiplier_le p k₁ k₂ q hmem v M R A D
  · exact branchU_move_data_multiplier_le p k₁ k₂ q hmem v M R A D
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_move
    (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
    (hmem : Λ'.move p k₁ k₂ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.move p k₁ k₂ q, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_move_exact_next p k₁ k₂ q hmem v M R A D
  · exact branchU_clause_move_multiplier_le p k₁ k₂ q hmem v M R A D

private theorem branchU_clear_main_source_exact
    (p : Γ' → Bool) (q : Λ')
    (hmem : Λ'.clear p K'.main q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p K'.main q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p K'.main q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p K'.main q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases M with
  | nil =>
      simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
        stackGet, stackSet, stackActionU, BranchAction.evalQ,
        BranchAction.stay, BranchAction.affine]
  | cons a Mt =>
      cases Mt with
      | nil =>
          by_cases hp : p a = true
          all_goals
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
              stackGet, stackSet, stackActionU, hp,
              eval_stack_pop_actionU, eval_stack_stay_actionU]
      | cons b Mt =>
          by_cases hp : p a = true
          all_goals
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
              stackGet, stackSet, stackActionU, hp,
              eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem branchU_clear_rev_source_exact
    (p : Γ' → Bool) (q : Λ')
    (hmem : Λ'.clear p K'.rev q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p K'.rev q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p K'.rev q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p K'.rev q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases R with
  | nil =>
      simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
        stackGet, stackSet, stackActionU, BranchAction.evalQ,
        BranchAction.stay, BranchAction.affine]
  | cons a Rt =>
      by_cases hp : p a = true
      all_goals
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
          stackGet, stackSet, stackActionU, hp,
          eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem branchU_clear_aux_source_exact
    (p : Γ' → Bool) (q : Λ')
    (hmem : Λ'.clear p K'.aux q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p K'.aux q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p K'.aux q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p K'.aux q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases A with
  | nil =>
      simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
        stackGet, stackSet, stackActionU, BranchAction.evalQ,
        BranchAction.stay, BranchAction.affine]
  | cons a At =>
      by_cases hp : p a = true
      all_goals
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
          stackGet, stackSet, stackActionU, hp,
          eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem branchU_clear_data_source_exact
    (p : Γ' → Bool) (q : Λ')
    (hmem : Λ'.clear p K'.stack q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p K'.stack q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p K'.stack q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p K'.stack q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases D with
  | nil =>
      simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
        stackGet, stackSet, stackActionU, BranchAction.evalQ,
        BranchAction.stay, BranchAction.affine]
  | cons a Dt =>
      by_cases hp : p a = true
      all_goals
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
          stackGet, stackSet, stackActionU, hp,
          eval_stack_pop_actionU, eval_stack_stay_actionU]

private theorem branchU_clear_main_all_exact
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases k
  · exact branchU_clear_main_source_exact p q hmem v M R A D
  · cases R with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, revStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, revStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]
  · cases A with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, auxStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, auxStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]
  · cases D with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, dataStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, dataStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]

private theorem branchU_clear_rev_all_exact
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, revStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, mainStackU, revStackU,
                stackPop, stackGet, stackSet, stackActionU_self,
                eval_stack_stay_actionU, hp]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, mainStackU, revStackU,
                stackPop, stackGet, stackSet, stackActionU_self,
                eval_stack_stay_actionU, hp]
  · exact branchU_clear_rev_source_exact p q hmem v M R A D
  · cases A with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, auxStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
            localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, auxStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]
  · cases D with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, dataStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
            localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, dataStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]

private theorem branchU_clear_aux_all_exact
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, auxStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
                localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, mainStackU, auxStackU,
                stackPop, stackGet, stackSet, stackActionU_self,
                eval_stack_stay_actionU, hp]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
                localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, mainStackU, auxStackU,
                stackPop, stackGet, stackSet, stackActionU_self,
                eval_stack_stay_actionU, hp]
  · cases R with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, auxStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
            localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, auxStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]
  · exact branchU_clear_aux_source_exact p q hmem v M R A D
  · cases D with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, dataStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
            localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, dataStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]

private theorem branchU_clear_data_all_exact
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, dataStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
                localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, mainStackU, dataStackU,
                stackPop, stackGet, stackSet, stackActionU_self,
                eval_stack_stay_actionU, hp]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
                localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, mainStackU, dataStackU,
                stackPop, stackGet, stackSet, stackActionU_self,
                eval_stack_stay_actionU, hp]
  · cases R with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, dataStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
            localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, dataStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]
  · cases A with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, dataStackU,
          stackPop, stackGet, stackSet, stackActionU_self,
          eval_stack_stay_actionU]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
            localViewU, localViewConfU, shortStackU, stackTopU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, dataStackU,
            stackPop, stackGet, stackSet, stackActionU_self,
            eval_stack_stay_actionU, hp]
  · exact branchU_clear_data_source_exact p q hmem v M R A D

private theorem branchU_clear_ctrl_exact
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine]
  · cases R with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
            stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine]
  · cases A with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
            stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine]
  · cases D with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_ctrl,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
            stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine]

private theorem branchU_clear_halt_exact
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine, haltFlagU, finHalted]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                haltFlagU, finHalted]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                mainStackU, stackPop, stackSet, stackGet, hp,
                BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                haltFlagU, finHalted]
  · cases R with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine, haltFlagU, finHalted]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
            stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine, haltFlagU, finHalted]
  · cases A with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine, haltFlagU, finHalted]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPop,
            stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine, haltFlagU, finHalted]
  · cases D with
    | nil =>
        simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
          stackSet, stackGet, BranchAction.evalQ, BranchAction.const,
          BranchAction.affine, haltFlagU, finHalted]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_halt,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPop,
            stackSet, stackGet, hp, BranchAction.evalQ,
            BranchAction.const, BranchAction.affine, haltFlagU, finHalted]

private theorem branchU_clause_clear_exact_next
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
          i =
        stackMachineEncodingU.enc
          (M_U.step
            (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))
          i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_clear_main_all_exact p k q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_clear_rev_all_exact p k q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_clear_aux_all_exact p k q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_clear_data_all_exact p k q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_clear_ctrl_exact p k q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_clear_halt_exact p k q hmem v M R A D)

private theorem branchU_clear_main_multiplier_le
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))
        mainStackCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
          stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_main, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
        | cons b Mt =>
            have hcycle : Mt ≠ a :: b :: Mt := by
              intro h
              have hlen := congrArg List.length h
              simp at hlen
              omega
            by_cases hp : p a = true
            all_goals
              simp [hcycle, branchU, branchActionForCoordU_main, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases R with
    | nil =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
          revStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            revStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases A with
    | nil =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
          auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases D with
    | nil =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
          dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]

private theorem branchU_clear_rev_multiplier_le
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))
        revStackCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
          revStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_rev, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                revStackU, stackPop, stackSet, stackGet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_rev, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                revStackU, stackPop, stackSet, stackGet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases R with
    | nil =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
          stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Rt =>
        have hnoPushCycle : ¬ ∃ x : Γ', Rt = x :: a :: Rt := by
          rintro ⟨x, hx⟩
          have hlen := congrArg List.length hx
          simp at hlen
          omega
        by_cases hp : p a = true
        all_goals
          simp [hnoPushCycle, branchU, branchActionForCoordU_rev, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases A with
    | nil =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
          auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases D with
    | nil =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
          dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]

private theorem branchU_clear_aux_multiplier_le
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))
        auxStackCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
          auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_aux, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_aux, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases R with
    | nil =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
          auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            auxStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases A with
    | nil =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
          stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a At =>
        have hnoPushCycle : ¬ ∃ x : Γ', At = x :: a :: At := by
          rintro ⟨x, hx⟩
          have hlen := congrArg List.length hx
          simp at hlen
          omega
        by_cases hp : p a = true
        all_goals
          simp [hnoPushCycle, branchU, branchActionForCoordU_aux, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases D with
    | nil =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
          dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Dt =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]

private theorem branchU_clear_data_multiplier_le
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))
        dataStackCoordU := by
  cases k
  · cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
          dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt with
        | nil =>
            by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_data, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
        | cons b Mt =>
            by_cases hp : p a = true
            all_goals
              simp [branchU, branchActionForCoordU_data, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
                dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.const,
                BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases R with
    | nil =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
          dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Rt =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, revStackU,
            dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases A with
    | nil =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
          dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a At =>
        by_cases hp : p a = true
        all_goals
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, auxStackU,
            dataStackU, stackPop, stackSet, stackGet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]
  · cases D with
    | nil =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU, dataStackU,
          stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.const,
          BranchAction.pop, BranchAction.affine, StackMove.delta, B_U]
    | cons a Dt =>
        have hnoPushCycle : ¬ ∃ x : Γ', Dt = x :: a :: Dt := by
          rintro ⟨x, hx⟩
          have hlen := congrArg List.length hx
          simp at hlen
          omega
        by_cases hp : p a = true
        all_goals
          simp [hnoPushCycle, branchU, branchActionForCoordU_data, localViewU,
            localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, dataStackU,
            stackPop, stackSet, stackGet, stackActionU, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.const,
            BranchAction.pop, BranchAction.affine, StackMove.delta, B_U, hp]

private theorem branchU_clause_clear_multiplier_le
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · exact branchU_clear_main_multiplier_le p k q hmem v M R A D
  · exact branchU_clear_rev_multiplier_le p k q hmem v M R A D
  · exact branchU_clear_aux_multiplier_le p k q hmem v M R A D
  · exact branchU_clear_data_multiplier_le p k q hmem v M R A D
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_clear
    (p : Γ' → Bool) (k : K') (q : Λ')
    (hmem : Λ'.clear p k q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.clear p k q, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_clear_exact_next p k q hmem v M R A D
  · exact branchU_clause_clear_multiplier_le p k q hmem v M R A D

private theorem branchU_read_main_exact
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    mainStackU] using eval_stackActionU_short_stack_self_full M

private theorem branchU_read_rev_exact
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    revStackU] using eval_stackActionU_short_top_self_full R

private theorem branchU_read_aux_exact
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    auxStackU] using eval_stackActionU_short_top_self_full A

private theorem branchU_read_data_exact
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    dataStackU] using eval_stackActionU_short_top_self_full D

private theorem branchU_read_ctrl_exact
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU)
      (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) ctrlCoordU) =
    confEncU
      (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
      ctrlCoordU
  rw [branchActionForCoordU_ctrl]
  simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU]

private theorem branchU_read_halt_exact
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
        haltCoordU)
      (confEncU (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) haltCoordU) =
    confEncU
      (finStep (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
      haltCoordU
  rw [branchActionForCoordU_halt]
  simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU, haltCoordU, haltFlagU, finHalted]

private theorem branchU_clause_read_exact_next
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
          i =
        stackMachineEncodingU.enc
          (M_U.step
            (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))
          i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_read_main_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_read_rev_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_read_aux_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_read_data_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_read_ctrl_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_read_halt_exact q hmem v M R A D)

private theorem branchU_read_stack_multiplier_le
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i, i = mainStackCoordU ∨ i = revStackCoordU ∨
        i = auxStackCoordU ∨ i = dataStackCoordU →
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) i := by
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl
  · simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
      finStep_eq_finStepBranch_U, finStepBranch, stackActionU_self,
      BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self, mainStackU,
      StackMove.delta, B_U]
  · simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
      finStep_eq_finStepBranch_U, finStepBranch, stackActionU_self,
      BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self, revStackU,
      StackMove.delta, B_U]
  · simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
      finStep_eq_finStepBranch_U, finStepBranch, stackActionU_self,
      BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self, auxStackU,
      StackMove.delta, B_U]
  · simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
      finStep_eq_finStepBranch_U, finStepBranch, stackActionU_self,
      BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self, dataStackU,
      StackMove.delta, B_U]

private theorem branchU_clause_read_multiplier_le
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · exact branchU_read_stack_multiplier_le q hmem v M R A D
      mainStackCoordU (Or.inl rfl)
  · exact branchU_read_stack_multiplier_le q hmem v M R A D
      revStackCoordU (Or.inr (Or.inl rfl))
  · exact branchU_read_stack_multiplier_le q hmem v M R A D
      auxStackCoordU (Or.inr (Or.inr (Or.inl rfl)))
  · exact branchU_read_stack_multiplier_le q hmem v M R A D
      dataStackCoordU (Or.inr (Or.inr (Or.inr rfl)))
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_read
    (q : Option Γ' → Λ')
    (hmem : Λ'.read q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.read q, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_read_exact_next q hmem v M R A D
  · exact branchU_clause_read_multiplier_le q hmem v M R A D

private theorem branchU_push_main_exact
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases hfv : f v with
  | none =>
      cases k <;>
        simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, revStackU, auxStackU, dataStackU,
          stackPush, stackGet, stackSet, hfv] using
          eval_stackActionU_short_stack_self_full M
  | some g =>
      cases k
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
          finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPush,
          stackGet, stackSet, hfv, stackActionU_push_cons] using
          eval_stack_push_actionU g M
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, revStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_stack_self_full M
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, auxStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_stack_self_full M
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, dataStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_stack_self_full M

private theorem branchU_push_rev_exact
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases hfv : f v with
  | none =>
      cases k <;>
        simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, revStackU, auxStackU, dataStackU,
          stackPush, stackGet, stackSet, hfv] using
          eval_stackActionU_short_top_self_full R
  | some g =>
      cases k
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, revStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full R
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPush,
          stackGet, stackSet, hfv, stackActionU_push_cons] using
          eval_stack_push_actionU g R
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, revStackU, auxStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full R
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, revStackU, dataStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full R

private theorem branchU_push_aux_exact
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases hfv : f v with
  | none =>
      cases k <;>
        simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, revStackU, auxStackU, dataStackU,
          stackPush, stackGet, stackSet, hfv] using
          eval_stackActionU_short_top_self_full A
  | some g =>
      cases k
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, auxStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full A
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, revStackU, auxStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full A
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, auxStackU, stackPush,
          stackGet, stackSet, hfv, stackActionU_push_cons] using
          eval_stack_push_actionU g A
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, auxStackU, dataStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full A

private theorem branchU_push_data_exact
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases hfv : f v with
  | none =>
      cases k <;>
        simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, revStackU, auxStackU, dataStackU,
          stackPush, stackGet, stackSet, hfv] using
          eval_stackActionU_short_top_self_full D
  | some g =>
      cases k
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, mainStackU, dataStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full D
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, revStackU, dataStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full D
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, finStep_eq_finStepBranch_U,
          finStepBranch, auxStackU, dataStackU, stackPush, stackGet,
          stackSet, hfv] using eval_stackActionU_short_top_self_full D
      · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
          localViewU, localViewConfU, shortStackU, stackTopU,
          finStep_eq_finStepBranch_U, finStepBranch, dataStackU, stackPush,
          stackGet, stackSet, hfv, stackActionU_push_cons] using
          eval_stack_push_actionU g D

private theorem branchU_push_ctrl_exact
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU)
      (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)) ctrlCoordU) =
    confEncU
      (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
      ctrlCoordU
  rw [branchActionForCoordU_ctrl]
  cases hfv : f v <;> cases k <;>
    simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
      localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
      confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
      ctrlCoordU, stackPush, stackGet, stackSet, hfv]

private theorem branchU_push_halt_exact
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
        haltCoordU)
      (confEncU (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)) haltCoordU) =
    confEncU
      (finStep (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
      haltCoordU
  rw [branchActionForCoordU_halt]
  cases hfv : f v <;> cases k <;>
    simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
      localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
      confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
      ctrlCoordU, haltCoordU, haltFlagU, finHalted, stackPush, stackGet,
      stackSet, hfv]

private theorem branchU_clause_push_exact_next
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
          i =
        stackMachineEncodingU.enc
          (M_U.step
            (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))
          i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_push_main_exact k f q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_push_rev_exact k f q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_push_aux_exact k f q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_push_data_exact k f q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_push_ctrl_exact k f q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_push_halt_exact k f q hmem v M R A D)

private theorem branchU_push_main_multiplier_le
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))
        mainStackCoordU := by
  cases hfv : f v <;> cases k <;>
    simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
      shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
      finStepBranch, stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self,
      stackMoveForListsU_push, mainStackU, revStackU, auxStackU, dataStackU,
      stackPush, stackGet, stackSet, stackActionU_self, stackActionU_push_cons,
      BranchAction.multiplier, BranchAction.stay, BranchAction.push,
      BranchAction.affine, StackMove.delta, hfv, B_U]

private theorem branchU_push_rev_multiplier_le
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))
        revStackCoordU := by
  cases hfv : f v <;> cases k <;>
    simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self,
      stackMoveForListsU_push, mainStackU, revStackU, auxStackU, dataStackU,
      stackPush, stackGet, stackSet, stackActionU_self, stackActionU_push_cons,
      BranchAction.multiplier, BranchAction.stay, BranchAction.push,
      BranchAction.affine, StackMove.delta, hfv, B_U]

private theorem branchU_push_aux_multiplier_le
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))
        auxStackCoordU := by
  cases hfv : f v <;> cases k <;>
    simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self,
      stackMoveForListsU_push, mainStackU, revStackU, auxStackU, dataStackU,
      stackPush, stackGet, stackSet, stackActionU_self, stackActionU_push_cons,
      BranchAction.multiplier, BranchAction.stay, BranchAction.push,
      BranchAction.affine, StackMove.delta, hfv, B_U]

private theorem branchU_push_data_multiplier_le
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))
        dataStackCoordU := by
  cases hfv : f v <;> cases k <;>
    simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self,
      stackMoveForListsU_push, mainStackU, revStackU, auxStackU, dataStackU,
      stackPush, stackGet, stackSet, stackActionU_self, stackActionU_push_cons,
      BranchAction.multiplier, BranchAction.stay, BranchAction.push,
      BranchAction.affine, StackMove.delta, hfv, B_U]

private theorem branchU_clause_push_multiplier_le
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · exact branchU_push_main_multiplier_le k f q hmem v M R A D
  · exact branchU_push_rev_multiplier_le k f q hmem v M R A D
  · exact branchU_push_aux_multiplier_le k f q hmem v M R A D
  · exact branchU_push_data_multiplier_le k f q hmem v M R A D
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_push
    (k : K') (f : Option Γ' → Option Γ') (q : Λ')
    (hmem : Λ'.push k f q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.push k f q, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_push_exact_next k f q hmem v M R A D
  · exact branchU_clause_push_multiplier_le k f q hmem v M R A D

private theorem branchU_copy_main_exact
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases R with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        mainStackU, revStackU, stackPop] using
        eval_stackActionU_short_stack_self_full M
  | cons a Rt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, revStackU,
        stackPop, stackPush, stackGet, stackSet, stackActionU_push_cons] using
        eval_stack_push_actionU a M

private theorem branchU_copy_rev_exact
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases R with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU, stackPop] using eval_stackActionU_short_top_self_full []
  | cons a Rt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, revStackU, stackPop,
        stackPush, stackGet, stackSet, stackActionU_pop_cons] using
        eval_stack_pop_actionU a Rt

private theorem branchU_copy_aux_exact
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases R with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU, auxStackU, stackPop] using
        eval_stackActionU_short_top_self_full A
  | cons a Rt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU, auxStackU, stackPop, stackPush, stackGet, stackSet] using
        eval_stackActionU_short_top_self_full A

private theorem branchU_copy_data_exact
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases R with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU, dataStackU, stackPop] using
        eval_stackActionU_short_top_self_full D
  | cons a Rt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, revStackU, dataStackU,
        stackPop, stackPush, stackGet, stackSet, stackActionU_push_cons] using
        eval_stack_push_actionU a D

private theorem branchU_copy_ctrl_exact
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU)
      (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)) ctrlCoordU) =
    confEncU
      (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
      ctrlCoordU
  rw [branchActionForCoordU_ctrl]
  cases R <;>
    simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
      localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
      confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
      ctrlCoordU, mainStackU, revStackU, auxStackU, dataStackU, shortStackU,
      stackTopU, stackSecondU, stackPop, stackPush, stackGet, stackSet]

private theorem branchU_copy_halt_exact
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
        haltCoordU)
      (confEncU (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)) haltCoordU) =
    confEncU
      (finStep (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
      haltCoordU
  rw [branchActionForCoordU_halt]
  cases R <;>
    simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
      localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
      confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
      ctrlCoordU, haltCoordU, haltFlagU, finHalted, mainStackU, revStackU,
      auxStackU, dataStackU, shortStackU, stackTopU, stackSecondU, stackPop,
      stackPush, stackGet, stackSet]

private theorem branchU_clause_copy_exact_next
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
          i =
        stackMachineEncodingU.enc
          (M_U.step
            (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))
          i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_copy_main_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_copy_rev_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_copy_aux_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_copy_data_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_copy_ctrl_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ))
      (branchU_copy_halt_exact q hmem v M R A D)

private theorem branchU_copy_main_multiplier_le
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))
        mainStackCoordU := by
  cases R <;>
    simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
      shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
      finStepBranch, stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self,
      stackMoveForListsU_push, mainStackU, revStackU, stackPop, stackPush,
      stackGet, stackSet, stackActionU_self, stackActionU_push_cons,
      BranchAction.multiplier, BranchAction.stay, BranchAction.push,
      BranchAction.affine, StackMove.delta, B_U]

private theorem branchU_copy_rev_multiplier_le
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))
        revStackCoordU := by
  cases R <;>
    simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self,
      stackMoveForListsU_pop, revStackU, stackPop, stackPush, stackGet,
      stackSet, stackActionU_self, stackActionU_pop_cons,
      BranchAction.multiplier, BranchAction.stay, BranchAction.pop,
      BranchAction.affine, StackMove.delta, B_U]

private theorem branchU_copy_aux_multiplier_le
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))
        auxStackCoordU := by
  cases R <;>
    simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackMachineEncodingU,
      StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
      StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
      stackMoveForListsU_self, revStackU, auxStackU, stackPop, stackPush,
      stackGet, stackSet, stackActionU_self, BranchAction.multiplier,
      BranchAction.stay, BranchAction.affine, StackMove.delta, B_U]

private theorem branchU_copy_data_multiplier_le
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))
        dataStackCoordU := by
  cases R <;>
    simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
      StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
      moveTypeStackU, indexedStackU, stackMoveForListsU_self,
      stackMoveForListsU_push, revStackU, dataStackU, stackPop, stackPush,
      stackGet, stackSet, stackActionU_self, stackActionU_push_cons,
      BranchAction.multiplier, BranchAction.stay, BranchAction.push,
      BranchAction.affine, StackMove.delta, B_U]

private theorem branchU_clause_copy_multiplier_le
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · exact branchU_copy_main_multiplier_le q hmem v M R A D
  · exact branchU_copy_rev_multiplier_le q hmem v M R A D
  · exact branchU_copy_aux_multiplier_le q hmem v M R A D
  · exact branchU_copy_data_multiplier_le q hmem v M R A D
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_copy
    (q : Λ') (hmem : Λ'.copy q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.copy q, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_copy_exact_next q hmem v M R A D
  · exact branchU_clause_copy_multiplier_le q hmem v M R A D

private theorem branchU_none_main_exact
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU (none, v, (M, R, A, D))))
        (confEncU (none, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU (finStep (none, v, (M, R, A, D))) mainStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    mainStackU] using eval_stackActionU_short_stack_self_full M

private theorem branchU_none_rev_exact
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU (none, v, (M, R, A, D))))
        (confEncU (none, v, (M, R, A, D)))
        revStackCoordU =
      confEncU (finStep (none, v, (M, R, A, D))) revStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    revStackU] using eval_stackActionU_short_top_self_full R

private theorem branchU_none_aux_exact
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU (none, v, (M, R, A, D))))
        (confEncU (none, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU (finStep (none, v, (M, R, A, D))) auxStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    auxStackU] using eval_stackActionU_short_top_self_full A

private theorem branchU_none_data_exact
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU (none, v, (M, R, A, D))))
        (confEncU (none, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU (finStep (none, v, (M, R, A, D))) dataStackCoordU := by
  simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    dataStackU] using eval_stackActionU_short_top_self_full D

private theorem branchU_none_ctrl_exact
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU (none, v, (M, R, A, D))))
        (confEncU (none, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU (finStep (none, v, (M, R, A, D))) ctrlCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU (localViewU (none, v, (M, R, A, D))) ctrlCoordU)
      (confEncU (none, v, (M, R, A, D)) ctrlCoordU) =
    confEncU (finStep (none, v, (M, R, A, D))) ctrlCoordU
  rw [branchActionForCoordU_ctrl]
  simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU]

private theorem branchU_none_halt_exact
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU (none, v, (M, R, A, D))))
        (confEncU (none, v, (M, R, A, D)))
        haltCoordU =
      confEncU (finStep (none, v, (M, R, A, D))) haltCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU (localViewU (none, v, (M, R, A, D))) haltCoordU)
      (confEncU (none, v, (M, R, A, D)) haltCoordU) =
    confEncU (finStep (none, v, (M, R, A, D))) haltCoordU
  rw [branchActionForCoordU_halt]
  simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
    localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
    confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
    ctrlCoordU, haltCoordU, haltFlagU, finHalted]

private theorem branchU_clause_none_exact_next
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU (none, v, (M, R, A, D))))
          (stackMachineEncodingU.enc (none, v, (M, R, A, D))) i =
        stackMachineEncodingU.enc
          (M_U.step (none, v, (M, R, A, D))) i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_none_main_exact v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_none_rev_exact v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_none_aux_exact v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_none_data_exact v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_none_ctrl_exact v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_none_halt_exact v M R A D)

private theorem branchU_clause_none_multiplier_le
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU (none, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier (none, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · change BranchAction.multiplier B_U
        ((branchU (localViewU (none, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier (none, v, (M, R, A, D))
        mainStackCoordU
    simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
      shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
      finStepBranch, stackActionU_self, BranchAction.multiplier,
      BranchAction.stay, BranchAction.affine, stackMachineEncodingU,
      StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
      StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
      stackMoveForListsU_self, mainStackU, StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU (none, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier (none, v, (M, R, A, D))
        revStackCoordU
    simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackActionU_self, BranchAction.multiplier, BranchAction.stay,
      BranchAction.affine, stackMachineEncodingU,
      StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
      StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
      stackMoveForListsU_self, revStackU, StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU (none, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier (none, v, (M, R, A, D))
        auxStackCoordU
    simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackActionU_self, BranchAction.multiplier, BranchAction.stay,
      BranchAction.affine, stackMachineEncodingU,
      StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
      StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
      stackMoveForListsU_self, auxStackU, StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU (none, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier (none, v, (M, R, A, D))
        dataStackCoordU
    simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
      shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
      stackActionU_self, BranchAction.multiplier, BranchAction.stay,
      BranchAction.affine, stackMachineEncodingU,
      StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
      StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
      stackMoveForListsU_self, dataStackU, StackMove.delta, B_U]
  · exact branchU_reset_multiplier_le (none, v, (M, R, A, D)) ctrlCoordU
      (Or.inl rfl)
  · exact branchU_reset_multiplier_le (none, v, (M, R, A, D)) haltCoordU
      (Or.inr rfl)

private theorem branchU_clause_none
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU (none, v, (M, R, A, D))
      (branchU (localViewU (none, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_none_exact_next v M R A D
  · exact branchU_clause_none_multiplier_le v M R A D

private theorem branchU_succ_main_exact
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases M with
  | nil =>
      simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
        stackPush, stackGet, stackSet, stackActionU, BranchAction.evalQ,
        BranchAction.push, BranchAction.affine, stackCodeU]
      norm_num [B_U]
      ring
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU, BranchAction.evalQ, BranchAction.push,
              BranchAction.pop, BranchAction.replace, BranchAction.affine,
              eval_stack_pop_actionU, eval_stack_push_actionU,
              eval_stack_replace_actionU, stackCodeU] <;>
            norm_num [B_U] <;> ring
      | cons b Mt =>
          cases a <;>
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU, BranchAction.evalQ, BranchAction.push,
              BranchAction.pop, BranchAction.replace, BranchAction.affine,
              eval_stack_pop_actionU, eval_stack_push_actionU,
              eval_stack_replace_actionU, stackCodeU] <;>
            norm_num [B_U] <;> ring

private theorem branchU_succ_rev_exact
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases M with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, revStackU, mainStackU,
        stackPop, stackPush, stackGet, stackSet] using
        eval_stackActionU_short_top_self_full R
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full R
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full R
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full R
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_push_cons]
            using eval_stack_push_actionU Γ'.bit0 R
      | cons b Mt =>
          cases a
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full R
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full R
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full R
          · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_push_cons]
            using eval_stack_push_actionU Γ'.bit0 R

private theorem branchU_succ_aux_exact
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases M with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, auxStackU, mainStackU,
        stackPop, stackPush, stackGet, stackSet] using
        eval_stackActionU_short_top_self_full A
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              auxStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full A
      | cons b Mt =>
          cases a <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              auxStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full A

private theorem branchU_succ_data_exact
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases M with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, shortStackU, stackTopU,
        finStep_eq_finStepBranch_U, finStepBranch, dataStackU, mainStackU,
        stackPop, stackPush, stackGet, stackSet] using
        eval_stackActionU_short_top_self_full D
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              dataStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full D
      | cons b Mt =>
          cases a <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              dataStackU, mainStackU, stackPop, stackPush, stackGet, stackSet]
            using eval_stackActionU_short_top_self_full D

private theorem branchU_succ_ctrl_exact
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU)
      (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) ctrlCoordU) =
    confEncU
      (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
      ctrlCoordU
  rw [branchActionForCoordU_ctrl]
  cases M with
  | nil =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
        stackPush, stackGet, stackSet, confEncU, mainStackCoordU,
        revStackCoordU, auxStackCoordU, dataStackCoordU, ctrlCoordU]
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU]
      | cons b Mt =>
          cases a <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU]

private theorem branchU_succ_halt_exact
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
        haltCoordU)
      (confEncU (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) haltCoordU) =
    confEncU
      (finStep (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))
      haltCoordU
  rw [branchActionForCoordU_halt]
  cases M with
  | nil =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
        stackPush, stackGet, stackSet, confEncU, mainStackCoordU,
        revStackCoordU, auxStackCoordU, dataStackCoordU, ctrlCoordU,
        haltCoordU, haltFlagU, finHalted]
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU, haltCoordU, haltFlagU, finHalted]
      | cons b Mt =>
          cases a <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU, haltCoordU, haltFlagU, finHalted]

private theorem branchU_clause_succ_exact_next
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))) i =
        stackMachineEncodingU.enc
          (M_U.step (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))) i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_succ_main_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_succ_rev_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_succ_aux_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_succ_data_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_succ_ctrl_exact q hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_succ_halt_exact q hmem v M R A D)

private theorem branchU_clause_succ_multiplier_le
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) mainStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_push, mainStackU, stackPop, stackPush, stackGet,
          stackSet, stackActionU, BranchAction.multiplier, BranchAction.push,
          BranchAction.affine, StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt <;> cases a <;>
          simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU, mainStackU,
            stackMoveForListsU_pop, stackPop, stackPush, stackGet, stackSet,
            stackActionU,
            BranchAction.multiplier, BranchAction.push, BranchAction.pop,
            BranchAction.replace, BranchAction.affine, StackMove.delta, B_U,
            list_ne_cons_cons_self]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) revStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
          stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU_self, revStackU,
          mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt <;> cases a <;>
          simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU_self,
            stackMoveForListsU_push, revStackU, mainStackU, stackPop,
            stackPush, stackGet, stackSet, stackActionU_self,
            stackActionU_push_cons, BranchAction.multiplier, BranchAction.stay,
            BranchAction.push, BranchAction.affine, StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) auxStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
          stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU_self, auxStackU,
          mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt <;> cases a <;>
          simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU_self, auxStackU,
            mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
            StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) dataStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          shortStackU, stackTopU, finStep_eq_finStepBranch_U, finStepBranch,
          stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
          StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
          moveTypeStackU, indexedStackU, stackMoveForListsU_self, dataStackU,
          mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | cons a Mt =>
        cases Mt <;> cases a <;>
          simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
            shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
            finStepBranch, stackMachineEncodingU,
            StackMachineEncoding.coordMultiplier,
            StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
            moveTypeStackU, indexedStackU, stackMoveForListsU_self, dataStackU,
            mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
            BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
            StackMove.delta, B_U]
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_succ
    (q : Λ') (hmem : Λ'.succ q ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.succ q, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_succ_exact_next q hmem v M R A D
  · exact branchU_clause_succ_multiplier_le q hmem v M R A D

private theorem branchU_pred_main_exact
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases M with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
        stackPush, stackGet, stackSet, natEnd] using
        eval_stackActionU_short_stack_self_full []
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU, BranchAction.evalQ, BranchAction.stay,
              BranchAction.pop, BranchAction.push, BranchAction.const,
              BranchAction.affine, eval_stack_pop_actionU,
              eval_stack_push_actionU, eval_stack_const_actionU,
              eval_stack_stay_actionU, stackCodeU, natEnd] <;>
            norm_num [B_U, bot, gammaDigit] <;>
            ring_nf
      | cons b Mt =>
          cases a <;> cases b <;>
            simp [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU, BranchAction.evalQ, BranchAction.stay,
              BranchAction.pop, BranchAction.push, BranchAction.const,
              BranchAction.affine, eval_stack_pop_actionU,
              eval_stack_push_actionU, eval_stack_const_actionU,
              eval_stack_stay_actionU, stackCodeU, natEnd] <;>
            norm_num [B_U, bot, gammaDigit] <;>
            ring_nf

private theorem branchU_pred_rev_exact
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases M with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, revStackU, mainStackU,
        stackPop, stackPush, stackGet, stackSet, stackActionU_self,
        natEnd] using eval_stackActionU_short_top_self_full R
  | cons a Mt =>
      cases a
      · cases Mt with
        | nil =>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, revStackU, mainStackU,
              stackPop, stackPush, stackGet, stackSet, stackActionU_self,
              natEnd] using eval_stackActionU_short_top_self_full R
        | cons b Mt =>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, revStackU, mainStackU,
              stackPop, stackPush, stackGet, stackSet, stackActionU_self,
              natEnd] using eval_stackActionU_short_top_self_full R
      · cases Mt with
        | nil =>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, revStackU, mainStackU,
              stackPop, stackPush, stackGet, stackSet, stackActionU_self,
              natEnd] using eval_stackActionU_short_top_self_full R
        | cons b Mt =>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
              finStep_eq_finStepBranch_U, finStepBranch, revStackU, mainStackU,
              stackPop, stackPush, stackGet, stackSet, stackActionU_self,
              natEnd] using eval_stackActionU_short_top_self_full R
      · cases Mt with
        | nil =>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_push_cons, natEnd] using
              eval_stack_push_actionU Γ'.bit1 R
        | cons b Mt =>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_push_cons, natEnd] using
              eval_stack_push_actionU Γ'.bit1 R
      · cases Mt with
        | nil =>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_self, natEnd] using
              eval_stackActionU_short_top_self_full R
        | cons b Mt =>
            cases b
            · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
                stackActionU_self, natEnd] using
                eval_stackActionU_short_top_self_full R
            · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
                stackActionU_self, natEnd] using
                eval_stackActionU_short_top_self_full R
            · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
                stackActionU_push_cons, natEnd] using
                eval_stack_push_actionU Γ'.bit0 R
            · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                localViewU, localViewConfU, shortStackU, stackTopU,
                stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                revStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
                stackActionU_push_cons, natEnd] using
                eval_stack_push_actionU Γ'.bit0 R

private theorem branchU_pred_aux_exact
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases M with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, auxStackU, mainStackU,
        stackPop, stackPush, stackGet, stackSet, stackActionU_self, natEnd]
        using eval_stackActionU_short_top_self_full A
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              auxStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_self, natEnd] using
              eval_stackActionU_short_top_self_full A
      | cons b Mt =>
          cases a <;> cases b <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              auxStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_self, natEnd] using
              eval_stackActionU_short_top_self_full A

private theorem branchU_pred_data_exact
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases M with
  | nil =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, dataStackU, mainStackU,
        stackPop, stackPush, stackGet, stackSet, stackActionU_self, natEnd]
        using eval_stackActionU_short_top_self_full D
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              dataStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_self, natEnd] using
              eval_stackActionU_short_top_self_full D
      | cons b Mt =>
          cases a <;> cases b <;>
            simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              dataStackU, mainStackU, stackPop, stackPush, stackGet, stackSet,
              stackActionU_self, natEnd] using
              eval_stackActionU_short_top_self_full D

private theorem branchU_pred_ctrl_exact
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU)
      (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) ctrlCoordU) =
    confEncU
      (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
      ctrlCoordU
  rw [branchActionForCoordU_ctrl]
  cases M with
  | nil =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
        stackPush, stackGet, stackSet, confEncU, mainStackCoordU,
        revStackCoordU, auxStackCoordU, dataStackCoordU, ctrlCoordU, natEnd]
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU, natEnd]
      | cons b Mt =>
          cases a <;> cases b <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU, natEnd]

private theorem branchU_pred_halt_exact
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
        haltCoordU)
      (confEncU (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) haltCoordU) =
    confEncU
      (finStep (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))
      haltCoordU
  rw [branchActionForCoordU_halt]
  cases M with
  | nil =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
        finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
        stackPush, stackGet, stackSet, confEncU, mainStackCoordU,
        revStackCoordU, auxStackCoordU, dataStackCoordU, ctrlCoordU,
        haltCoordU, haltFlagU, finHalted, natEnd]
  | cons a Mt =>
      cases Mt with
      | nil =>
          cases a <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU, haltCoordU, haltFlagU, finHalted, natEnd]
      | cons b Mt =>
          cases a <;> cases b <;>
            simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
              localViewU, localViewConfU, shortStackU, stackTopU,
              stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
              mainStackU, stackPop, stackPush, stackGet, stackSet, confEncU,
              mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
              ctrlCoordU, haltCoordU, haltFlagU, finHalted, natEnd]

private theorem branchU_clause_pred_exact_next
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))) i =
        stackMachineEncodingU.enc
          (M_U.step (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))) i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_pred_main_exact q₁ q₂ hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_pred_rev_exact q₁ q₂ hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_pred_aux_exact q₁ q₂ hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_pred_data_exact q₁ q₂ hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_pred_ctrl_exact q₁ q₂ hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_pred_halt_exact q₁ q₂ hmem v M R A D)

private theorem branchU_clause_pred_multiplier_le
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) mainStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, mainStackU, stackPop, stackPush, stackGet,
          stackSet, stackActionU_self, BranchAction.multiplier,
          BranchAction.stay, BranchAction.affine, StackMove.delta, B_U, natEnd]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases a <;>
              simp [branchU, branchActionForCoordU_main, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU,
                stackMoveForListsU_pop, stackMoveForListsU_self, mainStackU,
                stackPop, stackPush, stackGet, stackSet, stackActionU,
                stackActionU_self, stackActionU_pop_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.pop,
                BranchAction.const, BranchAction.affine, StackMove.delta, B_U,
                natEnd, list_ne_cons_cons_self]
        | cons b Mt =>
            cases a <;> cases b <;>
              simp [branchU, branchActionForCoordU_main, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU,
                stackMoveForListsU_pop, stackMoveForListsU_self, mainStackU,
                stackPop, stackPush, stackGet, stackSet, stackActionU,
                stackActionU_self, stackActionU_pop_cons,
                BranchAction.multiplier, BranchAction.stay, BranchAction.pop,
                BranchAction.const, BranchAction.affine, StackMove.delta, B_U,
                natEnd, list_ne_cons_cons_self]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) revStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, revStackU, mainStackU, stackPop, stackPush,
          stackGet, stackSet, stackActionU_self, BranchAction.multiplier,
          BranchAction.stay, BranchAction.affine, StackMove.delta, B_U, natEnd]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases a <;>
              simp [branchU, branchActionForCoordU_rev, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                stackMoveForListsU_push, revStackU, mainStackU, stackPop,
                stackPush, stackGet, stackSet, stackActionU_self,
                stackActionU_push_cons, BranchAction.multiplier,
                BranchAction.stay, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, natEnd]
        | cons b Mt =>
            cases a <;> cases b <;>
              simp [branchU, branchActionForCoordU_rev, localViewU,
                localViewConfU, shortStackU, stackTopU, stackSecondU,
                finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                stackMoveForListsU_push, revStackU, mainStackU, stackPop,
                stackPush, stackGet, stackSet, stackActionU_self,
                stackActionU_push_cons, BranchAction.multiplier,
                BranchAction.stay, BranchAction.push, BranchAction.affine,
                StackMove.delta, B_U, natEnd]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) auxStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, auxStackU, mainStackU, stackPop, stackPush,
          stackGet, stackSet, stackActionU_self, BranchAction.multiplier,
          BranchAction.stay, BranchAction.affine, StackMove.delta, B_U, natEnd]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases a <;>
              simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
                shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
                finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU_self, auxStackU,
                mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
                StackMove.delta, B_U, natEnd]
        | cons b Mt =>
            cases a <;> cases b <;>
              simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
                shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
                finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU_self, auxStackU,
                mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
                StackMove.delta, B_U, natEnd]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) dataStackCoordU
    cases M with
    | nil =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
          finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, dataStackU, mainStackU, stackPop, stackPush,
          stackGet, stackSet, stackActionU_self, BranchAction.multiplier,
          BranchAction.stay, BranchAction.affine, StackMove.delta, B_U, natEnd]
    | cons a Mt =>
        cases Mt with
        | nil =>
            cases a <;>
              simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
                shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
                finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU_self, dataStackU,
                mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
                StackMove.delta, B_U, natEnd]
        | cons b Mt =>
            cases a <;> cases b <;>
              simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
                shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
                finStepBranch, stackMachineEncodingU,
                StackMachineEncoding.coordMultiplier,
                StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                moveTypeStackU, indexedStackU, stackMoveForListsU_self, dataStackU,
                mainStackU, stackPop, stackPush, stackGet, stackSet, stackActionU_self,
                BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
                StackMove.delta, B_U, natEnd]
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_pred
    (q₁ q₂ : Λ') (hmem : Λ'.pred q₁ q₂ ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.pred q₁ q₂, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_pred_exact_next q₁ q₂ hmem v M R A D
  · exact branchU_clause_pred_multiplier_le q₁ q₂ hmem v M R A D

private theorem branchU_ret_main_exact
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        mainStackCoordU := by
  cases k with
  | cons₁ fs k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        mainStackU] using eval_stackActionU_short_stack_self_full M
  | cons₂ k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        mainStackU] using eval_stackActionU_short_stack_self_full M
  | comp f k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        mainStackU] using eval_stackActionU_short_stack_self_full M
  | fix f k =>
      cases M with
      | nil =>
          simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
            stackGet, stackSet, stackActionU_self, natEnd] using
            eval_stackActionU_short_stack_self_full []
      | cons a Mt =>
          cases Mt with
          | nil =>
              cases a
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.consₗ []
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.cons []
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.bit0 []
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.bit1 []
          | cons b Mt =>
              cases a
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.consₗ (b :: Mt)
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.cons (b :: Mt)
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.bit0 (b :: Mt)
              · simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, stackActionU_pop_cons,
                  natEnd] using eval_stack_pop_actionU Γ'.bit1 (b :: Mt)
  | halt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_main,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        mainStackU] using eval_stackActionU_short_stack_self_full M

private theorem branchU_ret_rev_exact
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        revStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        revStackCoordU := by
  cases k with
  | cons₁ fs k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU] using eval_stackActionU_short_top_self_full R
  | cons₂ k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU] using eval_stackActionU_short_top_self_full R
  | comp f k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU] using eval_stackActionU_short_top_self_full R
  | fix f k =>
      cases M with
      | nil =>
          simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, revStackU, mainStackU,
            stackPop, stackGet, stackSet, stackActionU_self, natEnd] using
            eval_stackActionU_short_top_self_full R
      | cons a Mt =>
          cases Mt with
          | nil =>
              cases a <;>
                simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  revStackU, mainStackU, stackPop, stackGet, stackSet,
                  stackActionU_self, natEnd] using
                  eval_stackActionU_short_top_self_full R
          | cons b Mt =>
              cases a <;> cases b <;>
                simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  revStackU, mainStackU, stackPop, stackGet, stackSet,
                  stackActionU_self, natEnd] using
                  eval_stackActionU_short_top_self_full R
  | halt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_rev,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        revStackU] using eval_stackActionU_short_top_self_full R

private theorem branchU_ret_aux_exact
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        auxStackCoordU := by
  cases k with
  | cons₁ fs k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        auxStackU] using eval_stackActionU_short_top_self_full A
  | cons₂ k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        auxStackU] using eval_stackActionU_short_top_self_full A
  | comp f k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        auxStackU] using eval_stackActionU_short_top_self_full A
  | fix f k =>
      cases M with
      | nil =>
          simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, auxStackU, mainStackU,
            stackPop, stackGet, stackSet, stackActionU_self, natEnd] using
            eval_stackActionU_short_top_self_full A
      | cons a Mt =>
          cases Mt with
          | nil =>
              cases a <;>
                simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  auxStackU, mainStackU, stackPop, stackGet, stackSet,
                  stackActionU_self, natEnd] using
                  eval_stackActionU_short_top_self_full A
          | cons b Mt =>
              cases a <;> cases b <;>
                simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  auxStackU, mainStackU, stackPop, stackGet, stackSet,
                  stackActionU_self, natEnd] using
                  eval_stackActionU_short_top_self_full A
  | halt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_aux,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        auxStackU] using eval_stackActionU_short_top_self_full A

private theorem branchU_ret_data_exact
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU =
      confEncU
        (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        dataStackCoordU := by
  cases k with
  | cons₁ fs k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        dataStackU] using eval_stackActionU_short_top_self_full D
  | cons₂ k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        dataStackU] using eval_stackActionU_short_top_self_full D
  | comp f k =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        dataStackU] using eval_stackActionU_short_top_self_full D
  | fix f k =>
      cases M with
      | nil =>
          simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, dataStackU, mainStackU,
            stackPop, stackGet, stackSet, stackActionU_self, natEnd] using
            eval_stackActionU_short_top_self_full D
      | cons a Mt =>
          cases Mt with
          | nil =>
              cases a <;>
                simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  dataStackU, mainStackU, stackPop, stackGet, stackSet,
                  stackActionU_self, natEnd] using
                  eval_stackActionU_short_top_self_full D
          | cons b Mt =>
              cases a <;> cases b <;>
                simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  dataStackU, mainStackU, stackPop, stackGet, stackSet,
                  stackActionU_self, natEnd] using
                  eval_stackActionU_short_top_self_full D
  | halt =>
      simpa [BranchData.evalBranchQ, branchU, branchActionForCoordU_data,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        dataStackU] using eval_stackActionU_short_top_self_full D

private theorem branchU_ret_ctrl_exact
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU =
      confEncU
        (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        ctrlCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))) ctrlCoordU)
      (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) ctrlCoordU) =
    confEncU (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))) ctrlCoordU
  rw [branchActionForCoordU_ctrl]
  cases k with
  | cons₁ fs k =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU]
  | cons₂ k =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU]
  | comp f k =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU]
  | fix f k =>
      cases M with
      | nil =>
          simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
            stackGet, stackSet, confEncU, mainStackCoordU, revStackCoordU,
            auxStackCoordU, dataStackCoordU, ctrlCoordU, natEnd]
      | cons a Mt =>
          cases Mt with
          | nil =>
              cases a <;>
                simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, confEncU,
                  mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
                  ctrlCoordU, natEnd]
          | cons b Mt =>
              cases a <;> cases b <;>
                simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, confEncU,
                  mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
                  ctrlCoordU, natEnd]
  | halt =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU]

private theorem branchU_ret_halt_exact
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchData.evalBranchQ
        (branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))))
        (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        haltCoordU =
      confEncU
        (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))
        haltCoordU := by
  change BranchAction.evalQ B_U
      (branchActionForCoordU
        (localViewU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))) haltCoordU)
      (confEncU (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) haltCoordU) =
    confEncU (finStep (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))) haltCoordU
  rw [branchActionForCoordU_halt]
  cases k with
  | cons₁ fs k =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU, haltCoordU, haltFlagU, finHalted]
  | cons₂ k =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU, haltCoordU, haltFlagU, finHalted]
  | comp f k =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU, haltCoordU, haltFlagU, finHalted]
  | fix f k =>
      cases M with
      | nil =>
          simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
            localViewU, localViewConfU, shortStackU, stackTopU, stackSecondU,
            finStep_eq_finStepBranch_U, finStepBranch, mainStackU, stackPop,
            stackGet, stackSet, confEncU, mainStackCoordU, revStackCoordU,
            auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU, haltFlagU,
            finHalted, natEnd]
      | cons a Mt =>
          cases Mt with
          | nil =>
              cases a <;>
                simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, confEncU,
                  mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
                  ctrlCoordU, haltCoordU, haltFlagU, finHalted, natEnd]
          | cons b Mt =>
              cases a <;> cases b <;>
                simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
                  localViewU, localViewConfU, shortStackU, stackTopU,
                  stackSecondU, finStep_eq_finStepBranch_U, finStepBranch,
                  mainStackU, stackPop, stackGet, stackSet, confEncU,
                  mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
                  ctrlCoordU, haltCoordU, haltFlagU, finHalted, natEnd]
  | halt =>
      simp [BranchAction.evalQ, BranchAction.const, BranchAction.affine,
        localViewU, localViewConfU, finStep_eq_finStepBranch_U, finStepBranch,
        confEncU, mainStackCoordU, revStackCoordU, auxStackCoordU, dataStackCoordU,
        ctrlCoordU, haltCoordU, haltFlagU, finHalted]

private theorem branchU_clause_ret_exact_next
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchData.evalBranch
          (branchU (localViewU
            (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))))
          (stackMachineEncodingU.enc
            (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))) i =
        stackMachineEncodingU.enc
          (M_U.step (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))) i := by
  intro i
  fin_cases i
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_ret_main_exact k hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_ret_rev_exact k hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_ret_aux_exact k hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U] using congrArg (fun z : ℚ => (z : ℝ))
      (branchU_ret_data_exact k hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_ret_ctrl_exact k hmem v M R A D)
  · simpa [stackMachineEncodingU, M_U, confEncU, mainStackCoordU, revStackCoordU,
      auxStackCoordU, dataStackCoordU, ctrlCoordU, haltCoordU] using
      congrArg (fun z : ℚ => (z : ℝ)) (branchU_ret_halt_exact k hmem v M R A D)

private theorem branchU_clause_ret_multiplier_le
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    ∀ i,
      BranchAction.multiplier B_U
          ((branchU (localViewU
            (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))).action i) ≤
        stackMachineEncodingU.coordMultiplier
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) i := by
  intro i
  fin_cases i
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))).action
          mainStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) mainStackCoordU
    cases k with
    | cons₁ fs k =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, mainStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | cons₂ k =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, mainStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | comp f k =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, mainStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | fix f k =>
        cases M with
        | nil =>
            simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
              shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
              finStepBranch, stackMachineEncodingU,
              StackMachineEncoding.coordMultiplier,
              StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
              moveTypeStackU, indexedStackU, stackMoveForListsU_self, mainStackU,
              stackPop, stackGet, stackSet, stackActionU_self,
              BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
              StackMove.delta, B_U, natEnd]
        | cons a Mt =>
            cases Mt with
            | nil =>
                cases a <;>
                  simp [branchU, branchActionForCoordU_main, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU,
                    stackMoveForListsU_pop, stackMoveForListsU_self, mainStackU,
                    stackPop, stackGet, stackSet, stackActionU,
                    stackActionU_self, stackActionU_pop_cons,
                    BranchAction.multiplier, BranchAction.stay, BranchAction.pop,
                    BranchAction.const, BranchAction.affine, StackMove.delta, B_U,
                    natEnd, list_ne_cons_cons_self]
            | cons b Mt =>
                cases a <;> cases b <;>
                  simp [branchU, branchActionForCoordU_main, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU,
                    stackMoveForListsU_pop, stackMoveForListsU_self, mainStackU,
                    stackPop, stackGet, stackSet, stackActionU,
                    stackActionU_self, stackActionU_pop_cons,
                    BranchAction.multiplier, BranchAction.stay, BranchAction.pop,
                    BranchAction.const, BranchAction.affine, StackMove.delta, B_U,
                    natEnd, list_ne_cons_cons_self]
    | halt =>
        simp [branchU, branchActionForCoordU_main, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, mainStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))).action
          revStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) revStackCoordU
    cases k with
    | cons₁ fs k =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, revStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | cons₂ k =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, revStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | comp f k =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, revStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | fix f k =>
        cases M with
        | nil =>
            simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
              shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
              finStepBranch, stackMachineEncodingU,
              StackMachineEncoding.coordMultiplier,
              StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
              moveTypeStackU, indexedStackU, stackMoveForListsU_self, revStackU,
              mainStackU, stackPop, stackGet, stackSet, stackActionU_self,
              BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
              StackMove.delta, B_U, natEnd]
        | cons a Mt =>
            cases Mt with
            | nil =>
                cases a <;>
                  simp [branchU, branchActionForCoordU_rev, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                    revStackU, mainStackU, stackPop, stackGet, stackSet,
                    stackActionU_self, BranchAction.multiplier, BranchAction.stay,
                    BranchAction.affine, StackMove.delta, B_U, natEnd]
            | cons b Mt =>
                cases a <;> cases b <;>
                  simp [branchU, branchActionForCoordU_rev, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                    revStackU, mainStackU, stackPop, stackGet, stackSet,
                    stackActionU_self, BranchAction.multiplier, BranchAction.stay,
                    BranchAction.affine, StackMove.delta, B_U, natEnd]
    | halt =>
        simp [branchU, branchActionForCoordU_rev, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, revStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))).action
          auxStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) auxStackCoordU
    cases k with
    | cons₁ fs k =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, auxStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | cons₂ k =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, auxStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | comp f k =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, auxStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | fix f k =>
        cases M with
        | nil =>
            simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
              shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
              finStepBranch, stackMachineEncodingU,
              StackMachineEncoding.coordMultiplier,
              StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
              moveTypeStackU, indexedStackU, stackMoveForListsU_self, auxStackU,
              mainStackU, stackPop, stackGet, stackSet, stackActionU_self,
              BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
              StackMove.delta, B_U, natEnd]
        | cons a Mt =>
            cases Mt with
            | nil =>
                cases a <;>
                  simp [branchU, branchActionForCoordU_aux, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                    auxStackU, mainStackU, stackPop, stackGet, stackSet,
                    stackActionU_self, BranchAction.multiplier, BranchAction.stay,
                    BranchAction.affine, StackMove.delta, B_U, natEnd]
            | cons b Mt =>
                cases a <;> cases b <;>
                  simp [branchU, branchActionForCoordU_aux, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                    auxStackU, mainStackU, stackPop, stackGet, stackSet,
                    stackActionU_self, BranchAction.multiplier, BranchAction.stay,
                    BranchAction.affine, StackMove.delta, B_U, natEnd]
    | halt =>
        simp [branchU, branchActionForCoordU_aux, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, auxStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
  · change BranchAction.multiplier B_U
        ((branchU (localViewU
          (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))).action
          dataStackCoordU) ≤
      stackMachineEncodingU.coordMultiplier
        (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) dataStackCoordU
    cases k with
    | cons₁ fs k =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, dataStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | cons₂ k =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, dataStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | comp f k =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, dataStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
    | fix f k =>
        cases M with
        | nil =>
            simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
              shortStackU, stackTopU, stackSecondU, finStep_eq_finStepBranch_U,
              finStepBranch, stackMachineEncodingU,
              StackMachineEncoding.coordMultiplier,
              StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
              moveTypeStackU, indexedStackU, stackMoveForListsU_self, dataStackU,
              mainStackU, stackPop, stackGet, stackSet, stackActionU_self,
              BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
              StackMove.delta, B_U, natEnd]
        | cons a Mt =>
            cases Mt with
            | nil =>
                cases a <;>
                  simp [branchU, branchActionForCoordU_data, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                    dataStackU, mainStackU, stackPop, stackGet, stackSet,
                    stackActionU_self, BranchAction.multiplier, BranchAction.stay,
                    BranchAction.affine, StackMove.delta, B_U, natEnd]
            | cons b Mt =>
                cases a <;> cases b <;>
                  simp [branchU, branchActionForCoordU_data, localViewU,
                    localViewConfU, shortStackU, stackTopU, stackSecondU,
                    finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
                    StackMachineEncoding.coordMultiplier,
                    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta,
                    moveTypeStackU, indexedStackU, stackMoveForListsU_self,
                    dataStackU, mainStackU, stackPop, stackGet, stackSet,
                    stackActionU_self, BranchAction.multiplier, BranchAction.stay,
                    BranchAction.affine, StackMove.delta, B_U, natEnd]
    | halt =>
        simp [branchU, branchActionForCoordU_data, localViewU, localViewConfU,
          finStep_eq_finStepBranch_U, finStepBranch, stackMachineEncodingU,
          StackMachineEncoding.coordMultiplier, StackMachineEncoding.stackMultiplier,
          StackMachineEncoding.stackDelta, moveTypeStackU, indexedStackU,
          stackMoveForListsU_self, dataStackU, stackActionU_self,
          BranchAction.multiplier, BranchAction.stay, BranchAction.affine,
          StackMove.delta, B_U]
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) ctrlCoordU (Or.inl rfl)
  · exact branchU_reset_multiplier_le
      (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)) haltCoordU (Or.inr rfl)

private theorem branchU_clause_ret
    (k : Cont') (hmem : Λ'.ret k ∈ supportSet c_f)
    (v : Option Γ') (M R A D : List Γ') :
    BranchContractClause stackMachineEncodingU
      (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D))
      (branchU (localViewU
        (some ⟨Λ'.ret k, hmem⟩, v, (M, R, A, D)))) := by
  constructor
  · exact branchU_clause_ret_exact_next k hmem v M R A D
  · exact branchU_clause_ret_multiplier_le k hmem v M R A D

theorem branchU_contract_clause (c : UConf) :
    BranchContractClause stackMachineEncodingU c (branchU (localViewU c)) := by
  rcases c with ⟨ol, v, M, R, A, D⟩
  cases ol with
  | none =>
      exact branchU_clause_none v M R A D
  | some l =>
      rcases l with ⟨lv, hmem⟩
      cases lv with
      | move p k₁ k₂ q =>
          exact branchU_clause_move p k₁ k₂ q hmem v M R A D
      | clear p k q =>
          exact branchU_clause_clear p k q hmem v M R A D
      | copy q =>
          exact branchU_clause_copy q hmem v M R A D
      | push k f q =>
          exact branchU_clause_push k f q hmem v M R A D
      | read q =>
          exact branchU_clause_read q hmem v M R A D
      | succ q =>
          exact branchU_clause_succ q hmem v M R A D
      | pred q₁ q₂ =>
          exact branchU_clause_pred q₁ q₂ hmem v M R A D
      | ret k =>
          exact branchU_clause_ret k hmem v M R A D

/--
The universal machine's branch-contract clause: the selected affine branch
`branchU (localViewU c)` computes the discrete step exactly (`exact_next`) and
respects the per-coordinate amplifier budget (`multiplier_le`).  This is the
hypothesis `hbranch` carried by `robustStepContractU`; here it is discharged
from the per-instruction case analysis assembled in `branchU_contract_clause`.
-/
theorem branchU_branchContractClause (c : UConf) :
    BranchContractClause stackMachineEncodingU c (branchU (localViewU c)) :=
  branchU_contract_clause c

/-! ## Selector and robust-step hooks at dimension six -/

/--
Encode the whole universal local view into the control atom.  The two binary
top atoms are fixed to `none`; this works with the current gate-selector API
while preserving injectivity through `q`.
-/
def universalViewSpec : GateViewSpec UniversalLocalView where
  q := fun v => (((Fintype.equivFin UniversalLocalView) v).val : ℤ)
  leftTop := fun _ => (none : Option (Fin 2))
  rightTop := fun _ => (none : Option (Fin 2))
  ext := by
    intro v w hq _ _
    have hval :
        ((Fintype.equivFin UniversalLocalView) v).val =
          ((Fintype.equivFin UniversalLocalView) w).val := by
      exact_mod_cast hq
    apply (Fintype.equivFin UniversalLocalView).injective
    exact Fin.ext hval

/-- Injective `ℤ` code for a stack-top symbol. -/
def topCodeU (o : Option Γ') : ℤ :=
  (((Fintype.equivFin (Option Γ')) o).val : ℤ)

theorem topCodeU_injective : Function.Injective topCodeU := by
  intro a b h
  unfold topCodeU at h
  exact (Fintype.equivFin (Option Γ')).injective (Fin.ext (by exact_mod_cast h))

/-- Injective `ℤ` code for the `(mainTop, mainSecond)` pair on the main stack. -/
def mainPairCodeU (t s : Option Γ') : ℤ :=
  (((Fintype.equivFin (Option Γ' × Option Γ')) (t, s)).val : ℤ)

theorem mainPairCodeU_injective :
    Function.Injective (fun p : Option Γ' × Option Γ' => mainPairCodeU p.1 p.2) := by
  intro p p' h
  rcases p with ⟨t, s⟩
  rcases p' with ⟨t', s'⟩
  simp only [mainPairCodeU] at h
  exact (Fintype.equivFin (Option Γ' × Option Γ')).injective
    (Fin.ext (by exact_mod_cast h))


/-! ### Main-stack (top, second) pair geometry -/

/-- Left endpoint scaled by `B^3` (integer, kernel-friendly for `decide`). -/
def mainPairLoN : Option Γ' × Option Γ' → ℕ
  | (none, none) => bot B_U * B_U ^ 2
  | (none, some b) => (10 + gammaDigit b) * B_U ^ 3
  | (some a, none) => gammaDigit a * B_U ^ 2 + bot B_U * B_U
  | (some a, some b) => gammaDigit a * B_U ^ 2 + gammaDigit b * B_U

/-- Right endpoint scaled by `B^3`. -/
def mainPairHiN : Option Γ' × Option Γ' → ℕ
  | (none, none) => bot B_U * B_U ^ 2
  | (none, some b) => (10 + gammaDigit b) * B_U ^ 3
  | (some a, none) => gammaDigit a * B_U ^ 2 + bot B_U * B_U
  | (some a, some b) => gammaDigit a * B_U ^ 2 + gammaDigit b * B_U + bot B_U

/-- Left endpoint of the pair interval (rational). -/
def mainPairLoQ (p : Option Γ' × Option Γ') : ℚ := (mainPairLoN p : ℚ) / (B_U : ℚ) ^ 3

/-- Right endpoint of the pair interval (rational). -/
def mainPairHiQ (p : Option Γ' × Option Γ') : ℚ := (mainPairHiN p : ℚ) / (B_U : ℚ) ^ 3

/-- Pair-interval separation gap (one place-value level below the top gap). -/
def mainPairGapQ : ℚ := 2 / (B_U : ℚ) ^ 3

/-- Integer-scaled separation, proved by `decide` over `ℕ`. -/
theorem mainPair_sepN :
    ∀ p q : Option Γ' × Option Γ', p ≠ q →
      mainPairHiN p + 2 ≤ mainPairLoN q ∨ mainPairHiN q + 2 ≤ mainPairLoN p := by
  decide

/-- Distinct pair intervals are `mainPairGapQ`-separated. -/
theorem mainPair_sepQ (p q : Option Γ' × Option Γ') (h : p ≠ q) :
    mainPairHiQ p + mainPairGapQ ≤ mainPairLoQ q ∨
      mainPairHiQ q + mainPairGapQ ≤ mainPairLoQ p := by
  have hB3 : (0 : ℚ) < (B_U : ℚ) ^ 3 := by norm_num [B_U]
  rcases mainPair_sepN p q h with hk | hk
  · left
    have hle : (mainPairHiN p : ℚ) + 2 ≤ (mainPairLoN q : ℚ) := by exact_mod_cast hk
    unfold mainPairHiQ mainPairLoQ mainPairGapQ
    rw [← add_div]
    gcongr
  · right
    have hle : (mainPairHiN q : ℚ) + 2 ≤ (mainPairLoN p : ℚ) := by exact_mod_cast hk
    unfold mainPairHiQ mainPairLoQ mainPairGapQ
    rw [← add_div]
    gcongr

/-! ### Concrete stack-top interval atoms (rev / aux / data) -/

/-- Interval-atom specification for a stack-top coordinate (symbols `Option Γ'`). -/
noncomputable def stackTopAtomSpec (coord : Fin d_U) (eta : ℚ) (heta : 0 < eta) :
    IntervalAtomSpec d_U (Option Γ') where
  coord := coord
  C := 1
  C_pos := by norm_num
  lo := fun o => topLoU o - r_LE_U
  hi := fun o => topHiU o + r_LE_U
  gap := topGapU - 2 * r_LE_U
  gap_pos := by norm_num [topGapU, B_U, r_LE_U]
  sep := by
    intro o o' h
    have hr := r_LE_U_pos
    rcases topInterval_sep o o' h with hk | hk
    · left; linarith
    · right; linarith
  eta := eta
  eta_pos := heta

/-- The ℤ-coded stack-top atom, relabeled along `topCodeU`. -/
noncomputable def stackTopAtom (coord : Fin d_U) (eta : ℚ) (heta : 0 < eta) :
    CoordAtomData d_U ℤ :=
  ((stackTopAtomSpec coord eta heta).toCoordAtomData).relabel topCodeU topCodeU_injective

/-- The main stack code lies in the interval of its `(top, second)` pair. -/
theorem stackCodeU_mem_mainPairInterval (L : List Γ') :
    (mainPairLoQ (stackTopU L, stackSecondU L) : ℝ) ≤
        ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ∧
      ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ≤
        (mainPairHiQ (stackTopU L, stackSecondU L) : ℝ) := by
  have hBne : (B_U : ℝ) ≠ 0 := by norm_num [B_U]
  have hb : ((bot B_U : ℕ) : ℝ) = 4 := by norm_num [bot, B_U]
  have hB6 : (B_U : ℝ) = 6 := by norm_num [B_U]
  cases L with
  | nil =>
      simp only [stackTopU, stackSecondU]
      rw [stackCodeU_nil]
      refine ⟨le_of_eq ?_, le_of_eq ?_⟩ <;>
        · simp only [mainPairLoQ, mainPairHiQ, mainPairLoN, mainPairHiN]
          push_cast
          rw [hb, hB6]; norm_num
  | cons a T =>
      cases T with
      | nil =>
          have hval : ((stackCodeU B_U gammaDigit [a] : ℚ) : ℝ) =
              ((gammaDigit a : ℝ) + ((bot B_U : ℕ) : ℝ) / (B_U : ℝ)) / (B_U : ℝ) := by
            rw [show [a] = a :: ([] : List Γ') from rfl, stackCodeU_push, stackCodeU_nil]
            push_cast; ring
          simp only [stackTopU, stackSecondU]
          rw [hval]
          refine ⟨le_of_eq ?_, le_of_eq ?_⟩ <;>
            · simp only [mainPairLoQ, mainPairHiQ, mainPairLoN, mainPairHiN]
              push_cast
              rw [hb, hB6]; field_simp <;> ring
      | cons b R =>
          have hgap := stackCodeU_mem_gap_range R
          have hr0 : (0 : ℝ) < ((stackCodeU B_U gammaDigit R : ℚ) : ℝ) := by
            exact_mod_cast hgap.1
          have hrle : ((stackCodeU B_U gammaDigit R : ℚ) : ℝ) ≤
              ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) := by
            calc ((stackCodeU B_U gammaDigit R : ℚ) : ℝ)
                ≤ (((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℚ) : ℝ) := by exact_mod_cast hgap.2.1
              _ = ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) := by push_cast; ring
          have hval : ((stackCodeU B_U gammaDigit (a :: b :: R) : ℚ) : ℝ) =
              (gammaDigit a : ℝ) / (B_U : ℝ) + (gammaDigit b : ℝ) / (B_U : ℝ) ^ 2 +
                ((stackCodeU B_U gammaDigit R : ℚ) : ℝ) / (B_U : ℝ) ^ 2 := by
            rw [stackCodeU_push, stackCodeU_push]
            push_cast; field_simp <;> ring
          have hlo : (mainPairLoQ (stackTopU (a :: b :: R),
              stackSecondU (a :: b :: R)) : ℝ) =
              (gammaDigit a : ℝ) / (B_U : ℝ) + (gammaDigit b : ℝ) / (B_U : ℝ) ^ 2 := by
            simp only [stackTopU, stackSecondU, mainPairLoQ, mainPairLoN]
            push_cast; field_simp <;> ring
          have hhi : (mainPairHiQ (stackTopU (a :: b :: R),
              stackSecondU (a :: b :: R)) : ℝ) =
              (gammaDigit a : ℝ) / (B_U : ℝ) + (gammaDigit b : ℝ) / (B_U : ℝ) ^ 2 +
                ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) ^ 3 := by
            simp only [stackTopU, stackSecondU, mainPairHiQ, mainPairHiN]
            push_cast; field_simp <;> ring
          rw [hval, hlo, hhi]
          have hsq : (0 : ℝ) < (B_U : ℝ) ^ 2 := by positivity
          refine ⟨?_, ?_⟩
          · have hnn : (0 : ℝ) ≤ ((stackCodeU B_U gammaDigit R : ℚ) : ℝ) / (B_U : ℝ) ^ 2 := by
              positivity
            linarith
          · have hkey : ((stackCodeU B_U gammaDigit R : ℚ) : ℝ) / (B_U : ℝ) ^ 2 ≤
                ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) ^ 3 := by
              have he : ((bot B_U : ℕ) : ℝ) / (B_U : ℝ) ^ 3 =
                  (((bot B_U : ℕ) : ℝ) / (B_U : ℝ)) / (B_U : ℝ) ^ 2 := by
                field_simp <;> ring
              rw [he]; gcongr
            linarith

/-! ### Concrete main-stack (top, second) pair atom -/

/-- Interval-atom specification for the main stack `(top, second)` pair. -/
noncomputable def mainPairAtomSpec (eta : ℚ) (heta : 0 < eta) :
    IntervalAtomSpec d_U (Option Γ' × Option Γ') where
  coord := mainStackCoordU
  C := 1
  C_pos := by norm_num
  lo := fun p => (mainPairLoQ p : ℝ) - r_LE_U
  hi := fun p => (mainPairHiQ p : ℝ) + r_LE_U
  gap := (mainPairGapQ : ℝ) - 2 * r_LE_U
  gap_pos := by norm_num [mainPairGapQ, B_U, r_LE_U]
  sep := by
    intro p q hpq
    have hr := r_LE_U_pos
    rcases mainPair_sepQ p q hpq with h | h
    · left; have h' : (mainPairHiQ p : ℝ) + (mainPairGapQ : ℝ) ≤ (mainPairLoQ q : ℝ) := by exact_mod_cast h
      linarith
    · right; have h' : (mainPairHiQ q : ℝ) + (mainPairGapQ : ℝ) ≤ (mainPairLoQ p : ℝ) := by exact_mod_cast h
      linarith
  eta := eta
  eta_pos := heta

/-- The ℤ-coded main-pair atom, relabeled along `mainPairCodeU`. -/
noncomputable def mainPairAtom (eta : ℚ) (heta : 0 < eta) : CoordAtomData d_U ℤ :=
  ((mainPairAtomSpec eta heta).toCoordAtomData).relabel
    (fun p => mainPairCodeU p.1 p.2) mainPairCodeU_injective

/-! ### Five-atom universal gate family and its sharpness -/

/-- The five universal gate atoms: control, main `(top,second)` pair, and the
`rev`, `aux`, `data` stack tops. -/
noncomputable def universalGateAtoms (eta : ℚ) (heta : 0 < eta) :
    Fin 5 → CoordAtomData d_U ℤ :=
  ![controlAtom eta heta,
    mainPairAtom eta heta,
    stackTopAtom revStackCoordU eta heta,
    stackTopAtom auxStackCoordU eta heta,
    stackTopAtom dataStackCoordU eta heta]

/-- Tube fact: at a tube point the control coordinate is within `1/4` of the
true control code. -/
theorem ctrl_tube_close {c : UConf} {x : Fin d_U → ℝ} (htube : UTube r_LE_U c x) :
    |x ctrlCoordU - (ctrlVarCodeU c.1 c.2.1 : ℝ)| ≤ (1 / 4 : ℝ) := by
  have h := htube ctrlCoordU
  rw [confEncU_ctrl] at h
  have hr : r_LE_U ≤ (1 / 4 : ℝ) := by norm_num [r_LE_U]
  have : |x ctrlCoordU - (ctrlVarCodeU c.1 c.2.1 : ℝ)| ≤ r_LE_U := by
    have hcast : (((ctrlVarCodeU c.1 c.2.1 : ℤ) : ℚ) : ℝ) = (ctrlVarCodeU c.1 c.2.1 : ℝ) := by
      push_cast; ring
    rwa [hcast] at h
  linarith

/-- Tube fact: at a tube point a stack coordinate holding `L` lands in the
widened top interval of `L`'s top symbol. -/
theorem stackTop_tube_widened {c : UConf} {x : Fin d_U → ℝ} (htube : UTube r_LE_U c x)
    {coord : Fin d_U} {L : List Γ'}
    (hcoord : confEncU c coord = (stackCodeU B_U gammaDigit L : ℚ)) :
    topLoU (stackTopU L) - r_LE_U ≤ x coord ∧
      x coord ≤ topHiU (stackTopU L) + r_LE_U := by
  have h := htube coord
  rw [hcoord] at h
  have hmem := stackCodeU_mem_topInterval L
  have habs := abs_le.mp h
  exact ⟨by linarith [hmem.1, habs.1], by linarith [hmem.2, habs.2]⟩

/-- Tube fact: the main coordinate lands in the widened pair interval. -/
theorem mainPair_tube_widened {c : UConf} {x : Fin d_U → ℝ} (htube : UTube r_LE_U c x) :
    (mainPairLoQ (stackTopU (mainStackU c), stackSecondU (mainStackU c)) : ℝ) - r_LE_U ≤
        x mainStackCoordU ∧
      x mainStackCoordU ≤
        (mainPairHiQ (stackTopU (mainStackU c), stackSecondU (mainStackU c)) : ℝ) + r_LE_U := by
  have h := htube mainStackCoordU
  rw [confEncU_main] at h
  have hmem := stackCodeU_mem_mainPairInterval (mainStackU c)
  have habs := abs_le.mp h
  exact ⟨by linarith [hmem.1, habs.1], by linarith [hmem.2, habs.2]⟩

/-- Working-domain discharge for the five-atom universal gate family. -/
theorem universalGateAtoms_inWorkingDomain (eta : ℚ) (heta : 0 < eta)
    {c : UConf} {x : Fin d_U → ℝ} (htube : UTube r_LE_U c x) :
    (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).inWorkingDomain x := by
  have hstack : ∀ (coord : Fin d_U) (L : List Γ'),
      confEncU c coord = (stackCodeU B_U gammaDigit L : ℚ) →
        |x coord| ≤ ((1 : ℚ) : ℝ) := by
    intro coord L hcoord
    have h := htube coord
    rw [hcoord] at h
    have hg := stackCodeU_mem_gap_range L
    have hle : ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ≤ 2 / 3 := by
      have hh := hg.2.1
      have h23 : ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) = 2 / 3 := by
        norm_num [bot, B_U]
      calc ((stackCodeU B_U gammaDigit L : ℚ) : ℝ)
          ≤ ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) := by exact_mod_cast hh
        _ = 2 / 3 := h23
    have hpos : (0 : ℝ) ≤ ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) := by
      exact_mod_cast hg.1.le
    have hrle : r_LE_U ≤ 1 / 3 := by norm_num [r_LE_U]
    obtain ⟨habs1, habs2⟩ := abs_le.mp h
    rw [abs_le]
    push_cast
    constructor <;> linarith
  intro k
  fin_cases k
  · -- control: |x ctrlCoordU| ≤ (2*card+1)
    show |x ctrlCoordU| ≤
        ((2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ')) + 1 : ℚ) : ℝ)
    have h := htube ctrlCoordU
    rw [confEncU_ctrl] at h
    have hidx :
        ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (c.1, c.2.1)).val <
          Fintype.card (Option (SuppLabel c_f) × Option Γ') :=
      (Fintype.equivFin (Option (SuppLabel c_f) × Option Γ') (c.1, c.2.1)).isLt
    have hcle : (ctrlVarCodeU c.1 c.2.1 : ℝ) ≤
        2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
      unfold ctrlVarCodeU
      push_cast
      have : (((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (c.1, c.2.1)).val : ℝ) ≤
          (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by exact_mod_cast hidx.le
      linarith
    have hcnn : (0 : ℝ) ≤ (ctrlVarCodeU c.1 c.2.1 : ℝ) := by
      unfold ctrlVarCodeU; positivity
    have hrle : r_LE_U ≤ 1 := by norm_num [r_LE_U]
    obtain ⟨habs1, habs2⟩ := abs_le.mp h
    rw [abs_le]
    push_cast
    push_cast at habs1 habs2
    constructor <;> linarith
  · exact hstack mainStackCoordU (mainStackU c) (confEncU_main c)
  · exact hstack revStackCoordU (revStackU c) (confEncU_rev c)
  · exact hstack auxStackCoordU (auxStackU c) (confEncU_aux c)
  · exact hstack dataStackCoordU (dataStackU c) (confEncU_data c)

/-! ### Five-component N-atom view specification -/

/--
Five-component universal view specification.  Component `0` is the packed
control code `(label, var)`; component `1` is the `(mainTop, mainSecond)` pair
on the main stack (read via the multiplied-tail tube); components `2,3,4` are
the `rev`, `aux`, `data` stack tops.  Together they pin down all seven view
fields, so the view is recoverable (`ext`).
-/
def universalViewSpecN : GateViewSpecN UniversalLocalView 5 where
  comp := fun k v =>
    if k = 0 then ctrlVarCodeU v.label v.var
    else if k = 1 then mainPairCodeU v.mainTop v.mainSecond
    else if k = 2 then topCodeU v.revTop
    else if k = 3 then topCodeU v.auxTop
    else topCodeU v.dataTop
  ext := by
    intro v w hcomp
    have h0 : ctrlVarCodeU v.label v.var = ctrlVarCodeU w.label w.var := hcomp 0
    have h1 : mainPairCodeU v.mainTop v.mainSecond =
        mainPairCodeU w.mainTop w.mainSecond := hcomp 1
    have h2 : topCodeU v.revTop = topCodeU w.revTop := hcomp 2
    have h3 : topCodeU v.auxTop = topCodeU w.auxTop := hcomp 3
    have h4 : topCodeU v.dataTop = topCodeU w.dataTop := hcomp 4
    have hcv : (v.label, v.var) = (w.label, w.var) := ctrlVarCodeU_injective h0
    have hms : (v.mainTop, v.mainSecond) = (w.mainTop, w.mainSecond) :=
      mainPairCodeU_injective h1
    have hlabel : v.label = w.label := congrArg Prod.fst hcv
    have hvar : v.var = w.var := congrArg Prod.snd hcv
    have hmt : v.mainTop = w.mainTop := congrArg Prod.fst hms
    have hms2 : v.mainSecond = w.mainSecond := congrArg Prod.snd hms
    have hrev : v.revTop = w.revTop := topCodeU_injective h2
    have haux : v.auxTop = w.auxTop := topCodeU_injective h3
    have hdat : v.dataTop = w.dataTop := topCodeU_injective h4
    calc v = ⟨v.label, v.var, v.mainTop, v.mainSecond, v.revTop, v.auxTop, v.dataTop⟩ := by
            cases v; rfl
      _ = ⟨w.label, w.var, w.mainTop, w.mainSecond, w.revTop, w.auxTop, w.dataTop⟩ := by
            rw [hlabel, hvar, hmt, hms2, hrev, haux, hdat]
      _ = w := by cases w; rfl

/-- Sharpness discharge for the five-atom universal gate family at a tube point. -/
theorem universalGateAtoms_sharpness (eta : ℚ) (heta : 0 < eta)
    {c : UConf} {x : Fin d_U → ℝ} (htube : UTube r_LE_U c x) :
    GateAtomSharpnessN universalViewSpecN
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) x (localViewU c) := by
  apply gateAtomSharpnessN_of_coord_atoms
  · exact universalGateAtoms_inWorkingDomain eta heta htube
  · intro k
    fin_cases k
    · refine ⟨(c.1, c.2.1), ?_, ?_⟩
      · rfl
      · simpa [SlabAtomicSelectorData.toCoordAtomData, controlAtomSlab,
          finiteCoordinateAtoms] using ctrl_tube_close htube
    · refine ⟨(stackTopU (mainStackU c), stackSecondU (mainStackU c)), ?_, ?_⟩
      · rfl
      · exact mainPair_tube_widened htube
    · refine ⟨stackTopU (revStackU c), ?_, ?_⟩
      · rfl
      · exact stackTop_tube_widened htube (confEncU_rev c)
    · refine ⟨stackTopU (auxStackU c), ?_, ?_⟩
      · rfl
      · exact stackTop_tube_widened htube (confEncU_aux c)
    · refine ⟨stackTopU (dataStackU c), ?_, ?_⟩
      · rfl
      · exact stackTop_tube_widened htube (confEncU_data c)

/-- Selector-polynomial field for the universal-machine view family. -/
def selectorTotalPolyU
    (branch : UniversalLocalView → BranchData d_U B_U)
    (atoms : GateSelectorAtoms d_U) (i : Fin d_U) : Poly4 d_U :=
  selectorTotalPoly branch universalViewSpec atoms i

/-- Evaluated selector field in the `RobustStepContract` function shape. -/
def selectorContractF_U
    (branch : UniversalLocalView → BranchData d_U B_U)
    (atoms : GateSelectorAtoms d_U) :
    ℝ → (Fin d_U → ℝ) → Fin d_U → ℝ :=
  fun _mu x i => evalPoly4 x (selectorTotalPolyU branch atoms i)

@[simp] theorem selectorContractF_U_eval
    (branch : UniversalLocalView → BranchData d_U B_U)
    (atoms : GateSelectorAtoms d_U) (mu : ℝ) (x : Fin d_U → ℝ)
    (i : Fin d_U) :
    selectorContractF_U branch atoms mu x i =
      evalPoly4 x (selectorTotalPolyU branch atoms i) := rfl

/--
Polynomial-side identity connecting the contract field `F` to the rational
selector polynomial along any point.  This is the field-evaluation hook needed
later by `ContractPolynomialFieldPackage`; the Euclidean field package itself
is assembled in later SPEC items.
-/
theorem selectorContractF_U_field_eval_identity
    (branch : UniversalLocalView → BranchData d_U B_U)
    (atoms : GateSelectorAtoms d_U) (mu : ℝ) (x : Fin d_U → ℝ)
    (i : Fin d_U) :
    selectorContractF_U branch atoms mu x i =
      evalPoly4 x (selectorTotalPoly branch universalViewSpec atoms i) := by
  rfl

/-- Gate-selector coordinate clause specialized to the universal d=6 instance. -/
theorem gate_selector_varMu_coord_clause_U
    (branch : UniversalLocalView → BranchData d_U stackMachineEncodingU.k)
    (atoms : GateSelectorAtoms d_U) (Z : Fin d_U → ℝ)
    (c : UConf) (i : Fin d_U)
    {spread theta : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness universalViewSpec atoms Z (localViewU c))
    (htheta :
      selectorEpsTotal (V := UniversalLocalView)
          atoms.errSel atoms.errOff (atoms.errSum UniversalLocalView) spread ≤
        theta)
    (hspread : BranchSpread branch Z (localViewU c) i spread)
    (hcontract :
      BranchContractClause stackMachineEncodingU c (branch (localViewU c))) :
    |evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
        stackMachineEncodingU.enc (M_U.step c) i| ≤
      (stackMachineEncodingU.k : ℝ) ^
          stackMachineEncodingU.coordDelta c i *
        |Z i - stackMachineEncodingU.enc c i| + theta := by
  simpa [M_U, stackMachineEncodingU] using
    gate_selector_varMu_coord_clause
      (E := stackMachineEncodingU)
      branch universalViewSpec atoms Z c (localViewU c) i
      hZ hsharp htheta hspread hcontract

/-- Gate-selector coordinate clause in the `RobustStepContract.diagonal_bound` shape. -/
theorem gate_selector_robust_coord_clause_U
    (branch : UniversalLocalView → BranchData d_U stackMachineEncodingU.k)
    (atoms : GateSelectorAtoms d_U) (Z : Fin d_U → ℝ)
    (c : UConf) (i : Fin d_U)
    {spread theta : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpness universalViewSpec atoms Z (localViewU c))
    (htheta :
      selectorEpsTotal (V := UniversalLocalView)
          atoms.errSel atoms.errOff (atoms.errSum UniversalLocalView) spread ≤
        theta)
    (hspread : BranchSpread branch Z (localViewU c) i spread)
    (hcontract :
      BranchContractClause stackMachineEncodingU c (branch (localViewU c))) :
    |evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
        stackMachineEncodingU.enc (M_U.step c) i| ≤
      stackMachineEncodingU.coordMultiplier c i *
        |Z i - stackMachineEncodingU.enc c i| + theta := by
  classical
  have hsel := gate_selector_reassembly
    (branch := branch) (spec := universalViewSpec) (atoms := atoms)
    (Z := Z) (vstar := localViewU c) (i := i)
    (spread := spread) hZ hsharp hspread
  have hdiag := hcontract.diagonal Z i
  have htri :
      |evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
          stackMachineEncodingU.enc (M_U.step c) i| ≤
        |evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
          BranchData.evalBranch (branch (localViewU c)) Z i| +
        |BranchData.evalBranch (branch (localViewU c)) Z i -
          stackMachineEncodingU.enc (M_U.step c) i| := by
    have hsum :
        evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
            stackMachineEncodingU.enc (M_U.step c) i =
          (evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
            BranchData.evalBranch (branch (localViewU c)) Z i) +
          (BranchData.evalBranch (branch (localViewU c)) Z i -
            stackMachineEncodingU.enc (M_U.step c) i) := by
      ring
    rw [hsum]
    exact abs_add_le _ _
  calc
    |evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
        stackMachineEncodingU.enc (M_U.step c) i|
        ≤ |evalPoly4 Z (selectorTotalPoly branch universalViewSpec atoms i) -
            BranchData.evalBranch (branch (localViewU c)) Z i| +
          |BranchData.evalBranch (branch (localViewU c)) Z i -
            stackMachineEncodingU.enc (M_U.step c) i| := htri
    _ ≤ selectorEpsTotal (V := UniversalLocalView)
            atoms.errSel atoms.errOff (atoms.errSum UniversalLocalView) spread +
          stackMachineEncodingU.coordMultiplier c i *
            |Z i - stackMachineEncodingU.enc c i| := by
        simpa [selectorEpsTotal, M_U] using add_le_add hsel hdiag
    _ ≤ theta +
          stackMachineEncodingU.coordMultiplier c i *
            |Z i - stackMachineEncodingU.enc c i| := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right htheta
            (stackMachineEncodingU.coordMultiplier c i *
              |Z i - stackMachineEncodingU.enc c i|)
    _ = stackMachineEncodingU.coordMultiplier c i *
          |Z i - stackMachineEncodingU.enc c i| + theta := by
        ring

/-! ### N-atom selector field and robust-step contract -/

/-- N-atom selector reassembly polynomial for the universal view family. -/
def selectorTotalPolyN_U
    (branch : UniversalLocalView → BranchData d_U B_U)
    (atoms : GateSelectorAtomsN d_U 5) (i : Fin d_U) : Poly4 d_U :=
  selectorTotalPolyN branch universalViewSpecN atoms i

/-- Evaluated N-atom selector field in the `RobustStepContract` function shape. -/
def selectorContractF_N_U
    (branch : UniversalLocalView → BranchData d_U B_U)
    (atoms : GateSelectorAtomsN d_U 5) :
    ℝ → (Fin d_U → ℝ) → Fin d_U → ℝ :=
  fun _mu x i => evalPoly4 x (selectorTotalPolyN_U branch atoms i)

@[simp] theorem selectorContractF_N_U_eval
    (branch : UniversalLocalView → BranchData d_U B_U)
    (atoms : GateSelectorAtomsN d_U 5) (mu : ℝ) (x : Fin d_U → ℝ) (i : Fin d_U) :
    selectorContractF_N_U branch atoms mu x i =
      evalPoly4 x (selectorTotalPolyN_U branch atoms i) := rfl

/-- N-atom gate-selector coordinate clause in the `diagonal_bound` shape. -/
theorem gate_selector_robust_coord_clause_N_U
    (branch : UniversalLocalView → BranchData d_U stackMachineEncodingU.k)
    (atoms : GateSelectorAtomsN d_U 5) (Z : Fin d_U → ℝ)
    (c : UConf) (i : Fin d_U)
    {spread theta : ℝ}
    (hZ : atoms.inWorkingDomain Z)
    (hsharp : GateAtomSharpnessN universalViewSpecN atoms Z (localViewU c))
    (htheta :
      selectorEpsTotal (V := UniversalLocalView)
          atoms.errSel atoms.errSel (atoms.errSum UniversalLocalView) spread ≤
        theta)
    (hspread : BranchSpread branch Z (localViewU c) i spread)
    (hcontract :
      BranchContractClause stackMachineEncodingU c (branch (localViewU c))) :
    |evalPoly4 Z (selectorTotalPolyN branch universalViewSpecN atoms i) -
        stackMachineEncodingU.enc (M_U.step c) i| ≤
      stackMachineEncodingU.coordMultiplier c i *
        |Z i - stackMachineEncodingU.enc c i| + theta := by
  classical
  have hsel := gate_selector_reassemblyN
    (branch := branch) (spec := universalViewSpecN) (atoms := atoms)
    (Z := Z) (vstar := localViewU c) (i := i)
    (spread := spread) hZ hsharp hspread
  have hdiag := hcontract.diagonal Z i
  have htri :
      |evalPoly4 Z (selectorTotalPolyN branch universalViewSpecN atoms i) -
          stackMachineEncodingU.enc (M_U.step c) i| ≤
        |evalPoly4 Z (selectorTotalPolyN branch universalViewSpecN atoms i) -
          BranchData.evalBranch (branch (localViewU c)) Z i| +
        |BranchData.evalBranch (branch (localViewU c)) Z i -
          stackMachineEncodingU.enc (M_U.step c) i| := by
    have hsum :
        evalPoly4 Z (selectorTotalPolyN branch universalViewSpecN atoms i) -
            stackMachineEncodingU.enc (M_U.step c) i =
          (evalPoly4 Z (selectorTotalPolyN branch universalViewSpecN atoms i) -
            BranchData.evalBranch (branch (localViewU c)) Z i) +
          (BranchData.evalBranch (branch (localViewU c)) Z i -
            stackMachineEncodingU.enc (M_U.step c) i) := by ring
    rw [hsum]
    exact abs_add_le _ _
  calc
    |evalPoly4 Z (selectorTotalPolyN branch universalViewSpecN atoms i) -
        stackMachineEncodingU.enc (M_U.step c) i|
        ≤ |evalPoly4 Z (selectorTotalPolyN branch universalViewSpecN atoms i) -
            BranchData.evalBranch (branch (localViewU c)) Z i| +
          |BranchData.evalBranch (branch (localViewU c)) Z i -
            stackMachineEncodingU.enc (M_U.step c) i| := htri
    _ ≤ selectorEpsTotal (V := UniversalLocalView)
            atoms.errSel atoms.errSel (atoms.errSum UniversalLocalView) spread +
          stackMachineEncodingU.coordMultiplier c i *
            |Z i - stackMachineEncodingU.enc c i| := by
        simpa [selectorEpsTotal, M_U] using add_le_add hsel hdiag
    _ ≤ theta +
          stackMachineEncodingU.coordMultiplier c i *
            |Z i - stackMachineEncodingU.enc c i| := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right htheta
            (stackMachineEncodingU.coordMultiplier c i *
              |Z i - stackMachineEncodingU.enc c i|)
    _ = stackMachineEncodingU.coordMultiplier c i *
          |Z i - stackMachineEncodingU.enc c i| + theta := by ring

/--
Parameterized robust-step contract for the d=6 universal selector field,
N-atom version (5 per-coordinate atoms).  Same shape as `robustStepContractU`
but the sharpness/domain hypotheses are now dischargeable theorems
(`universalGateAtoms_sharpness`, `universalGateAtoms_inWorkingDomain`).
-/
def robustStepContractN_U_withSpread
    (branch : UniversalLocalView → BranchData d_U stackMachineEncodingU.k)
    (atoms : GateSelectorAtomsN d_U 5)
    (epsF : ℝ → Fin d_U → ℝ)
    (spread : ℝ → Fin d_U → ℝ)
    (D : ℝ)
    (hD : 0 ≤ D)
    (hlocal_unique :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          ∀ c' : UConf, UTube r_LE_U c' x → localViewU c' = localViewU c)
    (hsharp :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          GateAtomSharpnessN universalViewSpecN atoms x (localViewU c))
    (hdomain :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          atoms.inWorkingDomain x)
    (hspread :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ} (i : Fin d_U),
        EncodingTube stackMachineEncodingU r_LE_U c x →
          BranchSpread branch x (localViewU c) i (spread mu i))
    (hselector_budget :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ} (i : Fin d_U),
        EncodingTube stackMachineEncodingU r_LE_U c x →
          selectorEpsTotal (V := UniversalLocalView)
              atoms.errSel atoms.errSel (atoms.errSum UniversalLocalView)
              (spread mu i) ≤ epsF mu i)
    (hbranch :
      ∀ c : UConf,
        BranchContractClause stackMachineEncodingU c (branch (localViewU c)))
    (hdisp :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x → ∀ i,
          |selectorContractF_N_U branch atoms mu x i - x i| ≤ D) :
    RobustStepContract M_U stackMachineEncodingU where
  mu_min := 0
  radius := fun _ => r_LE_U
  radius_mono := by intro mu nu _ _; rfl
  radius_pos := by intro mu _; exact r_LE_U_pos
  FiniteData := UniversalLocalView
  finiteDataDecidableEq := inferInstance
  localView := localViewU
  localExtract := localExtractU
  F := selectorContractF_N_U branch atoms
  epsF := epsF
  D := D
  D_nonneg := hD
  local_extract_correct := by
    intro mu c x _ htube
    refine localExtractU_tube ?_ ?_
    · simpa [EncodingTube, stackMachineEncodingU] using htube
    · exact hlocal_unique htube
  diagonal_bound := by
    intro mu c x _ htube i
    have hcoord := gate_selector_robust_coord_clause_N_U
      (branch := branch) (atoms := atoms) (Z := x) (c := c) (i := i)
      (spread := spread mu i) (theta := epsF mu i)
      (hdomain htube)
      (hsharp htube)
      (hselector_budget (mu := mu) i htube)
      (hspread (mu := mu) i htube) (hbranch c)
    simpa [selectorContractF_N_U, selectorTotalPolyN_U, M_U] using hcoord
  displacement_bound := by
    intro mu c x _ htube i
    exact hdisp htube i

/--
Backward-compatible N-atom robust-step contract where the selector target
`epsF` is also used as the branch-spread radius.
-/
def robustStepContractN_U
    (branch : UniversalLocalView → BranchData d_U stackMachineEncodingU.k)
    (atoms : GateSelectorAtomsN d_U 5)
    (epsF : ℝ → Fin d_U → ℝ)
    (D : ℝ)
    (hD : 0 ≤ D)
    (hlocal_unique :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          ∀ c' : UConf, UTube r_LE_U c' x → localViewU c' = localViewU c)
    (hsharp :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          GateAtomSharpnessN universalViewSpecN atoms x (localViewU c))
    (hdomain :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          atoms.inWorkingDomain x)
    (hspread :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ} (i : Fin d_U),
        EncodingTube stackMachineEncodingU r_LE_U c x →
          BranchSpread branch x (localViewU c) i (epsF mu i))
    (hselector_budget :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ} (i : Fin d_U),
        EncodingTube stackMachineEncodingU r_LE_U c x →
          selectorEpsTotal (V := UniversalLocalView)
              atoms.errSel atoms.errSel (atoms.errSum UniversalLocalView)
              (epsF mu i) ≤ epsF mu i)
    (hbranch :
      ∀ c : UConf,
        BranchContractClause stackMachineEncodingU c (branch (localViewU c)))
    (hdisp :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x → ∀ i,
          |selectorContractF_N_U branch atoms mu x i - x i| ≤ D) :
    RobustStepContract M_U stackMachineEncodingU :=
  robustStepContractN_U_withSpread branch atoms epsF epsF D hD
    hlocal_unique hsharp hdomain hspread hselector_budget hbranch hdisp

/--
Parameterized robust-step contract for the d=6 universal selector field.

The remaining hypotheses are exactly the parametric SEL2/analytic obligations:
positive-tube local-view uniqueness, atom sharpness, branch spread, selector
error domination, branch-contract compatibility, and a working displacement
bound.
-/
def robustStepContractU
    (branch : UniversalLocalView → BranchData d_U stackMachineEncodingU.k)
    (atoms : GateSelectorAtoms d_U)
    (epsF : ℝ → Fin d_U → ℝ)
    (D : ℝ)
    (hD : 0 ≤ D)
    (hlocal_unique :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          ∀ c' : UConf, UTube r_LE_U c' x → localViewU c' = localViewU c)
    (hsharp :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          GateAtomSharpness universalViewSpec atoms x (localViewU c))
    (hdomain :
      ∀ {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x →
          atoms.inWorkingDomain x)
    (hspread :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ} (i : Fin d_U),
        EncodingTube stackMachineEncodingU r_LE_U c x →
          BranchSpread branch x (localViewU c) i (epsF mu i))
    (hselector_budget :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ} (i : Fin d_U),
        EncodingTube stackMachineEncodingU r_LE_U c x →
          selectorEpsTotal (V := UniversalLocalView)
              atoms.errSel atoms.errOff (atoms.errSum UniversalLocalView)
              (epsF mu i) ≤ epsF mu i)
    (hbranch :
      ∀ c : UConf,
        BranchContractClause stackMachineEncodingU c (branch (localViewU c)))
    (hdisp :
      ∀ {mu : ℝ} {c : UConf} {x : Fin d_U → ℝ},
        EncodingTube stackMachineEncodingU r_LE_U c x → ∀ i,
          |selectorContractF_U branch atoms mu x i - x i| ≤ D) :
    RobustStepContract M_U stackMachineEncodingU where
  mu_min := 0
  radius := fun _ => r_LE_U
  radius_mono := by
    intro mu nu _ _
    rfl
  radius_pos := by
    intro mu _
    exact r_LE_U_pos
  FiniteData := UniversalLocalView
  finiteDataDecidableEq := inferInstance
  localView := localViewU
  localExtract := localExtractU
  F := selectorContractF_U branch atoms
  epsF := epsF
  D := D
  D_nonneg := hD
  local_extract_correct := by
    intro mu c x _ htube
    refine localExtractU_tube ?_ ?_
    · simpa [EncodingTube, stackMachineEncodingU] using htube
    · exact hlocal_unique htube
  diagonal_bound := by
    intro mu c x _ htube i
    have hcoord := gate_selector_robust_coord_clause_U
      (branch := branch) (atoms := atoms) (Z := x) (c := c) (i := i)
      (spread := epsF mu i) (theta := epsF mu i)
      (hdomain htube)
      (hsharp htube)
      (hselector_budget (mu := mu) i htube)
      (hspread (mu := mu) i htube) (hbranch c)
    simpa [selectorContractF_U, selectorTotalPolyU, M_U] using hcoord
  displacement_bound := by
    intro mu c x _ htube i
    exact hdisp htube i

/-! ## Bounded assembly artifacts -/

/-- Contract readout indicator for the universal halt flag coordinate. -/
def contractFlagIndicatorPackageU :
    ContractFlagIndicatorPackage haltCoordU where
  Hval := fun x => if x haltCoordU < (2 : ℝ)⁻¹ then 0 else 1
  eta := 0
  eta_nonneg := by norm_num
  eta_lt := by norm_num
  in_unit := by
    intro x _
    by_cases h : x haltCoordU < (2 : ℝ)⁻¹
    · simp [h]
    · simp [h]
  on_flag_one := by
    intro x hx hclose
    have hxlo : (2 : ℝ)⁻¹ ≤ x haltCoordU := by
      have hdist : 1 - x haltCoordU ≤ |x haltCoordU - 1| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      have hquarter : 1 - x haltCoordU ≤ (1 : ℝ) / 4 := hdist.trans hclose
      norm_num at hquarter ⊢
      linarith
    have hnot : ¬ x haltCoordU < (2 : ℝ)⁻¹ := not_lt.mpr hxlo
    simp [hnot]
  on_flag_zero := by
    intro x hx hclose
    have hxhi : x haltCoordU ≤ (1 : ℝ) / 4 := by
      have hdist : x haltCoordU ≤ |x haltCoordU - 0| := by
        simpa using le_abs_self (x haltCoordU - 0)
      exact hdist.trans hclose
    have hlt : x haltCoordU < (2 : ℝ)⁻¹ := by
      norm_num
      linarith
    simp [hlt]

/-- Concrete positive local-extraction radius used as a coordinatewise schedule. -/
def rLE_constU : Fin d_U → ℝ :=
  fun _ => r_LE_U

/--
Structural amplifier for the universal machine: stack coordinates get the
per-stack diagonal multiplier and reset coordinates get zero.
-/
def ampU (c : ℕ → UConf) (j : ℕ) (i : Fin d_U) : ℝ :=
  match coordStackIndexU i with
  | some s => (B_U : ℝ) ^ stackMachineEncodingU.stackDelta (c j) s
  | none => 0

theorem ampU_stack (c : ℕ → UConf) (j : ℕ) (s : Fin 4) :
    ampU c j (stackMachineEncodingU.stackCoord s) =
      (stackMachineEncodingU.k : ℝ) ^
        stackMachineEncodingU.stackDelta (c j) s := by
  simp [ampU, stackMachineEncodingU]

theorem ampU_reset (c : ℕ → UConf) (j : ℕ) (i : Fin d_U)
    (hi : stackMachineEncodingU.coordStackIndex i = none) :
    ampU c j i = 0 := by
  change coordStackIndexU i = none at hi
  simp [ampU, hi]

/-- Stack/reset depth attached to a coordinate at one machine cycle. -/
def depthCoordU (c : UConf) (i : Fin d_U) : ℤ :=
  match coordStackIndexU i with
  | some s => (indexedStackU c s).length
  | none => 0

/-- Cycle-indexed structural depth for the universal machine. -/
def depthU (c : ℕ → UConf) (j : ℕ) (i : Fin d_U) : ℤ :=
  depthCoordU (c j) i

theorem depthU_stack (c : ℕ → UConf) (j : ℕ) (s : Fin 4) :
    depthU c j (stackMachineEncodingU.stackCoord s) =
      ((indexedStackU (c j) s).length : ℤ) := by
  simp [depthU, depthCoordU, stackMachineEncodingU]

theorem depthU_reset (c : ℕ → UConf) (j : ℕ) (i : Fin d_U)
    (hi : stackMachineEncodingU.coordStackIndex i = none) :
    depthU c j i = 0 := by
  change coordStackIndexU i = none at hi
  simp [depthU, depthCoordU, hi]

theorem depthU_recurrence (c : ℕ → UConf) (d0 : Fin d_U → ℤ) :
    ∀ j i,
      contractDepthU stackMachineEncodingU c d0 (j + 1) i =
        contractDepthU stackMachineEncodingU c d0 j i -
          stackMachineEncodingU.coordDelta (c j) i := by
  intro j i
  exact contractDepthU_step stackMachineEncodingU c d0 j i

/--
Concrete coarse displacement scale for the universal branch layer.  The stack
part covers push/pop/replace actions on the local tube; the control part covers
the finite packed `(label, variable)` coordinate.
-/
def D_U : ℝ :=
  max 8 (2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) + 2)

theorem D_U_nonneg : 0 ≤ D_U := by
  simp [D_U]

private theorem D_U_ge_eight : (8 : ℝ) ≤ D_U := by
  unfold D_U
  exact le_max_left _ _

private theorem one_le_two_D_U : (1 : ℝ) ≤ 2 * D_U := by
  have hD := D_U_ge_eight
  nlinarith

private theorem sixteen_le_two_D_U : (16 : ℝ) ≤ 2 * D_U := by
  have hD := D_U_ge_eight
  nlinarith

theorem coordMultiplierU_nonneg (c : UConf) (i : Fin d_U) :
    0 ≤ stackMachineEncodingU.coordMultiplier c i := by
  simp [stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta]
  split
  · cases moveTypeStackU c _ <;> norm_num [B_U, StackMove.delta]
  · norm_num

theorem coordMultiplierU_le_six (c : UConf) (i : Fin d_U) :
    stackMachineEncodingU.coordMultiplier c i ≤ (6 : ℝ) := by
  simp [stackMachineEncodingU, StackMachineEncoding.coordMultiplier,
    StackMachineEncoding.stackMultiplier, StackMachineEncoding.stackDelta]
  split
  · cases moveTypeStackU c _ <;> norm_num [B_U, StackMove.delta]
  · norm_num

private theorem stack_enc_mem_unit_U (c : UConf) (k : K') :
    ((confEncU c (stackCoordU k) : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have h := confEncU_stack_gap_range c k
  constructor
  · exact_mod_cast (le_of_lt h.1)
  · have hle :
        ((confEncU c (stackCoordU k) : ℚ) : ℝ) ≤
          (((bot B_U : ℕ) : ℚ) / (B_U : ℚ) : ℚ) := by
      exact_mod_cast h.2.1
    have hgap : ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ) : ℚ) : ℝ) ≤ (1 : ℝ) := by
      norm_num [bot, B_U]
    exact hle.trans hgap

private theorem stack_step_abs_diff_le_one_U (c : UConf) (k : K') :
    |((confEncU (finStep c) (stackCoordU k) : ℚ) : ℝ) -
        ((confEncU c (stackCoordU k) : ℚ) : ℝ)| ≤ (1 : ℝ) := by
  have hn := stack_enc_mem_unit_U (finStep c) k
  have hc := stack_enc_mem_unit_U c k
  rw [abs_le]
  constructor <;> linarith [hn.1, hn.2, hc.1, hc.2]

private theorem ctrlVarCodeU_mem_range
    (q : Option (SuppLabel c_f)) (v : Option Γ') :
    (0 : ℝ) ≤ (ctrlVarCodeU q v : ℝ) ∧
      (ctrlVarCodeU q v : ℝ) ≤
        2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
  constructor
  · unfold ctrlVarCodeU
    positivity
  · have hidx :
        ((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q, v)).val <
          Fintype.card (Option (SuppLabel c_f) × Option Γ') :=
      (Fintype.equivFin (Option (SuppLabel c_f) × Option Γ') (q, v)).isLt
    unfold ctrlVarCodeU
    push_cast
    have hle :
        (((Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')) (q, v)).val : ℝ) ≤
          (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
      exact_mod_cast hidx.le
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)

private theorem ctrl_step_abs_diff_le_twocard_U (c : UConf) :
    |((confEncU (finStep c) ctrlCoordU : ℚ) : ℝ) -
        ((confEncU c ctrlCoordU : ℚ) : ℝ)| ≤
      2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) := by
  have hn := ctrlVarCodeU_mem_range (finStep c).1 (finStep c).2.1
  have hc := ctrlVarCodeU_mem_range c.1 c.2.1
  rw [confEncU_ctrl, confEncU_ctrl]
  push_cast
  rw [abs_le]
  constructor <;> linarith [hn.1, hn.2, hc.1, hc.2]

private theorem halt_step_abs_diff_le_one_U (c : UConf) :
    |((confEncU (finStep c) haltCoordU : ℚ) : ℝ) -
        ((confEncU c haltCoordU : ℚ) : ℝ)| ≤ (1 : ℝ) := by
  rw [confEncU_halt, confEncU_halt]
  unfold haltFlagU
  by_cases hn : finHalted (finStep c) <;>
    by_cases hc : finHalted c <;>
      simp [hn, hc]

private theorem one_le_D_U_sub_two : (1 : ℝ) ≤ D_U - 2 := by
  have hD := D_U_ge_eight
  linarith

private theorem twocard_le_D_U_sub_two :
    2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) ≤
      D_U - 2 := by
  have hD :
      2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) + 2 ≤ D_U :=
    le_max_right _ _
  linarith

theorem enc_step_abs_diff_le_D_U_sub_two (c : UConf) (i : Fin d_U) :
    |stackMachineEncodingU.enc (M_U.step c) i - stackMachineEncodingU.enc c i| ≤
      D_U - 2 := by
  fin_cases i
  · exact (by
      simpa [stackMachineEncodingU, M_U, discreteMachine, mainStackCoordU, stackCoordU]
        using (stack_step_abs_diff_le_one_U c K'.main).trans one_le_D_U_sub_two)
  · exact (by
      simpa [stackMachineEncodingU, M_U, discreteMachine, revStackCoordU, stackCoordU]
        using (stack_step_abs_diff_le_one_U c K'.rev).trans one_le_D_U_sub_two)
  · exact (by
      simpa [stackMachineEncodingU, M_U, discreteMachine, auxStackCoordU, stackCoordU]
        using (stack_step_abs_diff_le_one_U c K'.aux).trans one_le_D_U_sub_two)
  · exact (by
      simpa [stackMachineEncodingU, M_U, discreteMachine, dataStackCoordU, stackCoordU]
        using (stack_step_abs_diff_le_one_U c K'.stack).trans one_le_D_U_sub_two)
  · exact (by
      simpa [stackMachineEncodingU, M_U, discreteMachine, ctrlCoordU]
        using (ctrl_step_abs_diff_le_twocard_U c).trans twocard_le_D_U_sub_two)
  · exact (by
      simpa [stackMachineEncodingU, M_U, discreteMachine, haltCoordU]
        using (halt_step_abs_diff_le_one_U c).trans one_le_D_U_sub_two)

private theorem stackCodeU_abs_le_one_real (L : List Γ') :
    |((stackCodeU B_U gammaDigit L : ℚ) : ℝ)| ≤ (1 : ℝ) := by
  have hgap := stackCodeU_mem_gap_range L
  have hnonneg : (0 : ℝ) ≤ ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) := by
    exact_mod_cast hgap.1.le
  have hle : ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ≤ (1 : ℝ) := by
    have hleQ := hgap.2.1
    have hleR :
        ((stackCodeU B_U gammaDigit L : ℚ) : ℝ) ≤
          ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) := by
      exact_mod_cast hleQ
    have hbot : ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) ≤ (1 : ℝ) := by
      norm_num [B_U, bot]
    exact hleR.trans hbot
  exact abs_le.mpr ⟨by linarith, hle⟩

private theorem gammaDigit_abs_le_three (a : Γ') :
    |(gammaDigit a : ℝ)| ≤ (3 : ℝ) := by
  cases a <;> norm_num [gammaDigit]

private theorem stackActionU_scale_abs_le_six (before after : List Γ') :
    |((stackActionU before after).scale : ℝ)| ≤ (6 : ℝ) := by
  unfold stackActionU
  repeat' split
  all_goals
    norm_num [BranchAction.push, BranchAction.pop, BranchAction.stay,
      BranchAction.replace, BranchAction.const, BranchAction.affine, B_U]

private theorem stackActionU_shift_abs_le_four (before after : List Γ') :
    |((stackActionU before after).shift : ℝ)| ≤ (4 : ℝ) := by
  have hpush : ∀ a : Γ',
      |((((gammaDigit a : ℚ) / (B_U : ℚ)) : ℚ) : ℝ)| ≤ (4 : ℝ) := by
    intro a
    cases a <;> norm_num [gammaDigit, B_U]
  have hpop : ∀ a : Γ', |(gammaDigit a : ℝ)| ≤ (4 : ℝ) := by
    intro a
    cases a <;> norm_num [gammaDigit]
  have hreplace : ∀ a b : Γ',
      |(((((gammaDigit a : ℚ) - (gammaDigit b : ℚ)) / (B_U : ℚ)) : ℚ) : ℝ)| ≤
        (4 : ℝ) := by
    intro a b
    cases a <;> cases b <;> norm_num [gammaDigit, B_U]
  have hconst : ∀ L : List Γ',
      |((stackCodeU B_U gammaDigit L : ℚ) : ℝ)| ≤ (4 : ℝ) := by
    intro L
    exact (stackCodeU_abs_le_one_real L).trans (by norm_num)
  have hpush6 : ∀ a : Γ', |(gammaDigit a : ℝ) / 6| ≤ (4 : ℝ) := by
    intro a
    cases a <;> norm_num [gammaDigit]
  have hpopNat : ∀ a : Γ', gammaDigit a ≤ 4 := by
    intro a
    cases a <;> norm_num [gammaDigit]
  have hpopR : ∀ a : Γ', (gammaDigit a : ℝ) ≤ (4 : ℝ) := by
    intro a
    exact_mod_cast hpopNat a
  have hreplace6 : ∀ a b : Γ',
      |((gammaDigit a : ℝ) - (gammaDigit b : ℝ)) / 6| ≤ (4 : ℝ) := by
    intro a b
    cases a <;> cases b <;> norm_num [gammaDigit]
  have hconst6 : ∀ L : List Γ',
      |((stackCodeU 6 gammaDigit L : ℚ) : ℝ)| ≤ (4 : ℝ) := by
    intro L
    simpa [B_U] using hconst L
  unfold stackActionU
  repeat' split
  all_goals
    simp [BranchAction.push, BranchAction.pop, BranchAction.stay,
      BranchAction.replace, BranchAction.const, BranchAction.affine, B_U]
  all_goals
    first
    | exact hpush6 _
    | exact hpopNat _
    | exact hpopR _
    | exact hreplace6 _ _
    | exact hconst6 _
    | exact hpush _
    | exact hpop _
    | exact hreplace _ _
    | exact hconst _
    | norm_num [bot]

private theorem stackActionU_eval_abs_le_sixteen
    (before after : List Γ') {y : ℝ} (hy : |y| ≤ (1 : ℝ)) :
    |BranchAction.evalReal B_U (stackActionU before after) y| ≤ (16 : ℝ) := by
  have hscale := stackActionU_scale_abs_le_six before after
  have hshift := stackActionU_shift_abs_le_four before after
  have htri :
      |BranchAction.evalReal B_U (stackActionU before after) y| ≤
        |((stackActionU before after).scale : ℝ) * y| +
          |((stackActionU before after).shift : ℝ)| := by
    simpa [BranchAction.evalReal] using
      abs_add_le (((stackActionU before after).scale : ℝ) * y)
        (((stackActionU before after).shift : ℝ))
  have hprod :
      |((stackActionU before after).scale : ℝ) * y| ≤ (6 : ℝ) := by
    calc
      |((stackActionU before after).scale : ℝ) * y|
          = |((stackActionU before after).scale : ℝ)| * |y| := abs_mul _ _
      _ ≤ 6 * 1 := by
          exact mul_le_mul hscale hy (abs_nonneg _) (by norm_num)
      _ = (6 : ℝ) := by norm_num
  calc
    |BranchAction.evalReal B_U (stackActionU before after) y|
        ≤ |((stackActionU before after).scale : ℝ) * y| +
          |((stackActionU before after).shift : ℝ)| := htri
    _ ≤ 6 + 4 := add_le_add hprod hshift
    _ ≤ (16 : ℝ) := by norm_num

private theorem tube_stack_coord_abs_le_one
    {c : UConf} {x : Fin d_U → ℝ}
    (htube : EncodingTube stackMachineEncodingU r_LE_U c x) (k : K') :
    |x (stackCoordU k)| ≤ (1 : ℝ) := by
  have hdist : |x (stackCoordU k) - stackMachineEncodingU.enc c (stackCoordU k)| ≤
      r_LE_U := htube (stackCoordU k)
  have hgap := confEncU_stack_gap_range c k
  have henc_nonneg : (0 : ℝ) ≤ stackMachineEncodingU.enc c (stackCoordU k) := by
    simpa [stackMachineEncodingU] using (show (0 : ℝ) ≤ (confEncU c (stackCoordU k) : ℝ) by
      exact_mod_cast hgap.1.le)
  have henc_le : stackMachineEncodingU.enc c (stackCoordU k) ≤ (2 : ℝ) / 3 := by
    have hleQ := hgap.2.1
    have hleR :
        (confEncU c (stackCoordU k) : ℝ) ≤
          ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) := by
      exact_mod_cast hleQ
    calc
      stackMachineEncodingU.enc c (stackCoordU k)
          = (confEncU c (stackCoordU k) : ℝ) := rfl
      _ ≤ ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) := hleR
      _ = (2 : ℝ) / 3 := by norm_num [B_U, bot]
  have hdist' := abs_le.mp hdist
  rw [abs_le]
  constructor
  · have hr : r_LE_U ≤ (1 : ℝ) := by norm_num [r_LE_U]
    linarith
  · have hr : r_LE_U + (2 : ℝ) / 3 ≤ (1 : ℝ) := by norm_num [r_LE_U]
    linarith

private theorem ctrlVarCodeU_abs_le_two_D_U
    (q : Option (SuppLabel c_f)) (v : Option Γ') :
    |(ctrlVarCodeU q v : ℝ)| ≤ 2 * D_U := by
  let C : ℕ := Fintype.card (Option (SuppLabel c_f) × Option Γ')
  let e := Fintype.equivFin (Option (SuppLabel c_f) × Option Γ')
  have hval_le : ((e (q, v)).val : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast Nat.le_of_lt (e (q, v)).isLt
  have hnonneg : (0 : ℝ) ≤ (ctrlVarCodeU q v : ℝ) := by
    unfold ctrlVarCodeU
    positivity
  have hcode_le : (ctrlVarCodeU q v : ℝ) ≤ 2 * (C : ℝ) := by
    unfold ctrlVarCodeU
    change ((2 * (e (q, v)).val : ℕ) : ℝ) ≤ 2 * (C : ℝ)
    exact_mod_cast (Nat.mul_le_mul_left 2 (Nat.le_of_lt (e (q, v)).isLt))
  have hD : 2 * (C : ℝ) ≤ D_U := by
    unfold D_U C
    exact le_trans (by linarith : 2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) ≤
        2 * (Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℝ) + 2)
      (le_max_right _ _)
  have habs : |(ctrlVarCodeU q v : ℝ)| = (ctrlVarCodeU q v : ℝ) :=
    abs_of_nonneg hnonneg
  rw [habs]
  nlinarith

theorem branchU_evalBranch_abs_le_two_D_U
    {c : UConf} {x : Fin d_U → ℝ}
    (htube : EncodingTube stackMachineEncodingU r_LE_U c x)
    (v : UniversalLocalView) (i : Fin d_U) :
    |BranchData.evalBranch (branchU v) x i| ≤ 2 * D_U := by
  fin_cases i
  · have hstack := stackActionU_eval_abs_le_sixteen
      (mainStackU (localViewConfU v)) (mainStackU (finStep (localViewConfU v)))
      (tube_stack_coord_abs_le_one htube K'.main)
    exact hstack.trans sixteen_le_two_D_U
  · have hstack := stackActionU_eval_abs_le_sixteen
      (revStackU (localViewConfU v)) (revStackU (finStep (localViewConfU v)))
      (tube_stack_coord_abs_le_one htube K'.rev)
    exact hstack.trans sixteen_le_two_D_U
  · have hstack := stackActionU_eval_abs_le_sixteen
      (auxStackU (localViewConfU v)) (auxStackU (finStep (localViewConfU v)))
      (tube_stack_coord_abs_le_one htube K'.aux)
    exact hstack.trans sixteen_le_two_D_U
  · have hstack := stackActionU_eval_abs_le_sixteen
      (dataStackU (localViewConfU v)) (dataStackU (finStep (localViewConfU v)))
      (tube_stack_coord_abs_le_one htube K'.stack)
    exact hstack.trans sixteen_le_two_D_U
  · change |BranchData.evalBranch (branchU v) x ctrlCoordU| ≤ 2 * D_U
    have hctrl :=
      ctrlVarCodeU_abs_le_two_D_U
        (finStep (localViewConfU v)).1 (finStep (localViewConfU v)).2.1
    simpa [BranchData.evalBranch, branchU, branchActionForCoordU_ctrl,
      BranchAction.evalReal, BranchAction.const, BranchAction.affine] using hctrl
  · have hmem := branchU_halt_target_mem_Icc v x
    have habs : |BranchData.evalBranch (branchU v) x haltCoordU| ≤ (1 : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith [hmem.1], hmem.2⟩
    exact habs.trans one_le_two_D_U

theorem branchU_BranchSpread_four_D_U
    {c : UConf} {x : Fin d_U → ℝ}
    (htube : EncodingTube stackMachineEncodingU r_LE_U c x)
    (i : Fin d_U) :
    BranchSpread branchU x (localViewU c) i (4 * D_U) := by
  constructor
  · have h := branchU_evalBranch_abs_le_two_D_U htube (localViewU c) i
    have hD := D_U_nonneg
    nlinarith
  · intro v _hv
    have hv := branchU_evalBranch_abs_le_two_D_U htube v i
    have hstar := branchU_evalBranch_abs_le_two_D_U htube (localViewU c) i
    have htri :
        |BranchData.evalBranch (branchU v) x i -
            BranchData.evalBranch (branchU (localViewU c)) x i| ≤
          |BranchData.evalBranch (branchU v) x i| +
            |BranchData.evalBranch (branchU (localViewU c)) x i| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le
        (BranchData.evalBranch (branchU v) x i)
        (-(BranchData.evalBranch (branchU (localViewU c)) x i))
    have hD := D_U_nonneg
    nlinarith

/-- `1/3`-tube stack coordinate box: the stack encodings sit in `[0, 2/3]`
(`confEncU_stack_gap_range`), so a third-radius tube still keeps the
coordinate inside `[-1, 1]`.  Radius-relaxed sibling of
`tube_stack_coord_abs_le_one` (which is hardwired to `r_LE_U`). -/
private theorem tube_third_stack_coord_abs_le_one
    {c : UConf} {x : Fin d_U → ℝ}
    (htube : EncodingTube stackMachineEncodingU (1 / 3 : ℝ) c x) (k : K') :
    |x (stackCoordU k)| ≤ (1 : ℝ) := by
  have hdist : |x (stackCoordU k) -
      stackMachineEncodingU.enc c (stackCoordU k)| ≤ (1 / 3 : ℝ) :=
    htube (stackCoordU k)
  have hgap := confEncU_stack_gap_range c k
  have henc_nonneg : (0 : ℝ) ≤ stackMachineEncodingU.enc c (stackCoordU k) := by
    simpa [stackMachineEncodingU] using
      (show (0 : ℝ) ≤ (confEncU c (stackCoordU k) : ℝ) by
        exact_mod_cast hgap.1.le)
  have henc_le : stackMachineEncodingU.enc c (stackCoordU k) ≤ (2 : ℝ) / 3 := by
    have hleQ := hgap.2.1
    have hleR :
        (confEncU c (stackCoordU k) : ℝ) ≤
          ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) := by
      exact_mod_cast hleQ
    calc
      stackMachineEncodingU.enc c (stackCoordU k)
          = (confEncU c (stackCoordU k) : ℝ) := rfl
      _ ≤ ((((bot B_U : ℕ) : ℚ) / (B_U : ℚ)) : ℝ) := hleR
      _ = (2 : ℝ) / 3 := by norm_num [B_U, bot]
  have hdist' := abs_le.mp hdist
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Radius-`1/3` variant of `branchU_evalBranch_abs_le_two_D_U`: the hull
bound only needs the stack coordinates inside `[-1, 1]` (which a
third-radius tube still guarantees); the ctrl and halt branch targets are
`x`-independent resp. `[0, 1]`-valued. -/
theorem branchU_evalBranch_abs_le_two_D_U_of_third_tube
    {c : UConf} {x : Fin d_U → ℝ}
    (htube : EncodingTube stackMachineEncodingU (1 / 3 : ℝ) c x)
    (v : UniversalLocalView) (i : Fin d_U) :
    |BranchData.evalBranch (branchU v) x i| ≤ 2 * D_U := by
  fin_cases i
  · have hstack := stackActionU_eval_abs_le_sixteen
      (mainStackU (localViewConfU v)) (mainStackU (finStep (localViewConfU v)))
      (tube_third_stack_coord_abs_le_one htube K'.main)
    exact hstack.trans sixteen_le_two_D_U
  · have hstack := stackActionU_eval_abs_le_sixteen
      (revStackU (localViewConfU v)) (revStackU (finStep (localViewConfU v)))
      (tube_third_stack_coord_abs_le_one htube K'.rev)
    exact hstack.trans sixteen_le_two_D_U
  · have hstack := stackActionU_eval_abs_le_sixteen
      (auxStackU (localViewConfU v)) (auxStackU (finStep (localViewConfU v)))
      (tube_third_stack_coord_abs_le_one htube K'.aux)
    exact hstack.trans sixteen_le_two_D_U
  · have hstack := stackActionU_eval_abs_le_sixteen
      (dataStackU (localViewConfU v)) (dataStackU (finStep (localViewConfU v)))
      (tube_third_stack_coord_abs_le_one htube K'.stack)
    exact hstack.trans sixteen_le_two_D_U
  · change |BranchData.evalBranch (branchU v) x ctrlCoordU| ≤ 2 * D_U
    have hctrl :=
      ctrlVarCodeU_abs_le_two_D_U
        (finStep (localViewConfU v)).1 (finStep (localViewConfU v)).2.1
    simpa [BranchData.evalBranch, branchU, branchActionForCoordU_ctrl,
      BranchAction.evalReal, BranchAction.const, BranchAction.affine] using hctrl
  · have hmem := branchU_halt_target_mem_Icc v x
    have habs : |BranchData.evalBranch (branchU v) x haltCoordU| ≤ (1 : ℝ) := by
      rw [abs_le]
      exact ⟨by linarith [hmem.1], hmem.2⟩
    exact habs.trans one_le_two_D_U

/-- Concrete latch gain used by the bounded assembly layer. -/
def K_U : ℝ := 1

theorem K_U_pos : 0 < K_U := by
  norm_num [K_U]

/--
Contract bridge shape for the six-coordinate machine instance.

The existing `RobustStepContract` cannot consume this directly because it fixes
`Fin 4` and two stack sides.  A dimension-generic contract can use this theorem
as its instance-layer handoff: once a selector polynomial family realizes the
view-indexed six-coordinate branch data with error `eps`, the universal-machine
sampled step clause is exactly the supplied realization hypothesis.
-/
theorem universal_contract_bridge
    (F : ℝ → (Fin d_U → ℝ) → Fin d_U → ℝ)
    (eps : ℝ → Fin d_U → ℝ)
    (radius : ℝ → ℝ)
    (mu_min : ℝ)
    (diag :
      ∀ {mu c x}, mu_min ≤ mu → UTube (radius mu) c x → ∀ i,
        |F mu x i - (confEncU (finStep c) i : ℝ)| ≤ eps mu i) :
    ∀ {mu c x}, mu_min ≤ mu → UTube (radius mu) c x → ∀ i,
      |F mu x i - (confEncU (finStep c) i : ℝ)| ≤ eps mu i := by
  intro mu c x hmu hx i
  exact diag hmu hx i

end

end MachineInstance
end Ripple.BoundedUniversality.BGP
