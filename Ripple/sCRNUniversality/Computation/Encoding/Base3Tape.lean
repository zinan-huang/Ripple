import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc
import Mathlib.Tactic
import Ripple.sCRNUniversality.Computation.CTM.Basic

namespace Ripple.sCRNUniversality

namespace Encoding

def bitDigit : Bool -> Nat
  | false => 1
  | true => 2

@[simp]
theorem bitDigit_false : bitDigit false = 1 := rfl

@[simp]
theorem bitDigit_true : bitDigit true = 2 := rfl

def IsBase3BoolDigit (d : Nat) : Prop :=
  d = 1 \/ d = 2

def IsBase3BoolDigitList (digits : List Nat) : Prop :=
  forall d, d ∈ digits -> IsBase3BoolDigit d

def boolDigits {n : Nat} (w : List.Vector Bool n) : List Nat :=
  w.toList.map bitDigit

def readDigit? (d : Nat) : Option Bool :=
  if d = 1 then some false else if d = 2 then some true else none

def readMSBVector? {n : Nat} (w : List.Vector Bool n) : Option Bool :=
  w.toList.head?

def eraseMSBVector {n : Nat} (w : List.Vector Bool (n + 1)) : List.Vector Bool n :=
  w.tail

def base3ValList : List Bool -> Nat
  | [] => 0
  | b :: bs => bitDigit b * 3 ^ bs.length + base3ValList bs

def base3Val {n : Nat} (w : List.Vector Bool n) : Nat :=
  base3ValList w.toList

def IsBase3BoolTape (n m : Nat) : Prop :=
  exists w : List.Vector Bool n, base3Val w = m

def readMSB? (s m : Nat) : Bool :=
  decide (2 * 3 ^ s <= m)

def eraseMSBWith (s : Nat) (r : Bool) (m : Nat) : Nat :=
  m - bitDigit r * 3 ^ s

def eraseMSB (s m : Nat) : Nat :=
  eraseMSBWith s (readMSB? s m) m

def shiftTail (m : Nat) : Nat :=
  3 * m

def IsShiftedBase3BoolTape (n m : Nat) : Prop :=
  exists tail : Nat, IsBase3BoolTape n tail /\ m = shiftTail tail

def writeLSB (m : Nat) (b : Bool) : Nat :=
  m + bitDigit b

def rotateWriteVal (s m : Nat) (b : Bool) : Nat :=
  writeLSB (shiftTail (eraseMSB s m)) b

theorem bitDigit_isBase3BoolDigit (b : Bool) :
    IsBase3BoolDigit (bitDigit b) := by
  cases b <;> simp [IsBase3BoolDigit, bitDigit]

theorem bitDigit_eq_one_or_two (b : Bool) :
    bitDigit b = 1 \/ bitDigit b = 2 := by
  cases b <;> simp [bitDigit]

theorem bitDigit_ne_zero (b : Bool) :
    bitDigit b ≠ 0 := by
  cases b <;> simp [bitDigit]

theorem boolDigits_isBase3BoolDigitList {n : Nat} (w : List.Vector Bool n) :
    IsBase3BoolDigitList (boolDigits w) := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨b, _hb, rfl⟩
  exact bitDigit_isBase3BoolDigit b

theorem IsBase3BoolTape.of_base3Val {n : Nat} (w : List.Vector Bool n) :
    IsBase3BoolTape n (base3Val w) := by
  exact ⟨w, rfl⟩

theorem readDigit?_bitDigit (b : Bool) :
    readDigit? (bitDigit b) = some b := by
  cases b <;> simp [readDigit?, bitDigit]

theorem readMSBVector?_nil :
    readMSBVector? (List.Vector.nil : List.Vector Bool 0) = none := by
  rfl

theorem readMSBVector?_cons {n : Nat} (b : Bool) (w : List.Vector Bool n) :
    readMSBVector? (List.Vector.cons b w) = some b := by
  simp [readMSBVector?]

theorem readMSBVector?_succ {n : Nat} (w : List.Vector Bool (n + 1)) :
    readMSBVector? w = some w.head := by
  simpa [readMSBVector?] using List.Vector.head?_toList w

theorem eraseMSBVector_cons {n : Nat} (b : Bool) (w : List.Vector Bool n) :
    eraseMSBVector (List.Vector.cons b w) = w := by
  simp [eraseMSBVector]

theorem base3Val_nil :
    base3Val (List.Vector.nil : List.Vector Bool 0) = 0 := by
  rfl

theorem base3Val_cons {n : Nat} (b : Bool) (w : List.Vector Bool n) :
    base3Val (List.Vector.cons b w) = bitDigit b * 3 ^ n + base3Val w := by
  simp [base3Val, base3ValList]

theorem base3Val_cons_false {n : Nat} (w : List.Vector Bool n) :
    base3Val (List.Vector.cons false w) = 3 ^ n + base3Val w := by
  simp [base3Val_cons, bitDigit]

theorem base3Val_cons_true {n : Nat} (w : List.Vector Bool n) :
    base3Val (List.Vector.cons true w) = 2 * 3 ^ n + base3Val w := by
  simp [base3Val_cons, bitDigit]

theorem base3Val_decompose {n : Nat} (w : List.Vector Bool (n + 1)) :
    base3Val w = bitDigit w.head * 3 ^ n + base3Val (eraseMSBVector w) := by
  rw [← List.Vector.cons_head_tail w]
  simp [eraseMSBVector, base3Val_cons]

theorem headDigit_mul_pow_le_base3Val {n : Nat}
    (w : List.Vector Bool (n + 1)) :
    bitDigit w.head * 3 ^ n <= base3Val w := by
  rw [base3Val_decompose w]
  exact Nat.le_add_right _ _

theorem base3ValList_lt_pow_length (bs : List Bool) :
    base3ValList bs < 3 ^ bs.length := by
  induction bs with
  | nil =>
      simp [base3ValList]
  | cons b bs ih =>
      have hpos : 0 < 3 ^ bs.length := Nat.pow_pos (by norm_num)
      have hpow : 3 ^ (bs.length + 1) = 3 ^ bs.length * 3 := by
        rw [pow_succ]
      change base3ValList (b :: bs) < 3 ^ (bs.length + 1)
      rw [hpow]
      cases b <;> simp [base3ValList, bitDigit] <;> nlinarith

theorem base3Val_bounds {n : Nat} (w : List.Vector Bool n) :
    base3Val w < 3 ^ n := by
  simpa [base3Val, w.2] using base3ValList_lt_pow_length w.toList

theorem IsBase3BoolTape.lt_pow {n m : Nat}
    (h : IsBase3BoolTape n m) : m < 3 ^ n := by
  rcases h with ⟨w, rfl⟩
  exact base3Val_bounds w

theorem IsBase3BoolTape.nonzero {n m : Nat}
    (h : IsBase3BoolTape (n + 1) m) : 0 < m := by
  rcases h with ⟨w, rfl⟩
  rw [base3Val_decompose w]
  have hpow : 0 < 3 ^ n := Nat.pow_pos (by norm_num)
  cases w.head <;> simp [bitDigit, hpow]

theorem base3Val_cons_false_lt_threshold {n : Nat} (w : List.Vector Bool n) :
    base3Val (List.Vector.cons false w) < 2 * 3 ^ n := by
  have h := base3Val_bounds w
  rw [base3Val_cons_false]
  nlinarith

theorem threshold_le_base3Val_cons_true {n : Nat} (w : List.Vector Bool n) :
    2 * 3 ^ n <= base3Val (List.Vector.cons true w) := by
  rw [base3Val_cons_true]
  exact Nat.le_add_right _ _

theorem readMSB?_eq_true {s m : Nat} :
    readMSB? s m = true ↔ 2 * 3 ^ s <= m := by
  simp [readMSB?]

theorem readMSB?_eq_false {s m : Nat} :
    readMSB? s m = false ↔ m < 2 * 3 ^ s := by
  by_cases h : 2 * 3 ^ s <= m
  · have hnlt : ¬ m < 2 * 3 ^ s := not_lt_of_ge h
    simp [readMSB?, h, hnlt]
  · have hlt : m < 2 * 3 ^ s := Nat.lt_of_not_ge h
    simp [readMSB?, h, hlt]

theorem base3Val_lt_threshold_iff_head_false {n : Nat} (w : List.Vector Bool (n + 1)) :
    base3Val w < 2 * 3 ^ n ↔ w.head = false := by
  constructor
  · intro h
    cases hHead : w.head
    · rfl
    · have hge : 2 * 3 ^ n <= base3Val w := by
        rw [← List.Vector.cons_head_tail w]
        simpa [hHead] using threshold_le_base3Val_cons_true (eraseMSBVector w)
      exact False.elim ((not_lt_of_ge hge) h)
  · intro hHead
    rw [← List.Vector.cons_head_tail w]
    simpa [hHead] using base3Val_cons_false_lt_threshold (eraseMSBVector w)

theorem threshold_le_base3Val_iff_head_true {n : Nat} (w : List.Vector Bool (n + 1)) :
    2 * 3 ^ n <= base3Val w ↔ w.head = true := by
  constructor
  · intro h
    cases hHead : w.head
    · have hlt : base3Val w < 2 * 3 ^ n := by
        rw [← List.Vector.cons_head_tail w]
        simpa [hHead] using base3Val_cons_false_lt_threshold (eraseMSBVector w)
      exact False.elim ((not_lt_of_ge h) hlt)
    · rfl
  · intro hHead
    rw [← List.Vector.cons_head_tail w]
    simpa [hHead] using threshold_le_base3Val_cons_true (eraseMSBVector w)

theorem readMSB?_base3Val {s : Nat} (w : List.Vector Bool (s + 1)) :
    readMSB? s (base3Val w) = w.head := by
  cases hHead : w.head
  · have hlt : base3Val w < 2 * 3 ^ s :=
      (base3Val_lt_threshold_iff_head_false w).mpr hHead
    have hnot : ¬ 2 * 3 ^ s <= base3Val w := not_le_of_gt hlt
    simp [readMSB?, hnot]
  · have hle : 2 * 3 ^ s <= base3Val w :=
      (threshold_le_base3Val_iff_head_true w).mpr hHead
    simp [readMSB?, hle]

theorem eraseMSBWith_false {s m : Nat} :
    eraseMSBWith s false m = m - 3 ^ s := by
  simp [eraseMSBWith, bitDigit]

theorem eraseMSBWith_true {s m : Nat} :
    eraseMSBWith s true m = m - 2 * 3 ^ s := by
  simp [eraseMSBWith, bitDigit]

theorem eraseMSBWith_base3Val {s : Nat} (w : List.Vector Bool (s + 1)) :
    eraseMSBWith s w.head (base3Val w) = base3Val (eraseMSBVector w) := by
  simp [eraseMSBWith, base3Val_decompose]

theorem bitDigit_readMSB?_mul_pow_le_of_IsBase3BoolTape {s m : Nat}
    (h : IsBase3BoolTape (s + 1) m) :
    bitDigit (readMSB? s m) * 3 ^ s <= m := by
  rcases h with ⟨w, rfl⟩
  rw [readMSB?_base3Val w]
  exact headDigit_mul_pow_le_base3Val w

theorem bitDigit_mul_pow_le_of_IsBase3BoolTape_read {s m : Nat}
    {r : Bool} (h : IsBase3BoolTape (s + 1) m)
    (hr : r = readMSB? s m) :
    bitDigit r * 3 ^ s <= m := by
  rw [hr]
  exact bitDigit_readMSB?_mul_pow_le_of_IsBase3BoolTape h

theorem eraseMSBWith_preserves_IsBase3BoolTape {s m : Nat}
    {r : Bool} (h : IsBase3BoolTape (s + 1) m)
    (hr : r = readMSB? s m) :
    IsBase3BoolTape s (eraseMSBWith s r m) := by
  rcases h with ⟨w, rfl⟩
  refine ⟨eraseMSBVector w, ?_⟩
  rw [hr, readMSB?_base3Val w]
  exact (eraseMSBWith_base3Val w).symm

theorem eraseMSBWith_lt_pow_of_IsBase3BoolTape {s m : Nat}
    {r : Bool} (h : IsBase3BoolTape (s + 1) m)
    (hr : r = readMSB? s m) :
    eraseMSBWith s r m < 3 ^ s :=
  (eraseMSBWith_preserves_IsBase3BoolTape h hr).lt_pow

theorem eraseMSB_base3Val {s : Nat} (w : List.Vector Bool (s + 1)) :
    eraseMSB s (base3Val w) = base3Val (eraseMSBVector w) := by
  simp [eraseMSB, readMSB?_base3Val, eraseMSBWith_base3Val]

theorem base3Val_eraseMSBVector {s : Nat} (w : List.Vector Bool (s + 1)) :
    base3Val (eraseMSBVector w) = base3ValList w.toList.tail := by
  exact congrArg base3ValList (List.Vector.toList_tail w)

theorem base3ValList_append_singleton (bs : List Bool) (b : Bool) :
    base3ValList (bs ++ [b]) = 3 * base3ValList bs + bitDigit b := by
  induction bs with
  | nil =>
      simp [base3ValList]
  | cons c cs ih =>
      have hpow : 3 ^ (cs.length + 1) = 3 ^ cs.length * 3 := by
        rw [pow_succ]
      rw [List.cons_append, base3ValList, ih]
      change bitDigit c * 3 ^ (cs ++ [b]).length +
          (3 * base3ValList cs + bitDigit b) =
        3 * (bitDigit c * 3 ^ cs.length + base3ValList cs) + bitDigit b
      simp [List.length_append, hpow]
      nlinarith

theorem base3Val_snoc {n : Nat} (w : List.Vector Bool n) (b : Bool) :
    base3Val (w.snoc b) = 3 * base3Val w + bitDigit b := by
  simp [base3Val, List.Vector.snoc, base3ValList_append_singleton]

theorem IsBase3BoolTape.shiftTail {n m : Nat}
    (h : IsBase3BoolTape n m) :
    IsShiftedBase3BoolTape n (shiftTail m) := by
  exact ⟨m, h, rfl⟩

theorem IsShiftedBase3BoolTape.writeLSB {n m : Nat}
    (h : IsShiftedBase3BoolTape n m) (b : Bool) :
    IsBase3BoolTape (n + 1) (writeLSB m b) := by
  rcases h with ⟨tail, hTail, rfl⟩
  rcases hTail with ⟨w, rfl⟩
  refine ⟨w.snoc b, ?_⟩
  rw [base3Val_snoc]
  rfl

theorem rotateWrite_toList {s : Nat}
    (w : List.Vector Bool (s + 1)) (b : Bool) :
    (CTM.Machine.rotateWrite w b).toList = w.toList.tail ++ [b] := by
  rfl

theorem rotateWrite_base3Val {s : Nat}
    (w : List.Vector Bool (s + 1)) (b : Bool) :
    base3Val (CTM.Machine.rotateWrite w b) =
      base3ValList (w.toList.tail ++ [b]) := by
  rfl

theorem rotateWriteVal_base3Val {s : Nat}
    (w : List.Vector Bool (s + 1)) (b : Bool) :
    rotateWriteVal s (base3Val w) b =
      base3Val (CTM.Machine.rotateWrite w b) := by
  rw [rotateWrite_base3Val, rotateWriteVal, writeLSB, shiftTail,
    eraseMSB_base3Val, base3Val_eraseMSBVector, base3ValList_append_singleton]

theorem rotateWriteVal_preserves_IsBase3BoolTape {s m : Nat} (b : Bool)
    (h : IsBase3BoolTape (s + 1) m) :
  IsBase3BoolTape (s + 1) (rotateWriteVal s m b) := by
  rcases h with ⟨w, rfl⟩
  exact ⟨CTM.Machine.rotateWrite w b, (rotateWriteVal_base3Val w b).symm⟩

end Encoding

end Ripple.sCRNUniversality
