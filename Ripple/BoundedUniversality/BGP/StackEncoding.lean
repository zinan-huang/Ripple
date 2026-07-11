/-
Ripple.BoundedUniversality.BGP.StackEncoding
------------------------
Concrete stack/configuration encoding layer for the four-coordinate BGP
interface.

Design sources read for this file:
* notes/gpt-life-umachine.md, deliverables 5-6
* notes/gpt-life-p13-encoding.md, D1

Documented choices and note mismatches:
* The stack recursion is exactly the D1 recursion:
  `stk [] = (B - 2) / B` and `stk (a :: L) = (dig a + stk L) / B`.
* The scanned-symbol coordinate is currently the constant `0`.  For the
  two-stack local robust-step layer the local branch data is carried by
  the two stack tops and the control coordinate; a future one-tape wrapper
  may replace this slot by a separate scanned-symbol integer without
  changing the stack algebra below.
* The notes ask for a uniform lower endpoint `lo > 0`.  For arbitrary
  finite stack length no such uniform positive lower bound exists: the
  stacks `0 :: ... :: 0 :: []` tend to `0`.  The file proves the sharp
  usable statement `0 < stk L` and the missing-digit upper bound.
* The computational `localExtract` below is specialized to the binary
  digit embedding `bitDigit a = a.val`.  The algebraic stack recursion and
  push/pop identities are provided for an arbitrary digit map `dig`.
-/

import Ripple.BoundedUniversality.BGP.RobustStepContract
import Mathlib

namespace Ripple.BoundedUniversality.BGP

noncomputable section

/-! ## Binary stack codes over an arbitrary base -/

/-- Bottom marker digit.  The missing digit is `B - 1`. -/
def bot (B : ℕ) : ℕ := B - 2

/-- The canonical binary digit embedding used by the extraction layer. -/
def bitDigit (a : Fin 2) : ℕ := a.val

/--
Stack encoding with the recursion specified in `notes/gpt-life-p13-encoding.md`.
The list is top-first.
-/
def stackCode (B : ℕ) (dig : Fin 2 → ℕ) : List (Fin 2) → ℚ
  | [] => ((bot B : ℕ) : ℚ) / (B : ℚ)
  | a :: L => ((dig a : ℚ) + stackCode B dig L) / (B : ℚ)

/-- Push identity, definitionally exposed. -/
theorem stackCode_push (B : ℕ) (dig : Fin 2 → ℕ) (a : Fin 2)
    (L : List (Fin 2)) :
    stackCode B dig (a :: L) =
      ((dig a : ℚ) + stackCode B dig L) / (B : ℚ) := by
  rfl

/-- Pop identity for a nonzero base. -/
theorem stackCode_pop (B : ℕ) (hB : 4 ≤ B) (dig : Fin 2 → ℕ)
    (a : Fin 2) (L : List (Fin 2)) :
    (B : ℚ) * stackCode B dig (a :: L) - (dig a : ℚ) =
      stackCode B dig L := by
  have hB0 : (B : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 4) hB))
  rw [stackCode]
  field_simp [hB0]
  ring

private theorem bot_lt_base (B : ℕ) (hB : 4 ≤ B) : bot B < B := by
  unfold bot
  omega

private theorem bot_pos (B : ℕ) (hB : 4 ≤ B) : 0 < bot B := by
  unfold bot
  omega

private theorem bitDigit_lt_bot (B : ℕ) (hB : 4 ≤ B) (a : Fin 2) :
    bitDigit a < bot B := by
  unfold bitDigit bot
  have ha : a.val < 2 := a.isLt
  omega

private theorem base_pos_rat (B : ℕ) (hB : 4 ≤ B) : (0 : ℚ) < (B : ℚ) := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)

private theorem bot_div_base_lt_one_rat (B : ℕ) (hB : 4 ≤ B) :
    ((bot B : ℕ) : ℚ) / (B : ℚ) < 1 := by
  have hpos := base_pos_rat B hB
  rw [div_lt_one hpos]
  exact_mod_cast bot_lt_base B hB

/-- Every legal stack code is strictly positive. -/
theorem stackCode_pos (B : ℕ) (hB : 4 ≤ B) (dig : Fin 2 → ℕ)
    (hdig : ∀ a, dig a < bot B) :
    ∀ L : List (Fin 2), 0 < stackCode B dig L := by
  intro L
  induction L with
  | nil =>
      exact div_pos (by exact_mod_cast bot_pos B hB) (base_pos_rat B hB)
  | cons a L ih =>
      exact div_pos (add_pos_of_nonneg_of_pos (by positivity) ih) (base_pos_rat B hB)

/--
Sharp global upper bound for this finite-list recursion.  The maximum legal
code is the empty stack bottom value `(B - 2) / B`; nonempty stacks are below it.
-/
theorem stackCode_le_bot_div_base (B : ℕ) (hB : 4 ≤ B) (dig : Fin 2 → ℕ)
    (hdig : ∀ a, dig a < bot B) :
    ∀ L : List (Fin 2), stackCode B dig L ≤ ((bot B : ℕ) : ℚ) / (B : ℚ) := by
  intro L
  induction L with
  | nil => rfl
  | cons a L ih =>
      have hBpos := base_pos_rat B hB
      have htail_lt_one : stackCode B dig L < 1 :=
        lt_of_le_of_lt ih (bot_div_base_lt_one_rat B hB)
      have hdig_le : (dig a : ℚ) ≤ ((bot B : ℕ) : ℚ) - 1 := by
        have hle : dig a + 1 ≤ bot B := Nat.succ_le_of_lt (hdig a)
        have hleQ : ((dig a + 1 : ℕ) : ℚ) ≤ ((bot B : ℕ) : ℚ) := by
          exact_mod_cast hle
        norm_num at hleQ ⊢
        linarith
      rw [stackCode]
      rw [div_le_div_iff₀ hBpos hBpos]
      nlinarith

/-- Legal stack codes lie below the missing digit threshold `(B - 1) / B`. -/
theorem stackCode_lt_missing_digit (B : ℕ) (hB : 4 ≤ B)
    (dig : Fin 2 → ℕ) (hdig : ∀ a, dig a < bot B) (L : List (Fin 2)) :
    stackCode B dig L < ((B - 1 : ℕ) : ℚ) / (B : ℚ) := by
  have hle := stackCode_le_bot_div_base B hB dig hdig L
  have hlt : ((bot B : ℕ) : ℚ) / (B : ℚ) <
      ((B - 1 : ℕ) : ℚ) / (B : ℚ) := by
    have hBpos := base_pos_rat B hB
    unfold bot
    have hn : B - 2 < B - 1 := by omega
    exact div_lt_div_of_pos_right (by exact_mod_cast hn : ((B - 2 : ℕ) : ℚ) <
      ((B - 1 : ℕ) : ℚ)) hBpos
  exact lt_of_le_of_lt hle hlt

/-- Range statement in the form used by the missing-digit gap argument. -/
theorem stackCode_mem_gap_range (B : ℕ) (hB : 4 ≤ B)
    (dig : Fin 2 → ℕ) (hdig : ∀ a, dig a < bot B) (L : List (Fin 2)) :
    0 < stackCode B dig L ∧
      stackCode B dig L ≤ ((bot B : ℕ) : ℚ) / (B : ℚ) ∧
      stackCode B dig L < ((B - 1 : ℕ) : ℚ) / (B : ℚ) := by
  exact ⟨stackCode_pos B hB dig hdig L,
    stackCode_le_bot_div_base B hB dig hdig L,
    stackCode_lt_missing_digit B hB dig hdig L⟩

/-! ## Explicit binary top separation -/

private theorem bit_zero_or_one (a : Fin 2) : bitDigit a = 0 ∨ bitDigit a = 1 := by
  fin_cases a <;> simp [bitDigit]

private theorem bitDigit_ne_iff {a a' : Fin 2} :
    a ≠ a' → bitDigit a ≠ bitDigit a' := by
  intro h hdig
  fin_cases a <;> fin_cases a' <;> simp [bitDigit] at h hdig

/--
Different binary top symbols are separated by an explicit positive gap.  The
constant is conservative and is the one used by `localExtract`.
-/
theorem stackCode_cons_ne_sep (B : ℕ) (hB : 4 ≤ B)
    {a a' : Fin 2} (hne : a ≠ a') (L L' : List (Fin 2)) :
    (2 : ℚ) / ((B : ℚ) ^ 2) ≤
      |stackCode B bitDigit (a :: L) - stackCode B bitDigit (a' :: L')| := by
  have hBpos := base_pos_rat B hB
  have hdig := bitDigit_ne_iff hne
  have hLpos := stackCode_pos B hB bitDigit (bitDigit_lt_bot B hB) L
  have hL'pos := stackCode_pos B hB bitDigit (bitDigit_lt_bot B hB) L'
  have hLle := stackCode_le_bot_div_base B hB bitDigit (bitDigit_lt_bot B hB) L
  have hL'le := stackCode_le_bot_div_base B hB bitDigit (bitDigit_lt_bot B hB) L'
  have hbot : (((bot B : ℕ) : ℚ) / (B : ℚ)) = ((B : ℚ) - 2) / (B : ℚ) := by
    unfold bot
    have hsub : ((B - 2 : ℕ) : ℚ) = (B : ℚ) - 2 := by
      norm_num [Nat.cast_sub (by omega : 2 ≤ B)]
    rw [hsub]
  have hgap : (1 : ℚ) - ((bot B : ℕ) : ℚ) / (B : ℚ) = (2 : ℚ) / (B : ℚ) := by
    rw [hbot]
    field_simp [ne_of_gt hBpos]
    ring
  fin_cases a
  · fin_cases a'
    · exact False.elim (hne rfl)
    · have htail : (2 : ℚ) / (B : ℚ) ≤
          (1 : ℚ) + stackCode B bitDigit L' - stackCode B bitDigit L := by
        rw [← hgap]
        nlinarith
      have hmain : (2 : ℚ) / ((B : ℚ) ^ 2) ≤
          ((1 : ℚ) + stackCode B bitDigit L' - stackCode B bitDigit L) /
            (B : ℚ) := by
        calc
          (2 : ℚ) / ((B : ℚ) ^ 2) = ((2 : ℚ) / (B : ℚ)) / (B : ℚ) := by
            field_simp [ne_of_gt hBpos]
          _ ≤ ((1 : ℚ) + stackCode B bitDigit L' - stackCode B bitDigit L) /
              (B : ℚ) := div_le_div_of_nonneg_right htail (le_of_lt hBpos)
      have hneg : (2 : ℚ) / ((B : ℚ) ^ 2) ≤
          -(stackCode B bitDigit (⟨0, by decide⟩ :: L) -
            stackCode B bitDigit (⟨1, by decide⟩ :: L')) := by
        rw [stackCode, stackCode]
        simp [bitDigit]
        field_simp [ne_of_gt hBpos] at hmain ⊢
        linarith
      exact le_trans hneg (neg_le_abs _)
  · fin_cases a'
    · have htail : (2 : ℚ) / (B : ℚ) ≤
          (1 : ℚ) + stackCode B bitDigit L - stackCode B bitDigit L' := by
        rw [← hgap]
        nlinarith
      have hmain : (2 : ℚ) / ((B : ℚ) ^ 2) ≤
          ((1 : ℚ) + stackCode B bitDigit L - stackCode B bitDigit L') /
            (B : ℚ) := by
        calc
          (2 : ℚ) / ((B : ℚ) ^ 2) = ((2 : ℚ) / (B : ℚ)) / (B : ℚ) := by
            field_simp [ne_of_gt hBpos]
          _ ≤ ((1 : ℚ) + stackCode B bitDigit L - stackCode B bitDigit L') /
              (B : ℚ) := div_le_div_of_nonneg_right htail (le_of_lt hBpos)
      have hpos : (2 : ℚ) / ((B : ℚ) ^ 2) ≤
          stackCode B bitDigit (⟨1, by decide⟩ :: L) -
            stackCode B bitDigit (⟨0, by decide⟩ :: L') := by
        rw [stackCode, stackCode]
        simp [bitDigit]
        field_simp [ne_of_gt hBpos] at hmain ⊢
        linarith
      exact le_trans hpos (le_abs_self _)
    · exact False.elim (hne rfl)

/-! ## Four-coordinate configuration encoding -/

/-- Four-coordinate rational configuration encoding `(X, Sigma, Y, Q)`. -/
def confEnc (B : ℕ) (ctrlCode : ℤ) (left right : List (Fin 2)) :
    Fin 4 → ℚ :=
  fun i =>
    if i = leftStackCoord then
      stackCode B bitDigit left
    else if i = symbolCoord then
      0
    else if i = rightStackCoord then
      stackCode B bitDigit right
    else
      (ctrlCode : ℚ)

@[simp] theorem confEnc_left (B : ℕ) (q : ℤ) (L R : List (Fin 2)) :
    confEnc B q L R leftStackCoord = stackCode B bitDigit L := by
  simp [confEnc]

@[simp] theorem confEnc_symbol (B : ℕ) (q : ℤ) (L R : List (Fin 2)) :
    confEnc B q L R symbolCoord = 0 := by
  simp [confEnc, leftStackCoord, symbolCoord]

@[simp] theorem confEnc_right (B : ℕ) (q : ℤ) (L R : List (Fin 2)) :
    confEnc B q L R rightStackCoord = stackCode B bitDigit R := by
  simp [confEnc, leftStackCoord, symbolCoord, rightStackCoord]

@[simp] theorem confEnc_state (B : ℕ) (q : ℤ) (L R : List (Fin 2)) :
    confEnc B q L R stateCoord = (q : ℚ) := by
  simp [confEnc, leftStackCoord, symbolCoord, rightStackCoord, stateCoord]

/-! ## Local extraction -/

/-- Exact top-of-stack view. -/
def stackTop : List (Fin 2) → Option (Fin 2)
  | [] => none
  | a :: _ => some a

/-- The exact local view carried by the encoding layer. -/
def localView (_B : ℕ) (ctrlCode : ℤ) (left right : List (Fin 2)) :
    ℤ × Option (Fin 2) × Option (Fin 2) :=
  (ctrlCode, stackTop left, stackTop right)

/-- Sup-coordinate tube around a rational encoding point. -/
def supTube (r : ℝ) (Z : Fin 4 → ℝ) (E : Fin 4 → ℚ) : Prop :=
  ∀ i, |Z i - (E i : ℝ)| ≤ r

/-- Extraction radius supported by the binary stack gaps. -/
def rLE (B : ℕ) : ℚ := 1 / (4 * (B : ℚ) ^ 2)

/-- First threshold: separates top digit `0` from top digit `1`. -/
def stackThresh01 (B : ℕ) : ℝ := ((B : ℝ) - 1) / ((B : ℝ) ^ 2)

/-- Second threshold: separates nonempty top digit `1` from the empty marker. -/
def stackThreshEmpty (B : ℕ) : ℝ :=
  ((((1 : ℝ) / (B : ℝ)) + (((B : ℝ) - 2) / ((B : ℝ) ^ 2))) +
    (((B : ℝ) - 2) / (B : ℝ))) / 2

private theorem zero_upper_plus_r_lt_thresh01 (B : ℕ) (hB : 4 ≤ B) :
    ((B : ℝ) - 2) / ((B : ℝ) ^ 2) + ((rLE B : ℚ) : ℝ) <
      stackThresh01 B := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  unfold stackThresh01 rLE
  norm_num
  field_simp [ne_of_gt hBpos]
  nlinarith

private theorem thresh01_plus_r_le_one_div (B : ℕ) (hB : 4 ≤ B) :
    stackThresh01 B + ((rLE B : ℚ) : ℝ) ≤ 1 / (B : ℝ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  unfold stackThresh01 rLE
  norm_num
  field_simp [ne_of_gt hBpos]
  nlinarith

private theorem upper1_plus_r_lt_threshEmpty (B : ℕ) (hB : 4 ≤ B) :
    (1 / (B : ℝ) + ((B : ℝ) - 2) / ((B : ℝ) ^ 2)) +
        ((rLE B : ℚ) : ℝ) < stackThreshEmpty B := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  have hB4 : (4 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  unfold stackThreshEmpty rLE
  norm_num
  field_simp [ne_of_gt hBpos]
  nlinarith [sq_nonneg ((B : ℝ) - 4)]

private theorem stackThresh01_lt_empty (B : ℕ) (hB : 4 ≤ B) :
    stackThresh01 B < stackThreshEmpty B := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  have hB4 : (4 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  unfold stackThresh01 stackThreshEmpty
  field_simp [ne_of_gt hBpos]
  nlinarith [sq_nonneg ((B : ℝ) - 4)]

private theorem threshEmpty_plus_r_le_empty (B : ℕ) (hB : 4 ≤ B) :
    stackThreshEmpty B + ((rLE B : ℚ) : ℝ) ≤ ((B : ℝ) - 2) / (B : ℝ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  have hB4 : (4 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  unfold stackThreshEmpty rLE
  norm_num
  field_simp [ne_of_gt hBpos]
  nlinarith [sq_nonneg ((B : ℝ) - 4)]

/-- Stack-top extraction by interval thresholds. -/
def extractStackTop (B : ℕ) (x : ℝ) : Option (Fin 2) :=
  if stackThreshEmpty B ≤ x then
    none
  else if x < stackThresh01 B then
    some ⟨0, by decide⟩
  else
    some ⟨1, by decide⟩

/-- Integer rounding used for the control coordinate. -/
def roundInt (x : ℝ) : ℤ := ⌊x + (1 / 2 : ℝ)⌋

/--
Local extractor for the four-coordinate encoding.  It returns `none` for
bases below the supported range; otherwise it rounds `Q` and threshold-tests
the two stack coordinates.
-/
def localExtract (B : ℕ) (_r_LE : ℚ) (Z : Fin 4 → ℝ) :
    Option (ℤ × Option (Fin 2) × Option (Fin 2)) :=
  if 4 ≤ B then
    some (roundInt (Z stateCoord),
      extractStackTop B (Z leftStackCoord),
      extractStackTop B (Z rightStackCoord))
  else
    none

private theorem roundInt_of_abs_le_quarter (q : ℤ) {x : ℝ}
    (hx : |x - (q : ℝ)| ≤ (1 / 4 : ℝ)) :
    roundInt x = q := by
  unfold roundInt
  rw [Int.floor_eq_iff]
  constructor
  · nlinarith [abs_le.mp hx |>.1]
  · nlinarith [abs_le.mp hx |>.2]

private theorem rLE_pos_real (B : ℕ) (hB : 4 ≤ B) : (0 : ℝ) < (rLE B : ℚ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  unfold rLE
  positivity

private theorem rLE_le_quarter (B : ℕ) (hB : 4 ≤ B) :
    ((rLE B : ℚ) : ℝ) ≤ (1 / 4 : ℝ) := by
  have hsq : (1 : ℝ) ≤ (B : ℝ) ^ 2 := by
    have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 4) hB)
    nlinarith [sq_nonneg ((B : ℝ) - 1)]
  unfold rLE
  norm_num
  simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsq

private theorem stackCode_nil_real (B : ℕ) (hB : 4 ≤ B) :
    ((stackCode B bitDigit [] : ℚ) : ℝ) = ((B : ℝ) - 2) / (B : ℝ) := by
  simp [stackCode, bot, Nat.cast_sub (by omega : 2 ≤ B)]

private theorem stackCode_cons0_le (B : ℕ) (hB : 4 ≤ B)
    (L : List (Fin 2)) :
    ((stackCode B bitDigit (⟨0, by decide⟩ :: L) : ℚ) : ℝ) ≤
      ((B : ℝ) - 2) / ((B : ℝ) ^ 2) := by
  have htail := stackCode_le_bot_div_base B hB bitDigit (bitDigit_lt_bot B hB) L
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  rw [stackCode]
  simp [bitDigit]
  have htailR : ((stackCode B bitDigit L : ℚ) : ℝ) ≤ ((B : ℝ) - 2) / (B : ℝ) := by
    have hbot : (((bot B : ℕ) : ℚ) / (B : ℚ) : ℝ) =
        ((B : ℝ) - 2) / (B : ℝ) := by
      unfold bot
      have hsub : ((B - 2 : ℕ) : ℝ) = (B : ℝ) - 2 := by
        norm_num [Nat.cast_sub (by omega : 2 ≤ B)]
      norm_num [hsub]
    exact le_trans (by exact_mod_cast htail) (le_of_eq hbot)
  calc
    ((stackCode B bitDigit L : ℚ) : ℝ) / (B : ℝ)
        ≤ (((B : ℝ) - 2) / (B : ℝ)) / (B : ℝ) := by
          exact div_le_div_of_nonneg_right htailR (le_of_lt hBpos)
    _ = ((B : ℝ) - 2) / ((B : ℝ) ^ 2) := by ring_nf

private theorem stackCode_cons1_bounds (B : ℕ) (hB : 4 ≤ B)
    (L : List (Fin 2)) :
    (1 / (B : ℝ) ≤
        ((stackCode B bitDigit (⟨1, by decide⟩ :: L) : ℚ) : ℝ)) ∧
      ((stackCode B bitDigit (⟨1, by decide⟩ :: L) : ℚ) : ℝ) ≤
        1 / (B : ℝ) + ((B : ℝ) - 2) / ((B : ℝ) ^ 2) := by
  have htail_pos := stackCode_pos B hB bitDigit (bitDigit_lt_bot B hB) L
  have htail_le := stackCode_le_bot_div_base B hB bitDigit (bitDigit_lt_bot B hB) L
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  rw [stackCode]
  simp [bitDigit]
  constructor
  · have htail_nonneg : (0 : ℝ) ≤ ((stackCode B bitDigit L : ℚ) : ℝ) := by
      exact le_of_lt (by exact_mod_cast htail_pos)
    have hcalc : (1 : ℝ) / (B : ℝ) ≤
        (1 + ((stackCode B bitDigit L : ℚ) : ℝ)) / (B : ℝ) := by
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hBpos)
    simpa [one_div] using hcalc
  · have htailR : ((stackCode B bitDigit L : ℚ) : ℝ) ≤ ((B : ℝ) - 2) / (B : ℝ) := by
      have hbot : ((((bot B : ℕ) : ℚ) / (B : ℚ) : ℝ) =
          ((B : ℝ) - 2) / (B : ℝ)) := by
        unfold bot
        have hsub : ((B - 2 : ℕ) : ℝ) = (B : ℝ) - 2 := by
          norm_num [Nat.cast_sub (by omega : 2 ≤ B)]
        norm_num [hsub]
      exact le_trans (by exact_mod_cast htail_le) (le_of_eq hbot)
    change (1 + ((stackCode B bitDigit L : ℚ) : ℝ)) / (B : ℝ) ≤
      (B : ℝ)⁻¹ + ((B : ℝ) - 2) / ((B : ℝ) ^ 2)
    calc
      (1 + ((stackCode B bitDigit L : ℚ) : ℝ)) / (B : ℝ)
          ≤ (1 + ((B : ℝ) - 2) / (B : ℝ)) / (B : ℝ) := by
        exact div_le_div_of_nonneg_right
          (by simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left htailR 1)
          (le_of_lt hBpos)
      _ = (B : ℝ)⁻¹ + ((B : ℝ) - 2) / ((B : ℝ) ^ 2) := by ring_nf

private theorem extractStackTop_correct (B : ℕ) (hB : 4 ≤ B)
    (L : List (Fin 2)) {x : ℝ}
    (hx : |x - ((stackCode B bitDigit L : ℚ) : ℝ)| ≤ ((rLE B : ℚ) : ℝ)) :
    extractStackTop B x = stackTop L := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hB)
  cases L with
  | nil =>
      have hcode := stackCode_nil_real B hB
      have hxlow : stackThreshEmpty B ≤ x := by
        have hx1 := abs_le.mp hx |>.1
        rw [hcode] at hx1
        have hmargin := threshEmpty_plus_r_le_empty B hB
        linarith
      simp [extractStackTop, hxlow, stackTop]
  | cons a L =>
      fin_cases a
      · have hcode_le := stackCode_cons0_le B hB L
        have hxupper : x < stackThresh01 B := by
          have hx2 := abs_le.mp hx |>.2
          have hmargin := zero_upper_plus_r_lt_thresh01 B hB
          linarith
        have hxempty : ¬ stackThreshEmpty B ≤ x := by
          intro hempty
          have hth := stackThresh01_lt_empty B hB
          linarith
        simp [extractStackTop, hxempty, hxupper, stackTop]
      · have hbounds := stackCode_cons1_bounds B hB L
        have hxlower01 : stackThresh01 B ≤ x := by
          have hx1 := abs_le.mp hx |>.1
          have hmargin := thresh01_plus_r_le_one_div B hB
          linarith
        have hxempty : ¬ stackThreshEmpty B ≤ x := by
          intro hempty
          have hx2 := abs_le.mp hx |>.2
          have hmargin := upper1_plus_r_lt_threshEmpty B hB
          linarith
        have hnotlt : ¬ x < stackThresh01 B := not_lt.mpr hxlower01
        simp [extractStackTop, hxempty, hnotlt, stackTop]

/--
Tube correctness for local extraction.  The radius is the explicit rational
`rLE B = 1 / (4 * B^2)`, which is below both the stack half-gap and the
integer rounding margin.
-/
theorem localExtract_tube (B : ℕ) (hB : 4 ≤ B) (ctrlCode : ℤ)
    (left right : List (Fin 2)) (Z : Fin 4 → ℝ)
    (hZ : supTube ((rLE B : ℚ) : ℝ) Z (confEnc B ctrlCode left right)) :
    localExtract B (rLE B) Z = some (localView B ctrlCode left right) := by
  have hstate_abs : |Z stateCoord - (ctrlCode : ℝ)| ≤ (1 / 4 : ℝ) := by
    have hz := hZ stateCoord
    simpa using le_trans (by simpa using hz) (rLE_le_quarter B hB)
  have hround : roundInt (Z stateCoord) = ctrlCode :=
    roundInt_of_abs_le_quarter ctrlCode hstate_abs
  have hleft : extractStackTop B (Z leftStackCoord) = stackTop left := by
    apply extractStackTop_correct B hB left
    simpa using hZ leftStackCoord
  have hright : extractStackTop B (Z rightStackCoord) = stackTop right := by
    apply extractStackTop_correct B hB right
    simpa using hZ rightStackCoord
  simp [localExtract, hB, hround, hleft, hright, localView]

end

end Ripple.BoundedUniversality.BGP
