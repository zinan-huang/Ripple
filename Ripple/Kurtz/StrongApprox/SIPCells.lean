/-
  Ripple.Kurtz.StrongApprox.SIPCells — the coarse-block layout of the unit cells for the discrete
  strong invariance principle: annulus `r` is the cell range `[4^r − 1, 4^{r+1} − 1)`, cut into
  `3·2^r` blocks of length `2^r`; block `(r, s)` starts at `4^r − 1 + s·2^r`.

  The partition of `[4^r, 4^{r+1})` into `3H` blocks of length `H = 2^r` is shifted by one cell so
  that cell `0` is the first cell of annulus 0.
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

/-- Annulus of a cell: the `r` with `4^r ≤ i + 1 < 4^{r+1}`. -/
def cellAnn (i : ℕ) : ℕ := Nat.log 4 (i + 1)

/-- First cell of annulus `r`. -/
def annStart (r : ℕ) : ℕ := 4 ^ r - 1

/-- First cell of block `(r, s)`. -/
def blockStart (r s : ℕ) : ℕ := annStart r + s * 2 ^ r

/-- Offset of a cell inside its annulus. -/
def cellOff (i : ℕ) : ℕ := i + 1 - 4 ^ cellAnn i

/-- Block index of a cell inside its annulus. -/
def cellBlk (i : ℕ) : ℕ := cellOff i / 2 ^ cellAnn i

/-- Position of a cell inside its block. -/
def cellPos (i : ℕ) : ℕ := cellOff i % 2 ^ cellAnn i

theorem four_pow_eq (r : ℕ) : (4:ℕ) ^ r = 2 ^ r * 2 ^ r := by
  rw [← mul_pow]
  norm_num

theorem one_le_four_pow (r : ℕ) : 1 ≤ 4 ^ r := Nat.one_le_pow _ _ (by norm_num)

theorem annStart_zero : annStart 0 = 0 := by simp [annStart]

theorem blockStart_zero (r : ℕ) : blockStart r 0 = annStart r := by simp [blockStart]

theorem blockStart_succ (r s : ℕ) : blockStart r (s + 1) = blockStart r s + 2 ^ r := by
  unfold blockStart
  rw [Nat.succ_mul, add_assoc]

/-- The annulus `r + 1` starts where the last block of annulus `r` ends. -/
theorem annStart_succ (r : ℕ) : annStart (r + 1) = blockStart r (3 * 2 ^ r) := by
  unfold blockStart annStart
  rw [pow_succ, mul_assoc, ← four_pow_eq]
  have := one_le_four_pow r
  omega

/-! ### Decoding a cell -/

theorem cellAnn_spec (i : ℕ) : 4 ^ cellAnn i ≤ i + 1 ∧ i + 1 < 4 ^ (cellAnn i + 1) :=
  ⟨Nat.pow_log_le_self 4 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _⟩

theorem cellOff_lt (i : ℕ) : cellOff i < 3 * 4 ^ cellAnn i := by
  have h := cellAnn_spec i
  rw [pow_succ] at h
  unfold cellOff
  omega

theorem cellPos_lt (i : ℕ) : cellPos i < 2 ^ cellAnn i :=
  Nat.mod_lt _ (by positivity)

theorem cellBlk_lt (i : ℕ) : cellBlk i < 3 * 2 ^ cellAnn i := by
  unfold cellBlk
  rw [Nat.div_lt_iff_lt_mul (by positivity), mul_assoc, ← four_pow_eq]
  exact cellOff_lt i

/-- Every cell is `blockStart (cellAnn i) (cellBlk i) + cellPos i`. -/
theorem blockStart_cell (i : ℕ) : blockStart (cellAnn i) (cellBlk i) + cellPos i = i := by
  have h := Nat.div_add_mod (cellOff i) (2 ^ cellAnn i)
  have h1 := (cellAnn_spec i).1
  have hoff : cellOff i = i + 1 - 4 ^ cellAnn i := rfl
  unfold blockStart annStart cellBlk cellPos
  rw [mul_comm] at h
  rw [add_assoc, h, hoff]
  have := one_le_four_pow (cellAnn i)
  omega

theorem cellAnn_mono {k n : ℕ} (h : k ≤ n) : cellAnn k ≤ cellAnn n :=
  Nat.log_mono_right (by omega)

theorem le_cellAnn_of_annStart_le {r k : ℕ} (h : annStart r ≤ k) : r ≤ cellAnn k := by
  unfold annStart at h
  have := one_le_four_pow r
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

/-! ### Encoding a cell -/

theorem cellAnn_blockStart {r s p : ℕ} (hs : s < 3 * 2 ^ r) (hp : p < 2 ^ r) :
    cellAnn (blockStart r s + p) = r := by
  have h4 : (4:ℕ) ^ r = 2 ^ r * 2 ^ r := four_pow_eq r
  have h1 : 1 ≤ 4 ^ r := one_le_four_pow r
  have hsH : s * 2 ^ r + 2 ^ r ≤ 3 * 4 ^ r := by
    have := Nat.mul_le_mul_right (2 ^ r) (Nat.succ_le_of_lt hs)
    rw [Nat.succ_mul, mul_assoc, ← h4] at this
    exact this
  unfold cellAnn blockStart annStart
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
  constructor
  · omega
  · rw [pow_succ]
    omega

theorem cellOff_blockStart {r s p : ℕ} (hs : s < 3 * 2 ^ r) (hp : p < 2 ^ r) :
    cellOff (blockStart r s + p) = s * 2 ^ r + p := by
  unfold cellOff
  rw [cellAnn_blockStart hs hp]
  unfold blockStart annStart
  have := one_le_four_pow r
  omega

theorem cellBlk_blockStart {r s p : ℕ} (hs : s < 3 * 2 ^ r) (hp : p < 2 ^ r) :
    cellBlk (blockStart r s + p) = s := by
  unfold cellBlk
  rw [cellOff_blockStart hs hp, cellAnn_blockStart hs hp, mul_comm,
    Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hp, add_zero]

theorem cellPos_blockStart {r s p : ℕ} (hs : s < 3 * 2 ^ r) (hp : p < 2 ^ r) :
    cellPos (blockStart r s + p) = p := by
  unfold cellPos
  rw [cellOff_blockStart hs hp, cellAnn_blockStart hs hp, mul_comm, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hp]

end Ripple.Kurtz.StrongApprox
