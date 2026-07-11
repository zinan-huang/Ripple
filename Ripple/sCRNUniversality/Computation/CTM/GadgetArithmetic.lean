import Ripple.sCRNUniversality.Computation.CTM.FourPhaseGadgetInterface

namespace Ripple.sCRNUniversality

namespace CTM

namespace FourPhaseEncoding

theorem le_maxTape_of_IsBase3BoolTape {s m : Nat}
    (h : Encoding.IsBase3BoolTape (s + 1) m) :
    m <= maxTape s := by
  have hlt : m < 3 ^ (s + 1) := h.lt_pow
  have hpos : 0 < 3 ^ (s + 1) := Nat.pow_pos (by norm_num)
  unfold maxTape
  omega

theorem maxTape_sub_eraseMSBWith_eq_add {s m : Nat}
    {r : Bool} (h : Encoding.IsBase3BoolTape (s + 1) m)
    (hr : r = Encoding.readMSB? s m) :
    maxTape s - Encoding.eraseMSBWith s r m =
      maxTape s - m + Encoding.bitDigit r * 3 ^ s := by
  have hDigit :
      Encoding.bitDigit r * 3 ^ s <= m :=
    Encoding.bitDigit_mul_pow_le_of_IsBase3BoolTape_read h hr
  have hMax : m <= maxTape s :=
    le_maxTape_of_IsBase3BoolTape h
  unfold Encoding.eraseMSBWith
  omega

theorem maxTape_sub_eraseMSB_eq_add_readDigit {s m : Nat}
    (h : Encoding.IsBase3BoolTape (s + 1) m) :
    maxTape s - Encoding.eraseMSB s m =
      maxTape s - m + Encoding.bitDigit (Encoding.readMSB? s m) * 3 ^ s := by
  simpa [Encoding.eraseMSB] using
    maxTape_sub_eraseMSBWith_eq_add (s := s) (m := m)
      (r := Encoding.readMSB? s m) h rfl

theorem writeLSB_shiftTail_le_maxTape_of_lt_pow {s m : Nat}
    (h : m < 3 ^ s) (b : Bool) :
    Encoding.writeLSB (Encoding.shiftTail m) b <= maxTape s := by
  unfold Encoding.writeLSB Encoding.shiftTail maxTape
  rw [pow_succ]
  cases b <;> simp [Encoding.bitDigit] <;> omega

theorem shiftTail_le_maxTape_of_lt_pow {s m : Nat}
    (h : m < 3 ^ s) :
    Encoding.shiftTail m <= maxTape s := by
  have hFit := writeLSB_shiftTail_le_maxTape_of_lt_pow h false
  unfold Encoding.writeLSB at hFit
  simp [Encoding.bitDigit] at hFit
  omega

theorem two_mul_le_tapeBar_of_lt_pow {s m : Nat}
    (h : m < 3 ^ s) :
    2 * m <= maxTape s - m := by
  have hShift : Encoding.shiftTail m <= maxTape s :=
    shiftTail_le_maxTape_of_lt_pow h
  unfold Encoding.shiftTail at hShift
  omega

theorem maxTape_sub_shiftTail_eq_sub {s m : Nat}
    (h : m < 3 ^ s) :
    maxTape s - Encoding.shiftTail m =
      maxTape s - m - 2 * m := by
  have hShift : Encoding.shiftTail m <= maxTape s :=
    shiftTail_le_maxTape_of_lt_pow h
  unfold Encoding.shiftTail at hShift
  unfold Encoding.shiftTail
  omega

theorem writeLSB_shiftTail_le_maxTape_of_erasedBase3 {s m : Nat}
    {r : Bool} (h : Encoding.IsBase3BoolTape (s + 1) m)
    (hr : r = Encoding.readMSB? s m) (b : Bool) :
    Encoding.writeLSB (Encoding.shiftTail (Encoding.eraseMSBWith s r m)) b
      <= maxTape s := by
  exact writeLSB_shiftTail_le_maxTape_of_lt_pow
    (Encoding.eraseMSBWith_lt_pow_of_IsBase3BoolTape h hr) b

theorem writeLSB_le_maxTape_of_shifted {s m : Nat}
    (h : Encoding.IsShiftedBase3BoolTape s m) (b : Bool) :
    Encoding.writeLSB m b <= maxTape s := by
  rcases h with ⟨tail, hTail, rfl⟩
  exact writeLSB_shiftTail_le_maxTape_of_lt_pow hTail.lt_pow b

theorem bitDigit_le_tapeBar_of_shifted {s m : Nat}
    (h : Encoding.IsShiftedBase3BoolTape s m) (b : Bool) :
    Encoding.bitDigit b <= maxTape s - m := by
  have hFit : Encoding.writeLSB m b <= maxTape s :=
    writeLSB_le_maxTape_of_shifted h b
  unfold Encoding.writeLSB at hFit
  omega

theorem maxTape_sub_writeLSB_eq_sub {s m : Nat} {b : Bool}
    (_hFit : Encoding.writeLSB m b <= maxTape s) :
    maxTape s - Encoding.writeLSB m b =
      maxTape s - m - Encoding.bitDigit b := by
  unfold Encoding.writeLSB
  omega

theorem maxTape_sub_writeLSB_eq_sub_of_shifted {s m : Nat}
    (h : Encoding.IsShiftedBase3BoolTape s m) (b : Bool) :
    maxTape s - Encoding.writeLSB m b =
      maxTape s - m - Encoding.bitDigit b :=
  maxTape_sub_writeLSB_eq_sub
    (writeLSB_le_maxTape_of_shifted h b)

end FourPhaseEncoding

end CTM

end Ripple.sCRNUniversality
