import Ripple.BoundedUniversality.BGP.BernsteinSeparator

noncomputable section

namespace Ripple.BoundedUniversality.BGP

instance : Primcodable ℤ := Primcodable.ofDenumerable ℤ

@[simp] lemma int_ofNat_even_code (m : ℕ) :
    Denumerable.ofNat ℤ (2 * m) = (m : ℤ) := by
  rw [show Denumerable.ofNat ℤ (2 * m) = Equiv.intEquivNat.symm (2 * m) from rfl]
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat_symm_apply, Nat.div2_bit0]

@[simp] lemma int_ofNat_odd_code (m : ℕ) :
    Denumerable.ofNat ℤ (2 * m + 1) = Int.negSucc m := by
  rw [show Denumerable.ofNat ℤ (2 * m + 1) =
    Equiv.intEquivNat.symm (2 * m + 1) from rfl]
  simp [Equiv.intEquivNat, Equiv.intEquivNatSumNat,
    Equiv.natSumNatEquivNat_symm_apply]

-- 4.30: downstream goals surface the decode in the defeq `Equiv.intEquivNat.symm` form
-- (not the `Denumerable.ofNat ℤ` form), so the two lemmas above no longer fire as `simp`.
-- These `Equiv.intEquivNat.symm`-form mirrors restore the rewrites.
@[simp] lemma intEquivNat_symm_two_mul (m : ℕ) :
    Equiv.intEquivNat.symm (2 * m) = (m : ℤ) := int_ofNat_even_code m

@[simp] lemma intEquivNat_symm_two_mul_add_one (m : ℕ) :
    Equiv.intEquivNat.symm (2 * m + 1) = Int.negSucc m := int_ofNat_odd_code m

@[simp] lemma int_encode_natCast (m : ℕ) :
    Encodable.encode (m : ℤ) = 2 * m := rfl

@[simp] lemma int_encode_negSucc (m : ℕ) :
    Encodable.encode (Int.negSucc m) = 2 * m + 1 := rfl

theorem primrec_int_natAbs : Primrec (fun z : ℤ => z.natAbs) := by
  rw [Primrec.ofNat_iff]
  refine (Primrec.cond Primrec.nat_bodd
    (Primrec.succ.comp Primrec.nat_div2) Primrec.nat_div2).of_eq ?_
  intro n
  have hn := (Nat.bit_bodd_div2 n).symm
  cases hb : n.bodd
  · rw [hn, hb]
    simp [Nat.bit, Nat.div2_bit0]
  · rw [hn, hb]
    simp [Nat.bit]

theorem primrec_int_ofNat : Primrec (fun n : ℕ => (n : ℤ)) := by
  rw [← Primrec.encode_iff]
  simpa using Primrec.nat_double

theorem computable_int_natAbs : Computable (fun z : ℤ => z.natAbs) :=
  primrec_int_natAbs.to_comp

theorem computable_int_ofNat : Computable (fun n : ℕ => (n : ℤ)) :=
  primrec_int_ofNat.to_comp

private def intAddCode (m n : ℕ) : ℕ :=
  let a := m.div2
  let b := n.div2
  if m.bodd then
    if n.bodd then
      2 * (a + b + 1) + 1
    else if a < b then
      2 * (b - a - 1)
    else
      2 * (a - b) + 1
  else
    if n.bodd then
      if b < a then
        2 * (a - b - 1)
      else
        2 * (b - a) + 1
    else
      2 * (a + b)

private def intMulCode (m n : ℕ) : ℕ :=
  let a := if m.bodd then m.div2 + 1 else m.div2
  let b := if n.bodd then n.div2 + 1 else n.div2
  let mag := a * b
  if m.bodd = n.bodd then
    2 * mag
  else if mag = 0 then
    0
  else
    2 * (mag - 1) + 1

private theorem primrec2_intAddCode : Primrec₂ intAddCode := by
  unfold intAddCode
  let a : ℕ → ℕ → ℕ := fun m _ => m.div2
  let b : ℕ → ℕ → ℕ := fun _ n => n.div2
  have ha : Primrec₂ a := Primrec.nat_div2.comp₂ Primrec₂.left
  have hb : Primrec₂ b := Primrec.nat_div2.comp₂ Primrec₂.right
  have hma : Primrec₂ (fun m n => a m n + b m n) := Primrec.nat_add.comp₂ ha hb
  have hsameEven : Primrec₂ (fun m n => 2 * (a m n + b m n)) :=
    Primrec.nat_double.comp₂ hma
  have hsameOdd : Primrec₂ (fun m n => 2 * (a m n + b m n + 1) + 1) :=
    Primrec.nat_double_succ.comp₂ (Primrec.succ.comp₂ hma)
  have hba : Primrec₂ (fun m n => b m n - a m n) := Primrec.nat_sub.comp₂ hb ha
  have hab : Primrec₂ (fun m n => a m n - b m n) := Primrec.nat_sub.comp₂ ha hb
  have hbaPred : Primrec₂ (fun m n => b m n - a m n - 1) :=
    Primrec.nat_sub.comp₂ hba (Primrec₂.const 1)
  have habPred : Primrec₂ (fun m n => a m n - b m n - 1) :=
    Primrec.nat_sub.comp₂ hab (Primrec₂.const 1)
  have hEvenOddLt : Primrec₂ (fun m n => 2 * (a m n - b m n - 1)) :=
    Primrec.nat_double.comp₂ habPred
  have hEvenOddGe : Primrec₂ (fun m n => 2 * (b m n - a m n) + 1) :=
    Primrec.nat_double_succ.comp₂ hba
  have hOddEvenLt : Primrec₂ (fun m n => 2 * (b m n - a m n - 1)) :=
    Primrec.nat_double.comp₂ hbaPred
  have hOddEvenGe : Primrec₂ (fun m n => 2 * (a m n - b m n) + 1) :=
    Primrec.nat_double_succ.comp₂ hab
  have hmOdd : Primrec₂ (fun m _ : ℕ => m.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.left
  have hnOdd : Primrec₂ (fun _ n : ℕ => n.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.right
  have hblta : PrimrecPred (fun p : ℕ × ℕ => b p.1 p.2 < a p.1 p.2) :=
    Primrec.nat_lt.comp hb ha
  have haltb : PrimrecPred (fun p : ℕ × ℕ => a p.1 p.2 < b p.1 p.2) :=
    Primrec.nat_lt.comp ha hb
  have hEvenOdd : Primrec₂
      (fun m n => if b m n < a m n then
        2 * (a m n - b m n - 1) else 2 * (b m n - a m n) + 1) :=
    Primrec.ite hblta hEvenOddLt hEvenOddGe
  have hOddEven : Primrec₂
      (fun m n => if a m n < b m n then
        2 * (b m n - a m n - 1) else 2 * (a m n - b m n) + 1) :=
    Primrec.ite haltb hOddEvenLt hOddEvenGe
  have hOdd : Primrec₂
      (fun m n => if n.bodd then
        2 * (a m n + b m n + 1) + 1
      else if a m n < b m n then
        2 * (b m n - a m n - 1)
      else
        2 * (a m n - b m n) + 1) :=
    (Primrec.cond hnOdd hsameOdd hOddEven).of_eq fun p => by
      cases p
      simp
  have hEven : Primrec₂
      (fun m n => if n.bodd then
        (if b m n < a m n then
          2 * (a m n - b m n - 1)
        else
          2 * (b m n - a m n) + 1)
      else
        2 * (a m n + b m n)) :=
    (Primrec.cond hnOdd hEvenOdd hsameEven).of_eq fun p => by
      cases p
      simp
  exact (Primrec.cond hmOdd hOdd hEven).of_eq fun p => by
    cases p
    simp [a, b]

private theorem primrec2_intMulCode : Primrec₂ intMulCode := by
  unfold intMulCode
  let a : ℕ → ℕ → ℕ := fun m _ => if m.bodd then m.div2 + 1 else m.div2
  let b : ℕ → ℕ → ℕ := fun _ n => if n.bodd then n.div2 + 1 else n.div2
  have hmOdd : Primrec₂ (fun m _ : ℕ => m.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.left
  have hnOdd : Primrec₂ (fun _ n : ℕ => n.bodd) :=
    Primrec.nat_bodd.comp₂ Primrec₂.right
  have ha : Primrec₂ a :=
    (Primrec.cond hmOdd
      (Primrec.succ.comp₂ (Primrec.nat_div2.comp₂ Primrec₂.left))
      (Primrec.nat_div2.comp₂ Primrec₂.left)).of_eq fun p => by
        cases p
        simp [a]
  have hb : Primrec₂ b :=
    (Primrec.cond hnOdd
      (Primrec.succ.comp₂ (Primrec.nat_div2.comp₂ Primrec₂.right))
      (Primrec.nat_div2.comp₂ Primrec₂.right)).of_eq fun p => by
        cases p
        simp [b]
  let mag : ℕ → ℕ → ℕ := fun m n => a m n * b m n
  have hmag : Primrec₂ mag := Primrec.nat_mul.comp₂ ha hb
  have hsame : Primrec₂ (fun m n => 2 * mag m n) :=
    Primrec.nat_double.comp₂ hmag
  have hzero : PrimrecPred (fun p : ℕ × ℕ => mag p.1 p.2 = 0) :=
    Primrec.eq.comp hmag (Primrec.const 0)
  have hdiffNeg : Primrec₂ (fun m n => if mag m n = 0 then 0 else 2 * (mag m n - 1) + 1) :=
    Primrec.ite hzero (Primrec₂.const 0)
      (Primrec.nat_double_succ.comp₂
        (Primrec.nat_sub.comp₂ hmag (Primrec₂.const 1)))
  have hsameParity : PrimrecPred (fun p : ℕ × ℕ => p.1.bodd = p.2.bodd) :=
    Primrec.eq.comp hmOdd hnOdd
  exact Primrec.ite hsameParity hsame hdiffNeg

private lemma encode_add_even_even (a b : ℕ) :
    Encodable.encode ((a : ℤ) + (b : ℤ)) = 2 * (a + b) := by
  rw [Int.ofNat_add_ofNat, int_encode_natCast]

private lemma encode_add_even_odd_pos (a b : ℕ) (h : b < a) :
    Encodable.encode ((a : ℤ) + Int.negSucc b) = 2 * (a - b - 1) := by
  change Encodable.encode (Int.ofNat a + Int.negSucc b) = 2 * (a - b - 1)
  rw [Int.ofNat_add_negSucc_of_ge (by omega : b.succ ≤ a)]
  have hsub : a - b.succ = a - b - 1 := by omega
  rw [hsub]
  change Encodable.encode (((a - b - 1 : ℕ) : ℤ)) = 2 * (a - b - 1)
  rw [int_encode_natCast]

private lemma encode_add_even_odd_neg (a b : ℕ) (h : ¬ b < a) :
    Encodable.encode ((a : ℤ) + Int.negSucc b) = 2 * (b - a) + 1 := by
  rw [Int.ofNat_add_negSucc, Int.subNatNat_of_lt (by omega : a < b.succ)]
  have hpred : (b.succ - a).pred = b - a := by
    rw [Nat.pred_eq_sub_one]
    omega
  rw [hpred, int_encode_negSucc]

private lemma encode_add_odd_even_pos (a b : ℕ) (h : a < b) :
    Encodable.encode (Int.negSucc a + (b : ℤ)) = 2 * (b - a - 1) := by
  rw [Int.negSucc_add_ofNat, Int.subNatNat_eq_coe]
  have hEq : Int.ofNat b - Int.ofNat a.succ = Int.ofNat (b - a - 1) := by
    change ((b : ℤ) - (a.succ : ℤ)) = ((b - a - 1 : ℕ) : ℤ)
    rw [← Int.natCast_sub (by omega : a.succ ≤ b)]
    have hn : b - a.succ = b - a - 1 := by omega
    rw [hn]
  change Encodable.encode (Int.ofNat b - Int.ofNat a.succ) = 2 * (b - a - 1)
  rw [hEq]
  change Encodable.encode (((b - a - 1 : ℕ) : ℤ)) = 2 * (b - a - 1)
  rw [int_encode_natCast]

private lemma encode_add_odd_even_neg (a b : ℕ) (h : ¬ a < b) :
    Encodable.encode (Int.negSucc a + (b : ℤ)) = 2 * (a - b) + 1 := by
  rw [Int.negSucc_add_ofNat, Int.subNatNat_of_lt (by omega : b < a.succ)]
  have hpred : (a.succ - b).pred = a - b := by
    rw [Nat.pred_eq_sub_one]
    omega
  rw [hpred, int_encode_negSucc]

private lemma encode_add_odd_odd (a b : ℕ) :
    Encodable.encode (Int.negSucc a + Int.negSucc b) = 2 * (a + b + 1) + 1 := by
  rw [Int.negSucc_add_negSucc, int_encode_negSucc]

private lemma negSucc_pred_eq_neg_cast (p : ℕ) (hp : p ≠ 0) :
    Int.negSucc (p - 1) = -(p : ℤ) := by
  rw [Int.negSucc_eq, ← Int.natCast_succ]
  rw [Nat.succ_eq_add_one, Nat.sub_one_add_one hp]

private lemma encode_mul_even_even (a b : ℕ) :
    Encodable.encode ((a : ℤ) * (b : ℤ)) = 2 * (a * b) := by
  rw [Int.ofNat_mul_ofNat, int_encode_natCast]

private lemma encode_mul_even_odd_zero (a b : ℕ) (h : a * (b + 1) = 0) :
    Encodable.encode ((a : ℤ) * Int.negSucc b) = 0 := by
  rw [Int.ofNat_mul_negSucc, h]
  rfl

private lemma encode_mul_even_odd_neg (a b : ℕ) (h : a * (b + 1) ≠ 0) :
    Encodable.encode ((a : ℤ) * Int.negSucc b) =
      2 * (a * (b + 1) - 1) + 1 := by
  rw [Int.ofNat_mul_negSucc]
  have hneg := negSucc_pred_eq_neg_cast (a * (b + 1)) h
  rw [← hneg, int_encode_negSucc]

private lemma encode_mul_odd_even_zero (a b : ℕ) (h : (a + 1) * b = 0) :
    Encodable.encode (Int.negSucc a * (b : ℤ)) = 0 := by
  rw [Int.negSucc_mul_ofNat]
  change Encodable.encode (-(((a + 1) * b : ℕ) : ℤ)) = 0
  rw [h]
  rfl

private lemma encode_mul_odd_even_neg (a b : ℕ) (h : (a + 1) * b ≠ 0) :
    Encodable.encode (Int.negSucc a * (b : ℤ)) =
      2 * ((a + 1) * b - 1) + 1 := by
  rw [Int.negSucc_mul_ofNat]
  change Encodable.encode (-(((a + 1) * b : ℕ) : ℤ)) =
    2 * ((a + 1) * b - 1) + 1
  have hneg := negSucc_pred_eq_neg_cast ((a + 1) * b) h
  rw [← hneg, int_encode_negSucc]

private lemma encode_mul_odd_odd (a b : ℕ) :
    Encodable.encode (Int.negSucc a * Int.negSucc b) =
      2 * ((a + 1) * (b + 1)) := by
  rw [Int.negSucc_mul_negSucc]
  change Encodable.encode ((((a.succ * b.succ : ℕ) : ℤ))) =
    2 * ((a + 1) * (b + 1))
  rw [int_encode_natCast]

private lemma intAddCode_spec (m n : ℕ) :
    intAddCode m n =
      Encodable.encode (Denumerable.ofNat ℤ m + Denumerable.ofNat ℤ n) := by
  have hm := (Nat.bit_bodd_div2 m).symm
  have hn := (Nat.bit_bodd_div2 n).symm
  rcases hboddm : m.bodd with _ | _
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      simp [intAddCode, Nat.bit, Nat.div2_bit0, encode_add_even_even]
    · rw [hm, hn, hboddm, hboddn]
      by_cases h : n.div2 < m.div2
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_even_odd_pos _ _ h]
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_even_odd_neg _ _ h]
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      by_cases h : m.div2 < n.div2
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_odd_even_pos _ _ h]
      · simp [intAddCode, h, Nat.bit, Nat.div2_bit0, encode_add_odd_even_neg _ _ h]
    · rw [hm, hn, hboddm, hboddn]
      simp [intAddCode, Nat.bit, encode_add_odd_odd]

private lemma intMulCode_spec (m n : ℕ) :
    intMulCode m n =
      Encodable.encode (Denumerable.ofNat ℤ m * Denumerable.ofNat ℤ n) := by
  have hm := (Nat.bit_bodd_div2 m).symm
  have hn := (Nat.bit_bodd_div2 n).symm
  rcases hboddm : m.bodd with _ | _
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      simp [intMulCode, Nat.bit, Nat.div2_bit0, encode_mul_even_even]
    · rw [hm, hn, hboddm, hboddn]
      by_cases hzero : m.div2 * (n.div2 + 1) = 0
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_even_odd_zero _ _ hzero]
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_even_odd_neg _ _ hzero]
  · rcases hboddn : n.bodd with _ | _
    · rw [hm, hn, hboddm, hboddn]
      by_cases hzero : (m.div2 + 1) * n.div2 = 0
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_odd_even_zero _ _ hzero]
      · simp [intMulCode, hzero, Nat.bit, Nat.div2_bit0,
          encode_mul_odd_even_neg _ _ hzero]
    · rw [hm, hn, hboddm, hboddn]
      simp [intMulCode, Nat.bit, encode_mul_odd_odd]

theorem primrec2_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂.ofNat_iff, ← Primrec₂.encode_iff]
  exact primrec2_intAddCode.of_eq intAddCode_spec

theorem primrec2_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂.ofNat_iff, ← Primrec₂.encode_iff]
  exact primrec2_intMulCode.of_eq intMulCode_spec

theorem computable2_int_add : Computable₂ ((· + ·) : ℤ → ℤ → ℤ) :=
  primrec2_int_add.to_comp

theorem computable2_int_mul : Computable₂ ((· * ·) : ℤ → ℤ → ℤ) :=
  primrec2_int_mul.to_comp

end Ripple.BoundedUniversality.BGP
