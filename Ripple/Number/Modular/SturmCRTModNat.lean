/-
  Compute-from-scratch mod-p Sturm certificate verification.

  Instead of loading precomputed certificate arrays (which produce 100MB+
  olean files), compute the recurrence rows mod p from scratch inside
  native_decide.  The ℤ division step is replaced by a modular inverse
  (Fermat: a^(p-2) mod p), and all output values are reduced mod p.
-/
import Ripple.Number.Modular.ModularPolynomialSturmCertificate

namespace Ripple.Number.Modular

/-! ## Modular arithmetic helpers (ℕ) -/

def natPowMod (p base : ℕ) : ℕ → ℕ
  | 0 => 1 % p
  | 1 => base % p
  | n + 2 =>
    let half := natPowMod p base ((n + 2) / 2)
    let sq := (half * half) % p
    if (n + 2) % 2 = 0 then sq
    else (sq * (base % p)) % p

def modInvNat (p a : ℕ) : ℕ :=
  natPowMod p (a % p) (p - 2)

/-! ## Mod-p recurrence row computation -/

def phi41QRecurrenceNextCoeffMod
    (p j valuation k : ℕ) (E4 E6 E2E4 out : Array ℤ) : ℤ :=
  if k < valuation then 0
  else if k = valuation then 1
  else
    let s := sumRangeFromZ 1 k (fun a =>
      (((42 : ℤ) * truncCoeffArrayAt E2E4 a -
          (j : ℤ) * truncCoeffArrayAt E6 a) -
        truncCoeffArrayAt E4 a * ((k - a : ℕ) : ℤ)) *
          truncCoeffArrayAt out (k - a))
    let smod := s % (p : ℤ)
    let spos := if smod < 0 then smod + (p : ℤ) else smod
    let inv := (modInvNat p (k - valuation) : ℤ)
    (spos * inv) % (p : ℤ)

def phi41QRecurrenceRowArrayModAux
    (N p j valuation : ℕ) (E4 E6 E2E4 : Array ℤ) : ℕ → Array ℤ
  | 0 => #[]
  | k + 1 =>
      let out := phi41QRecurrenceRowArrayModAux N p j valuation E4 E6 E2E4 k
      out.push (phi41QRecurrenceNextCoeffMod p j valuation k E4 E6 E2E4 out)

def phi41QRecurrenceRowArrayMod
    (N p j : ℕ) (E4 E6 E2E4 : Array ℤ) : Array ℤ :=
  phi41QRecurrenceRowArrayModAux N p j (42 - j) E4 E6 E2E4 N

def phi41QRecurrenceRowsArrayComputeMod (N p : ℕ) : Array (Array ℤ) :=
  let E4 := E4TruncCoeffArray N
  let E6 := E6TruncCoeffArray N
  let E2E4 := E2E4TruncCoeffArray N
  ((List.range 43).map
    (fun j => phi41QRecurrenceRowArrayMod N p j E4 E6 E2E4)).toArray

/-! ## Optimized checker wrapper -/

def phi41SturmCheckQ (N p : ℕ) (rows : Array (Array ℤ)) : Bool :=
  let E4 := E4TruncCoeffArray N
  let E6 := E6TruncCoeffArray N
  let E2E4 := E2E4TruncCoeffArray N
  phi41QRecurrenceRowsModCertificateWithCoeffArrays N p E4 E6 E2E4 rows

theorem phi41SturmCheckQ_eq (N p : ℕ) (rows : Array (Array ℤ)) :
    phi41SturmCheckQ N p rows =
    phi41QRecurrenceRowsModCertificate N p rows := rfl

/-! ## Per-prime row definitions -/

def sturmCRTM : ℕ := (phi41Level41SturmBound + 40) / 41

def sturmCRTPCompressedMod (p : ℕ) : Array (Array ℤ) :=
  phi41QRecurrenceRowsArrayComputeMod sturmCRTM p

def sturmCRTQMod (p : ℕ) : Array (Array ℤ) :=
  phi41QRecurrenceRowsArrayComputeMod phi41Level41SturmBound p

/-! ## Per-prime opaque check components (for cheap bridge proofs) -/

def sturmCRT_hP (p : ℕ) : Bool :=
  phi41SturmCheckQ sturmCRTM p (sturmCRTPCompressedMod p)

def sturmCRT_hQ (p : ℕ) : Bool :=
  phi41SturmCheckQ phi41Level41SturmBound p (sturmCRTQMod p)

def sturmCRT_hz (p : ℕ) : Bool :=
  truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
    (phi41Level41RecurrenceCoeffArrayFromRows
      phi41Level41SturmBound sturmCRTM
      (sturmCRTPCompressedMod p) (sturmCRTQMod p))

/-! ## Combined per-prime check -/

def sturmCRTCheckAll (p : ℕ) : Bool :=
  sturmCRT_hP p && sturmCRT_hQ p && sturmCRT_hz p

/-! ## Bridge: combined check → component forms -/

private theorem sturmCRTCheckAll_expand (p : ℕ) :
    sturmCRTCheckAll p = (sturmCRT_hP p && sturmCRT_hQ p && sturmCRT_hz p) := rfl

theorem sturmCRTCheckAll_hPcert {p : ℕ} (h : sturmCRTCheckAll p = true) :
    phi41QRecurrenceRowsModCertificate
      sturmCRTM p (sturmCRTPCompressedMod p) = true := by
  rw [← phi41SturmCheckQ_eq]
  change sturmCRT_hP p = true
  rw [sturmCRTCheckAll_expand] at h
  revert h; cases sturmCRT_hP p <;> simp

theorem sturmCRTCheckAll_hQcert {p : ℕ} (h : sturmCRTCheckAll p = true) :
    phi41QRecurrenceRowsModCertificate
      phi41Level41SturmBound p (sturmCRTQMod p) = true := by
  rw [← phi41SturmCheckQ_eq]
  change sturmCRT_hQ p = true
  rw [sturmCRTCheckAll_expand] at h
  revert h; cases sturmCRT_hP p <;> cases sturmCRT_hQ p <;> simp

theorem sturmCRTCheckAll_hzero {p : ℕ} (h : sturmCRTCheckAll p = true) :
    truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
      (phi41Level41RecurrenceCoeffArrayFromRows
        phi41Level41SturmBound sturmCRTM
        (sturmCRTPCompressedMod p) (sturmCRTQMod p)) = true := by
  change sturmCRT_hz p = true
  rw [sturmCRTCheckAll_expand] at h
  revert h; cases sturmCRT_hP p <;> cases sturmCRT_hQ p <;> cases sturmCRT_hz p <;> simp

/-! ## Optimized combined check (shared computation for native_decide) -/

def sturmCRTCheckAllFast (p : ℕ) : Bool :=
  let M := sturmCRTM
  let N := phi41Level41SturmBound
  let E4M := E4TruncCoeffArray M
  let E6M := E6TruncCoeffArray M
  let E2E4M := E2E4TruncCoeffArray M
  let E4N := E4TruncCoeffArray N
  let E6N := E6TruncCoeffArray N
  let E2E4N := E2E4TruncCoeffArray N
  let Prows := ((List.range 43).map
    (fun j => phi41QRecurrenceRowArrayMod M p j E4M E6M E2E4M)).toArray
  let Qrows := ((List.range 43).map
    (fun j => phi41QRecurrenceRowArrayMod N p j E4N E6N E2E4N)).toArray
  phi41QRecurrenceRowsModCertificateWithCoeffArrays M p E4M E6M E2E4M Prows &&
  phi41QRecurrenceRowsModCertificateWithCoeffArrays N p E4N E6N E2E4N Qrows &&
  truncCoeffArrayFirstZeroMod N p
    (phi41Level41RecurrenceCoeffArrayFromRows N M Prows Qrows)

theorem sturmCRTCheckAllFast_eq (p : ℕ) :
    sturmCRTCheckAllFast p = sturmCRTCheckAll p := rfl

theorem sturmCRTCheckAllFast_eq_fn :
    sturmCRTCheckAllFast = sturmCRTCheckAll := funext sturmCRTCheckAllFast_eq

end Ripple.Number.Modular
