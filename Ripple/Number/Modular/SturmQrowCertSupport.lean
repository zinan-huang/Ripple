import Ripple.Number.Modular.ModularPolynomialSturmCertificate

namespace Ripple
namespace Number
namespace Modular

theorem phi41QRecurrenceRowFnModCertificateChunk_zero
    {N p j start len : ℕ} {E4 E6 E2E4 row : ℕ → ℤ}
    (hchunk :
      phi41QRecurrenceRowFnModCertificateChunk
        N p j start len E4 E6 E2E4 row = true)
    {n : ℕ} (hstart : start ≤ n) (hend : n < start + len)
    (hn : n < N) (hval : n < 42 - j) :
    row n ≡ 0 [ZMOD (p : ℤ)] := by
  unfold phi41QRecurrenceRowFnModCertificateChunk at hchunk
  let offset := n - start
  have hoffset_lt : offset < len := by omega
  have hoffset_mem : offset ∈ List.range len := List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : start + offset = n := by
    dsimp [offset]
    omega
  exact int_modEq_of_intCoeffModEq (by simpa [hn_eq, hn, hval] using hentry)

theorem phi41QRecurrenceRowFnModCertificateChunk_one
    {N p j start len : ℕ} {E4 E6 E2E4 row : ℕ → ℤ}
    (hchunk :
      phi41QRecurrenceRowFnModCertificateChunk
        N p j start len E4 E6 E2E4 row = true)
    {n : ℕ} (hstart : start ≤ n) (hend : n < start + len)
    (hn : n < N) (hval : n = 42 - j) :
    row n ≡ 1 [ZMOD (p : ℤ)] := by
  unfold phi41QRecurrenceRowFnModCertificateChunk at hchunk
  let offset := n - start
  have hoffset_lt : offset < len := by omega
  have hoffset_mem : offset ∈ List.range len := List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : start + offset = n := by
    dsimp [offset]
    omega
  have hnotlt : ¬n < 42 - j := by omega
  have hidx : 42 - j < N := by
    omega
  exact int_modEq_of_intCoeffModEq (by
    simpa [hn_eq, hidx, hnotlt, hval] using hentry)

theorem phi41QRecurrenceRowFnModCertificateChunk_rec
    {N p j start len : ℕ} {E4 E6 E2E4 row : ℕ → ℤ}
    (hchunk :
      phi41QRecurrenceRowFnModCertificateChunk
        N p j start len E4 E6 E2E4 row = true)
    {n : ℕ} (hstart : start ≤ n) (hend : n < start + len)
    (hn : n < N) (hval : 42 - j < n) :
    (((n - (42 - j) : ℕ) : ℤ)) * row n ≡
      sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * E2E4 a -
            (j : ℤ) * E6 a) -
          E4 a * ((n - a : ℕ) : ℤ)) *
            row (n - a)) [ZMOD (p : ℤ)] := by
  unfold phi41QRecurrenceRowFnModCertificateChunk at hchunk
  let offset := n - start
  have hoffset_lt : offset < len := by omega
  have hoffset_mem : offset ∈ List.range len := List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : start + offset = n := by
    dsimp [offset]
    omega
  have hnotlt : ¬n < 42 - j := by omega
  have hneq : ¬n = 42 - j := by omega
  exact int_modEq_of_intCoeffModEq (by
    simpa [hn_eq, hn, hnotlt, hneq] using hentry)

theorem phi41QRecurrenceRowFnModCertificate_rec_of_chunks
    {N p j chunkSize numChunks : ℕ} {E4 E6 E2E4 row : ℕ → ℤ}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41QRecurrenceRowFnModCertificateChunk
        N p j (c * chunkSize) chunkSize E4 E6 E2E4 row = true)
    {n : ℕ} (hn : n < N) (hval : 42 - j < n) :
    (((n - (42 - j) : ℕ) : ℤ)) * row n ≡
      sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * E2E4 a -
            (j : ℤ) * E6 a) -
          E4 a * ((n - a : ℕ) : ℤ)) *
            row (n - a)) [ZMOD (p : ℤ)] := by
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hN0 : N = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  let offset := n % chunkSize
  have hstart : c * chunkSize ≤ n := by
    dsimp [c]
    exact Nat.div_mul_le_self n chunkSize
  have hend : n < c * chunkSize + chunkSize := by
    have hoffset_lt : offset < chunkSize := by
      dsimp [offset]
      exact Nat.mod_lt n hchunkPos
    have hn_eq : c * chunkSize + offset = n := by
      dsimp [c, offset]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod n chunkSize
    omega
  exact phi41QRecurrenceRowFnModCertificateChunk_rec
    (hchunks c hc_lt) hstart hend hn hval

def phi41QRecurrenceResidual
    (j n : ℕ) (E4 E6 E2E4 row : ℕ → ℤ) : ℤ :=
  (((n - (42 - j) : ℕ) : ℤ)) * row n -
    sumRangeFromZ 1 n (fun a =>
      (((42 : ℤ) * E2E4 a -
          (j : ℤ) * E6 a) -
        E4 a * ((n - a : ℕ) : ℤ)) *
          row (n - a))

theorem phi41QRecurrenceResidual_modEq_zero_of_fn_mod_certificate_chunks
    {N p j chunkSize numChunks : ℕ}
    {E4Z E6Z E2E4Z rowZ E4M E6M E2E4M rowM : ℕ → ℤ}
    (hcover : N ≤ chunkSize * numChunks)
    (hE4 : ∀ n : ℕ, n < N → E4Z n ≡ E4M n [ZMOD (p : ℤ)])
    (hE6 : ∀ n : ℕ, n < N → E6Z n ≡ E6M n [ZMOD (p : ℤ)])
    (hE2E4 : ∀ n : ℕ, n < N → E2E4Z n ≡ E2E4M n [ZMOD (p : ℤ)])
    (hrow : ∀ n : ℕ, n < N → rowZ n ≡ rowM n [ZMOD (p : ℤ)])
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41QRecurrenceRowFnModCertificateChunk
        N p j (c * chunkSize) chunkSize E4M E6M E2E4M rowM = true)
    {n : ℕ} (hn : n < N) (hval : 42 - j < n) :
    phi41QRecurrenceResidual j n E4Z E6Z E2E4Z rowZ ≡
      0 [ZMOD (p : ℤ)] := by
  let d : ℤ := ((n - (42 - j) : ℕ) : ℤ)
  let S_Z : ℤ := sumRangeFromZ 1 n (fun a =>
    (((42 : ℤ) * E2E4Z a -
        (j : ℤ) * E6Z a) -
      E4Z a * ((n - a : ℕ) : ℤ)) *
        rowZ (n - a))
  let S_M : ℤ := sumRangeFromZ 1 n (fun a =>
    (((42 : ℤ) * E2E4M a -
        (j : ℤ) * E6M a) -
      E4M a * ((n - a : ℕ) : ℤ)) *
        rowM (n - a))
  have hleft : d * rowZ n ≡ d * rowM n [ZMOD (p : ℤ)] :=
    Int.ModEq.mul_left d (hrow n hn)
  have hS : S_Z ≡ S_M [ZMOD (p : ℤ)] := by
    apply sumRangeFromZ_modEq
    intro a ha1 ha2
    have haN : a < N := by omega
    have hidxN : n - a < N := by omega
    have hcoef :
        (((42 : ℤ) * E2E4Z a -
            (j : ℤ) * E6Z a) -
          E4Z a * ((n - a : ℕ) : ℤ)) ≡
        (((42 : ℤ) * E2E4M a -
            (j : ℤ) * E6M a) -
          E4M a * ((n - a : ℕ) : ℤ)) [ZMOD (p : ℤ)] := by
      exact
        ((Int.ModEq.mul_left (42 : ℤ) (hE2E4 a haN)).sub
          (Int.ModEq.mul_left (j : ℤ) (hE6 a haN))).sub
            ((hE4 a haN).mul (Int.ModEq.refl ((n - a : ℕ) : ℤ)))
    exact hcoef.mul (hrow (n - a) hidxN)
  have hrecM :
      d * rowM n ≡ S_M [ZMOD (p : ℤ)] := by
    simpa [d, S_M] using
      phi41QRecurrenceRowFnModCertificate_rec_of_chunks
        (N := N) (p := p) (j := j)
        (chunkSize := chunkSize) (numChunks := numChunks)
        (E4 := E4M) (E6 := E6M) (E2E4 := E2E4M) (row := rowM)
        hcover hchunks hn hval
  have hmain : d * rowZ n ≡ S_Z [ZMOD (p : ℤ)] :=
    (hleft.trans hrecM).trans hS.symm
  have hzero := hmain.sub (Int.ModEq.refl S_Z)
  simpa [phi41QRecurrenceResidual, d, S_Z, sub_eq_add_neg, add_assoc] using hzero

end Modular
end Number
end Ripple
