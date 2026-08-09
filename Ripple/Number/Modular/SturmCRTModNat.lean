/-
  Compute-from-scratch mod-p Sturm certificate verification.

  Instead of loading precomputed certificate arrays (which produce 100MB+
  olean files), compute the recurrence rows mod p from scratch inside
  native_decide.  The ℤ division step uses a table of modular inverses
  (computed by Fermat: a^(p-2) mod p), and both the input coefficients and
  output values are reduced mod p before the large recurrence is evaluated.
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

/-! ## Machine-word mod-p recurrence row computation -/

@[inline] def addNatResidues (p a b : ℕ) : ℕ :=
  let s := a + b
  if s < p then s else s - p

@[inline] def subNatResidues (p a b : ℕ) : ℕ :=
  if b ≤ a then a - b else a + (p - b)

/-- Sum a consecutive range while reducing after every addition.  All callers
keep their arguments below `p`, so the native evaluator stays on machine-word
natural numbers instead of allocating large integers. -/
def sumRangeFromNatModAux (p : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, acc => acc
  | start, len + 1, acc =>
      sumRangeFromNatModAux p f (start + 1) len
        (addNatResidues p acc (f start))

def sumRangeFromNatMod (p start len : ℕ) (f : ℕ → ℕ) : ℕ :=
  sumRangeFromNatModAux p f start len 0

@[inline] def natCoeffAt (xs : Array ℕ) (n : ℕ) : ℕ :=
  xs.getD n 0

/-- The row recurrence only divides by values in `0 .. N`.  Computing their
modular inverses once avoids repeating Fermat exponentiation in every row. -/
def modInvNatTable (N p : ℕ) : Array ℕ :=
  ((List.range (N + 1)).map (modInvNat p)).toArray

def phi41QRecurrenceNextCoeffModNat
    (p j valuation k : ℕ) (inverses E4 E6 E2E4 out : Array ℕ) : ℕ :=
  if k < valuation then 0
  else if k = valuation then 1
  else
    let s := sumRangeFromNatMod p 1 k (fun a =>
      let e2e4 := natCoeffAt E2E4 a
      let e6 := natCoeffAt E6 a
      let e4 := natCoeffAt E4 a
      let prev := natCoeffAt out (k - a)
      let c1 := (42 * e2e4) % p
      let c2 := (j * e6) % p
      let c3 := (e4 * (k - a)) % p
      let coeff := subNatResidues p (subNatResidues p c1 c2) c3
      (coeff * prev) % p)
    (s * natCoeffAt inverses (k - valuation)) % p

def phi41QRecurrenceRowArrayModNatAux
    (p j valuation : ℕ) (inverses E4 E6 E2E4 : Array ℕ) :
    ℕ → ℕ → Array ℕ → Array ℕ
  | _, 0, out => out
  | k, len + 1, out =>
      let next := phi41QRecurrenceNextCoeffModNat
        p j valuation k inverses E4 E6 E2E4 out
      phi41QRecurrenceRowArrayModNatAux
        p j valuation inverses E4 E6 E2E4 (k + 1) len (out.push next)

def phi41QRecurrenceRowArrayModNat
    (N p j : ℕ) (inverses E4 E6 E2E4 : Array ℕ) : Array ℕ :=
  phi41QRecurrenceRowArrayModNatAux p j (42 - j)
    inverses E4 E6 E2E4 0 N #[]

def phi41QRecurrenceRowsArrayComputeModNat
    (N p : ℕ) (E4 E6 E2E4 : Array ℕ) : Array (Array ℕ) :=
  let inverses := modInvNatTable N p
  ((List.range 43).map
    (fun j => phi41QRecurrenceRowArrayModNat
      N p j inverses E4 E6 E2E4)).toArray

/-- Compute a recurrence coefficient and check its defining modular equation in
the same pass.  The Boolean is later connected to the proof-facing certificate. -/
def phi41QRecurrenceNextCoeffModNatChecked
    (p j valuation k : ℕ) (inverses E4 E6 E2E4 out : Array ℕ) : ℕ × Bool :=
  if k < valuation then (0, true)
  else if k = valuation then (1, true)
  else
    let s := sumRangeFromNatMod p 1 k (fun a =>
      let e2e4 := natCoeffAt E2E4 a
      let e6 := natCoeffAt E6 a
      let e4 := natCoeffAt E4 a
      let prev := natCoeffAt out (k - a)
      let c1 := (42 * e2e4) % p
      let c2 := (j * e6) % p
      let c3 := (e4 * (k - a)) % p
      let coeff := subNatResidues p (subNatResidues p c1 c2) c3
      (coeff * prev) % p)
    let next := (s * natCoeffAt inverses (k - valuation)) % p
    (next, (((k - valuation) * next) % p == s))

/-- Structurally recursive row construction used by the one-pass checker. -/
def phi41QRecurrenceRowArrayModNatCheckedAux
    (p j valuation : ℕ) (inverses E4 E6 E2E4 : Array ℕ) :
    ℕ → Array ℕ × Bool
  | 0 => (#[], true)
  | k + 1 =>
      let previous := phi41QRecurrenceRowArrayModNatCheckedAux
        p j valuation inverses E4 E6 E2E4 k
      let step := phi41QRecurrenceNextCoeffModNatChecked
        p j valuation k inverses E4 E6 E2E4 previous.1
      (previous.1.push step.1, previous.2 && step.2)

def phi41QRecurrenceRowArrayModNatChecked
    (N p j : ℕ) (inverses E4 E6 E2E4 : Array ℕ) : Array ℕ × Bool :=
  phi41QRecurrenceRowArrayModNatCheckedAux p j (42 - j)
    inverses E4 E6 E2E4 N

/-- Compute all 43 rows while accumulating the recurrence checks, so the
quadratic recurrence sums are not evaluated a second time by a certificate pass. -/
def phi41QRecurrenceRowsArrayComputeModNatChecked
    (N p : ℕ) (E4 E6 E2E4 : Array ℕ) : Array (Array ℕ) × Bool :=
  let inverses := modInvNatTable N p
  let checked := (List.range 43).map (fun j =>
    phi41QRecurrenceRowArrayModNatChecked
      N p j inverses E4 E6 E2E4)
  ((checked.map Prod.fst).toArray, checked.all Prod.snd)

def intArrayResiduesToNat (p : ℕ) (xs : Array ℤ) : Array ℕ :=
  xs.map (fun x => Int.toNat (x % (p : ℤ)))

def natArrayToInt (xs : Array ℕ) : Array ℤ :=
  xs.map (fun x : ℕ => Int.ofNat x)

def natRowsToInt (xs : Array (Array ℕ)) : Array (Array ℤ) :=
  xs.map natArrayToInt

/-- Compute rows using bounded natural-number residues, then convert back to the
integer representation consumed by the proof-facing CRT bridge and final recurrence. -/
def phi41QRecurrenceRowsArrayComputeModWithCoeffArrays
    (N p : ℕ) (E4 E6 E2E4 : Array ℤ) : Array (Array ℤ) :=
  natRowsToInt <| phi41QRecurrenceRowsArrayComputeModNat N p
    (intArrayResiduesToNat p E4) (intArrayResiduesToNat p E6)
    (intArrayResiduesToNat p E2E4)

/-! ## Bounded-residue certificate and soundness bridge -/

def phi41QRecurrenceTermModNatArrays
    (p j n a : ℕ) (E4 E6 E2E4 row : Array ℕ) : ℕ :=
  let e2e4 := natCoeffAt E2E4 a
  let e6 := natCoeffAt E6 a
  let e4 := natCoeffAt E4 a
  let prev := natCoeffAt row (n - a)
  let c1 := (42 * e2e4) % p
  let c2 := (j * e6) % p
  let c3 := (e4 * (n - a)) % p
  let coeff := subNatResidues p (subNatResidues p c1 c2) c3
  (coeff * prev) % p

def phi41QRecurrenceRowModCertificateNatEntry
    (p j n : ℕ) (E4 E6 E2E4 row : Array ℕ) : Bool :=
  let rowN := natCoeffAt row n
  if n < 42 - j then
    rowN == 0
  else if n = 42 - j then
    rowN == (1 % p)
  else
    ((n - (42 - j)) * rowN) % p ==
      sumRangeFromNatMod p 1 n (fun a =>
        phi41QRecurrenceTermModNatArrays p j n a E4 E6 E2E4 row)

def phi41QRecurrenceRowModCertificateNatArrays
    (N p j : ℕ) (E4 E6 E2E4 row : Array ℕ) : Bool :=
  (List.range N).all (fun n =>
    phi41QRecurrenceRowModCertificateNatEntry p j n E4 E6 E2E4 row)

def phi41QRecurrenceRowsModCertificateNatArrays
    (N p : ℕ) (E4 E6 E2E4 : Array ℕ)
    (rows : Array (Array ℕ)) : Bool :=
  (List.range 43).all (fun j =>
    phi41QRecurrenceRowModCertificateNatArrays N p j E4 E6 E2E4
      (rows.getD j #[]))

theorem intCoeffModEq_eq_true_of_modEq {p : ℕ} {a b : ℤ}
    (h : a ≡ b [ZMOD (p : ℤ)]) : intCoeffModEq p a b = true := by
  have hz := h.sub (Int.ModEq.refl b)
  simpa [intCoeffModEq, intCoeffZeroMod, Int.ModEq] using hz

theorem natCast_mod_modEq (p a : ℕ) :
    ((a % p : ℕ) : ℤ) ≡ (a : ℤ) [ZMOD (p : ℤ)] := by
  exact_mod_cast Nat.mod_modEq a p

theorem addNatResidues_modEq (p a b : ℕ) :
    (addNatResidues p a b : ℤ) ≡ (a : ℤ) + (b : ℤ) [ZMOD (p : ℤ)] := by
  simp only [addNatResidues]
  split_ifs with h
  · norm_num
  · have hp : p ≤ a + b := by omega
    rw [Nat.cast_sub hp, Nat.cast_add]
    simpa [sub_eq_add_neg, add_assoc] using
      (Int.modEq_add_fac_self (a := (a : ℤ) + (b : ℤ))
        (t := (-1 : ℤ)) (n := (p : ℤ)))

theorem subNatResidues_modEq (p a b : ℕ) (hb : b ≤ p) :
    (subNatResidues p a b : ℤ) ≡ (a : ℤ) - (b : ℤ) [ZMOD (p : ℤ)] := by
  unfold subNatResidues
  split_ifs with h
  · rw [Nat.cast_sub h]
  · have hbp : b ≤ p := hb
    rw [Nat.cast_add, Nat.cast_sub hbp]
    convert Int.modEq_add_fac_self (a := (a : ℤ) - (b : ℤ))
      (t := (1 : ℤ)) (n := (p : ℤ)) using 1
    all_goals ring

theorem sumRangeFromNatModAux_modEq
    (p : ℕ) (f : ℕ → ℕ) (g : ℕ → ℤ)
    (hfg : ∀ i, (f i : ℤ) ≡ g i [ZMOD (p : ℤ)]) :
    ∀ start len acc,
      (sumRangeFromNatModAux p f start len acc : ℤ) ≡
        (acc : ℤ) + sumRangeFromZ start len g [ZMOD (p : ℤ)]
  | start, 0, acc => by
      simp [sumRangeFromNatModAux, sumRangeFromZ]
  | start, len + 1, acc => by
      rw [sumRangeFromNatModAux, sumRangeFromZ]
      calc
        (sumRangeFromNatModAux p f (start + 1) len
              (addNatResidues p acc (f start)) : ℤ)
            ≡ (addNatResidues p acc (f start) : ℤ) +
                sumRangeFromZ (start + 1) len g [ZMOD (p : ℤ)] :=
          sumRangeFromNatModAux_modEq p f g hfg
            (start + 1) len (addNatResidues p acc (f start))
        _ ≡ ((acc : ℤ) + (f start : ℤ)) +
                sumRangeFromZ (start + 1) len g [ZMOD (p : ℤ)] :=
          (addNatResidues_modEq p acc (f start)).add
            (Int.ModEq.refl (sumRangeFromZ (start + 1) len g))
        _ ≡ (acc : ℤ) +
              (g start + sumRangeFromZ (start + 1) len g) [ZMOD (p : ℤ)] := by
          simpa [add_assoc] using (Int.ModEq.refl (acc : ℤ)).add
              ((hfg start).add
                (Int.ModEq.refl (sumRangeFromZ (start + 1) len g)))

theorem sumRangeFromNatMod_modEq
    (p start len : ℕ) (f : ℕ → ℕ) (g : ℕ → ℤ)
    (hfg : ∀ i, (f i : ℤ) ≡ g i [ZMOD (p : ℤ)]) :
    (sumRangeFromNatMod p start len f : ℤ) ≡
      sumRangeFromZ start len g [ZMOD (p : ℤ)] := by
  simpa [sumRangeFromNatMod] using
    sumRangeFromNatModAux_modEq p f g hfg start len 0

theorem sumRangeFromNatMod_modEq_range
    (p start len : ℕ) (f : ℕ → ℕ) (g : ℕ → ℤ)
    (hfg : ∀ i, start ≤ i → i < start + len →
      (f i : ℤ) ≡ g i [ZMOD (p : ℤ)]) :
    (sumRangeFromNatMod p start len f : ℤ) ≡
      sumRangeFromZ start len g [ZMOD (p : ℤ)] := by
  let g' : ℕ → ℤ := fun i =>
    if start ≤ i ∧ i < start + len then g i else (f i : ℤ)
  have hall : ∀ i, (f i : ℤ) ≡ g' i [ZMOD (p : ℤ)] := by
    intro i
    by_cases hi : start ≤ i ∧ i < start + len
    · simpa [g', hi] using hfg i hi.1 hi.2
    · simp [g', hi]
  have hs := sumRangeFromNatMod_modEq p start len f g' hall
  have hsum : sumRangeFromZ start len g' = sumRangeFromZ start len g := by
    apply sumRangeFromZ_congr
    intro i hi1 hi2
    simp [g', hi1, hi2]
  simpa [hsum] using hs

def TruncCoeffArrayNatModEq
    (N p : ℕ) (zs : Array ℤ) (ns : Array ℕ) : Prop :=
  ∀ n, n < N →
    (natCoeffAt ns n : ℤ) ≡ truncCoeffArrayAt zs n [ZMOD (p : ℤ)]

theorem intArrayResiduesToNat_modEq
    (N p : ℕ) (xs : Array ℤ) (hp : 0 < p) :
    TruncCoeffArrayNatModEq N p xs (intArrayResiduesToNat p xs) := by
  intro n hn
  have hget :
      natCoeffAt (intArrayResiduesToNat p xs) n =
        Int.toNat (truncCoeffArrayAt xs n % (p : ℤ)) := by
    simp [natCoeffAt, intArrayResiduesToNat, truncCoeffArrayAt,
      Array.getD_eq_getD_getElem?]
    simpa using
      (Option.getD_map (fun x : ℤ => Int.toNat (x % (p : ℤ))) 0 xs[n]?)
  rw [hget]
  have hp0 : (p : ℤ) ≠ 0 := by omega
  have hnonneg : 0 ≤ truncCoeffArrayAt xs n % (p : ℤ) :=
    Int.emod_nonneg _ hp0
  rw [Int.toNat_of_nonneg hnonneg]
  exact Int.mod_modEq _ _

theorem natArrayToInt_at (xs : Array ℕ) (n : ℕ) :
    truncCoeffArrayAt (natArrayToInt xs) n = (natCoeffAt xs n : ℤ) := by
  have hget :
      truncCoeffArrayAt (natArrayToInt xs) n =
        ((fun x : ℕ => (x : ℤ)) (natCoeffAt xs n)) := by
    simp [natCoeffAt, natArrayToInt, truncCoeffArrayAt,
      Array.getD_eq_getD_getElem?]
    simpa using
      (Option.getD_map (fun x : ℕ => (x : ℤ)) 0 xs[n]?)
  exact hget

theorem natRowsToInt_row_modEq
    (N p : ℕ) (rows : Array (Array ℕ)) (j : ℕ) :
    TruncCoeffArrayNatModEq N p
      ((natRowsToInt rows).getD j (zeroTruncCoeffArray N))
      (rows.getD j #[]) := by
  intro n hn
  by_cases hj : j < rows.size
  · have hj' : j < (natRowsToInt rows).size := by
      simpa [natRowsToInt] using hj
    rw [← Array.getElem_eq_getD (h := hj) #[]]
    rw [← Array.getElem_eq_getD (h := hj') (zeroTruncCoeffArray N)]
    simp only [natRowsToInt, Array.getElem_map]
    rw [natArrayToInt_at]
  · have hj' : ¬j < (natRowsToInt rows).size := by
      simpa [natRowsToInt] using hj
    have hnat : rows.getD j #[] = #[] := by
      simp [Array.getD, hj]
    have hint :
        (natRowsToInt rows).getD j (zeroTruncCoeffArray N) =
          zeroTruncCoeffArray N := by
      simp [Array.getD, hj']
    rw [hnat, hint]
    rw [zeroTruncCoeffArray, truncCoeffArrayAt_ofFn_of_lt hn]
    simp [natCoeffAt, Array.getD]

theorem phi41QRecurrenceTermModNatArrays_modEq
    {N p j n a : ℕ}
    {E4Z E6Z E2E4Z rowZ : Array ℤ}
    {E4N E6N E2E4N rowN : Array ℕ}
    (hp : 0 < p) (hn : n < N) (ha1 : 1 ≤ a) (han : a ≤ n)
    (hE4 : TruncCoeffArrayNatModEq N p E4Z E4N)
    (hE6 : TruncCoeffArrayNatModEq N p E6Z E6N)
    (hE2E4 : TruncCoeffArrayNatModEq N p E2E4Z E2E4N)
    (hrow : TruncCoeffArrayNatModEq N p rowZ rowN) :
    (phi41QRecurrenceTermModNatArrays p j n a E4N E6N E2E4N rowN : ℤ) ≡
      (((42 : ℤ) * truncCoeffArrayAt E2E4Z a -
          (j : ℤ) * truncCoeffArrayAt E6Z a) -
        truncCoeffArrayAt E4Z a * ((n - a : ℕ) : ℤ)) *
          truncCoeffArrayAt rowZ (n - a) [ZMOD (p : ℤ)] := by
  have haN : a < N := by omega
  have hnaN : n - a < N := by omega
  let e2e4 := natCoeffAt E2E4N a
  let e6 := natCoeffAt E6N a
  let e4 := natCoeffAt E4N a
  let prev := natCoeffAt rowN (n - a)
  let c1 := (42 * e2e4) % p
  let c2 := (j * e6) % p
  let c3 := (e4 * (n - a)) % p
  let coeff12 := subNatResidues p c1 c2
  let coeff := subNatResidues p coeff12 c3
  have hc1 : (c1 : ℤ) ≡
      (42 : ℤ) * truncCoeffArrayAt E2E4Z a [ZMOD (p : ℤ)] :=
    (natCast_mod_modEq p (42 * e2e4)).trans
      (Int.ModEq.mul_left (42 : ℤ) (hE2E4 a haN))
  have hc2 : (c2 : ℤ) ≡
      (j : ℤ) * truncCoeffArrayAt E6Z a [ZMOD (p : ℤ)] :=
    (natCast_mod_modEq p (j * e6)).trans
      (Int.ModEq.mul_left (j : ℤ) (hE6 a haN))
  have hc3 : (c3 : ℤ) ≡
      truncCoeffArrayAt E4Z a * ((n - a : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    (natCast_mod_modEq p (e4 * (n - a))).trans
      ((hE4 a haN).mul (Int.ModEq.refl ((n - a : ℕ) : ℤ)))
  have hc2le : c2 ≤ p := (Nat.mod_lt _ hp).le
  have hc3le : c3 ≤ p := (Nat.mod_lt _ hp).le
  have hc12 : (coeff12 : ℤ) ≡
      (42 : ℤ) * truncCoeffArrayAt E2E4Z a -
        (j : ℤ) * truncCoeffArrayAt E6Z a [ZMOD (p : ℤ)] :=
    (subNatResidues_modEq p c1 c2 hc2le).trans (hc1.sub hc2)
  have hcoeff : (coeff : ℤ) ≡
      ((42 : ℤ) * truncCoeffArrayAt E2E4Z a -
        (j : ℤ) * truncCoeffArrayAt E6Z a) -
          truncCoeffArrayAt E4Z a * ((n - a : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    (subNatResidues_modEq p coeff12 c3 hc3le).trans (hc12.sub hc3)
  have hprev : (prev : ℤ) ≡
      truncCoeffArrayAt rowZ (n - a) [ZMOD (p : ℤ)] :=
    hrow (n - a) hnaN
  change (((coeff * prev) % p : ℕ) : ℤ) ≡ _ [ZMOD (p : ℤ)]
  exact (natCast_mod_modEq p (coeff * prev)).trans (hcoeff.mul hprev)

theorem phi41QRecurrenceRowModCertificateNatArrays_sound
    {N p j : ℕ}
    {E4Z E6Z E2E4Z rowZ : Array ℤ}
    {E4N E6N E2E4N rowN : Array ℕ}
    (hp : 0 < p)
    (hE4 : TruncCoeffArrayNatModEq N p E4Z E4N)
    (hE6 : TruncCoeffArrayNatModEq N p E6Z E6N)
    (hE2E4 : TruncCoeffArrayNatModEq N p E2E4Z E2E4N)
    (hrow : TruncCoeffArrayNatModEq N p rowZ rowN)
    (hcert : phi41QRecurrenceRowModCertificateNatArrays
      N p j E4N E6N E2E4N rowN = true) :
    phi41QRecurrenceRowModCertificate N p j E4Z E6Z E2E4Z rowZ = true := by
  unfold phi41QRecurrenceRowModCertificateNatArrays at hcert
  unfold phi41QRecurrenceRowModCertificate
  apply List.all_eq_true.mpr
  intro n hnmem
  have hn : n < N := List.mem_range.mp hnmem
  have hentry := List.all_eq_true.mp hcert n hnmem
  unfold phi41QRecurrenceRowModCertificateNatEntry at hentry
  by_cases hlt : n < 42 - j
  · simp only [hlt, ↓reduceIte] at hentry ⊢
    have hnzero : natCoeffAt rowN n = 0 := by simpa using hentry
    apply intCoeffModEq_eq_true_of_modEq
    exact (hrow n hn).symm.trans (by simp [hnzero])
  · by_cases heq : n = 42 - j
    · rw [if_neg hlt, if_pos heq] at hentry ⊢
      have hnone : natCoeffAt rowN n = 1 % p := by simpa using hentry
      apply intCoeffModEq_eq_true_of_modEq
      exact (hrow n hn).symm.trans <| by
        rw [hnone]
        exact natCast_mod_modEq p 1
    · simp only [hlt, heq, ↓reduceIte] at hentry ⊢
      have hval : 42 - j < n := by omega
      let lhsN := ((n - (42 - j)) * natCoeffAt rowN n) % p
      let rhsN := sumRangeFromNatMod p 1 n (fun a =>
        phi41QRecurrenceTermModNatArrays p j n a E4N E6N E2E4N rowN)
      have hlhs : (lhsN : ℤ) ≡
          (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffArrayAt rowZ n
            [ZMOD (p : ℤ)] :=
        (natCast_mod_modEq p
          ((n - (42 - j)) * natCoeffAt rowN n)).trans
            ((Int.ModEq.refl ((n - (42 - j) : ℕ) : ℤ)).mul (hrow n hn))
      have hrhs : (rhsN : ℤ) ≡
          sumRangeFromZ 1 n (fun a =>
            (((42 : ℤ) * truncCoeffArrayAt E2E4Z a -
                (j : ℤ) * truncCoeffArrayAt E6Z a) -
              truncCoeffArrayAt E4Z a * ((n - a : ℕ) : ℤ)) *
                truncCoeffArrayAt rowZ (n - a)) [ZMOD (p : ℤ)] := by
        apply sumRangeFromNatMod_modEq_range
        intro a ha1 han
        exact phi41QRecurrenceTermModNatArrays_modEq hp hn ha1 (by omega)
          hE4 hE6 hE2E4 hrow
      have hlr : lhsN = rhsN := by simpa [lhsN, rhsN] using hentry
      apply intCoeffModEq_eq_true_of_modEq
      exact hlhs.symm.trans ((by rw [hlr] : (lhsN : ℤ) ≡ rhsN [ZMOD (p : ℤ)]).trans hrhs)

theorem phi41QRecurrenceRowsModCertificateNatArrays_sound
    {N p : ℕ}
    {E4Z E6Z E2E4Z : Array ℤ}
    {E4N E6N E2E4N : Array ℕ}
    {rowsZ : Array (Array ℤ)} {rowsN : Array (Array ℕ)}
    (hp : 0 < p)
    (hE4 : TruncCoeffArrayNatModEq N p E4Z E4N)
    (hE6 : TruncCoeffArrayNatModEq N p E6Z E6N)
    (hE2E4 : TruncCoeffArrayNatModEq N p E2E4Z E2E4N)
    (hrows : ∀ j, j < 43 → TruncCoeffArrayNatModEq N p
      (rowsZ.getD j (zeroTruncCoeffArray N)) (rowsN.getD j #[]))
    (hcert : phi41QRecurrenceRowsModCertificateNatArrays
      N p E4N E6N E2E4N rowsN = true) :
    phi41QRecurrenceRowsModCertificateWithCoeffArrays
      N p E4Z E6Z E2E4Z rowsZ = true := by
  unfold phi41QRecurrenceRowsModCertificateNatArrays at hcert
  unfold phi41QRecurrenceRowsModCertificateWithCoeffArrays
  apply List.all_eq_true.mpr
  intro j hjmem
  have hj : j < 43 := List.mem_range.mp hjmem
  have hjcert := List.all_eq_true.mp hcert j hjmem
  exact phi41QRecurrenceRowModCertificateNatArrays_sound hp
    hE4 hE6 hE2E4 (hrows j hj) hjcert

theorem phi41QRecurrenceRowsModCertificateNatArrays_sound_of_conversions
    {N p : ℕ} {E4 E6 E2E4 : Array ℤ}
    {rowsN : Array (Array ℕ)}
    (hp : 0 < p)
    (hcert : phi41QRecurrenceRowsModCertificateNatArrays N p
      (intArrayResiduesToNat p E4)
      (intArrayResiduesToNat p E6)
      (intArrayResiduesToNat p E2E4) rowsN = true) :
    phi41QRecurrenceRowsModCertificateWithCoeffArrays N p E4 E6 E2E4
      (natRowsToInt rowsN) = true := by
  apply phi41QRecurrenceRowsModCertificateNatArrays_sound hp
    (intArrayResiduesToNat_modEq N p E4 hp)
    (intArrayResiduesToNat_modEq N p E6 hp)
    (intArrayResiduesToNat_modEq N p E2E4 hp)
  · intro j hj
    exact natRowsToInt_row_modEq N p rowsN j
  · exact hcert

/-! ## Soundness of the one-pass checked generator -/

private theorem natCoeffAt_push_of_lt (xs : Array ℕ) (x i : ℕ)
    (h : i < xs.size) :
    natCoeffAt (xs.push x) i = natCoeffAt xs i := by
  unfold natCoeffAt Array.getD
  simp only [Array.size_push]
  rw [dif_pos (by omega), dif_pos h]
  exact Array.getElem_push_lt h

private theorem natCoeffAt_push_eq (xs : Array ℕ) (x : ℕ) :
    natCoeffAt (xs.push x) xs.size = x := by
  simp [natCoeffAt, Array.getD]

private theorem sumRangeFromNatModAux_congr
    (p start len acc : ℕ) (f g : ℕ → ℕ)
    (hfg : ∀ i, start ≤ i → i < start + len → f i = g i) :
    sumRangeFromNatModAux p f start len acc =
      sumRangeFromNatModAux p g start len acc := by
  induction len generalizing start acc with
  | zero => rfl
  | succ len ih =>
      simp only [sumRangeFromNatModAux]
      rw [hfg start (by omega) (by omega)]
      apply ih
      intro i hi hlt
      apply hfg i <;> omega

private theorem sumRangeFromNatMod_congr
    (p start len : ℕ) (f g : ℕ → ℕ)
    (hfg : ∀ i, start ≤ i → i < start + len → f i = g i) :
    sumRangeFromNatMod p start len f = sumRangeFromNatMod p start len g := by
  unfold sumRangeFromNatMod
  exact sumRangeFromNatModAux_congr p start len 0 f g hfg

private theorem phi41QRecurrenceTermModNatArrays_push_of_lt
    (p j n a : ℕ) (E4 E6 E2E4 row : Array ℕ) (x : ℕ)
    (h : n - a < row.size) :
    phi41QRecurrenceTermModNatArrays p j n a E4 E6 E2E4 (row.push x) =
      phi41QRecurrenceTermModNatArrays p j n a E4 E6 E2E4 row := by
  unfold phi41QRecurrenceTermModNatArrays
  rw [natCoeffAt_push_of_lt row x (n - a) h]

private theorem phi41QRecurrenceRowModCertificateNatEntry_push_of_lt
    (p j n : ℕ) (E4 E6 E2E4 row : Array ℕ) (x : ℕ)
    (hn : n < row.size) :
    phi41QRecurrenceRowModCertificateNatEntry
        p j n E4 E6 E2E4 (row.push x) =
      phi41QRecurrenceRowModCertificateNatEntry
        p j n E4 E6 E2E4 row := by
  unfold phi41QRecurrenceRowModCertificateNatEntry
  rw [natCoeffAt_push_of_lt row x n hn]
  by_cases hlt : n < 42 - j
  · simp [hlt]
  · by_cases heq : n = 42 - j
    · simp [heq]
    · simp only [hlt, heq, ↓reduceIte]
      congr 1
      apply sumRangeFromNatMod_congr
      intro a ha1 han
      apply phi41QRecurrenceTermModNatArrays_push_of_lt
      omega

private theorem phi41QRecurrenceRowModCertificateNatEntry_push_next
    (p j valuation k : ℕ) (inverses E4 E6 E2E4 out : Array ℕ)
    (hp : 1 < p) (hvaluation : valuation = 42 - j)
    (hsize : out.size = k) :
    let step := phi41QRecurrenceNextCoeffModNatChecked
      p j valuation k inverses E4 E6 E2E4 out
    phi41QRecurrenceRowModCertificateNatEntry
        p j k E4 E6 E2E4 (out.push step.1) = step.2 := by
  subst valuation
  dsimp only
  unfold phi41QRecurrenceNextCoeffModNatChecked
  by_cases hlt : k < 42 - j
  · rw [if_pos hlt]
    unfold phi41QRecurrenceRowModCertificateNatEntry
    rw [if_pos hlt]
    have hnew : natCoeffAt (out.push 0) k = 0 := by
      rw [← hsize]
      exact natCoeffAt_push_eq out 0
    simp [hnew]
  · by_cases heq : k = 42 - j
    · rw [if_neg hlt, if_pos heq]
      unfold phi41QRecurrenceRowModCertificateNatEntry
      rw [if_neg hlt, if_pos heq]
      have hnew : natCoeffAt (out.push 1) k = 1 := by
        rw [← hsize]
        exact natCoeffAt_push_eq out 1
      rw [hnew, Nat.mod_eq_of_lt hp]
      rfl
    · rw [if_neg hlt, if_neg heq]
      let s := sumRangeFromNatMod p 1 k (fun a =>
        let e2e4 := natCoeffAt E2E4 a
        let e6 := natCoeffAt E6 a
        let e4 := natCoeffAt E4 a
        let prev := natCoeffAt out (k - a)
        let c1 := (42 * e2e4) % p
        let c2 := (j * e6) % p
        let c3 := (e4 * (k - a)) % p
        let coeff := subNatResidues p (subNatResidues p c1 c2) c3
        (coeff * prev) % p)
      let next := (s * natCoeffAt inverses (k - (42 - j))) % p
      change phi41QRecurrenceRowModCertificateNatEntry
          p j k E4 E6 E2E4 (out.push next) =
        (((k - (42 - j)) * next) % p == s)
      unfold phi41QRecurrenceRowModCertificateNatEntry
      rw [if_neg hlt, if_neg heq]
      have hnew : natCoeffAt (out.push next) k = next := by
        rw [← hsize]
        exact natCoeffAt_push_eq out next
      rw [hnew]
      congr 1
      apply sumRangeFromNatMod_congr
      intro a ha1 hak
      unfold phi41QRecurrenceTermModNatArrays
      rw [natCoeffAt_push_of_lt out next (k - a) (by omega)]

private theorem phi41QRecurrenceRowModCertificateNatArrays_push_next
    (p j k : ℕ) (inverses E4 E6 E2E4 out : Array ℕ)
    (hp : 1 < p) (hsize : out.size = k)
    (hcert : phi41QRecurrenceRowModCertificateNatArrays
      k p j E4 E6 E2E4 out = true)
    (hstep : (phi41QRecurrenceNextCoeffModNatChecked
      p j (42 - j) k inverses E4 E6 E2E4 out).2 = true) :
    phi41QRecurrenceRowModCertificateNatArrays (k + 1) p j E4 E6 E2E4
      (out.push (phi41QRecurrenceNextCoeffModNatChecked
        p j (42 - j) k inverses E4 E6 E2E4 out).1) = true := by
  unfold phi41QRecurrenceRowModCertificateNatArrays at hcert ⊢
  rw [List.range_succ, List.all_append]
  have hprevious : (List.range k).all (fun n =>
      phi41QRecurrenceRowModCertificateNatEntry p j n E4 E6 E2E4
        (out.push (phi41QRecurrenceNextCoeffModNatChecked
          p j (42 - j) k inverses E4 E6 E2E4 out).1)) = true := by
    apply List.all_eq_true.mpr
    intro n hnmem
    have hn : n < k := List.mem_range.mp hnmem
    rw [phi41QRecurrenceRowModCertificateNatEntry_push_of_lt]
    · exact List.all_eq_true.mp hcert n hnmem
    · omega
  have hlast : [k].all (fun n =>
      phi41QRecurrenceRowModCertificateNatEntry p j n E4 E6 E2E4
        (out.push (phi41QRecurrenceNextCoeffModNatChecked
          p j (42 - j) k inverses E4 E6 E2E4 out).1)) = true := by
    have hentry : phi41QRecurrenceRowModCertificateNatEntry p j k E4 E6 E2E4
        (out.push (phi41QRecurrenceNextCoeffModNatChecked
          p j (42 - j) k inverses E4 E6 E2E4 out).1) = true := by
      rw [phi41QRecurrenceRowModCertificateNatEntry_push_next
        p j (42 - j) k inverses E4 E6 E2E4 out hp rfl hsize]
      exact hstep
    simpa using hentry
  rw [hprevious, hlast]
  rfl

private theorem bool_and_eq_true_left {a b : Bool}
    (h : (a && b) = true) : a = true := by
  cases a <;> simp_all

private theorem bool_and_eq_true_right {a b : Bool}
    (h : (a && b) = true) : b = true := by
  cases a <;> simp_all

private theorem phi41QRecurrenceRowArrayModNatCheckedAux_size
    (p j valuation : ℕ) (inverses E4 E6 E2E4 : Array ℕ) (k : ℕ) :
    (phi41QRecurrenceRowArrayModNatCheckedAux
      p j valuation inverses E4 E6 E2E4 k).1.size = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [phi41QRecurrenceRowArrayModNatCheckedAux, Array.size_push]
      omega

private theorem phi41QRecurrenceRowArrayModNatCheckedAux_sound
    (p j : ℕ) (inverses E4 E6 E2E4 : Array ℕ) (hp : 1 < p) (k : ℕ)
    (hok : (phi41QRecurrenceRowArrayModNatCheckedAux
      p j (42 - j) inverses E4 E6 E2E4 k).2 = true) :
    phi41QRecurrenceRowModCertificateNatArrays k p j E4 E6 E2E4
      (phi41QRecurrenceRowArrayModNatCheckedAux
        p j (42 - j) inverses E4 E6 E2E4 k).1 = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let previous := phi41QRecurrenceRowArrayModNatCheckedAux
        p j (42 - j) inverses E4 E6 E2E4 k
      let step := phi41QRecurrenceNextCoeffModNatChecked
        p j (42 - j) k inverses E4 E6 E2E4 previous.1
      change (previous.2 && step.2) = true at hok
      change phi41QRecurrenceRowModCertificateNatArrays (k + 1) p j
        E4 E6 E2E4 (previous.1.push step.1) = true
      apply phi41QRecurrenceRowModCertificateNatArrays_push_next
        p j k inverses E4 E6 E2E4 previous.1 hp
      · exact phi41QRecurrenceRowArrayModNatCheckedAux_size
          p j (42 - j) inverses E4 E6 E2E4 k
      · apply ih
        exact bool_and_eq_true_left hok
      · exact bool_and_eq_true_right hok

private theorem phi41QRecurrenceRowArrayModNatChecked_sound
    (N p j : ℕ) (inverses E4 E6 E2E4 : Array ℕ) (hp : 1 < p)
    (hok : (phi41QRecurrenceRowArrayModNatChecked
      N p j inverses E4 E6 E2E4).2 = true) :
    phi41QRecurrenceRowModCertificateNatArrays N p j E4 E6 E2E4
      (phi41QRecurrenceRowArrayModNatChecked
        N p j inverses E4 E6 E2E4).1 = true := by
  exact phi41QRecurrenceRowArrayModNatCheckedAux_sound
    p j inverses E4 E6 E2E4 hp N hok

private theorem listMapToArray_getD_of_lt {α β : Type}
    (xs : List α) (f : α → β) (fallback : β) (i : ℕ)
    (hi : i < xs.length) :
    ((xs.map f).toArray).getD i fallback = f xs[i] := by
  unfold Array.getD
  rw [dif_pos (by simpa using hi)]
  have hmap : i < (xs.map f).length := by simpa using hi
  have harray : i < (xs.map f).toArray.size := by simpa using hmap
  change ((xs.map f).toArray)[i]'harray = f (xs[i]'hi)
  simp

theorem phi41QRecurrenceRowsArrayComputeModNatChecked_sound
    (N p : ℕ) (E4 E6 E2E4 : Array ℕ) (hp : 1 < p)
    (hok : (phi41QRecurrenceRowsArrayComputeModNatChecked
      N p E4 E6 E2E4).2 = true) :
    phi41QRecurrenceRowsModCertificateNatArrays N p E4 E6 E2E4
      (phi41QRecurrenceRowsArrayComputeModNatChecked
        N p E4 E6 E2E4).1 = true := by
  let inverses := modInvNatTable N p
  let row := fun j => phi41QRecurrenceRowArrayModNatChecked
    N p j inverses E4 E6 E2E4
  let checked := (List.range 43).map row
  change checked.all Prod.snd = true at hok
  change phi41QRecurrenceRowsModCertificateNatArrays N p E4 E6 E2E4
    ((checked.map Prod.fst).toArray) = true
  unfold phi41QRecurrenceRowsModCertificateNatArrays
  apply List.all_eq_true.mpr
  intro j hjmem
  have hj : j < 43 := List.mem_range.mp hjmem
  have hrowmem : row j ∈ checked := by
    unfold checked
    exact List.mem_map.mpr ⟨j, hjmem, rfl⟩
  have hrowok : (row j).2 = true :=
    List.all_eq_true.mp hok (row j) hrowmem
  have hget : ((checked.map Prod.fst).toArray).getD j #[] = (row j).1 := by
    have hjchecked : j < checked.length := by
      simp [checked, hj]
    rw [listMapToArray_getD_of_lt checked Prod.fst #[] j hjchecked]
    unfold checked
    simp [row]
  rw [hget]
  exact phi41QRecurrenceRowArrayModNatChecked_sound
    N p j inverses E4 E6 E2E4 hp hrowok

theorem phi41QRecurrenceRowsArrayComputeModNatChecked_sound_of_conversions
    {N p : ℕ} {E4 E6 E2E4 : Array ℤ} (hp : 1 < p)
    (hok : (phi41QRecurrenceRowsArrayComputeModNatChecked N p
      (intArrayResiduesToNat p E4)
      (intArrayResiduesToNat p E6)
      (intArrayResiduesToNat p E2E4)).2 = true) :
    phi41QRecurrenceRowsModCertificateWithCoeffArrays N p E4 E6 E2E4
      (natRowsToInt (phi41QRecurrenceRowsArrayComputeModNatChecked N p
        (intArrayResiduesToNat p E4)
        (intArrayResiduesToNat p E6)
        (intArrayResiduesToNat p E2E4)).1) = true := by
  apply phi41QRecurrenceRowsModCertificateNatArrays_sound_of_conversions (by omega)
  exact phi41QRecurrenceRowsArrayComputeModNatChecked_sound
    N p (intArrayResiduesToNat p E4) (intArrayResiduesToNat p E6)
      (intArrayResiduesToNat p E2E4) hp hok

/-! ## Per-prime row definitions -/

def sturmCRTM : ℕ := (phi41Level41SturmBound + 40) / 41

/-! ## Coefficient reduction before recurrence evaluation -/

/-- Keep exactly the first `N` coefficients and replace each by its residue mod `p`.
This prevents the recurrence evaluator from repeatedly multiplying the very large
integer coefficients of the Eisenstein-series truncations. -/
def sturmCRTCoeffArrayMod (N p : ℕ) (xs : Array ℤ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun n => truncCoeffArrayAt xs n % (p : ℤ))

theorem sturmCRTCoeffArrayMod_modEq (N p : ℕ) (xs : Array ℤ) :
    TruncCoeffArrayModEq N p xs (sturmCRTCoeffArrayMod N p xs) := by
  intro n hn
  rw [sturmCRTCoeffArrayMod, truncCoeffArrayAt_ofFn_of_lt hn]
  exact (Int.mod_modEq _ _).symm

def sturmCRTE4Mod (N p : ℕ) : Array ℤ :=
  sturmCRTCoeffArrayMod N p (E4TruncCoeffArray N)

def sturmCRTE6Mod (N p : ℕ) : Array ℤ :=
  sturmCRTCoeffArrayMod N p (E6TruncCoeffArray N)

def sturmCRTE2E4Mod (N p : ℕ) : Array ℤ :=
  sturmCRTCoeffArrayMod N p (E2E4TruncCoeffArray N)

def sturmCRTE4ModNat (N p : ℕ) : Array ℕ :=
  intArrayResiduesToNat p (sturmCRTE4Mod N p)

def sturmCRTE6ModNat (N p : ℕ) : Array ℕ :=
  intArrayResiduesToNat p (sturmCRTE6Mod N p)

def sturmCRTE2E4ModNat (N p : ℕ) : Array ℕ :=
  intArrayResiduesToNat p (sturmCRTE2E4Mod N p)

def sturmCRTPCompressedModNatChecked (p : ℕ) : Array (Array ℕ) × Bool :=
  phi41QRecurrenceRowsArrayComputeModNatChecked sturmCRTM p
    (sturmCRTE4ModNat sturmCRTM p)
    (sturmCRTE6ModNat sturmCRTM p)
    (sturmCRTE2E4ModNat sturmCRTM p)

def sturmCRTQModNatChecked (p : ℕ) : Array (Array ℕ) × Bool :=
  phi41QRecurrenceRowsArrayComputeModNatChecked phi41Level41SturmBound p
    (sturmCRTE4ModNat phi41Level41SturmBound p)
    (sturmCRTE6ModNat phi41Level41SturmBound p)
    (sturmCRTE2E4ModNat phi41Level41SturmBound p)

def sturmCRTPCompressedModNat (p : ℕ) : Array (Array ℕ) :=
  (sturmCRTPCompressedModNatChecked p).1

def sturmCRTQModNat (p : ℕ) : Array (Array ℕ) :=
  (sturmCRTQModNatChecked p).1

def sturmCRTPCompressedMod (p : ℕ) : Array (Array ℤ) :=
  natRowsToInt (sturmCRTPCompressedModNat p)

def sturmCRTQMod (p : ℕ) : Array (Array ℤ) :=
  natRowsToInt (sturmCRTQModNat p)

/-! ## Per-prime opaque check components (for cheap bridge proofs) -/

def sturmCRT_hP (p : ℕ) : Bool :=
  (sturmCRTPCompressedModNatChecked p).2

def sturmCRT_hQ (p : ℕ) : Bool :=
  (sturmCRTQModNatChecked p).2

def sturmCRT_hz (p : ℕ) : Bool :=
  truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
    (phi41Level41RecurrenceCoeffArrayFromRows
      phi41Level41SturmBound sturmCRTM
      (sturmCRTPCompressedMod p) (sturmCRTQMod p))

/-! ## Combined per-prime check -/

def sturmCRTCheckAll (p : ℕ) : Bool :=
  let M := sturmCRTM
  let N := phi41Level41SturmBound
  let E4M := sturmCRTE4Mod M p
  let E6M := sturmCRTE6Mod M p
  let E2E4M := sturmCRTE2E4Mod M p
  let E4N := sturmCRTE4Mod N p
  let E6N := sturmCRTE6Mod N p
  let E2E4N := sturmCRTE2E4Mod N p
  let E4MNat := intArrayResiduesToNat p E4M
  let E6MNat := intArrayResiduesToNat p E6M
  let E2E4MNat := intArrayResiduesToNat p E2E4M
  let E4NNat := intArrayResiduesToNat p E4N
  let E6NNat := intArrayResiduesToNat p E6N
  let E2E4NNat := intArrayResiduesToNat p E2E4N
  let Pchecked := phi41QRecurrenceRowsArrayComputeModNatChecked
    M p E4MNat E6MNat E2E4MNat
  let Qchecked := phi41QRecurrenceRowsArrayComputeModNatChecked
    N p E4NNat E6NNat E2E4NNat
  let Prows := natRowsToInt Pchecked.1
  let Qrows := natRowsToInt Qchecked.1
  Pchecked.2 && Qchecked.2 &&
    truncCoeffArrayFirstZeroMod N p
      (phi41Level41RecurrenceCoeffArrayFromRows N M Prows Qrows)

/-! ## Bridge: combined check → component forms -/

private theorem sturmCRTCheckAll_expand (p : ℕ) :
    sturmCRTCheckAll p = (sturmCRT_hP p && sturmCRT_hQ p && sturmCRT_hz p) := rfl

theorem sturmCRTCheckAll_hPcert {p : ℕ} (hp : 1 < p)
    (h : sturmCRTCheckAll p = true) :
    phi41QRecurrenceRowsModCertificateWithCoeffArrays sturmCRTM p
      (sturmCRTE4Mod sturmCRTM p)
      (sturmCRTE6Mod sturmCRTM p)
      (sturmCRTE2E4Mod sturmCRTM p)
      (sturmCRTPCompressedMod p) = true := by
  have hP : sturmCRT_hP p = true := by
    rw [sturmCRTCheckAll_expand] at h
    revert h
    cases sturmCRT_hP p <;> simp
  change phi41QRecurrenceRowsModCertificateWithCoeffArrays sturmCRTM p
    (sturmCRTE4Mod sturmCRTM p)
    (sturmCRTE6Mod sturmCRTM p)
    (sturmCRTE2E4Mod sturmCRTM p)
    (natRowsToInt (sturmCRTPCompressedModNat p)) = true
  apply phi41QRecurrenceRowsArrayComputeModNatChecked_sound_of_conversions hp
  simpa [sturmCRT_hP, sturmCRTPCompressedModNatChecked,
    sturmCRTE4ModNat, sturmCRTE6ModNat, sturmCRTE2E4ModNat] using hP

theorem sturmCRTCheckAll_hQcert {p : ℕ} (hp : 1 < p)
    (h : sturmCRTCheckAll p = true) :
    phi41QRecurrenceRowsModCertificateWithCoeffArrays phi41Level41SturmBound p
      (sturmCRTE4Mod phi41Level41SturmBound p)
      (sturmCRTE6Mod phi41Level41SturmBound p)
      (sturmCRTE2E4Mod phi41Level41SturmBound p)
      (sturmCRTQMod p) = true := by
  have hQ : sturmCRT_hQ p = true := by
    rw [sturmCRTCheckAll_expand] at h
    revert h
    cases sturmCRT_hP p <;> cases sturmCRT_hQ p <;> simp
  change phi41QRecurrenceRowsModCertificateWithCoeffArrays
    phi41Level41SturmBound p
    (sturmCRTE4Mod phi41Level41SturmBound p)
    (sturmCRTE6Mod phi41Level41SturmBound p)
    (sturmCRTE2E4Mod phi41Level41SturmBound p)
    (natRowsToInt (sturmCRTQModNat p)) = true
  apply phi41QRecurrenceRowsArrayComputeModNatChecked_sound_of_conversions hp
  simpa [sturmCRT_hQ, sturmCRTQModNatChecked,
    sturmCRTE4ModNat, sturmCRTE6ModNat, sturmCRTE2E4ModNat] using hQ

theorem sturmCRTCheckAll_hzero {p : ℕ} (h : sturmCRTCheckAll p = true) :
    truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
      (phi41Level41RecurrenceCoeffArrayFromRows
        phi41Level41SturmBound sturmCRTM
        (sturmCRTPCompressedMod p) (sturmCRTQMod p)) = true := by
  change sturmCRT_hz p = true
  rw [sturmCRTCheckAll_expand] at h
  revert h; cases sturmCRT_hP p <;> cases sturmCRT_hQ p <;> cases sturmCRT_hz p <;> simp

end Ripple.Number.Modular
