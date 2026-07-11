import Ripple.Number.Modular.ModularPolynomialQExpansion
import Batteries.Data.Range.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.PowerSeries.Derivative

set_option linter.style.longFile 9000

namespace Ripple
namespace Number
namespace Modular

open EisensteinSeries
open CongruenceSubgroup
open UpperHalfPlane
open scoped UpperHalfPlane
open scoped MatrixGroups
open scoped Manifold
open scoped ModularForm
open scoped PowerSeries.WithPiTopology

/-- CRT-style integer elimination: if an integer is zero modulo a modulus
larger than its absolute value, then it is actually zero. -/
theorem int_eq_zero_of_modEq_zero_of_abs_lt {P a : ℤ}
    (hbound : |a| < P) (hmod : a ≡ 0 [ZMOD P]) : a = 0 := by
  have hdvd : P ∣ a := Int.modEq_zero_iff_dvd.mp hmod
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  have hnat := Int.natAbs_lt_natAbs_of_nonneg_of_lt (abs_nonneg a) hbound
  simpa [Int.natAbs_abs] using hnat

theorem nat_list_prod_dvd_of_pairwise_coprime_dvd {ps : List ℕ}
    (hcop : ps.Pairwise Nat.Coprime) {m : ℕ}
    (hdvd : ∀ p ∈ ps, p ∣ m) : ps.prod ∣ m := by
  have hmodsIdx : ∀ i : Fin ps.length, m ≡ 0 [MOD ps.get i] := by
    intro i
    exact Nat.modEq_zero_iff_dvd.mpr (hdvd (ps.get i) (List.get_mem ps i))
  have hprod : m ≡ 0 [MOD ps.prod] :=
    (Nat.modEq_list_prod_iff hcop).mpr hmodsIdx
  exact Nat.modEq_zero_iff_dvd.mp hprod

theorem list_pairwise_coprime_of_nodup_prime {ps : List ℕ}
    (hnodup : ps.Nodup) (hprime : ∀ p ∈ ps, Nat.Prime p) :
    ps.Pairwise Nat.Coprime := by
  induction ps with
  | nil =>
      simp
  | cons p ps ih =>
      rw [List.pairwise_cons]
      constructor
      · intro q hq
        have hp : Nat.Prime p := hprime p (by simp)
        have hqprime : Nat.Prime q := hprime q (by simp [hq])
        have hpq : p ≠ q := by
          intro heq
          have hp_not_mem : p ∉ ps := by
            simpa using (List.nodup_cons.mp hnodup).1
          exact hp_not_mem (by simpa [heq] using hq)
        exact (Nat.coprime_primes hp hqprime).mpr hpq
      · exact ih (List.nodup_cons.mp hnodup).2 (by
          intro q hq
          exact hprime q (by simp [hq]))

theorem int_modEq_zero_list_prod_of_pairwise_coprime {ps : List ℕ}
    (hcop : ps.Pairwise Nat.Coprime) {a : ℤ}
    (hmods : ∀ p ∈ ps, a ≡ 0 [ZMOD (p : ℤ)]) :
    a ≡ 0 [ZMOD (ps.prod : ℤ)] := by
  have hdvdNat : ps.prod ∣ a.natAbs := by
    apply nat_list_prod_dvd_of_pairwise_coprime_dvd hcop
    intro p hp
    have hdvdInt : (p : ℤ) ∣ a := Int.modEq_zero_iff_dvd.mp (hmods p hp)
    exact Int.natCast_dvd.mp hdvdInt
  exact Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd.mpr hdvdNat)

theorem int_eq_zero_of_modEq_zero_list_of_abs_lt_prod {ps : List ℕ}
    (hcop : ps.Pairwise Nat.Coprime) {a : ℤ}
    (hbound : |a| < (ps.prod : ℤ))
    (hmods : ∀ p ∈ ps, a ≡ 0 [ZMOD (p : ℤ)]) : a = 0 :=
  int_eq_zero_of_modEq_zero_of_abs_lt hbound
    (int_modEq_zero_list_prod_of_pairwise_coprime hcop hmods)

theorem int_eq_zero_of_modEq_zero_list_of_abs_le_bound_lt_prod {ps : List ℕ}
    (hcop : ps.Pairwise Nat.Coprime) {a B : ℤ}
    (habs : |a| ≤ B) (hB : B < (ps.prod : ℤ))
    (hmods : ∀ p ∈ ps, a ≡ 0 [ZMOD (p : ℤ)]) : a = 0 :=
  int_eq_zero_of_modEq_zero_list_of_abs_lt_prod hcop
    (lt_of_le_of_lt habs hB) hmods

theorem int_modEq_cancel_mul_left_of_coprime {P d a b : ℤ}
    (hP : 0 < P) (hcop : Int.gcd P d = 1)
    (h : d * a ≡ d * b [ZMOD P]) : a ≡ b [ZMOD P] := by
  have hcancel := Int.ModEq.cancel_left_div_gcd hP h
  simpa [hcop] using hcancel

theorem int_division_modEq_of_mul_modEq {P d s q r : ℤ}
    (hP : 0 < P) (hcop : Int.gcd P d = 1)
    (hs : s = d * q) (hmod : d * r ≡ s [ZMOD P]) :
    q ≡ r [ZMOD P] := by
  apply int_modEq_cancel_mul_left_of_coprime hP hcop
  have hsym : s ≡ d * r [ZMOD P] := hmod.symm
  simpa [hs] using hsym

theorem int_gcd_natCast_eq_one_of_prime_gt {p d : ℕ}
    (hp : Nat.Prime p) (hdpos : 0 < d) (hdlt : d < p) :
    Int.gcd (p : ℤ) (d : ℤ) = 1 := by
  rw [Int.gcd_natCast_natCast]
  exact (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hdpos hdlt)).gcd_eq_one

def truncCoeffAt (xs : List ℤ) (n : ℕ) : ℤ :=
  xs.getD n 0

/-- The first `N` coefficients of a computable integer sequence. -/
def truncCoeffList (N : ℕ) (f : ℕ → ℤ) : List ℤ :=
  (List.range N).map f

theorem truncCoeffAt_truncCoeffList_of_lt {N n : ℕ} {f : ℕ → ℤ}
    (hn : n < N) :
    truncCoeffAt (truncCoeffList N f) n = f n := by
  simp [truncCoeffAt, truncCoeffList, hn]

/-- Zero truncated series of length `N`. -/
def zeroTruncCoeffList (N : ℕ) : List ℤ :=
  truncCoeffList N (fun _ => 0)

/-- Constant truncated series of length `N`. -/
def constTruncCoeffList (N : ℕ) (c : ℤ) : List ℤ :=
  truncCoeffList N (fun n => if n = 0 then c else 0)

/-- Termwise sum of truncated coefficient lists. -/
def addTruncCoeffList (N : ℕ) (a b : List ℤ) : List ℤ :=
  truncCoeffList N (fun n => truncCoeffAt a n + truncCoeffAt b n)

/-- Scalar multiple of a truncated coefficient list. -/
def scaleTruncCoeffList (N : ℕ) (c : ℤ) (a : List ℤ) : List ℤ :=
  truncCoeffList N (fun n => c * truncCoeffAt a n)

/-- Difference of truncated coefficient lists. -/
def subTruncCoeffList (N : ℕ) (a b : List ℤ) : List ℤ :=
  addTruncCoeffList N a (scaleTruncCoeffList N (-1) b)

/-- Cauchy product, truncated to the first `N` coefficients. -/
def mulTruncCoeffList (N : ℕ) (a b : List ℤ) : List ℤ :=
  truncCoeffList N
    (fun n => ∑ ij ∈ Finset.antidiagonal n,
      truncCoeffAt a ij.1 * truncCoeffAt b ij.2)

/-- Repeated truncated Cauchy product. -/
def powTruncCoeffList (N : ℕ) (a : List ℤ) : ℕ → List ℤ
  | 0 => constTruncCoeffList N 1
  | k + 1 => mulTruncCoeffList N (powTruncCoeffList N a k) a

/-- Powers `1, a, a², ..., a^maxPow`, all truncated to length `N`.  This
is computed incrementally so the coefficient checker does not repeatedly
recompute powers. -/
def powTruncCoeffTableAux (N : ℕ) (base : List ℤ) :
    List ℤ → ℕ → List (List ℤ)
  | current, 0 => [current]
  | current, k + 1 =>
      current :: powTruncCoeffTableAux N base
        (mulTruncCoeffList N current base) k

def powTruncCoeffTable (N : ℕ) (base : List ℤ) (maxPow : ℕ) :
    List (List ℤ) :=
  powTruncCoeffTableAux N base (constTruncCoeffList N 1) maxPow

theorem powTruncCoeffTableAux_getD_of_le
    (N : ℕ) (base : List ℤ) :
    ∀ (maxPow offset k : ℕ), k ≤ maxPow →
      (powTruncCoeffTableAux N base
        (powTruncCoeffList N base offset) maxPow).getD k
          (zeroTruncCoeffList N) =
        powTruncCoeffList N base (offset + k)
  | 0, offset, k, hk => by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [powTruncCoeffTableAux]
  | maxPow + 1, offset, k, hk => by
      cases k with
      | zero =>
          simp [powTruncCoeffTableAux]
      | succ k =>
          have hk' : k ≤ maxPow := Nat.succ_le_succ_iff.mp hk
          have hrec :=
            powTruncCoeffTableAux_getD_of_le N base maxPow (offset + 1) k hk'
          rw [powTruncCoeffTableAux]
          simpa [powTruncCoeffList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hrec

theorem powTruncCoeffTable_getD_of_le
    (N : ℕ) (base : List ℤ) {k maxPow : ℕ} (hk : k ≤ maxPow) :
    (powTruncCoeffTable N base maxPow).getD k (zeroTruncCoeffList N) =
      powTruncCoeffList N base k := by
  simpa [powTruncCoeffTable] using
    powTruncCoeffTableAux_getD_of_le N base maxPow 0 k hk

/-- Truncated coefficient list for the pullback `q ↦ q^41`. -/
def qPullback41TruncCoeffList (N : ℕ) (a : List ℤ) : List ℤ :=
  truncCoeffList N
    (fun n => if 41 ∣ n then truncCoeffAt a (n / 41) else 0)

/-- Truncated coefficient list for `X^m`. -/
def XPowTruncCoeffList (N m : ℕ) : List ℤ :=
  truncCoeffList N (fun n => if n = m then 1 else 0)

/-- Truncated integer coefficient list for `E₄`. -/
def E4TruncCoeffList (N : ℕ) : List ℤ :=
  truncCoeffList N E4CoeffZ

/-- Multiply a truncated list by the Euler factor `(1 - q^m)^24`.
This sparse multiplication avoids constructing noncomputable `Polynomial`
objects and is the finite algorithm used by the Sturm coefficient checker. -/
def mulDeltaEulerFactorTruncCoeffList (N : ℕ) (a : List ℤ) (m : ℕ) :
    List ℤ :=
  truncCoeffList N
    (fun n => ∑ j ∈ Finset.range 25,
      if j * m ≤ n then
        ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
          truncCoeffAt a (n - j * m)
      else 0)

/-- Truncated coefficient list for `q * ∏_{m=1}^{N} (1-q^m)^24`. -/
def deltaEulerTruncCoeffListAux (N : ℕ) : ℕ → List ℤ
  | 0 => truncCoeffList N (fun n => if n = 1 then 1 else 0)
  | k + 1 =>
      mulDeltaEulerFactorTruncCoeffList N
        (deltaEulerTruncCoeffListAux N k) (k + 1)

def deltaEulerTruncCoeffList (N : ℕ) : List ℤ :=
  deltaEulerTruncCoeffListAux N N

/-- Proof-friendly truncated list for the Euler factor `(1 - q^m)^24`.
The fast checker uses the sparse closed form above; this one is used to connect
the finite list model to `PowerSeries`. -/
def deltaEulerFactorTruncCoeffListSlow (N m : ℕ) : List ℤ :=
  powTruncCoeffList N
    (subTruncCoeffList N (constTruncCoeffList N 1) (XPowTruncCoeffList N m)) 24

/-- Proof-facing sparse truncated list for the Euler factor `(1 - q^m)^24`,
using the binomial expansion directly. -/
def deltaEulerFactorSparseTruncCoeffList (N m : ℕ) : List ℤ :=
  truncCoeffList N (fun n =>
    ∑ j ∈ Finset.range 25,
      if n = j * m then
        ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ))
      else 0)

/-- Proof-friendly truncated list for
`q * ∏_{m=1}^{M} (1-q^m)^24`. -/
def deltaEulerProductTruncCoeffListSlow (N : ℕ) : ℕ → List ℤ
  | 0 => XPowTruncCoeffList N 1
  | M + 1 =>
      mulTruncCoeffList N (deltaEulerProductTruncCoeffListSlow N M)
        (deltaEulerFactorTruncCoeffListSlow N (M + 1))

/-- Proof-facing Euler product truncation using sparse binomial factors.  This
is closer to the fast checker than `deltaEulerProductTruncCoeffListSlow`, but
still uses ordinary Cauchy multiplication. -/
def deltaEulerProductTruncCoeffListSparse (N : ℕ) : ℕ → List ℤ
  | 0 => XPowTruncCoeffList N 1
  | M + 1 =>
      mulTruncCoeffList N (deltaEulerProductTruncCoeffListSparse N M)
        (deltaEulerFactorSparseTruncCoeffList N (M + 1))

/-- Products `A^x B^(42-x)` for `0 ≤ x ≤ 42`, represented as truncated
coefficient lists. -/
def phi41TermProductTable (N : ℕ) (A B : List (List ℤ)) :
    List (List ℤ) :=
  (List.range 43).map
    (fun x => mulTruncCoeffList N
      (A.getD x (zeroTruncCoeffList N))
      (B.getD (42 - x) (zeroTruncCoeffList N)))

theorem phi41TermProductTable_getD_of_le
    (N : ℕ) (A B : List (List ℤ)) {x : ℕ} (hx : x ≤ 42) :
    (phi41TermProductTable N A B).getD x (zeroTruncCoeffList N) =
      mulTruncCoeffList N
        (A.getD x (zeroTruncCoeffList N))
        (B.getD (42 - x) (zeroTruncCoeffList N)) := by
  have hlen : x < (phi41TermProductTable N A B).length := by
    simp [phi41TermProductTable]
    omega
  rw [List.getD_eq_getElem (l := phi41TermProductTable N A B)
    (d := zeroTruncCoeffList N) hlen]
  simp [phi41TermProductTable]

/-- Evaluate the sparse cleared Φ₄₁ expression from precomputed product
tables `P[x] = A^x B^(42-x)` and `Q[y] = C^y D^(42-y)`. -/
def evalSparseFromProductTablesTrunc (N : ℕ)
    (P Q : List (List ℤ)) : List SparseBivarTerm → List ℤ
  | [] => zeroTruncCoeffList N
  | t :: ts =>
      addTruncCoeffList N
        (scaleTruncCoeffList N t.coeff
          (mulTruncCoeffList N
            (P.getD t.xPow (zeroTruncCoeffList N))
            (Q.getD t.yPow (zeroTruncCoeffList N))))
        (evalSparseFromProductTablesTrunc N P Q ts)

/-- Direct truncated-list evaluator mirroring `evalSparseBivarCleared`.  This
version is convenient for proving coefficient correctness; the table-based
version above is the faster computational target. -/
def evalSparseBivarClearedTruncCoeffList (N : ℕ) :
    List SparseBivarTerm → ℕ → ℕ → List ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | [], _, _, _, _, _, _ => zeroTruncCoeffList N
  | t :: ts, xMax, yMax, xNum, xDen, yNum, yDen =>
      addTruncCoeffList N
        (scaleTruncCoeffList N t.coeff
          (mulTruncCoeffList N
            (mulTruncCoeffList N
              (powTruncCoeffList N xNum t.xPow)
              (powTruncCoeffList N xDen (xMax - t.xPow)))
            (mulTruncCoeffList N
              (powTruncCoeffList N yNum t.yPow)
              (powTruncCoeffList N yDen (yMax - t.yPow)))))
        (evalSparseBivarClearedTruncCoeffList N ts xMax yMax xNum xDen yNum yDen)

theorem evalSparseFromProductTablesTrunc_eq_evalSparseBivarClearedTruncCoeffList
    (N : ℕ) (terms : List SparseBivarTerm)
    (xNum xDen yNum yDen : List ℤ)
    (hdeg : ∀ t ∈ terms, t.xPow ≤ 42 ∧ t.yPow ≤ 42) :
    evalSparseFromProductTablesTrunc N
        (phi41TermProductTable N
          (powTruncCoeffTable N xNum 42) (powTruncCoeffTable N xDen 42))
        (phi41TermProductTable N
          (powTruncCoeffTable N yNum 42) (powTruncCoeffTable N yDen 42))
        terms =
      evalSparseBivarClearedTruncCoeffList N terms 42 42 xNum xDen yNum yDen := by
  induction terms with
  | nil =>
      rfl
  | cons t ts ih =>
      have htdeg : t.xPow ≤ 42 ∧ t.yPow ≤ 42 := hdeg t (by simp)
      have htsdeg : ∀ u ∈ ts, u.xPow ≤ 42 ∧ u.yPow ≤ 42 := by
        intro u hu
        exact hdeg u (by simp [hu])
      rw [evalSparseFromProductTablesTrunc, evalSparseBivarClearedTruncCoeffList,
        ih htsdeg]
      rw [phi41TermProductTable_getD_of_le N
          (powTruncCoeffTable N xNum 42) (powTruncCoeffTable N xDen 42) htdeg.1,
        phi41TermProductTable_getD_of_le N
          (powTruncCoeffTable N yNum 42) (powTruncCoeffTable N yDen 42) htdeg.2]
      rw [powTruncCoeffTable_getD_of_le N xNum htdeg.1,
        powTruncCoeffTable_getD_of_le N yNum htdeg.2]
      have hxDen : 42 - t.xPow ≤ 42 := Nat.sub_le 42 t.xPow
      have hyDen : 42 - t.yPow ≤ 42 := Nat.sub_le 42 t.yPow
      rw [powTruncCoeffTable_getD_of_le N xDen hxDen,
        powTruncCoeffTable_getD_of_le N yDen hyDen]

/-- Computable truncated coefficient model for
`phi41Level41ClearedEulerQExpansionZ`.  This is not yet connected to the
formal `PowerSeries` coefficient theorem; it is the reflection target for the
finite Sturm certificate. -/
def phi41Level41FastCoeffList (N : ℕ) : List ℤ :=
  let E := E4TruncCoeffList N
  let D := deltaEulerTruncCoeffList N
  let C := powTruncCoeffList N E 3
  let A := qPullback41TruncCoeffList N C
  let B := qPullback41TruncCoeffList N D
  let APow := powTruncCoeffTable N A 42
  let BPow := powTruncCoeffTable N B 42
  let CPow := powTruncCoeffTable N C 42
  let DPow := powTruncCoeffTable N D 42
  let P := phi41TermProductTable N APow BPow
  let Q := phi41TermProductTable N CPow DPow
  evalSparseFromProductTablesTrunc N P Q phi41SparseTerms

theorem phi41Level41FastCoeffList_eq_direct (N : ℕ) :
    phi41Level41FastCoeffList N =
      evalSparseBivarClearedTruncCoeffList N phi41SparseTerms 42 42
        (qPullback41TruncCoeffList N
          (powTruncCoeffList N (E4TruncCoeffList N) 3))
        (qPullback41TruncCoeffList N (deltaEulerTruncCoeffList N))
        (powTruncCoeffList N (E4TruncCoeffList N) 3)
        (deltaEulerTruncCoeffList N) := by
  unfold phi41Level41FastCoeffList
  exact evalSparseFromProductTablesTrunc_eq_evalSparseBivarClearedTruncCoeffList
    N phi41SparseTerms
    (qPullback41TruncCoeffList N
      (powTruncCoeffList N (E4TruncCoeffList N) 3))
    (qPullback41TruncCoeffList N (deltaEulerTruncCoeffList N))
    (powTruncCoeffList N (E4TruncCoeffList N) 3)
    (deltaEulerTruncCoeffList N)
    (fun t ht => phi41SparseTerms_degree_le_42 t ht)

def truncCoeffListFirstZero (K : ℕ) (xs : List ℤ) : Bool :=
  (List.range K).all (fun n => truncCoeffAt xs n == 0)

theorem truncCoeffListFirstZero_of_crt_certificate {K : ℕ} {xs : List ℤ}
    {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    (hbound : ∀ n : ℕ, n < K → |truncCoeffAt xs n| < (ps.prod : ℤ))
    (hmods : ∀ n : ℕ, n < K → ∀ p ∈ ps,
      truncCoeffAt xs n ≡ 0 [ZMOD (p : ℤ)]) :
    truncCoeffListFirstZero K xs = true := by
  unfold truncCoeffListFirstZero
  apply List.all_eq_true.mpr
  intro n hnmem
  have hn : n < K := List.mem_range.mp hnmem
  have hz :
      truncCoeffAt xs n = 0 :=
    int_eq_zero_of_modEq_zero_list_of_abs_lt_prod
      hcop (hbound n hn) (hmods n hn)
  simp [hz]

theorem truncCoeffListFirstZero_of_crt_bounded_certificate {K : ℕ}
    {xs : List ℤ} {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    {B : ℕ}
    (hbound : ∀ n : ℕ, n < K → |truncCoeffAt xs n| ≤ (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (hmods : ∀ n : ℕ, n < K → ∀ p ∈ ps,
      truncCoeffAt xs n ≡ 0 [ZMOD (p : ℤ)]) :
    truncCoeffListFirstZero K xs = true := by
  apply truncCoeffListFirstZero_of_crt_certificate hcop
  · intro n hn
    exact lt_of_le_of_lt (hbound n hn) hB
  · exact hmods

theorem truncCoeffAt_eq_zero_of_firstZero {K : ℕ} {xs : List ℤ} {n : ℕ}
    (h : truncCoeffListFirstZero K xs = true) (hn : n < K) :
    truncCoeffAt xs n = 0 := by
  unfold truncCoeffListFirstZero at h
  have hnmem : n ∈ List.range K := by
    simpa using List.mem_range.mpr hn
  have hall := List.all_eq_true.mp h n hnmem
  simpa using hall

/-! ### VM-oriented array coefficient checker

The list/`Finset` checker above is proof-friendly, but full Sturm-bound
evaluation is too slow in the Lean VM.  The following definitions are a
computational mirror using mutable arrays and tight loops.  They are kept
separate from the proof-facing `TruncRep` model; the next proof layer should
connect the array model to the list model coefficientwise. -/

def truncCoeffArrayOfFn (N : ℕ) (f : ℕ → ℤ) : Array ℤ := Id.run do
  let mut out : Array ℤ := #[]
  for n in [0:N] do
    out := out.push (f n)
  return out

def truncCoeffArrayAt (a : Array ℤ) (n : ℕ) : ℤ :=
  a.getD n 0

theorem truncCoeffArrayAt_push_of_lt {a : Array ℤ} {n : ℕ} (v : ℤ)
    (hn : n < a.size) :
    truncCoeffArrayAt (a.push v) n = truncCoeffArrayAt a n := by
  unfold truncCoeffArrayAt Array.getD
  simp [hn, Array.getElem_push_lt]
  omega

theorem truncCoeffArrayAt_push_eq {a : Array ℤ} (v : ℤ) :
    truncCoeffArrayAt (a.push v) a.size = v := by
  unfold truncCoeffArrayAt Array.getD
  simp [Array.size_push]

theorem truncCoeffArrayAt_push_eq_of_size {a : Array ℤ} {n : ℕ} (v : ℤ)
    (hn : n = a.size) :
    truncCoeffArrayAt (a.push v) n = v := by
  subst n
  exact truncCoeffArrayAt_push_eq v

def sumRangeZ (K : ℕ) (f : ℕ → ℤ) : ℤ :=
  match K with
  | 0 => 0
  | k + 1 => sumRangeZ k f + f k

theorem sumRangeZ_eq_finset_sum (K : ℕ) (f : ℕ → ℤ) :
    sumRangeZ K f = ∑ i ∈ Finset.range K, f i := by
  induction K with
  | zero =>
      simp [sumRangeZ]
  | succ K ih =>
      simp [sumRangeZ, ih, Finset.sum_range_succ]

def sumRangeFromZ (start len : ℕ) (f : ℕ → ℤ) : ℤ :=
  match len with
  | 0 => 0
  | k + 1 => f start + sumRangeFromZ (start + 1) k f

theorem sumRangeFromZ_eq_finset_sum (start len : ℕ) (f : ℕ → ℤ) :
    sumRangeFromZ start len f = ∑ i ∈ Finset.range len, f (start + i) := by
  induction len generalizing start with
  | zero =>
      simp [sumRangeFromZ]
  | succ len ih =>
      rw [sumRangeFromZ, Finset.sum_range_succ']
      rw [ih]
      ring_nf

theorem sumRangeFromZ_zero_eq_finset_sum (K : ℕ) (f : ℕ → ℤ) :
    sumRangeFromZ 0 K f = ∑ i ∈ Finset.range K, f i := by
  rw [sumRangeFromZ_eq_finset_sum]
  simp

theorem sumRangeFromZ_congr {start len : ℕ} {f g : ℕ → ℤ}
    (h : ∀ i, start ≤ i → i < start + len → f i = g i) :
    sumRangeFromZ start len f = sumRangeFromZ start len g := by
  induction len generalizing start with
  | zero =>
      simp [sumRangeFromZ]
  | succ len ih =>
      simp only [sumRangeFromZ]
      have hhead : f start = g start := h start (by omega) (by omega)
      have htail :
          sumRangeFromZ (start + 1) len f =
            sumRangeFromZ (start + 1) len g := by
        apply ih
        intro i hi1 hi2
        apply h i <;> omega
      rw [hhead, htail]

theorem sumRangeFromZ_modEq {P : ℤ} {start len : ℕ} {f g : ℕ → ℤ}
    (h : ∀ i, start ≤ i → i < start + len → f i ≡ g i [ZMOD P]) :
    sumRangeFromZ start len f ≡ sumRangeFromZ start len g [ZMOD P] := by
  induction len generalizing start with
  | zero =>
      simp [sumRangeFromZ]
  | succ len ih =>
      simp only [sumRangeFromZ]
      exact (h start (by omega) (by omega)).add (ih (by
        intro i hi1 hi2
        apply h i <;> omega))

theorem sumRangeFromZ_one_reverse (n : ℕ) (f : ℕ → ℕ → ℤ) :
    sumRangeFromZ 1 (n + 1) (fun i => f i (n + 2 - i)) =
      sumRangeFromZ 1 (n + 1) (fun i => f (n + 2 - i) i) := by
  rw [sumRangeFromZ_eq_finset_sum]
  rw [sumRangeFromZ_eq_finset_sum]
  rw [← Finset.sum_range_reflect
    (fun x => f (1 + x) (n + 2 - (1 + x))) (n + 1)]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxlt : x < n + 1 := Finset.mem_range.mp hx
  simp
  congr 2 <;> omega

theorem sum_range_qPullback41_left (n : ℕ) (c f : ℕ → ℤ) :
    (∑ i ∈ Finset.range (n + 1),
        (if 41 ∣ i then c (i / 41) else 0) * f (n - i)) =
      ∑ m ∈ Finset.range (n / 41 + 1), c m * f (n - 41 * m) := by
  let T : Finset ℕ := (Finset.range (n + 1)).filter (fun i => 41 ∣ i)
  have hfilter :
      (∑ i ∈ Finset.range (n + 1),
          (if 41 ∣ i then c (i / 41) else 0) * f (n - i)) =
        ∑ i ∈ T, c (i / 41) * f (n - i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hdiv : 41 ∣ i
    · simp [hdiv]
    · simp [hdiv]
  rw [hfilter]
  symm
  refine Finset.sum_bij (fun m _ => 41 * m) ?_ ?_ ?_ ?_
  · intro m hm
    have hmle : m ≤ n / 41 := by
      have : m < n / 41 + 1 := Finset.mem_range.mp hm
      omega
    have hmul : 41 * m ≤ n := by
      have h1 : 41 * m ≤ 41 * (n / 41) := Nat.mul_le_mul_left 41 hmle
      have h2 : 41 * (n / 41) ≤ n := by
        simpa [Nat.mul_comm] using (Nat.div_mul_le_self n 41)
      omega
    simp [T, hmul, dvd_mul_right]
  · intro m₁ hm₁ m₂ hm₂ h
    exact Nat.mul_left_cancel (by norm_num : 0 < 41) h
  · intro i hi
    have hiS : i < n + 1 := by
      exact Finset.mem_range.mp (Finset.mem_of_mem_filter i hi)
    have hdiv : 41 ∣ i := by
      exact (Finset.mem_filter.mp hi).2
    refine ⟨i / 41, ?_, ?_⟩
    · have hle : i / 41 ≤ n / 41 := Nat.div_le_div_right (by omega)
      exact Finset.mem_range.mpr (by omega)
    · simpa [Nat.mul_comm] using Nat.div_mul_cancel hdiv
  · intro m hm
    have hmle : m ≤ n / 41 := by
      have : m < n / 41 + 1 := Finset.mem_range.mp hm
      omega
    have hmul : 41 * m ≤ n := by
      have h1 : 41 * m ≤ 41 * (n / 41) := Nat.mul_le_mul_left 41 hmle
      have h2 : 41 * (n / 41) ≤ n := by
        simpa [Nat.mul_comm] using (Nat.div_mul_le_self n 41)
      omega
    have hdiv : 41 ∣ 41 * m := dvd_mul_right 41 m
    simp [Nat.mul_div_right _ (by norm_num : 0 < 41)]

theorem foldl_range'_add_eq_add_sumRangeFromZ
    (start len : ℕ) (f : ℕ → ℤ) (init : ℤ) :
    List.foldl (fun s i => s + f i) init (List.range' start len 1) =
      init + sumRangeFromZ start len f := by
  induction len generalizing start init with
  | zero =>
      simp [sumRangeFromZ]
  | succ len ih =>
      simp [List.range'_succ, sumRangeFromZ, ih, add_assoc]

theorem forIn_range_add_eq_sumRangeFromZ (K : ℕ) (f : ℕ → ℤ) :
    (Id.run do
      let mut s : ℤ := 0
      for i in [0:K] do
        s := s + f i
      return s) = sumRangeFromZ 0 K f := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  induction K with
  | zero =>
      simp [sumRangeFromZ]
  | succ K ih =>
      simp only [Std.Legacy.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one,
        bind_pure_comp, map_pure, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
      rw [foldl_range'_add_eq_add_sumRangeFromZ]
      simp

theorem forIn_range'_add_if_eq_add_sumRangeFromZ
    (start len : ℕ) (p : ℕ → Prop) [DecidablePred p] (g : ℕ → ℤ) (init : ℤ) :
    (Id.run do
      let mut s : ℤ := init
      for i in List.range' start len do
        if p i then
          s := s + g i
      return s) =
      init + sumRangeFromZ start len (fun i => if p i then g i else 0) := by
  induction len generalizing start init with
  | zero =>
      simp [sumRangeFromZ]
  | succ len ih =>
      by_cases hp : p start
      · simp [List.range'_succ, sumRangeFromZ, hp]
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, add_assoc] using
          ih (start + 1) (init + g start)
      · simp [List.range'_succ, sumRangeFromZ, hp]
        simpa using ih (start + 1) init

/-- Coefficientwise agreement between a proof-facing list truncation and a
VM-facing array truncation. -/
def ListArrayEq (N : ℕ) (xs : List ℤ) (ys : Array ℤ) : Prop :=
  ∀ n, n < N → truncCoeffAt xs n = truncCoeffArrayAt ys n

theorem ListArrayEq.ofFn (N : ℕ) (f : ℕ → ℤ) :
    ListArrayEq N (truncCoeffList N f) (truncCoeffArrayOfFn N f) := by
  intro n hn
  rw [truncCoeffAt_truncCoeffList_of_lt hn]
  unfold truncCoeffArrayAt truncCoeffArrayOfFn
  simp [hn]

theorem truncCoeffArrayAt_ofFn_of_lt {N n : ℕ} {f : ℕ → ℤ}
    (hn : n < N) :
    truncCoeffArrayAt (truncCoeffArrayOfFn N f) n = f n := by
  simpa [truncCoeffAt_truncCoeffList_of_lt hn] using
    (ListArrayEq.ofFn N f n hn).symm

def zeroTruncCoeffArray (N : ℕ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun _ => 0)

def constTruncCoeffArray (N : ℕ) (c : ℤ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun n => if n = 0 then c else 0)

def addTruncCoeffArray (N : ℕ) (a b : Array ℤ) : Array ℤ :=
  truncCoeffArrayOfFn N
    (fun n => truncCoeffArrayAt a n + truncCoeffArrayAt b n)

def scaleTruncCoeffArray (N : ℕ) (c : ℤ) (a : Array ℤ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun n => c * truncCoeffArrayAt a n)

def subTruncCoeffArray (N : ℕ) (a b : Array ℤ) : Array ℤ :=
  addTruncCoeffArray N a (scaleTruncCoeffArray N (-1) b)

theorem ListArrayEq.zero (N : ℕ) :
    ListArrayEq N (zeroTruncCoeffList N) (zeroTruncCoeffArray N) := by
  simpa [zeroTruncCoeffList, zeroTruncCoeffArray] using
    ListArrayEq.ofFn N (fun _ => (0 : ℤ))

theorem ListArrayEq.const (N : ℕ) (c : ℤ) :
    ListArrayEq N (constTruncCoeffList N c) (constTruncCoeffArray N c) := by
  simpa [constTruncCoeffList, constTruncCoeffArray] using
    ListArrayEq.ofFn N (fun n => if n = 0 then c else 0)

def mulTruncCoeffArray (N : ℕ) (a b : Array ℤ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun n => Id.run do
    let mut s : ℤ := 0
    for i in [0:n + 1] do
      s := s + truncCoeffArrayAt a i * truncCoeffArrayAt b (n - i)
    return s)

def powTruncCoeffArray (N : ℕ) (a : Array ℤ) : ℕ → Array ℤ
  | 0 => constTruncCoeffArray N 1
  | k + 1 => mulTruncCoeffArray N (powTruncCoeffArray N a k) a

def powTruncCoeffArrayTableAux (N : ℕ) (base : Array ℤ) :
    Array ℤ → ℕ → List (Array ℤ)
  | current, 0 => [current]
  | current, k + 1 =>
      current :: powTruncCoeffArrayTableAux N base
        (mulTruncCoeffArray N current base) k

def powTruncCoeffArrayTable (N : ℕ) (base : Array ℤ) (maxPow : ℕ) :
    Array (Array ℤ) :=
  (powTruncCoeffArrayTableAux N base (constTruncCoeffArray N 1) maxPow).toArray

def qPullback41TruncCoeffArray (N : ℕ) (a : Array ℤ) : Array ℤ :=
  truncCoeffArrayOfFn N
    (fun n => if 41 ∣ n then truncCoeffArrayAt a (n / 41) else 0)

def XPowTruncCoeffArray (N m : ℕ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun n => if n = m then 1 else 0)

def E4TruncCoeffArray (N : ℕ) : Array ℤ :=
  truncCoeffArrayOfFn N E4CoeffZ

def mulDeltaEulerFactorTruncCoeffArray
    (N : ℕ) (a : Array ℤ) (m : ℕ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun n => Id.run do
    let mut s : ℤ := 0
    for j in [0:25] do
      s := s +
        if j * m ≤ n then
          ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
            truncCoeffArrayAt a (n - j * m)
        else 0
    return s)

def deltaEulerTruncCoeffArrayAux (N : ℕ) : ℕ → Array ℤ
  | 0 => truncCoeffArrayOfFn N (fun n => if n = 1 then 1 else 0)
  | k + 1 =>
      mulDeltaEulerFactorTruncCoeffArray N
        (deltaEulerTruncCoeffArrayAux N k) (k + 1)

def deltaEulerTruncCoeffArray (N : ℕ) : Array ℤ :=
  deltaEulerTruncCoeffArrayAux N N

def sigmaOneNat (n : ℕ) : ℤ := Id.run do
  let mut s : ℤ := 0
  for d in [1:n + 1] do
    if d ∣ n then
      s := s + (d : ℤ)
  return s

theorem sigmaOneNat_eq_sumRangeFromZ (n : ℕ) :
    sigmaOneNat n =
      sumRangeFromZ 1 n (fun d => if d ∣ n then (d : ℤ) else 0) := by
  unfold sigmaOneNat
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [Std.Legacy.Range.size_step_1]
  rw [Nat.succ_sub_one]
  change (Id.run do
      let mut s : ℤ := 0
      for d in List.range' 1 n do
        if d ∣ n then
          s := s + (d : ℤ)
      return s) =
    sumRangeFromZ 1 n (fun d => if d ∣ n then (d : ℤ) else 0)
  simpa using
    forIn_range'_add_if_eq_add_sumRangeFromZ 1 n
      (fun d => d ∣ n) (fun d => (d : ℤ)) 0

theorem sigmaOneNat_eq_finset_range_sum (n : ℕ) :
    sigmaOneNat n =
      ∑ i ∈ Finset.range n, if (1 + i) ∣ n then ((1 + i : ℕ) : ℤ) else 0 := by
  rw [sigmaOneNat_eq_sumRangeFromZ]
  rw [sumRangeFromZ_eq_finset_sum]

theorem sigmaOneNat_eq_arithmeticFunction_sigma_one (n : ℕ) :
    sigmaOneNat n = (ArithmeticFunction.sigma 1 n : ℤ) := by
  rw [sigmaOneNat_eq_finset_range_sum]
  rw [ArithmeticFunction.sigma_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · have hshift :
        (∑ i ∈ Finset.range n, if (1 + i) ∣ n then ((1 + i : ℕ) : ℤ) else 0) =
          ∑ d ∈ Finset.range (n + 1), if d ∣ n then (d : ℤ) else 0 := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, zero_dvd_iff, CharP.cast_eq_zero, ite_self,
        add_zero]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases h : x + 1 ∣ n
      · simp [Nat.add_comm, h]
        ring
      · simp [Nat.add_comm, h]
    rw [hshift]
    rw [← Finset.sum_filter]
    rw [Nat.filter_dvd_eq_divisors hn]
    simp

theorem sumRangeFromZ_ramanujan_reverse (n : ℕ) (a : ℕ → ℤ) :
    sumRangeFromZ 1 (n + 1) (fun i => a i * sigmaOneNat (n + 2 - i)) =
      ∑ j ∈ Finset.range (n + 1), a (n + 1 - j) * sigmaOneNat (j + 1) := by
  rw [sumRangeFromZ_one_reverse n (fun i j => a i * sigmaOneNat j)]
  rw [sumRangeFromZ_eq_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjlt : j < n + 1 := Finset.mem_range.mp hj
  congr 2 <;> omega

theorem sumRangeFromZ_sigma_reverse (n : ℕ) (a : ℕ → ℤ) :
    sumRangeFromZ 1 (n + 1)
        (fun i => a i * ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ)) =
      ∑ j ∈ Finset.range (n + 1),
        a (n + 1 - j) * ((ArithmeticFunction.sigma 1 (j + 1) : ℕ) : ℤ) := by
  rw [sumRangeFromZ_one_reverse n
    (fun i j => a i * ((ArithmeticFunction.sigma 1 j : ℕ) : ℤ))]
  rw [sumRangeFromZ_eq_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjlt : j < n + 1 := Finset.mem_range.mp hj
  simp [Nat.add_comm]

/-- Proof-facing Ramanujan recurrence for the coefficients of
`Delta = q * prod_m (1 - q^m)^24`.

This mirrors `deltaRamanujanTruncCoeffArray`, but uses a structurally
recursive `Fin`-indexed sum so Lean can see that every recursive coefficient
index is smaller than the coefficient being defined. -/
def deltaRamanujanCoeffSpec : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      ((-24 : ℤ) * (∑ j : Fin (n + 1),
        deltaRamanujanCoeffSpec (j.1 + 1) *
          sigmaOneNat (n + 2 - (j.1 + 1)))) /
        ((n + 1 : ℕ) : ℤ)
termination_by m => m
decreasing_by omega

theorem deltaRamanujanCoeffSpec_zero :
    deltaRamanujanCoeffSpec 0 = 0 := by
  rw [deltaRamanujanCoeffSpec]

theorem deltaRamanujanCoeffSpec_one :
    deltaRamanujanCoeffSpec 1 = 1 := by
  rw [deltaRamanujanCoeffSpec]

theorem deltaRamanujanCoeffSpec_succ_succ (n : ℕ) :
    deltaRamanujanCoeffSpec (n + 2) =
      ((-24 : ℤ) * (∑ j : Fin (n + 1),
        deltaRamanujanCoeffSpec (j.1 + 1) *
          sigmaOneNat (n + 2 - (j.1 + 1)))) /
        ((n + 1 : ℕ) : ℤ) := by
  rw [deltaRamanujanCoeffSpec]

theorem deltaRamanujanCoeffSpec_succ_succ_sumRange (n : ℕ) :
    deltaRamanujanCoeffSpec (n + 2) =
      ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
        (fun i => deltaRamanujanCoeffSpec i * sigmaOneNat (n + 2 - i))) /
        ((n + 1 : ℕ) : ℤ) := by
  rw [deltaRamanujanCoeffSpec_succ_succ]
  rw [sumRangeFromZ_eq_finset_sum]
  congr 2
  have h := Fin.sum_univ_eq_sum_range
    (f := fun k =>
      deltaRamanujanCoeffSpec (k + 1) * sigmaOneNat (n + 2 - (k + 1)))
    (n := n + 1)
  simpa [Nat.add_comm] using h

theorem deltaRamanujanCoeffSpec_succ_succ_sigma (n : ℕ) :
    deltaRamanujanCoeffSpec (n + 2) =
      ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
        (fun i =>
          deltaRamanujanCoeffSpec i *
            ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ))) /
        ((n + 1 : ℕ) : ℤ) := by
  rw [deltaRamanujanCoeffSpec_succ_succ_sumRange]
  congr 2
  apply sumRangeFromZ_congr
  intro i _hi1 _hi2
  rw [sigmaOneNat_eq_arithmeticFunction_sigma_one]

theorem eq_deltaRamanujanCoeffSpec_of_initial_recurrence
    (a : ℕ → ℤ)
    (h0 : a 0 = 0)
    (h1 : a 1 = 1)
    (hrec : ∀ n : ℕ,
      a (n + 2) =
        ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
          (fun i => a i * sigmaOneNat (n + 2 - i))) /
          ((n + 1 : ℕ) : ℤ)) :
    ∀ n : ℕ, a n = deltaRamanujanCoeffSpec n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [h0, deltaRamanujanCoeffSpec_zero]
      | succ n =>
          cases n with
          | zero =>
              rw [h1, deltaRamanujanCoeffSpec_one]
          | succ n =>
              rw [hrec n, deltaRamanujanCoeffSpec_succ_succ_sumRange]
              congr 2
              apply sumRangeFromZ_congr
              intro i _hi1 hi2
              rw [ih i]
              omega

theorem eq_deltaRamanujanCoeffSpec_of_initial_recurrence_sigma
    (a : ℕ → ℤ)
    (h0 : a 0 = 0)
    (h1 : a 1 = 1)
    (hrec : ∀ n : ℕ,
      a (n + 2) =
        ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
          (fun i =>
            a i * ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ))) /
          ((n + 1 : ℕ) : ℤ)) :
    ∀ n : ℕ, a n = deltaRamanujanCoeffSpec n := by
  apply eq_deltaRamanujanCoeffSpec_of_initial_recurrence a h0 h1
  intro n
  rw [hrec]
  congr 2
  apply sumRangeFromZ_congr
  intro i _hi1 _hi2
  rw [sigmaOneNat_eq_arithmeticFunction_sigma_one]

def deltaRamanujanTruncCoeffList (N : ℕ) : List ℤ :=
  truncCoeffList N deltaRamanujanCoeffSpec

theorem ListArrayEq.deltaRamanujanCoeffSpecTrunc (N : ℕ) :
    ListArrayEq N (deltaRamanujanTruncCoeffList N)
      (truncCoeffArrayOfFn N deltaRamanujanCoeffSpec) := by
  unfold deltaRamanujanTruncCoeffList
  exact ListArrayEq.ofFn N deltaRamanujanCoeffSpec

theorem truncCoeffAt_deltaRamanujanTruncCoeffList_of_lt {N n : ℕ}
    (hn : n < N) :
    truncCoeffAt (deltaRamanujanTruncCoeffList N) n =
      deltaRamanujanCoeffSpec n := by
  unfold deltaRamanujanTruncCoeffList
  exact truncCoeffAt_truncCoeffList_of_lt hn

theorem truncCoeffAt_deltaRamanujanTruncCoeffList_zero {N : ℕ} (hN : 0 < N) :
    truncCoeffAt (deltaRamanujanTruncCoeffList N) 0 = 0 := by
  rw [truncCoeffAt_deltaRamanujanTruncCoeffList_of_lt hN]
  exact deltaRamanujanCoeffSpec_zero

theorem truncCoeffAt_deltaRamanujanTruncCoeffList_one {N : ℕ} (hN : 1 < N) :
    truncCoeffAt (deltaRamanujanTruncCoeffList N) 1 = 1 := by
  rw [truncCoeffAt_deltaRamanujanTruncCoeffList_of_lt hN]
  exact deltaRamanujanCoeffSpec_one

theorem truncCoeffAt_deltaRamanujanTruncCoeffList_succ_succ {N n : ℕ}
    (hn : n + 2 < N) :
    truncCoeffAt (deltaRamanujanTruncCoeffList N) (n + 2) =
      ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
        (fun i =>
          truncCoeffAt (deltaRamanujanTruncCoeffList N) i *
            sigmaOneNat (n + 2 - i))) /
        ((n + 1 : ℕ) : ℤ) := by
  rw [truncCoeffAt_deltaRamanujanTruncCoeffList_of_lt hn]
  rw [deltaRamanujanCoeffSpec_succ_succ_sumRange]
  congr 2
  apply sumRangeFromZ_congr
  intro i hi1 hi2
  rw [truncCoeffAt_deltaRamanujanTruncCoeffList_of_lt]
  omega

def sigmaOneArray (N : ℕ) : Array ℤ :=
  truncCoeffArrayOfFn N sigmaOneNat

theorem truncCoeffArrayAt_sigmaOneArray {N n : ℕ} (hn : n < N) :
    truncCoeffArrayAt (sigmaOneArray N) n = sigmaOneNat n := by
  simpa [sigmaOneArray, truncCoeffAt_truncCoeffList_of_lt hn] using
    (ListArrayEq.ofFn N sigmaOneNat n hn).symm

/-- VM-oriented recurrence for the coefficients of
`Delta = q * prod_m (1 - q^m)^24`.

From `q Delta' / Delta = 1 - 24 * sum_{n >= 1} sigma_1(n) q^n`, the
coefficient `tau(n)` for `n >= 2` satisfies
`(n - 1) tau(n) = -24 * sum_{i=1}^{n-1} tau(i) sigma_1(n-i)`. -/
def deltaRamanujanTruncCoeffArrayAux (N : ℕ) : ℕ → Array ℤ
  | 0 => #[]
  | k + 1 =>
      let sigma := sigmaOneArray N
      let out := deltaRamanujanTruncCoeffArrayAux N k
      out.push
        (if k = 0 then 0
         else if k = 1 then 1
         else
          (((-24 : ℤ) * sumRangeFromZ 1 (k - 1)
            (fun i => truncCoeffArrayAt out i * truncCoeffArrayAt sigma (k - i))) /
            ((k - 1 : ℕ) : ℤ)))

def deltaRamanujanTruncCoeffArray (N : ℕ) : Array ℤ :=
  deltaRamanujanTruncCoeffArrayAux N N

theorem deltaRamanujanTruncCoeffArrayAux_size (N k : ℕ) :
    (deltaRamanujanTruncCoeffArrayAux N k).size = k := by
  induction k with
  | zero => simp [deltaRamanujanTruncCoeffArrayAux]
  | succ k ih => simp [deltaRamanujanTruncCoeffArrayAux, ih]

theorem truncCoeffArrayAt_deltaRamanujanTruncCoeffArrayAux_of_lt
    {N k n : ℕ} (hkN : k ≤ N) (hn : n < k) :
    truncCoeffArrayAt (deltaRamanujanTruncCoeffArrayAux N k) n =
      deltaRamanujanCoeffSpec n := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      by_cases hnk : n < k
      · rw [deltaRamanujanTruncCoeffArrayAux]
        rw [truncCoeffArrayAt_push_of_lt]
        · exact ih (by omega) hnk
        · rw [deltaRamanujanTruncCoeffArrayAux_size]
          exact hnk
      · have hn_eq : n = k := by omega
        subst n
        rw [deltaRamanujanTruncCoeffArrayAux]
        rw [truncCoeffArrayAt_push_eq_of_size]
        · by_cases hk0 : k = 0
          · subst hk0
            simp [deltaRamanujanCoeffSpec_zero]
          · by_cases hk1 : k = 1
            · subst hk1
              simp [deltaRamanujanCoeffSpec_one]
            · obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := by
                refine ⟨k - 2, ?_⟩
                omega
              subst hm
              have hm21 : ¬m + 2 = 1 := by omega
              simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
                Nat.reduceEqDiff, Int.reduceNeg, Nat.add_one_sub_one, neg_mul,
                Nat.cast_add, Nat.cast_one]
              rw [deltaRamanujanCoeffSpec_succ_succ_sumRange]
              have hsum :
                  sumRangeFromZ 1 (m + 1)
                      (fun i => truncCoeffArrayAt
                        (deltaRamanujanTruncCoeffArrayAux N (m + 2)) i *
                        truncCoeffArrayAt (sigmaOneArray N) (m + 2 - i)) =
                    sumRangeFromZ 1 (m + 1)
                      (fun i => deltaRamanujanCoeffSpec i * sigmaOneNat (m + 2 - i)) := by
                apply sumRangeFromZ_congr
                intro i _hi1 hi2
                have hik : i < m + 2 := by omega
                have hsig : m + 2 - i < N := by omega
                rw [ih (by omega) hik]
                rw [truncCoeffArrayAt_sigmaOneArray hsig]
              rw [hsum]
              simp
        · rw [deltaRamanujanTruncCoeffArrayAux_size]

theorem truncCoeffArrayAt_deltaRamanujanTruncCoeffArray_of_lt {N n : ℕ}
    (hn : n < N) :
    truncCoeffArrayAt (deltaRamanujanTruncCoeffArray N) n =
      deltaRamanujanCoeffSpec n := by
  exact truncCoeffArrayAt_deltaRamanujanTruncCoeffArrayAux_of_lt
    (N := N) (k := N) (n := n) (by rfl) hn

theorem ListArrayEq.deltaRamanujanCoeffSpecArray (N : ℕ) :
    ListArrayEq N (deltaRamanujanTruncCoeffList N)
      (deltaRamanujanTruncCoeffArray N) := by
  intro n hn
  rw [truncCoeffAt_deltaRamanujanTruncCoeffList_of_lt hn]
  rw [truncCoeffArrayAt_deltaRamanujanTruncCoeffArray_of_lt hn]

def phi41TermProductArrayTable (N : ℕ)
    (A B : Array (Array ℤ)) : Array (Array ℤ) :=
  ((List.range 43).map
    (fun x => mulTruncCoeffArray N
      (A.getD x (zeroTruncCoeffArray N))
      (B.getD (42 - x) (zeroTruncCoeffArray N)))).toArray

def evalSparseFromProductArrayTablesTrunc (N : ℕ)
    (P Q : Array (Array ℤ)) : List SparseBivarTerm → Array ℤ
  | [] => zeroTruncCoeffArray N
  | t :: ts =>
      addTruncCoeffArray N
        (scaleTruncCoeffArray N t.coeff
          (mulTruncCoeffArray N
            (P.getD t.xPow (zeroTruncCoeffArray N))
            (Q.getD t.yPow (zeroTruncCoeffArray N))))
        (evalSparseFromProductArrayTablesTrunc N P Q ts)

def linearCombinationForXPowArray (N x : ℕ)
    (Q : Array (Array ℤ)) (terms : List SparseBivarTerm) : Array ℤ :=
  terms.foldl
    (fun acc t =>
      if t.xPow = x then
        addTruncCoeffArray N acc
          (scaleTruncCoeffArray N t.coeff
            (Q.getD t.yPow (zeroTruncCoeffArray N)))
      else acc)
    (zeroTruncCoeffArray N)

def phi41SparseCoeffAt (x y : ℕ) : ℤ :=
  phi41SparseTerms.foldl
    (fun s t => if t.xPow = x ∧ t.yPow = y then s + t.coeff else s) 0

/-- Recursive sparse coefficient accumulator for a bivariate sparse-term list.
This form is proof-friendly; `phi41SparseCoeffAt` is the same accumulator
specialized to `phi41SparseTerms`. -/
def sparseCoeffAtTerms : List SparseBivarTerm → ℕ → ℕ → ℤ
  | [], _, _ => 0
  | t :: ts, x, y =>
      (if t.xPow = x ∧ t.yPow = y then t.coeff else 0) +
        sparseCoeffAtTerms ts x y

def sparseRowLinearCombinationTerms
    (terms : List SparseBivarTerm) (x : ℕ) (q : ℕ → ℤ) : ℤ :=
  match terms with
  | [] => 0
  | t :: ts =>
      (if t.xPow = x then t.coeff * q t.yPow else 0) +
        sparseRowLinearCombinationTerms ts x q

def sparseTermLinearCombinationTerms
    (terms : List SparseBivarTerm) (F : ℕ → ℕ → ℤ) : ℤ :=
  match terms with
  | [] => 0
  | t :: ts =>
      t.coeff * F t.xPow t.yPow +
        sparseTermLinearCombinationTerms ts F

theorem sparseCoeffAtTerms_eq_foldl_aux
    (terms : List SparseBivarTerm) (x y : ℕ) (s : ℤ) :
    terms.foldl
        (fun acc t => if t.xPow = x ∧ t.yPow = y then acc + t.coeff else acc) s =
      s + sparseCoeffAtTerms terms x y := by
  induction terms generalizing s with
  | nil =>
      simp [sparseCoeffAtTerms]
  | cons t ts ih =>
      by_cases h : t.xPow = x ∧ t.yPow = y
      · simp [sparseCoeffAtTerms, h, ih]
        ring
      · simp [sparseCoeffAtTerms, h, ih]

theorem phi41SparseCoeffAt_eq_sparseCoeffAtTerms (x y : ℕ) :
    phi41SparseCoeffAt x y = sparseCoeffAtTerms phi41SparseTerms x y := by
  simpa [phi41SparseCoeffAt] using
    sparseCoeffAtTerms_eq_foldl_aux phi41SparseTerms x y 0

theorem sumRangeFromZ_single_sparseCoeffTerm
    (t : SparseBivarTerm) (x : ℕ) (q : ℕ → ℤ)
    (hy : t.yPow < 43) :
    sumRangeFromZ 0 43
        (fun y => (if t.xPow = x ∧ t.yPow = y then t.coeff else 0) * q y) =
      if t.xPow = x then t.coeff * q t.yPow else 0 := by
  rw [sumRangeFromZ_zero_eq_finset_sum]
  by_cases hx : t.xPow = x
  · rw [if_pos hx]
    have hmem : t.yPow ∈ Finset.range 43 := Finset.mem_range.mpr hy
    rw [Finset.sum_eq_single_of_mem t.yPow hmem]
    · simp [hx]
    · intro y hyMem hyNe
      have hyNe' : ¬ t.yPow = y := by
        intro h
        exact hyNe h.symm
      simp [hyNe']
  · rw [if_neg hx]
    refine Finset.sum_eq_zero ?_
    intro y _hy
    simp [hx]

theorem sum_sparseCoeffAtTerms_eq_sparseRowLinearCombinationTerms
    (terms : List SparseBivarTerm) (x : ℕ) (q : ℕ → ℤ)
    (hdeg : ∀ t ∈ terms, t.yPow < 43) :
    sumRangeFromZ 0 43
        (fun y => sparseCoeffAtTerms terms x y * q y) =
      sparseRowLinearCombinationTerms terms x q := by
  induction terms with
  | nil =>
      simp [sparseCoeffAtTerms, sparseRowLinearCombinationTerms, sumRangeFromZ]
  | cons t ts ih =>
      have ht : t.yPow < 43 := hdeg t (by simp)
      have hts : ∀ u ∈ ts, u.yPow < 43 := by
        intro u hu
        exact hdeg u (by simp [hu])
      change
        sumRangeFromZ 0 43
            (fun y =>
              (((if t.xPow = x ∧ t.yPow = y then t.coeff else 0) +
                    sparseCoeffAtTerms ts x y) * q y)) =
          (if t.xPow = x then t.coeff * q t.yPow else 0) +
            sparseRowLinearCombinationTerms ts x q
      rw [sumRangeFromZ_zero_eq_finset_sum]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      rw [← sumRangeFromZ_zero_eq_finset_sum 43
          (fun y => (if t.xPow = x ∧ t.yPow = y then t.coeff else 0) * q y),
        sumRangeFromZ_single_sparseCoeffTerm t x q ht]
      rw [← sumRangeFromZ_zero_eq_finset_sum 43
          (fun y => sparseCoeffAtTerms ts x y * q y),
        ih hts]

def phi41SparseCoeffMatrixArray : Array (Array ℤ) :=
  ((List.range 43).map
    (fun x => ((List.range 43).map
      (fun y => phi41SparseCoeffAt x y)).toArray)).toArray

def linearCombinationFromCoeffMatrixArray (N x : ℕ)
    (Q coeffs : Array (Array ℤ)) : Array ℤ :=
  let zeroRow : Array ℤ := Array.replicate 43 0
  let row := coeffs.getD x zeroRow
  let zeroSeries := zeroTruncCoeffArray N
  truncCoeffArrayOfFn N (fun n => Id.run do
    let mut s : ℤ := 0
    for y in [0:43] do
      s := s + row.getD y 0 *
        truncCoeffArrayAt (Q.getD y zeroSeries) n
    return s)

def evalSparseGroupedProductArrayTablesTrunc (N : ℕ)
    (P Q : Array (Array ℤ)) (terms : List SparseBivarTerm) : Array ℤ := Id.run do
  let mut out := zeroTruncCoeffArray N
  for x in [0:43] do
    let qPart := linearCombinationForXPowArray N x Q terms
    out := addTruncCoeffArray N out
      (mulTruncCoeffArray N (P.getD x (zeroTruncCoeffArray N)) qPart)
  return out

def mulQPullback41CompressedTruncCoeffArray
    (N : ℕ) (compressed full : Array ℤ) : Array ℤ :=
  truncCoeffArrayOfFn N (fun n => Id.run do
    let mut s : ℤ := 0
    for m in [0:(n / 41) + 1] do
      s := s + compressed.getD m 0 * full.getD (n - 41 * m) 0
    return s)

def linearCombinationFromCoeffMatrixList (N x : ℕ)
    (Q : List (List ℤ)) (coeffs : Array (Array ℤ)) : List ℤ :=
  let zeroRow : Array ℤ := Array.replicate 43 0
  let row := coeffs.getD x zeroRow
  truncCoeffList N (fun n => sumRangeFromZ 0 43
    (fun y => row.getD y 0 *
      truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n))

def linearCombinationForXPowList (N x : ℕ)
    (Q : List (List ℤ)) (terms : List SparseBivarTerm) : List ℤ :=
  truncCoeffList N (fun n =>
    sparseRowLinearCombinationTerms terms x
      (fun y => truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n))

def mulQPullback41CompressedTruncCoeffList
    (N : ℕ) (compressed full : List ℤ) : List ℤ :=
  truncCoeffList N (fun n => sumRangeFromZ 0 ((n / 41) + 1)
    (fun m => truncCoeffAt compressed m * truncCoeffAt full (n - 41 * m)))

/-- Sparse-term evaluator using a compressed table for the `q ↦ q^41` side.
If `P[x]` represents the unpulled-back level-one product
`C^x D^(42-x)`, this evaluator multiplies `P[x](q^41)` by the full
level-one `Q[y]` table term-by-term. -/
def evalSparseCompressedFromProductTablesTrunc (N M : ℕ)
    (PCompressed Q : List (List ℤ)) : List SparseBivarTerm → List ℤ
  | [] => zeroTruncCoeffList N
  | t :: ts =>
      addTruncCoeffList N
        (scaleTruncCoeffList N t.coeff
          (mulQPullback41CompressedTruncCoeffList N
            (PCompressed.getD t.xPow (zeroTruncCoeffList M))
            (Q.getD t.yPow (zeroTruncCoeffList N))))
        (evalSparseCompressedFromProductTablesTrunc N M PCompressed Q ts)

def evalSparseCompressedMatrixStep (N M : ℕ)
    (PCompressed Q : List (List ℤ)) (coeffs : Array (Array ℤ))
    (out : List ℤ) (x : ℕ) : List ℤ :=
  let qPart := linearCombinationFromCoeffMatrixList N x Q coeffs
  addTruncCoeffList N out
    (mulQPullback41CompressedTruncCoeffList N
      (PCompressed.getD x (zeroTruncCoeffList M)) qPart)

def evalSparseCompressedMatrixFromProductTablesTrunc (N M : ℕ)
    (PCompressed Q : List (List ℤ)) (coeffs : Array (Array ℤ)) : List ℤ :=
  (List.range 43).foldl
    (evalSparseCompressedMatrixStep N M PCompressed Q coeffs)
    (zeroTruncCoeffList N)

def phi41Level41CoeffListCompressedSparse (N : ℕ) : List ℤ :=
  let M := (N + 40) / 41
  let E := E4TruncCoeffList N
  let D := deltaEulerTruncCoeffList N
  let C := powTruncCoeffList N E 3
  let Esmall := E4TruncCoeffList M
  let Dsmall := deltaEulerTruncCoeffList M
  let Csmall := powTruncCoeffList M Esmall 3
  let CPow := powTruncCoeffTable N C 42
  let DPow := powTruncCoeffTable N D 42
  let CSmallPow := powTruncCoeffTable M Csmall 42
  let DSmallPow := powTruncCoeffTable M Dsmall 42
  let PCompressed := phi41TermProductTable M CSmallPow DSmallPow
  let Q := phi41TermProductTable N CPow DPow
  evalSparseCompressedFromProductTablesTrunc N M PCompressed Q phi41SparseTerms

def phi41LevelOneDenseRowsList (N : ℕ) : List (List ℤ) :=
  let E := E4TruncCoeffList N
  let D := deltaEulerTruncCoeffList N
  let C := powTruncCoeffList N E 3
  let CPow := powTruncCoeffTable N C 42
  let DPow := powTruncCoeffTable N D 42
  phi41TermProductTable N CPow DPow

def phi41Level41CoeffListCompressedMatrix (N : ℕ) : List ℤ :=
  let M := (N + 40) / 41
  let E := E4TruncCoeffList N
  let D := deltaEulerTruncCoeffList N
  let C := powTruncCoeffList N E 3
  let Esmall := E4TruncCoeffList M
  let Dsmall := deltaEulerTruncCoeffList M
  let Csmall := powTruncCoeffList M Esmall 3
  let CPow := powTruncCoeffTable N C 42
  let DPow := powTruncCoeffTable N D 42
  let CSmallPow := powTruncCoeffTable M Csmall 42
  let DSmallPow := powTruncCoeffTable M Dsmall 42
  let PCompressed := phi41TermProductTable M CSmallPow DSmallPow
  let Q := phi41TermProductTable N CPow DPow
  let coeffs := phi41SparseCoeffMatrixArray
  evalSparseCompressedMatrixFromProductTablesTrunc N M PCompressed Q coeffs

def phi41Level41CoeffArrayCompressedPullbackOfDelta
    (N : ℕ) (D Dsmall : Array ℤ) : Array ℤ :=
  let M := (N + 40) / 41
  let E := E4TruncCoeffArray N
  let C := powTruncCoeffArray N E 3
  let Esmall := E4TruncCoeffArray M
  let Csmall := powTruncCoeffArray M Esmall 3
  let CPow := powTruncCoeffArrayTable N C 42
  let DPow := powTruncCoeffArrayTable N D 42
  let CSmallPow := powTruncCoeffArrayTable M Csmall 42
  let DSmallPow := powTruncCoeffArrayTable M Dsmall 42
  let PCompressed := phi41TermProductArrayTable M CSmallPow DSmallPow
  let Q := phi41TermProductArrayTable N CPow DPow
  let coeffs := phi41SparseCoeffMatrixArray
  (List.range 43).foldl
    (fun out x =>
      let qPart := linearCombinationFromCoeffMatrixArray N x Q coeffs
      addTruncCoeffArray N out
        (mulQPullback41CompressedTruncCoeffArray N
          (PCompressed.getD x (zeroTruncCoeffArray M)) qPart))
    (zeroTruncCoeffArray N)

def phi41Level41EulerCoeffArrayCompressedPullback (N : ℕ) : Array ℤ :=
  phi41Level41CoeffArrayCompressedPullbackOfDelta N
    (deltaEulerTruncCoeffArray N)
    (deltaEulerTruncCoeffArray ((N + 40) / 41))

def phi41Level41FastCoeffArrayCompressedPullback (N : ℕ) : Array ℤ :=
  phi41Level41CoeffArrayCompressedPullbackOfDelta N
    (deltaRamanujanTruncCoeffArray N)
    (deltaRamanujanTruncCoeffArray ((N + 40) / 41))

def phi41Level41FastCoeffArray (N : ℕ) : Array ℤ :=
  phi41Level41FastCoeffArrayCompressedPullback N

def truncCoeffArrayFirstZero (K : ℕ) (xs : Array ℤ) : Bool :=
  (List.range K).all (fun n => truncCoeffArrayAt xs n == 0)

def intCoeffZeroMod (p : ℕ) (a : ℤ) : Bool :=
  a % (p : ℤ) == 0

def intCoeffModEq (p : ℕ) (a b : ℤ) : Bool :=
  intCoeffZeroMod p (a - b)

def truncCoeffArrayFirstZeroMod (K p : ℕ) (xs : Array ℤ) : Bool :=
  (List.range K).all (fun n => intCoeffZeroMod p (truncCoeffArrayAt xs n))

def truncCoeffArrayFirstZeroModChunk
    (K p start len : ℕ) (xs : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      intCoeffZeroMod p (truncCoeffArrayAt xs n)
    else
      true)

def truncCoeffArrayFirstZeroModChunked
    (K p chunkSize numChunks : ℕ) (xs : Array ℤ) : Bool :=
  (List.range numChunks).all (fun c =>
    truncCoeffArrayFirstZeroModChunk K p (c * chunkSize) chunkSize xs)

theorem truncCoeffArrayFirstZeroMod_of_chunked
    {K p chunkSize numChunks : ℕ} {xs : Array ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (hchunked : truncCoeffArrayFirstZeroModChunked
      K p chunkSize numChunks xs = true) :
    truncCoeffArrayFirstZeroMod K p xs = true := by
  unfold truncCoeffArrayFirstZeroMod
  apply List.all_eq_true.mpr
  intro n hnmem
  have hn : n < K := List.mem_range.mp hnmem
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  unfold truncCoeffArrayFirstZeroModChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold truncCoeffArrayFirstZeroModChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  simpa [hn_eq, hn] using hentry

theorem truncCoeffArrayFirstZeroModChunked_of_chunks
    {K p chunkSize numChunks : ℕ} {xs : Array ℤ}
    (hchunks : ∀ c : ℕ, c < numChunks →
      truncCoeffArrayFirstZeroModChunk
        K p (c * chunkSize) chunkSize xs = true) :
    truncCoeffArrayFirstZeroModChunked
      K p chunkSize numChunks xs = true := by
  unfold truncCoeffArrayFirstZeroModChunked
  apply List.all_eq_true.mpr
  intro c hcmem
  exact hchunks c (List.mem_range.mp hcmem)

theorem truncCoeffArrayFirstZeroModChunk_of_entries
    {K p start len : ℕ} {xs : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         intCoeffZeroMod p (truncCoeffArrayAt xs n)
       else
         true) = true) :
    truncCoeffArrayFirstZeroModChunk K p start len xs = true := by
  unfold truncCoeffArrayFirstZeroModChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

def TruncCoeffArrayModEq (K p : ℕ) (xs ys : Array ℤ) : Prop :=
  ∀ n : ℕ, n < K →
    truncCoeffArrayAt xs n ≡ truncCoeffArrayAt ys n [ZMOD (p : ℤ)]

theorem TruncCoeffArrayModEq.of_fn
    {K p : ℕ} {xs : Array ℤ} {f : ℕ → ℤ}
    (h : ∀ n : ℕ, n < K →
      truncCoeffArrayAt xs n ≡ f n [ZMOD (p : ℤ)]) :
    TruncCoeffArrayModEq K p xs (truncCoeffArrayOfFn K f) := by
  intro n hn
  rw [truncCoeffArrayAt_ofFn_of_lt hn]
  exact h n hn

def truncCoeffArrayModEqFirst (K p : ℕ) (xs ys : Array ℤ) : Bool :=
  (List.range K).all (fun n =>
    intCoeffModEq p (truncCoeffArrayAt xs n) (truncCoeffArrayAt ys n))

theorem TruncCoeffArrayModEq.of_modEqFirst
    {K p : ℕ} {xs ys : Array ℤ}
    (h : truncCoeffArrayModEqFirst K p xs ys = true) :
    TruncCoeffArrayModEq K p xs ys := by
  intro n hn
  unfold truncCoeffArrayModEqFirst at h
  have hnmem : n ∈ List.range K := List.mem_range.mpr hn
  have hentry := List.all_eq_true.mp h n hnmem
  have hmod :
      (truncCoeffArrayAt xs n - truncCoeffArrayAt ys n) % (p : ℤ) = 0 := by
    simpa [intCoeffModEq, intCoeffZeroMod] using hentry
  have hz :
      truncCoeffArrayAt xs n - truncCoeffArrayAt ys n ≡ 0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)
  have hplus := hz.add (Int.ModEq.refl (truncCoeffArrayAt ys n))
  simpa [sub_eq_add_neg, add_assoc] using hplus

def truncCoeffArrayModEqFirstChunk
    (K p start len : ℕ) (xs ys : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      intCoeffModEq p (truncCoeffArrayAt xs n) (truncCoeffArrayAt ys n)
    else
      true)

theorem truncCoeffArrayModEqFirstChunk_of_entries
    {K p start len : ℕ} {xs ys : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         intCoeffModEq p (truncCoeffArrayAt xs n) (truncCoeffArrayAt ys n)
       else
         true) = true) :
    truncCoeffArrayModEqFirstChunk K p start len xs ys = true := by
  unfold truncCoeffArrayModEqFirstChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

def truncCoeffArrayModEqFirstChunked
    (K p chunkSize numChunks : ℕ) (xs ys : Array ℤ) : Bool :=
  (List.range numChunks).all (fun c =>
    truncCoeffArrayModEqFirstChunk K p (c * chunkSize) chunkSize xs ys)

def truncCoeffArrayEqLiteralChunk
    (K start len : ℕ) (xs chunk : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      truncCoeffArrayAt xs n == truncCoeffArrayAt chunk offset
    else
      true)

def truncCoeffFnEqLiteralChunk
    (K start len : ℕ) (f : ℕ → ℤ) (chunk : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      f n == truncCoeffArrayAt chunk offset
    else
      true)

def truncCoeffArrayModEqLiteralChunk
    (K p start len : ℕ) (chunk ys : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      intCoeffModEq p
        (truncCoeffArrayAt chunk offset)
        (truncCoeffArrayAt ys n)
    else
      true)

def truncCoeffChunkFn (chunkSize : ℕ) (chunk : ℕ → Array ℤ) (n : ℕ) : ℤ :=
  truncCoeffArrayAt (chunk (n / chunkSize)) (n % chunkSize)

def truncCoeffLiteralChunksModEqChunk
    (K p start len : ℕ) (exactChunk residueChunk : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      intCoeffModEq p
        (truncCoeffArrayAt exactChunk offset)
        (truncCoeffArrayAt residueChunk offset)
    else
      true)

theorem truncCoeffArrayEqLiteralChunk_of_entries
    {K start len : ℕ} {xs chunk : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         truncCoeffArrayAt xs n == truncCoeffArrayAt chunk offset
       else
         true) = true) :
    truncCoeffArrayEqLiteralChunk K start len xs chunk = true := by
  unfold truncCoeffArrayEqLiteralChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem truncCoeffFnEqLiteralChunk_of_entries
    {K start len : ℕ} {f : ℕ → ℤ} {chunk : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         f n == truncCoeffArrayAt chunk offset
       else
         true) = true) :
    truncCoeffFnEqLiteralChunk K start len f chunk = true := by
  unfold truncCoeffFnEqLiteralChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem truncCoeffArrayModEqLiteralChunk_of_entries
    {K p start len : ℕ} {chunk ys : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         intCoeffModEq p
          (truncCoeffArrayAt chunk offset)
          (truncCoeffArrayAt ys n)
       else
         true) = true) :
    truncCoeffArrayModEqLiteralChunk K p start len chunk ys = true := by
  unfold truncCoeffArrayModEqLiteralChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem truncCoeffLiteralChunksModEqChunk_of_entries
    {K p start len : ℕ} {exactChunk residueChunk : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         intCoeffModEq p
          (truncCoeffArrayAt exactChunk offset)
          (truncCoeffArrayAt residueChunk offset)
       else
         true) = true) :
    truncCoeffLiteralChunksModEqChunk
      K p start len exactChunk residueChunk = true := by
  unfold truncCoeffLiteralChunksModEqChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem TruncCoeffArrayModEq.of_literal_chunks
    {K p chunkSize numChunks : ℕ} {xs ys : Array ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (chunk : ℕ → Array ℤ)
    (hEq : ∀ c : ℕ, c < numChunks →
      truncCoeffArrayEqLiteralChunk
        K (c * chunkSize) chunkSize xs (chunk c) = true)
    (hMod : ∀ c : ℕ, c < numChunks →
      truncCoeffArrayModEqLiteralChunk
        K p (c * chunkSize) chunkSize (chunk c) ys = true) :
    TruncCoeffArrayModEq K p xs ys := by
  intro n hn
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hEqChunk := hEq c hc_lt
  unfold truncCoeffArrayEqLiteralChunk at hEqChunk
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hEqEntry := List.all_eq_true.mp hEqChunk offset hoffset_mem
  have hxeq :
      truncCoeffArrayAt xs n = truncCoeffArrayAt (chunk c) offset := by
    simpa [hn_eq, hn] using hEqEntry
  have hModChunk := hMod c hc_lt
  unfold truncCoeffArrayModEqLiteralChunk at hModChunk
  have hModEntry := List.all_eq_true.mp hModChunk offset hoffset_mem
  have hmod :
      (truncCoeffArrayAt (chunk c) offset - truncCoeffArrayAt ys n) %
        (p : ℤ) = 0 := by
    simpa [hn_eq, hn, intCoeffModEq, intCoeffZeroMod] using hModEntry
  rw [hxeq]
  have hz :
      truncCoeffArrayAt (chunk c) offset - truncCoeffArrayAt ys n ≡
        0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)
  have hplus := hz.add (Int.ModEq.refl (truncCoeffArrayAt ys n))
  simpa [sub_eq_add_neg, add_assoc] using hplus

theorem TruncCoeffArrayModEq.of_fn_literal_chunks
    {K p chunkSize numChunks : ℕ} {f : ℕ → ℤ} {ys : Array ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (chunk : ℕ → Array ℤ)
    (hEq : ∀ c : ℕ, c < numChunks →
      truncCoeffFnEqLiteralChunk
        K (c * chunkSize) chunkSize f (chunk c) = true)
    (hMod : ∀ c : ℕ, c < numChunks →
      truncCoeffArrayModEqLiteralChunk
        K p (c * chunkSize) chunkSize (chunk c) ys = true) :
    TruncCoeffArrayModEq K p (truncCoeffArrayOfFn K f) ys := by
  intro n hn
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hEqChunk := hEq c hc_lt
  unfold truncCoeffFnEqLiteralChunk at hEqChunk
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hEqEntry := List.all_eq_true.mp hEqChunk offset hoffset_mem
  have hxeq :
      f n = truncCoeffArrayAt (chunk c) offset := by
    simpa [hn_eq, hn] using hEqEntry
  have hModChunk := hMod c hc_lt
  unfold truncCoeffArrayModEqLiteralChunk at hModChunk
  have hModEntry := List.all_eq_true.mp hModChunk offset hoffset_mem
  have hmod :
      (truncCoeffArrayAt (chunk c) offset - truncCoeffArrayAt ys n) %
        (p : ℤ) = 0 := by
    simpa [hn_eq, hn, intCoeffModEq, intCoeffZeroMod] using hModEntry
  rw [truncCoeffArrayAt_ofFn_of_lt hn, hxeq]
  have hz :
      truncCoeffArrayAt (chunk c) offset - truncCoeffArrayAt ys n ≡
        0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)
  have hplus := hz.add (Int.ModEq.refl (truncCoeffArrayAt ys n))
  simpa [sub_eq_add_neg, add_assoc] using hplus

theorem TruncCoeffArrayModEq.of_fn_literal_chunk_functions
    {K p chunkSize numChunks : ℕ} {f : ℕ → ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (exactChunk residueChunk : ℕ → Array ℤ)
    (hEq : ∀ c : ℕ, c < numChunks →
      truncCoeffFnEqLiteralChunk
        K (c * chunkSize) chunkSize f (exactChunk c) = true)
    (hMod : ∀ c : ℕ, c < numChunks →
      truncCoeffLiteralChunksModEqChunk
        K p (c * chunkSize) chunkSize
        (exactChunk c) (residueChunk c) = true) :
    TruncCoeffArrayModEq K p
      (truncCoeffArrayOfFn K f)
      (truncCoeffArrayOfFn K (truncCoeffChunkFn chunkSize residueChunk)) := by
  intro n hn
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hEqChunk := hEq c hc_lt
  unfold truncCoeffFnEqLiteralChunk at hEqChunk
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hEqEntry := List.all_eq_true.mp hEqChunk offset hoffset_mem
  have hxeq :
      f n = truncCoeffArrayAt (exactChunk c) offset := by
    simpa [hn_eq, hn] using hEqEntry
  have hModChunk := hMod c hc_lt
  unfold truncCoeffLiteralChunksModEqChunk at hModChunk
  have hModEntry := List.all_eq_true.mp hModChunk offset hoffset_mem
  have hmod :
      (truncCoeffArrayAt (exactChunk c) offset -
          truncCoeffArrayAt (residueChunk c) offset) % (p : ℤ) = 0 := by
    simpa [hn_eq, hn, intCoeffModEq, intCoeffZeroMod] using hModEntry
  rw [truncCoeffArrayAt_ofFn_of_lt hn, truncCoeffArrayAt_ofFn_of_lt hn]
  dsimp [truncCoeffChunkFn]
  rw [hxeq]
  have hz :
      truncCoeffArrayAt (exactChunk c) offset -
          truncCoeffArrayAt (residueChunk c) offset ≡
        0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)
  have hplus := hz.add (Int.ModEq.refl (truncCoeffArrayAt (residueChunk c) offset))
  simpa [sub_eq_add_neg, add_assoc, c, offset] using hplus

def truncCoeffArrayE2E4DerivRelationChunk
    (K p start len : ℕ) (E4 E6 E2E4 : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      intCoeffModEq p
        (truncCoeffArrayAt E2E4 n)
        (truncCoeffArrayAt E6 n +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 n)
    else
      true)

def truncCoeffArrayE2E4DerivRelationChunked
    (K p chunkSize numChunks : ℕ) (E4 E6 E2E4 : Array ℤ) : Bool :=
  (List.range numChunks).all (fun c =>
    truncCoeffArrayE2E4DerivRelationChunk
      K p (c * chunkSize) chunkSize E4 E6 E2E4)

def truncCoeffE2E4DerivRelationFnChunk
    (K p start len : ℕ) (E4 E6 E2E4 : ℕ → ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      intCoeffModEq p
        (E2E4 n)
        (E6 n + (3 : ℤ) * (n : ℤ) * E4 n)
    else
      true)

def truncCoeffE2E4DerivRelationLiteralChunk
    (K p start len : ℕ) (E4 E6 E2E4 : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      intCoeffModEq p
        (truncCoeffArrayAt E2E4 offset)
        (truncCoeffArrayAt E6 offset +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 offset)
    else
      true)

def truncCoeffE2E4DerivRelationFnChunked
    (K p chunkSize numChunks : ℕ) (E4 E6 E2E4 : ℕ → ℤ) : Bool :=
  (List.range numChunks).all (fun c =>
    truncCoeffE2E4DerivRelationFnChunk
      K p (c * chunkSize) chunkSize E4 E6 E2E4)

theorem truncCoeffArrayE2E4DerivRelationChunk_of_entries
    {K p start len : ℕ} {E4 E6 E2E4 : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         intCoeffModEq p
          (truncCoeffArrayAt E2E4 n)
          (truncCoeffArrayAt E6 n +
            (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 n)
       else
         true) = true) :
    truncCoeffArrayE2E4DerivRelationChunk
      K p start len E4 E6 E2E4 = true := by
  unfold truncCoeffArrayE2E4DerivRelationChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem truncCoeffE2E4DerivRelationFnChunk_of_entries
    {K p start len : ℕ} {E4 E6 E2E4 : ℕ → ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         intCoeffModEq p
          (E2E4 n)
          (E6 n + (3 : ℤ) * (n : ℤ) * E4 n)
       else
         true) = true) :
    truncCoeffE2E4DerivRelationFnChunk
      K p start len E4 E6 E2E4 = true := by
  unfold truncCoeffE2E4DerivRelationFnChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem truncCoeffE2E4DerivRelationLiteralChunk_of_entries
    {K p start len : ℕ} {E4 E6 E2E4 : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         intCoeffModEq p
          (truncCoeffArrayAt E2E4 offset)
          (truncCoeffArrayAt E6 offset +
            (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 offset)
       else
         true) = true) :
    truncCoeffE2E4DerivRelationLiteralChunk
      K p start len E4 E6 E2E4 = true := by
  unfold truncCoeffE2E4DerivRelationLiteralChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem truncCoeffArrayE2E4DerivRelation_of_chunked
    {K p chunkSize numChunks : ℕ} {E4 E6 E2E4 : Array ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (hchunked : truncCoeffArrayE2E4DerivRelationChunked
      K p chunkSize numChunks E4 E6 E2E4 = true) :
    ∀ n : ℕ, n < K →
      truncCoeffArrayAt E2E4 n ≡
        truncCoeffArrayAt E6 n +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 n
        [ZMOD (p : ℤ)] := by
  intro n hn
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  unfold truncCoeffArrayE2E4DerivRelationChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold truncCoeffArrayE2E4DerivRelationChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hmod :
      (truncCoeffArrayAt E2E4 n -
        (truncCoeffArrayAt E6 n +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 n)) % (p : ℤ) = 0 := by
    simpa [hn_eq, hn, intCoeffModEq, intCoeffZeroMod] using hentry
  have hz :
      truncCoeffArrayAt E2E4 n -
        (truncCoeffArrayAt E6 n +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 n) ≡
        0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)
  have hplus := hz.add (Int.ModEq.refl
    (truncCoeffArrayAt E6 n +
      (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4 n))
  simpa [sub_eq_add_neg, add_assoc] using hplus

theorem truncCoeffE2E4DerivRelationFn_of_chunked
    {K p chunkSize numChunks : ℕ} {E4 E6 E2E4 : ℕ → ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (hchunked : truncCoeffE2E4DerivRelationFnChunked
      K p chunkSize numChunks E4 E6 E2E4 = true) :
    ∀ n : ℕ, n < K →
      E2E4 n ≡ E6 n + (3 : ℤ) * (n : ℤ) * E4 n [ZMOD (p : ℤ)] := by
  intro n hn
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  unfold truncCoeffE2E4DerivRelationFnChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold truncCoeffE2E4DerivRelationFnChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hmod :
      (E2E4 n - (E6 n + (3 : ℤ) * (n : ℤ) * E4 n)) %
        (p : ℤ) = 0 := by
    simpa [hn_eq, hn, intCoeffModEq, intCoeffZeroMod] using hentry
  have hz :
      E2E4 n - (E6 n + (3 : ℤ) * (n : ℤ) * E4 n) ≡
        0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)
  have hplus := hz.add (Int.ModEq.refl
    (E6 n + (3 : ℤ) * (n : ℤ) * E4 n))
  simpa [sub_eq_add_neg, add_assoc] using hplus

theorem truncCoeffE2E4DerivRelationFn_of_literal_chunks
    {K p chunkSize numChunks : ℕ}
    (hcover : K ≤ chunkSize * numChunks)
    (E4 E6 E2E4 : ℕ → Array ℤ)
    (hchunks : ∀ c : ℕ, c < numChunks →
      truncCoeffE2E4DerivRelationLiteralChunk
        K p (c * chunkSize) chunkSize (E4 c) (E6 c) (E2E4 c) = true) :
    ∀ n : ℕ, n < K →
      truncCoeffChunkFn chunkSize E2E4 n ≡
        truncCoeffChunkFn chunkSize E6 n +
          (3 : ℤ) * (n : ℤ) * truncCoeffChunkFn chunkSize E4 n
        [ZMOD (p : ℤ)] := by
  intro n hn
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hchunk := hchunks c hc_lt
  unfold truncCoeffE2E4DerivRelationLiteralChunk at hchunk
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hmod :
      (truncCoeffArrayAt (E2E4 c) offset -
        (truncCoeffArrayAt (E6 c) offset +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt (E4 c) offset)) %
        (p : ℤ) = 0 := by
    simpa [hn_eq, hn, intCoeffModEq, intCoeffZeroMod] using hentry
  have hz :
      truncCoeffArrayAt (E2E4 c) offset -
        (truncCoeffArrayAt (E6 c) offset +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt (E4 c) offset) ≡
        0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)
  have hplus := hz.add (Int.ModEq.refl
    (truncCoeffArrayAt (E6 c) offset +
      (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt (E4 c) offset))
  simpa [truncCoeffChunkFn, c, offset, sub_eq_add_neg, add_assoc] using hplus

theorem truncCoeffArrayModEqFirst_of_chunked
    {K p chunkSize numChunks : ℕ} {xs ys : Array ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (hchunked : truncCoeffArrayModEqFirstChunked
      K p chunkSize numChunks xs ys = true) :
    truncCoeffArrayModEqFirst K p xs ys = true := by
  unfold truncCoeffArrayModEqFirst
  apply List.all_eq_true.mpr
  intro n hnmem
  have hn : n < K := List.mem_range.mp hnmem
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  unfold truncCoeffArrayModEqFirstChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold truncCoeffArrayModEqFirstChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  simpa [hn_eq, hn] using hentry

theorem TruncCoeffArrayModEq.of_modEqFirstChunked
    {K p chunkSize numChunks : ℕ} {xs ys : Array ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (hchunked : truncCoeffArrayModEqFirstChunked
      K p chunkSize numChunks xs ys = true) :
    TruncCoeffArrayModEq K p xs ys :=
  TruncCoeffArrayModEq.of_modEqFirst
    (truncCoeffArrayModEqFirst_of_chunked hcover hchunked)

def truncCoeffArrayTableModEqFirstChunked
    (K maxIdx p chunkSize numChunks : ℕ)
    (xs ys : Array (Array ℤ)) : Bool :=
  (List.range (maxIdx + 1)).all (fun k =>
    truncCoeffArrayModEqFirstChunked K p chunkSize numChunks
      (xs.getD k (zeroTruncCoeffArray K))
      (ys.getD k (zeroTruncCoeffArray K)))

theorem TruncCoeffArrayModEq.refl (K p : ℕ) (xs : Array ℤ) :
    TruncCoeffArrayModEq K p xs xs := by
  intro n hn
  exact Int.ModEq.refl _

theorem TruncCoeffArrayModEq.symm {K p : ℕ} {xs ys : Array ℤ}
    (h : TruncCoeffArrayModEq K p xs ys) :
    TruncCoeffArrayModEq K p ys xs := by
  intro n hn
  exact (h n hn).symm

theorem TruncCoeffArrayModEq.trans {K p : ℕ} {xs ys zs : Array ℤ}
    (hxy : TruncCoeffArrayModEq K p xs ys)
    (hyz : TruncCoeffArrayModEq K p ys zs) :
    TruncCoeffArrayModEq K p xs zs := by
  intro n hn
  exact (hxy n hn).trans (hyz n hn)

theorem TruncCoeffArrayModEq.zero (K p : ℕ) :
    TruncCoeffArrayModEq K p (zeroTruncCoeffArray K) (zeroTruncCoeffArray K) :=
  TruncCoeffArrayModEq.refl K p _

theorem TruncCoeffArrayModEq.const (K p : ℕ) (c : ℤ) :
    TruncCoeffArrayModEq K p (constTruncCoeffArray K c) (constTruncCoeffArray K c) :=
  TruncCoeffArrayModEq.refl K p _

theorem TruncCoeffArrayModEq.add {K p : ℕ} {xs ys xs' ys' : Array ℤ}
    (hxs : TruncCoeffArrayModEq K p xs xs')
    (hys : TruncCoeffArrayModEq K p ys ys') :
    TruncCoeffArrayModEq K p
      (addTruncCoeffArray K xs ys) (addTruncCoeffArray K xs' ys') := by
  intro n hn
  rw [addTruncCoeffArray, addTruncCoeffArray]
  rw [truncCoeffArrayAt_ofFn_of_lt hn, truncCoeffArrayAt_ofFn_of_lt hn]
  exact (hxs n hn).add (hys n hn)

theorem TruncCoeffArrayModEq.scale {K p : ℕ} (c : ℤ) {xs xs' : Array ℤ}
    (hxs : TruncCoeffArrayModEq K p xs xs') :
    TruncCoeffArrayModEq K p
      (scaleTruncCoeffArray K c xs) (scaleTruncCoeffArray K c xs') := by
  intro n hn
  rw [scaleTruncCoeffArray, scaleTruncCoeffArray]
  rw [truncCoeffArrayAt_ofFn_of_lt hn, truncCoeffArrayAt_ofFn_of_lt hn]
  exact Int.ModEq.mul_left c (hxs n hn)

theorem TruncCoeffArrayModEq.sub {K p : ℕ} {xs ys xs' ys' : Array ℤ}
    (hxs : TruncCoeffArrayModEq K p xs xs')
    (hys : TruncCoeffArrayModEq K p ys ys') :
    TruncCoeffArrayModEq K p
      (subTruncCoeffArray K xs ys) (subTruncCoeffArray K xs' ys') := by
  exact hxs.add (hys.scale (-1))

theorem TruncCoeffArrayModEq.mul {K p : ℕ} {xs ys xs' ys' : Array ℤ}
    (hxs : TruncCoeffArrayModEq K p xs xs')
    (hys : TruncCoeffArrayModEq K p ys ys') :
    TruncCoeffArrayModEq K p
      (mulTruncCoeffArray K xs ys) (mulTruncCoeffArray K xs' ys') := by
  intro n hn
  rw [mulTruncCoeffArray, mulTruncCoeffArray]
  rw [truncCoeffArrayAt_ofFn_of_lt hn, truncCoeffArrayAt_ofFn_of_lt hn]
  rw [forIn_range_add_eq_sumRangeFromZ]
  rw [forIn_range_add_eq_sumRangeFromZ]
  apply sumRangeFromZ_modEq
  intro i hi1 hi2
  exact (hxs i (by omega)).mul (hys (n - i) (by omega))

theorem TruncCoeffArrayModEq.pow {K p e : ℕ} {xs ys : Array ℤ}
    (hxs : TruncCoeffArrayModEq K p xs ys) :
    TruncCoeffArrayModEq K p
      (powTruncCoeffArray K xs e) (powTruncCoeffArray K ys e) := by
  induction e with
  | zero =>
      exact TruncCoeffArrayModEq.const K p 1
  | succ e ih =>
      simpa [powTruncCoeffArray] using ih.mul hxs

theorem TruncCoeffArrayModEq.qPullback41 {K p : ℕ} {xs ys : Array ℤ}
    (hxs : TruncCoeffArrayModEq K p xs ys) :
    TruncCoeffArrayModEq K p
      (qPullback41TruncCoeffArray K xs) (qPullback41TruncCoeffArray K ys) := by
  intro n hn
  rw [qPullback41TruncCoeffArray, qPullback41TruncCoeffArray]
  rw [truncCoeffArrayAt_ofFn_of_lt hn, truncCoeffArrayAt_ofFn_of_lt hn]
  by_cases hdiv : 41 ∣ n
  · simp only [hdiv, ↓reduceIte]
    exact hxs (n / 41) (lt_of_le_of_lt (Nat.div_le_self n 41) hn)
  · simp [hdiv]

theorem int_modEq_zero_of_intCoeffZeroMod {p : ℕ} {a : ℤ}
    (h : intCoeffZeroMod p a = true) : a ≡ 0 [ZMOD (p : ℤ)] := by
  have hmod : a % (p : ℤ) = 0 := by
    simpa [intCoeffZeroMod] using h
  exact Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_emod_eq_zero hmod)

theorem int_modEq_of_intCoeffModEq {p : ℕ} {a b : ℤ}
    (h : intCoeffModEq p a b = true) : a ≡ b [ZMOD (p : ℤ)] := by
  have hz : a - b ≡ 0 [ZMOD (p : ℤ)] :=
    int_modEq_zero_of_intCoeffZeroMod h
  have hplus := hz.add (Int.ModEq.refl b)
  simpa [sub_eq_add_neg, add_assoc] using hplus

theorem truncCoeffArray_modEq_zero_of_firstZeroMod {K p : ℕ} {xs : Array ℤ}
    (h : truncCoeffArrayFirstZeroMod K p xs = true) :
    ∀ n : ℕ, n < K → truncCoeffArrayAt xs n ≡ 0 [ZMOD (p : ℤ)] := by
  intro n hn
  unfold truncCoeffArrayFirstZeroMod at h
  have hnmem : n ∈ List.range K := by
    simpa using List.mem_range.mpr hn
  have hzero := List.all_eq_true.mp h n hnmem
  exact int_modEq_zero_of_intCoeffZeroMod hzero

theorem truncCoeffArray_modEq_zero_of_modEq_firstZeroMod {K p : ℕ}
    {xs ys : Array ℤ}
    (hxy : TruncCoeffArrayModEq K p xs ys)
    (hy : truncCoeffArrayFirstZeroMod K p ys = true) :
    ∀ n : ℕ, n < K → truncCoeffArrayAt xs n ≡ 0 [ZMOD (p : ℤ)] := by
  intro n hn
  exact (hxy n hn).trans
    (truncCoeffArray_modEq_zero_of_firstZeroMod hy n hn)

theorem truncCoeffArrayFirstZero_of_crt_certificate {K : ℕ} {xs : Array ℤ}
    {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    (hbound : ∀ n : ℕ, n < K → |truncCoeffArrayAt xs n| < (ps.prod : ℤ))
    (hmods : ∀ n : ℕ, n < K → ∀ p ∈ ps,
      truncCoeffArrayAt xs n ≡ 0 [ZMOD (p : ℤ)]) :
    truncCoeffArrayFirstZero K xs = true := by
  unfold truncCoeffArrayFirstZero
  apply List.all_eq_true.mpr
  intro n hnmem
  have hn : n < K := List.mem_range.mp hnmem
  have hz :
      truncCoeffArrayAt xs n = 0 :=
    int_eq_zero_of_modEq_zero_list_of_abs_lt_prod
      hcop (hbound n hn) (hmods n hn)
  simp [hz]

theorem truncCoeffArrayFirstZero_of_crt_bounded_certificate {K : ℕ}
    {xs : Array ℤ} {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    {B : ℕ}
    (hbound : ∀ n : ℕ, n < K → |truncCoeffArrayAt xs n| ≤ (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (hmods : ∀ n : ℕ, n < K → ∀ p ∈ ps,
      truncCoeffArrayAt xs n ≡ 0 [ZMOD (p : ℤ)]) :
    truncCoeffArrayFirstZero K xs = true := by
  apply truncCoeffArrayFirstZero_of_crt_certificate hcop
  · intro n hn
    exact lt_of_le_of_lt (hbound n hn) hB
  · exact hmods

theorem truncCoeffArrayFirstZero_of_crt_bounded_mod_certificate {K : ℕ}
    {xs : Array ℤ} {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    {B : ℕ}
    (hbound : ∀ n : ℕ, n < K → |truncCoeffArrayAt xs n| ≤ (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (hmods : ∀ p ∈ ps, truncCoeffArrayFirstZeroMod K p xs = true) :
    truncCoeffArrayFirstZero K xs = true := by
  apply truncCoeffArrayFirstZero_of_crt_bounded_certificate hcop hbound hB
  intro n hn p hp
  exact truncCoeffArray_modEq_zero_of_firstZeroMod (hmods p hp) n hn

theorem truncCoeffArrayFirstZero_of_crt_bounded_modEq_certificate {K : ℕ}
    {xs : Array ℤ} {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    {B : ℕ}
    (hbound : ∀ n : ℕ, n < K → |truncCoeffArrayAt xs n| ≤ (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (ys : ℕ → Array ℤ)
    (hrel : ∀ p ∈ ps, TruncCoeffArrayModEq K p xs (ys p))
    (hzero : ∀ p ∈ ps, truncCoeffArrayFirstZeroMod K p (ys p) = true) :
    truncCoeffArrayFirstZero K xs = true := by
  apply truncCoeffArrayFirstZero_of_crt_bounded_certificate hcop hbound hB
  intro n hn p hp
  exact truncCoeffArray_modEq_zero_of_modEq_firstZeroMod (hrel p hp) (hzero p hp) n hn

theorem truncCoeffArrayFirstZero_of_crt_bounded_function_certificate {K : ℕ}
    {xs : Array ℤ} {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    {B : ℕ}
    (hbound : ∀ n : ℕ, n < K → |truncCoeffArrayAt xs n| ≤ (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (ys : ℕ → ℕ → ℤ)
    (hrel : ∀ p ∈ ps, ∀ n : ℕ, n < K →
      truncCoeffArrayAt xs n ≡ ys p n [ZMOD (p : ℤ)])
    (hzero : ∀ p ∈ ps, ∀ n : ℕ, n < K →
      ys p n ≡ 0 [ZMOD (p : ℤ)]) :
    truncCoeffArrayFirstZero K xs = true := by
  apply truncCoeffArrayFirstZero_of_crt_bounded_certificate hcop hbound hB
  intro n hn p hp
  exact (hrel p hp n hn).trans (hzero p hp n hn)

def truncCoeffArrayEqFirst (K : ℕ) (xs ys : Array ℤ) : Bool :=
  (List.range K).all (fun n => truncCoeffArrayAt xs n == truncCoeffArrayAt ys n)

def truncCoeffArrayEqFirstChunk
    (K start len : ℕ) (xs ys : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < K then
      truncCoeffArrayAt xs n == truncCoeffArrayAt ys n
    else
      true)

def truncCoeffArrayEqFirstChunked
    (K chunkSize numChunks : ℕ) (xs ys : Array ℤ) : Bool :=
  (List.range numChunks).all (fun c =>
    truncCoeffArrayEqFirstChunk K (c * chunkSize) chunkSize xs ys)

theorem truncCoeffArrayEqFirstChunk_of_entries
    {K start len : ℕ} {xs ys : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < K then
         truncCoeffArrayAt xs n == truncCoeffArrayAt ys n
       else
         true) = true) :
    truncCoeffArrayEqFirstChunk K start len xs ys = true := by
  unfold truncCoeffArrayEqFirstChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem truncCoeffArrayEqFirst_of_chunked
    {K chunkSize numChunks : ℕ} {xs ys : Array ℤ}
    (hcover : K ≤ chunkSize * numChunks)
    (hchunked : truncCoeffArrayEqFirstChunked
      K chunkSize numChunks xs ys = true) :
    truncCoeffArrayEqFirst K xs ys = true := by
  unfold truncCoeffArrayEqFirst
  apply List.all_eq_true.mpr
  intro n hnmem
  have hn : n < K := List.mem_range.mp hnmem
  let c := n / chunkSize
  have hchunkPos : 0 < chunkSize := by
    by_contra hzero
    have hcs : chunkSize = 0 := Nat.eq_zero_of_not_pos hzero
    have hK0 : K = 0 := Nat.eq_zero_of_le_zero (by simpa [hcs] using hcover)
    omega
  have hc_lt : c < numChunks := by
    dsimp [c]
    have hnprod : n < chunkSize * numChunks := lt_of_lt_of_le hn hcover
    exact Nat.div_lt_of_lt_mul hnprod
  unfold truncCoeffArrayEqFirstChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold truncCoeffArrayEqFirstChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  simpa [hn_eq, hn] using hentry

theorem truncCoeffArrayEqFirst_eq_true_of_ListArrayEq {K : ℕ}
    {xs : List ℤ} {A B : Array ℤ}
    (hA : ListArrayEq K xs A) (hB : ListArrayEq K xs B) :
    truncCoeffArrayEqFirst K A B = true := by
  unfold truncCoeffArrayEqFirst
  apply List.all_eq_true.mpr
  intro n hn
  have hnK : n < K := List.mem_range.mp hn
  rw [← hA n hnK, ← hB n hnK]
  simp

def truncCoeffArrayFirstZeroCached (K : ℕ) (mk : Unit → Array ℤ) : Bool :=
  let xs := mk ()
  truncCoeffArrayFirstZero K xs

def truncCoeffArrayEqFirstCached (K : ℕ) (mkx mky : Unit → Array ℤ) : Bool :=
  let xs := mkx ()
  let ys := mky ()
  truncCoeffArrayEqFirst K xs ys

theorem truncCoeffArrayAt_eq_zero_of_firstZero {K : ℕ} {xs : Array ℤ} {n : ℕ}
    (h : truncCoeffArrayFirstZero K xs = true) (hn : n < K) :
    truncCoeffArrayAt xs n = 0 := by
  unfold truncCoeffArrayFirstZero at h
  have hnmem : n ∈ List.range K := by
    simpa using List.mem_range.mpr hn
  have hall := List.all_eq_true.mp h n hnmem
  simpa using hall

theorem truncCoeffArrayAt_eq_of_eqFirst {K : ℕ} {xs ys : Array ℤ} {n : ℕ}
    (h : truncCoeffArrayEqFirst K xs ys = true) (hn : n < K) :
    truncCoeffArrayAt xs n = truncCoeffArrayAt ys n := by
  unfold truncCoeffArrayEqFirst at h
  have hnmem : n ∈ List.range K := by
    simpa using List.mem_range.mpr hn
  have hall := List.all_eq_true.mp h n hnmem
  simpa using hall

theorem TruncCoeffArrayModEq.of_eqFirst {K p : ℕ} {xs ys : Array ℤ}
    (h : truncCoeffArrayEqFirst K xs ys = true) :
    TruncCoeffArrayModEq K p xs ys := by
  intro n hn
  rw [truncCoeffArrayAt_eq_of_eqFirst h hn]

/-- A finite coefficient list represents a formal power series through degree
`N - 1`. -/
def TruncRep (N : ℕ) (p : PowerSeries ℤ) (xs : List ℤ) : Prop :=
  ∀ n : ℕ, n < N → PowerSeries.coeff (R := ℤ) n p = truncCoeffAt xs n

theorem coeff_succ_of_X_derivative_eq_mul (f g : PowerSeries ℤ)
    (h : PowerSeries.X * PowerSeries.derivative ℤ f = g * f) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) (n + 1) f * ((n + 1 : ℕ) : ℤ) =
      ∑ ij ∈ Finset.antidiagonal (n + 1),
        PowerSeries.coeff (R := ℤ) ij.1 g *
          PowerSeries.coeff (R := ℤ) ij.2 f := by
  rw [← PowerSeries.coeff_mul]
  rw [← h]
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
  simp

theorem deltaEulerCoeffZ_one : deltaEulerCoeffZ 1 = 1 := by
  simp [deltaEulerCoeffZ, deltaEulerProductTruncZ, deltaEulerFactorZ]

theorem coeff_deltaEulerSeriesZ_one :
    PowerSeries.coeff (R := ℤ) 1 deltaEulerSeriesZ = 1 := by
  rw [coeff_deltaEulerSeriesZ]
  exact deltaEulerCoeffZ_one

/-- Integer q-expansion coefficients of the Eisenstein series
`E₂ = 1 - 24 ∑_{n≥1} σ₁(n) q^n`, used only as a formal power series in the
Delta logarithmic-derivative bridge. -/
def E2CoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 1 else (-24 : ℤ) * ((ArithmeticFunction.sigma 1 n : ℕ) : ℤ)

def E2ZSeries : PowerSeries ℤ :=
  PowerSeries.mk E2CoeffZ

theorem coeff_E2ZSeries_zero : PowerSeries.coeff (R := ℤ) 0 E2ZSeries = 1 := by
  simp [E2ZSeries, E2CoeffZ]

theorem coeff_E2ZSeries_pos {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff (R := ℤ) n E2ZSeries =
      (-24 : ℤ) * ((ArithmeticFunction.sigma 1 n : ℕ) : ℤ) := by
  simp [E2ZSeries, E2CoeffZ, hn]

theorem coeff_E2ZSeries_succ (n : ℕ) :
    PowerSeries.coeff (R := ℤ) (n + 1) E2ZSeries =
      (-24 : ℤ) * ((ArithmeticFunction.sigma 1 (n + 1) : ℕ) : ℤ) := by
  rw [coeff_E2ZSeries_pos]
  omega

/-- Integer coefficients of the normalized `E₆` q-expansion. -/
def E6CoeffZ (n : ℕ) : ℤ :=
  if n = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 n : ℤ)

def E6ZSeries : PowerSeries ℤ :=
  PowerSeries.mk E6CoeffZ

theorem coeff_E6ZSeries (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n E6ZSeries = E6CoeffZ n := by
  simp [E6ZSeries]

private theorem E2ZSeries_complex_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (PowerSeries.map (Int.castRingHom ℂ) E2ZSeries) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (EisensteinSeries.E2 τ) := by
  convert E2_qExpansion_hasSum τ using 1
  ext n
  rw [PowerSeries.coeff_map]
  by_cases hn : n = 0
  · subst hn
    simp [E2ZSeries, E2CoeffZ]
  · rw [coeff_E2ZSeries_pos hn]
    simp [hn]

private theorem E4ZSeries_complex_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (PowerSeries.map (Int.castRingHom ℂ) E4ZSeries) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (E4 τ) := by
  simpa [map_E4ZSeries] using E4QExpansion_hasSum τ

private theorem E6ZSeries_complex_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (PowerSeries.map (Int.castRingHom ℂ) E6ZSeries) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (E6 τ) := by
  convert E6QExpansion_hasSum τ using 1
  ext n
  rw [PowerSeries.coeff_map, coeff_E6ZSeries, coeff_E6QExpansion]
  unfold E6CoeffZ
  by_cases hn : n = 0 <;> simp [hn]

private theorem E2E4ZSeries_complex_hasSum (τ : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
        (PowerSeries.map (Int.castRingHom ℂ) (E2ZSeries * E4ZSeries)) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ n)
      (EisensteinSeries.E2 τ * E4 τ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  let E2C : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) E2ZSeries
  let E4C : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) E4ZSeries
  have hE2 : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n E2C * q ^ n)
      (EisensteinSeries.E2 τ) := by
    simpa [E2C, q] using E2ZSeries_complex_hasSum τ
  have hE4 : HasSum (fun n : ℕ => PowerSeries.coeff (R := ℂ) n E4C * q ^ n)
      (E4 τ) := by
    simpa [E4C, q] using E4ZSeries_complex_hasSum τ
  have hprod := Ripple.Number.Modular.powerSeries_mul_hasSum_eval_of_summable_norm
    hE2 hE4 hE2.summable.norm hE4.summable.norm
  convert hprod using 1
  ext n
  dsimp [E2C, E4C, q]
  rw [← map_mul, PowerSeries.coeff_map]
  simp

def E6TruncCoeffList (N : ℕ) : List ℤ :=
  truncCoeffList N E6CoeffZ

def E2TruncCoeffList (N : ℕ) : List ℤ :=
  truncCoeffList N E2CoeffZ

def E2E4TruncCoeffList (N : ℕ) : List ℤ :=
  mulTruncCoeffList N (E2TruncCoeffList N) (E4TruncCoeffList N)

def E2TruncCoeffArray (N : ℕ) : Array ℤ :=
  truncCoeffArrayOfFn N E2CoeffZ

def E6TruncCoeffArray (N : ℕ) : Array ℤ :=
  truncCoeffArrayOfFn N E6CoeffZ

def E2E4TruncCoeffArray (N : ℕ) : Array ℤ :=
  mulTruncCoeffArray N (E2TruncCoeffArray N) (E4TruncCoeffArray N)

/-- The next coefficient in the recurrence for
`Q_j(q) = E₄(q)^(3j) * Δ(q)^(42-j)`. -/
def phi41QRecurrenceNextCoeff
    (j valuation k : ℕ) (E4 E6 E2E4 out : Array ℤ) : ℤ :=
  if k < valuation then 0
  else if k = valuation then 1
  else
    (sumRangeFromZ 1 k (fun a =>
      (((42 : ℤ) * truncCoeffArrayAt E2E4 a -
          (j : ℤ) * truncCoeffArrayAt E6 a) -
        truncCoeffArrayAt E4 a * ((k - a : ℕ) : ℤ)) *
          truncCoeffArrayAt out (k - a))) /
      (((k - valuation : ℕ) : ℤ))

/-- Recurrence row for `Q_j(q) = E₄(q)^(3j) * Δ(q)^(42-j)`.

The recurrence comes from the Ramanujan identities:
`E₄ * q dQ_j/dq = (42 E₂ E₄ - j E₆) * Q_j`.
The initial valuation is `42 - j`, with leading coefficient `1`. -/
def phi41QRecurrenceRowArrayAux
    (N j valuation : ℕ) (E4 E6 E2E4 : Array ℤ) : ℕ → Array ℤ
  | 0 => #[]
  | k + 1 =>
      let out := phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 k
      out.push (phi41QRecurrenceNextCoeff j valuation k E4 E6 E2E4 out)

def phi41QRecurrenceRowArray
    (N j : ℕ) (E4 E6 E2E4 : Array ℤ) : Array ℤ :=
  phi41QRecurrenceRowArrayAux N j (42 - j) E4 E6 E2E4 N

theorem phi41QRecurrenceRowArrayAux_size
    (N j valuation : ℕ) (E4 E6 E2E4 : Array ℤ) (k : ℕ) :
    (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 k).size = k := by
  induction k with
  | zero =>
      simp [phi41QRecurrenceRowArrayAux]
  | succ k ih =>
      simp [phi41QRecurrenceRowArrayAux, ih]

theorem phi41QRecurrenceRowArray_size
    (N j : ℕ) (E4 E6 E2E4 : Array ℤ) :
    (phi41QRecurrenceRowArray N j E4 E6 E2E4).size = N := by
  simp [phi41QRecurrenceRowArray, phi41QRecurrenceRowArrayAux_size]

theorem truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_succ_of_lt
    {N j valuation : ℕ} {E4 E6 E2E4 : Array ℤ} {k n : ℕ}
    (hn : n < k) :
    truncCoeffArrayAt
        (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 (k + 1)) n =
      truncCoeffArrayAt
        (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 k) n := by
  rw [phi41QRecurrenceRowArrayAux]
  rw [truncCoeffArrayAt_push_of_lt]
  rw [phi41QRecurrenceRowArrayAux_size]
  exact hn

theorem truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_succ_eq
    (N j valuation : ℕ) (E4 E6 E2E4 : Array ℤ) (k : ℕ) :
    truncCoeffArrayAt
        (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 (k + 1)) k =
      phi41QRecurrenceNextCoeff j valuation k E4 E6 E2E4
        (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 k) := by
  rw [phi41QRecurrenceRowArrayAux]
  rw [truncCoeffArrayAt_push_eq_of_size]
  rw [phi41QRecurrenceRowArrayAux_size]

theorem truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_next
    {N j valuation : ℕ} {E4 E6 E2E4 : Array ℤ} :
    ∀ {k n : ℕ}, n < k →
      truncCoeffArrayAt
          (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 k) n =
        phi41QRecurrenceNextCoeff j valuation n E4 E6 E2E4
          (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 n)
  | 0, n, hn => by omega
  | k + 1, n, hn => by
      by_cases hnk : n < k
      · rw [truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_succ_of_lt hnk]
        exact truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_next hnk
      · have hn_eq : n = k := by omega
        have hlast := truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_succ_eq
          N j valuation E4 E6 E2E4 k
        simpa [hn_eq] using hlast

theorem truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_zero_of_lt_valuation
    {N j valuation : ℕ} {E4 E6 E2E4 : Array ℤ} {k n : ℕ}
    (hnk : n < k) (hnv : n < valuation) :
    truncCoeffArrayAt
        (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 k) n = 0 := by
  rw [truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_next hnk]
  simp [phi41QRecurrenceNextCoeff, hnv]

theorem truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_one_of_eq_valuation
    {N j valuation : ℕ} {E4 E6 E2E4 : Array ℤ} {k n : ℕ}
    (hnk : n < k) (hnv : n = valuation) :
    truncCoeffArrayAt
        (phi41QRecurrenceRowArrayAux N j valuation E4 E6 E2E4 k) n = 1 := by
  rw [truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_next hnk]
  simp [phi41QRecurrenceNextCoeff, hnv]

theorem truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_next
    {N j n : ℕ} {E4 E6 E2E4 : Array ℤ} (hn : n < N) :
    truncCoeffArrayAt (phi41QRecurrenceRowArray N j E4 E6 E2E4) n =
      phi41QRecurrenceNextCoeff j (42 - j) n E4 E6 E2E4
        (phi41QRecurrenceRowArrayAux N j (42 - j) E4 E6 E2E4 n) := by
  simpa [phi41QRecurrenceRowArray] using
    (truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_next
      (N := N) (j := j) (valuation := 42 - j)
      (E4 := E4) (E6 := E6) (E2E4 := E2E4) hn)

theorem truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_zero_of_lt_valuation
    {N j n : ℕ} {E4 E6 E2E4 : Array ℤ}
    (hn : n < N) (hnv : n < 42 - j) :
    truncCoeffArrayAt (phi41QRecurrenceRowArray N j E4 E6 E2E4) n = 0 := by
  simpa [phi41QRecurrenceRowArray] using
    (truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_zero_of_lt_valuation
      (N := N) (j := j) (valuation := 42 - j)
      (E4 := E4) (E6 := E6) (E2E4 := E2E4) hn hnv)

theorem truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_one_of_eq_valuation
    {N j n : ℕ} {E4 E6 E2E4 : Array ℤ}
    (hn : n < N) (hnv : n = 42 - j) :
    truncCoeffArrayAt (phi41QRecurrenceRowArray N j E4 E6 E2E4) n = 1 := by
  simpa [phi41QRecurrenceRowArray] using
    (truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_one_of_eq_valuation
      (N := N) (j := j) (valuation := 42 - j)
      (E4 := E4) (E6 := E6) (E2E4 := E2E4) hn hnv)

theorem truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_recurrence_of_gt_valuation
    {N j n : ℕ} {E4 E6 E2E4 : Array ℤ}
    (hn : n < N) (hval : 42 - j < n) :
    truncCoeffArrayAt (phi41QRecurrenceRowArray N j E4 E6 E2E4) n =
      (sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * truncCoeffArrayAt E2E4 a -
            (j : ℤ) * truncCoeffArrayAt E6 a) -
          truncCoeffArrayAt E4 a * ((n - a : ℕ) : ℤ)) *
            truncCoeffArrayAt (phi41QRecurrenceRowArray N j E4 E6 E2E4) (n - a))) /
        (((n - (42 - j) : ℕ) : ℤ)) := by
  rw [truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_next hn]
  simp only [phi41QRecurrenceNextCoeff]
  rw [if_neg (by omega : ¬n < 42 - j)]
  rw [if_neg (by omega : ¬n = 42 - j)]
  congr 1
  apply sumRangeFromZ_congr
  intro a ha1 ha2
  congr 1
  have hidxn : n - a < n := by omega
  have hidxN : n - a < N := by omega
  rw [truncCoeffArrayAt_phi41QRecurrenceRowArrayAux_eq_next
    (N := N) (j := j) (valuation := 42 - j)
    (E4 := E4) (E6 := E6) (E2E4 := E2E4) hidxn]
  rw [truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_next hidxN]

theorem phi41QRecurrence_denominator_coprime_of_prime_gt
    {p N j n : ℕ} (hp : Nat.Prime p) (hpN : N < p)
    (hn : n < N) (hval : 42 - j < n) :
    Int.gcd (p : ℤ) (((n - (42 - j) : ℕ) : ℤ)) = 1 := by
  apply int_gcd_natCast_eq_one_of_prime_gt hp
  · omega
  · omega

theorem ListArrayEq.of_phi41QRecurrence
    {N j : ℕ} {rowL E4L E6L E2E4L : List ℤ}
    {E4A E6A E2E4A : Array ℤ}
    (hE4 : ListArrayEq N E4L E4A)
    (hE6 : ListArrayEq N E6L E6A)
    (hE2E4 : ListArrayEq N E2E4L E2E4A)
    (hzero : ∀ n : ℕ, n < N → n < 42 - j → truncCoeffAt rowL n = 0)
    (hone : ∀ n : ℕ, n < N → n = 42 - j → truncCoeffAt rowL n = 1)
    (hrec : ∀ n : ℕ, n < N → 42 - j < n →
      truncCoeffAt rowL n =
        (sumRangeFromZ 1 n (fun a =>
          (((42 : ℤ) * truncCoeffAt E2E4L a -
              (j : ℤ) * truncCoeffAt E6L a) -
            truncCoeffAt E4L a * ((n - a : ℕ) : ℤ)) *
              truncCoeffAt rowL (n - a))) /
          (((n - (42 - j) : ℕ) : ℤ))) :
    ListArrayEq N rowL (phi41QRecurrenceRowArray N j E4A E6A E2E4A) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hlt : n < 42 - j
      · rw [hzero n hn hlt]
        exact (truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_zero_of_lt_valuation
          (N := N) (j := j) (E4 := E4A) (E6 := E6A) (E2E4 := E2E4A)
          hn hlt).symm
      · by_cases heq : n = 42 - j
        · rw [hone n hn heq]
          exact (truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_one_of_eq_valuation
            (N := N) (j := j) (E4 := E4A) (E6 := E6A) (E2E4 := E2E4A)
            hn heq).symm
        · have hgt : 42 - j < n := by omega
          rw [hrec n hn hgt]
          rw [truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_recurrence_of_gt_valuation
            (N := N) (j := j) (E4 := E4A) (E6 := E6A) (E2E4 := E2E4A)
            hn hgt]
          congr 1
          apply sumRangeFromZ_congr
          intro a ha1 ha2
          have haN : a < N := by omega
          have hidxlt : n - a < n := by omega
          have hidxN : n - a < N := by omega
          rw [hE2E4 a haN, hE6 a haN, hE4 a haN, ih (n - a) hidxlt hidxN]

def phi41QRecurrenceRowsArray (N : ℕ) : Array (Array ℤ) :=
  let E4 := E4TruncCoeffArray N
  let E6 := E6TruncCoeffArray N
  let E2E4 := E2E4TruncCoeffArray N
  ((List.range 43).map
    (fun j => phi41QRecurrenceRowArray N j E4 E6 E2E4)).toArray

def phi41QRecurrenceRowsArrayOfFn
    (N : ℕ) (row : ℕ → ℕ → ℤ) : Array (Array ℤ) :=
  ((List.range 43).map
    (fun j => truncCoeffArrayOfFn N (row j))).toArray

theorem phi41QRecurrenceRowsArray_size (N : ℕ) :
    (phi41QRecurrenceRowsArray N).size = 43 := by
  simp [phi41QRecurrenceRowsArray]

/-- Recurrence-based level-41 coefficient array.

This mirrors `phi41Level41CoeffListCompressedMatrix`, but replaces the dense
tables for `(E₄^3)^j * Δ^(42-j)` by the Ramanujan recurrence rows above. -/
def phi41Level41RecurrenceCoeffArray (N : ℕ) : Array ℤ :=
  let M := (N + 40) / 41
  let PCompressed := phi41QRecurrenceRowsArray M
  let Q := phi41QRecurrenceRowsArray N
  let coeffs := phi41SparseCoeffMatrixArray
  (List.range 43).foldl
    (fun out x =>
      let qPart := linearCombinationFromCoeffMatrixArray N x Q coeffs
      addTruncCoeffArray N out
        (mulQPullback41CompressedTruncCoeffArray N
          (PCompressed.getD x (zeroTruncCoeffArray M)) qPart))
    (zeroTruncCoeffArray N)

def phi41Level41RecurrenceCoeffArrayFromRows
    (N M : ℕ) (PCompressed Q : Array (Array ℤ)) : Array ℤ :=
  let coeffs := phi41SparseCoeffMatrixArray
  (List.range 43).foldl
    (fun out x =>
      let qPart := linearCombinationFromCoeffMatrixArray N x Q coeffs
      addTruncCoeffArray N out
        (mulQPullback41CompressedTruncCoeffArray N
          (PCompressed.getD x (zeroTruncCoeffArray M)) qPart))
    (zeroTruncCoeffArray N)

def phi41QPartTableFromRows (N : ℕ) (Q : Array (Array ℤ)) :
    Array (Array ℤ) :=
  let coeffs := phi41SparseCoeffMatrixArray
  ((List.range 43).map
    (fun x => linearCombinationFromCoeffMatrixArray N x Q coeffs)).toArray

def phi41ContributionTableFromQParts
    (N M : ℕ) (PCompressed QParts : Array (Array ℤ)) :
    Array (Array ℤ) :=
  ((List.range 43).map
    (fun x =>
      mulQPullback41CompressedTruncCoeffArray N
        (PCompressed.getD x (zeroTruncCoeffArray M))
        (QParts.getD x (zeroTruncCoeffArray N)))).toArray

def phi41FinalFromContributions (N : ℕ)
    (Contributions : Array (Array ℤ)) : Array ℤ :=
  (List.range 43).foldl
    (fun out x =>
      addTruncCoeffArray N out
        (Contributions.getD x (zeroTruncCoeffArray N)))
    (zeroTruncCoeffArray N)

theorem array_getD_toArray_early {α : Type*} (xs : List α) (i : ℕ) (d : α) :
    xs.toArray.getD i d = xs.getD i d := by
  unfold Array.getD List.getD
  by_cases h : i < xs.length
  · simp [h]
  · simp [h]

theorem phi41QRecurrenceRowsArrayOfFn_getD_of_le
    (N : ℕ) (row : ℕ → ℕ → ℤ) {j : ℕ} (hj : j ≤ 42) :
    (phi41QRecurrenceRowsArrayOfFn N row).getD j (zeroTruncCoeffArray N) =
      truncCoeffArrayOfFn N (row j) := by
  have hjlt : j < 43 := by omega
  unfold phi41QRecurrenceRowsArrayOfFn
  rw [array_getD_toArray_early]
  rw [List.getD_eq_getElem
    (l := (List.range 43).map
      (fun j => truncCoeffArrayOfFn N (row j)))
    (d := zeroTruncCoeffArray N) (by simp [hjlt])]
  simp

theorem phi41QPartTableFromRows_getD_of_le
    (N : ℕ) (Q : Array (Array ℤ)) {x : ℕ} (hx : x ≤ 42) :
    (phi41QPartTableFromRows N Q).getD x (zeroTruncCoeffArray N) =
      linearCombinationFromCoeffMatrixArray N x Q phi41SparseCoeffMatrixArray := by
  have hxlt : x < 43 := by omega
  unfold phi41QPartTableFromRows
  rw [array_getD_toArray_early]
  rw [List.getD_eq_getElem
    (l := (List.range 43).map
      (fun x => linearCombinationFromCoeffMatrixArray N x Q
        phi41SparseCoeffMatrixArray))
    (d := zeroTruncCoeffArray N) (by simp [hxlt])]
  simp

theorem phi41ContributionTableFromQParts_getD_of_le
    (N M : ℕ) (PCompressed QParts : Array (Array ℤ))
    {x : ℕ} (hx : x ≤ 42) :
    (phi41ContributionTableFromQParts N M PCompressed QParts).getD x
        (zeroTruncCoeffArray N) =
      mulQPullback41CompressedTruncCoeffArray N
        (PCompressed.getD x (zeroTruncCoeffArray M))
        (QParts.getD x (zeroTruncCoeffArray N)) := by
  have hxlt : x < 43 := by omega
  unfold phi41ContributionTableFromQParts
  rw [array_getD_toArray_early]
  rw [List.getD_eq_getElem
    (l := (List.range 43).map
      (fun x =>
        mulQPullback41CompressedTruncCoeffArray N
          (PCompressed.getD x (zeroTruncCoeffArray M))
          (QParts.getD x (zeroTruncCoeffArray N))))
    (d := zeroTruncCoeffArray N) (by simp [hxlt])]
  simp

def phi41Level41RecurrenceCoeffArrayFromRowsCoeff
    (N M : ℕ) (PCompressed Q : Array (Array ℤ)) (n : ℕ) : ℤ :=
  let coeffs := phi41SparseCoeffMatrixArray
  sumRangeFromZ 0 43 (fun x =>
    truncCoeffArrayAt
      (mulQPullback41CompressedTruncCoeffArray N
        (PCompressed.getD x (zeroTruncCoeffArray M))
        (linearCombinationFromCoeffMatrixArray N x Q coeffs)) n)

theorem sumRangeFromZ_zero_succ_eq_add_last (K : ℕ) (f : ℕ → ℤ) :
    sumRangeFromZ 0 (K + 1) f = sumRangeFromZ 0 K f + f K := by
  rw [sumRangeFromZ_zero_eq_finset_sum, sumRangeFromZ_zero_eq_finset_sum]
  exact Finset.sum_range_succ f K

theorem sumRangeFromZ_zero_modEq_prefix
    {P : ℤ} {K : ℕ} {f pref : ℕ → ℤ}
    (hzero : pref 0 ≡ 0 [ZMOD P])
    (hstep : ∀ y : ℕ, y < K →
      pref (y + 1) ≡ pref y + f y [ZMOD P]) :
    sumRangeFromZ 0 K f ≡ pref K [ZMOD P] := by
  induction K with
  | zero =>
      simpa [sumRangeFromZ] using hzero.symm
  | succ K ih =>
      rw [sumRangeFromZ_zero_succ_eq_add_last]
      have ihK :
          sumRangeFromZ 0 K f ≡ pref K [ZMOD P] := by
        exact ih (by
          intro y hy
          exact hstep y (by omega))
      have hnext := hstep K (Nat.lt_succ_self K)
      exact (ihK.add (Int.ModEq.refl (f K))).trans hnext.symm

theorem truncCoeffArrayAt_foldl_add_terms_eq_sumRangeFromZ
    {N K n : ℕ} (hn : n < N) (term : ℕ → Array ℤ) :
    truncCoeffArrayAt
        ((List.range K).foldl
          (fun out x => addTruncCoeffArray N out (term x))
          (zeroTruncCoeffArray N)) n =
      sumRangeFromZ 0 K (fun x => truncCoeffArrayAt (term x) n) := by
  induction K with
  | zero =>
      simp [sumRangeFromZ, zeroTruncCoeffArray, truncCoeffArrayAt_ofFn_of_lt hn]
  | succ K ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [addTruncCoeffArray, truncCoeffArrayAt_ofFn_of_lt hn]
      rw [ih, sumRangeFromZ_zero_succ_eq_add_last]

theorem truncCoeffArrayAt_phi41Level41RecurrenceCoeffArrayFromRows
    {N M n : ℕ} {PCompressed Q : Array (Array ℤ)} (hn : n < N) :
    truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArrayFromRows N M PCompressed Q) n =
      phi41Level41RecurrenceCoeffArrayFromRowsCoeff
        N M PCompressed Q n := by
  unfold phi41Level41RecurrenceCoeffArrayFromRows
    phi41Level41RecurrenceCoeffArrayFromRowsCoeff
  exact truncCoeffArrayAt_foldl_add_terms_eq_sumRangeFromZ hn
    (fun x =>
      let qPart := linearCombinationFromCoeffMatrixArray N x Q
        phi41SparseCoeffMatrixArray
      mulQPullback41CompressedTruncCoeffArray N
        (PCompressed.getD x (zeroTruncCoeffArray M)) qPart)

theorem truncCoeffArrayAt_phi41FinalFromContributions
    {N n : ℕ} {Contributions : Array (Array ℤ)} (hn : n < N) :
    truncCoeffArrayAt (phi41FinalFromContributions N Contributions) n =
      sumRangeFromZ 0 43 (fun x =>
        truncCoeffArrayAt
          (Contributions.getD x (zeroTruncCoeffArray N)) n) := by
  unfold phi41FinalFromContributions
  exact truncCoeffArrayAt_foldl_add_terms_eq_sumRangeFromZ hn
    (fun x => Contributions.getD x (zeroTruncCoeffArray N))

def phi41Level41RecurrenceCoeffArrayFromRowsFinalModEqChunk
    (N M p start len : ℕ)
    (PCompressed Q : Array (Array ℤ)) (Final : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < N then
      intCoeffModEq p
        (phi41Level41RecurrenceCoeffArrayFromRowsCoeff N M PCompressed Q n)
        (truncCoeffArrayAt Final n)
    else
      true)

def phi41Level41RecurrenceCoeffArrayFromRowsFinalModEqChunked
    (N M p chunkSize numChunks : ℕ)
    (PCompressed Q : Array (Array ℤ)) (Final : Array ℤ) : Bool :=
  (List.range numChunks).all (fun c =>
    phi41Level41RecurrenceCoeffArrayFromRowsFinalModEqChunk
      N M p (c * chunkSize) chunkSize PCompressed Q Final)

theorem TruncCoeffArrayModEq.of_phi41FinalModEqChunked
    {N M p chunkSize numChunks : ℕ}
    {PCompressed Q : Array (Array ℤ)} {Final : Array ℤ}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunked :
      phi41Level41RecurrenceCoeffArrayFromRowsFinalModEqChunked
        N M p chunkSize numChunks PCompressed Q Final = true) :
    TruncCoeffArrayModEq N p
      (phi41Level41RecurrenceCoeffArrayFromRows N M PCompressed Q)
      Final := by
  intro n hn
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
  unfold phi41Level41RecurrenceCoeffArrayFromRowsFinalModEqChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold phi41Level41RecurrenceCoeffArrayFromRowsFinalModEqChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hentry_n :
      intCoeffModEq p
        (phi41Level41RecurrenceCoeffArrayFromRowsCoeff N M PCompressed Q n)
        (truncCoeffArrayAt Final n) = true := by
    simpa [hn_eq, hn] using hentry
  rw [truncCoeffArrayAt_phi41Level41RecurrenceCoeffArrayFromRows hn]
  exact int_modEq_of_intCoeffModEq hentry_n

def phi41FinalFromContributionsCoeff
    (N : ℕ) (Contributions : Array (Array ℤ)) (n : ℕ) : ℤ :=
  sumRangeFromZ 0 43 (fun x =>
    truncCoeffArrayAt
      (Contributions.getD x (zeroTruncCoeffArray N)) n)

def phi41FinalFromContributionsModEqChunk
    (N p start len : ℕ)
    (Contributions : Array (Array ℤ)) (Final : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < N then
      intCoeffModEq p
        (phi41FinalFromContributionsCoeff N Contributions n)
        (truncCoeffArrayAt Final n)
    else
      true)

def phi41FinalFromContributionsModEqChunked
    (N p chunkSize numChunks : ℕ)
    (Contributions : Array (Array ℤ)) (Final : Array ℤ) : Bool :=
  (List.range numChunks).all (fun c =>
    phi41FinalFromContributionsModEqChunk
      N p (c * chunkSize) chunkSize Contributions Final)

theorem phi41FinalFromContributionsModEqChunked_of_chunks
    {N p chunkSize numChunks : ℕ}
    {Contributions : Array (Array ℤ)} {Final : Array ℤ}
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41FinalFromContributionsModEqChunk
        N p (c * chunkSize) chunkSize Contributions Final = true) :
    phi41FinalFromContributionsModEqChunked
      N p chunkSize numChunks Contributions Final = true := by
  unfold phi41FinalFromContributionsModEqChunked
  apply List.all_eq_true.mpr
  intro c hcmem
  exact hchunks c (List.mem_range.mp hcmem)

theorem phi41FinalFromContributionsModEqChunk_of_entries
    {N p start len : ℕ}
    {Contributions : Array (Array ℤ)} {Final : Array ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < N then
         intCoeffModEq p
           (phi41FinalFromContributionsCoeff N Contributions n)
           (truncCoeffArrayAt Final n)
       else
         true) = true) :
    phi41FinalFromContributionsModEqChunk
      N p start len Contributions Final = true := by
  unfold phi41FinalFromContributionsModEqChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem TruncCoeffArrayModEq.phi41FinalFromContributions_of_prefix
    {N p : ℕ} {Contributions : Array (Array ℤ)}
    {Final Prefix : Array ℤ}
    (hzero : ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix (0 * N + n) ≡ 0 [ZMOD (p : ℤ)])
    (hstep : ∀ x : ℕ, x < 43 → ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix ((x + 1) * N + n) ≡
        truncCoeffArrayAt Prefix (x * N + n) +
          truncCoeffArrayAt
            (Contributions.getD x (zeroTruncCoeffArray N)) n
        [ZMOD (p : ℤ)])
    (hfinal : ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix (43 * N + n) ≡
        truncCoeffArrayAt Final n [ZMOD (p : ℤ)]) :
    TruncCoeffArrayModEq N p
      (phi41FinalFromContributions N Contributions) Final := by
  intro n hn
  rw [truncCoeffArrayAt_phi41FinalFromContributions hn]
  have hprefix :
      sumRangeFromZ 0 43 (fun x =>
        truncCoeffArrayAt
          (Contributions.getD x (zeroTruncCoeffArray N)) n) ≡
        truncCoeffArrayAt Prefix (43 * N + n) [ZMOD (p : ℤ)] := by
    apply sumRangeFromZ_zero_modEq_prefix
      (pref := fun x => truncCoeffArrayAt Prefix (x * N + n))
    · simpa using hzero n hn
    · intro x hx
      simpa [Nat.add_mul] using hstep x hx n hn
  exact hprefix.trans (hfinal n hn)

theorem TruncCoeffArrayModEq.of_phi41FinalFromContributionsModEqChunked
    {N p chunkSize numChunks : ℕ}
    {Contributions : Array (Array ℤ)} {Final : Array ℤ}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunked :
      phi41FinalFromContributionsModEqChunked
        N p chunkSize numChunks Contributions Final = true) :
    TruncCoeffArrayModEq N p
      (phi41FinalFromContributions N Contributions) Final := by
  intro n hn
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
  unfold phi41FinalFromContributionsModEqChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold phi41FinalFromContributionsModEqChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hentry_n :
      intCoeffModEq p
        (phi41FinalFromContributionsCoeff N Contributions n)
        (truncCoeffArrayAt Final n) = true := by
    simpa [hn_eq, hn] using hentry
  rw [truncCoeffArrayAt_phi41FinalFromContributions hn]
  simpa [phi41FinalFromContributionsCoeff] using
    int_modEq_of_intCoeffModEq hentry_n

theorem TruncCoeffArrayModEq.of_phi41FinalFromContributionsModEqChunks
    {N p chunkSize numChunks : ℕ}
    {Contributions : Array (Array ℤ)} {Final : Array ℤ}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41FinalFromContributionsModEqChunk
        N p (c * chunkSize) chunkSize Contributions Final = true) :
    TruncCoeffArrayModEq N p
      (phi41FinalFromContributions N Contributions) Final :=
  TruncCoeffArrayModEq.of_phi41FinalFromContributionsModEqChunked
    hcover (phi41FinalFromContributionsModEqChunked_of_chunks hchunks)

def phi41Level41RecurrenceCoeffArrayFirstZero (N : ℕ) : Bool :=
  truncCoeffArrayFirstZero N (phi41Level41RecurrenceCoeffArray N)

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_crt_certificate
    {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime)
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| <
          (ps.prod : ℤ))
    (hmods : ∀ n : ℕ, n < phi41Level41SturmBound → ∀ p ∈ ps,
      truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n ≡
          0 [ZMOD (p : ℤ)]) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  exact truncCoeffArrayFirstZero_of_crt_certificate hcop hbound hmods

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_crt_bounded_certificate
    {ps : List ℕ} (hcop : ps.Pairwise Nat.Coprime) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (hmods : ∀ n : ℕ, n < phi41Level41SturmBound → ∀ p ∈ ps,
      truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n ≡
          0 [ZMOD (p : ℤ)]) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  exact truncCoeffArrayFirstZero_of_crt_bounded_certificate hcop hbound hB hmods

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_certificate
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (hmods : ∀ n : ℕ, n < phi41Level41SturmBound → ∀ p ∈ ps,
      truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n ≡
          0 [ZMOD (p : ℤ)]) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  exact phi41Level41RecurrenceCoeffArrayFirstZero_of_crt_bounded_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB hmods

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_mod_certificate
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (hmods : ∀ p ∈ ps,
      truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) = true) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  exact truncCoeffArrayFirstZero_of_crt_bounded_mod_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB hmods

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_function_certificate
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (ys : ℕ → ℕ → ℤ)
    (hrel : ∀ p ∈ ps, ∀ n : ℕ, n < phi41Level41SturmBound →
      truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n ≡
          ys p n [ZMOD (p : ℤ)])
    (hzero : ∀ p ∈ ps, ∀ n : ℕ, n < phi41Level41SturmBound →
      ys p n ≡ 0 [ZMOD (p : ℤ)]) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  exact truncCoeffArrayFirstZero_of_crt_bounded_function_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB ys hrel hzero

/-- The formal geometric series `1 + X^m + X^(2m) + ...`.  It is used only for
positive `m`, where it is the inverse of `1 - X^m`. -/
def geomSeriesZ (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if m ∣ n then 1 else 0

theorem coeff_geomSeriesZ (m n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (geomSeriesZ m) = if m ∣ n then 1 else 0 := by
  simp [geomSeriesZ]

theorem one_sub_X_pow_mul_geomSeriesZ {m : ℕ} (hm : 0 < m) :
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) * geomSeriesZ m = 1 := by
  ext n
  rw [sub_mul]
  simp only [one_mul]
  simp only [map_sub]
  rw [coeff_geomSeriesZ]
  rw [PowerSeries.coeff_X_pow_mul']
  rw [show PowerSeries.coeff (R := ℤ) n (1 : PowerSeries ℤ) =
      if n = 0 then 1 else 0 by simp]
  by_cases hn0 : n = 0
  · subst hn0
    have hmnot : ¬m ≤ 0 := by omega
    simp [hmnot]
  · have h0coeff : (if n = 0 then (1 : ℤ) else 0) = 0 := by simp [hn0]
    rw [h0coeff]
    by_cases hmn : m ≤ n
    · rw [if_pos hmn]
      rw [coeff_geomSeriesZ]
      have hdiv_iff : m ∣ n ↔ m ∣ n - m := by
        constructor
        · intro h
          exact Nat.dvd_sub h (dvd_refl m)
        · intro h
          have hadd : m ∣ (n - m) + m := Nat.dvd_add h (dvd_refl m)
          rwa [Nat.sub_add_cancel hmn] at hadd
      by_cases hdiv : m ∣ n
      · rw [if_pos hdiv]
        rw [if_pos (hdiv_iff.mp hdiv)]
        ring
      · rw [if_neg hdiv]
        rw [if_neg (by exact mt hdiv_iff.mpr hdiv)]
        ring
    · rw [if_neg hmn]
      have hnotdiv : ¬m ∣ n := by
        intro h
        exact hmn (Nat.le_of_dvd (by omega) h)
      rw [if_neg hnotdiv]
      ring

theorem geomSeriesZ_mul_one_sub_X_pow {m : ℕ} (hm : 0 < m) :
    geomSeriesZ m * (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) = 1 := by
  rw [mul_comm]
  exact one_sub_X_pow_mul_geomSeriesZ hm

theorem deltaEulerFactorZ_mul_geomSeriesZ {m : ℕ} (hm : 0 < m) :
    deltaEulerFactorZ m * geomSeriesZ m =
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) ^ 23 := by
  unfold deltaEulerFactorZ
  rw [show (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) ^ 24 =
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) ^ 23 *
        (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) by ring]
  rw [mul_assoc]
  rw [one_sub_X_pow_mul_geomSeriesZ hm]
  ring

noncomputable def finiteE2ProductLogSeriesZ (N : ℕ) : PowerSeries ℤ :=
  1 + ∑ i ∈ Finset.range N,
    PowerSeries.C ((-24 : ℤ) * ((i + 1 : ℕ) : ℤ)) *
      (PowerSeries.X : PowerSeries ℤ) ^ (i + 1) * geomSeriesZ (i + 1)

theorem coeff_finiteE2ProductLogSeriesZ_zero (N : ℕ) :
    PowerSeries.coeff (R := ℤ) 0 (finiteE2ProductLogSeriesZ N) = 1 := by
  unfold finiteE2ProductLogSeriesZ
  rw [map_add]
  rw [map_sum]
  have hsum :
      (∑ x ∈ Finset.range N,
        PowerSeries.coeff (R := ℤ) 0
          (PowerSeries.C ((-24 : ℤ) * ((x + 1 : ℕ) : ℤ)) *
            (PowerSeries.X : PowerSeries ℤ) ^ (x + 1) * geomSeriesZ (x + 1))) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x _hx
    rw [show PowerSeries.C ((-24 : ℤ) * ((x + 1 : ℕ) : ℤ)) *
          (PowerSeries.X : PowerSeries ℤ) ^ (x + 1) * geomSeriesZ (x + 1) =
        PowerSeries.C ((-24 : ℤ) * ((x + 1 : ℕ) : ℤ)) *
          ((PowerSeries.X : PowerSeries ℤ) ^ (x + 1) * geomSeriesZ (x + 1)) by ring]
    rw [PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_X_pow_mul']
    rw [if_neg (by omega : ¬x + 1 ≤ 0)]
    ring
  rw [hsum]
  simp

theorem coeff_finiteE2ProductLogSeriesZ_pos (N k : ℕ) (hk : k ≠ 0) :
    PowerSeries.coeff (R := ℤ) k (finiteE2ProductLogSeriesZ N) =
      ∑ i ∈ Finset.range N,
        if i + 1 ∣ k then (-24 : ℤ) * ((i + 1 : ℕ) : ℤ) else 0 := by
  unfold finiteE2ProductLogSeriesZ
  rw [map_add]
  rw [map_sum]
  have hone : PowerSeries.coeff (R := ℤ) k (1 : PowerSeries ℤ) = 0 := by
    simp [hk]
  rw [hone, zero_add]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [show PowerSeries.C ((-24 : ℤ) * ((i + 1 : ℕ) : ℤ)) *
        (PowerSeries.X : PowerSeries ℤ) ^ (i + 1) * geomSeriesZ (i + 1) =
      PowerSeries.C ((-24 : ℤ) * ((i + 1 : ℕ) : ℤ)) *
        ((PowerSeries.X : PowerSeries ℤ) ^ (i + 1) * geomSeriesZ (i + 1)) by ring]
  rw [PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hik : i + 1 ≤ k
  · rw [if_pos hik]
    rw [coeff_geomSeriesZ]
    have hdiv_iff : i + 1 ∣ k ↔ i + 1 ∣ k - (i + 1) := by
      constructor
      · intro h
        exact Nat.dvd_sub h (dvd_refl (i + 1))
      · intro h
        have hadd : i + 1 ∣ (k - (i + 1)) + (i + 1) :=
          Nat.dvd_add h (dvd_refl (i + 1))
        rwa [Nat.sub_add_cancel hik] at hadd
    by_cases hdiv : i + 1 ∣ k
    · rw [if_pos hdiv, if_pos (hdiv_iff.mp hdiv)]
      ring
    · rw [if_neg hdiv]
      rw [if_neg (by exact mt hdiv_iff.mpr hdiv)]
      ring
  · rw [if_neg hik]
    have hnotdiv : ¬i + 1 ∣ k := by
      intro h
      exact hik (Nat.le_of_dvd (by omega) h)
    rw [if_neg hnotdiv]
    ring

theorem sum_range_divisors_extend {N k : ℕ} (hk0 : k ≠ 0) (hkN : k ≤ N) :
    (∑ i ∈ Finset.range N,
      if i + 1 ∣ k then ((i + 1 : ℕ) : ℤ) else 0) =
    ∑ i ∈ Finset.range k,
      if i + 1 ∣ k then ((i + 1 : ℕ) : ℤ) else 0 := by
  symm
  apply Finset.sum_subset
  · intro i hi
    simp at hi ⊢
    omega
  · intro i _hiN hik
    have hi_ge : k ≤ i := by
      have hik' : ¬ i < k := by
        intro h
        exact hik (by simpa using h)
      omega
    have hnotdiv : ¬i + 1 ∣ k := by
      intro h
      have hle := Nat.le_of_dvd (by omega : 0 < k) h
      omega
    simp [hnotdiv]

theorem finite_divisor_sum_eq_sigma {N k : ℕ} (hk0 : k ≠ 0) (hkN : k ≤ N) :
    (∑ i ∈ Finset.range N,
      if i + 1 ∣ k then ((i + 1 : ℕ) : ℤ) else 0) =
      ((ArithmeticFunction.sigma 1 k : ℕ) : ℤ) := by
  rw [sum_range_divisors_extend hk0 hkN]
  have hs := sigmaOneNat_eq_finset_range_sum k
  rw [sigmaOneNat_eq_arithmeticFunction_sigma_one] at hs
  simpa [Nat.add_comm] using hs.symm

theorem coeff_finiteE2ProductLogSeriesZ_eq_E2ZSeries_of_le {N k : ℕ}
    (hkN : k ≤ N) :
    PowerSeries.coeff (R := ℤ) k (finiteE2ProductLogSeriesZ N) =
      PowerSeries.coeff (R := ℤ) k E2ZSeries := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [coeff_finiteE2ProductLogSeriesZ_zero]
    rw [coeff_E2ZSeries_zero]
  · rw [coeff_finiteE2ProductLogSeriesZ_pos N k hk0]
    rw [coeff_E2ZSeries_pos hk0]
    have hfactor :
        (∑ i ∈ Finset.range N,
          if i + 1 ∣ k then (-24 : ℤ) * ((i + 1 : ℕ) : ℤ) else 0) =
          (-24 : ℤ) * ∑ i ∈ Finset.range N,
            if i + 1 ∣ k then ((i + 1 : ℕ) : ℤ) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases hdiv : i + 1 ∣ k
      · simp [hdiv]
      · simp [hdiv]
    rw [hfactor]
    rw [finite_divisor_sum_eq_sigma hk0 hkN]

theorem X_mul_natCast_mul_X_pow_pred (m : ℕ) :
    (PowerSeries.X : PowerSeries ℤ) *
        ((m : PowerSeries ℤ) * (PowerSeries.X : PowerSeries ℤ) ^ (m - 1)) =
      (m : PowerSeries ℤ) * (PowerSeries.X : PowerSeries ℤ) ^ m := by
  cases m with
  | zero => simp
  | succ m =>
      simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]
      rw [pow_succ']
      ring

theorem C_neg_24_mul_nat (m : ℕ) :
    PowerSeries.C ((-24 : ℤ) * (m : ℤ)) =
      -((24 : PowerSeries ℤ) * (m : PowerSeries ℤ)) := by
  simp

theorem X_mul_derivative_deltaEulerFactorZ (m : ℕ) :
    PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerFactorZ m) =
      PowerSeries.C ((-24 : ℤ) * (m : ℤ)) *
        (PowerSeries.X : PowerSeries ℤ) ^ m *
        (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) ^ 23 := by
  rw [deltaEulerFactorZ]
  rw [PowerSeries.derivative_pow]
  rw [map_sub]
  rw [Derivation.map_one_eq_zero]
  rw [PowerSeries.derivative_pow]
  rw [PowerSeries.derivative_X]
  simp only [Nat.cast_ofNat, Nat.reduceSub, mul_one]
  rw [show (24 : PowerSeries ℤ) * (1 - PowerSeries.X ^ m) ^ 23 *
        (0 - ((m : PowerSeries ℤ) * PowerSeries.X ^ (m - 1))) =
      -((24 : PowerSeries ℤ) * ((m : PowerSeries ℤ) * PowerSeries.X ^ (m - 1)) *
        (1 - PowerSeries.X ^ m) ^ 23) by ring]
  calc
    PowerSeries.X *
        -((24 : PowerSeries ℤ) * ((m : PowerSeries ℤ) * PowerSeries.X ^ (m - 1)) *
          (1 - PowerSeries.X ^ m) ^ 23)
        = -((24 : PowerSeries ℤ) *
            (PowerSeries.X * ((m : PowerSeries ℤ) * PowerSeries.X ^ (m - 1))) *
            (1 - PowerSeries.X ^ m) ^ 23) := by ring
    _ = -((24 : PowerSeries ℤ) * ((m : PowerSeries ℤ) * PowerSeries.X ^ m) *
            (1 - PowerSeries.X ^ m) ^ 23) := by
          rw [X_mul_natCast_mul_X_pow_pred]
    _ = PowerSeries.C ((-24 : ℤ) * (m : ℤ)) * PowerSeries.X ^ m *
            (1 - PowerSeries.X ^ m) ^ 23 := by
          rw [C_neg_24_mul_nat]
          ring

theorem trunc_one_sub_X_pow_Z_eq_one_of_lt {d m : ℕ} (hdm : d < m) :
    PowerSeries.trunc (R := ℤ) (d + 1)
        (1 - (PowerSeries.X : PowerSeries ℤ) ^ m) = 1 := by
  ext i
  rw [PowerSeries.coeff_trunc]
  by_cases hi : i < d + 1
  · have him : i ≠ m := by omega
    rw [if_pos hi, Polynomial.coeff_one]
    simp [PowerSeries.coeff_X_pow, him]
  · have hi0 : i ≠ 0 := by omega
    rw [if_neg hi, Polynomial.coeff_one]
    simp [hi0]

theorem trunc_deltaEulerFactorZ_eq_one_of_lt {d m : ℕ} (hdm : d < m) :
    PowerSeries.trunc (R := ℤ) (d + 1) (deltaEulerFactorZ m) = 1 := by
  unfold deltaEulerFactorZ
  induction 24 with
  | zero =>
      exact PowerSeries.trunc_one d
  | succ _k ih =>
      rw [pow_succ, ← PowerSeries.trunc_trunc_mul_trunc]
      rw [trunc_one_sub_X_pow_Z_eq_one_of_lt hdm, ih]
      simp

theorem coeff_mul_deltaEulerFactorZ_of_lt (f : PowerSeries ℤ) {d m : ℕ}
    (hdm : d < m) :
    PowerSeries.coeff (R := ℤ) d (f * deltaEulerFactorZ m) =
      PowerSeries.coeff (R := ℤ) d f := by
  rw [PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc
    (f := f) (g := deltaEulerFactorZ m) (n := d + 1) (d := d)
    (Nat.lt_succ_self d)]
  rw [trunc_deltaEulerFactorZ_eq_one_of_lt hdm]
  simp [PowerSeries.coeff_coe_trunc_of_lt (Nat.lt_succ_self d)]

theorem coeff_deltaEulerFactorZ_zero_of_pos {m : ℕ} (hm : 0 < m) :
    PowerSeries.coeff (R := ℤ) 0 (deltaEulerFactorZ m) = 1 := by
  have hm0 : m ≠ 0 := by omega
  simp [deltaEulerFactorZ, PowerSeries.coeff_zero_eq_constantCoeff, zero_pow hm0]

theorem coeff_deltaEulerFactorZ_eq_zero_of_pos_lt {m n : ℕ} (hn0 : n ≠ 0)
    (hnm : n < m) :
    PowerSeries.coeff (R := ℤ) n (deltaEulerFactorZ m) = 0 := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff n)
    (trunc_deltaEulerFactorZ_eq_one_of_lt (d := n) (m := m) hnm)
  change (PowerSeries.trunc (R := ℤ) (n + 1) (deltaEulerFactorZ m)).coeff n =
    (1 : Polynomial ℤ).coeff n at h
  rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)] at h
  simpa [Polynomial.coeff_one, hn0] using h

theorem coeff_mul_deltaEulerFactorZ_of_le_of_coeff_zero
    (f : PowerSeries ℤ) {d m : ℕ}
    (hdm : d ≤ m) (hf0 : PowerSeries.coeff (R := ℤ) 0 f = 0) :
    PowerSeries.coeff (R := ℤ) d (f * deltaEulerFactorZ m) =
      PowerSeries.coeff (R := ℤ) d f := by
  by_cases hlt : d < m
  · exact coeff_mul_deltaEulerFactorZ_of_lt f hlt
  · have hdm' : d = m := by omega
    subst d
    by_cases hm0 : m = 0
    · subst hm0
      simp [hf0, deltaEulerFactorZ, PowerSeries.coeff_zero_eq_constantCoeff]
    · have hmpos : 0 < m := by omega
      rw [PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff (R := ℤ) i f *
          PowerSeries.coeff (R := ℤ) j (deltaEulerFactorZ m)) m]
      rw [Finset.sum_range_succ]
      have hlow :
          (∑ x ∈ Finset.range m,
            PowerSeries.coeff (R := ℤ) x f *
              PowerSeries.coeff (R := ℤ) (m - x) (deltaEulerFactorZ m)) = 0 := by
        rw [Finset.sum_eq_zero]
        intro x hx
        have hxlt : x < m := Finset.mem_range.mp hx
        by_cases hx0 : x = 0
        · subst hx0
          rw [hf0]
          ring
        · have hn0 : m - x ≠ 0 := by omega
          have hnlt : m - x < m := by omega
          rw [coeff_deltaEulerFactorZ_eq_zero_of_pos_lt hn0 hnlt]
          ring
      rw [hlow]
      rw [show m - m = 0 by omega]
      rw [coeff_deltaEulerFactorZ_zero_of_pos hmpos]
      ring

theorem coeff_deltaEulerProductTruncZ_succ_of_lt {N d : ℕ} (hdN : d < N + 1) :
    PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ (N + 1)) =
      PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ N) := by
  unfold deltaEulerProductTruncZ
  rw [Finset.prod_range_succ]
  rw [← mul_assoc]
  exact coeff_mul_deltaEulerFactorZ_of_lt
    ((PowerSeries.X : PowerSeries ℤ) *
      ∏ m ∈ Finset.range N, deltaEulerFactorZ (m + 1)) hdN

theorem coeff_deltaEulerProductTruncZ_succ_of_le {N d : ℕ} (hdN : d ≤ N + 1) :
    PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ (N + 1)) =
      PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ N) := by
  unfold deltaEulerProductTruncZ
  rw [Finset.prod_range_succ]
  rw [← mul_assoc]
  apply coeff_mul_deltaEulerFactorZ_of_le_of_coeff_zero
  · exact hdN
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]

theorem coeff_deltaEulerProductTruncZ_eq_of_le_succ {N M d : ℕ}
    (hdN : d ≤ N + 1) (hNM : N ≤ M) :
    PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ M) =
      PowerSeries.coeff (R := ℤ) d (deltaEulerProductTruncZ N) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ]
      rw [coeff_deltaEulerProductTruncZ_succ_of_le]
      · exact ih (Nat.le_add_right N k)
      · omega

theorem coeff_deltaEulerProductTruncZ_zero (N : ℕ) :
    PowerSeries.coeff (R := ℤ) 0 (deltaEulerProductTruncZ N) = 0 := by
  simp [deltaEulerProductTruncZ, PowerSeries.coeff_zero_eq_constantCoeff]

theorem coeff_deltaEulerProductTruncZ_one (N : ℕ) :
    PowerSeries.coeff (R := ℤ) 1 (deltaEulerProductTruncZ N) = 1 := by
  induction N with
  | zero =>
      simp [deltaEulerProductTruncZ]
  | succ N ih =>
      by_cases hN : N = 0
      · subst hN
        simp [deltaEulerProductTruncZ, deltaEulerFactorZ]
      · have hlt : 1 < N + 1 := by omega
        rw [coeff_deltaEulerProductTruncZ_succ_of_lt hlt]
        exact ih

theorem coeff_X_pow_mul_eq_zero_of_lt (f : PowerSeries ℤ) {k d : ℕ} (hd : d < k) :
    PowerSeries.coeff (R := ℤ) d ((PowerSeries.X : PowerSeries ℤ) ^ k * f) = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  simp [show ¬ k ≤ d by omega]

theorem coeff_C_mul_X_pow_mul_eq_zero_of_lt (c : ℤ) (f : PowerSeries ℤ) {k d : ℕ}
    (hd : d < k) :
    PowerSeries.coeff (R := ℤ) d
      (PowerSeries.C c * (PowerSeries.X : PowerSeries ℤ) ^ k * f) = 0 := by
  rw [show PowerSeries.C c * (PowerSeries.X : PowerSeries ℤ) ^ k * f =
      PowerSeries.C c * ((PowerSeries.X : PowerSeries ℤ) ^ k * f) by ring]
  rw [PowerSeries.coeff_C_mul]
  rw [coeff_X_pow_mul_eq_zero_of_lt f hd]
  ring

theorem prod_range_succ_erase_last (f : ℕ → PowerSeries ℤ) (N : ℕ) :
    (∏ j ∈ (Finset.range (N + 1)).erase N, f j) = ∏ j ∈ Finset.range N, f j := by
  refine Finset.prod_congr ?_ ?_
  · ext j
    simp
    omega
  · intro x _hx
    rfl

theorem prod_range_succ_erase_of_mem_range (f : ℕ → PowerSeries ℤ) {N x : ℕ}
    (hx : x ∈ Finset.range N) :
    (∏ j ∈ (Finset.range (N + 1)).erase x, f j) =
      (∏ j ∈ (Finset.range N).erase x, f j) * f N := by
  have hNmem : N ∈ (Finset.range (N + 1)).erase x := by
    simp
    have hxlt : x < N := Finset.mem_range.mp hx
    omega
  have hprod := Finset.prod_erase_mul ((Finset.range (N + 1)).erase x) f hNmem
  rw [← hprod]
  congr 1
  refine Finset.prod_congr ?_ ?_
  · ext j
    simp
    omega
  · intro y _hy
    rfl

theorem derivative_prod_range_powerSeries (f : ℕ → PowerSeries ℤ) (N : ℕ) :
    PowerSeries.derivative ℤ (∏ i ∈ Finset.range N, f i) =
      ∑ i ∈ Finset.range N,
        (∏ j ∈ (Finset.range N).erase i, f j) * PowerSeries.derivative ℤ (f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.prod_range_succ]
      rw [Derivation.leibniz]
      rw [ih]
      rw [Finset.sum_range_succ]
      rw [prod_range_succ_erase_last]
      simp only [Algebra.smul_def]
      rw [Algebra.algebraMap_self]
      simp only [RingHom.id_apply]
      have hsumold :
          (∑ x ∈ Finset.range N,
            (∏ j ∈ (Finset.range (N + 1)).erase x, f j) *
              PowerSeries.derivative ℤ (f x)) =
          f N * ∑ x ∈ Finset.range N,
            (∏ j ∈ (Finset.range N).erase x, f j) *
              PowerSeries.derivative ℤ (f x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [prod_range_succ_erase_of_mem_range f hx]
        ring
      rw [hsumold]
      ring

theorem X_mul_derivative_deltaEulerProductTruncZ (N : ℕ) :
    PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerProductTruncZ N) =
      deltaEulerProductTruncZ N +
        PowerSeries.X * ∑ i ∈ Finset.range N,
          (∏ j ∈ (Finset.range N).erase i, deltaEulerFactorZ (j + 1)) *
            (PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerFactorZ (i + 1))) := by
  rw [deltaEulerProductTruncZ]
  rw [Derivation.leibniz]
  rw [derivative_prod_range_powerSeries (fun i => deltaEulerFactorZ (i + 1)) N]
  rw [PowerSeries.derivative_X]
  simp only [Algebra.smul_def]
  rw [Algebra.algebraMap_self]
  simp only [RingHom.id_apply, mul_one]
  let S : PowerSeries ℤ := ∑ i ∈ Finset.range N,
    (∏ j ∈ (Finset.range N).erase i, deltaEulerFactorZ (j + 1)) *
      PowerSeries.derivative ℤ (deltaEulerFactorZ (i + 1))
  let T : PowerSeries ℤ := ∑ i ∈ Finset.range N,
    (∏ j ∈ (Finset.range N).erase i, deltaEulerFactorZ (j + 1)) *
      (PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerFactorZ (i + 1)))
  have hsum : (PowerSeries.X : PowerSeries ℤ) ^ 2 * S = PowerSeries.X * T := by
    unfold S T
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    ring
  change PowerSeries.X * (PowerSeries.X * S +
      ∏ j ∈ Finset.range N, deltaEulerFactorZ (j + 1)) =
    PowerSeries.X * ∏ j ∈ Finset.range N, deltaEulerFactorZ (j + 1) +
      PowerSeries.X * T
  rw [mul_add]
  rw [show PowerSeries.X * (PowerSeries.X * S) =
      (PowerSeries.X : PowerSeries ℤ) ^ 2 * S by ring]
  rw [hsum]
  ring

theorem X_mul_derivative_deltaEulerProductTruncZ_expanded (N : ℕ) :
    PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerProductTruncZ N) =
      deltaEulerProductTruncZ N +
        PowerSeries.X * ∑ i ∈ Finset.range N,
          (∏ j ∈ (Finset.range N).erase i, deltaEulerFactorZ (j + 1)) *
            (PowerSeries.C ((-24 : ℤ) * ((i + 1 : ℕ) : ℤ)) *
              (PowerSeries.X : PowerSeries ℤ) ^ (i + 1) *
              (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) ^ 23) := by
  rw [X_mul_derivative_deltaEulerProductTruncZ]
  congr 2
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [X_mul_derivative_deltaEulerFactorZ]

theorem X_mul_derivative_deltaEulerProductTruncZ_log (N : ℕ) :
    PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerProductTruncZ N) =
      finiteE2ProductLogSeriesZ N * deltaEulerProductTruncZ N := by
  rw [X_mul_derivative_deltaEulerProductTruncZ_expanded]
  unfold finiteE2ProductLogSeriesZ deltaEulerProductTruncZ
  rw [add_mul]
  rw [one_mul]
  rw [Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hprod := Finset.prod_erase_mul (Finset.range N)
    (fun j => deltaEulerFactorZ (j + 1)) hi
  have hfactor :
      (∏ j ∈ Finset.range N, deltaEulerFactorZ (j + 1)) =
        (∏ j ∈ (Finset.range N).erase i, deltaEulerFactorZ (j + 1)) *
          deltaEulerFactorZ (i + 1) := by
    exact hprod.symm
  rw [hfactor]
  have hgeom :
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ (i + 1)) ^ 23 =
        geomSeriesZ (i + 1) * deltaEulerFactorZ (i + 1) := by
    rw [mul_comm]
    exact (deltaEulerFactorZ_mul_geomSeriesZ (by omega : 0 < i + 1)).symm
  rw [hgeom]
  ring

theorem coeff_X_derivative_eq_of_coeff_eq {f g : PowerSeries ℤ} {d : ℕ}
    (hcoeff : PowerSeries.coeff (R := ℤ) d f = PowerSeries.coeff (R := ℤ) d g) :
    PowerSeries.coeff (R := ℤ) d (PowerSeries.X * PowerSeries.derivative ℤ f) =
      PowerSeries.coeff (R := ℤ) d (PowerSeries.X * PowerSeries.derivative ℤ g) := by
  cases d with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      rw [PowerSeries.coeff_succ_X_mul]
      rw [PowerSeries.coeff_derivative]
      rw [PowerSeries.coeff_derivative]
      rw [hcoeff]

theorem coeff_X_derivative_eq_natCast_mul_coeff (f : PowerSeries ℤ) (d : ℕ) :
    PowerSeries.coeff (R := ℤ) d (PowerSeries.X * PowerSeries.derivative ℤ f) =
      (d : ℤ) * PowerSeries.coeff (R := ℤ) d f := by
  cases d with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      rw [PowerSeries.coeff_derivative]
      rw [show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 by omega]
      ring

theorem coeff_X_derivative_deltaEulerSeriesZ_eq_trunc_of_lt {N d : ℕ}
    (hdN : d < N) :
    PowerSeries.coeff (R := ℤ) d
        (PowerSeries.X * PowerSeries.derivative ℤ deltaEulerSeriesZ) =
      PowerSeries.coeff (R := ℤ) d
        (PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerProductTruncZ N)) := by
  apply coeff_X_derivative_eq_of_coeff_eq
  rw [coeff_deltaEulerSeriesZ]
  exact (coeff_deltaEulerProductTruncZ_eq_deltaEulerCoeffZ_of_lt hdN).symm

theorem coeff_mul_eq_of_right_coeff_eq_up_to (g f h : PowerSeries ℤ) {d : ℕ}
    (hcoeff : ∀ n : ℕ, n ≤ d →
      PowerSeries.coeff (R := ℤ) n f = PowerSeries.coeff (R := ℤ) n h) :
    PowerSeries.coeff (R := ℤ) d (g * f) =
      PowerSeries.coeff (R := ℤ) d (g * h) := by
  rw [PowerSeries.coeff_mul]
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl ?_
  intro ij hij
  have hsum : ij.1 + ij.2 = d := Finset.mem_antidiagonal.mp hij
  rw [hcoeff ij.2 (by omega)]

theorem coeff_mul_eq_const_add_tail (p q : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (p * q) =
      PowerSeries.coeff (R := ℤ) 0 p * PowerSeries.coeff (R := ℤ) n q +
        ∑ a ∈ Finset.range n,
          PowerSeries.coeff (R := ℤ) (a + 1) p *
            PowerSeries.coeff (R := ℤ) (n - (a + 1)) q := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j =>
      PowerSeries.coeff (R := ℤ) i p *
        PowerSeries.coeff (R := ℤ) j q) n]
  rw [Finset.sum_range_succ']
  rw [show n - 0 = n by omega]
  ring

theorem coeff_mul_X_derivative_eq_const_add_tail
    (p q : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n
        (p * (PowerSeries.X * PowerSeries.derivative ℤ q)) =
      PowerSeries.coeff (R := ℤ) 0 p *
          ((n : ℤ) * PowerSeries.coeff (R := ℤ) n q) +
        ∑ a ∈ Finset.range n,
          PowerSeries.coeff (R := ℤ) (a + 1) p *
            (((n - (a + 1) : ℕ) : ℤ) *
              PowerSeries.coeff (R := ℤ) (n - (a + 1)) q) := by
  rw [coeff_mul_eq_const_add_tail]
  rw [coeff_X_derivative_eq_natCast_mul_coeff]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [coeff_X_derivative_eq_natCast_mul_coeff]

theorem coeff_E2_mul_deltaEulerSeriesZ_eq_trunc_of_lt {N d : ℕ} (hdN : d < N) :
    PowerSeries.coeff (R := ℤ) d (E2ZSeries * deltaEulerSeriesZ) =
      PowerSeries.coeff (R := ℤ) d (E2ZSeries * deltaEulerProductTruncZ N) := by
  apply coeff_mul_eq_of_right_coeff_eq_up_to
  intro n hn
  rw [coeff_deltaEulerSeriesZ]
  exact (coeff_deltaEulerProductTruncZ_eq_deltaEulerCoeffZ_of_lt (N := N)
    (d := n) (by omega)).symm

theorem coeff_E2ZSeries_mul (f : PowerSeries ℤ) (d : ℕ) :
    PowerSeries.coeff (R := ℤ) d (E2ZSeries * f) =
      PowerSeries.coeff (R := ℤ) d f +
        (-24 : ℤ) * ∑ k ∈ Finset.range d,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            PowerSeries.coeff (R := ℤ) (d - (k + 1)) f := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff (R := ℤ) i E2ZSeries *
      PowerSeries.coeff (R := ℤ) j f) d]
  rw [Finset.sum_range_succ']
  rw [coeff_E2ZSeries_zero]
  have hmid :
      (∑ x ∈ Finset.range d,
        PowerSeries.coeff (R := ℤ) (x + 1) E2ZSeries *
          PowerSeries.coeff (R := ℤ) (d - (x + 1)) f) =
        (-24 : ℤ) * ∑ k ∈ Finset.range d,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            PowerSeries.coeff (R := ℤ) (d - (k + 1)) f := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [coeff_E2ZSeries_succ]
    ring
  rw [hmid]
  rw [show d - 0 = d by omega]
  ring

theorem coeff_X_derivative_deltaEulerProductTruncZ_eq_E2_mul_of_le {N d : ℕ}
    (hdN : d ≤ N) :
    PowerSeries.coeff (R := ℤ) d
        (PowerSeries.X * PowerSeries.derivative ℤ (deltaEulerProductTruncZ N)) =
      PowerSeries.coeff (R := ℤ) d (E2ZSeries * deltaEulerProductTruncZ N) := by
  rw [X_mul_derivative_deltaEulerProductTruncZ_log]
  rw [mul_comm (finiteE2ProductLogSeriesZ N) (deltaEulerProductTruncZ N)]
  rw [show E2ZSeries * deltaEulerProductTruncZ N =
      deltaEulerProductTruncZ N * E2ZSeries by ring]
  apply coeff_mul_eq_of_right_coeff_eq_up_to
  intro n hn
  exact coeff_finiteE2ProductLogSeriesZ_eq_E2ZSeries_of_le (le_trans hn hdN)

theorem deltaEulerCoeffZ_recurrence_of_derivative_identity
    (hderiv : PowerSeries.X * PowerSeries.derivative ℤ deltaEulerSeriesZ =
      E2ZSeries * deltaEulerSeriesZ) :
    ∀ n : ℕ,
      deltaEulerCoeffZ (n + 2) =
        ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
          (fun i =>
            deltaEulerCoeffZ i *
              ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ))) /
          ((n + 1 : ℕ) : ℤ) := by
  intro n
  let S : ℤ := ∑ j ∈ Finset.range (n + 1),
    deltaEulerCoeffZ (n + 1 - j) * ((ArithmeticFunction.sigma 1 (j + 1) : ℕ) : ℤ)
  have hcoeff := coeff_succ_of_X_derivative_eq_mul
    deltaEulerSeriesZ E2ZSeries hderiv (n + 1)
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff (R := ℤ) i E2ZSeries *
      PowerSeries.coeff (R := ℤ) j deltaEulerSeriesZ) (n + 1 + 1)] at hcoeff
  simp only [coeff_deltaEulerSeriesZ] at hcoeff
  have hconv :
      (∑ k ∈ Finset.range (n + 1 + 1).succ,
        PowerSeries.coeff (R := ℤ) k E2ZSeries *
          deltaEulerCoeffZ (n + 1 + 1 - k)) =
        deltaEulerCoeffZ (n + 2) + (-24 : ℤ) * S := by
    rw [show (n + 1 + 1).succ = n + 3 by omega]
    rw [show n + 3 = (n + 2) + 1 by omega]
    rw [Finset.sum_range_succ]
    have hlast : PowerSeries.coeff (R := ℤ) (n + 2) E2ZSeries *
          deltaEulerCoeffZ (n + 2 - (n + 2)) = 0 := by
      rw [show n + 2 - (n + 2) = 0 by omega]
      rw [deltaEulerCoeffZ_zero]
      ring
    rw [hlast, add_zero]
    rw [show n + 2 = (n + 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    rw [coeff_E2ZSeries_zero]
    have hmid :
        (∑ k ∈ Finset.range (n + 1),
          PowerSeries.coeff (R := ℤ) (k + 1) E2ZSeries *
            deltaEulerCoeffZ (n + 2 - (k + 1))) = (-24 : ℤ) * S := by
      unfold S
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [coeff_E2ZSeries_succ]
      have hklt : k < n + 1 := Finset.mem_range.mp hk
      rw [show n + 2 - (k + 1) = n + 1 - k by omega]
      ring
    rw [hmid]
    rw [show n + 2 - 0 = n + 2 by omega]
    ring
  rw [hconv] at hcoeff
  have hcoeff' : deltaEulerCoeffZ (n + 2) * (((n + 1 : ℕ) : ℤ) + 1) =
      deltaEulerCoeffZ (n + 2) + (-24 : ℤ) * S := by
    simpa [show n + 1 + 1 = n + 2 by omega,
      show ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 by omega] using hcoeff
  have hmul : ((n + 1 : ℕ) : ℤ) * deltaEulerCoeffZ (n + 2) =
      (-24 : ℤ) * S := by
    calc
      ((n + 1 : ℕ) : ℤ) * deltaEulerCoeffZ (n + 2)
          = deltaEulerCoeffZ (n + 2) * (((n + 1 : ℕ) : ℤ) + 1) -
              deltaEulerCoeffZ (n + 2) := by ring
      _ = (-24 : ℤ) * S := by
          rw [hcoeff']
          ring
  have hS :
      sumRangeFromZ 1 (n + 1)
          (fun i =>
            deltaEulerCoeffZ i *
              ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ)) = S := by
    exact sumRangeFromZ_sigma_reverse n deltaEulerCoeffZ
  rw [hS]
  rw [← hmul]
  rw [Int.mul_ediv_cancel_left]
  exact_mod_cast (Nat.succ_ne_zero n)

theorem TruncRep.coeff_eq_zero_of_array_firstZero {N : ℕ}
    {p : PowerSeries ℤ} {xs : List ℤ} {A : Array ℤ}
    (hrep : TruncRep N p xs) (harray : ListArrayEq N xs A)
    (hzero : truncCoeffArrayFirstZero N A = true) :
    ∀ n : ℕ, n < N → PowerSeries.coeff (R := ℤ) n p = 0 := by
  intro n hn
  rw [hrep n hn, harray n hn]
  exact truncCoeffArrayAt_eq_zero_of_firstZero hzero hn

theorem ListArrayEq.of_array_eq_first {N : ℕ} {xs : List ℤ} {A B : Array ℤ}
    (hxs : ListArrayEq N xs A) (hAB : truncCoeffArrayEqFirst N A B = true) :
    ListArrayEq N xs B := by
  intro n hn
  rw [hxs n hn, truncCoeffArrayAt_eq_of_eqFirst hAB hn]

def deltaEulerRamanujanEqFirst (N : ℕ) : Bool :=
  truncCoeffArrayEqFirstCached N
    (fun _ => deltaEulerTruncCoeffArray N)
    (fun _ => deltaRamanujanTruncCoeffArray N)

def phi41Level41FastCoeffArrayFirstZero (N : ℕ) : Bool :=
  truncCoeffArrayFirstZeroCached N
    (fun _ => phi41Level41FastCoeffArray N)

theorem truncCoeffAt_addTruncCoeffList_of_lt {N n : ℕ}
    (a b : List ℤ) (hn : n < N) :
    truncCoeffAt (addTruncCoeffList N a b) n =
      truncCoeffAt a n + truncCoeffAt b n := by
  simp [addTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]

theorem truncCoeffAt_scaleTruncCoeffList_of_lt {N n : ℕ}
    (c : ℤ) (a : List ℤ) (hn : n < N) :
    truncCoeffAt (scaleTruncCoeffList N c a) n =
      c * truncCoeffAt a n := by
  simp [scaleTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]

theorem truncCoeffAt_mulTruncCoeffList_of_lt {N n : ℕ}
    (a b : List ℤ) (hn : n < N) :
    truncCoeffAt (mulTruncCoeffList N a b) n =
      ∑ ij ∈ Finset.antidiagonal n, truncCoeffAt a ij.1 * truncCoeffAt b ij.2 := by
  simp [mulTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]

theorem truncCoeffAt_mulTruncCoeffList_eq_zero_of_lt_add {N n va vb : ℕ}
    {a b : List ℤ}
    (hn : n < N)
    (ha : ∀ i, i < N → i < va → truncCoeffAt a i = 0)
    (hb : ∀ i, i < N → i < vb → truncCoeffAt b i = 0)
    (hnv : n < va + vb) :
    truncCoeffAt (mulTruncCoeffList N a b) n = 0 := by
  rw [truncCoeffAt_mulTruncCoeffList_of_lt a b hn]
  apply Finset.sum_eq_zero
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  have hiN : ij.1 < N := by omega
  have hjN : ij.2 < N := by omega
  have hsplit : ij.1 < va ∨ ij.2 < vb := by
    by_contra h
    have hia : va ≤ ij.1 := by omega
    have hib : vb ≤ ij.2 := by omega
    omega
  rcases hsplit with hia | hib
  · rw [ha ij.1 hiN hia]
    ring
  · rw [hb ij.2 hjN hib]
    ring

theorem truncCoeffAt_mulTruncCoeffList_eq_mul_of_eq_add {N va vb : ℕ}
    {a b : List ℤ} {ca cb : ℤ}
    (hn : va + vb < N)
    (ha0 : ∀ i, i < N → i < va → truncCoeffAt a i = 0)
    (hb0 : ∀ i, i < N → i < vb → truncCoeffAt b i = 0)
    (ha : truncCoeffAt a va = ca)
    (hb : truncCoeffAt b vb = cb) :
    truncCoeffAt (mulTruncCoeffList N a b) (va + vb) = ca * cb := by
  rw [truncCoeffAt_mulTruncCoeffList_of_lt a b hn]
  have hmem : (va, vb) ∈ Finset.antidiagonal (va + vb) := by
    simp
  rw [Finset.sum_eq_single (a := (va, vb))]
  · rw [ha, hb]
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = va + vb := Finset.mem_antidiagonal.mp hij
    have hiN : ij.1 < N := by omega
    have hjN : ij.2 < N := by omega
    have hsplit : ij.1 < va ∨ ij.2 < vb := by
      by_contra h
      have hia : va ≤ ij.1 := by omega
      have hib : vb ≤ ij.2 := by omega
      have hiaeq : ij.1 = va := by omega
      have hibeq : ij.2 = vb := by omega
      exact hne (Prod.ext hiaeq hibeq)
    rcases hsplit with hia | hib
    · rw [ha0 ij.1 hiN hia]
      ring
    · rw [hb0 ij.2 hjN hib]
      ring
  · intro hnot
    exact False.elim (hnot hmem)

theorem truncCoeffAt_constTruncCoeffList_zero {N : ℕ} (hN : 0 < N) :
    truncCoeffAt (constTruncCoeffList N 1) 0 = 1 := by
  rw [constTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hN]
  simp

theorem truncCoeffAt_powTruncCoeffList_eq_zero_of_lt_mul {N n v k : ℕ}
    {a : List ℤ}
    (hn : n < N)
    (ha0 : ∀ i, i < N → i < v → truncCoeffAt a i = 0)
    (hnv : n < k * v) :
    truncCoeffAt (powTruncCoeffList N a k) n = 0 := by
  induction k generalizing n with
  | zero =>
      omega
  | succ k ih =>
      rw [powTruncCoeffList]
      apply truncCoeffAt_mulTruncCoeffList_eq_zero_of_lt_add hn
      · intro i hiN hiv
        exact ih hiN hiv
      · exact ha0
      · simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnv

theorem truncCoeffAt_powTruncCoeffList_eq_pow_of_eq_mul {N v k : ℕ}
    {a : List ℤ} {c : ℤ}
    (hN : k * v < N)
    (ha0 : ∀ i, i < N → i < v → truncCoeffAt a i = 0)
    (ha : truncCoeffAt a v = c) :
    truncCoeffAt (powTruncCoeffList N a k) (k * v) = c ^ k := by
  induction k with
  | zero =>
      have hN0 : 0 < N := by simpa using hN
      simpa [powTruncCoeffList] using truncCoeffAt_constTruncCoeffList_zero hN0
  | succ k ih =>
      rw [powTruncCoeffList]
      rw [show (k + 1) * v = k * v + v by
        simp [Nat.succ_mul, Nat.add_comm]]
      have hprevN : k * v < N := by
        exact lt_of_le_of_lt (Nat.mul_le_mul_right v (Nat.le_succ k)) hN
      have hmulN : k * v + v < N := by
        simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hN
      rw [truncCoeffAt_mulTruncCoeffList_eq_mul_of_eq_add
        (N := N) (va := k * v) (vb := v)
        (a := powTruncCoeffList N a k) (b := a) (ca := c ^ k) (cb := c)
        hmulN]
      · rw [pow_succ]
      · intro i hiN hiv
        exact truncCoeffAt_powTruncCoeffList_eq_zero_of_lt_mul hiN ha0 hiv
      · exact ha0
      · exact ih hprevN
      · exact ha

theorem ListArrayEq.add {N : ℕ} {a b : List ℤ} {A B : Array ℤ}
    (ha : ListArrayEq N a A) (hb : ListArrayEq N b B) :
    ListArrayEq N (addTruncCoeffList N a b) (addTruncCoeffArray N A B) := by
  intro n hn
  calc
    truncCoeffAt (addTruncCoeffList N a b) n
        = truncCoeffAt a n + truncCoeffAt b n :=
          truncCoeffAt_addTruncCoeffList_of_lt a b hn
    _ = truncCoeffArrayAt A n + truncCoeffArrayAt B n := by rw [ha n hn, hb n hn]
    _ = truncCoeffArrayAt (addTruncCoeffArray N A B) n := by
          unfold addTruncCoeffArray
          simpa [truncCoeffAt_truncCoeffList_of_lt hn] using
            (ListArrayEq.ofFn N
              (fun n => truncCoeffArrayAt A n + truncCoeffArrayAt B n) n hn)

theorem ListArrayEq.scale {N : ℕ} {a : List ℤ} {A : Array ℤ} (c : ℤ)
    (ha : ListArrayEq N a A) :
    ListArrayEq N (scaleTruncCoeffList N c a) (scaleTruncCoeffArray N c A) := by
  intro n hn
  calc
    truncCoeffAt (scaleTruncCoeffList N c a) n = c * truncCoeffAt a n :=
      truncCoeffAt_scaleTruncCoeffList_of_lt c a hn
    _ = c * truncCoeffArrayAt A n := by rw [ha n hn]
    _ = truncCoeffArrayAt (scaleTruncCoeffArray N c A) n := by
      unfold scaleTruncCoeffArray
      simpa [truncCoeffAt_truncCoeffList_of_lt hn] using
        (ListArrayEq.ofFn N (fun n => c * truncCoeffArrayAt A n) n hn)

theorem ListArrayEq.sub {N : ℕ} {a b : List ℤ} {A B : Array ℤ}
    (ha : ListArrayEq N a A) (hb : ListArrayEq N b B) :
    ListArrayEq N (subTruncCoeffList N a b) (subTruncCoeffArray N A B) := by
  simpa [subTruncCoeffList, subTruncCoeffArray] using ha.add (hb.scale (-1))

theorem truncCoeffArrayAt_mulTruncCoeffArray_of_lt {N n : ℕ}
    (a b : Array ℤ) (hn : n < N) :
    truncCoeffArrayAt (mulTruncCoeffArray N a b) n =
      ∑ ij ∈ Finset.antidiagonal n,
        truncCoeffArrayAt a ij.1 * truncCoeffArrayAt b ij.2 := by
  unfold mulTruncCoeffArray
  calc
    truncCoeffArrayAt
        (truncCoeffArrayOfFn N
          (fun n => Id.run do
            let mut s : ℤ := 0
            for i in [0:n + 1] do
              s := s + truncCoeffArrayAt a i * truncCoeffArrayAt b (n - i)
            return s)) n =
        sumRangeFromZ 0 (n + 1)
          (fun i => truncCoeffArrayAt a i * truncCoeffArrayAt b (n - i)) := by
          rw [← forIn_range_add_eq_sumRangeFromZ (n + 1)
            (fun i => truncCoeffArrayAt a i * truncCoeffArrayAt b (n - i))]
          simpa [truncCoeffAt_truncCoeffList_of_lt hn] using
            (ListArrayEq.ofFn N
              (fun n => Id.run do
                let mut s : ℤ := 0
                for i in [0:n + 1] do
                  s := s + truncCoeffArrayAt a i * truncCoeffArrayAt b (n - i)
                return s) n hn).symm
    _ = ∑ i ∈ Finset.range (n + 1),
        truncCoeffArrayAt a i * truncCoeffArrayAt b (n - i) := by
          rw [sumRangeFromZ_zero_eq_finset_sum]
    _ = ∑ ij ∈ Finset.antidiagonal n,
        truncCoeffArrayAt a ij.1 * truncCoeffArrayAt b ij.2 := by
          exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => truncCoeffArrayAt a i * truncCoeffArrayAt b j) n).symm

theorem ListArrayEq.mul {N : ℕ} {a b : List ℤ} {A B : Array ℤ}
    (ha : ListArrayEq N a A) (hb : ListArrayEq N b B) :
    ListArrayEq N (mulTruncCoeffList N a b) (mulTruncCoeffArray N A B) := by
  intro n hn
  calc
    truncCoeffAt (mulTruncCoeffList N a b) n =
        ∑ ij ∈ Finset.antidiagonal n, truncCoeffAt a ij.1 * truncCoeffAt b ij.2 :=
          truncCoeffAt_mulTruncCoeffList_of_lt a b hn
    _ = ∑ ij ∈ Finset.antidiagonal n,
        truncCoeffArrayAt A ij.1 * truncCoeffArrayAt B ij.2 := by
          refine Finset.sum_congr rfl ?_
          intro ij hij
          have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
          have hiN : ij.1 < N := by omega
          have hjN : ij.2 < N := by omega
          rw [ha ij.1 hiN, hb ij.2 hjN]
    _ = truncCoeffArrayAt (mulTruncCoeffArray N A B) n := by
          rw [truncCoeffArrayAt_mulTruncCoeffArray_of_lt A B hn]

theorem ListArrayEq.pow {N k : ℕ} {a : List ℤ} {A : Array ℤ}
    (ha : ListArrayEq N a A) :
    ListArrayEq N (powTruncCoeffList N a k) (powTruncCoeffArray N A k) := by
  induction k with
  | zero =>
      simpa [powTruncCoeffList, powTruncCoeffArray] using ListArrayEq.const N 1
  | succ k ih =>
      simpa [powTruncCoeffList, powTruncCoeffArray] using ih.mul ha

theorem truncCoeffArrayAt_qPullback41TruncCoeffArray_of_lt {N n : ℕ}
    (A : Array ℤ) (hn : n < N) :
    truncCoeffArrayAt (qPullback41TruncCoeffArray N A) n =
      if 41 ∣ n then truncCoeffArrayAt A (n / 41) else 0 := by
  unfold qPullback41TruncCoeffArray
  simpa [truncCoeffAt_truncCoeffList_of_lt hn] using
    (ListArrayEq.ofFn N
      (fun n => if 41 ∣ n then truncCoeffArrayAt A (n / 41) else 0) n hn).symm

theorem ListArrayEq.qPullback41 {N : ℕ} {a : List ℤ} {A : Array ℤ}
    (ha : ListArrayEq N a A) :
    ListArrayEq N (qPullback41TruncCoeffList N a) (qPullback41TruncCoeffArray N A) := by
  intro n hn
  rw [qPullback41TruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn,
    truncCoeffArrayAt_qPullback41TruncCoeffArray_of_lt A hn]
  by_cases hdiv : 41 ∣ n
  · rw [if_pos hdiv]
    rw [if_pos hdiv]
    exact ha (n / 41) (lt_of_le_of_lt (Nat.div_le_self n 41) hn)
  · rw [if_neg hdiv]
    rw [if_neg hdiv]

theorem ListArrayEq.XPow (N m : ℕ) :
    ListArrayEq N (XPowTruncCoeffList N m) (XPowTruncCoeffArray N m) := by
  simpa [XPowTruncCoeffList, XPowTruncCoeffArray] using
    ListArrayEq.ofFn N (fun n => if n = m then (1 : ℤ) else 0)

theorem ListArrayEq.E4 (N : ℕ) :
    ListArrayEq N (E4TruncCoeffList N) (E4TruncCoeffArray N) := by
  simpa [E4TruncCoeffList, E4TruncCoeffArray] using
    ListArrayEq.ofFn N E4CoeffZ

theorem ListArrayEq.E2 (N : ℕ) :
    ListArrayEq N (E2TruncCoeffList N) (E2TruncCoeffArray N) := by
  simpa [E2TruncCoeffList, E2TruncCoeffArray] using
    ListArrayEq.ofFn N E2CoeffZ

theorem ListArrayEq.E6 (N : ℕ) :
    ListArrayEq N (E6TruncCoeffList N) (E6TruncCoeffArray N) := by
  simpa [E6TruncCoeffList, E6TruncCoeffArray] using
    ListArrayEq.ofFn N E6CoeffZ

theorem ListArrayEq.E2E4 (N : ℕ) :
    ListArrayEq N (E2E4TruncCoeffList N) (E2E4TruncCoeffArray N) := by
  simpa [E2E4TruncCoeffList, E2E4TruncCoeffArray] using
    (ListArrayEq.E2 N).mul (ListArrayEq.E4 N)

theorem Array.getD_toArray {α : Type*} (xs : List α) (i : ℕ) (d : α) :
    xs.toArray.getD i d = xs.getD i d := by
  unfold Array.getD List.getD
  by_cases h : i < xs.length
  · simp [h]
  · simp [h]

theorem phi41QRecurrenceRowsArray_getD_of_le
    (N : ℕ) {j : ℕ} (hj : j ≤ 42) :
    (phi41QRecurrenceRowsArray N).getD j (zeroTruncCoeffArray N) =
      phi41QRecurrenceRowArray N j
        (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N) := by
  have hjlt : j < 43 := by omega
  unfold phi41QRecurrenceRowsArray
  rw [Array.getD_toArray]
  rw [List.getD_eq_getElem (l := (List.range 43).map
      (fun j =>
        phi41QRecurrenceRowArray N j
          (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N)))
      (d := zeroTruncCoeffArray N) (by simp [hjlt])]
  simp

theorem phi41SparseCoeffMatrixArray_getD_of_lt {x y : ℕ}
    (hx : x < 43) (hy : y < 43) :
    (phi41SparseCoeffMatrixArray.getD x (Array.replicate 43 0)).getD y 0 =
      phi41SparseCoeffAt x y := by
  let rows : List (Array ℤ) :=
    (List.range 43).map
      (fun x => ((List.range 43).map
        (fun y => phi41SparseCoeffAt x y)).toArray)
  have hrows : phi41SparseCoeffMatrixArray = rows.toArray := by
    rfl
  rw [hrows]
  unfold Array.getD
  have hxsize : x < rows.toArray.size := by
    simp [rows, hx]
  rw [dif_pos hxsize]
  have hxlen : x < rows.length := by
    simp [rows, hx]
  have hrow :
      rows.toArray.getInternal x hxsize = rows[x] := by
    exact List.getElem_toArray hxlen
  rw [hrow]
  have hrowval :
      rows[x] = ((List.range 43).map
        (fun y => phi41SparseCoeffAt x y)).toArray := by
    simp [rows]
  rw [hrowval]
  have hysize :
      y < ((List.range 43).map
        (fun y => phi41SparseCoeffAt x y)).toArray.size := by
    simp [hy]
  rw [dif_pos hysize]
  have hylen :
      y < ((List.range 43).map
        (fun y => phi41SparseCoeffAt x y)).length := by
    simp [hy]
  have hyval :
      ((List.range 43).map
          (fun y => phi41SparseCoeffAt x y)).toArray.getInternal y hysize =
        ((List.range 43).map
          (fun y => phi41SparseCoeffAt x y))[y] := by
    exact List.getElem_toArray hylen
  rw [hyval]
  simp

theorem truncCoeffAt_linearCombinationFromCoeffMatrixList_phi41Sparse
    {N x n : ℕ} (Q : List (List ℤ))
    (hx : x < 43) (hn : n < N) :
    truncCoeffAt
        (linearCombinationFromCoeffMatrixList N x Q phi41SparseCoeffMatrixArray) n =
      sparseRowLinearCombinationTerms phi41SparseTerms x
        (fun y => truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n) := by
  unfold linearCombinationFromCoeffMatrixList
  rw [truncCoeffAt_truncCoeffList_of_lt hn]
  calc
    sumRangeFromZ 0 43
        (fun y =>
          (phi41SparseCoeffMatrixArray.getD x (Array.replicate 43 0)).getD y 0 *
            truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n)
        =
      sumRangeFromZ 0 43
        (fun y =>
          phi41SparseCoeffAt x y *
            truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n) := by
        rw [sumRangeFromZ_eq_finset_sum, sumRangeFromZ_eq_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro y hy
        have hylt : y < 43 := Finset.mem_range.mp hy
        simpa [Nat.zero_add] using congrArg
          (fun c => c * truncCoeffAt (Q.getD (0 + y) (zeroTruncCoeffList N)) n)
          (phi41SparseCoeffMatrixArray_getD_of_lt (x := x) (y := y) hx hylt)
    _ =
      sumRangeFromZ 0 43
        (fun y =>
          sparseCoeffAtTerms phi41SparseTerms x y *
            truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n) := by
        rw [sumRangeFromZ_eq_finset_sum, sumRangeFromZ_eq_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro y _hy
        rw [phi41SparseCoeffAt_eq_sparseCoeffAtTerms]
    _ =
      sparseRowLinearCombinationTerms phi41SparseTerms x
        (fun y => truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n) := by
        exact sum_sparseCoeffAtTerms_eq_sparseRowLinearCombinationTerms
          phi41SparseTerms x
          (fun y => truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n)
          (by
            intro t ht
            have hdeg := phi41SparseTerms_degree_le_42 t ht
            omega)

theorem sumRangeFromZ_single_sparseRowTerm
    (t : SparseBivarTerm) (F : ℕ → ℕ → ℤ)
    (hx : t.xPow < 43) :
    sumRangeFromZ 0 43
        (fun x => if t.xPow = x then t.coeff * F x t.yPow else 0) =
      t.coeff * F t.xPow t.yPow := by
  rw [sumRangeFromZ_zero_eq_finset_sum]
  have hmem : t.xPow ∈ Finset.range 43 := Finset.mem_range.mpr hx
  rw [Finset.sum_eq_single_of_mem t.xPow hmem]
  · simp
  · intro x _hxMem hxNe
    have hxNe' : ¬ t.xPow = x := by
      intro h
      exact hxNe h.symm
    simp [hxNe']

theorem sum_sparseRowLinearCombinationTerms_eq_sparseTermLinearCombinationTerms
    (terms : List SparseBivarTerm) (F : ℕ → ℕ → ℤ)
    (hdeg : ∀ t ∈ terms, t.xPow < 43) :
    sumRangeFromZ 0 43
        (fun x => sparseRowLinearCombinationTerms terms x (F x)) =
      sparseTermLinearCombinationTerms terms F := by
  induction terms with
  | nil =>
      simp [sparseRowLinearCombinationTerms, sparseTermLinearCombinationTerms, sumRangeFromZ]
  | cons t ts ih =>
      have ht : t.xPow < 43 := hdeg t (by simp)
      have hts : ∀ u ∈ ts, u.xPow < 43 := by
        intro u hu
        exact hdeg u (by simp [hu])
      change
        sumRangeFromZ 0 43
            (fun x =>
              ((if t.xPow = x then t.coeff * F x t.yPow else 0) +
                sparseRowLinearCombinationTerms ts x (F x))) =
          t.coeff * F t.xPow t.yPow +
            sparseTermLinearCombinationTerms ts F
      rw [sumRangeFromZ_zero_eq_finset_sum]
      rw [Finset.sum_add_distrib]
      rw [← sumRangeFromZ_zero_eq_finset_sum 43
          (fun x => if t.xPow = x then t.coeff * F x t.yPow else 0),
        sumRangeFromZ_single_sparseRowTerm t F ht]
      rw [← sumRangeFromZ_zero_eq_finset_sum 43
          (fun x => sparseRowLinearCombinationTerms ts x (F x)),
        ih hts]

theorem truncCoeffAt_linearCombinationFromCoeffMatrixList_eq_forXPowList
    {N x n : ℕ} (Q : List (List ℤ))
    (hx : x < 43) (hn : n < N) :
    truncCoeffAt
        (linearCombinationFromCoeffMatrixList N x Q phi41SparseCoeffMatrixArray) n =
      truncCoeffAt (linearCombinationForXPowList N x Q phi41SparseTerms) n := by
  rw [truncCoeffAt_linearCombinationFromCoeffMatrixList_phi41Sparse Q hx hn]
  rw [linearCombinationForXPowList, truncCoeffAt_truncCoeffList_of_lt hn]

theorem truncCoeffAt_evalSparseCompressedFromProductTablesTrunc
    {N M n : ℕ} (P Q : List (List ℤ)) (terms : List SparseBivarTerm)
    (hn : n < N) :
    truncCoeffAt
        (evalSparseCompressedFromProductTablesTrunc N M P Q terms) n =
      sparseTermLinearCombinationTerms terms
        (fun x y =>
          truncCoeffAt
            (mulQPullback41CompressedTruncCoeffList N
              (P.getD x (zeroTruncCoeffList M))
              (Q.getD y (zeroTruncCoeffList N))) n) := by
  induction terms with
  | nil =>
      simp [evalSparseCompressedFromProductTablesTrunc,
        sparseTermLinearCombinationTerms, zeroTruncCoeffList,
        truncCoeffAt_truncCoeffList_of_lt hn]
  | cons t ts ih =>
      rw [evalSparseCompressedFromProductTablesTrunc,
        sparseTermLinearCombinationTerms]
      rw [truncCoeffAt_addTruncCoeffList_of_lt _ _ hn,
        truncCoeffAt_scaleTruncCoeffList_of_lt _ _ hn, ih]

theorem sparseRowLinearCombinationTerms_congr
    (terms : List SparseBivarTerm) (x : ℕ) {q r : ℕ → ℤ}
    (h : ∀ y, q y = r y) :
    sparseRowLinearCombinationTerms terms x q =
      sparseRowLinearCombinationTerms terms x r := by
  induction terms with
  | nil =>
      simp [sparseRowLinearCombinationTerms]
  | cons t ts ih =>
      simp [sparseRowLinearCombinationTerms, h, ih]

theorem sparseTermLinearCombinationTerms_congr
    (terms : List SparseBivarTerm) {F G : ℕ → ℕ → ℤ}
    (h : ∀ x y, F x y = G x y) :
    sparseTermLinearCombinationTerms terms F =
      sparseTermLinearCombinationTerms terms G := by
  induction terms with
  | nil =>
      simp [sparseTermLinearCombinationTerms]
  | cons t ts ih =>
      simp [sparseTermLinearCombinationTerms, h, ih]

theorem sparseRowLinearCombinationTerms_sumRangeFromZ
    (terms : List SparseBivarTerm) (x K : ℕ)
    (a : ℕ → ℤ) (q : ℕ → ℕ → ℤ) :
    sumRangeFromZ 0 K
        (fun m => a m * sparseRowLinearCombinationTerms terms x (q m)) =
      sparseRowLinearCombinationTerms terms x
        (fun y => sumRangeFromZ 0 K (fun m => a m * q m y)) := by
  induction terms with
  | nil =>
      rw [sumRangeFromZ_zero_eq_finset_sum]
      simp [sparseRowLinearCombinationTerms]
  | cons t ts ih =>
      change
        sumRangeFromZ 0 K
            (fun m =>
              a m *
                ((if t.xPow = x then t.coeff * q m t.yPow else 0) +
                  sparseRowLinearCombinationTerms ts x (q m))) =
          (if t.xPow = x then
              t.coeff * sumRangeFromZ 0 K (fun m => a m * q m t.yPow)
            else 0) +
            sparseRowLinearCombinationTerms ts x
              (fun y => sumRangeFromZ 0 K (fun m => a m * q m y))
      rw [sumRangeFromZ_zero_eq_finset_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rw [← sumRangeFromZ_zero_eq_finset_sum K
          (fun m => a m * sparseRowLinearCombinationTerms ts x (q m)),
        ih]
      by_cases hx : t.xPow = x
      · rw [if_pos hx]
        simp_rw [if_pos hx]
        have hterm :
            (∑ m ∈ Finset.range K, a m * (t.coeff * q m t.yPow)) =
              t.coeff * sumRangeFromZ 0 K (fun m => a m * q m t.yPow) := by
          rw [sumRangeFromZ_zero_eq_finset_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro m _hm
          ring
        rw [hterm]
      · rw [if_neg hx]
        simp [hx]

theorem truncCoeffAt_mulQPullback41Compressed_linearCombinationForXPowList
    {N n x : ℕ} (Prow : List ℤ) (Q : List (List ℤ))
    (terms : List SparseBivarTerm) (hn : n < N) :
    truncCoeffAt
        (mulQPullback41CompressedTruncCoeffList N Prow
          (linearCombinationForXPowList N x Q terms)) n =
      sparseRowLinearCombinationTerms terms x
        (fun y =>
          truncCoeffAt
            (mulQPullback41CompressedTruncCoeffList N Prow
              (Q.getD y (zeroTruncCoeffList N))) n) := by
  rw [mulQPullback41CompressedTruncCoeffList,
    truncCoeffAt_truncCoeffList_of_lt hn]
  calc
    sumRangeFromZ 0 (n / 41 + 1)
        (fun m =>
          truncCoeffAt Prow m *
            truncCoeffAt (linearCombinationForXPowList N x Q terms)
              (n - 41 * m))
        =
      sumRangeFromZ 0 (n / 41 + 1)
        (fun m =>
          truncCoeffAt Prow m *
            sparseRowLinearCombinationTerms terms x
              (fun y =>
                truncCoeffAt (Q.getD y (zeroTruncCoeffList N))
                  (n - 41 * m))) := by
        rw [sumRangeFromZ_eq_finset_sum, sumRangeFromZ_eq_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro m _hm
        have hidx : n - 41 * (0 + m) < N := by omega
        rw [linearCombinationForXPowList,
          truncCoeffAt_truncCoeffList_of_lt hidx]
    _ =
      sparseRowLinearCombinationTerms terms x
        (fun y =>
          sumRangeFromZ 0 (n / 41 + 1)
            (fun m =>
              truncCoeffAt Prow m *
                truncCoeffAt (Q.getD y (zeroTruncCoeffList N))
                  (n - 41 * m))) := by
        exact sparseRowLinearCombinationTerms_sumRangeFromZ terms x
          (n / 41 + 1) (fun m => truncCoeffAt Prow m)
          (fun m y =>
            truncCoeffAt (Q.getD y (zeroTruncCoeffList N))
              (n - 41 * m))
    _ =
      sparseRowLinearCombinationTerms terms x
        (fun y =>
          truncCoeffAt
            (mulQPullback41CompressedTruncCoeffList N Prow
              (Q.getD y (zeroTruncCoeffList N))) n) := by
        apply sparseRowLinearCombinationTerms_congr
        intro y
        rw [mulQPullback41CompressedTruncCoeffList,
          truncCoeffAt_truncCoeffList_of_lt hn]

theorem truncCoeffAt_evalSparseCompressedMatrix_fold_range'
    {N M n start len : ℕ} (P Q : List (List ℤ))
    (coeffs : Array (Array ℤ)) (out : List ℤ)
    (hn : n < N) :
    truncCoeffAt
        ((List.range' start len 1).foldl
          (evalSparseCompressedMatrixStep N M P Q coeffs) out) n =
      truncCoeffAt out n +
        sumRangeFromZ start len
          (fun x =>
            truncCoeffAt
              (mulQPullback41CompressedTruncCoeffList N
                (P.getD x (zeroTruncCoeffList M))
                (linearCombinationFromCoeffMatrixList N x Q coeffs)) n) := by
  induction len generalizing start out with
  | zero =>
      simp [sumRangeFromZ]
  | succ len ih =>
      rw [List.range'_succ, List.foldl_cons,
        ih (start := start + 1)
          (out := evalSparseCompressedMatrixStep N M P Q coeffs out start)]
      rw [evalSparseCompressedMatrixStep,
        truncCoeffAt_addTruncCoeffList_of_lt _ _ hn, sumRangeFromZ]
      ring

theorem truncCoeffAt_evalSparseCompressedMatrixFromProductTablesTrunc_phi41Sparse
    {N M n : ℕ} (P Q : List (List ℤ)) (hn : n < N) :
    truncCoeffAt
        (evalSparseCompressedMatrixFromProductTablesTrunc N M P Q
          phi41SparseCoeffMatrixArray) n =
      sparseTermLinearCombinationTerms phi41SparseTerms
        (fun x y =>
          truncCoeffAt
            (mulQPullback41CompressedTruncCoeffList N
              (P.getD x (zeroTruncCoeffList M))
              (Q.getD y (zeroTruncCoeffList N))) n) := by
  unfold evalSparseCompressedMatrixFromProductTablesTrunc
  rw [show List.range 43 = List.range' 0 43 1 by rfl]
  rw [truncCoeffAt_evalSparseCompressedMatrix_fold_range'
    (P := P) (Q := Q) (coeffs := phi41SparseCoeffMatrixArray)
    (out := zeroTruncCoeffList N) hn]
  rw [zeroTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]
  simp only [zero_add]
  calc
    sumRangeFromZ 0 43
        (fun x =>
          truncCoeffAt
            (mulQPullback41CompressedTruncCoeffList N
              (P.getD x (zeroTruncCoeffList M))
              (linearCombinationFromCoeffMatrixList N x Q
                phi41SparseCoeffMatrixArray)) n)
        =
      sumRangeFromZ 0 43
        (fun x =>
          sparseRowLinearCombinationTerms phi41SparseTerms x
            (fun y =>
              truncCoeffAt
                (mulQPullback41CompressedTruncCoeffList N
                  (P.getD x (zeroTruncCoeffList M))
                  (Q.getD y (zeroTruncCoeffList N))) n)) := by
        rw [sumRangeFromZ_zero_eq_finset_sum,
          sumRangeFromZ_zero_eq_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro x hxmem
        have hx : x < 43 := Finset.mem_range.mp hxmem
        calc
          truncCoeffAt
              (mulQPullback41CompressedTruncCoeffList N
                (P.getD x (zeroTruncCoeffList M))
                (linearCombinationFromCoeffMatrixList N x Q
                  phi41SparseCoeffMatrixArray)) n =
            truncCoeffAt
              (mulQPullback41CompressedTruncCoeffList N
                (P.getD x (zeroTruncCoeffList M))
                (linearCombinationForXPowList N x Q phi41SparseTerms)) n := by
              unfold mulQPullback41CompressedTruncCoeffList
              rw [truncCoeffAt_truncCoeffList_of_lt hn,
                truncCoeffAt_truncCoeffList_of_lt hn]
              rw [sumRangeFromZ_eq_finset_sum,
                sumRangeFromZ_eq_finset_sum]
              refine Finset.sum_congr rfl ?_
              intro m _hm
              have hidx : n - 41 * (0 + m) < N := by omega
              rw [truncCoeffAt_linearCombinationFromCoeffMatrixList_eq_forXPowList
                (Q := Q) (x := x) hx hidx]
          _ =
            sparseRowLinearCombinationTerms phi41SparseTerms x
              (fun y =>
                truncCoeffAt
                  (mulQPullback41CompressedTruncCoeffList N
                    (P.getD x (zeroTruncCoeffList M))
                    (Q.getD y (zeroTruncCoeffList N))) n) := by
              exact
                truncCoeffAt_mulQPullback41Compressed_linearCombinationForXPowList
                  (N := N) (n := n) (x := x)
                  (P.getD x (zeroTruncCoeffList M)) Q phi41SparseTerms hn
    _ =
      sparseTermLinearCombinationTerms phi41SparseTerms
        (fun x y =>
          truncCoeffAt
            (mulQPullback41CompressedTruncCoeffList N
              (P.getD x (zeroTruncCoeffList M))
              (Q.getD y (zeroTruncCoeffList N))) n) := by
        exact sum_sparseRowLinearCombinationTerms_eq_sparseTermLinearCombinationTerms
          phi41SparseTerms
          (fun x y =>
            truncCoeffAt
              (mulQPullback41CompressedTruncCoeffList N
                (P.getD x (zeroTruncCoeffList M))
                (Q.getD y (zeroTruncCoeffList N))) n)
          (by
            intro t ht
            have hdeg := phi41SparseTerms_degree_le_42 t ht
            omega)

theorem truncCoeffAt_phi41Level41CoeffListCompressedMatrix_eq_sparse
    {N n : ℕ} (hn : n < N) :
    truncCoeffAt (phi41Level41CoeffListCompressedMatrix N) n =
      truncCoeffAt (phi41Level41CoeffListCompressedSparse N) n := by
  unfold phi41Level41CoeffListCompressedMatrix
    phi41Level41CoeffListCompressedSparse
  let M := (N + 40) / 41
  let E := E4TruncCoeffList N
  let D := deltaEulerTruncCoeffList N
  let C := powTruncCoeffList N E 3
  let Esmall := E4TruncCoeffList M
  let Dsmall := deltaEulerTruncCoeffList M
  let Csmall := powTruncCoeffList M Esmall 3
  let CPow := powTruncCoeffTable N C 42
  let DPow := powTruncCoeffTable N D 42
  let CSmallPow := powTruncCoeffTable M Csmall 42
  let DSmallPow := powTruncCoeffTable M Dsmall 42
  let PCompressed := phi41TermProductTable M CSmallPow DSmallPow
  let Q := phi41TermProductTable N CPow DPow
  calc
    truncCoeffAt
        (evalSparseCompressedMatrixFromProductTablesTrunc N M PCompressed Q
          phi41SparseCoeffMatrixArray) n =
      sparseTermLinearCombinationTerms phi41SparseTerms
        (fun x y =>
          truncCoeffAt
            (mulQPullback41CompressedTruncCoeffList N
              (PCompressed.getD x (zeroTruncCoeffList M))
              (Q.getD y (zeroTruncCoeffList N))) n) := by
        exact
          truncCoeffAt_evalSparseCompressedMatrixFromProductTablesTrunc_phi41Sparse
            (N := N) (M := M) (n := n) PCompressed Q hn
    _ =
      truncCoeffAt
        (evalSparseCompressedFromProductTablesTrunc N M PCompressed Q
          phi41SparseTerms) n := by
        rw [truncCoeffAt_evalSparseCompressedFromProductTablesTrunc
          (P := PCompressed) (Q := Q) (terms := phi41SparseTerms) hn]

/-- Coefficientwise agreement for a table of truncated series. -/
def ListArrayTableEq (N maxIdx : ℕ) (xs : List (List ℤ)) (ys : Array (Array ℤ)) : Prop :=
  ∀ k, k ≤ maxIdx →
    ListArrayEq N (xs.getD k (zeroTruncCoeffList N))
      (ys.getD k (zeroTruncCoeffArray N))

theorem ListArrayTableEq.phi41LevelOneDenseRows_of_recurrence
    (N : ℕ)
    (hzero : ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ, n < N → n < 42 - j →
      truncCoeffAt ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)) n = 0)
    (hone : ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ, n < N → n = 42 - j →
      truncCoeffAt ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)) n = 1)
    (hrec : ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ, n < N → 42 - j < n →
      truncCoeffAt ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)) n =
        (sumRangeFromZ 1 n (fun a =>
          (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
              (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
            truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
              truncCoeffAt
                ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N))
                (n - a))) /
          (((n - (42 - j) : ℕ) : ℤ))) :
    ListArrayTableEq N 42
      (phi41LevelOneDenseRowsList N) (phi41QRecurrenceRowsArray N) := by
  intro j hj
  rw [phi41QRecurrenceRowsArray_getD_of_le N hj]
  exact ListArrayEq.of_phi41QRecurrence
    (N := N) (j := j)
    (rowL := (phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N))
    (E4L := E4TruncCoeffList N) (E6L := E6TruncCoeffList N)
    (E2E4L := E2E4TruncCoeffList N)
    (E4A := E4TruncCoeffArray N) (E6A := E6TruncCoeffArray N)
    (E2E4A := E2E4TruncCoeffArray N)
    (ListArrayEq.E4 N) (ListArrayEq.E6 N) (ListArrayEq.E2E4 N)
    (hzero j hj) (hone j hj) (hrec j hj)

theorem ListArrayEq.powTruncCoeffTableAux {N : ℕ}
    {baseL currentL : List ℤ} {baseA currentA : Array ℤ}
    (hbase : ListArrayEq N baseL baseA)
    (hcurrent : ListArrayEq N currentL currentA) :
    ∀ (maxPow k : ℕ), k ≤ maxPow →
      ListArrayEq N
        ((powTruncCoeffTableAux N baseL currentL maxPow).getD k
          (zeroTruncCoeffList N))
        ((powTruncCoeffArrayTableAux N baseA currentA maxPow).getD k
          (zeroTruncCoeffArray N))
  | 0, k, hk => by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simpa [powTruncCoeffTableAux, powTruncCoeffArrayTableAux] using hcurrent
  | maxPow + 1, k, hk => by
      cases k with
      | zero =>
          simpa [powTruncCoeffTableAux, powTruncCoeffArrayTableAux] using hcurrent
      | succ k =>
          have hk' : k ≤ maxPow := Nat.succ_le_succ_iff.mp hk
          simpa [powTruncCoeffTableAux, powTruncCoeffArrayTableAux] using
            ListArrayEq.powTruncCoeffTableAux hbase (hcurrent.mul hbase) maxPow k hk'

theorem ListArrayTableEq.powTable {N maxPow : ℕ}
    {baseL : List ℤ} {baseA : Array ℤ}
    (hbase : ListArrayEq N baseL baseA) :
    ListArrayTableEq N maxPow
      (powTruncCoeffTable N baseL maxPow)
      (powTruncCoeffArrayTable N baseA maxPow) := by
  intro k hk
  unfold powTruncCoeffTable powTruncCoeffArrayTable
  rw [Array.getD_toArray]
  exact ListArrayEq.powTruncCoeffTableAux hbase (ListArrayEq.const N 1) maxPow k hk

/-- Coefficientwise modular agreement for a table of truncated series. -/
def TruncCoeffArrayTableModEq
    (N maxIdx p : ℕ) (xs ys : Array (Array ℤ)) : Prop :=
  ∀ k, k ≤ maxIdx →
    TruncCoeffArrayModEq N p
      (xs.getD k (zeroTruncCoeffArray N))
      (ys.getD k (zeroTruncCoeffArray N))

theorem TruncCoeffArrayTableModEq.refl (N maxIdx p : ℕ) (xs : Array (Array ℤ)) :
    TruncCoeffArrayTableModEq N maxIdx p xs xs := by
  intro k hk
  exact TruncCoeffArrayModEq.refl N p _

theorem TruncCoeffArrayTableModEq.of_modEqFirstChunked
    {N maxIdx p chunkSize numChunks : ℕ}
    {xs ys : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunked : truncCoeffArrayTableModEqFirstChunked
      N maxIdx p chunkSize numChunks xs ys = true) :
    TruncCoeffArrayTableModEq N maxIdx p xs ys := by
  intro k hk
  unfold truncCoeffArrayTableModEqFirstChunked at hchunked
  have hkmem : k ∈ List.range (maxIdx + 1) := List.mem_range.mpr (by omega)
  exact TruncCoeffArrayModEq.of_modEqFirstChunked hcover
    (List.all_eq_true.mp hchunked k hkmem)

theorem TruncCoeffArrayModEq.powTruncCoeffArrayTableAux {N p : ℕ}
    {baseA currentA baseB currentB : Array ℤ}
    (hbase : TruncCoeffArrayModEq N p baseA baseB)
    (hcurrent : TruncCoeffArrayModEq N p currentA currentB) :
    ∀ (maxPow k : ℕ), k ≤ maxPow →
      TruncCoeffArrayModEq N p
        ((powTruncCoeffArrayTableAux N baseA currentA maxPow).getD k
          (zeroTruncCoeffArray N))
        ((powTruncCoeffArrayTableAux N baseB currentB maxPow).getD k
          (zeroTruncCoeffArray N))
  | 0, k, hk => by
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simpa [powTruncCoeffArrayTableAux] using hcurrent
  | maxPow + 1, k, hk => by
      cases k with
      | zero =>
          simpa [powTruncCoeffArrayTableAux] using hcurrent
      | succ k =>
          have hk' : k ≤ maxPow := Nat.succ_le_succ_iff.mp hk
          simpa [powTruncCoeffArrayTableAux] using
            TruncCoeffArrayModEq.powTruncCoeffArrayTableAux
              hbase (hcurrent.mul hbase) maxPow k hk'

theorem TruncCoeffArrayTableModEq.powTable {N maxPow p : ℕ}
    {baseA baseB : Array ℤ}
    (hbase : TruncCoeffArrayModEq N p baseA baseB) :
    TruncCoeffArrayTableModEq N maxPow p
      (powTruncCoeffArrayTable N baseA maxPow)
      (powTruncCoeffArrayTable N baseB maxPow) := by
  intro k hk
  unfold powTruncCoeffArrayTable
  rw [Array.getD_toArray, Array.getD_toArray]
  exact TruncCoeffArrayModEq.powTruncCoeffArrayTableAux
    hbase (TruncCoeffArrayModEq.const N p 1) maxPow k hk

theorem phi41TermProductArrayTable_getD_of_le
    (N : ℕ) (A B : Array (Array ℤ)) {x : ℕ} (hx : x ≤ 42) :
    (phi41TermProductArrayTable N A B).getD x (zeroTruncCoeffArray N) =
      mulTruncCoeffArray N
        (A.getD x (zeroTruncCoeffArray N))
        (B.getD (42 - x) (zeroTruncCoeffArray N)) := by
  have hxlt : x < 43 := by omega
  unfold phi41TermProductArrayTable
  rw [Array.getD_toArray]
  rw [List.getD_eq_getElem (l := (List.range 43).map
      (fun x => mulTruncCoeffArray N
        (A.getD x (zeroTruncCoeffArray N))
        (B.getD (42 - x) (zeroTruncCoeffArray N))))
      (d := zeroTruncCoeffArray N) (by simp [hxlt])]
  simp

theorem ListArrayTableEq.phi41TermProductTable {N : ℕ}
    {AL BL : List (List ℤ)} {AA BA : Array (Array ℤ)}
    (hA : ListArrayTableEq N 42 AL AA)
    (hB : ListArrayTableEq N 42 BL BA) :
    ListArrayTableEq N 42
      (phi41TermProductTable N AL BL)
      (phi41TermProductArrayTable N AA BA) := by
  intro x hx
  rw [phi41TermProductTable_getD_of_le N AL BL hx,
    phi41TermProductArrayTable_getD_of_le N AA BA hx]
  exact (hA x hx).mul (hB (42 - x) (Nat.sub_le 42 x))

theorem TruncCoeffArrayTableModEq.phi41TermProductArrayTable {N p : ℕ}
    {A B A' B' : Array (Array ℤ)}
    (hA : TruncCoeffArrayTableModEq N 42 p A A')
    (hB : TruncCoeffArrayTableModEq N 42 p B B') :
    TruncCoeffArrayTableModEq N 42 p
      (phi41TermProductArrayTable N A B)
      (phi41TermProductArrayTable N A' B') := by
  intro x hx
  rw [phi41TermProductArrayTable_getD_of_le N A B hx,
    phi41TermProductArrayTable_getD_of_le N A' B' hx]
  exact (hA x hx).mul (hB (42 - x) (Nat.sub_le 42 x))

theorem truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt {N n : ℕ} {f : ℕ → ℤ}
    (hn : n < N) :
    truncCoeffArrayAt (truncCoeffArrayOfFn N f) n = f n := by
  simpa [truncCoeffAt_truncCoeffList_of_lt hn] using
    (ListArrayEq.ofFn N f n hn).symm

theorem ListArrayEq.linearCombinationFromCoeffMatrix {N x : ℕ}
    {Q : List (List ℤ)} {QA : Array (Array ℤ)} (coeffs : Array (Array ℤ))
    (hQ : ListArrayTableEq N 42 Q QA) :
    ListArrayEq N
      (linearCombinationFromCoeffMatrixList N x Q coeffs)
      (linearCombinationFromCoeffMatrixArray N x QA coeffs) := by
  intro n hn
  unfold linearCombinationFromCoeffMatrixList linearCombinationFromCoeffMatrixArray
  rw [truncCoeffAt_truncCoeffList_of_lt hn,
    truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn]
  let row := coeffs.getD x (Array.replicate 43 0)
  calc
    sumRangeFromZ 0 43
        (fun y => row.getD y 0 *
          truncCoeffAt (Q.getD y (zeroTruncCoeffList N)) n)
        =
      sumRangeFromZ 0 43
        (fun y => row.getD y 0 *
          truncCoeffArrayAt (QA.getD y (zeroTruncCoeffArray N)) n) := by
        rw [sumRangeFromZ_eq_finset_sum, sumRangeFromZ_eq_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro y hy
        have hy42 : y ≤ 42 := by
          have : y < 43 := Finset.mem_range.mp hy
          omega
        have hqy := hQ (0 + y) (by omega) n hn
        simpa [Nat.zero_add] using
          congrArg (fun z => row.getD (0 + y) 0 * z) hqy
    _ =
      (Id.run do
        let mut s : ℤ := 0
        for y in [0:43] do
          s := s + row.getD y 0 *
            truncCoeffArrayAt (QA.getD y (zeroTruncCoeffArray N)) n
        return s) := by
        exact (forIn_range_add_eq_sumRangeFromZ 43
          (fun y => row.getD y 0 *
            truncCoeffArrayAt (QA.getD y (zeroTruncCoeffArray N)) n)).symm

theorem TruncCoeffArrayModEq.linearCombinationFromCoeffMatrix {N x p : ℕ}
    {Q Q' : Array (Array ℤ)} (coeffs : Array (Array ℤ))
    (hQ : TruncCoeffArrayTableModEq N 42 p Q Q') :
    TruncCoeffArrayModEq N p
      (linearCombinationFromCoeffMatrixArray N x Q coeffs)
      (linearCombinationFromCoeffMatrixArray N x Q' coeffs) := by
  intro n hn
  unfold linearCombinationFromCoeffMatrixArray
  rw [truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn,
    truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn]
  let row := coeffs.getD x (Array.replicate 43 0)
  rw [forIn_range_add_eq_sumRangeFromZ]
  rw [forIn_range_add_eq_sumRangeFromZ]
  apply sumRangeFromZ_modEq
  intro y _hy1 hy2
  have hy42 : y ≤ 42 := by omega
  exact Int.ModEq.mul_left (row.getD y 0) (hQ y hy42 n hn)

theorem ListArrayEq.mulQPullback41Compressed {N M : ℕ}
    {compressed full : List ℤ} {compressedA fullA : Array ℤ}
    (hM : (N + 40) / 41 ≤ M)
    (hcompressed : ListArrayEq M compressed compressedA)
    (hfull : ListArrayEq N full fullA) :
    ListArrayEq N
      (mulQPullback41CompressedTruncCoeffList N compressed full)
      (mulQPullback41CompressedTruncCoeffArray N compressedA fullA) := by
  intro n hn
  rw [mulQPullback41CompressedTruncCoeffList,
    truncCoeffAt_truncCoeffList_of_lt hn]
  unfold mulQPullback41CompressedTruncCoeffArray
  rw [truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn]
  calc
    sumRangeFromZ 0 (n / 41 + 1)
        (fun m => truncCoeffAt compressed m * truncCoeffAt full (n - 41 * m))
        =
      sumRangeFromZ 0 (n / 41 + 1)
        (fun m => truncCoeffArrayAt compressedA m * truncCoeffArrayAt fullA (n - 41 * m)) := by
        rw [sumRangeFromZ_eq_finset_sum, sumRangeFromZ_eq_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro m hm
        have hm_lt : m < n / 41 + 1 := Finset.mem_range.mp hm
        have hmM : m < M := by
          have hm_le : m ≤ n / 41 := by omega
          have hnM' : n / 41 < (N + 40) / 41 := by omega
          have hnM : n / 41 < M := lt_of_lt_of_le hnM' hM
          omega
        have hidxN : n - 41 * m < N := by omega
        have hcm := hcompressed (0 + m) (by simpa [Nat.zero_add] using hmM)
        have hfm := hfull (n - 41 * (0 + m)) (by simpa [Nat.zero_add] using hidxN)
        simpa [Nat.zero_add] using
          congrArg₂ (fun a b => a * b) hcm hfm
    _ =
      (Id.run do
        let mut s : ℤ := 0
        for m in [0:n / 41 + 1] do
          s := s + compressedA.getD m 0 * fullA.getD (n - 41 * m) 0
        return s) := by
        exact (forIn_range_add_eq_sumRangeFromZ (n / 41 + 1)
          (fun m => truncCoeffArrayAt compressedA m *
            truncCoeffArrayAt fullA (n - 41 * m))).symm

theorem TruncCoeffArrayModEq.mulQPullback41Compressed {N M p : ℕ}
    {compressed compressed' full full' : Array ℤ}
    (hM : (N + 40) / 41 ≤ M)
    (hcompressed : TruncCoeffArrayModEq M p compressed compressed')
    (hfull : TruncCoeffArrayModEq N p full full') :
    TruncCoeffArrayModEq N p
      (mulQPullback41CompressedTruncCoeffArray N compressed full)
      (mulQPullback41CompressedTruncCoeffArray N compressed' full') := by
  intro n hn
  unfold mulQPullback41CompressedTruncCoeffArray
  rw [truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn,
    truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn]
  rw [forIn_range_add_eq_sumRangeFromZ]
  rw [forIn_range_add_eq_sumRangeFromZ]
  apply sumRangeFromZ_modEq
  intro m _hm1 hm2
  have hm_lt : m < n / 41 + 1 := by omega
  have hmM : m < M := by
    have hm_le : m ≤ n / 41 := by omega
    have hnM' : n / 41 < (N + 40) / 41 := by omega
    have hnM : n / 41 < M := lt_of_lt_of_le hnM' hM
    omega
  have hidxN : n - 41 * m < N := by omega
  exact (hcompressed m hmM).mul (hfull (n - 41 * m) hidxN)

theorem truncCoeffArrayAt_linearCombinationFromCoeffMatrixArray
    {N x n : ℕ} {Q coeffs : Array (Array ℤ)} (hn : n < N) :
    truncCoeffArrayAt
        (linearCombinationFromCoeffMatrixArray N x Q coeffs) n =
      sumRangeFromZ 0 43 (fun y =>
        (coeffs.getD x (Array.replicate 43 0)).getD y 0 *
          truncCoeffArrayAt (Q.getD y (zeroTruncCoeffArray N)) n) := by
  unfold linearCombinationFromCoeffMatrixArray
  rw [truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn]
  exact forIn_range_add_eq_sumRangeFromZ 43
    (fun y =>
      (coeffs.getD x (Array.replicate 43 0)).getD y 0 *
        truncCoeffArrayAt (Q.getD y (zeroTruncCoeffArray N)) n)

theorem truncCoeffArrayAt_mulQPullback41CompressedTruncCoeffArray
    {N n : ℕ} {compressed full : Array ℤ} (hn : n < N) :
    truncCoeffArrayAt
        (mulQPullback41CompressedTruncCoeffArray N compressed full) n =
      sumRangeFromZ 0 (n / 41 + 1) (fun m =>
        truncCoeffArrayAt compressed m *
          truncCoeffArrayAt full (n - 41 * m)) := by
  unfold mulQPullback41CompressedTruncCoeffArray
  rw [truncCoeffArrayAt_truncCoeffArrayOfFn_of_lt hn]
  exact forIn_range_add_eq_sumRangeFromZ (n / 41 + 1)
    (fun m =>
      truncCoeffArrayAt compressed m *
        truncCoeffArrayAt full (n - 41 * m))

def phi41QPartTableFromRowsCoeff
    (N : ℕ) (Q : Array (Array ℤ)) (x n : ℕ) : ℤ :=
  sumRangeFromZ 0 43 (fun y =>
    (phi41SparseCoeffMatrixArray.getD x (Array.replicate 43 0)).getD y 0 *
      truncCoeffArrayAt (Q.getD y (zeroTruncCoeffArray N)) n)

def phi41QPartTableFromRowsModEqChunk
    (N p start len : ℕ)
    (Q QParts : Array (Array ℤ)) : Bool :=
  (List.range 43).all (fun x =>
    (List.range len).all (fun offset =>
      let n := start + offset
      if _ : n < N then
        intCoeffModEq p
          (phi41QPartTableFromRowsCoeff N Q x n)
          (truncCoeffArrayAt
            (QParts.getD x (zeroTruncCoeffArray N)) n)
      else
        true))

def phi41QPartTableFromRowsModEqChunked
    (N p chunkSize numChunks : ℕ)
    (Q QParts : Array (Array ℤ)) : Bool :=
  (List.range numChunks).all (fun c =>
    phi41QPartTableFromRowsModEqChunk
      N p (c * chunkSize) chunkSize Q QParts)

def phi41QPartTableFromRowsModEqRowChunk
    (N p x start len : ℕ)
    (Q QParts : Array (Array ℤ)) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < N then
      intCoeffModEq p
        (phi41QPartTableFromRowsCoeff N Q x n)
        (truncCoeffArrayAt
          (QParts.getD x (zeroTruncCoeffArray N)) n)
    else
      true)

def phi41QPartTableFromRowsModEqRowChunked
    (N p x chunkSize numChunks : ℕ)
    (Q QParts : Array (Array ℤ)) : Bool :=
  (List.range numChunks).all (fun c =>
    phi41QPartTableFromRowsModEqRowChunk
      N p x (c * chunkSize) chunkSize Q QParts)

theorem phi41QPartTableFromRowsModEqRowChunked_of_chunks
    {N p x chunkSize numChunks : ℕ}
    {Q QParts : Array (Array ℤ)}
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41QPartTableFromRowsModEqRowChunk
        N p x (c * chunkSize) chunkSize Q QParts = true) :
    phi41QPartTableFromRowsModEqRowChunked
      N p x chunkSize numChunks Q QParts = true := by
  unfold phi41QPartTableFromRowsModEqRowChunked
  apply List.all_eq_true.mpr
  intro c hcmem
  exact hchunks c (List.mem_range.mp hcmem)

theorem phi41QPartTableFromRowsModEqRowChunk_of_entries
    {N p x start len : ℕ}
    {Q QParts : Array (Array ℤ)}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < N then
         intCoeffModEq p
           (phi41QPartTableFromRowsCoeff N Q x n)
           (truncCoeffArrayAt
             (QParts.getD x (zeroTruncCoeffArray N)) n)
       else
         true) = true) :
    phi41QPartTableFromRowsModEqRowChunk
      N p x start len Q QParts = true := by
  unfold phi41QPartTableFromRowsModEqRowChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem TruncCoeffArrayModEq.phi41QPartRow_of_prefix
    {N p x : ℕ} {QPart Prefix : Array ℤ}
    (QRows : Array (Array ℤ))
    (hzero : ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix (0 * N + n) ≡ 0 [ZMOD (p : ℤ)])
    (hstep : ∀ y : ℕ, y < 43 → ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix ((y + 1) * N + n) ≡
        truncCoeffArrayAt Prefix (y * N + n) +
          (phi41SparseCoeffMatrixArray.getD x
            (Array.replicate 43 0)).getD y 0 *
            truncCoeffArrayAt
              (QRows.getD y (zeroTruncCoeffArray N)) n
        [ZMOD (p : ℤ)])
    (hfinal : ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix (43 * N + n) ≡
        truncCoeffArrayAt QPart n [ZMOD (p : ℤ)]) :
    TruncCoeffArrayModEq N p
      (linearCombinationFromCoeffMatrixArray
        N x QRows phi41SparseCoeffMatrixArray)
      QPart := by
  intro n hn
  rw [truncCoeffArrayAt_linearCombinationFromCoeffMatrixArray hn]
  have hprefix :
      sumRangeFromZ 0 43 (fun y =>
        (phi41SparseCoeffMatrixArray.getD x
          (Array.replicate 43 0)).getD y 0 *
          truncCoeffArrayAt
            (QRows.getD y (zeroTruncCoeffArray N)) n) ≡
        truncCoeffArrayAt Prefix (43 * N + n) [ZMOD (p : ℤ)] := by
    apply sumRangeFromZ_zero_modEq_prefix
      (pref := fun y => truncCoeffArrayAt Prefix (y * N + n))
    · simpa using hzero n hn
    · intro y hy
      simpa using hstep y hy n hn
  exact hprefix.trans (hfinal n hn)

theorem TruncCoeffArrayTableModEq.phi41QPartTableFromRows_of_prefix
    {N p : ℕ} {QRows QParts : Array (Array ℤ)}
    (Prefixes : Array (Array ℤ))
    (hzero : ∀ x : ℕ, x ≤ 42 → ∀ n : ℕ, n < N →
      truncCoeffArrayAt
        (Prefixes.getD x (Array.replicate (44 * N) 0))
        (0 * N + n) ≡ 0 [ZMOD (p : ℤ)])
    (hstep : ∀ x : ℕ, x ≤ 42 → ∀ y : ℕ, y < 43 →
      ∀ n : ℕ, n < N →
      truncCoeffArrayAt
          (Prefixes.getD x (Array.replicate (44 * N) 0))
          ((y + 1) * N + n) ≡
        truncCoeffArrayAt
          (Prefixes.getD x (Array.replicate (44 * N) 0))
          (y * N + n) +
          (phi41SparseCoeffMatrixArray.getD x
            (Array.replicate 43 0)).getD y 0 *
            truncCoeffArrayAt
              (QRows.getD y (zeroTruncCoeffArray N)) n
        [ZMOD (p : ℤ)])
    (hfinal : ∀ x : ℕ, x ≤ 42 → ∀ n : ℕ, n < N →
      truncCoeffArrayAt
          (Prefixes.getD x (Array.replicate (44 * N) 0))
          (43 * N + n) ≡
        truncCoeffArrayAt
          (QParts.getD x (zeroTruncCoeffArray N)) n [ZMOD (p : ℤ)]) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41QPartTableFromRows N QRows) QParts := by
  intro x hx
  rw [phi41QPartTableFromRows_getD_of_le N QRows hx]
  exact TruncCoeffArrayModEq.phi41QPartRow_of_prefix QRows
    (hzero x hx) (hstep x hx) (hfinal x hx)

theorem TruncCoeffArrayTableModEq.of_phi41QPartTableFromRowsModEqChunked
    {N p chunkSize numChunks : ℕ}
    {Q QParts : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunked :
      phi41QPartTableFromRowsModEqChunked
        N p chunkSize numChunks Q QParts = true) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41QPartTableFromRows N Q) QParts := by
  intro x hx n hn
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
  unfold phi41QPartTableFromRowsModEqChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold phi41QPartTableFromRowsModEqChunk at hchunk
  have hxmem : x ∈ List.range 43 := List.mem_range.mpr (by omega)
  have hxrow := List.all_eq_true.mp hchunk x hxmem
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hxrow offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hentry_n :
      intCoeffModEq p
        (phi41QPartTableFromRowsCoeff N Q x n)
        (truncCoeffArrayAt
          (QParts.getD x (zeroTruncCoeffArray N)) n) = true := by
    simpa [hn_eq, hn] using hentry
  rw [phi41QPartTableFromRows_getD_of_le N Q hx]
  rw [truncCoeffArrayAt_linearCombinationFromCoeffMatrixArray hn]
  simpa [phi41QPartTableFromRowsCoeff] using
    int_modEq_of_intCoeffModEq hentry_n

theorem TruncCoeffArrayTableModEq.of_phi41QPartTableFromRowsModEqRows
    {N p chunkSize numChunks : ℕ}
    {Q QParts : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hrows : ∀ x : ℕ, x ≤ 42 →
      phi41QPartTableFromRowsModEqRowChunked
        N p x chunkSize numChunks Q QParts = true) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41QPartTableFromRows N Q) QParts := by
  intro x hx n hn
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
  have hchunked := hrows x hx
  unfold phi41QPartTableFromRowsModEqRowChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold phi41QPartTableFromRowsModEqRowChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hentry_n :
      intCoeffModEq p
        (phi41QPartTableFromRowsCoeff N Q x n)
        (truncCoeffArrayAt
          (QParts.getD x (zeroTruncCoeffArray N)) n) = true := by
    simpa [hn_eq, hn] using hentry
  rw [phi41QPartTableFromRows_getD_of_le N Q hx]
  rw [truncCoeffArrayAt_linearCombinationFromCoeffMatrixArray hn]
  simpa [phi41QPartTableFromRowsCoeff] using
    int_modEq_of_intCoeffModEq hentry_n

theorem TruncCoeffArrayTableModEq.of_phi41QPartTableFromRowsModEqRowChunks
    {N p chunkSize numChunks : ℕ}
    {Q QParts : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunks : ∀ x : ℕ, x ≤ 42 → ∀ c : ℕ, c < numChunks →
      phi41QPartTableFromRowsModEqRowChunk
        N p x (c * chunkSize) chunkSize Q QParts = true) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41QPartTableFromRows N Q) QParts :=
  TruncCoeffArrayTableModEq.of_phi41QPartTableFromRowsModEqRows
    hcover (by
      intro x hx
      exact phi41QPartTableFromRowsModEqRowChunked_of_chunks
        (hchunks x hx))

def phi41ContributionTableFromQPartsCoeff
    (N M : ℕ) (PCompressed QParts : Array (Array ℤ)) (x n : ℕ) : ℤ :=
  sumRangeFromZ 0 (n / 41 + 1) (fun m =>
    truncCoeffArrayAt
        (PCompressed.getD x (zeroTruncCoeffArray M)) m *
      truncCoeffArrayAt
        (QParts.getD x (zeroTruncCoeffArray N)) (n - 41 * m))

def phi41ContributionTableFromQPartsModEqChunk
    (N M p start len : ℕ)
    (PCompressed QParts Contributions : Array (Array ℤ)) : Bool :=
  (List.range 43).all (fun x =>
    (List.range len).all (fun offset =>
      let n := start + offset
      if _ : n < N then
        intCoeffModEq p
          (phi41ContributionTableFromQPartsCoeff
            N M PCompressed QParts x n)
          (truncCoeffArrayAt
            (Contributions.getD x (zeroTruncCoeffArray N)) n)
      else
        true))

def phi41ContributionTableFromQPartsModEqChunked
    (N M p chunkSize numChunks : ℕ)
    (PCompressed QParts Contributions : Array (Array ℤ)) : Bool :=
  (List.range numChunks).all (fun c =>
    phi41ContributionTableFromQPartsModEqChunk
      N M p (c * chunkSize) chunkSize PCompressed QParts Contributions)

def phi41ContributionTableFromQPartsModEqRowChunk
    (N M p x start len : ℕ)
    (PCompressed QParts Contributions : Array (Array ℤ)) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < N then
      intCoeffModEq p
        (phi41ContributionTableFromQPartsCoeff
          N M PCompressed QParts x n)
        (truncCoeffArrayAt
          (Contributions.getD x (zeroTruncCoeffArray N)) n)
    else
      true)

def phi41ContributionTableFromQPartsModEqRowChunked
    (N M p x chunkSize numChunks : ℕ)
    (PCompressed QParts Contributions : Array (Array ℤ)) : Bool :=
  (List.range numChunks).all (fun c =>
    phi41ContributionTableFromQPartsModEqRowChunk
      N M p x (c * chunkSize) chunkSize
      PCompressed QParts Contributions)

theorem phi41ContributionTableFromQPartsModEqRowChunked_of_chunks
    {N M p x chunkSize numChunks : ℕ}
    {PCompressed QParts Contributions : Array (Array ℤ)}
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41ContributionTableFromQPartsModEqRowChunk
        N M p x (c * chunkSize) chunkSize
        PCompressed QParts Contributions = true) :
    phi41ContributionTableFromQPartsModEqRowChunked
      N M p x chunkSize numChunks
      PCompressed QParts Contributions = true := by
  unfold phi41ContributionTableFromQPartsModEqRowChunked
  apply List.all_eq_true.mpr
  intro c hcmem
  exact hchunks c (List.mem_range.mp hcmem)

theorem phi41ContributionTableFromQPartsModEqRowChunk_of_entries
    {N M p x start len : ℕ}
    {PCompressed QParts Contributions : Array (Array ℤ)}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < N then
         intCoeffModEq p
           (phi41ContributionTableFromQPartsCoeff
             N M PCompressed QParts x n)
           (truncCoeffArrayAt
             (Contributions.getD x (zeroTruncCoeffArray N)) n)
       else
         true) = true) :
    phi41ContributionTableFromQPartsModEqRowChunk
      N M p x start len PCompressed QParts Contributions = true := by
  unfold phi41ContributionTableFromQPartsModEqRowChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem TruncCoeffArrayModEq.phi41ContributionRow_of_prefix
    {N M p : ℕ}
    {PCompressed QPart Contribution Prefix : Array ℤ}
    (hM : (N + 40) / 41 ≤ M)
    (hzero : ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix (0 * N + n) ≡ 0 [ZMOD (p : ℤ)])
    (hstep : ∀ m : ℕ, m < M → ∀ n : ℕ, n < N →
      m < n / 41 + 1 →
      truncCoeffArrayAt Prefix ((m + 1) * N + n) ≡
        truncCoeffArrayAt Prefix (m * N + n) +
          truncCoeffArrayAt PCompressed m *
            truncCoeffArrayAt QPart (n - 41 * m)
        [ZMOD (p : ℤ)])
    (hfinal : ∀ n : ℕ, n < N →
      truncCoeffArrayAt Prefix ((n / 41 + 1) * N + n) ≡
        truncCoeffArrayAt Contribution n [ZMOD (p : ℤ)]) :
    TruncCoeffArrayModEq N p
      (mulQPullback41CompressedTruncCoeffArray N PCompressed QPart)
      Contribution := by
  intro n hn
  rw [truncCoeffArrayAt_mulQPullback41CompressedTruncCoeffArray hn]
  have hprefix :
      sumRangeFromZ 0 (n / 41 + 1) (fun m =>
        truncCoeffArrayAt PCompressed m *
          truncCoeffArrayAt QPart (n - 41 * m)) ≡
        truncCoeffArrayAt Prefix ((n / 41 + 1) * N + n)
        [ZMOD (p : ℤ)] := by
    apply sumRangeFromZ_zero_modEq_prefix
      (pref := fun m => truncCoeffArrayAt Prefix (m * N + n))
    · simpa using hzero n hn
    · intro m hm
      have hmM : m < M := by
        have hm_le : m ≤ n / 41 := by omega
        have hnM' : n / 41 < (N + 40) / 41 := by omega
        exact lt_of_lt_of_le (lt_of_le_of_lt hm_le hnM') hM
      simpa using hstep m hmM n hn hm
  exact hprefix.trans (hfinal n hn)

theorem TruncCoeffArrayTableModEq.phi41ContributionTableFromQParts_of_prefix
    {N M p : ℕ}
    {PCompressed QParts Contributions : Array (Array ℤ)}
    (Prefixes : Array (Array ℤ))
    (hM : (N + 40) / 41 ≤ M)
    (hzero : ∀ x : ℕ, x ≤ 42 → ∀ n : ℕ, n < N →
      truncCoeffArrayAt
        (Prefixes.getD x (Array.replicate ((M + 1) * N) 0))
        (0 * N + n) ≡ 0 [ZMOD (p : ℤ)])
    (hstep : ∀ x : ℕ, x ≤ 42 → ∀ m : ℕ, m < M →
      ∀ n : ℕ, n < N → m < n / 41 + 1 →
      truncCoeffArrayAt
          (Prefixes.getD x (Array.replicate ((M + 1) * N) 0))
          ((m + 1) * N + n) ≡
        truncCoeffArrayAt
          (Prefixes.getD x (Array.replicate ((M + 1) * N) 0))
          (m * N + n) +
          truncCoeffArrayAt
            (PCompressed.getD x (zeroTruncCoeffArray M)) m *
            truncCoeffArrayAt
              (QParts.getD x (zeroTruncCoeffArray N)) (n - 41 * m)
        [ZMOD (p : ℤ)])
    (hfinal : ∀ x : ℕ, x ≤ 42 → ∀ n : ℕ, n < N →
      truncCoeffArrayAt
          (Prefixes.getD x (Array.replicate ((M + 1) * N) 0))
          ((n / 41 + 1) * N + n) ≡
        truncCoeffArrayAt
          (Contributions.getD x (zeroTruncCoeffArray N)) n
        [ZMOD (p : ℤ)]) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41ContributionTableFromQParts N M PCompressed QParts)
      Contributions := by
  intro x hx
  rw [phi41ContributionTableFromQParts_getD_of_le
    N M PCompressed QParts hx]
  exact TruncCoeffArrayModEq.phi41ContributionRow_of_prefix
    hM (hzero x hx) (hstep x hx) (hfinal x hx)

theorem TruncCoeffArrayTableModEq.of_phi41ContributionTableFromQPartsModEqChunked
    {N M p chunkSize numChunks : ℕ}
    {PCompressed QParts Contributions : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunked :
      phi41ContributionTableFromQPartsModEqChunked
        N M p chunkSize numChunks PCompressed QParts Contributions = true) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41ContributionTableFromQParts N M PCompressed QParts)
      Contributions := by
  intro x hx n hn
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
  unfold phi41ContributionTableFromQPartsModEqChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold phi41ContributionTableFromQPartsModEqChunk at hchunk
  have hxmem : x ∈ List.range 43 := List.mem_range.mpr (by omega)
  have hxrow := List.all_eq_true.mp hchunk x hxmem
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hxrow offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hentry_n :
      intCoeffModEq p
        (phi41ContributionTableFromQPartsCoeff
          N M PCompressed QParts x n)
        (truncCoeffArrayAt
          (Contributions.getD x (zeroTruncCoeffArray N)) n) = true := by
    simpa [hn_eq, hn] using hentry
  rw [phi41ContributionTableFromQParts_getD_of_le
    N M PCompressed QParts hx]
  rw [truncCoeffArrayAt_mulQPullback41CompressedTruncCoeffArray hn]
  simpa [phi41ContributionTableFromQPartsCoeff] using
    int_modEq_of_intCoeffModEq hentry_n

theorem TruncCoeffArrayTableModEq.of_phi41ContributionTableFromQPartsModEqRows
    {N M p chunkSize numChunks : ℕ}
    {PCompressed QParts Contributions : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hrows : ∀ x : ℕ, x ≤ 42 →
      phi41ContributionTableFromQPartsModEqRowChunked
        N M p x chunkSize numChunks
        PCompressed QParts Contributions = true) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41ContributionTableFromQParts N M PCompressed QParts)
      Contributions := by
  intro x hx n hn
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
  have hchunked := hrows x hx
  unfold phi41ContributionTableFromQPartsModEqRowChunked at hchunked
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc_lt
  have hchunk := List.all_eq_true.mp hchunked c hcmem
  unfold phi41ContributionTableFromQPartsModEqRowChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize :=
    List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [c, offset]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hentry_n :
      intCoeffModEq p
        (phi41ContributionTableFromQPartsCoeff
          N M PCompressed QParts x n)
        (truncCoeffArrayAt
          (Contributions.getD x (zeroTruncCoeffArray N)) n) = true := by
    simpa [hn_eq, hn] using hentry
  rw [phi41ContributionTableFromQParts_getD_of_le
    N M PCompressed QParts hx]
  rw [truncCoeffArrayAt_mulQPullback41CompressedTruncCoeffArray hn]
  simpa [phi41ContributionTableFromQPartsCoeff] using
    int_modEq_of_intCoeffModEq hentry_n

theorem TruncCoeffArrayTableModEq.of_phi41ContributionTableFromQPartsModEqRowChunks
    {N M p chunkSize numChunks : ℕ}
    {PCompressed QParts Contributions : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunks : ∀ x : ℕ, x ≤ 42 → ∀ c : ℕ, c < numChunks →
      phi41ContributionTableFromQPartsModEqRowChunk
        N M p x (c * chunkSize) chunkSize
        PCompressed QParts Contributions = true) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41ContributionTableFromQParts N M PCompressed QParts)
      Contributions :=
  TruncCoeffArrayTableModEq.of_phi41ContributionTableFromQPartsModEqRows
    hcover (by
      intro x hx
      exact phi41ContributionTableFromQPartsModEqRowChunked_of_chunks
        (hchunks x hx))

theorem TruncCoeffArrayTableModEq.phi41ContributionTableFromQParts
    {N M p : ℕ} {PCompressed QPartsA QPartsB : Array (Array ℤ)}
    (hM : (N + 40) / 41 ≤ M)
    (hQParts : TruncCoeffArrayTableModEq N 42 p QPartsA QPartsB) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41ContributionTableFromQParts N M PCompressed QPartsA)
      (phi41ContributionTableFromQParts N M PCompressed QPartsB) := by
  intro x hx
  rw [phi41ContributionTableFromQParts_getD_of_le N M PCompressed QPartsA hx,
    phi41ContributionTableFromQParts_getD_of_le N M PCompressed QPartsB hx]
  exact TruncCoeffArrayModEq.mulQPullback41Compressed
    (N := N) (M := M) hM
    (TruncCoeffArrayModEq.refl M p _)
    (hQParts x hx)

theorem TruncCoeffArrayModEq.phi41FinalFromContributions_modEq
    {N p : ℕ} {ContributionsA ContributionsB : Array (Array ℤ)}
    (hContributions :
      TruncCoeffArrayTableModEq N 42 p ContributionsA ContributionsB) :
    TruncCoeffArrayModEq N p
      (phi41FinalFromContributions N ContributionsA)
      (phi41FinalFromContributions N ContributionsB) := by
  intro n hn
  rw [truncCoeffArrayAt_phi41FinalFromContributions hn,
    truncCoeffArrayAt_phi41FinalFromContributions hn]
  apply sumRangeFromZ_modEq
  intro x _hx0 hx43
  have hx : x ≤ 42 := by omega
  exact hContributions x hx n hn

theorem TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArrayFromRows_intermediate
    (N M p : ℕ) (PCompressed Q : Array (Array ℤ)) :
    TruncCoeffArrayModEq N p
      (phi41Level41RecurrenceCoeffArrayFromRows N M PCompressed Q)
      (phi41FinalFromContributions N
        (phi41ContributionTableFromQParts N M PCompressed
          (phi41QPartTableFromRows N Q))) := by
  intro n hn
  rw [truncCoeffArrayAt_phi41Level41RecurrenceCoeffArrayFromRows hn,
    truncCoeffArrayAt_phi41FinalFromContributions hn]
  unfold phi41Level41RecurrenceCoeffArrayFromRowsCoeff
  have hsum :
      sumRangeFromZ 0 43
          (fun x =>
            truncCoeffArrayAt
              (mulQPullback41CompressedTruncCoeffArray N
                (PCompressed.getD x (zeroTruncCoeffArray M))
                (linearCombinationFromCoeffMatrixArray N x Q
                  phi41SparseCoeffMatrixArray)) n) =
        sumRangeFromZ 0 43
          (fun x =>
            truncCoeffArrayAt
              ((phi41ContributionTableFromQParts N M PCompressed
                (phi41QPartTableFromRows N Q)).getD x
                  (zeroTruncCoeffArray N)) n) := by
    apply sumRangeFromZ_congr
    intro x _hx0 hx43
    have hx : x ≤ 42 := by omega
    rw [phi41ContributionTableFromQParts_getD_of_le
      N M PCompressed (phi41QPartTableFromRows N Q) hx]
    rw [phi41QPartTableFromRows_getD_of_le N Q hx]
  rw [hsum]

theorem TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArrayFromRows_of_intermediate
    {N M p : ℕ}
    {PCompressed Q QParts Contributions : Array (Array ℤ)}
    {Final : Array ℤ}
    (hM : (N + 40) / 41 ≤ M)
    (hQParts :
      TruncCoeffArrayTableModEq N 42 p
        (phi41QPartTableFromRows N Q) QParts)
    (hContributions :
      TruncCoeffArrayTableModEq N 42 p
        (phi41ContributionTableFromQParts N M PCompressed QParts)
        Contributions)
    (hFinal :
      TruncCoeffArrayModEq N p
        (phi41FinalFromContributions N Contributions) Final) :
    TruncCoeffArrayModEq N p
      (phi41Level41RecurrenceCoeffArrayFromRows N M PCompressed Q)
      Final := by
  have hqToContrib :
      TruncCoeffArrayTableModEq N 42 p
        (phi41ContributionTableFromQParts N M PCompressed
          (phi41QPartTableFromRows N Q))
        (phi41ContributionTableFromQParts N M PCompressed QParts) :=
    TruncCoeffArrayTableModEq.phi41ContributionTableFromQParts hM hQParts
  have hContrib :
      TruncCoeffArrayTableModEq N 42 p
        (phi41ContributionTableFromQParts N M PCompressed
          (phi41QPartTableFromRows N Q))
        Contributions := by
    intro x hx
    exact (hqToContrib x hx).trans (hContributions x hx)
  exact
    (TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArrayFromRows_intermediate
      N M p PCompressed Q).trans
      ((TruncCoeffArrayModEq.phi41FinalFromContributions_modEq hContrib).trans hFinal)

theorem ListArrayEq.evalSparseCompressedMatrixFromProductTables
    {N M : ℕ} {PCompressedL QL : List (List ℤ)}
    {PCompressedA QA : Array (Array ℤ)} (coeffs : Array (Array ℤ))
    (hM : (N + 40) / 41 ≤ M)
    (hP : ListArrayTableEq M 42 PCompressedL PCompressedA)
    (hQ : ListArrayTableEq N 42 QL QA) :
    ListArrayEq N
      (evalSparseCompressedMatrixFromProductTablesTrunc N M PCompressedL QL coeffs)
      ((List.range 43).foldl
        (fun out x =>
          let qPart := linearCombinationFromCoeffMatrixArray N x QA coeffs
          addTruncCoeffArray N out
            (mulQPullback41CompressedTruncCoeffArray N
              (PCompressedA.getD x (zeroTruncCoeffArray M)) qPart))
        (zeroTruncCoeffArray N)) := by
  let stepL : List ℤ → ℕ → List ℤ := fun out x =>
    let qPart := linearCombinationFromCoeffMatrixList N x QL coeffs
    addTruncCoeffList N out
      (mulQPullback41CompressedTruncCoeffList N
        (PCompressedL.getD x (zeroTruncCoeffList M)) qPart)
  let stepA : Array ℤ → ℕ → Array ℤ := fun out x =>
    let qPart := linearCombinationFromCoeffMatrixArray N x QA coeffs
    addTruncCoeffArray N out
      (mulQPullback41CompressedTruncCoeffArray N
        (PCompressedA.getD x (zeroTruncCoeffArray M)) qPart)
  have hstep : ∀ {outL outA : _} {x : ℕ}, x ≤ 42 →
      ListArrayEq N outL outA →
        ListArrayEq N (stepL outL x) (stepA outA x) := by
    intro outL outA x hx hout
    have hqPart :
        ListArrayEq N
          (linearCombinationFromCoeffMatrixList N x QL coeffs)
          (linearCombinationFromCoeffMatrixArray N x QA coeffs) :=
      ListArrayEq.linearCombinationFromCoeffMatrix coeffs hQ
    have hp := hP x hx
    have hmul :=
      ListArrayEq.mulQPullback41Compressed
        (N := N) (M := M) hM hp hqPart
    simpa [stepL, stepA] using hout.add hmul
  have hfold : ∀ (xs : List ℕ) (outL : List ℤ) (outA : Array ℤ),
      (∀ x ∈ xs, x ≤ 42) → ListArrayEq N outL outA →
        ListArrayEq N (xs.foldl stepL outL) (xs.foldl stepA outA) := by
    intro xs
    induction xs with
    | nil =>
        intro outL outA _ hout
        simpa using hout
    | cons x xs ih =>
        intro outL outA hxs hout
        have hx : x ≤ 42 := hxs x (by simp)
        have hxs' : ∀ y ∈ xs, y ≤ 42 := by
          intro y hy
          exact hxs y (by simp [hy])
        simpa [List.foldl] using ih (stepL outL x) (stepA outA x) hxs'
          (hstep hx hout)
  have hRange : ∀ x ∈ List.range 43, x ≤ 42 := by
    intro x hx
    have : x < 43 := List.mem_range.mp hx
    omega
  simpa [evalSparseCompressedMatrixFromProductTablesTrunc, stepL, stepA] using
    hfold (List.range 43) (zeroTruncCoeffList N) (zeroTruncCoeffArray N)
      hRange (ListArrayEq.zero N)

theorem TruncCoeffArrayModEq.evalSparseCompressedMatrixFromProductTables
    {N M p : ℕ} {PCompressedA PCompressedB QA QB : Array (Array ℤ)}
    (coeffs : Array (Array ℤ))
    (hM : (N + 40) / 41 ≤ M)
    (hP : TruncCoeffArrayTableModEq M 42 p PCompressedA PCompressedB)
    (hQ : TruncCoeffArrayTableModEq N 42 p QA QB) :
    TruncCoeffArrayModEq N p
      ((List.range 43).foldl
        (fun out x =>
          let qPart := linearCombinationFromCoeffMatrixArray N x QA coeffs
          addTruncCoeffArray N out
            (mulQPullback41CompressedTruncCoeffArray N
              (PCompressedA.getD x (zeroTruncCoeffArray M)) qPart))
        (zeroTruncCoeffArray N))
      ((List.range 43).foldl
        (fun out x =>
          let qPart := linearCombinationFromCoeffMatrixArray N x QB coeffs
          addTruncCoeffArray N out
            (mulQPullback41CompressedTruncCoeffArray N
              (PCompressedB.getD x (zeroTruncCoeffArray M)) qPart))
        (zeroTruncCoeffArray N)) := by
  let stepA : Array ℤ → ℕ → Array ℤ := fun out x =>
    let qPart := linearCombinationFromCoeffMatrixArray N x QA coeffs
    addTruncCoeffArray N out
      (mulQPullback41CompressedTruncCoeffArray N
        (PCompressedA.getD x (zeroTruncCoeffArray M)) qPart)
  let stepB : Array ℤ → ℕ → Array ℤ := fun out x =>
    let qPart := linearCombinationFromCoeffMatrixArray N x QB coeffs
    addTruncCoeffArray N out
      (mulQPullback41CompressedTruncCoeffArray N
        (PCompressedB.getD x (zeroTruncCoeffArray M)) qPart)
  have hstep : ∀ {outA outB : _} {x : ℕ}, x ≤ 42 →
      TruncCoeffArrayModEq N p outA outB →
        TruncCoeffArrayModEq N p (stepA outA x) (stepB outB x) := by
    intro outA outB x hx hout
    have hqPart :
        TruncCoeffArrayModEq N p
          (linearCombinationFromCoeffMatrixArray N x QA coeffs)
          (linearCombinationFromCoeffMatrixArray N x QB coeffs) :=
      TruncCoeffArrayModEq.linearCombinationFromCoeffMatrix coeffs hQ
    have hp := hP x hx
    have hmul :=
      TruncCoeffArrayModEq.mulQPullback41Compressed
        (N := N) (M := M) hM hp hqPart
    simpa [stepA, stepB] using hout.add hmul
  have hfold : ∀ (xs : List ℕ) (outA outB : Array ℤ),
      (∀ x ∈ xs, x ≤ 42) → TruncCoeffArrayModEq N p outA outB →
        TruncCoeffArrayModEq N p (xs.foldl stepA outA) (xs.foldl stepB outB) := by
    intro xs
    induction xs with
    | nil =>
        intro outA outB _ hout
        simpa using hout
    | cons x xs ih =>
        intro outA outB hxs hout
        have hx : x ≤ 42 := hxs x (by simp)
        have hxs' : ∀ y ∈ xs, y ≤ 42 := by
          intro y hy
          exact hxs y (by simp [hy])
        simpa [List.foldl] using ih (stepA outA x) (stepB outB x) hxs'
          (hstep hx hout)
  have hRange : ∀ x ∈ List.range 43, x ≤ 42 := by
    intro x hx
    have : x < 43 := List.mem_range.mp hx
    omega
  simpa [stepA, stepB] using
    hfold (List.range 43) (zeroTruncCoeffArray N) (zeroTruncCoeffArray N)
      hRange (TruncCoeffArrayModEq.zero N p)

theorem ListArrayEq.phi41Level41CoeffCompressedMatrix_of_recurrenceRows
    (N : ℕ)
    (hP :
      ListArrayTableEq ((N + 40) / 41) 42
        (phi41LevelOneDenseRowsList ((N + 40) / 41))
        (phi41QRecurrenceRowsArray ((N + 40) / 41)))
    (hQ :
      ListArrayTableEq N 42
        (phi41LevelOneDenseRowsList N)
        (phi41QRecurrenceRowsArray N)) :
    ListArrayEq N
      (phi41Level41CoeffListCompressedMatrix N)
      (phi41Level41RecurrenceCoeffArray N) := by
  unfold phi41Level41CoeffListCompressedMatrix
    phi41Level41RecurrenceCoeffArray
  let M := (N + 40) / 41
  let coeffs := phi41SparseCoeffMatrixArray
  simpa [M, coeffs, phi41LevelOneDenseRowsList] using
    (ListArrayEq.evalSparseCompressedMatrixFromProductTables
      (N := N) (M := M)
      (PCompressedL := phi41LevelOneDenseRowsList M)
      (QL := phi41LevelOneDenseRowsList N)
      (PCompressedA := phi41QRecurrenceRowsArray M)
      (QA := phi41QRecurrenceRowsArray N)
      coeffs (by rfl) (by simpa [M] using hP) hQ)

theorem ListArrayEq.phi41Level41CoeffCompressedMatrix_of_deltaArrays
    (N : ℕ) {DA DsmallA : Array ℤ}
    (hD : ListArrayEq N (deltaEulerTruncCoeffList N) DA)
    (hDsmall :
      ListArrayEq ((N + 40) / 41)
        (deltaEulerTruncCoeffList ((N + 40) / 41))
        DsmallA) :
    ListArrayEq N
      (phi41Level41CoeffListCompressedMatrix N)
      (phi41Level41CoeffArrayCompressedPullbackOfDelta N DA DsmallA) := by
  unfold phi41Level41CoeffListCompressedMatrix
    phi41Level41CoeffArrayCompressedPullbackOfDelta
  let M := (N + 40) / 41
  let EL := E4TruncCoeffList N
  let EA := E4TruncCoeffArray N
  let DL := deltaEulerTruncCoeffList N
  let CL := powTruncCoeffList N EL 3
  let CA := powTruncCoeffArray N EA 3
  let EsmallL := E4TruncCoeffList M
  let EsmallA := E4TruncCoeffArray M
  let DsmallL := deltaEulerTruncCoeffList M
  let CsmallL := powTruncCoeffList M EsmallL 3
  let CsmallA := powTruncCoeffArray M EsmallA 3
  let CPowL := powTruncCoeffTable N CL 42
  let CPowA := powTruncCoeffArrayTable N CA 42
  let DPowL := powTruncCoeffTable N DL 42
  let DPowA := powTruncCoeffArrayTable N DA 42
  let CSmallPowL := powTruncCoeffTable M CsmallL 42
  let CSmallPowA := powTruncCoeffArrayTable M CsmallA 42
  let DSmallPowL := powTruncCoeffTable M DsmallL 42
  let DSmallPowA := powTruncCoeffArrayTable M DsmallA 42
  let PCompressedL := phi41TermProductTable M CSmallPowL DSmallPowL
  let PCompressedA := phi41TermProductArrayTable M CSmallPowA DSmallPowA
  let QL := phi41TermProductTable N CPowL DPowL
  let QA := phi41TermProductArrayTable N CPowA DPowA
  let coeffs := phi41SparseCoeffMatrixArray
  have hE : ListArrayEq N EL EA := by
    simpa [EL, EA] using ListArrayEq.E4 N
  have hC : ListArrayEq N CL CA := by
    simpa [CL, CA] using hE.pow (k := 3)
  have hEsmall : ListArrayEq M EsmallL EsmallA := by
    simpa [EsmallL, EsmallA] using ListArrayEq.E4 M
  have hCsmall : ListArrayEq M CsmallL CsmallA := by
    simpa [CsmallL, CsmallA] using hEsmall.pow (k := 3)
  have hCPow : ListArrayTableEq N 42 CPowL CPowA := by
    simpa [CPowL, CPowA] using ListArrayTableEq.powTable (N := N) (maxPow := 42) hC
  have hDPow : ListArrayTableEq N 42 DPowL DPowA := by
    simpa [DPowL, DPowA] using ListArrayTableEq.powTable (N := N) (maxPow := 42) hD
  have hCSmallPow : ListArrayTableEq M 42 CSmallPowL CSmallPowA := by
    simpa [CSmallPowL, CSmallPowA] using
      ListArrayTableEq.powTable (N := M) (maxPow := 42) hCsmall
  have hDSmallPow : ListArrayTableEq M 42 DSmallPowL DSmallPowA := by
    simpa [DSmallPowL, DSmallPowA] using
      ListArrayTableEq.powTable (N := M) (maxPow := 42) hDsmall
  have hP : ListArrayTableEq M 42 PCompressedL PCompressedA := by
    simpa [PCompressedL, PCompressedA] using
      ListArrayTableEq.phi41TermProductTable hCSmallPow hDSmallPow
  have hQ : ListArrayTableEq N 42 QL QA := by
    simpa [QL, QA] using
      ListArrayTableEq.phi41TermProductTable hCPow hDPow
  let stepL : List ℤ → ℕ → List ℤ := fun out x =>
    let qPart := linearCombinationFromCoeffMatrixList N x QL coeffs
    addTruncCoeffList N out
      (mulQPullback41CompressedTruncCoeffList N
        (PCompressedL.getD x (zeroTruncCoeffList M)) qPart)
  let stepA : Array ℤ → ℕ → Array ℤ := fun out x =>
    let qPart := linearCombinationFromCoeffMatrixArray N x QA coeffs
    addTruncCoeffArray N out
      (mulQPullback41CompressedTruncCoeffArray N
        (PCompressedA.getD x (zeroTruncCoeffArray M)) qPart)
  have hstep : ∀ {outL outA : _} {x : ℕ}, x ≤ 42 →
      ListArrayEq N outL outA →
        ListArrayEq N (stepL outL x) (stepA outA x) := by
    intro outL outA x hx hout
    have hqPart :
        ListArrayEq N
          (linearCombinationFromCoeffMatrixList N x QL coeffs)
          (linearCombinationFromCoeffMatrixArray N x QA coeffs) :=
      ListArrayEq.linearCombinationFromCoeffMatrix coeffs hQ
    have hp := hP x hx
    have hmul :=
      ListArrayEq.mulQPullback41Compressed
        (N := N) (M := M) (by rfl) hp hqPart
    simpa [stepL, stepA] using hout.add hmul
  have hfold : ∀ (xs : List ℕ) (outL : List ℤ) (outA : Array ℤ),
      (∀ x ∈ xs, x ≤ 42) → ListArrayEq N outL outA →
        ListArrayEq N (xs.foldl stepL outL) (xs.foldl stepA outA) := by
    intro xs
    induction xs with
    | nil =>
        intro outL outA _ hout
        simpa using hout
    | cons x xs ih =>
        intro outL outA hxs hout
        have hx : x ≤ 42 := hxs x (by simp)
        have hxs' : ∀ y ∈ xs, y ≤ 42 := by
          intro y hy
          exact hxs y (by simp [hy])
        simpa [List.foldl] using ih (stepL outL x) (stepA outA x) hxs'
          (hstep hx hout)
  have hRange : ∀ x ∈ List.range 43, x ≤ 42 := by
    intro x hx
    have : x < 43 := List.mem_range.mp hx
    omega
  simpa [M, EL, EA, DL, CL, CA, EsmallL, EsmallA, DsmallL,
    CsmallL, CsmallA, CPowL, CPowA, DPowL, DPowA, CSmallPowL, CSmallPowA,
    DSmallPowL, DSmallPowA, PCompressedL, PCompressedA, QL, QA, coeffs,
    stepL, stepA] using
    hfold (List.range 43) (zeroTruncCoeffList N) (zeroTruncCoeffArray N)
      hRange (ListArrayEq.zero N)

theorem truncCoeffArrayAt_mulDeltaEulerFactorTruncCoeffArray_of_lt {N n : ℕ}
    (A : Array ℤ) (m : ℕ) (hn : n < N) :
    truncCoeffArrayAt (mulDeltaEulerFactorTruncCoeffArray N A m) n =
      ∑ j ∈ Finset.range 25,
        if j * m ≤ n then
          ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
            truncCoeffArrayAt A (n - j * m)
        else 0 := by
  unfold mulDeltaEulerFactorTruncCoeffArray
  calc
    truncCoeffArrayAt
        (truncCoeffArrayOfFn N
          (fun n => Id.run do
            let mut s : ℤ := 0
            for j in [0:25] do
              s := s +
                if j * m ≤ n then
                  ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
                    truncCoeffArrayAt A (n - j * m)
                else 0
            return s)) n =
        sumRangeFromZ 0 25
          (fun j =>
            if j * m ≤ n then
              ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
                truncCoeffArrayAt A (n - j * m)
            else 0) := by
          let f : ℕ → ℤ := fun j =>
              if j * m ≤ n then
                ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
                  truncCoeffArrayAt A (n - j * m)
              else 0
          have hget :
              truncCoeffArrayAt
                  (truncCoeffArrayOfFn N
                    (fun n => Id.run do
                      let mut s : ℤ := 0
                      for j in [0:25] do
                        s := s +
                          if j * m ≤ n then
                            ((if Even j then (1 : ℤ) else -1) *
                              (Nat.choose 24 j : ℤ)) *
                              truncCoeffArrayAt A (n - j * m)
                          else 0
                      return s)) n =
                (Id.run do
                  let mut s : ℤ := 0
                  for j in [0:25] do
                    s := s +
                      if j * m ≤ n then
                        ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
                          truncCoeffArrayAt A (n - j * m)
                      else 0
                  return s) := by
              simpa [truncCoeffAt_truncCoeffList_of_lt hn] using
                (ListArrayEq.ofFn N
                  (fun n => Id.run do
                    let mut s : ℤ := 0
                    for j in [0:25] do
                      s := s +
                        if j * m ≤ n then
                          ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
                            truncCoeffArrayAt A (n - j * m)
                        else 0
                    return s) n hn).symm
          have hloop :
              (Id.run do
                  let mut s : ℤ := 0
                  for j in [0:25] do
                    s := s +
                      if j * m ≤ n then
                        ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
                          truncCoeffArrayAt A (n - j * m)
                      else 0
                  return s) =
                sumRangeFromZ 0 25 f := by
              simpa only [f] using forIn_range_add_eq_sumRangeFromZ 25 f
          exact hget.trans hloop
    _ = ∑ j ∈ Finset.range 25,
        if j * m ≤ n then
          ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) *
            truncCoeffArrayAt A (n - j * m)
        else 0 := by
          rw [sumRangeFromZ_zero_eq_finset_sum]

theorem ListArrayEq.mulDeltaEulerFactor {N : ℕ} {a : List ℤ} {A : Array ℤ}
    (ha : ListArrayEq N a A) (m : ℕ) :
    ListArrayEq N
      (mulDeltaEulerFactorTruncCoeffList N a m)
      (mulDeltaEulerFactorTruncCoeffArray N A m) := by
  intro n hn
  rw [mulDeltaEulerFactorTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn,
    truncCoeffArrayAt_mulDeltaEulerFactorTruncCoeffArray_of_lt A m hn]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hle : j * m ≤ n
  · rw [if_pos hle, if_pos hle]
    congr 1
    exact ha (n - j * m) (by omega)
  · rw [if_neg hle, if_neg hle]

theorem ListArrayEq.deltaEulerTruncCoeffAux (N M : ℕ) :
    ListArrayEq N
      (deltaEulerTruncCoeffListAux N M)
      (deltaEulerTruncCoeffArrayAux N M) := by
  induction M with
  | zero =>
      simpa [deltaEulerTruncCoeffListAux, deltaEulerTruncCoeffArrayAux,
        XPowTruncCoeffList, XPowTruncCoeffArray] using
        ListArrayEq.ofFn N (fun n => if n = 1 then (1 : ℤ) else 0)
  | succ M ih =>
      simpa [deltaEulerTruncCoeffListAux, deltaEulerTruncCoeffArrayAux] using
        ih.mulDeltaEulerFactor (M + 1)

theorem ListArrayEq.deltaEulerTruncCoeff (N : ℕ) :
    ListArrayEq N (deltaEulerTruncCoeffList N) (deltaEulerTruncCoeffArray N) := by
  simpa [deltaEulerTruncCoeffList, deltaEulerTruncCoeffArray] using
    ListArrayEq.deltaEulerTruncCoeffAux N N

theorem ListArrayEq.phi41Level41CoeffCompressedMatrixEuler (N : ℕ) :
    ListArrayEq N
      (phi41Level41CoeffListCompressedMatrix N)
      (phi41Level41EulerCoeffArrayCompressedPullback N) := by
  unfold phi41Level41EulerCoeffArrayCompressedPullback
  exact ListArrayEq.phi41Level41CoeffCompressedMatrix_of_deltaArrays N
    (ListArrayEq.deltaEulerTruncCoeff N)
    (ListArrayEq.deltaEulerTruncCoeff ((N + 40) / 41))

theorem ListArrayEq.phi41Level41CoeffCompressedMatrixRamanujan
    (N : ℕ)
    (hD : ListArrayEq N
      (deltaEulerTruncCoeffList N)
      (deltaRamanujanTruncCoeffArray N))
    (hDsmall :
      ListArrayEq ((N + 40) / 41)
        (deltaEulerTruncCoeffList ((N + 40) / 41))
        (deltaRamanujanTruncCoeffArray ((N + 40) / 41))) :
    ListArrayEq N
      (phi41Level41CoeffListCompressedMatrix N)
      (phi41Level41FastCoeffArrayCompressedPullback N) := by
  unfold phi41Level41FastCoeffArrayCompressedPullback
  exact ListArrayEq.phi41Level41CoeffCompressedMatrix_of_deltaArrays N hD hDsmall

theorem deltaEulerRamanujanEqFirst_iff (N : ℕ) :
    deltaEulerRamanujanEqFirst N =
      truncCoeffArrayEqFirst N
        (deltaEulerTruncCoeffArray N)
        (deltaRamanujanTruncCoeffArray N) := by
  rfl

theorem deltaEulerRamanujanEqFirst_of_ListArrayEq (N : ℕ)
    (hD : ListArrayEq N (deltaEulerTruncCoeffList N)
      (deltaRamanujanTruncCoeffArray N)) :
    deltaEulerRamanujanEqFirst N = true := by
  rw [deltaEulerRamanujanEqFirst_iff]
  exact truncCoeffArrayEqFirst_eq_true_of_ListArrayEq
    (ListArrayEq.deltaEulerTruncCoeff N) hD

theorem phi41Level41FastCoeffArrayFirstZero_iff (N : ℕ) :
    phi41Level41FastCoeffArrayFirstZero N =
      truncCoeffArrayFirstZero N (phi41Level41FastCoeffArray N) := by
  rfl

theorem sum_antidiagonal_qPullback41_left
    (compressed full : List ℤ) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      (if 41 ∣ ij.1 then truncCoeffAt compressed (ij.1 / 41) else 0) *
        truncCoeffAt full ij.2) =
      sumRangeFromZ 0 (n / 41 + 1)
        (fun m => truncCoeffAt compressed m * truncCoeffAt full (n - 41 * m)) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j =>
      (if 41 ∣ i then truncCoeffAt compressed (i / 41) else 0) *
        truncCoeffAt full j)]
  rw [sumRangeFromZ_zero_eq_finset_sum]
  exact sum_range_qPullback41_left n
    (fun m => truncCoeffAt compressed m)
    (fun j => truncCoeffAt full j)

theorem sum_antidiagonal_mul_single_right (a : List ℤ) (n k : ℕ) (c : ℤ) :
    (∑ ij ∈ Finset.antidiagonal n,
      truncCoeffAt a ij.1 * (if ij.2 = k then c else 0)) =
    if k ≤ n then truncCoeffAt a (n - k) * c else 0 := by
  let f : ℕ × ℕ → ℤ := fun ij => truncCoeffAt a ij.1 * (if ij.2 = k then c else 0)
  change (∑ ij ∈ Finset.antidiagonal n, f ij) = _
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have hmem : (n - k, k) ∈ Finset.antidiagonal n := by
      simp [Finset.mem_antidiagonal, Nat.sub_add_cancel hk]
    rw [Finset.sum_eq_single_of_mem (n - k, k) hmem]
    · simp [f]
    · intro ij hij hne
      by_cases hijk : ij.2 = k
      · exfalso
        have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        have hfirst : ij.1 = n - k := by omega
        exact hne (Prod.ext hfirst hijk)
      · simp [f, hijk]
  · rw [if_neg hk]
    refine Finset.sum_eq_zero ?_
    intro ij hij
    by_cases hijk : ij.2 = k
    · have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
      have : k ≤ n := by omega
      exact (hk this).elim
    · simp [f, hijk]

theorem TruncRep.add {N : ℕ} {p q : PowerSeries ℤ} {a b : List ℤ}
    (hp : TruncRep N p a) (hq : TruncRep N q b) :
    TruncRep N (p + q) (addTruncCoeffList N a b) := by
  intro n hn
  simp [hp n hn, hq n hn, truncCoeffAt_addTruncCoeffList_of_lt a b hn]

theorem TruncRep.scale {N : ℕ} {p : PowerSeries ℤ} {a : List ℤ}
    (c : ℤ) (hp : TruncRep N p a) :
    TruncRep N ((PowerSeries.C c) * p) (scaleTruncCoeffList N c a) := by
  intro n hn
  rw [PowerSeries.coeff_C_mul n p c, hp n hn,
    truncCoeffAt_scaleTruncCoeffList_of_lt c a hn]

theorem TruncRep.const (N : ℕ) (c : ℤ) :
    TruncRep N (PowerSeries.C c) (constTruncCoeffList N c) := by
  intro n hn
  rw [constTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn,
    PowerSeries.coeff_C]

theorem TruncRep.neg {N : ℕ} {p : PowerSeries ℤ} {a : List ℤ}
    (hp : TruncRep N p a) :
    TruncRep N (-p) (scaleTruncCoeffList N (-1) a) := by
  intro n hn
  simp [hp n hn, scaleTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]

theorem TruncRep.sub {N : ℕ} {p q : PowerSeries ℤ} {a b : List ℤ}
    (hp : TruncRep N p a) (hq : TruncRep N q b) :
    TruncRep N (p - q) (subTruncCoeffList N a b) := by
  simpa [sub_eq_add_neg, subTruncCoeffList] using hp.add hq.neg

theorem TruncRep.X_pow (N m : ℕ) :
    TruncRep N ((PowerSeries.X : PowerSeries ℤ) ^ m) (XPowTruncCoeffList N m) := by
  intro n hn
  rw [XPowTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn,
    PowerSeries.coeff_X_pow]

theorem TruncRep.mul {N : ℕ} {p q : PowerSeries ℤ} {a b : List ℤ}
    (hp : TruncRep N p a) (hq : TruncRep N q b) :
    TruncRep N (p * q) (mulTruncCoeffList N a b) := by
  intro n hn
  rw [PowerSeries.coeff_mul, truncCoeffAt_mulTruncCoeffList_of_lt a b hn]
  refine Finset.sum_congr rfl ?_
  intro ij hij
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  have hiN : ij.1 < N := by omega
  have hjN : ij.2 < N := by omega
  rw [hp ij.1 hiN, hq ij.2 hjN]

theorem TruncRep.mulQPullback41Compressed {N M : ℕ}
    {p q : PowerSeries ℤ} {compressed full : List ℤ}
    (hM : (N + 40) / 41 ≤ M)
    (hp : TruncRep M p compressed) (hq : TruncRep N q full) :
    TruncRep N ((qPullback41Z p) * q)
      (mulQPullback41CompressedTruncCoeffList N compressed full) := by
  intro n hn
  rw [PowerSeries.coeff_mul, mulQPullback41CompressedTruncCoeffList,
    truncCoeffAt_truncCoeffList_of_lt hn]
  calc
    (∑ ij ∈ Finset.antidiagonal n,
        PowerSeries.coeff (R := ℤ) ij.1 (qPullback41Z p) *
          PowerSeries.coeff (R := ℤ) ij.2 q)
        =
      ∑ ij ∈ Finset.antidiagonal n,
        (if 41 ∣ ij.1 then truncCoeffAt compressed (ij.1 / 41) else 0) *
          truncCoeffAt full ij.2 := by
        refine Finset.sum_congr rfl ?_
        intro ij hij
        have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
        have hjN : ij.2 < N := by omega
        rw [hq ij.2 hjN, coeff_qPullback41Z]
        by_cases hdiv : 41 ∣ ij.1
        · rw [if_pos hdiv]
          have hquot_lt : ij.1 / 41 < M := by
            have hij_lt : ij.1 < N := by omega
            have hceil : ij.1 / 41 < (N + 40) / 41 := by omega
            exact lt_of_lt_of_le hceil hM
          rw [hp (ij.1 / 41) hquot_lt]
          rw [if_pos hdiv]
        · rw [if_neg hdiv]
          rw [if_neg hdiv]
    _ =
      sumRangeFromZ 0 (n / 41 + 1)
        (fun m => truncCoeffAt compressed m * truncCoeffAt full (n - 41 * m)) := by
        exact sum_antidiagonal_qPullback41_left compressed full n

theorem TruncRep.pow {N k : ℕ} {p : PowerSeries ℤ} {a : List ℤ}
    (hp : TruncRep N p a) :
    TruncRep N (p ^ k) (powTruncCoeffList N a k) := by
  induction k with
  | zero =>
      simpa [powTruncCoeffList] using TruncRep.const N 1
  | succ k ih =>
      simpa [pow_succ, powTruncCoeffList] using ih.mul hp

theorem TruncRep.qPullback41 {N : ℕ} {p : PowerSeries ℤ} {a : List ℤ}
    (hp : TruncRep N p a) :
    TruncRep N (qPullback41Z p) (qPullback41TruncCoeffList N a) := by
  intro n hn
  rw [coeff_qPullback41Z, qPullback41TruncCoeffList,
    truncCoeffAt_truncCoeffList_of_lt hn]
  by_cases hdiv : 41 ∣ n
  · rw [if_pos hdiv]
    rw [if_pos hdiv]
    exact hp (n / 41) (lt_of_le_of_lt (Nat.div_le_self n 41) hn)
  · rw [if_neg hdiv]
    rw [if_neg hdiv]

theorem TruncRep.evalSparseBivarClearedCompressed {N M : ℕ}
    {xNum xDen yNum yDen : PowerSeries ℤ}
    {xNumM xDenM yNumN yDenN : List ℤ}
    (hM : (N + 40) / 41 ≤ M)
    (hxNumM : TruncRep M xNum xNumM)
    (hxDenM : TruncRep M xDen xDenM)
    (hyNumN : TruncRep N yNum yNumN)
    (hyDenN : TruncRep N yDen yDenN) :
    ∀ terms : List SparseBivarTerm,
      (∀ t ∈ terms, t.xPow ≤ 42 ∧ t.yPow ≤ 42) →
      TruncRep N
        (evalSparseBivarCleared terms 42 42
          (qPullback41Z xNum) (qPullback41Z xDen) yNum yDen)
        (evalSparseCompressedFromProductTablesTrunc N M
          (phi41TermProductTable M
            (powTruncCoeffTable M xNumM 42)
            (powTruncCoeffTable M xDenM 42))
          (phi41TermProductTable N
            (powTruncCoeffTable N yNumN 42)
            (powTruncCoeffTable N yDenN 42))
          terms) := by
  intro terms hdeg
  induction terms with
  | nil =>
      intro n hn
      change PowerSeries.coeff (R := ℤ) n (0 : PowerSeries ℤ) =
        truncCoeffAt (zeroTruncCoeffList N) n
      simp [zeroTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]
  | cons t ts ih =>
      have htdeg : t.xPow ≤ 42 ∧ t.yPow ≤ 42 := hdeg t (by simp)
      have htsdeg : ∀ u ∈ ts, u.xPow ≤ 42 ∧ u.yPow ≤ 42 := by
        intro u hu
        exact hdeg u (by simp [hu])
      have hxP := hxNumM.pow (k := t.xPow)
      have hxD := hxDenM.pow (k := 42 - t.xPow)
      have hyP := hyNumN.pow (k := t.yPow)
      have hyD := hyDenN.pow (k := 42 - t.yPow)
      have hxTerm :
          TruncRep M
            (xNum ^ t.xPow * xDen ^ (42 - t.xPow))
            (mulTruncCoeffList M
              (powTruncCoeffList M xNumM t.xPow)
              (powTruncCoeffList M xDenM (42 - t.xPow))) := hxP.mul hxD
      have hyTerm :
          TruncRep N
            (yNum ^ t.yPow * yDen ^ (42 - t.yPow))
            (mulTruncCoeffList N
              (powTruncCoeffList N yNumN t.yPow)
              (powTruncCoeffList N yDenN (42 - t.yPow))) := hyP.mul hyD
      have hterm :=
        (hxTerm.mulQPullback41Compressed hM hyTerm).scale t.coeff
      have htail := ih htsdeg
      rw [evalSparseBivarCleared, evalSparseCompressedFromProductTablesTrunc]
      rw [phi41TermProductTable_getD_of_le M
          (powTruncCoeffTable M xNumM 42) (powTruncCoeffTable M xDenM 42) htdeg.1,
        phi41TermProductTable_getD_of_le N
          (powTruncCoeffTable N yNumN 42) (powTruncCoeffTable N yDenN 42) htdeg.2]
      rw [powTruncCoeffTable_getD_of_le M xNumM htdeg.1,
        powTruncCoeffTable_getD_of_le M xDenM (Nat.sub_le 42 t.xPow),
        powTruncCoeffTable_getD_of_le N yNumN htdeg.2,
        powTruncCoeffTable_getD_of_le N yDenN (Nat.sub_le 42 t.yPow)]
      have hsum := hterm.add htail
      simpa [qPullback41Z_mul, qPullback41Z_pow, mul_assoc] using hsum

theorem TruncRep.E4 (N : ℕ) :
    TruncRep N E4ZSeries (E4TruncCoeffList N) := by
  intro n hn
  rw [coeff_E4ZSeries, E4TruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]

theorem TruncRep.E2 (N : ℕ) :
    TruncRep N E2ZSeries (E2TruncCoeffList N) := by
  intro n hn
  rw [E2ZSeries, E2TruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]
  simp [E2CoeffZ]

theorem TruncRep.E6 (N : ℕ) :
    TruncRep N E6ZSeries (E6TruncCoeffList N) := by
  intro n hn
  rw [coeff_E6ZSeries, E6TruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]

theorem TruncRep.E2E4 (N : ℕ) :
    TruncRep N (E2ZSeries * E4ZSeries) (E2E4TruncCoeffList N) := by
  simpa [E2E4TruncCoeffList] using (TruncRep.E2 N).mul (TruncRep.E4 N)

theorem coeff_phi41RecurrenceMultiplier_zero (j : ℕ) :
    PowerSeries.coeff (R := ℤ) 0
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) =
      (42 : ℤ) - (j : ℤ) := by
  rw [map_sub]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_mul]
  simp [E2ZSeries, E2CoeffZ, E4ZSeries, E4CoeffZ, E6ZSeries, E6CoeffZ]

theorem coeff_phi41RecurrenceMultiplier_pos
    {N j a : ℕ} (ha : a < N) :
    PowerSeries.coeff (R := ℤ) a
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) =
      (42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
        (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a := by
  rw [map_sub]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  rw [(TruncRep.E2E4 N) a ha, (TruncRep.E6 N) a ha]

theorem truncCoeffAt_phi41DenseRow_mul_recurrence_of_derivative_identity
    {N j n : ℕ} {f : PowerSeries ℤ} {row : List ℤ}
    (hj : j ≤ 42) (hn : n < N) (hval : 42 - j < n)
    (hrep : TruncRep N f row)
    (hderiv :
      E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ f) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) * f) :
    (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffAt row n =
      (sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
            (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
          truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
            truncCoeffAt row (n - a))) := by
  let H : PowerSeries ℤ :=
    PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
      PowerSeries.C (j : ℤ) * E6ZSeries
  let S : ℤ := sumRangeFromZ 1 n (fun a =>
    (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
        (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
      truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
        truncCoeffAt row (n - a))
  have hcoeff :
      PowerSeries.coeff (R := ℤ) n
          (E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ f)) =
        PowerSeries.coeff (R := ℤ) n (H * f) := by
    simpa [H] using congrArg (PowerSeries.coeff (R := ℤ) n) hderiv
  rw [coeff_mul_X_derivative_eq_const_add_tail] at hcoeff
  rw [coeff_mul_eq_const_add_tail] at hcoeff
  have hleft :
      PowerSeries.coeff (R := ℤ) 0 E4ZSeries *
          ((n : ℤ) * PowerSeries.coeff (R := ℤ) n f) +
        ∑ a ∈ Finset.range n,
          PowerSeries.coeff (R := ℤ) (a + 1) E4ZSeries *
            (((n - (a + 1) : ℕ) : ℤ) *
              PowerSeries.coeff (R := ℤ) (n - (a + 1)) f) =
        (n : ℤ) * truncCoeffAt row n +
          ∑ a ∈ Finset.range n,
            truncCoeffAt (E4TruncCoeffList N) (a + 1) *
              (((n - (a + 1) : ℕ) : ℤ) *
                truncCoeffAt row (n - (a + 1))) := by
    rw [coeff_E4ZSeries]
    simp only [E4CoeffZ, ↓reduceIte, one_mul]
    congr 1
    · rw [hrep n hn]
    · refine Finset.sum_congr rfl ?_
      intro a ha
      have halt : a < n := Finset.mem_range.mp ha
      have haN : a + 1 < N := by omega
      have hidxN : n - (a + 1) < N := by omega
      rw [(TruncRep.E4 N) (a + 1) haN, hrep (n - (a + 1)) hidxN]
  have hright :
      PowerSeries.coeff (R := ℤ) 0 H * PowerSeries.coeff (R := ℤ) n f +
        ∑ a ∈ Finset.range n,
          PowerSeries.coeff (R := ℤ) (a + 1) H *
            PowerSeries.coeff (R := ℤ) (n - (a + 1)) f =
        ((42 : ℤ) - (j : ℤ)) * truncCoeffAt row n +
          ∑ a ∈ Finset.range n,
            ((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) (a + 1) -
              (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) (a + 1)) *
                truncCoeffAt row (n - (a + 1)) := by
    congr 1
    · rw [show PowerSeries.coeff (R := ℤ) 0 H = (42 : ℤ) - (j : ℤ) by
        exact coeff_phi41RecurrenceMultiplier_zero j]
      rw [hrep n hn]
    · refine Finset.sum_congr rfl ?_
      intro a ha
      have halt : a < n := Finset.mem_range.mp ha
      have haN : a + 1 < N := by omega
      have hidxN : n - (a + 1) < N := by omega
      rw [show PowerSeries.coeff (R := ℤ) (a + 1) H =
          (42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) (a + 1) -
            (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) (a + 1) by
        exact coeff_phi41RecurrenceMultiplier_pos (N := N) (j := j) haN]
      rw [hrep (n - (a + 1)) hidxN]
  rw [hleft, hright] at hcoeff
  have hS :
      S =
        ∑ a ∈ Finset.range n,
          (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) (a + 1) -
              (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) (a + 1)) -
            truncCoeffAt (E4TruncCoeffList N) (a + 1) *
              ((n - (a + 1) : ℕ) : ℤ)) *
              truncCoeffAt row (n - (a + 1)) := by
    unfold S
    rw [sumRangeFromZ_eq_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    ring_nf
  have hmul : (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffAt row n = S := by
    rw [hS]
    calc
      (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffAt row n
          = (n : ℤ) * truncCoeffAt row n -
              ((42 : ℤ) - (j : ℤ)) * truncCoeffAt row n := by
            have hcast :
                ((n - (42 - j) : ℕ) : ℤ) =
                  (n : ℤ) - ((42 : ℤ) - (j : ℤ)) := by
              omega
            rw [hcast]
            ring
      _ =
          (∑ a ∈ Finset.range n,
            ((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) (a + 1) -
              (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) (a + 1)) *
                truncCoeffAt row (n - (a + 1))) -
            ∑ a ∈ Finset.range n,
              truncCoeffAt (E4TruncCoeffList N) (a + 1) *
                (((n - (a + 1) : ℕ) : ℤ) *
                  truncCoeffAt row (n - (a + 1))) := by
            linarith
      _ =
          ∑ a ∈ Finset.range n,
            (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) (a + 1) -
                (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) (a + 1)) -
              truncCoeffAt (E4TruncCoeffList N) (a + 1) *
                ((n - (a + 1) : ℕ) : ℤ)) *
                truncCoeffAt row (n - (a + 1)) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro a _ha
            ring
  exact hmul

theorem truncCoeffAt_phi41DenseRow_recurrence_of_derivative_identity
    {N j n : ℕ} {f : PowerSeries ℤ} {row : List ℤ}
    (hj : j ≤ 42) (hn : n < N) (hval : 42 - j < n)
    (hrep : TruncRep N f row)
    (hderiv :
      E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ f) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) * f) :
    truncCoeffAt row n =
      (sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
            (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
          truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
            truncCoeffAt row (n - a))) /
        (((n - (42 - j) : ℕ) : ℤ)) := by
  let S : ℤ := sumRangeFromZ 1 n (fun a =>
    (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
        (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
      truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
        truncCoeffAt row (n - a))
  have hmul :
      (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffAt row n = S := by
    simpa [S] using
      truncCoeffAt_phi41DenseRow_mul_recurrence_of_derivative_identity
        (N := N) (j := j) (n := n) (f := f) (row := row)
        hj hn hval hrep hderiv
  change truncCoeffAt row n = S / (((n - (42 - j) : ℕ) : ℤ))
  rw [← hmul]
  rw [Int.mul_ediv_cancel_left]
  exact_mod_cast (Nat.sub_ne_zero_of_lt hval)

theorem TruncRep.deltaEulerFactor (N m : ℕ) :
    TruncRep N (deltaEulerFactorZ m) (deltaEulerFactorTruncCoeffListSlow N m) := by
  have hbase :
      TruncRep N
        ((1 : PowerSeries ℤ) - (PowerSeries.X : PowerSeries ℤ) ^ m)
        (subTruncCoeffList N (constTruncCoeffList N 1) (XPowTruncCoeffList N m)) := by
    simpa using (TruncRep.const N 1).sub (TruncRep.X_pow N m)
  simpa [deltaEulerFactorZ, deltaEulerFactorTruncCoeffListSlow] using hbase.pow (k := 24)

theorem TruncRep.deltaEulerFactorSparse (N m : ℕ) :
    TruncRep N (deltaEulerFactorZ m) (deltaEulerFactorSparseTruncCoeffList N m) := by
  intro n hn
  rw [coeff_deltaEulerFactorZ_sparse, deltaEulerFactorSparseTruncCoeffList,
    truncCoeffAt_truncCoeffList_of_lt hn]

theorem TruncRep.mulDeltaEulerFactorFast {N : ℕ} {p : PowerSeries ℤ} {a : List ℤ}
    (hp : TruncRep N p a) (m : ℕ) :
    TruncRep N (p * deltaEulerFactorZ m) (mulDeltaEulerFactorTruncCoeffList N a m) := by
  intro n hn
  rw [PowerSeries.coeff_mul, mulDeltaEulerFactorTruncCoeffList,
    truncCoeffAt_truncCoeffList_of_lt hn]
  simp_rw [coeff_deltaEulerFactorZ_sparse]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  trans ∑ ij ∈ Finset.antidiagonal n,
      truncCoeffAt a ij.1 *
        (if ij.2 = j * m then
          ((if Even j then (1 : ℤ) else -1) * (Nat.choose 24 j : ℤ)) else 0)
  · refine Finset.sum_congr rfl ?_
    intro ij hij
    have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    have hiN : ij.1 < N := by omega
    rw [hp ij.1 hiN]
  · rw [sum_antidiagonal_mul_single_right]
    by_cases hle : j * m ≤ n
    · rw [if_pos hle, if_pos hle]
      ring
    · rw [if_neg hle, if_neg hle]

theorem TruncRep.deltaEulerProductTrunc (N M : ℕ) :
    TruncRep N (deltaEulerProductTruncZ M)
      (deltaEulerProductTruncCoeffListSlow N M) := by
  induction M with
  | zero =>
      simpa [deltaEulerProductTruncZ, deltaEulerProductTruncCoeffListSlow]
        using TruncRep.X_pow N 1
  | succ M ih =>
      have hmul := ih.mul (TruncRep.deltaEulerFactor N (M + 1))
      simpa [deltaEulerProductTruncZ, deltaEulerProductTruncCoeffListSlow,
        Finset.prod_range_succ, mul_assoc] using hmul

theorem TruncRep.deltaEulerProductTruncSparse (N M : ℕ) :
    TruncRep N (deltaEulerProductTruncZ M)
      (deltaEulerProductTruncCoeffListSparse N M) := by
  induction M with
  | zero =>
      simpa [deltaEulerProductTruncZ, deltaEulerProductTruncCoeffListSparse]
        using TruncRep.X_pow N 1
  | succ M ih =>
      have hmul := ih.mul (TruncRep.deltaEulerFactorSparse N (M + 1))
      simpa [deltaEulerProductTruncZ, deltaEulerProductTruncCoeffListSparse,
        Finset.prod_range_succ, mul_assoc] using hmul

theorem TruncRep.deltaEulerProductTruncFast (N M : ℕ) :
    TruncRep N (deltaEulerProductTruncZ M)
      (deltaEulerTruncCoeffListAux N M) := by
  induction M with
  | zero =>
      simpa [deltaEulerProductTruncZ, deltaEulerTruncCoeffListAux]
        using TruncRep.X_pow N 1
  | succ M ih =>
      have hmul := ih.mulDeltaEulerFactorFast (M + 1)
      simpa [deltaEulerProductTruncZ, deltaEulerTruncCoeffListAux,
        Finset.prod_range_succ, mul_assoc] using hmul

theorem TruncRep.deltaEulerSeriesSparse (N : ℕ) :
    TruncRep N deltaEulerSeriesZ (deltaEulerProductTruncCoeffListSparse N N) := by
  intro n hn
  rw [coeff_deltaEulerSeriesZ,
    ← coeff_deltaEulerProductTruncZ_eq_deltaEulerCoeffZ_of_lt (N := N) hn]
  exact (TruncRep.deltaEulerProductTruncSparse N N) n hn

theorem TruncRep.deltaEulerSeriesFast (N : ℕ) :
    TruncRep N deltaEulerSeriesZ (deltaEulerTruncCoeffList N) := by
  intro n hn
  rw [deltaEulerTruncCoeffList, coeff_deltaEulerSeriesZ,
    ← coeff_deltaEulerProductTruncZ_eq_deltaEulerCoeffZ_of_lt (N := N) hn]
  exact (TruncRep.deltaEulerProductTruncFast N N) n hn

theorem truncCoeffAt_deltaEulerTruncCoeffList_eq_deltaEulerCoeffZ {N n : ℕ}
    (hn : n < N) :
    truncCoeffAt (deltaEulerTruncCoeffList N) n = deltaEulerCoeffZ n := by
  have hrep := TruncRep.deltaEulerSeriesFast N
  rw [← hrep n hn]
  rw [coeff_deltaEulerSeriesZ]

theorem truncCoeffAt_deltaEulerTruncCoeffList_eq_zero_of_lt_one {N n : ℕ}
    (hn : n < N) (hn1 : n < 1) :
    truncCoeffAt (deltaEulerTruncCoeffList N) n = 0 := by
  have hn0 : n = 0 := by omega
  subst hn0
  rw [truncCoeffAt_deltaEulerTruncCoeffList_eq_deltaEulerCoeffZ hn]
  exact deltaEulerCoeffZ_zero

theorem truncCoeffAt_deltaEulerTruncCoeffList_one {N : ℕ} (hN : 1 < N) :
    truncCoeffAt (deltaEulerTruncCoeffList N) 1 = 1 := by
  rw [truncCoeffAt_deltaEulerTruncCoeffList_eq_deltaEulerCoeffZ hN]
  exact deltaEulerCoeffZ_one

theorem truncCoeffAt_E4TruncCoeffList_zero {N : ℕ} (hN : 0 < N) :
    truncCoeffAt (E4TruncCoeffList N) 0 = 1 := by
  rw [E4TruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hN]
  simp [E4CoeffZ]

theorem truncCoeffAt_E4CubedTruncCoeffList_zero {N : ℕ} (hN : 0 < N) :
    truncCoeffAt (powTruncCoeffList N (E4TruncCoeffList N) 3) 0 = 1 := by
  have hN' : 3 * 0 < N := by simpa using hN
  simpa using
    (truncCoeffAt_powTruncCoeffList_eq_pow_of_eq_mul
      (N := N) (v := 0) (k := 3) (a := E4TruncCoeffList N) (c := 1)
      hN'
      (by intro i _hiN hi0; omega)
      (truncCoeffAt_E4TruncCoeffList_zero hN))

theorem truncCoeffAt_powE4CubedTruncCoeffList_zero {N j : ℕ} (hN : 0 < N) :
    truncCoeffAt
      (powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j) 0 = 1 := by
  have hN' : j * 0 < N := by simpa using hN
  simpa using
    (truncCoeffAt_powTruncCoeffList_eq_pow_of_eq_mul
      (N := N) (v := 0) (k := j)
      (a := powTruncCoeffList N (E4TruncCoeffList N) 3) (c := 1)
      hN'
      (by intro i _hiN hi0; omega)
      (truncCoeffAt_E4CubedTruncCoeffList_zero hN))

theorem truncCoeffAt_powDeltaEulerTruncCoeffList_eq_zero_of_lt
    {N n k : ℕ} (hn : n < N) (hnk : n < k) :
    truncCoeffAt (powTruncCoeffList N (deltaEulerTruncCoeffList N) k) n = 0 := by
  have hnk' : n < k * 1 := by simpa using hnk
  exact
    truncCoeffAt_powTruncCoeffList_eq_zero_of_lt_mul
      (N := N) (n := n) (v := 1) (k := k)
      (a := deltaEulerTruncCoeffList N) hn
      (by
        intro i hiN hi1
        exact truncCoeffAt_deltaEulerTruncCoeffList_eq_zero_of_lt_one hiN hi1)
      hnk'

theorem truncCoeffAt_powDeltaEulerTruncCoeffList_eq_one
    {N k : ℕ} (hN : k < N) :
    truncCoeffAt (powTruncCoeffList N (deltaEulerTruncCoeffList N) k) k = 1 := by
  cases k with
  | zero =>
      simpa [powTruncCoeffList] using truncCoeffAt_constTruncCoeffList_zero hN
  | succ k =>
      have hN' : (k + 1) * 1 < N := by simpa using hN
      simpa using
        (truncCoeffAt_powTruncCoeffList_eq_pow_of_eq_mul
          (N := N) (v := 1) (k := k + 1)
          (a := deltaEulerTruncCoeffList N) (c := 1)
          hN'
          (by
            intro i hiN hi1
            exact truncCoeffAt_deltaEulerTruncCoeffList_eq_zero_of_lt_one hiN hi1)
          (truncCoeffAt_deltaEulerTruncCoeffList_one (by omega : 1 < N)))

theorem truncCoeffAt_phi41LevelOneDenseRowExpr_eq_zero_of_lt_valuation
    {N j n : ℕ} (_hj : j ≤ 42) (hn : n < N) (hnv : n < 42 - j) :
    truncCoeffAt
      (mulTruncCoeffList N
        (powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j)
        (powTruncCoeffList N (deltaEulerTruncCoeffList N) (42 - j))) n = 0 := by
  apply truncCoeffAt_mulTruncCoeffList_eq_zero_of_lt_add
    (N := N) (n := n) (va := 0) (vb := 42 - j) hn
  · intro i _hiN hi0
    omega
  · intro i hiN hiv
    exact truncCoeffAt_powDeltaEulerTruncCoeffList_eq_zero_of_lt hiN hiv
  · simpa using hnv

theorem truncCoeffAt_phi41LevelOneDenseRowExpr_eq_one_of_eq_valuation
    {N j : ℕ} (_hj : j ≤ 42) (hN : 42 - j < N) :
    truncCoeffAt
      (mulTruncCoeffList N
        (powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j)
        (powTruncCoeffList N (deltaEulerTruncCoeffList N) (42 - j))) (42 - j) = 1 := by
  have hN0 : 0 < N := by omega
  nth_rewrite 2 [show 42 - j = 0 + (42 - j) by omega]
  rw [truncCoeffAt_mulTruncCoeffList_eq_mul_of_eq_add
    (N := N) (va := 0) (vb := 42 - j)
    (a := powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j)
    (b := powTruncCoeffList N (deltaEulerTruncCoeffList N) (42 - j))
    (ca := 1) (cb := 1)]
  · ring
  · simpa using hN
  · intro i _hiN hi0
    omega
  · intro i hiN hiv
    exact truncCoeffAt_powDeltaEulerTruncCoeffList_eq_zero_of_lt hiN hiv
  · exact truncCoeffAt_powE4CubedTruncCoeffList_zero hN0
  · exact truncCoeffAt_powDeltaEulerTruncCoeffList_eq_one hN

theorem phi41LevelOneDenseRowsList_getD_of_le
    (N : ℕ) {j : ℕ} (hj : j ≤ 42) :
    (phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N) =
      mulTruncCoeffList N
        (powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j)
        (powTruncCoeffList N (deltaEulerTruncCoeffList N) (42 - j)) := by
  unfold phi41LevelOneDenseRowsList
  rw [phi41TermProductTable_getD_of_le N
    (powTruncCoeffTable N (powTruncCoeffList N (E4TruncCoeffList N) 3) 42)
    (powTruncCoeffTable N (deltaEulerTruncCoeffList N) 42) hj]
  rw [powTruncCoeffTable_getD_of_le N
      (powTruncCoeffList N (E4TruncCoeffList N) 3) hj,
    powTruncCoeffTable_getD_of_le N
      (deltaEulerTruncCoeffList N) (Nat.sub_le 42 j)]

theorem truncCoeffAt_phi41LevelOneDenseRowsList_eq_zero_of_lt_valuation
    {N j n : ℕ} (hj : j ≤ 42) (hn : n < N) (hnv : n < 42 - j) :
    truncCoeffAt ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)) n = 0 := by
  rw [phi41LevelOneDenseRowsList_getD_of_le N hj]
  exact truncCoeffAt_phi41LevelOneDenseRowExpr_eq_zero_of_lt_valuation hj hn hnv

theorem truncCoeffAt_phi41LevelOneDenseRowsList_eq_one_of_eq_valuation
    {N j n : ℕ} (hj : j ≤ 42) (hn : n < N) (hnv : n = 42 - j) :
    truncCoeffAt ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)) n = 1 := by
  subst hnv
  rw [phi41LevelOneDenseRowsList_getD_of_le N hj]
  exact truncCoeffAt_phi41LevelOneDenseRowExpr_eq_one_of_eq_valuation hj hn

theorem TruncRep.phi41LevelOneDenseRowExpr (N j : ℕ) :
    TruncRep N
      ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))
      (mulTruncCoeffList N
        (powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j)
        (powTruncCoeffList N (deltaEulerTruncCoeffList N) (42 - j))) := by
  have hE4cubed :
      TruncRep N (E4ZSeries ^ 3)
        (powTruncCoeffList N (E4TruncCoeffList N) 3) :=
    (TruncRep.E4 N).pow
  exact (hE4cubed.pow).mul ((TruncRep.deltaEulerSeriesFast N).pow)

theorem natCast_mul_pow_pred_mul_self {R : Type*} [CommSemiring R]
    (x : R) (n : ℕ) :
    (n : R) * x ^ (n - 1) * x = (n : R) * x ^ n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      simp [pow_succ, mul_assoc]

theorem natCast_mul_pow_pred_mul_term_left {R : Type*} [CommSemiring R]
    (C D A : R) (j k : ℕ) :
    (j : R) * C ^ (j - 1) * D ^ k * (A * C) =
      (j : R) * A * (C ^ j * D ^ k) := by
  calc
    (j : R) * C ^ (j - 1) * D ^ k * (A * C)
        = ((j : R) * C ^ (j - 1) * C) * (A * D ^ k) := by ring
    _ = ((j : R) * C ^ j) * (A * D ^ k) := by
        rw [natCast_mul_pow_pred_mul_self C j]
    _ = (j : R) * A * (C ^ j * D ^ k) := by ring

theorem natCast_mul_pow_pred_mul_term_right {R : Type*} [CommSemiring R]
    (C D E : R) (j k : ℕ) :
    (k : R) * C ^ j * D ^ (k - 1) * E * D =
      (k : R) * E * (C ^ j * D ^ k) := by
  calc
    (k : R) * C ^ j * D ^ (k - 1) * E * D
        = ((k : R) * D ^ (k - 1) * D) * (E * C ^ j) := by ring
    _ = ((k : R) * D ^ k) * (E * C ^ j) := by
        rw [natCast_mul_pow_pred_mul_self D k]
    _ = (k : R) * E * (C ^ j * D ^ k) := by ring

theorem E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity
    (hE4 :
      PowerSeries.C (3 : ℤ) *
          (PowerSeries.X * PowerSeries.derivative ℤ E4ZSeries) =
        E2ZSeries * E4ZSeries - E6ZSeries) :
      E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ (E4ZSeries ^ 3)) =
        (E2ZSeries * E4ZSeries - E6ZSeries) * (E4ZSeries ^ 3) := by
  rw [PowerSeries.derivative_pow]
  calc
    E4ZSeries *
        (PowerSeries.X *
          ((3 : PowerSeries ℤ) * E4ZSeries ^ (3 - 1) *
            PowerSeries.derivative ℤ E4ZSeries))
        =
      E4ZSeries ^ 3 *
        (PowerSeries.C (3 : ℤ) *
          (PowerSeries.X * PowerSeries.derivative ℤ E4ZSeries)) := by
        norm_num
        ring
    _ = E4ZSeries ^ 3 * (E2ZSeries * E4ZSeries - E6ZSeries) := by
        rw [hE4]
    _ = (E2ZSeries * E4ZSeries - E6ZSeries) * (E4ZSeries ^ 3) := by
        ring

theorem E4ZSeries_derivative_identity_of_coeff_identity
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (3 : ℤ) * ((n : ℤ) * E4CoeffZ n) =
        PowerSeries.coeff (R := ℤ) n (E2ZSeries * E4ZSeries) - E6CoeffZ n) :
      PowerSeries.C (3 : ℤ) *
          (PowerSeries.X * PowerSeries.derivative ℤ E4ZSeries) =
        E2ZSeries * E4ZSeries - E6ZSeries := by
  ext n
  rw [map_sub]
  rw [PowerSeries.coeff_C_mul]
  rw [coeff_X_derivative_eq_natCast_mul_coeff]
  rw [coeff_E4ZSeries]
  rw [coeff_E6ZSeries]
  by_cases hn : n = 0
  · subst hn
    rw [PowerSeries.coeff_mul]
    simp [E2ZSeries, E2CoeffZ, E4ZSeries, E4CoeffZ, E6CoeffZ]
  · rw [hcoeff n hn]

theorem E4ZSeries_derivative_identity_of_E4Coeff_convolution
    (hconv : ∀ n : ℕ, n ≠ 0 →
      (3 : ℤ) * ((n : ℤ) * E4CoeffZ n) =
        E4CoeffZ n + (-24 : ℤ) * ∑ k ∈ Finset.range n,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            E4CoeffZ (n - (k + 1)) - E6CoeffZ n) :
      PowerSeries.C (3 : ℤ) *
          (PowerSeries.X * PowerSeries.derivative ℤ E4ZSeries) =
        E2ZSeries * E4ZSeries - E6ZSeries := by
  apply E4ZSeries_derivative_identity_of_coeff_identity
  intro n hn
  rw [coeff_E2ZSeries_mul]
  simp_rw [coeff_E4ZSeries]
  exact hconv n hn

theorem E4Coeff_convolution_of_sigma_convolution
    (hconv : ∀ n : ℕ, n ≠ 0 →
      (21 : ℤ) * (ArithmeticFunction.sigma 5 n : ℤ) =
        ((30 : ℤ) * (n : ℤ) - 10) * (ArithmeticFunction.sigma 3 n : ℤ) +
          240 * ∑ k ∈ Finset.range (n - 1),
            (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
              (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ) +
          (ArithmeticFunction.sigma 1 n : ℤ)) :
    ∀ n : ℕ, n ≠ 0 →
      (3 : ℤ) * ((n : ℤ) * E4CoeffZ n) =
        E4CoeffZ n + (-24 : ℤ) * ∑ k ∈ Finset.range n,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            E4CoeffZ (n - (k + 1)) - E6CoeffZ n := by
  intro n hn
  have hsplit :
      (∑ k ∈ Finset.range n,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            E4CoeffZ (n - (k + 1))) =
        240 * (∑ k ∈ Finset.range (n - 1),
          (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
            (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ)) +
        (ArithmeticFunction.sigma 1 n : ℤ) := by
    rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro k hk
      have hklt : k < n - 1 := Finset.mem_range.mp hk
      have hpos : n - (k + 1) ≠ 0 := by omega
      have harg : n - 1 + 1 - (k + 1) = n - (k + 1) := by omega
      rw [E4CoeffZ]
      rw [harg]
      rw [if_neg hpos]
      ring
    · rw [show n - 1 + 1 = n by omega]
      rw [show n - n = 0 by omega]
      simp [E4CoeffZ]
  rw [E4CoeffZ, if_neg hn, E6CoeffZ, if_neg hn]
  rw [hsplit]
  have hconvn := hconv n hn
  have hconv24 :
      (504 : ℤ) * (ArithmeticFunction.sigma 5 n : ℤ) =
        24 * (((30 : ℤ) * (n : ℤ) - 10) *
          (ArithmeticFunction.sigma 3 n : ℤ) +
          240 * ∑ k ∈ Finset.range (n - 1),
            (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
              (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ) +
          (ArithmeticFunction.sigma 1 n : ℤ)) := by
    calc
      (504 : ℤ) * (ArithmeticFunction.sigma 5 n : ℤ)
          = 24 * ((21 : ℤ) * (ArithmeticFunction.sigma 5 n : ℤ)) := by ring
      _ =
        24 * (((30 : ℤ) * (n : ℤ) - 10) *
          (ArithmeticFunction.sigma 3 n : ℤ) +
          240 * ∑ k ∈ Finset.range (n - 1),
            (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
              (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ) +
          (ArithmeticFunction.sigma 1 n : ℤ)) := by
          rw [hconvn]
  ring_nf at hconv24 ⊢
  linarith

private theorem E4ZSeries_derivative_coeff_identity_complex (n : ℕ) :
    (3 : ℂ) * ((n : ℂ) * PowerSeries.coeff (R := ℂ) n
        (PowerSeries.map (Int.castRingHom ℂ) E4ZSeries)) =
      PowerSeries.coeff (R := ℂ) n
        (PowerSeries.map (Int.castRingHom ℂ) (E2ZSeries * E4ZSeries)) -
      PowerSeries.coeff (R := ℂ) n
        (PowerSeries.map (Int.castRingHom ℂ) E6ZSeries) := by
  let E4C : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) E4ZSeries
  let E2E4C : PowerSeries ℂ :=
    PowerSeries.map (Int.castRingHom ℂ) (E2ZSeries * E4ZSeries)
  let E6C : PowerSeries ℂ := PowerSeries.map (Int.castRingHom ℂ) E6ZSeries
  let cSerre : ℕ → ℂ := fun m => (m : ℂ) * PowerSeries.coeff (R := ℂ) m E4C -
    ((4 : ℂ) * (12 : ℂ)⁻¹) * PowerSeries.coeff (R := ℂ) m E2E4C
  have hSerreHasSum : ∀ τ : ℍ,
      HasSum (fun m : ℕ => cSerre m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (serreDerivativeE4ModularForm τ) := by
    intro τ
    let q := Function.Periodic.qParam 1 (τ : ℂ)
    have hD : HasSum (fun m : ℕ =>
        (m : ℂ) * PowerSeries.coeff (R := ℂ) m E4C * q ^ m)
        (Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ) τ) := by
      simpa [E4C, q, map_E4ZSeries] using E4_normalizedDeriv_qExpansion_hasSum τ
    have hprod : HasSum (fun m : ℕ =>
        PowerSeries.coeff (R := ℂ) m E2E4C * q ^ m)
        (EisensteinSeries.E2 τ * E4 τ) := by
      simpa [E2E4C, q] using E2E4ZSeries_complex_hasSum τ
    have hscaled := HasSum.mul_left ((4 : ℂ) * (12 : ℂ)⁻¹) hprod
    have hsub := hD.sub hscaled
    convert hsub using 1
    · ext m
      simp [cSerre, q, smul_eq_mul, mul_assoc]
      ring
    · change Derivative.serreDerivative (4 : ℂ) (E4 : ℍ → ℂ) τ =
        Derivative.normalizedDerivOfComplex (E4 : ℍ → ℂ) τ -
          (4 : ℂ) * (12 : ℂ)⁻¹ * (EisensteinSeries.E2 τ * E4 τ)
      simp [Derivative.serreDerivative, mul_assoc]
  let cE6 : ℕ → ℂ := fun m =>
    (-(1 / 3 : ℂ)) * PowerSeries.coeff (R := ℂ) m E6C
  have hE6HasSum : ∀ τ : ℍ,
      HasSum (fun m : ℕ => cE6 m • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
        (serreDerivativeE4ModularForm τ) := by
    intro τ
    let q := Function.Periodic.qParam 1 (τ : ℂ)
    have hE6 : HasSum (fun m : ℕ =>
        PowerSeries.coeff (R := ℂ) m E6C * q ^ m) (E6 τ) := by
      simpa [E6C, q] using E6ZSeries_complex_hasSum τ
    have hscaled := HasSum.mul_left (-(1 / 3 : ℂ)) hE6
    convert hscaled using 1
    · ext m
      simp [cE6, q, smul_eq_mul, mul_assoc]
    · have hfun := congrFun serreDerivative_E4_eq_neg_one_third_smul_E6 τ
      simpa [Pi.smul_apply, smul_eq_mul] using hfun
  have hcoefSerre := ModularFormClass.qExpansion_coeff_unique
    (f := (serreDerivativeE4ModularForm :
      ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 6))
    one_pos ModularFormClass.one_mem_strictPeriods_SL2Z hSerreHasSum n
  have hcoefE6 := ModularFormClass.qExpansion_coeff_unique
    (f := (serreDerivativeE4ModularForm :
      ModularForm (Matrix.SpecialLinearGroup.mapGL ℝ).range 6))
    one_pos ModularFormClass.one_mem_strictPeriods_SL2Z hE6HasSum n
  have h : cSerre n = cE6 n := hcoefSerre.trans hcoefE6.symm
  dsimp [cSerre, cE6, E4C, E2E4C, E6C] at h ⊢
  ring_nf at h ⊢
  linear_combination 3 * h

theorem E4ZSeries_derivative_coeff_identity_Ramanujan (n : ℕ) :
    (3 : ℤ) * ((n : ℤ) * E4CoeffZ n) =
      PowerSeries.coeff (R := ℤ) n (E2ZSeries * E4ZSeries) - E6CoeffZ n := by
  have hc := E4ZSeries_derivative_coeff_identity_complex n
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast]
  simpa [PowerSeries.coeff_map, coeff_E4ZSeries, coeff_E6ZSeries, ← map_mul] using hc

theorem truncCoeffArrayAt_E2E4_eq_E6_add_E4_deriv
    {N n : ℕ} (hn : n < N) :
    truncCoeffArrayAt (E2E4TruncCoeffArray N) n =
      truncCoeffArrayAt (E6TruncCoeffArray N) n +
        (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt (E4TruncCoeffArray N) n := by
  have hram := E4ZSeries_derivative_coeff_identity_Ramanujan n
  have hE2E4Rep := TruncRep.E2E4 N n hn
  have hE2E4Array := ListArrayEq.E2E4 N n hn
  have hE6Array :
      truncCoeffArrayAt (E6TruncCoeffArray N) n = E6CoeffZ n := by
    exact truncCoeffArrayAt_ofFn_of_lt hn
  have hE4Array :
      truncCoeffArrayAt (E4TruncCoeffArray N) n = E4CoeffZ n := by
    exact truncCoeffArrayAt_ofFn_of_lt hn
  rw [hE2E4Rep, hE2E4Array] at hram
  rw [← hE6Array, ← hE4Array] at hram
  ring_nf at hram ⊢
  omega

theorem TruncCoeffArrayModEq.E2E4_of_E4_deriv_relation
    {N p : ℕ} {E4M E6M E2E4M : Array ℤ}
    (hE4 : TruncCoeffArrayModEq N p (E4TruncCoeffArray N) E4M)
    (hE6 : TruncCoeffArrayModEq N p (E6TruncCoeffArray N) E6M)
    (hrel : ∀ n : ℕ, n < N →
      truncCoeffArrayAt E2E4M n ≡
        truncCoeffArrayAt E6M n +
          (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4M n
        [ZMOD (p : ℤ)]) :
    TruncCoeffArrayModEq N p (E2E4TruncCoeffArray N) E2E4M := by
  intro n hn
  rw [truncCoeffArrayAt_E2E4_eq_E6_add_E4_deriv hn]
  have hscale :
      (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt (E4TruncCoeffArray N) n ≡
        (3 : ℤ) * (n : ℤ) * truncCoeffArrayAt E4M n [ZMOD (p : ℤ)] := by
    exact Int.ModEq.mul_left ((3 : ℤ) * (n : ℤ)) (hE4 n hn)
  have hsum := (hE6 n hn).add hscale
  exact hsum.trans (hrel n hn).symm

theorem E4Coeff_convolution_Ramanujan :
    ∀ n : ℕ, n ≠ 0 →
      (3 : ℤ) * ((n : ℤ) * E4CoeffZ n) =
        E4CoeffZ n + (-24 : ℤ) * ∑ k ∈ Finset.range n,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            E4CoeffZ (n - (k + 1)) - E6CoeffZ n := by
  intro n _hn
  have h := E4ZSeries_derivative_coeff_identity_Ramanujan n
  rw [coeff_E2ZSeries_mul] at h
  simp_rw [coeff_E4ZSeries] at h
  exact h

theorem sigma_convolution_of_E4Coeff_convolution
    (hconv : ∀ n : ℕ, n ≠ 0 →
      (3 : ℤ) * ((n : ℤ) * E4CoeffZ n) =
        E4CoeffZ n + (-24 : ℤ) * ∑ k ∈ Finset.range n,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            E4CoeffZ (n - (k + 1)) - E6CoeffZ n) :
    ∀ n : ℕ, n ≠ 0 →
      (21 : ℤ) * (ArithmeticFunction.sigma 5 n : ℤ) =
        ((30 : ℤ) * (n : ℤ) - 10) * (ArithmeticFunction.sigma 3 n : ℤ) +
          240 * ∑ k ∈ Finset.range (n - 1),
            (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
              (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ) +
          (ArithmeticFunction.sigma 1 n : ℤ) := by
  intro n hn
  have hsplit :
      (∑ k ∈ Finset.range n,
          ((ArithmeticFunction.sigma 1 (k + 1) : ℕ) : ℤ) *
            E4CoeffZ (n - (k + 1))) =
        240 * (∑ k ∈ Finset.range (n - 1),
          (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
            (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ)) +
        (ArithmeticFunction.sigma 1 n : ℤ) := by
    rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro k hk
      have hklt : k < n - 1 := Finset.mem_range.mp hk
      have hpos : n - (k + 1) ≠ 0 := by omega
      have harg : n - 1 + 1 - (k + 1) = n - (k + 1) := by omega
      rw [E4CoeffZ]
      rw [harg]
      rw [if_neg hpos]
      ring
    · rw [show n - 1 + 1 = n by omega]
      rw [show n - n = 0 by omega]
      simp [E4CoeffZ]
  have hconvn := hconv n hn
  rw [E4CoeffZ, if_neg hn, E6CoeffZ, if_neg hn] at hconvn
  rw [hsplit] at hconvn
  ring_nf at hconvn ⊢
  linarith

theorem E4ZSeries_derivative_identity_of_sigma_convolution
    (hconv : ∀ n : ℕ, n ≠ 0 →
      (21 : ℤ) * (ArithmeticFunction.sigma 5 n : ℤ) =
        ((30 : ℤ) * (n : ℤ) - 10) * (ArithmeticFunction.sigma 3 n : ℤ) +
          240 * ∑ k ∈ Finset.range (n - 1),
            (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
              (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ) +
          (ArithmeticFunction.sigma 1 n : ℤ)) :
      PowerSeries.C (3 : ℤ) *
          (PowerSeries.X * PowerSeries.derivative ℤ E4ZSeries) =
        E2ZSeries * E4ZSeries - E6ZSeries :=
  E4ZSeries_derivative_identity_of_E4Coeff_convolution
    (E4Coeff_convolution_of_sigma_convolution hconv)

/-- Classical additive divisor-sum convolution behind Ramanujan's
`E₄` derivative identity.

Equivalently, this is the coefficient comparison in
`E₂ * E₄ - E₆ = 3 * q dE₄/dq`.  It is kept as a named mathematical
obligation so the recurrence certificate depends on a precise standard
identity rather than on an opaque computational shortcut. -/
theorem sigma_convolution_E4_Ramanujan :
    ∀ n : ℕ, n ≠ 0 →
      (21 : ℤ) * (ArithmeticFunction.sigma 5 n : ℤ) =
        ((30 : ℤ) * (n : ℤ) - 10) * (ArithmeticFunction.sigma 3 n : ℤ) +
          240 * ∑ k ∈ Finset.range (n - 1),
            (ArithmeticFunction.sigma 1 (k + 1) : ℤ) *
              (ArithmeticFunction.sigma 3 (n - (k + 1)) : ℤ) +
          (ArithmeticFunction.sigma 1 n : ℤ) := by
  exact sigma_convolution_of_E4Coeff_convolution E4Coeff_convolution_Ramanujan

/-- Formal-power-series Ramanujan identity for `E₄`, reduced to the
classical divisor-sum convolution above. -/
theorem E4ZSeries_derivative_identity :
      PowerSeries.C (3 : ℤ) *
          (PowerSeries.X * PowerSeries.derivative ℤ E4ZSeries) =
        E2ZSeries * E4ZSeries - E6ZSeries :=
  E4ZSeries_derivative_identity_of_sigma_convolution
    sigma_convolution_E4_Ramanujan

theorem phi41LevelOneDenseRow_derivative_identity_of_base
    (j : ℕ) (hj : j ≤ 42)
    (hE4cubed :
      E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ (E4ZSeries ^ 3)) =
        (E2ZSeries * E4ZSeries - E6ZSeries) * (E4ZSeries ^ 3))
    (hDelta :
      PowerSeries.X * PowerSeries.derivative ℤ deltaEulerSeriesZ =
        E2ZSeries * deltaEulerSeriesZ) :
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)) := by
  let C : PowerSeries ℤ := E4ZSeries ^ 3
  let D : PowerSeries ℤ := deltaEulerSeriesZ
  let A : PowerSeries ℤ := E2ZSeries * E4ZSeries - E6ZSeries
  let k : ℕ := 42 - j
  have hk_cast :
      (k : PowerSeries ℤ) = PowerSeries.C ((42 : ℤ) - (j : ℤ)) := by
    have hk_int : ((k : ℕ) : ℤ) = (42 : ℤ) - (j : ℤ) := by
      dsimp [k]
      omega
    calc
      (k : PowerSeries ℤ) = PowerSeries.C ((k : ℕ) : ℤ) := by simp
      _ = PowerSeries.C ((42 : ℤ) - (j : ℤ)) := by rw [hk_int]
  have hj_cast : (j : PowerSeries ℤ) = PowerSeries.C (j : ℤ) := by simp
  change E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ (C ^ j * D ^ k)) =
    (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
      PowerSeries.C (j : ℤ) * E6ZSeries) * (C ^ j * D ^ k)
  have hC : E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ C) = A * C := by
    simpa [C, A] using hE4cubed
  have hD : PowerSeries.X * PowerSeries.derivative ℤ D = E2ZSeries * D := by
    simpa [D] using hDelta
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_pow]
  calc
    E4ZSeries * (PowerSeries.X *
        (C ^ j * ((↑k : PowerSeries ℤ) * D ^ (k - 1) * PowerSeries.derivative ℤ D) +
          D ^ k * ((↑j : PowerSeries ℤ) * C ^ (j - 1) * PowerSeries.derivative ℤ C)))
        =
      (↑j : PowerSeries ℤ) * C ^ (j - 1) * D ^ k *
          (E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ C)) +
        (↑k : PowerSeries ℤ) * C ^ j * D ^ (k - 1) * E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ D) := by
        ring
    _ =
      (↑j : PowerSeries ℤ) * C ^ (j - 1) * D ^ k * (A * C) +
        (↑k : PowerSeries ℤ) * C ^ j * D ^ (k - 1) * E4ZSeries *
          (E2ZSeries * D) := by
        rw [hC, hD]
    _ =
      PowerSeries.C (j : ℤ) * A * (C ^ j * D ^ k) +
        PowerSeries.C ((42 : ℤ) - (j : ℤ)) *
          (E2ZSeries * E4ZSeries) * (C ^ j * D ^ k) := by
        rw [← hj_cast, ← hk_cast]
        rw [natCast_mul_pow_pred_mul_term_left C D A j k]
        rw [show (↑k : PowerSeries ℤ) * C ^ j * D ^ (k - 1) * E4ZSeries *
            (E2ZSeries * D) =
          (↑k : PowerSeries ℤ) * C ^ j * D ^ (k - 1) *
            (E2ZSeries * E4ZSeries) * D by ring]
        rw [natCast_mul_pow_pred_mul_term_right C D (E2ZSeries * E4ZSeries) j k]
    _ =
      (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
        PowerSeries.C (j : ℤ) * E6ZSeries) * (C ^ j * D ^ k) := by
        rw [show A = E2ZSeries * E4ZSeries - E6ZSeries by rfl]
        rw [show PowerSeries.C ((42 : ℤ) - (j : ℤ)) =
            PowerSeries.C (42 : ℤ) - PowerSeries.C (j : ℤ) by simp]
        ring

theorem truncCoeffAt_phi41LevelOneDenseRowsList_eq_mul_recurrence_of_derivative_identity
    {N j n : ℕ} (hj : j ≤ 42) (hn : n < N) (hval : 42 - j < n)
    (hderiv :
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    (((n - (42 - j) : ℕ) : ℤ)) *
        truncCoeffAt ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)) n =
      sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
            (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
          truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
            truncCoeffAt
              ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N))
              (n - a)) := by
  rw [phi41LevelOneDenseRowsList_getD_of_le N hj]
  exact
    truncCoeffAt_phi41DenseRow_mul_recurrence_of_derivative_identity
      (N := N) (j := j) (n := n)
      (f := ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)))
      (row := mulTruncCoeffList N
        (powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j)
        (powTruncCoeffList N (deltaEulerTruncCoeffList N) (42 - j)))
      hj hn hval (TruncRep.phi41LevelOneDenseRowExpr N j) hderiv

theorem truncCoeffAt_phi41LevelOneDenseRowsList_eq_recurrence_of_derivative_identity
    {N j n : ℕ} (hj : j ≤ 42) (hn : n < N) (hval : 42 - j < n)
    (hderiv :
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    truncCoeffAt ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)) n =
      (sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
            (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
          truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
            truncCoeffAt
              ((phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N))
              (n - a))) /
        (((n - (42 - j) : ℕ) : ℤ)) := by
  rw [phi41LevelOneDenseRowsList_getD_of_le N hj]
  exact
    truncCoeffAt_phi41DenseRow_recurrence_of_derivative_identity
      (N := N) (j := j) (n := n)
      (f := ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)))
      (row := mulTruncCoeffList N
        (powTruncCoeffList N (powTruncCoeffList N (E4TruncCoeffList N) 3) j)
        (powTruncCoeffList N (deltaEulerTruncCoeffList N) (42 - j)))
      hj hn hval (TruncRep.phi41LevelOneDenseRowExpr N j) hderiv

theorem truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_mul_recurrence_of_derivative_identity
    {N j n : ℕ} (hj : j ≤ 42) (hn : n < N) (hval : 42 - j < n)
    (hderiv :
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    (((n - (42 - j) : ℕ) : ℤ)) *
        truncCoeffArrayAt
          (phi41QRecurrenceRowArray N j
            (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N)) n =
      sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * truncCoeffArrayAt (E2E4TruncCoeffArray N) a -
            (j : ℤ) * truncCoeffArrayAt (E6TruncCoeffArray N) a) -
          truncCoeffArrayAt (E4TruncCoeffArray N) a * ((n - a : ℕ) : ℤ)) *
            truncCoeffArrayAt
              (phi41QRecurrenceRowArray N j
                (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N))
              (n - a)) := by
  let rowL := (phi41LevelOneDenseRowsList N).getD j (zeroTruncCoeffList N)
  let rowA :=
    phi41QRecurrenceRowArray N j
      (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N)
  have hLA : ListArrayEq N rowL rowA := by
    exact ListArrayEq.of_phi41QRecurrence
      (N := N) (j := j)
      (rowL := rowL)
      (E4L := E4TruncCoeffList N) (E6L := E6TruncCoeffList N)
      (E2E4L := E2E4TruncCoeffList N)
      (E4A := E4TruncCoeffArray N) (E6A := E6TruncCoeffArray N)
      (E2E4A := E2E4TruncCoeffArray N)
      (ListArrayEq.E4 N) (ListArrayEq.E6 N) (ListArrayEq.E2E4 N)
      (by
        intro m hm hmv
        simpa [rowL] using
          truncCoeffAt_phi41LevelOneDenseRowsList_eq_zero_of_lt_valuation
            (N := N) (j := j) hj hm hmv)
      (by
        intro m hm hmv
        simpa [rowL] using
          truncCoeffAt_phi41LevelOneDenseRowsList_eq_one_of_eq_valuation
            (N := N) (j := j) hj hm hmv)
      (by
        intro m hm hmv
        simpa [rowL] using
          truncCoeffAt_phi41LevelOneDenseRowsList_eq_recurrence_of_derivative_identity
            (N := N) (j := j) hj hm hmv hderiv)
  have hmul :=
    truncCoeffAt_phi41LevelOneDenseRowsList_eq_mul_recurrence_of_derivative_identity
      (N := N) (j := j) hj hn hval hderiv
  calc
    (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffArrayAt rowA n
        = (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffAt rowL n := by
          rw [hLA n hn]
    _ =
        sumRangeFromZ 1 n (fun a =>
          (((42 : ℤ) * truncCoeffAt (E2E4TruncCoeffList N) a -
              (j : ℤ) * truncCoeffAt (E6TruncCoeffList N) a) -
            truncCoeffAt (E4TruncCoeffList N) a * ((n - a : ℕ) : ℤ)) *
              truncCoeffAt rowL (n - a)) := by
          simpa [rowL] using hmul
    _ =
        sumRangeFromZ 1 n (fun a =>
          (((42 : ℤ) * truncCoeffArrayAt (E2E4TruncCoeffArray N) a -
              (j : ℤ) * truncCoeffArrayAt (E6TruncCoeffArray N) a) -
            truncCoeffArrayAt (E4TruncCoeffArray N) a * ((n - a : ℕ) : ℤ)) *
              truncCoeffArrayAt rowA (n - a)) := by
          apply sumRangeFromZ_congr
          intro a ha1 ha2
          have haN : a < N := by omega
          have hidxN : n - a < N := by omega
          rw [(ListArrayEq.E2E4 N) a haN,
            (ListArrayEq.E6 N) a haN,
            (ListArrayEq.E4 N) a haN,
            hLA (n - a) hidxN]

theorem TruncCoeffArrayModEq.phi41QRecurrenceRow_of_mod_mul_recurrence
    {N p j : ℕ} {rowM E4M E6M E2E4M : Array ℤ}
    (hp : Nat.Prime p) (hpN : N < p) (hj : j ≤ 42)
    (hE4 : TruncCoeffArrayModEq N p (E4TruncCoeffArray N) E4M)
    (hE6 : TruncCoeffArrayModEq N p (E6TruncCoeffArray N) E6M)
    (hE2E4 : TruncCoeffArrayModEq N p (E2E4TruncCoeffArray N) E2E4M)
    (hzero : ∀ n : ℕ, n < N → n < 42 - j →
      truncCoeffArrayAt rowM n ≡ 0 [ZMOD (p : ℤ)])
    (hone : ∀ n : ℕ, n < N → n = 42 - j →
      truncCoeffArrayAt rowM n ≡ 1 [ZMOD (p : ℤ)])
    (hrec : ∀ n : ℕ, n < N → 42 - j < n →
      (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffArrayAt rowM n ≡
        sumRangeFromZ 1 n (fun a =>
          (((42 : ℤ) * truncCoeffArrayAt E2E4M a -
              (j : ℤ) * truncCoeffArrayAt E6M a) -
            truncCoeffArrayAt E4M a * ((n - a : ℕ) : ℤ)) *
              truncCoeffArrayAt rowM (n - a)) [ZMOD (p : ℤ)])
    (hderiv :
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    TruncCoeffArrayModEq N p
      (phi41QRecurrenceRowArray N j
        (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N))
      rowM := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hlt : n < 42 - j
      · rw [truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_zero_of_lt_valuation
          (N := N) (j := j)
          (E4 := E4TruncCoeffArray N) (E6 := E6TruncCoeffArray N)
          (E2E4 := E2E4TruncCoeffArray N) hn hlt]
        exact (hzero n hn hlt).symm
      · by_cases heq : n = 42 - j
        · rw [truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_one_of_eq_valuation
            (N := N) (j := j)
            (E4 := E4TruncCoeffArray N) (E6 := E6TruncCoeffArray N)
            (E2E4 := E2E4TruncCoeffArray N) hn heq]
          exact (hone n hn heq).symm
        · have hgt : 42 - j < n := by omega
          let rowA :=
            phi41QRecurrenceRowArray N j
              (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N)
          let d : ℤ := ((n - (42 - j) : ℕ) : ℤ)
          let S_A : ℤ := sumRangeFromZ 1 n (fun a =>
            (((42 : ℤ) * truncCoeffArrayAt (E2E4TruncCoeffArray N) a -
                (j : ℤ) * truncCoeffArrayAt (E6TruncCoeffArray N) a) -
              truncCoeffArrayAt (E4TruncCoeffArray N) a * ((n - a : ℕ) : ℤ)) *
                truncCoeffArrayAt rowA (n - a))
          let S_M : ℤ := sumRangeFromZ 1 n (fun a =>
            (((42 : ℤ) * truncCoeffArrayAt E2E4M a -
                (j : ℤ) * truncCoeffArrayAt E6M a) -
              truncCoeffArrayAt E4M a * ((n - a : ℕ) : ℤ)) *
                truncCoeffArrayAt rowM (n - a))
          have hmulA : d * truncCoeffArrayAt rowA n = S_A := by
            simpa [rowA, d, S_A] using
              truncCoeffArrayAt_phi41QRecurrenceRowArray_eq_mul_recurrence_of_derivative_identity
                (N := N) (j := j) (n := n) hj hn hgt hderiv
          have hS : S_A ≡ S_M [ZMOD (p : ℤ)] := by
            apply sumRangeFromZ_modEq
            intro a ha1 ha2
            have haN : a < N := by omega
            have hidxlt : n - a < n := by omega
            have hidxN : n - a < N := by omega
            have hcoef :
                (((42 : ℤ) * truncCoeffArrayAt (E2E4TruncCoeffArray N) a -
                    (j : ℤ) * truncCoeffArrayAt (E6TruncCoeffArray N) a) -
                  truncCoeffArrayAt (E4TruncCoeffArray N) a *
                    ((n - a : ℕ) : ℤ)) ≡
                  (((42 : ℤ) * truncCoeffArrayAt E2E4M a -
                    (j : ℤ) * truncCoeffArrayAt E6M a) -
                  truncCoeffArrayAt E4M a *
                    ((n - a : ℕ) : ℤ)) [ZMOD (p : ℤ)] := by
              exact
                ((Int.ModEq.mul_left (42 : ℤ) (hE2E4 a haN)).sub
                  (Int.ModEq.mul_left (j : ℤ) (hE6 a haN))).sub
                    ((hE4 a haN).mul (Int.ModEq.refl ((n - a : ℕ) : ℤ)))
            exact hcoef.mul (ih (n - a) hidxlt hidxN)
          have hmulM : d * truncCoeffArrayAt rowM n ≡ S_M [ZMOD (p : ℤ)] := by
            simpa [d, S_M] using hrec n hn hgt
          have hmul :
              d * truncCoeffArrayAt rowA n ≡
                d * truncCoeffArrayAt rowM n [ZMOD (p : ℤ)] := by
            exact (by rw [hmulA] : d * truncCoeffArrayAt rowA n ≡ S_A [ZMOD (p : ℤ)]).trans
              (hS.trans hmulM.symm)
          exact int_modEq_cancel_mul_left_of_coprime
            (P := (p : ℤ)) (d := d)
            (by exact_mod_cast hp.pos)
            (by
              simpa [d] using
                phi41QRecurrence_denominator_coprime_of_prime_gt
                  (p := p) (N := N) (j := j) (n := n) hp hpN hn hgt)
            hmul

def phi41QRecurrenceRowModCertificate
    (N p j : ℕ) (E4 E6 E2E4 row : Array ℤ) : Bool :=
  (List.range N).all (fun n =>
    if n < 42 - j then
      intCoeffModEq p (truncCoeffArrayAt row n) 0
    else if n = 42 - j then
      intCoeffModEq p (truncCoeffArrayAt row n) 1
    else
      intCoeffModEq p
        ((((n - (42 - j) : ℕ) : ℤ)) * truncCoeffArrayAt row n)
        (sumRangeFromZ 1 n (fun a =>
          (((42 : ℤ) * truncCoeffArrayAt E2E4 a -
              (j : ℤ) * truncCoeffArrayAt E6 a) -
            truncCoeffArrayAt E4 a * ((n - a : ℕ) : ℤ)) *
              truncCoeffArrayAt row (n - a))))

theorem phi41QRecurrenceRowModCertificate_zero
    {N p j : ℕ} {E4 E6 E2E4 row : Array ℤ}
    (hcert : phi41QRecurrenceRowModCertificate N p j E4 E6 E2E4 row = true)
    {n : ℕ} (hn : n < N) (hnv : n < 42 - j) :
    truncCoeffArrayAt row n ≡ 0 [ZMOD (p : ℤ)] := by
  unfold phi41QRecurrenceRowModCertificate at hcert
  have hnmem : n ∈ List.range N := by
    simpa using List.mem_range.mpr hn
  have hentry := List.all_eq_true.mp hcert n hnmem
  exact int_modEq_of_intCoeffModEq (by simpa [hnv] using hentry)

theorem phi41QRecurrenceRowModCertificate_one
    {N p j : ℕ} {E4 E6 E2E4 row : Array ℤ}
    (hcert : phi41QRecurrenceRowModCertificate N p j E4 E6 E2E4 row = true)
    {n : ℕ} (hn : n < N) (hnv : n = 42 - j) :
    truncCoeffArrayAt row n ≡ 1 [ZMOD (p : ℤ)] := by
  unfold phi41QRecurrenceRowModCertificate at hcert
  have hnmem : n ∈ List.range N := by
    simpa using List.mem_range.mpr hn
  have hentry := List.all_eq_true.mp hcert n hnmem
  have hnotlt : ¬n < 42 - j := by omega
  exact int_modEq_of_intCoeffModEq (by simpa [hnotlt, hnv] using hentry)

theorem phi41QRecurrenceRowModCertificate_rec
    {N p j : ℕ} {E4 E6 E2E4 row : Array ℤ}
    (hcert : phi41QRecurrenceRowModCertificate N p j E4 E6 E2E4 row = true)
    {n : ℕ} (hn : n < N) (hval : 42 - j < n) :
    (((n - (42 - j) : ℕ) : ℤ)) * truncCoeffArrayAt row n ≡
      sumRangeFromZ 1 n (fun a =>
        (((42 : ℤ) * truncCoeffArrayAt E2E4 a -
            (j : ℤ) * truncCoeffArrayAt E6 a) -
          truncCoeffArrayAt E4 a * ((n - a : ℕ) : ℤ)) *
            truncCoeffArrayAt row (n - a)) [ZMOD (p : ℤ)] := by
  unfold phi41QRecurrenceRowModCertificate at hcert
  have hnmem : n ∈ List.range N := by
    simpa using List.mem_range.mpr hn
  have hentry := List.all_eq_true.mp hcert n hnmem
  have hnotlt : ¬n < 42 - j := by omega
  have hneq : ¬n = 42 - j := by omega
  exact int_modEq_of_intCoeffModEq (by simpa [hnotlt, hneq] using hentry)

def phi41QRecurrenceRowsModCertificate
    (N p : ℕ) (rows : Array (Array ℤ)) : Bool :=
  (List.range 43).all (fun j =>
    phi41QRecurrenceRowModCertificate N p j
      (E4TruncCoeffArray N) (E6TruncCoeffArray N)
      (E2E4TruncCoeffArray N)
      (rows.getD j (zeroTruncCoeffArray N)))

def phi41QRecurrenceRowsModCertificateWithCoeffArrays
    (N p : ℕ) (E4 E6 E2E4 : Array ℤ)
    (rows : Array (Array ℤ)) : Bool :=
  (List.range 43).all (fun j =>
    phi41QRecurrenceRowModCertificate N p j E4 E6 E2E4
      (rows.getD j (zeroTruncCoeffArray N)))

def phi41QRecurrenceRowModCertificateChunk
    (N p j start len : ℕ) (E4 E6 E2E4 row : Array ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < N then
      if n < 42 - j then
        intCoeffModEq p (truncCoeffArrayAt row n) 0
      else if n = 42 - j then
        intCoeffModEq p (truncCoeffArrayAt row n) 1
      else
        intCoeffModEq p
          ((((n - (42 - j) : ℕ) : ℤ)) * truncCoeffArrayAt row n)
          (sumRangeFromZ 1 n (fun a =>
            (((42 : ℤ) * truncCoeffArrayAt E2E4 a -
                (j : ℤ) * truncCoeffArrayAt E6 a) -
              truncCoeffArrayAt E4 a * ((n - a : ℕ) : ℤ)) *
                truncCoeffArrayAt row (n - a)))
    else
      true)

def phi41QRecurrenceRowFnModCertificateChunk
    (N p j start len : ℕ) (E4 E6 E2E4 row : ℕ → ℤ) : Bool :=
  (List.range len).all (fun offset =>
    let n := start + offset
    if _ : n < N then
      if n < 42 - j then
        intCoeffModEq p (row n) 0
      else if n = 42 - j then
        intCoeffModEq p (row n) 1
      else
        intCoeffModEq p
          ((((n - (42 - j) : ℕ) : ℤ)) * row n)
          (sumRangeFromZ 1 n (fun a =>
            (((42 : ℤ) * E2E4 a -
                (j : ℤ) * E6 a) -
              E4 a * ((n - a : ℕ) : ℤ)) *
                row (n - a)))
    else
      true)

theorem phi41QRecurrenceRowModCertificate_of_chunks
    {N p j chunkSize numChunks : ℕ} {E4 E6 E2E4 row : Array ℤ}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41QRecurrenceRowModCertificateChunk N p j (c * chunkSize) chunkSize
        E4 E6 E2E4 row = true) :
    phi41QRecurrenceRowModCertificate N p j E4 E6 E2E4 row = true := by
  unfold phi41QRecurrenceRowModCertificate
  apply List.all_eq_true.mpr
  intro n hnmem
  have hn : n < N := List.mem_range.mp hnmem
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
  have hchunk := hchunks c hc_lt
  unfold phi41QRecurrenceRowModCertificateChunk at hchunk
  let offset := n % chunkSize
  have hoffset_lt : offset < chunkSize := by
    dsimp [offset, c]
    exact Nat.mod_lt n hchunkPos
  have hoffset_mem : offset ∈ List.range chunkSize := by
    exact List.mem_range.mpr hoffset_lt
  have hentry := List.all_eq_true.mp hchunk offset hoffset_mem
  have hn_eq : c * chunkSize + offset = n := by
    dsimp [offset, c]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n chunkSize
  have hentry_n :
      (if n < N then
        if n < 42 - j then
          intCoeffModEq p (truncCoeffArrayAt row n) 0
        else if n = 42 - j then
          intCoeffModEq p (truncCoeffArrayAt row n) 1
        else
          intCoeffModEq p
            ((((n - (42 - j) : ℕ) : ℤ)) * truncCoeffArrayAt row n)
            (sumRangeFromZ 1 n (fun a =>
              (((42 : ℤ) * truncCoeffArrayAt E2E4 a -
                  (j : ℤ) * truncCoeffArrayAt E6 a) -
                truncCoeffArrayAt E4 a * ((n - a : ℕ) : ℤ)) *
                  truncCoeffArrayAt row (n - a)))
       else true) = true := by
    simpa [hn_eq] using hentry
  by_cases hlt : n < 42 - j
  · simpa [hn, hlt] using hentry_n
  · by_cases heq : n = 42 - j
    · have hidx : 42 - j < N := by
        simpa [heq] using hn
      simpa [hn, hidx, hlt, heq] using hentry_n
    · simpa [hn, hlt, heq] using hentry_n

theorem phi41QRecurrenceRowFnModCertificateChunk_of_entries
    {N p j start len : ℕ} {E4 E6 E2E4 row : ℕ → ℤ}
    (hentries : ∀ offset : ℕ, offset < len →
      (let n := start + offset
       if _ : n < N then
         if n < 42 - j then
           intCoeffModEq p (row n) 0
         else if n = 42 - j then
           intCoeffModEq p (row n) 1
         else
           intCoeffModEq p
             ((((n - (42 - j) : ℕ) : ℤ)) * row n)
             (sumRangeFromZ 1 n (fun a =>
               (((42 : ℤ) * E2E4 a -
                   (j : ℤ) * E6 a) -
                 E4 a * ((n - a : ℕ) : ℤ)) *
                   row (n - a)))
       else
         true) = true) :
    phi41QRecurrenceRowFnModCertificateChunk
      N p j start len E4 E6 E2E4 row = true := by
  unfold phi41QRecurrenceRowFnModCertificateChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  exact hentries offset (List.mem_range.mp hoffsetMem)

theorem phi41QRecurrenceRowModCertificateChunk_of_fn_chunk
    {N p j start len : ℕ} {E4 E6 E2E4 row : ℕ → ℤ}
    (hchunk :
      phi41QRecurrenceRowFnModCertificateChunk
        N p j start len E4 E6 E2E4 row = true) :
    phi41QRecurrenceRowModCertificateChunk N p j start len
      (truncCoeffArrayOfFn N E4)
      (truncCoeffArrayOfFn N E6)
      (truncCoeffArrayOfFn N E2E4)
      (truncCoeffArrayOfFn N row) = true := by
  unfold phi41QRecurrenceRowFnModCertificateChunk at hchunk
  unfold phi41QRecurrenceRowModCertificateChunk
  apply List.all_eq_true.mpr
  intro offset hoffsetMem
  have hentry := List.all_eq_true.mp hchunk offset hoffsetMem
  let n := start + offset
  by_cases hn : n < N
  · have hrow : truncCoeffArrayAt (truncCoeffArrayOfFn N row) n = row n :=
      truncCoeffArrayAt_ofFn_of_lt hn
    by_cases hlt : n < 42 - j
    · have hentry' : intCoeffModEq p (row n) 0 = true := by
        simpa [n, hn, hlt] using hentry
      have htarget :
          intCoeffModEq p
            (truncCoeffArrayAt (truncCoeffArrayOfFn N row) n) 0 = true := by
        rw [hrow]
        exact hentry'
      simpa [n, hn, hlt] using htarget
    · by_cases heq : n = 42 - j
      · have hidx : 42 - j < N := by
          simpa [heq] using hn
        have hentry' : intCoeffModEq p (row n) 1 = true := by
          simpa [n, hn, hlt, heq, hidx] using hentry
        have htarget :
            intCoeffModEq p
              (truncCoeffArrayAt (truncCoeffArrayOfFn N row) n) 1 = true := by
          rw [hrow]
          exact hentry'
        simpa [n, hn, hlt, heq, hidx] using htarget
      · have hsum :
            (sumRangeFromZ 1 n fun a =>
              (((42 : ℤ) *
                    truncCoeffArrayAt (truncCoeffArrayOfFn N E2E4) a -
                  (j : ℤ) *
                    truncCoeffArrayAt (truncCoeffArrayOfFn N E6) a) -
                truncCoeffArrayAt (truncCoeffArrayOfFn N E4) a *
                  ((n - a : ℕ) : ℤ)) *
                  truncCoeffArrayAt (truncCoeffArrayOfFn N row) (n - a)) =
            (sumRangeFromZ 1 n fun a =>
              (((42 : ℤ) * E2E4 a -
                  (j : ℤ) * E6 a) -
                E4 a * ((n - a : ℕ) : ℤ)) *
                  row (n - a)) := by
          apply sumRangeFromZ_congr
          intro a ha1 ha2
          have haN : a < N := by omega
          have hnaN : n - a < N := by omega
          rw [truncCoeffArrayAt_ofFn_of_lt haN,
            truncCoeffArrayAt_ofFn_of_lt haN,
            truncCoeffArrayAt_ofFn_of_lt haN,
            truncCoeffArrayAt_ofFn_of_lt hnaN]
        have hentry' :
            intCoeffModEq p
              ((((n - (42 - j) : ℕ) : ℤ)) * row n)
              (sumRangeFromZ 1 n fun a =>
                (((42 : ℤ) * E2E4 a -
                    (j : ℤ) * E6 a) -
                  E4 a * ((n - a : ℕ) : ℤ)) *
                    row (n - a)) = true := by
          simpa [n, hn, hlt, heq] using hentry
        have htarget :
            intCoeffModEq p
              ((((n - (42 - j) : ℕ) : ℤ)) *
                truncCoeffArrayAt (truncCoeffArrayOfFn N row) n)
              (sumRangeFromZ 1 n fun a =>
                (((42 : ℤ) *
                      truncCoeffArrayAt (truncCoeffArrayOfFn N E2E4) a -
                    (j : ℤ) *
                      truncCoeffArrayAt (truncCoeffArrayOfFn N E6) a) -
                  truncCoeffArrayAt (truncCoeffArrayOfFn N E4) a *
                    ((n - a : ℕ) : ℤ)) *
                    truncCoeffArrayAt (truncCoeffArrayOfFn N row) (n - a)) =
                true := by
          rw [hrow, hsum]
          exact hentry'
        simpa [n, hn, hlt, heq] using htarget
  · simp [n, hn]

def phi41QRecurrenceRowsModCertificateChunked
    (N p chunkSize numChunks : ℕ) (rows : Array (Array ℤ)) : Bool :=
  (List.range 43).all (fun j =>
    (List.range numChunks).all (fun c =>
      phi41QRecurrenceRowModCertificateChunk N p j (c * chunkSize) chunkSize
        (E4TruncCoeffArray N) (E6TruncCoeffArray N)
        (E2E4TruncCoeffArray N)
        (rows.getD j (zeroTruncCoeffArray N))))

theorem phi41QRecurrenceRowsModCertificate_of_chunked
    {N p chunkSize numChunks : ℕ} {rows : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunked : phi41QRecurrenceRowsModCertificateChunked
      N p chunkSize numChunks rows = true) :
    phi41QRecurrenceRowsModCertificate N p rows = true := by
  unfold phi41QRecurrenceRowsModCertificate
  apply List.all_eq_true.mpr
  intro j hjmem
  have hjlt : j < 43 := List.mem_range.mp hjmem
  unfold phi41QRecurrenceRowsModCertificateChunked at hchunked
  have hrowChunks := List.all_eq_true.mp hchunked j hjmem
  apply phi41QRecurrenceRowModCertificate_of_chunks hcover
  intro c hc
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc
  exact List.all_eq_true.mp hrowChunks c hcmem

def phi41QRecurrenceRowsModCertificateChunkedWithCoeffArrays
    (N p chunkSize numChunks : ℕ)
    (E4 E6 E2E4 : Array ℤ) (rows : Array (Array ℤ)) : Bool :=
  (List.range 43).all (fun j =>
    (List.range numChunks).all (fun c =>
      phi41QRecurrenceRowModCertificateChunk N p j (c * chunkSize) chunkSize
        E4 E6 E2E4 (rows.getD j (zeroTruncCoeffArray N))))

theorem phi41QRecurrenceRowsModCertificateWithCoeffArrays_of_chunked
    {N p chunkSize numChunks : ℕ}
    {E4 E6 E2E4 : Array ℤ} {rows : Array (Array ℤ)}
    (hcover : N ≤ chunkSize * numChunks)
    (hchunked : phi41QRecurrenceRowsModCertificateChunkedWithCoeffArrays
      N p chunkSize numChunks E4 E6 E2E4 rows = true) :
    phi41QRecurrenceRowsModCertificateWithCoeffArrays
      N p E4 E6 E2E4 rows = true := by
  unfold phi41QRecurrenceRowsModCertificateWithCoeffArrays
  apply List.all_eq_true.mpr
  intro j hjmem
  unfold phi41QRecurrenceRowsModCertificateChunkedWithCoeffArrays at hchunked
  have hrowChunks := List.all_eq_true.mp hchunked j hjmem
  apply phi41QRecurrenceRowModCertificate_of_chunks hcover
  intro c hc
  have hcmem : c ∈ List.range numChunks := List.mem_range.mpr hc
  exact List.all_eq_true.mp hrowChunks c hcmem

theorem TruncCoeffArrayModEq.phi41QRecurrenceRow_of_fn_mod_certificate_chunks
    {N p j chunkSize numChunks : ℕ}
    {E4M E6M E2E4M rowM : ℕ → ℤ}
    (hp : Nat.Prime p) (hpN : N < p) (hj : j ≤ 42)
    (hcover : N ≤ chunkSize * numChunks)
    (hE4 : ∀ n : ℕ, n < N →
      truncCoeffArrayAt (E4TruncCoeffArray N) n ≡ E4M n [ZMOD (p : ℤ)])
    (hE6 : ∀ n : ℕ, n < N →
      truncCoeffArrayAt (E6TruncCoeffArray N) n ≡ E6M n [ZMOD (p : ℤ)])
    (hE2E4 : ∀ n : ℕ, n < N →
      truncCoeffArrayAt (E2E4TruncCoeffArray N) n ≡ E2E4M n [ZMOD (p : ℤ)])
    (hchunks : ∀ c : ℕ, c < numChunks →
      phi41QRecurrenceRowFnModCertificateChunk
        N p j (c * chunkSize) chunkSize E4M E6M E2E4M rowM = true)
    (hderiv :
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    TruncCoeffArrayModEq N p
      (phi41QRecurrenceRowArray N j
        (E4TruncCoeffArray N) (E6TruncCoeffArray N) (E2E4TruncCoeffArray N))
      (truncCoeffArrayOfFn N rowM) := by
  let E4A := truncCoeffArrayOfFn N E4M
  let E6A := truncCoeffArrayOfFn N E6M
  let E2E4A := truncCoeffArrayOfFn N E2E4M
  let rowA := truncCoeffArrayOfFn N rowM
  have hcert :
      phi41QRecurrenceRowModCertificate N p j E4A E6A E2E4A rowA = true := by
    apply phi41QRecurrenceRowModCertificate_of_chunks hcover
    intro c hc
    simpa [E4A, E6A, E2E4A, rowA] using
      phi41QRecurrenceRowModCertificateChunk_of_fn_chunk (hchunks c hc)
  apply TruncCoeffArrayModEq.phi41QRecurrenceRow_of_mod_mul_recurrence
    (N := N) (p := p) (j := j)
    (rowM := rowA) (E4M := E4A) (E6M := E6A) (E2E4M := E2E4A)
  · exact hp
  · exact hpN
  · exact hj
  · exact TruncCoeffArrayModEq.of_fn hE4
  · exact TruncCoeffArrayModEq.of_fn hE6
  · exact TruncCoeffArrayModEq.of_fn hE2E4
  · intro n hn hnv
    exact phi41QRecurrenceRowModCertificate_zero hcert hn hnv
  · intro n hn hnv
    exact phi41QRecurrenceRowModCertificate_one hcert hn hnv
  · intro n hn hnv
    exact phi41QRecurrenceRowModCertificate_rec hcert hn hnv
  · exact hderiv

theorem TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_fn_mod_certificate_chunks
    {N p chunkSize numChunks : ℕ}
    {E4M E6M E2E4M : ℕ → ℤ} {rowsM : ℕ → ℕ → ℤ}
    (hp : Nat.Prime p) (hpN : N < p)
    (hcover : N ≤ chunkSize * numChunks)
    (hE4 : ∀ n : ℕ, n < N →
      truncCoeffArrayAt (E4TruncCoeffArray N) n ≡ E4M n [ZMOD (p : ℤ)])
    (hE6 : ∀ n : ℕ, n < N →
      truncCoeffArrayAt (E6TruncCoeffArray N) n ≡ E6M n [ZMOD (p : ℤ)])
    (hE2E4 : ∀ n : ℕ, n < N →
      truncCoeffArrayAt (E2E4TruncCoeffArray N) n ≡ E2E4M n [ZMOD (p : ℤ)])
    (hchunks : ∀ j : ℕ, j ≤ 42 → ∀ c : ℕ, c < numChunks →
      phi41QRecurrenceRowFnModCertificateChunk
        N p j (c * chunkSize) chunkSize E4M E6M E2E4M (rowsM j) = true)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    TruncCoeffArrayTableModEq N 42 p
      (phi41QRecurrenceRowsArray N)
      (phi41QRecurrenceRowsArrayOfFn N rowsM) := by
  intro j hj
  rw [phi41QRecurrenceRowsArray_getD_of_le N hj]
  rw [phi41QRecurrenceRowsArrayOfFn_getD_of_le N rowsM hj]
  exact TruncCoeffArrayModEq.phi41QRecurrenceRow_of_fn_mod_certificate_chunks
    (N := N) (p := p) (j := j)
    (E4M := E4M) (E6M := E6M) (E2E4M := E2E4M)
    (rowM := rowsM j)
    hp hpN hj hcover hE4 hE6 hE2E4 (hchunks j hj) (hderiv j hj)

theorem TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_mul_recurrence
    {N p : ℕ} {rowsM : Array (Array ℤ)}
    {E4M E6M E2E4M : Array ℤ}
    (hp : Nat.Prime p) (hpN : N < p)
    (hE4 : TruncCoeffArrayModEq N p (E4TruncCoeffArray N) E4M)
    (hE6 : TruncCoeffArrayModEq N p (E6TruncCoeffArray N) E6M)
    (hE2E4 : TruncCoeffArrayModEq N p (E2E4TruncCoeffArray N) E2E4M)
    (hzero : ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ, n < N → n < 42 - j →
      truncCoeffArrayAt (rowsM.getD j (zeroTruncCoeffArray N)) n ≡ 0 [ZMOD (p : ℤ)])
    (hone : ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ, n < N → n = 42 - j →
      truncCoeffArrayAt (rowsM.getD j (zeroTruncCoeffArray N)) n ≡ 1 [ZMOD (p : ℤ)])
    (hrec : ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ, n < N → 42 - j < n →
      (((n - (42 - j) : ℕ) : ℤ)) *
          truncCoeffArrayAt (rowsM.getD j (zeroTruncCoeffArray N)) n ≡
        sumRangeFromZ 1 n (fun a =>
          (((42 : ℤ) * truncCoeffArrayAt E2E4M a -
              (j : ℤ) * truncCoeffArrayAt E6M a) -
            truncCoeffArrayAt E4M a * ((n - a : ℕ) : ℤ)) *
              truncCoeffArrayAt (rowsM.getD j (zeroTruncCoeffArray N)) (n - a))
          [ZMOD (p : ℤ)])
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    TruncCoeffArrayTableModEq N 42 p (phi41QRecurrenceRowsArray N) rowsM := by
  intro j hj
  rw [phi41QRecurrenceRowsArray_getD_of_le N hj]
  exact TruncCoeffArrayModEq.phi41QRecurrenceRow_of_mod_mul_recurrence
    (N := N) (p := p) (j := j)
    (rowM := rowsM.getD j (zeroTruncCoeffArray N))
    (E4M := E4M) (E6M := E6M) (E2E4M := E2E4M)
    hp hpN hj hE4 hE6 hE2E4
    (hzero j hj) (hone j hj) (hrec j hj) (hderiv j hj)

theorem TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate
    {N p : ℕ} {rowsM : Array (Array ℤ)}
    (hp : Nat.Prime p) (hpN : N < p)
    (hcert : phi41QRecurrenceRowsModCertificate N p rowsM = true)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    TruncCoeffArrayTableModEq N 42 p (phi41QRecurrenceRowsArray N) rowsM := by
  apply TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_mul_recurrence
    (N := N) (p := p)
    (rowsM := rowsM)
    (E4M := E4TruncCoeffArray N)
    (E6M := E6TruncCoeffArray N)
    (E2E4M := E2E4TruncCoeffArray N)
  · exact hp
  · exact hpN
  · exact TruncCoeffArrayModEq.refl N p _
  · exact TruncCoeffArrayModEq.refl N p _
  · exact TruncCoeffArrayModEq.refl N p _
  · intro j hj n hn hnv
    unfold phi41QRecurrenceRowsModCertificate at hcert
    have hjmem : j ∈ List.range 43 := by
      exact List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp hcert j hjmem
    exact phi41QRecurrenceRowModCertificate_zero hrow hn hnv
  · intro j hj n hn hnv
    unfold phi41QRecurrenceRowsModCertificate at hcert
    have hjmem : j ∈ List.range 43 := by
      exact List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp hcert j hjmem
    exact phi41QRecurrenceRowModCertificate_one hrow hn hnv
  · intro j hj n hn hnv
    unfold phi41QRecurrenceRowsModCertificate at hcert
    have hjmem : j ∈ List.range 43 := by
      exact List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp hcert j hjmem
    exact phi41QRecurrenceRowModCertificate_rec hrow hn hnv
  · exact hderiv

theorem TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate_with_coeff_arrays
    {N p : ℕ} {rowsM : Array (Array ℤ)}
    {E4M E6M E2E4M : Array ℤ}
    (hp : Nat.Prime p) (hpN : N < p)
    (hE4 : TruncCoeffArrayModEq N p (E4TruncCoeffArray N) E4M)
    (hE6 : TruncCoeffArrayModEq N p (E6TruncCoeffArray N) E6M)
    (hE2E4 : TruncCoeffArrayModEq N p (E2E4TruncCoeffArray N) E2E4M)
    (hcert : phi41QRecurrenceRowsModCertificateWithCoeffArrays
      N p E4M E6M E2E4M rowsM = true)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    TruncCoeffArrayTableModEq N 42 p (phi41QRecurrenceRowsArray N) rowsM := by
  apply TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_mul_recurrence
    (N := N) (p := p)
    (rowsM := rowsM)
    (E4M := E4M) (E6M := E6M) (E2E4M := E2E4M)
  · exact hp
  · exact hpN
  · exact hE4
  · exact hE6
  · exact hE2E4
  · intro j hj n hn hnv
    unfold phi41QRecurrenceRowsModCertificateWithCoeffArrays at hcert
    have hjmem : j ∈ List.range 43 := by
      exact List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp hcert j hjmem
    exact phi41QRecurrenceRowModCertificate_zero hrow hn hnv
  · intro j hj n hn hnv
    unfold phi41QRecurrenceRowsModCertificateWithCoeffArrays at hcert
    have hjmem : j ∈ List.range 43 := by
      exact List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp hcert j hjmem
    exact phi41QRecurrenceRowModCertificate_one hrow hn hnv
  · intro j hj n hn hnv
    unfold phi41QRecurrenceRowsModCertificateWithCoeffArrays at hcert
    have hjmem : j ∈ List.range 43 := by
      exact List.mem_range.mpr (by omega)
    have hrow := List.all_eq_true.mp hcert j hjmem
    exact phi41QRecurrenceRowModCertificate_rec hrow hn hnv
  · exact hderiv

theorem TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArray_of_mod_row_tables
    {N p : ℕ} {PCompressedM QM : Array (Array ℤ)}
    (hP : TruncCoeffArrayTableModEq ((N + 40) / 41) 42 p
      (phi41QRecurrenceRowsArray ((N + 40) / 41)) PCompressedM)
    (hQ : TruncCoeffArrayTableModEq N 42 p
      (phi41QRecurrenceRowsArray N) QM) :
    TruncCoeffArrayModEq N p
      (phi41Level41RecurrenceCoeffArray N)
      (phi41Level41RecurrenceCoeffArrayFromRows N ((N + 40) / 41) PCompressedM QM) := by
  let M := (N + 40) / 41
  let coeffs := phi41SparseCoeffMatrixArray
  simpa [phi41Level41RecurrenceCoeffArray,
    phi41Level41RecurrenceCoeffArrayFromRows, M, coeffs] using
    (TruncCoeffArrayModEq.evalSparseCompressedMatrixFromProductTables
      (N := N) (M := M) (p := p)
      (PCompressedA := phi41QRecurrenceRowsArray M)
      (PCompressedB := PCompressedM)
      (QA := phi41QRecurrenceRowsArray N)
      (QB := QM)
      coeffs (by rfl) (by simpa [M] using hP) hQ)

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_row_tables
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hlarge : ∀ p ∈ ps, phi41Level41SturmBound < p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (PCompressedM QM : ℕ → Array (Array ℤ))
    (hPzero : ∀ p ∈ ps, ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ,
      n < (phi41Level41SturmBound + 40) / 41 → n < 42 - j →
        truncCoeffArrayAt
          ((PCompressedM p).getD j
            (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))) n ≡
          0 [ZMOD (p : ℤ)])
    (hPone : ∀ p ∈ ps, ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ,
      n < (phi41Level41SturmBound + 40) / 41 → n = 42 - j →
        truncCoeffArrayAt
          ((PCompressedM p).getD j
            (zeroTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))) n ≡
          1 [ZMOD (p : ℤ)])
    (hPrec : ∀ p ∈ ps, ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ,
      n < (phi41Level41SturmBound + 40) / 41 → 42 - j < n →
        (((n - (42 - j) : ℕ) : ℤ)) *
            truncCoeffArrayAt
              ((PCompressedM p).getD j
                (zeroTruncCoeffArray
                  ((phi41Level41SturmBound + 40) / 41))) n ≡
          sumRangeFromZ 1 n (fun a =>
            (((42 : ℤ) *
                truncCoeffArrayAt
                  (E2E4TruncCoeffArray
                    ((phi41Level41SturmBound + 40) / 41)) a -
                (j : ℤ) *
                  truncCoeffArrayAt
                    (E6TruncCoeffArray
                      ((phi41Level41SturmBound + 40) / 41)) a) -
              truncCoeffArrayAt
                (E4TruncCoeffArray
                  ((phi41Level41SturmBound + 40) / 41)) a *
                ((n - a : ℕ) : ℤ)) *
                truncCoeffArrayAt
                  ((PCompressedM p).getD j
                    (zeroTruncCoeffArray
                      ((phi41Level41SturmBound + 40) / 41))) (n - a))
            [ZMOD (p : ℤ)])
    (hQzero : ∀ p ∈ ps, ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ,
      n < phi41Level41SturmBound → n < 42 - j →
        truncCoeffArrayAt
          ((QM p).getD j (zeroTruncCoeffArray phi41Level41SturmBound)) n ≡
          0 [ZMOD (p : ℤ)])
    (hQone : ∀ p ∈ ps, ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ,
      n < phi41Level41SturmBound → n = 42 - j →
        truncCoeffArrayAt
          ((QM p).getD j (zeroTruncCoeffArray phi41Level41SturmBound)) n ≡
          1 [ZMOD (p : ℤ)])
    (hQrec : ∀ p ∈ ps, ∀ j : ℕ, j ≤ 42 → ∀ n : ℕ,
      n < phi41Level41SturmBound → 42 - j < n →
        (((n - (42 - j) : ℕ) : ℤ)) *
            truncCoeffArrayAt
              ((QM p).getD j
                (zeroTruncCoeffArray phi41Level41SturmBound)) n ≡
          sumRangeFromZ 1 n (fun a =>
            (((42 : ℤ) *
                truncCoeffArrayAt
                  (E2E4TruncCoeffArray phi41Level41SturmBound) a -
                (j : ℤ) *
                  truncCoeffArrayAt
                    (E6TruncCoeffArray phi41Level41SturmBound) a) -
              truncCoeffArrayAt
                (E4TruncCoeffArray phi41Level41SturmBound) a *
                ((n - a : ℕ) : ℤ)) *
                truncCoeffArrayAt
                  ((QM p).getD j
                    (zeroTruncCoeffArray phi41Level41SturmBound)) (n - a))
            [ZMOD (p : ℤ)])
    (hzero : ∀ p ∈ ps,
      truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
        (phi41Level41RecurrenceCoeffArrayFromRows
          phi41Level41SturmBound
          ((phi41Level41SturmBound + 40) / 41)
          (PCompressedM p) (QM p)) = true)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  let K := phi41Level41SturmBound
  let M := (phi41Level41SturmBound + 40) / 41
  have hrel : ∀ p ∈ ps,
      TruncCoeffArrayModEq K p
        (phi41Level41RecurrenceCoeffArray K)
        (phi41Level41RecurrenceCoeffArrayFromRows K M
          (PCompressedM p) (QM p)) := by
    intro p hp
    have hpprime := hprime p hp
    have hpK := hlarge p hp
    have hP :
        TruncCoeffArrayTableModEq M 42 p
          (phi41QRecurrenceRowsArray M) (PCompressedM p) := by
      apply TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_mul_recurrence
        (N := M) (p := p)
        (rowsM := PCompressedM p)
        (E4M := E4TruncCoeffArray M)
        (E6M := E6TruncCoeffArray M)
        (E2E4M := E2E4TruncCoeffArray M)
      · exact hpprime
      · dsimp [M, K]
        omega
      · exact TruncCoeffArrayModEq.refl M p _
      · exact TruncCoeffArrayModEq.refl M p _
      · exact TruncCoeffArrayModEq.refl M p _
      · intro j hj n hn hnv
        simpa [M] using hPzero p hp j hj n hn hnv
      · intro j hj n hn hnv
        simpa [M] using hPone p hp j hj n hn hnv
      · intro j hj n hn hnv
        simpa [M] using hPrec p hp j hj n hn hnv
      · exact hderiv
    have hQ :
        TruncCoeffArrayTableModEq K 42 p
          (phi41QRecurrenceRowsArray K) (QM p) := by
      apply TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_mul_recurrence
        (N := K) (p := p)
        (rowsM := QM p)
        (E4M := E4TruncCoeffArray K)
        (E6M := E6TruncCoeffArray K)
        (E2E4M := E2E4TruncCoeffArray K)
      · exact hpprime
      · exact hpK
      · exact TruncCoeffArrayModEq.refl K p _
      · exact TruncCoeffArrayModEq.refl K p _
      · exact TruncCoeffArrayModEq.refl K p _
      · intro j hj n hn hnv
        simpa [K] using hQzero p hp j hj n hn hnv
      · intro j hj n hn hnv
        simpa [K] using hQone p hp j hj n hn hnv
      · intro j hj n hn hnv
        simpa [K] using hQrec p hp j hj n hn hnv
      · exact hderiv
    simpa [K, M] using
      TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArray_of_mod_row_tables
        (N := K) (p := p)
        (PCompressedM := PCompressedM p) (QM := QM p)
        hP hQ
  change truncCoeffArrayFirstZero K (phi41Level41RecurrenceCoeffArray K) = true
  exact truncCoeffArrayFirstZero_of_crt_bounded_modEq_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB
    (fun p =>
      phi41Level41RecurrenceCoeffArrayFromRows K M (PCompressedM p) (QM p))
    hrel (by
      intro p hp
      simpa [K, M] using hzero p hp)

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_row_table_bools
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hlarge : ∀ p ∈ ps, phi41Level41SturmBound < p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (PCompressedM QM : ℕ → Array (Array ℤ))
    (hPcert : ∀ p ∈ ps,
      phi41QRecurrenceRowsModCertificate
        ((phi41Level41SturmBound + 40) / 41) p (PCompressedM p) = true)
    (hQcert : ∀ p ∈ ps,
      phi41QRecurrenceRowsModCertificate
        phi41Level41SturmBound p (QM p) = true)
    (hzero : ∀ p ∈ ps,
      truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
        (phi41Level41RecurrenceCoeffArrayFromRows
          phi41Level41SturmBound
          ((phi41Level41SturmBound + 40) / 41)
          (PCompressedM p) (QM p)) = true)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  let K := phi41Level41SturmBound
  let M := (phi41Level41SturmBound + 40) / 41
  have hrel : ∀ p ∈ ps,
      TruncCoeffArrayModEq K p
        (phi41Level41RecurrenceCoeffArray K)
        (phi41Level41RecurrenceCoeffArrayFromRows K M
          (PCompressedM p) (QM p)) := by
    intro p hp
    have hpprime := hprime p hp
    have hpK := hlarge p hp
    have hP :
        TruncCoeffArrayTableModEq M 42 p
          (phi41QRecurrenceRowsArray M) (PCompressedM p) := by
      apply TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate
      · exact hpprime
      · dsimp [M, K]
        omega
      · simpa [M] using hPcert p hp
      · exact hderiv
    have hQ :
        TruncCoeffArrayTableModEq K 42 p
          (phi41QRecurrenceRowsArray K) (QM p) := by
      apply TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate
      · exact hpprime
      · exact hpK
      · simpa [K] using hQcert p hp
      · exact hderiv
    simpa [K, M] using
      TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArray_of_mod_row_tables
        (N := K) (p := p)
        (PCompressedM := PCompressedM p) (QM := QM p)
        hP hQ
  change truncCoeffArrayFirstZero K (phi41Level41RecurrenceCoeffArray K) = true
  exact truncCoeffArrayFirstZero_of_crt_bounded_modEq_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB
    (fun p =>
      phi41Level41RecurrenceCoeffArrayFromRows K M (PCompressedM p) (QM p))
    hrel (by
      intro p hp
      simpa [K, M] using hzero p hp)

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_table_modEq_with_final
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (PCompressedM QM : ℕ → Array (Array ℤ))
    (FinalM : ℕ → Array ℤ)
    (hP : ∀ p ∈ ps,
      TruncCoeffArrayTableModEq ((phi41Level41SturmBound + 40) / 41) 42 p
        (phi41QRecurrenceRowsArray
          ((phi41Level41SturmBound + 40) / 41))
        (PCompressedM p))
    (hQ : ∀ p ∈ ps,
      TruncCoeffArrayTableModEq phi41Level41SturmBound 42 p
        (phi41QRecurrenceRowsArray phi41Level41SturmBound)
        (QM p))
    (hFinal : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (phi41Level41RecurrenceCoeffArrayFromRows
          phi41Level41SturmBound
          ((phi41Level41SturmBound + 40) / 41)
          (PCompressedM p) (QM p))
        (FinalM p))
    (hzero : ∀ p ∈ ps,
      truncCoeffArrayFirstZeroMod phi41Level41SturmBound p (FinalM p) = true) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  let K := phi41Level41SturmBound
  let M := (phi41Level41SturmBound + 40) / 41
  have hrel : ∀ p ∈ ps,
      TruncCoeffArrayModEq K p
        (phi41Level41RecurrenceCoeffArray K)
        (FinalM p) := by
    intro p hp
    have hrows :
        TruncCoeffArrayModEq K p
          (phi41Level41RecurrenceCoeffArray K)
          (phi41Level41RecurrenceCoeffArrayFromRows K M
            (PCompressedM p) (QM p)) := by
      simpa [K, M] using
        TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArray_of_mod_row_tables
          (N := K) (p := p)
          (PCompressedM := PCompressedM p) (QM := QM p)
          (by simpa [M] using hP p hp)
          (by simpa [K] using hQ p hp)
    exact hrows.trans (by simpa [K, M] using hFinal p hp)
  change truncCoeffArrayFirstZero K (phi41Level41RecurrenceCoeffArray K) = true
  exact truncCoeffArrayFirstZero_of_crt_bounded_modEq_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB
    FinalM hrel (by
      intro p hp
      simpa [K] using hzero p hp)

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_row_table_bools_with_coeffs
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hlarge : ∀ p ∈ ps, phi41Level41SturmBound < p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (PE4M PE6M PE2E4M QE4M QE6M QE2E4M : ℕ → Array ℤ)
    (PCompressedM QM : ℕ → Array (Array ℤ))
    (hPE4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq ((phi41Level41SturmBound + 40) / 41) p
        (E4TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))
        (PE4M p))
    (hPE6 : ∀ p ∈ ps,
      TruncCoeffArrayModEq ((phi41Level41SturmBound + 40) / 41) p
        (E6TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))
        (PE6M p))
    (hPE2E4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq ((phi41Level41SturmBound + 40) / 41) p
        (E2E4TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))
        (PE2E4M p))
    (hQE4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (E4TruncCoeffArray phi41Level41SturmBound) (QE4M p))
    (hQE6 : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (E6TruncCoeffArray phi41Level41SturmBound) (QE6M p))
    (hQE2E4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (E2E4TruncCoeffArray phi41Level41SturmBound) (QE2E4M p))
    (hPcert : ∀ p ∈ ps,
      phi41QRecurrenceRowsModCertificateWithCoeffArrays
        ((phi41Level41SturmBound + 40) / 41) p
        (PE4M p) (PE6M p) (PE2E4M p) (PCompressedM p) = true)
    (hQcert : ∀ p ∈ ps,
      phi41QRecurrenceRowsModCertificateWithCoeffArrays
        phi41Level41SturmBound p
        (QE4M p) (QE6M p) (QE2E4M p) (QM p) = true)
    (hzero : ∀ p ∈ ps,
      truncCoeffArrayFirstZeroMod phi41Level41SturmBound p
        (phi41Level41RecurrenceCoeffArrayFromRows
          phi41Level41SturmBound
          ((phi41Level41SturmBound + 40) / 41)
          (PCompressedM p) (QM p)) = true)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  let K := phi41Level41SturmBound
  let M := (phi41Level41SturmBound + 40) / 41
  have hrel : ∀ p ∈ ps,
      TruncCoeffArrayModEq K p
        (phi41Level41RecurrenceCoeffArray K)
        (phi41Level41RecurrenceCoeffArrayFromRows K M
          (PCompressedM p) (QM p)) := by
    intro p hp
    have hpprime := hprime p hp
    have hpK := hlarge p hp
    have hP :
        TruncCoeffArrayTableModEq M 42 p
          (phi41QRecurrenceRowsArray M) (PCompressedM p) := by
      apply
        TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate_with_coeff_arrays
      · exact hpprime
      · dsimp [M, K]
        omega
      · simpa [M] using hPE4 p hp
      · simpa [M] using hPE6 p hp
      · simpa [M] using hPE2E4 p hp
      · simpa [M] using hPcert p hp
      · exact hderiv
    have hQ :
        TruncCoeffArrayTableModEq K 42 p
          (phi41QRecurrenceRowsArray K) (QM p) := by
      apply
        TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate_with_coeff_arrays
      · exact hpprime
      · exact hpK
      · simpa [K] using hQE4 p hp
      · simpa [K] using hQE6 p hp
      · simpa [K] using hQE2E4 p hp
      · simpa [K] using hQcert p hp
      · exact hderiv
    simpa [K, M] using
      TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArray_of_mod_row_tables
        (N := K) (p := p)
        (PCompressedM := PCompressedM p) (QM := QM p)
        hP hQ
  change truncCoeffArrayFirstZero K (phi41Level41RecurrenceCoeffArray K) = true
  exact truncCoeffArrayFirstZero_of_crt_bounded_modEq_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB
    (fun p =>
      phi41Level41RecurrenceCoeffArrayFromRows K M (PCompressedM p) (QM p))
    hrel (by
      intro p hp
      simpa [K, M] using hzero p hp)

theorem phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_row_table_bools_with_final
    {ps : List ℕ} (hnodup : ps.Nodup)
    (hprime : ∀ p ∈ ps, Nat.Prime p)
    (hlarge : ∀ p ∈ ps, phi41Level41SturmBound < p) {B : ℕ}
    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →
      |truncCoeffArrayAt
        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤
          (B : ℤ))
    (hB : (B : ℤ) < (ps.prod : ℤ))
    (PE4M PE6M PE2E4M QE4M QE6M QE2E4M : ℕ → Array ℤ)
    (PCompressedM QM : ℕ → Array (Array ℤ))
    (FinalM : ℕ → Array ℤ)
    (hPE4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq ((phi41Level41SturmBound + 40) / 41) p
        (E4TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))
        (PE4M p))
    (hPE6 : ∀ p ∈ ps,
      TruncCoeffArrayModEq ((phi41Level41SturmBound + 40) / 41) p
        (E6TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))
        (PE6M p))
    (hPE2E4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq ((phi41Level41SturmBound + 40) / 41) p
        (E2E4TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))
        (PE2E4M p))
    (hQE4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (E4TruncCoeffArray phi41Level41SturmBound) (QE4M p))
    (hQE6 : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (E6TruncCoeffArray phi41Level41SturmBound) (QE6M p))
    (hQE2E4 : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (E2E4TruncCoeffArray phi41Level41SturmBound) (QE2E4M p))
    (hPcert : ∀ p ∈ ps,
      phi41QRecurrenceRowsModCertificateWithCoeffArrays
        ((phi41Level41SturmBound + 40) / 41) p
        (PE4M p) (PE6M p) (PE2E4M p) (PCompressedM p) = true)
    (hQcert : ∀ p ∈ ps,
      phi41QRecurrenceRowsModCertificateWithCoeffArrays
        phi41Level41SturmBound p
        (QE4M p) (QE6M p) (QE2E4M p) (QM p) = true)
    (hFinal : ∀ p ∈ ps,
      TruncCoeffArrayModEq phi41Level41SturmBound p
        (phi41Level41RecurrenceCoeffArrayFromRows
          phi41Level41SturmBound
          ((phi41Level41SturmBound + 40) / 41)
          (PCompressedM p) (QM p))
        (FinalM p))
    (hzero : ∀ p ∈ ps,
      truncCoeffArrayFirstZeroMod phi41Level41SturmBound p (FinalM p) = true)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  let K := phi41Level41SturmBound
  let M := (phi41Level41SturmBound + 40) / 41
  have hrel : ∀ p ∈ ps,
      TruncCoeffArrayModEq K p
        (phi41Level41RecurrenceCoeffArray K)
        (FinalM p) := by
    intro p hp
    have hpprime := hprime p hp
    have hpK := hlarge p hp
    have hP :
        TruncCoeffArrayTableModEq M 42 p
          (phi41QRecurrenceRowsArray M) (PCompressedM p) := by
      apply
        TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate_with_coeff_arrays
      · exact hpprime
      · dsimp [M, K]
        omega
      · simpa [M] using hPE4 p hp
      · simpa [M] using hPE6 p hp
      · simpa [M] using hPE2E4 p hp
      · simpa [M] using hPcert p hp
      · exact hderiv
    have hQ :
        TruncCoeffArrayTableModEq K 42 p
          (phi41QRecurrenceRowsArray K) (QM p) := by
      apply
        TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_mod_certificate_with_coeff_arrays
      · exact hpprime
      · exact hpK
      · simpa [K] using hQE4 p hp
      · simpa [K] using hQE6 p hp
      · simpa [K] using hQE2E4 p hp
      · simpa [K] using hQcert p hp
      · exact hderiv
    have hrows :
        TruncCoeffArrayModEq K p
          (phi41Level41RecurrenceCoeffArray K)
          (phi41Level41RecurrenceCoeffArrayFromRows K M
            (PCompressedM p) (QM p)) := by
      simpa [K, M] using
        TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArray_of_mod_row_tables
          (N := K) (p := p)
          (PCompressedM := PCompressedM p) (QM := QM p)
          hP hQ
    exact hrows.trans (by simpa [K, M] using hFinal p hp)
  change truncCoeffArrayFirstZero K (phi41Level41RecurrenceCoeffArray K) = true
  exact truncCoeffArrayFirstZero_of_crt_bounded_modEq_certificate
    (list_pairwise_coprime_of_nodup_prime hnodup hprime) hbound hB
    FinalM hrel (by
      intro p hp
      simpa [K] using hzero p hp)

theorem ListArrayTableEq.phi41LevelOneDenseRows_of_derivative_identities
    (N : ℕ)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    ListArrayTableEq N 42
      (phi41LevelOneDenseRowsList N) (phi41QRecurrenceRowsArray N) := by
  apply ListArrayTableEq.phi41LevelOneDenseRows_of_recurrence
  · intro j hj n hn hnv
    exact truncCoeffAt_phi41LevelOneDenseRowsList_eq_zero_of_lt_valuation hj hn hnv
  · intro j hj n hn hnv
    exact truncCoeffAt_phi41LevelOneDenseRowsList_eq_one_of_eq_valuation hj hn hnv
  · intro j hj n hn hval
    exact truncCoeffAt_phi41LevelOneDenseRowsList_eq_recurrence_of_derivative_identity
      hj hn hval (hderiv j hj)

theorem ListArrayEq.phi41Level41CoeffCompressedMatrix_of_derivative_identities
    (N : ℕ)
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :
    ListArrayEq N
      (phi41Level41CoeffListCompressedMatrix N)
      (phi41Level41RecurrenceCoeffArray N) :=
  ListArrayEq.phi41Level41CoeffCompressedMatrix_of_recurrenceRows N
    (ListArrayTableEq.phi41LevelOneDenseRows_of_derivative_identities
      ((N + 40) / 41) hderiv)
    (ListArrayTableEq.phi41LevelOneDenseRows_of_derivative_identities N hderiv)

theorem deltaEulerCoeffZ_eq_deltaRamanujanCoeffSpec_of_recurrence
    (hrec : ∀ n : ℕ,
      deltaEulerCoeffZ (n + 2) =
        ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
          (fun i =>
            deltaEulerCoeffZ i *
              ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ))) /
          ((n + 1 : ℕ) : ℤ)) :
    ∀ n : ℕ, deltaEulerCoeffZ n = deltaRamanujanCoeffSpec n := by
  apply eq_deltaRamanujanCoeffSpec_of_initial_recurrence_sigma
  · exact deltaEulerCoeffZ_zero
  · exact deltaEulerCoeffZ_one
  · exact hrec

theorem ListArrayEq.deltaEulerTruncCoeff_deltaRamanujanCoeffSpec_of_recurrence
    (N : ℕ)
    (hrec : ∀ n : ℕ,
      deltaEulerCoeffZ (n + 2) =
        ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
          (fun i =>
            deltaEulerCoeffZ i *
              ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ))) /
          ((n + 1 : ℕ) : ℤ)) :
    ListArrayEq N (deltaEulerTruncCoeffList N)
      (truncCoeffArrayOfFn N deltaRamanujanCoeffSpec) := by
  intro n hn
  rw [truncCoeffAt_deltaEulerTruncCoeffList_eq_deltaEulerCoeffZ hn]
  rw [deltaEulerCoeffZ_eq_deltaRamanujanCoeffSpec_of_recurrence hrec n]
  rw [← truncCoeffAt_truncCoeffList_of_lt (f := deltaRamanujanCoeffSpec) hn]
  exact ListArrayEq.ofFn N deltaRamanujanCoeffSpec n hn

theorem ListArrayEq.deltaEulerTruncCoeff_deltaRamanujan_of_recurrence
    (N : ℕ)
    (hrec : ∀ n : ℕ,
      deltaEulerCoeffZ (n + 2) =
        ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
          (fun i =>
            deltaEulerCoeffZ i *
              ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ))) /
          ((n + 1 : ℕ) : ℤ)) :
    ListArrayEq N (deltaEulerTruncCoeffList N)
      (deltaRamanujanTruncCoeffArray N) := by
  intro n hn
  rw [truncCoeffAt_deltaEulerTruncCoeffList_eq_deltaEulerCoeffZ hn]
  rw [deltaEulerCoeffZ_eq_deltaRamanujanCoeffSpec_of_recurrence hrec n]
  rw [← truncCoeffAt_deltaRamanujanTruncCoeffList_of_lt hn]
  exact ListArrayEq.deltaRamanujanCoeffSpecArray N n hn

theorem deltaEulerRamanujanEqFirst_of_recurrence
    (N : ℕ)
    (hrec : ∀ n : ℕ,
      deltaEulerCoeffZ (n + 2) =
        ((-24 : ℤ) * sumRangeFromZ 1 (n + 1)
          (fun i =>
            deltaEulerCoeffZ i *
              ((ArithmeticFunction.sigma 1 (n + 2 - i) : ℕ) : ℤ))) /
          ((n + 1 : ℕ) : ℤ)) :
    deltaEulerRamanujanEqFirst N = true :=
  deltaEulerRamanujanEqFirst_of_ListArrayEq N
    (ListArrayEq.deltaEulerTruncCoeff_deltaRamanujan_of_recurrence N hrec)

theorem deltaEulerRamanujanEqFirst_of_derivative_identity
    (N : ℕ)
    (hderiv : PowerSeries.X * PowerSeries.derivative ℤ deltaEulerSeriesZ =
      E2ZSeries * deltaEulerSeriesZ) :
    deltaEulerRamanujanEqFirst N = true :=
  deltaEulerRamanujanEqFirst_of_recurrence N
    (deltaEulerCoeffZ_recurrence_of_derivative_identity hderiv)

/-- Formal Delta logarithmic-derivative identity:
`q dΔ/dq = E₂ Δ` for the Euler-product q-expansion
`Δ = q ∏_{m≥1} (1 - q^m)^24`.

This is the remaining mathematical Delta bridge; once proved, every finite
Euler-vs-Ramanujan coefficient comparison follows uniformly from
`deltaEulerRamanujanEqFirst_of_derivative_identity`. -/
theorem deltaEulerSeriesZ_derivative_identity :
    PowerSeries.X * PowerSeries.derivative ℤ deltaEulerSeriesZ =
      E2ZSeries * deltaEulerSeriesZ := by
  ext d
  rw [coeff_X_derivative_deltaEulerSeriesZ_eq_trunc_of_lt
    (N := d + 1) (d := d) (by omega)]
  rw [coeff_X_derivative_deltaEulerProductTruncZ_eq_E2_mul_of_le
    (N := d + 1) (d := d) (by omega)]
  exact (coeff_E2_mul_deltaEulerSeriesZ_eq_trunc_of_lt
    (N := d + 1) (d := d) (by omega)).symm

theorem TruncRep.deltaEulerSeries (N : ℕ) :
    TruncRep N deltaEulerSeriesZ (deltaEulerProductTruncCoeffListSlow N N) := by
  intro n hn
  rw [coeff_deltaEulerSeriesZ,
    ← coeff_deltaEulerProductTruncZ_eq_deltaEulerCoeffZ_of_lt (N := N) hn]
  exact (TruncRep.deltaEulerProductTrunc N N) n hn

theorem TruncRep.evalSparseBivarCleared {N xMax yMax : ℕ}
    {xNum xDen yNum yDen : PowerSeries ℤ}
    {xNumL xDenL yNumL yDenL : List ℤ}
    (hxNum : TruncRep N xNum xNumL)
    (hxDen : TruncRep N xDen xDenL)
    (hyNum : TruncRep N yNum yNumL)
    (hyDen : TruncRep N yDen yDenL) :
    ∀ terms : List SparseBivarTerm,
      TruncRep N
        (evalSparseBivarCleared terms xMax yMax xNum xDen yNum yDen)
        (evalSparseBivarClearedTruncCoeffList N terms xMax yMax
          xNumL xDenL yNumL yDenL) := by
  intro terms
  induction terms with
  | nil =>
      intro n hn
      change PowerSeries.coeff (R := ℤ) n (0 : PowerSeries ℤ) =
        truncCoeffAt (zeroTruncCoeffList N) n
      simp [zeroTruncCoeffList, truncCoeffAt_truncCoeffList_of_lt hn]
  | cons t ts ih =>
      have hterm :
          TruncRep N
            ((t.coeff : PowerSeries ℤ) *
              xNum ^ t.xPow * xDen ^ (xMax - t.xPow) *
                yNum ^ t.yPow * yDen ^ (yMax - t.yPow))
            (scaleTruncCoeffList N t.coeff
              (mulTruncCoeffList N
                (mulTruncCoeffList N
                  (powTruncCoeffList N xNumL t.xPow)
                  (powTruncCoeffList N xDenL (xMax - t.xPow)))
                (mulTruncCoeffList N
                  (powTruncCoeffList N yNumL t.yPow)
                  (powTruncCoeffList N yDenL (yMax - t.yPow))))) := by
        have hxP := hxNum.pow (k := t.xPow)
        have hxD := hxDen.pow (k := xMax - t.xPow)
        have hyP := hyNum.pow (k := t.yPow)
        have hyD := hyDen.pow (k := yMax - t.yPow)
        have hprod := (hxP.mul hxD).mul (hyP.mul hyD)
        simpa [mul_assoc] using hprod.scale t.coeff
      exact hterm.add ih

/-- Correctness of the proof-friendly finite coefficient model for the full
cleared level-41 expression.  The remaining computational step is to connect
this slow model to the sparse fast model used by `native_decide`, or to make
the slow model itself evaluable at the full Sturm bound. -/
theorem phi41Level41ClearedEulerQExpansionZ_TruncRep_slow (N : ℕ) :
    TruncRep N phi41Level41ClearedEulerQExpansionZ
      (evalSparseBivarClearedTruncCoeffList N phi41SparseTerms 42 42
        (qPullback41TruncCoeffList N
          (powTruncCoeffList N (E4TruncCoeffList N) 3))
        (qPullback41TruncCoeffList N
          (deltaEulerProductTruncCoeffListSlow N N))
        (powTruncCoeffList N (E4TruncCoeffList N) 3)
        (deltaEulerProductTruncCoeffListSlow N N)) := by
  unfold phi41Level41ClearedEulerQExpansionZ
  apply TruncRep.evalSparseBivarCleared
  · exact ((TruncRep.E4 N).pow (k := 3)).qPullback41
  · exact (TruncRep.deltaEulerSeries N).qPullback41
  · exact (TruncRep.E4 N).pow (k := 3)
  · exact TruncRep.deltaEulerSeries N

theorem phi41Level41ClearedEulerQExpansionZ_TruncRep_fast (N : ℕ) :
    TruncRep N phi41Level41ClearedEulerQExpansionZ
      (evalSparseBivarClearedTruncCoeffList N phi41SparseTerms 42 42
        (qPullback41TruncCoeffList N
          (powTruncCoeffList N (E4TruncCoeffList N) 3))
        (qPullback41TruncCoeffList N (deltaEulerTruncCoeffList N))
        (powTruncCoeffList N (E4TruncCoeffList N) 3)
        (deltaEulerTruncCoeffList N)) := by
  unfold phi41Level41ClearedEulerQExpansionZ
  apply TruncRep.evalSparseBivarCleared
  · exact ((TruncRep.E4 N).pow (k := 3)).qPullback41
  · exact (TruncRep.deltaEulerSeriesFast N).qPullback41
  · exact (TruncRep.E4 N).pow (k := 3)
  · exact TruncRep.deltaEulerSeriesFast N

theorem phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedSparse
    (N : ℕ) :
    TruncRep N phi41Level41ClearedEulerQExpansionZ
      (phi41Level41CoeffListCompressedSparse N) := by
  unfold phi41Level41ClearedEulerQExpansionZ
    phi41Level41CoeffListCompressedSparse
  let M := (N + 40) / 41
  let Esmall := E4TruncCoeffList M
  let Dsmall := deltaEulerTruncCoeffList M
  let Csmall := powTruncCoeffList M Esmall 3
  let E := E4TruncCoeffList N
  let D := deltaEulerTruncCoeffList N
  let C := powTruncCoeffList N E 3
  have hCsmall :
      TruncRep M (E4ZSeries ^ 3) Csmall := by
    simpa [Csmall, Esmall] using (TruncRep.E4 M).pow (k := 3)
  have hDsmall :
      TruncRep M deltaEulerSeriesZ Dsmall := by
    simpa [Dsmall] using TruncRep.deltaEulerSeriesFast M
  have hC :
      TruncRep N (E4ZSeries ^ 3) C := by
    simpa [C, E] using (TruncRep.E4 N).pow (k := 3)
  have hD :
      TruncRep N deltaEulerSeriesZ D := by
    simpa [D] using TruncRep.deltaEulerSeriesFast N
  simpa [M, Esmall, Dsmall, Csmall, E, D, C] using
    TruncRep.evalSparseBivarClearedCompressed
      (N := N) (M := M) (xNum := E4ZSeries ^ 3)
      (xDen := deltaEulerSeriesZ) (yNum := E4ZSeries ^ 3)
      (yDen := deltaEulerSeriesZ)
      (xNumM := Csmall) (xDenM := Dsmall)
      (yNumN := C) (yDenN := D)
      (by rfl) hCsmall hDsmall hC hD
      phi41SparseTerms
      (fun t ht => phi41SparseTerms_degree_le_42 t ht)

theorem phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedMatrix
    (N : ℕ) :
    TruncRep N phi41Level41ClearedEulerQExpansionZ
      (phi41Level41CoeffListCompressedMatrix N) := by
  intro n hn
  rw [truncCoeffAt_phi41Level41CoeffListCompressedMatrix_eq_sparse hn]
  exact phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedSparse N n hn

theorem phi41Level41SturmCoefficientCertificate_of_compressedSparse_firstZero
    (hzero :
      truncCoeffListFirstZero phi41Level41SturmBound
        (phi41Level41CoeffListCompressedSparse phi41Level41SturmBound) = true) :
    phi41Level41SturmCoefficientCertificate := by
  intro n hn
  have hrep :=
    phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedSparse
      phi41Level41SturmBound
  rw [hrep n hn]
  exact truncCoeffAt_eq_zero_of_firstZero hzero hn

/-- Generic array-certificate exit for the level-41 Sturm coefficient check.

This is the kernel-facing target for a generated or improved finite
coefficient certificate: it only has to provide an array that agrees
coefficientwise with the already proved compressed-matrix truncation model and
whose first Sturm-bound entries are zero.  This avoids baking the current slow
dense evaluator into the final proof interface. -/
theorem phi41Level41SturmCoefficientCertificate_of_array_certificate
    {A : Array ℤ}
    (harray :
      ListArrayEq phi41Level41SturmBound
        (phi41Level41CoeffListCompressedMatrix phi41Level41SturmBound) A)
    (hzero :
      truncCoeffArrayFirstZero phi41Level41SturmBound A = true) :
    phi41Level41SturmCoefficientCertificate := by
  intro n hn
  have hrep :=
    phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedMatrix
      phi41Level41SturmBound
  rw [hrep n hn, harray n hn]
  exact truncCoeffArrayAt_eq_zero_of_firstZero hzero hn

theorem phi41Level41SturmCoefficientCertificate_of_recurrenceArray
    (hderiv : ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)))
    (hzero :
      phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true) :
    phi41Level41SturmCoefficientCertificate := by
  exact phi41Level41SturmCoefficientCertificate_of_array_certificate
    (A := phi41Level41RecurrenceCoeffArray phi41Level41SturmBound)
    (ListArrayEq.phi41Level41CoeffCompressedMatrix_of_derivative_identities
      phi41Level41SturmBound hderiv)
    hzero

theorem phi41Level41SturmCoefficientCertificate_of_recurrenceArray_base
    (hE4cubed :
      E4ZSeries * (PowerSeries.X * PowerSeries.derivative ℤ (E4ZSeries ^ 3)) =
        (E2ZSeries * E4ZSeries - E6ZSeries) * (E4ZSeries ^ 3))
    (hzero :
      phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true) :
    phi41Level41SturmCoefficientCertificate :=
  phi41Level41SturmCoefficientCertificate_of_recurrenceArray
    (fun j hj =>
      phi41LevelOneDenseRow_derivative_identity_of_base
        j hj hE4cubed deltaEulerSeriesZ_derivative_identity)
    hzero

theorem phi41Level41SturmCoefficientCertificate_of_recurrenceArray_E4_derivative
    (hE4 :
      PowerSeries.C (3 : ℤ) *
          (PowerSeries.X * PowerSeries.derivative ℤ E4ZSeries) =
        E2ZSeries * E4ZSeries - E6ZSeries)
    (hzero :
      phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true) :
    phi41Level41SturmCoefficientCertificate :=
  phi41Level41SturmCoefficientCertificate_of_recurrenceArray_base
    (E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity hE4)
    hzero

theorem phi41Level41SturmCoefficientCertificate_of_eulerCompressedArray_firstZero
    (hzero :
      truncCoeffArrayFirstZero phi41Level41SturmBound
        (phi41Level41EulerCoeffArrayCompressedPullback
          phi41Level41SturmBound) = true) :
    phi41Level41SturmCoefficientCertificate := by
  intro n hn
  have hrep :=
    phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedMatrix
      phi41Level41SturmBound
  have harray :=
    ListArrayEq.phi41Level41CoeffCompressedMatrixEuler
      phi41Level41SturmBound
  rw [hrep n hn, harray n hn]
  exact truncCoeffArrayAt_eq_zero_of_firstZero hzero hn

theorem phi41Level41SturmCoefficientCertificate_of_fastCompressedArray_firstZero
    (hD :
      truncCoeffArrayEqFirst phi41Level41SturmBound
        (deltaEulerTruncCoeffArray phi41Level41SturmBound)
        (deltaRamanujanTruncCoeffArray phi41Level41SturmBound) = true)
    (hDsmall :
      truncCoeffArrayEqFirst ((phi41Level41SturmBound + 40) / 41)
        (deltaEulerTruncCoeffArray ((phi41Level41SturmBound + 40) / 41))
        (deltaRamanujanTruncCoeffArray ((phi41Level41SturmBound + 40) / 41)) = true)
    (hzero :
      truncCoeffArrayFirstZero phi41Level41SturmBound
        (phi41Level41FastCoeffArray phi41Level41SturmBound) = true) :
    phi41Level41SturmCoefficientCertificate := by
  intro n hn
  have hrep :=
    phi41Level41ClearedEulerQExpansionZ_TruncRep_compressedMatrix
      phi41Level41SturmBound
  have hDarray :
      ListArrayEq phi41Level41SturmBound
        (deltaEulerTruncCoeffList phi41Level41SturmBound)
        (deltaRamanujanTruncCoeffArray phi41Level41SturmBound) :=
    ListArrayEq.of_array_eq_first
      (ListArrayEq.deltaEulerTruncCoeff phi41Level41SturmBound) hD
  have hDsmallArray :
      ListArrayEq ((phi41Level41SturmBound + 40) / 41)
        (deltaEulerTruncCoeffList ((phi41Level41SturmBound + 40) / 41))
        (deltaRamanujanTruncCoeffArray ((phi41Level41SturmBound + 40) / 41)) :=
    ListArrayEq.of_array_eq_first
      (ListArrayEq.deltaEulerTruncCoeff
        ((phi41Level41SturmBound + 40) / 41)) hDsmall
  have harray :=
    ListArrayEq.phi41Level41CoeffCompressedMatrixRamanujan
      phi41Level41SturmBound hDarray hDsmallArray
  rw [hrep n hn, harray n hn]
  simpa [phi41Level41FastCoeffArray] using
    truncCoeffArrayAt_eq_zero_of_firstZero hzero hn

theorem phi41Level41SturmCoefficientCertificate_of_fastCached_firstZero
    (hD : deltaEulerRamanujanEqFirst phi41Level41SturmBound = true)
    (hDsmall :
      deltaEulerRamanujanEqFirst ((phi41Level41SturmBound + 40) / 41) = true)
    (hzero : phi41Level41FastCoeffArrayFirstZero phi41Level41SturmBound = true) :
    phi41Level41SturmCoefficientCertificate := by
  apply phi41Level41SturmCoefficientCertificate_of_fastCompressedArray_firstZero
  · simpa [deltaEulerRamanujanEqFirst_iff] using hD
  · simpa [deltaEulerRamanujanEqFirst_iff] using hDsmall
  · simpa [phi41Level41FastCoeffArrayFirstZero_iff] using hzero

/-- Full Sturm-bound agreement between the proof-facing Euler-product `Δ`
truncation and the VM-facing Ramanujan-recurrence `Δ` truncation.

The statement is finite and decidable, but the current dense array evaluator is
not a usable kernel certificate at `phi41Level41SturmBound = 3528`: profiling
shows the power/product tables dominate before this bridge can be consumed by
the final coefficient checker.  Keep this as a tracked computational proof
obligation rather than a nonterminating `native_decide`. -/
theorem deltaEulerRamanujanEqFirst_sturmBound :
    deltaEulerRamanujanEqFirst phi41Level41SturmBound = true := by
  exact deltaEulerRamanujanEqFirst_of_derivative_identity
    phi41Level41SturmBound deltaEulerSeriesZ_derivative_identity

/-- Small pullback-side version of `deltaEulerRamanujanEqFirst_sturmBound`.
This one has length `(3528 + 40) / 41 = 87`, but it is kept parallel with the
main finite-certificate gap so the full certificate route has a uniform
dependency surface. -/
theorem deltaEulerRamanujanEqFirst_sturmBoundSmall :
    deltaEulerRamanujanEqFirst ((phi41Level41SturmBound + 40) / 41) = true := by
  exact deltaEulerRamanujanEqFirst_of_derivative_identity
    ((phi41Level41SturmBound + 40) / 41)
    deltaEulerSeriesZ_derivative_identity

set_option linter.style.maxHeartbeats false in
set_option linter.style.nativeDecide false in
-- Sturm certificate: evaluates 3529 recurrence coefficients via native_decide
-- (to be replaced by SturmCRTBound analytical route)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by
  native_decide

theorem phi41Level41SturmCoefficientCertificate_proof :
    phi41Level41SturmCoefficientCertificate := by
  exact phi41Level41SturmCoefficientCertificate_of_recurrenceArray_E4_derivative
    E4ZSeries_derivative_identity
    phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound

end Modular
end Number
end Ripple
