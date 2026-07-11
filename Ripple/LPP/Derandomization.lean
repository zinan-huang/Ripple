/-
  Ripple.LPP.Derandomization — PLPP → Deterministic LPP

  Formalizes Lemma 4 of [BFK] / Lemma 15 of [Koegler]:
  every probabilistic LPP (PLPP) with rational transition probabilities
  can be simulated by a deterministic LPP computing the same number.

  Construction overview:
  Given a PLPP P on states Q = {1,...,d} with rational transition
  probabilities α_{i,j,k,l}, let m be a common denominator of all α.

  1. Build a cyclic "coin" protocol P_m on Q_m = {1,...,m}:
       i j → (i+1)(j+1)  (mod m)
     This drives every state proportion to 1/m (Lemma 3/14 of [BFK/Koegler]).

  2. Construct a product protocol on Q × Q_m with transition rule:
       (q_i, r)(q_j, r') → (q_k, r+1)(q_l, r'+1)
     where (q_k, q_l) is determined by which part of the [0,1] partition
     (defined by the α_{i,j,k,l} for input pair (i,j)) the value (r-1)/m
     falls in. The second coordinate runs P_m independently.

  3. The equilibrium of the product system is:
       ν* = (ν_1/m, ..., ν_1/m, ..., ν_d/m, ..., ν_d/m)
     where (ν_1, ..., ν_d) is the equilibrium of the original PLPP.

  4. Koegler's long-time argument is readout/marginal-level, via a combined
     Lyapunov function:
       L(x) = L̃(x̃) + K · g(x̄)
     where L̃ is the Lyapunov function of the original system,
     g(x̄) = ∑_R (x̄_R - 1/m)² (Lyapunov for the cyclic P_m part),
     and K is large enough to dominate cross terms.

     Full product-state convergence to the independent replicated point is
     false in general; correlation modes can be unstable.  The unconditional
     theorem formalized here is therefore continuum/readout preservation by
     uniform trajectory lifting.

  References:
  - [BFK] Bournez-Fraigniaud-Koegler, §3.2 / Appendix C (MFCS 2012).
  - [Koegler] §5.2.2 / Lemma 15 (PhD thesis, 2012).
-/

import Ripple.LPP.Defs
import Ripple.LPP.Stochastic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Ripple

/-! ## The Cyclic "Coin" Protocol

Protocol P_m on m states: i j → (i+1) (j+1) mod m.
Drives all state proportions to 1/m exponentially.
This is Lemma 3 of [BFK] / Lemma 14 of [Koegler]. -/

/-- The cyclic protocol on m states. State i transitions with state j
to produce states (i+1 mod m) and (j+1 mod m). -/
def cyclicReaction (m : ℕ) (hm : 0 < m) (i j : Fin m) :
    Kurtz.PPReaction m where
  in1 := i
  in2 := j
  out1 := ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
  out2 := ⟨(j.val + 1) % m, Nat.mod_lt _ hm⟩

/-- The full cyclic protocol: all pairs (i,j) produce ((i+1) mod m, (j+1) mod m). -/
def cyclicProtocol (m : ℕ) (hm : 0 < m) : Kurtz.PopProtocol m where
  reactions := Finset.univ.image fun ij : Fin m × Fin m =>
    cyclicReaction m hm ij.1 ij.2

theorem cyclicReaction_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (fun ij : Fin m × Fin m => cyclicReaction m hm ij.1 ij.2) := by
  intro a b h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  have h₁ : a₁ = b₁ := congrArg (fun rxn : Kurtz.PPReaction m => rxn.in1) h
  have h₂ : a₂ = b₂ := congrArg (fun rxn : Kurtz.PPReaction m => rxn.in2) h
  cases h₁
  cases h₂
  rfl

theorem cyclicSucc_eq_finRotate (m : ℕ) (hm : 0 < m) (i : Fin m) :
    ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩ = finRotate m i := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [finRotate_succ_apply]
  ext
  simp [Fin.add_def]

theorem cyclicPred_eq_finRotate_symm (m : ℕ) (hm : 0 < m) (r : Fin m) :
    ⟨(r.val + m - 1) % m, Nat.mod_lt _ hm⟩ = (finRotate m).symm r := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [finRotate_succ_symm_apply]
  ext
  rw [Fin.coe_sub_one]
  by_cases hr : r = 0
  · simp [hr]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hr)
    have hrle : r.val ≤ n := Nat.lt_succ_iff.mp r.isLt
    have hmod : (r.val + (n + 1) - 1) % (n + 1) = r.val - 1 := by
      rw [show r.val + (n + 1) - 1 = (n + 1) + (r.val - 1) by omega]
      rw [Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    simpa [hr, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmod

private theorem cyclic_sum_first_coord (m : ℕ) (x : Fin m → ℝ)
    (hsum : ∑ i, x i = 1) (a : Fin m) :
    (∑ ij : Fin m × Fin m,
      (if ij.1 = a then (1 : ℝ) else 0) * (x ij.1 * x ij.2)) = x a := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : Fin m, ∑ j : Fin m,
        (if i = a then (1 : ℝ) else 0) * (x i * x j))
        = ∑ i : Fin m, ((if i = a then (1 : ℝ) else 0) * x i) * (∑ j, x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          ring_nf
    _ = ∑ i : Fin m, ((if i = a then (1 : ℝ) else 0) * x i) := by
          simp [hsum]
    _ = x a := by
          simp

private theorem cyclic_sum_second_coord (m : ℕ) (x : Fin m → ℝ)
    (hsum : ∑ i, x i = 1) (a : Fin m) :
    (∑ ij : Fin m × Fin m,
      (if ij.2 = a then (1 : ℝ) else 0) * (x ij.1 * x ij.2)) = x a := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : Fin m, ∑ j : Fin m,
        (if j = a then (1 : ℝ) else 0) * (x i * x j))
        = ∑ i : Fin m, x i * (∑ j : Fin m, (if j = a then (1 : ℝ) else 0) * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring_nf
    _ = (∑ i : Fin m, x i) * (∑ j : Fin m, (if j = a then (1 : ℝ) else 0) * x j) := by
          rw [Finset.sum_mul]
    _ = x a := by
          simp [hsum]

private theorem cyclic_sum_first_coord_rev (m : ℕ) (x : Fin m → ℝ)
    (hsum : ∑ i, x i = 1) (a : Fin m) :
    (∑ ij : Fin m × Fin m,
      (if a = ij.1 then (1 : ℝ) else 0) * (x ij.1 * x ij.2)) = x a := by
  simpa [eq_comm] using cyclic_sum_first_coord m x hsum a

private theorem cyclic_sum_second_coord_rev (m : ℕ) (x : Fin m → ℝ)
    (hsum : ∑ i, x i = 1) (a : Fin m) :
    (∑ ij : Fin m × Fin m,
      (if a = ij.2 then (1 : ℝ) else 0) * (x ij.1 * x ij.2)) = x a := by
  simpa [eq_comm] using cyclic_sum_second_coord m x hsum a

private theorem cyclic_sum_first_equiv (m : ℕ) (x : Fin m → ℝ)
    (hsum : ∑ i, x i = 1) (e : Equiv.Perm (Fin m)) (a : Fin m) :
    (∑ ij : Fin m × Fin m,
      (if a = e ij.1 then (1 : ℝ) else 0) * (x ij.1 * x ij.2)) = x (e.symm a) := by
  calc
    (∑ ij : Fin m × Fin m,
      (if a = e ij.1 then (1 : ℝ) else 0) * (x ij.1 * x ij.2))
        = ∑ ij : Fin m × Fin m,
          (if ij.1 = e.symm a then (1 : ℝ) else 0) * (x ij.1 * x ij.2) := by
          apply Finset.sum_congr rfl
          intro ij _
          have hiff : (a = e ij.1) ↔ (ij.1 = e.symm a) := by
            rw [eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
          by_cases h : a = e ij.1
          · have h' : ij.1 = e.symm a := hiff.mp h
            rw [if_pos h, if_pos h']
          · have h' : ij.1 ≠ e.symm a := fun h'' => h (hiff.mpr h'')
            rw [if_neg h, if_neg h']
    _ = x (e.symm a) := cyclic_sum_first_coord m x hsum (e.symm a)

private theorem cyclic_sum_second_equiv (m : ℕ) (x : Fin m → ℝ)
    (hsum : ∑ i, x i = 1) (e : Equiv.Perm (Fin m)) (a : Fin m) :
    (∑ ij : Fin m × Fin m,
      (if a = e ij.2 then (1 : ℝ) else 0) * (x ij.1 * x ij.2)) = x (e.symm a) := by
  calc
    (∑ ij : Fin m × Fin m,
      (if a = e ij.2 then (1 : ℝ) else 0) * (x ij.1 * x ij.2))
        = ∑ ij : Fin m × Fin m,
          (if ij.2 = e.symm a then (1 : ℝ) else 0) * (x ij.1 * x ij.2) := by
          apply Finset.sum_congr rfl
          intro ij _
          have hiff : (a = e ij.2) ↔ (ij.2 = e.symm a) := by
            rw [eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
          by_cases h : a = e ij.2
          · have h' : ij.2 = e.symm a := hiff.mp h
            rw [if_pos h, if_pos h']
          · have h' : ij.2 ≠ e.symm a := fun h'' => h (hiff.mpr h'')
            rw [if_neg h, if_neg h']
    _ = x (e.symm a) := cyclic_sum_second_coord m x hsum (e.symm a)

/-- The cyclic drift at coordinate r simplifies to
  2 · (x_{r-1 mod m} - x_r) on the simplex.
This is the core calculation needed for `cyclicProtocol_unique_equilibrium`. -/
theorem cyclicDrift_eq (m : ℕ) (hm : 0 < m) (x : Fin m → ℝ)
    (hsum : ∑ i, x i = 1) (r : Fin m) :
    (cyclicProtocol m hm).meanFieldDrift x r =
      2 * (x ⟨(r.val + m - 1) % m, Nat.mod_lt _ hm⟩ - x r) := by
  classical
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  rw [Kurtz.PopProtocol.meanFieldDrift, cyclicProtocol]
  rw [Finset.sum_image]
  · simp only [cyclicReaction, Kurtz.PPReaction.netChange, Kurtz.PPReaction.massActionRate,
      Int.cast_sub, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero]
    simp_rw [cyclicSucc_eq_finRotate m hm]
    simp_rw [sub_eq_add_neg, add_mul, neg_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [cyclic_sum_first_equiv m x hsum (finRotate m) r]
    rw [cyclic_sum_second_equiv m x hsum (finRotate m) r]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    rw [cyclic_sum_first_coord_rev m x hsum r]
    rw [cyclic_sum_second_coord_rev m x hsum r]
    rw [← cyclicPred_eq_finRotate_symm m hm r]
    ring
  · intro a _ b _ h
    exact cyclicReaction_injective m hm h

theorem cyclicProtocol_unique_equilibrium (m : ℕ) (hm : 0 < m) :
    let pp := cyclicProtocol m hm
    ∀ x : Fin m → ℝ, (∀ i, 0 ≤ x i) → ∑ i, x i = 1 →
      pp.meanFieldDrift x = 0 →
      ∀ i, x i = 1 / (m : ℝ) := by
  intro pp x _hpos hsum hdrift i
  have hdrift_r : ∀ r : Fin m, pp.meanFieldDrift x r = 0 := by
    intro r; exact congr_fun hdrift r
  have hprev_eq : ∀ r : Fin m,
      x ⟨(r.val + m - 1) % m, Nat.mod_lt _ hm⟩ = x r := by
    intro r
    have h := hdrift_r r
    rw [cyclicDrift_eq m hm x hsum r] at h
    linarith
  -- From hprev_eq: x_{r-1} = x_r cyclically → all coordinates equal.
  have hconst : ∀ j : Fin m, x j = x i := by
    haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    have hpred : ∀ r : Fin m,
        ⟨(r.val + m - 1) % m, Nat.mod_lt _ hm⟩ = (finRotate m).symm r := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      intro r
      rw [finRotate_succ_symm_apply]
      ext
      rw [Fin.coe_sub_one]
      by_cases hr : r = 0
      · simp [hr]
      · have hrpos : 0 < r.val := Nat.pos_of_ne_zero (Fin.val_ne_zero_iff.mpr hr)
        have hrle : r.val ≤ n := Nat.lt_succ_iff.mp r.isLt
        have hmod : (r.val + (n + 1) - 1) % (n + 1) = r.val - 1 := by
          rw [show r.val + (n + 1) - 1 = (n + 1) + (r.val - 1) by omega]
          rw [Nat.add_mod_left]
          exact Nat.mod_eq_of_lt (by omega)
        simpa [hr, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmod
    have hrot_symm : ∀ r : Fin m, x ((finRotate m).symm r) = x r := by
      intro r
      rw [← hpred r]
      exact hprev_eq r
    have hrot : ∀ r : Fin m, x (finRotate m r) = x r := by
      intro r
      have h := hrot_symm (finRotate m r)
      simpa using h.symm
    have hiter : ∀ k : ℕ, ∀ r : Fin m, x (((finRotate m)^[k]) r) = x r := by
      intro k
      induction k with
      | zero =>
          intro r
          simp
      | succ k ih =>
          intro r
          rw [Function.iterate_succ_apply']
          exact (hrot _).trans (ih r)
    intro j
    have hj : ((finRotate m)^[((j - i).val)]) i = j := by
      rw [← finCycle_eq_finRotate_iterate]
      simp [finCycle]
    rw [← hj]
    exact hiter ((j - i).val) i
  have hval : (m : ℝ) * x i = 1 := by
    have : ∑ j : Fin m, x j = 1 := hsum
    rw [show ∑ j : Fin m, x j = ∑ _j : Fin m, x i from
      Finset.sum_congr rfl (fun j _ => hconst j)] at this
    simpa [Finset.sum_const, Finset.card_fin] using this
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  field_simp at hval ⊢
  linarith

/-! ## The De-randomization Construction

Given PLPPTransitions on d states with rational α, construct a
deterministic PopProtocol on d × m states. -/

/-- Common denominator of all transition probabilities.
Every α_{i,j,k,l} can be written as p/m for some non-negative integer p. -/
noncomputable def PLPPTransitions.commonDenom {d : ℕ} (tr : PLPPTransitions d) : ℕ :=
  let denoms := Finset.univ.image fun ijkl : Fin d × Fin d × Fin d × Fin d =>
    (tr.α ijkl.1 ijkl.2.1 ijkl.2.2.1 ijkl.2.2.2).den
  denoms.lcm id

theorem PLPPTransitions.commonDenom_pos {d : ℕ} (tr : PLPPTransitions d) :
    0 < tr.commonDenom := by
  dsimp [PLPPTransitions.commonDenom]
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro q hq
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq
  obtain ⟨ijkl, rfl⟩ := hq
  exact Rat.den_nz _

/-! ## Product-state indexing -/

/-- The product-state equivalence used by the derandomized protocol.
The deterministic LPP state space is `Fin d × Fin m`, represented as
`Fin (d * m)` for compatibility with `PopProtocol`. -/
def finProdEquiv (d m : ℕ) : Fin (d * m) ≃ Fin d × Fin m :=
  (finProdFinEquiv : Fin d × Fin m ≃ Fin (d * m)).symm

/-- Encode a product state `(i,r)` as the flat state space `Fin (d * m)`. -/
def finProdEncode (d m : ℕ) (i : Fin d) (r : Fin m) : Fin (d * m) :=
  (finProdEquiv d m).symm (i, r)

@[simp] theorem finProdEquiv_encode {d m : ℕ} (i : Fin d) (r : Fin m) :
    finProdEquiv d m (finProdEncode d m i r) = (i, r) := by
  simp [finProdEncode]

@[simp] theorem finProdEncode_eq_encode {d m : ℕ}
    {i k : Fin d} {r s : Fin m} :
    finProdEncode d m i r = finProdEncode d m k s ↔ i = k ∧ r = s := by
  constructor
  · intro h
    have h' := congrArg (finProdEquiv d m) h
    simpa using h'
  · intro h
    rcases h with ⟨rfl, rfl⟩
    rfl

/-- Decode the original PLPP coordinate from a flat product state. -/
def finProdOrig {d m : ℕ} (idx : Fin (d * m)) : Fin d :=
  (finProdEquiv d m idx).1

/-- Decode the cyclic coin coordinate from a flat product state. -/
def finProdCoin {d m : ℕ} (idx : Fin (d * m)) : Fin m :=
  (finProdEquiv d m idx).2

@[simp] theorem finProdOrig_encode {d m : ℕ} (i : Fin d) (r : Fin m) :
    finProdOrig (finProdEncode d m i r) = i := by
  simp [finProdOrig]

@[simp] theorem finProdCoin_encode {d m : ℕ} (i : Fin d) (r : Fin m) :
    finProdCoin (finProdEncode d m i r) = r := by
  simp [finProdCoin]

theorem finProdEncode_orig_coin {d m : ℕ} (idx : Fin (d * m)) :
    finProdEncode d m (finProdOrig idx) (finProdCoin idx) = idx := by
  rw [finProdOrig, finProdCoin, finProdEncode]
  exact (finProdEquiv d m).symm_apply_apply idx

@[simp] theorem eq_finProdEquiv_symm_iff {d m : ℕ}
    (idx : Fin (d * m)) (p : Fin d × Fin m) :
    idx = (finProdEquiv d m).symm p ↔ finProdEquiv d m idx = p := by
  constructor
  · intro h
    rw [h]
    exact (finProdEquiv d m).apply_symm_apply p
  · intro h
    rw [← h]
    exact ((finProdEquiv d m).symm_apply_apply idx).symm

/-- The cyclic successor on `Fin m`. -/
def nextCoin {m : ℕ} (hm : 0 < m) (r : Fin m) : Fin m :=
  ⟨(r.val + 1) % m, Nat.mod_lt _ hm⟩

/-- Addition in the cyclic coin coordinate. -/
def coinAdd {m : ℕ} (hm : 0 < m) (r s : Fin m) : Fin m :=
  ⟨(r.val + s.val) % m, Nat.mod_lt _ hm⟩

theorem coinAdd_eq_finCycle_left {m : ℕ} (hm : 0 < m) (r s : Fin m) :
    coinAdd hm r s = finCycle r s := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  ext
  simp [coinAdd, finCycle_apply, Fin.add_def, Nat.add_comm]

theorem coinAdd_eq_finCycle_right {m : ℕ} (hm : 0 < m) (r s : Fin m) :
    coinAdd hm r s = finCycle s r := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  ext
  simp [coinAdd, finCycle_apply, Fin.add_def]

/-- The integer numerator of α_{i,j,k,l} scaled by the common denominator.
  Since m = commonDenom divides the denominator of each α, the product
  α * m is a non-negative integer. -/
noncomputable def PLPPTransitions.scaledAlpha {d : ℕ} (tr : PLPPTransitions d)
    (i j k l : Fin d) : ℕ :=
  ((tr.α i j k l) * (tr.commonDenom : ℚ)).num.toNat

theorem PLPPTransitions.den_dvd_commonDenom {d : ℕ} (tr : PLPPTransitions d)
    (i j k l : Fin d) :
    (tr.α i j k l).den ∣ tr.commonDenom := by
  dsimp [PLPPTransitions.commonDenom]
  apply Finset.dvd_lcm
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(i, j, k, l), rfl⟩

theorem PLPPTransitions.scaledAlpha_spec {d : ℕ} (tr : PLPPTransitions d)
    (i j k l : Fin d) :
    (tr.scaledAlpha i j k l : ℚ) =
      tr.α i j k l * (tr.commonDenom : ℚ) := by
  let q := tr.α i j k l
  let m := tr.commonDenom
  have hden_dvd : q.den ∣ m := tr.den_dvd_commonDenom i j k l
  obtain ⟨c, hc⟩ := hden_dvd
  have hq_nonneg : 0 ≤ q := tr.nonneg i j k l
  have hqm_nonneg : 0 ≤ q * (m : ℚ) := by positivity
  have hnum_nonneg : 0 ≤ (q * (m : ℚ)).num := by
    rwa [Rat.num_nonneg]
  have hqm_int : q * (m : ℚ) = (q.num * (c : ℤ) : ℤ) := by
    have hden_ne : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    calc
      q * (m : ℚ)
          = ((q.num : ℚ) / q.den) * (m : ℚ) := by
              conv_lhs => rw [← q.num_div_den]
      _ = ((q.num : ℚ) / q.den) * (q.den * c : ℕ) := by
              rw [hc]
      _ = (q.num : ℚ) * c := by
              rw [Nat.cast_mul]
              field_simp [hden_ne]
      _ = (q.num * (c : ℤ) : ℤ) := by
              norm_num
  dsimp [PLPPTransitions.scaledAlpha]
  change ((q * (m : ℚ)).num.toNat : ℚ) = q * (m : ℚ)
  have hnat :
      ((q * (m : ℚ)).num.toNat : ℚ) = ((q * (m : ℚ)).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum_nonneg
  rw [hnat]
  exact Rat.coe_int_num_of_den_eq_one (by rw [hqm_int, Rat.den_intCast])

theorem PLPPTransitions.scaledAlpha_sum {d : ℕ} (tr : PLPPTransitions d)
    (i j : Fin d) :
    (∑ k : Fin d, ∑ l : Fin d, tr.scaledAlpha i j k l) = tr.commonDenom := by
  have hcast :
      ((∑ k : Fin d, ∑ l : Fin d, tr.scaledAlpha i j k l : ℕ) : ℚ) =
        (tr.commonDenom : ℚ) := by
    rw [Nat.cast_sum]
    simp_rw [Nat.cast_sum]
    simp_rw [tr.scaledAlpha_spec i j]
    calc
      (∑ k : Fin d, ∑ l : Fin d,
          tr.α i j k l * (tr.commonDenom : ℚ))
          = (∑ k : Fin d, ∑ l : Fin d, tr.α i j k l) *
              (tr.commonDenom : ℚ) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
      _ = (tr.commonDenom : ℚ) := by
              rw [tr.sum_one i j]
              ring
  exact_mod_cast hcast

/-- The cumulative count up to pair (k,l) in lexicographic order.
  This is ∑_{(k',l') ≤_lex (k,l)} scaledAlpha(i,j,k',l'). -/
noncomputable def PLPPTransitions.cumulativeCount {d : ℕ} (tr : PLPPTransitions d)
    (i j : Fin d) (idx : ℕ) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin d × Fin d)).filter
    (fun p => p.1.val * d + p.2.val < idx),
    tr.scaledAlpha i j p.1 p.2

private abbrev PLPPTransitions.coinSlotSigma {d : ℕ} (tr : PLPPTransitions d)
    (i j : Fin d) : Type :=
  Sigma fun p : Fin d × Fin d => Fin (tr.scaledAlpha i j p.1 p.2)

private theorem PLPPTransitions.card_coinSlotSigma {d : ℕ} (tr : PLPPTransitions d)
    (i j : Fin d) :
    Fintype.card (tr.coinSlotSigma i j) = tr.commonDenom := by
  dsimp [PLPPTransitions.coinSlotSigma]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fintype.sum_prod_type]
  exact tr.scaledAlpha_sum i j

private noncomputable def PLPPTransitions.coinSlotEquiv {d : ℕ}
    (tr : PLPPTransitions d) (i j : Fin d) :
    Fin tr.commonDenom ≃ tr.coinSlotSigma i j :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, tr.card_coinSlotSigma i j])

noncomputable def PLPPTransitions.coinSlot {d : ℕ} (tr : PLPPTransitions d)
    (i j : Fin d) (r : Fin tr.commonDenom) : Fin d × Fin d :=
  (tr.coinSlotEquiv i j r).1

/-- Exact slot-count specification for `coinSlot`.
For every input pair `(i,j)`, exactly `m * α_{i,j,k,l}` slots choose
the output pair `(k,l)`, where `m = commonDenom`. -/
theorem PLPPTransitions.coinSlot_count {d : ℕ} (tr : PLPPTransitions d)
    (i j k l : Fin d) :
    (Finset.univ.filter fun r : Fin tr.commonDenom =>
      tr.coinSlot i j r = (k, l)).card =
      (tr.α i j k l * (tr.commonDenom : ℚ)).num.toNat := by
  classical
  rw [← Fintype.card_subtype
    (fun r : Fin tr.commonDenom => tr.coinSlot i j r = (k, l))]
  rw [Fintype.card_congr ((tr.coinSlotEquiv i j).subtypeEquiv
    (q := fun y : tr.coinSlotSigma i j => y.1 = (k, l)) (by
      intro r
      rfl))]
  rw [Fintype.card_congr
    (Equiv.subtypeSigmaEquiv
      (fun p : Fin d × Fin d => Fin (tr.scaledAlpha i j p.1 p.2))
      (fun p : Fin d × Fin d => p = (k, l)))]
  rw [Fintype.card_sigma]
  let target : Fin d × Fin d := (k, l)
  haveI : Unique {p : Fin d × Fin d // p = target} :=
    { default := ⟨target, rfl⟩
      uniq := by
        intro p
        apply Subtype.ext
        exact p.2 }
  simp only [Fintype.card_fin, Fintype.sum_unique]
  have hdef : ((default : {p : Fin d × Fin d // p = target}).val) = target :=
    (default : {p : Fin d × Fin d // p = target}).property
  rw [hdef]
  change tr.scaledAlpha i j target.1 target.2 =
    (tr.α i j k l * (tr.commonDenom : ℚ)).num.toNat
  rfl

theorem PLPPTransitions.coinSlot_first_count {d : ℕ} (tr : PLPPTransitions d)
    (i j k : Fin d) :
    ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
      (tr.coinSlot i j r).1 = k).card =
      ∑ l : Fin d, tr.scaledAlpha i j k l := by
  classical
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
        (tr.coinSlot i j r).1 = k)
      (t := (Finset.univ : Finset (Fin d)))
      (f := fun r : Fin tr.commonDenom => (tr.coinSlot i j r).2)
      (fun _ _ => Finset.mem_univ _)
  calc
    ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
      (tr.coinSlot i j r).1 = k).card
        = ∑ l : Fin d,
            ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
              (tr.coinSlot i j r).1 = k ∧ (tr.coinSlot i j r).2 = l).card := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using h
    _ = ∑ l : Fin d, tr.scaledAlpha i j k l := by
        apply Finset.sum_congr rfl
        intro l _
        calc
          ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
            (tr.coinSlot i j r).1 = k ∧ (tr.coinSlot i j r).2 = l).card
              = ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
                  tr.coinSlot i j r = (k, l)).card := by
                  apply congrArg Finset.card
                  ext r
                  simp [Prod.ext_iff]
          _ = tr.scaledAlpha i j k l := by
              change ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
                tr.coinSlot i j r = (k, l)).card =
                  (tr.α i j k l * (tr.commonDenom : ℚ)).num.toNat
              rw [tr.coinSlot_count i j k l]

theorem PLPPTransitions.coinSlot_second_count {d : ℕ} (tr : PLPPTransitions d)
    (i j l : Fin d) :
    ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
      (tr.coinSlot i j r).2 = l).card =
      ∑ k : Fin d, tr.scaledAlpha i j k l := by
  classical
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
        (tr.coinSlot i j r).2 = l)
      (t := (Finset.univ : Finset (Fin d)))
      (f := fun r : Fin tr.commonDenom => (tr.coinSlot i j r).1)
      (fun _ _ => Finset.mem_univ _)
  calc
    ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
      (tr.coinSlot i j r).2 = l).card
        = ∑ k : Fin d,
            ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
              (tr.coinSlot i j r).2 = l ∧ (tr.coinSlot i j r).1 = k).card := by
            simpa [Finset.filter_filter, and_left_comm, and_assoc] using h
    _ = ∑ k : Fin d, tr.scaledAlpha i j k l := by
        apply Finset.sum_congr rfl
        intro k _
        calc
          ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
            (tr.coinSlot i j r).2 = l ∧ (tr.coinSlot i j r).1 = k).card
              = ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
                  tr.coinSlot i j r = (k, l)).card := by
                  apply congrArg Finset.card
                  ext r
                  simp [Prod.ext_iff, and_comm]
          _ = tr.scaledAlpha i j k l := by
              change ((Finset.univ : Finset (Fin tr.commonDenom)).filter fun r =>
                tr.coinSlot i j r = (k, l)).card =
                  (tr.α i j k l * (tr.commonDenom : ℚ)).num.toNat
              rw [tr.coinSlot_count i j k l]

private theorem sum_ite_one_zero_eq_card_filter {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (∑ a : α, (if p a then (1 : ℝ) else 0)) =
      (((Finset.univ : Finset α).filter p).card : ℝ) := by
  simp

private theorem sum_original_indicator {d : ℕ} (i : Fin d)
    (p : Prop) [Decidable p] :
    (∑ I : Fin d, (if I = i ∧ p then (1 : ℝ) else 0)) =
      if p then 1 else 0 := by
  by_cases hp : p <;> simp [hp]

private theorem sum_nextCoin_indicator {m : ℕ} (hm : 0 < m) (r : Fin m) :
    (∑ s : Fin m, (if r = nextCoin hm s then (1 : ℝ) else 0)) = 1 := by
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  simp_rw [show (fun s : Fin m => nextCoin hm s) = finRotate m by
    funext s
    exact cyclicSucc_eq_finRotate m hm s]
  calc
    (∑ s : Fin m, (if r = finRotate m s then (1 : ℝ) else 0))
        = ∑ s : Fin m, (if s = (finRotate m).symm r then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro s _
            have hiff : r = finRotate m s ↔ s = (finRotate m).symm r := by
              rw [eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
            by_cases h : r = finRotate m s
            · rw [if_pos h, if_pos (hiff.mp h)]
            · rw [if_neg h, if_neg (fun hs => h (hiff.mpr hs))]
    _ = 1 := by simp

private theorem PLPPTransitions.coinSlot_first_indicator_sum_shift {d : ℕ}
    (tr : PLPPTransitions d) (i j k : Fin d) (s : Fin tr.commonDenom) :
    (∑ t : Fin tr.commonDenom,
      (if (tr.coinSlot i j (coinAdd tr.commonDenom_pos s t)).1 = k
        then (1 : ℝ) else 0)) =
      (tr.commonDenom : ℝ) * ∑ l : Fin d, (tr.α i j k l : ℝ) := by
  classical
  calc
    (∑ t : Fin tr.commonDenom,
      (if (tr.coinSlot i j (coinAdd tr.commonDenom_pos s t)).1 = k
        then (1 : ℝ) else 0))
        = ∑ t : Fin tr.commonDenom,
            (if (tr.coinSlot i j (finCycle s t)).1 = k then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro t _
            rw [coinAdd_eq_finCycle_left]
    _ = ∑ r : Fin tr.commonDenom,
          (if (tr.coinSlot i j r).1 = k then (1 : ℝ) else 0) := by
          exact Equiv.sum_comp (finCycle s)
            (g :=
            (fun r : Fin tr.commonDenom =>
              if (tr.coinSlot i j r).1 = k then (1 : ℝ) else 0))
    _ = (∑ l : Fin d, (tr.scaledAlpha i j k l : ℝ)) := by
          rw [sum_ite_one_zero_eq_card_filter]
          exact_mod_cast tr.coinSlot_first_count i j k
    _ = (tr.commonDenom : ℝ) * ∑ l : Fin d, (tr.α i j k l : ℝ) := by
          have hterm : ∀ l : Fin d,
              (tr.scaledAlpha i j k l : ℝ) =
                (tr.commonDenom : ℝ) * (tr.α i j k l : ℝ) := by
            intro l
            have hq := tr.scaledAlpha_spec i j k l
            have hreal :
                (tr.scaledAlpha i j k l : ℝ) =
                  (tr.α i j k l : ℝ) * (tr.commonDenom : ℝ) := by
              exact_mod_cast hq
            linarith
          simp_rw [hterm]
          rw [Finset.mul_sum]

private theorem PLPPTransitions.coinSlot_second_indicator_sum_shift {d : ℕ}
    (tr : PLPPTransitions d) (i j l : Fin d) (s : Fin tr.commonDenom) :
    (∑ t : Fin tr.commonDenom,
      (if (tr.coinSlot i j (coinAdd tr.commonDenom_pos t s)).2 = l
        then (1 : ℝ) else 0)) =
      (tr.commonDenom : ℝ) * ∑ k : Fin d, (tr.α i j k l : ℝ) := by
  classical
  calc
    (∑ t : Fin tr.commonDenom,
      (if (tr.coinSlot i j (coinAdd tr.commonDenom_pos t s)).2 = l
        then (1 : ℝ) else 0))
        = ∑ t : Fin tr.commonDenom,
            (if (tr.coinSlot i j (finCycle s t)).2 = l then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro t _
            rw [coinAdd_eq_finCycle_right]
    _ = ∑ r : Fin tr.commonDenom,
          (if (tr.coinSlot i j r).2 = l then (1 : ℝ) else 0) := by
          exact Equiv.sum_comp (finCycle s)
            (g :=
            (fun r : Fin tr.commonDenom =>
              if (tr.coinSlot i j r).2 = l then (1 : ℝ) else 0))
    _ = (∑ k : Fin d, (tr.scaledAlpha i j k l : ℝ)) := by
          rw [sum_ite_one_zero_eq_card_filter]
          exact_mod_cast tr.coinSlot_second_count i j l
    _ = (tr.commonDenom : ℝ) * ∑ k : Fin d, (tr.α i j k l : ℝ) := by
          have hterm : ∀ k : Fin d,
              (tr.scaledAlpha i j k l : ℝ) =
                (tr.commonDenom : ℝ) * (tr.α i j k l : ℝ) := by
            intro k
            have hq := tr.scaledAlpha_spec i j k l
            have hreal :
                (tr.scaledAlpha i j k l : ℝ) =
                  (tr.α i j k l : ℝ) * (tr.commonDenom : ℝ) := by
              exact_mod_cast hq
            linarith
          simp_rw [hterm]
          rw [Finset.mul_sum]

private theorem derandomized_prod1_replicated {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) (I : Fin d) (R : Fin tr.commonDenom) :
    (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
      (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).1 ∧ R = nextCoin tr.commonDenom_pos S
        then (1 : ℝ) else 0) * (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ)))) =
      (1 / (tr.commonDenom : ℝ)) *
        (∑ A : Fin d, ∑ B : Fin d,
          x A * x B * (∑ L : Fin d, (tr.α A B I L : ℝ))) := by
  classical
  have hmR : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  calc
    (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
      (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).1 ∧ R = nextCoin tr.commonDenom_pos S
        then (1 : ℝ) else 0) * (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))))
        = ∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d,
            (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) *
              (if R = nextCoin tr.commonDenom_pos S then
                ∑ T : Fin tr.commonDenom,
                  (if (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).1 = I
                    then (1 : ℝ) else 0)
              else 0) := by
            apply Finset.sum_congr rfl
            intro A _
            apply Finset.sum_congr rfl
            intro S _
            apply Finset.sum_congr rfl
            intro B _
            by_cases hR : R = nextCoin tr.commonDenom_pos S
            · simp [hR]
              rw [show (∑ x_1 : Fin tr.commonDenom,
                  if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S x_1)).1 then
                    x A / ↑tr.commonDenom * (x B / ↑tr.commonDenom)
                  else 0) =
                    (x A / ↑tr.commonDenom * (x B / ↑tr.commonDenom)) *
                      ∑ x_1 : Fin tr.commonDenom,
                        (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S x_1)).1
                          then (1 : ℝ) else 0) by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro T _
                    by_cases hI :
                        I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).1
                    · simp [hI]
                    · simp [hI]]
              rw [sum_ite_one_zero_eq_card_filter]
              simp [eq_comm, mul_assoc]
            · simp [hR]
    _ = ∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d,
          (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) *
            (if R = nextCoin tr.commonDenom_pos S then
              (tr.commonDenom : ℝ) * ∑ L : Fin d, (tr.α A B I L : ℝ)
            else 0) := by
          apply Finset.sum_congr rfl
          intro A _
          apply Finset.sum_congr rfl
          intro S _
          apply Finset.sum_congr rfl
          intro B _
          by_cases hR : R = nextCoin tr.commonDenom_pos S
          · simp [hR, tr.coinSlot_first_indicator_sum_shift A B I S]
          · simp [hR]
    _ = ∑ A : Fin d, ∑ B : Fin d,
          (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) *
            ((tr.commonDenom : ℝ) * ∑ L : Fin d, (tr.α A B I L : ℝ)) := by
          simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin tr.commonDenom)))
            (t := (Finset.univ : Finset (Fin d)))]
          apply Finset.sum_congr rfl
          intro A _
          apply Finset.sum_congr rfl
          intro B _
          rw [← Finset.mul_sum]
          rw [show (∑ S : Fin tr.commonDenom,
              (if R = nextCoin tr.commonDenom_pos S then
                (tr.commonDenom : ℝ) * ∑ L : Fin d, (tr.α A B I L : ℝ)
              else 0)) =
              ((tr.commonDenom : ℝ) * ∑ L : Fin d, (tr.α A B I L : ℝ)) *
                (∑ S : Fin tr.commonDenom,
                  (if R = nextCoin tr.commonDenom_pos S then (1 : ℝ) else 0)) by
                conv_rhs => rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro S _
                by_cases hR : R = nextCoin tr.commonDenom_pos S <;> simp [hR]]
          rw [sum_nextCoin_indicator]
          ring
    _ = (1 / (tr.commonDenom : ℝ)) *
        (∑ A : Fin d, ∑ B : Fin d,
          x A * x B * (∑ L : Fin d, (tr.α A B I L : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B _
          field_simp [hmR]

private theorem derandomized_prod2_replicated {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) (I : Fin d) (R : Fin tr.commonDenom) :
    (∑ A : Fin d, ∑ T : Fin tr.commonDenom, ∑ B : Fin d, ∑ S : Fin tr.commonDenom,
      (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧ R = nextCoin tr.commonDenom_pos T
        then (1 : ℝ) else 0) * (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ)))) =
      (1 / (tr.commonDenom : ℝ)) *
        (∑ A : Fin d, ∑ B : Fin d,
          x A * x B * (∑ K : Fin d, (tr.α A B K I : ℝ))) := by
  classical
  have hmR : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  calc
    (∑ A : Fin d, ∑ T : Fin tr.commonDenom, ∑ B : Fin d, ∑ S : Fin tr.commonDenom,
      (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧ R = nextCoin tr.commonDenom_pos T
        then (1 : ℝ) else 0) * (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))))
        = ∑ A : Fin d, ∑ T : Fin tr.commonDenom, ∑ B : Fin d,
            (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) *
              (if R = nextCoin tr.commonDenom_pos T then
                ∑ S : Fin tr.commonDenom,
                  (if (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 = I
                    then (1 : ℝ) else 0)
              else 0) := by
            apply Finset.sum_congr rfl
            intro A _
            apply Finset.sum_congr rfl
            intro T _
            apply Finset.sum_congr rfl
            intro B _
            by_cases hR : R = nextCoin tr.commonDenom_pos T
            · simp [hR]
              rw [show (∑ x_1 : Fin tr.commonDenom,
                  if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos x_1 T)).2 then
                    x A / ↑tr.commonDenom * (x B / ↑tr.commonDenom)
                  else 0) =
                    (x A / ↑tr.commonDenom * (x B / ↑tr.commonDenom)) *
                      ∑ x_1 : Fin tr.commonDenom,
                        (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos x_1 T)).2
                          then (1 : ℝ) else 0) by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro S _
                    by_cases hI :
                        I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2
                    · simp [hI]
                    · simp [hI]]
              rw [sum_ite_one_zero_eq_card_filter]
              simp [eq_comm, mul_assoc]
            · simp [hR]
    _ = ∑ A : Fin d, ∑ T : Fin tr.commonDenom, ∑ B : Fin d,
          (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) *
            (if R = nextCoin tr.commonDenom_pos T then
              (tr.commonDenom : ℝ) * ∑ K : Fin d, (tr.α A B K I : ℝ)
            else 0) := by
          apply Finset.sum_congr rfl
          intro A _
          apply Finset.sum_congr rfl
          intro T _
          apply Finset.sum_congr rfl
          intro B _
          by_cases hR : R = nextCoin tr.commonDenom_pos T
          · simp [hR, tr.coinSlot_second_indicator_sum_shift A B I T]
          · simp [hR]
    _ = ∑ A : Fin d, ∑ B : Fin d,
          (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) *
            ((tr.commonDenom : ℝ) * ∑ K : Fin d, (tr.α A B K I : ℝ)) := by
          simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin tr.commonDenom)))
            (t := (Finset.univ : Finset (Fin d)))]
          apply Finset.sum_congr rfl
          intro A _
          apply Finset.sum_congr rfl
          intro B _
          rw [← Finset.mul_sum]
          rw [show (∑ T : Fin tr.commonDenom,
              (if R = nextCoin tr.commonDenom_pos T then
                (tr.commonDenom : ℝ) * ∑ K : Fin d, (tr.α A B K I : ℝ)
              else 0)) =
              ((tr.commonDenom : ℝ) * ∑ K : Fin d, (tr.α A B K I : ℝ)) *
                (∑ T : Fin tr.commonDenom,
                  (if R = nextCoin tr.commonDenom_pos T then (1 : ℝ) else 0)) by
                conv_rhs => rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro T _
                by_cases hR : R = nextCoin tr.commonDenom_pos T <;> simp [hR]]
          rw [sum_nextCoin_indicator]
          ring
    _ = (1 / (tr.commonDenom : ℝ)) *
        (∑ A : Fin d, ∑ B : Fin d,
          x A * x B * (∑ K : Fin d, (tr.α A B K I : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B _
          field_simp [hmR]

private theorem derandomized_cons1_replicated {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) (I : Fin d) (R : Fin tr.commonDenom) :
    (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ _T : Fin tr.commonDenom,
      (if A = I ∧ S = R then (1 : ℝ) else 0) *
        (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ)))) =
      (x I / (tr.commonDenom : ℝ)) * (∑ B : Fin d, x B) := by
  classical
  have hmR : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  calc
    (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
      (if A = I ∧ S = R then (1 : ℝ) else 0) *
        (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))))
        = ∑ B : Fin d,
          (tr.commonDenom : ℝ) *
            (x I / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) := by
          calc
            (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
              (if A = I ∧ S = R then (1 : ℝ) else 0) *
                (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))))
                = ∑ A : Fin d, ∑ S : Fin tr.commonDenom,
                    (if A = I ∧ S = R then
                      ∑ B : Fin d,
                        (tr.commonDenom : ℝ) *
                          (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ)))
                    else 0) := by
                    apply Finset.sum_congr rfl
                    intro A _
                    apply Finset.sum_congr rfl
                    intro S _
                    by_cases h : A = I ∧ S = R
                    · simp [h, Finset.sum_const]
                    · simp [h]
            _ = ∑ B : Fin d,
                  (tr.commonDenom : ℝ) *
                    (x I / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) := by
                calc
                  (∑ A : Fin d, ∑ S : Fin tr.commonDenom,
                    (if A = I ∧ S = R then
                      ∑ B : Fin d,
                        (tr.commonDenom : ℝ) *
                          (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ)))
                    else 0))
                      = ∑ A : Fin d,
                          (if A = I then
                            ∑ B : Fin d,
                              (tr.commonDenom : ℝ) *
                                (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ)))
                          else 0) := by
                          apply Finset.sum_congr rfl
                          intro A _
                          by_cases hA : A = I
                          · simp [hA]
                          · simp [hA]
                  _ = ∑ B : Fin d,
                        (tr.commonDenom : ℝ) *
                          (x I / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))) := by
                      simp
    _ = (x I / (tr.commonDenom : ℝ)) * (∑ B : Fin d, x B) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B _
          field_simp [hmR]

private theorem derandomized_cons2_replicated {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) (I : Fin d) (R : Fin tr.commonDenom) :
    (∑ A : Fin d, ∑ _S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
      (if B = I ∧ T = R then (1 : ℝ) else 0) *
        (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ)))) =
      (x I / (tr.commonDenom : ℝ)) * (∑ A : Fin d, x A) := by
  classical
  have hmR : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  calc
    (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
      (if B = I ∧ T = R then (1 : ℝ) else 0) *
        (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))))
        = ∑ A : Fin d,
          (tr.commonDenom : ℝ) *
            (x A / (tr.commonDenom : ℝ) * (x I / (tr.commonDenom : ℝ))) := by
          calc
            (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
              (if B = I ∧ T = R then (1 : ℝ) else 0) *
                (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))))
                = ∑ A : Fin d, ∑ S : Fin tr.commonDenom,
                    x A / (tr.commonDenom : ℝ) * (x I / (tr.commonDenom : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro A _
                    apply Finset.sum_congr rfl
                    intro S _
                    calc
                      (∑ B : Fin d, ∑ T : Fin tr.commonDenom,
                        (if B = I ∧ T = R then (1 : ℝ) else 0) *
                          (x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))))
                          = ∑ B : Fin d,
                              (if B = I then
                                x A / (tr.commonDenom : ℝ) * (x B / (tr.commonDenom : ℝ))
                              else 0) := by
                              apply Finset.sum_congr rfl
                              intro B _
                              by_cases hB : B = I
                              · simp [hB]
                              · simp [hB]
                      _ = x A / (tr.commonDenom : ℝ) * (x I / (tr.commonDenom : ℝ)) := by
                          simp
            _ = ∑ A : Fin d,
                  (tr.commonDenom : ℝ) *
                    (x A / (tr.commonDenom : ℝ) * (x I / (tr.commonDenom : ℝ))) := by
                simp [Finset.sum_const]
    _ = (x I / (tr.commonDenom : ℝ)) * (∑ A : Fin d, x A) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro A _
          field_simp [hmR]

private theorem derandomized_replicated_expanded_eq {d : ℕ}
    (tr : PLPPTransitions d) (x₀ : Fin d → ℝ)
    (I : Fin d) (R : Fin tr.commonDenom) :
    (∑ x : (Fin d × Fin tr.commonDenom) × (Fin d × Fin tr.commonDenom),
      ((((if (I, R) =
              ((tr.coinSlot x.1.1 x.2.1 (coinAdd tr.commonDenom_pos x.1.2 x.2.2)).1,
                nextCoin tr.commonDenom_pos x.1.2)
            then (1 : ℝ) else 0) +
          if (I, R) =
              ((tr.coinSlot x.1.1 x.2.1 (coinAdd tr.commonDenom_pos x.1.2 x.2.2)).2,
                nextCoin tr.commonDenom_pos x.2.2)
            then (1 : ℝ) else 0) -
        if (I, R) = x.1 then (1 : ℝ) else 0) -
        if (I, R) = x.2 then (1 : ℝ) else 0) *
        (x₀ x.1.1 / (tr.commonDenom : ℝ) *
          (x₀ x.2.1 / (tr.commonDenom : ℝ)))) =
      (1 / (tr.commonDenom : ℝ)) * tr.balanceField x₀ I := by
  classical
  have hprod1 := derandomized_prod1_replicated tr x₀ I R
  have hprod2 := derandomized_prod2_replicated tr x₀ I R
  have hcons1 := derandomized_cons1_replicated tr x₀ I R
  have hcons2 := derandomized_cons2_replicated tr x₀ I R
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : Fin d × Fin tr.commonDenom,
      ∑ x_1 : Fin d × Fin tr.commonDenom,
        ((((if (I, R) =
              ((tr.coinSlot x.1 x_1.1 (coinAdd tr.commonDenom_pos x.2 x_1.2)).1,
                nextCoin tr.commonDenom_pos x.2) then (1 : ℝ) else 0) +
          if (I, R) =
              ((tr.coinSlot x.1 x_1.1 (coinAdd tr.commonDenom_pos x.2 x_1.2)).2,
                nextCoin tr.commonDenom_pos x_1.2) then (1 : ℝ) else 0) -
        if (I, R) = x then (1 : ℝ) else 0) -
      if (I, R) = x_1 then (1 : ℝ) else 0) *
        (x₀ x.1 / (tr.commonDenom : ℝ) *
          (x₀ x_1.1 / (tr.commonDenom : ℝ)))) =
      (∑ A : Fin d, ∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
        ((((if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).1 ∧
              R = nextCoin tr.commonDenom_pos S then (1 : ℝ) else 0) +
          if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧
              R = nextCoin tr.commonDenom_pos T then (1 : ℝ) else 0) -
        if A = I ∧ S = R then (1 : ℝ) else 0) -
      if B = I ∧ T = R then (1 : ℝ) else 0) *
        (x₀ A / (tr.commonDenom : ℝ) *
          (x₀ B / (tr.commonDenom : ℝ)))) by
        simp_rw [Fintype.sum_prod_type]
        simp [Prod.ext_iff, eq_comm]]
  simp_rw [sub_mul, add_mul]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- The four summands are exactly the two production and two consumption sums above.
  rw [hprod1]
  rw [show (∑ x : Fin d,
        ∑ x_1 : Fin tr.commonDenom,
          ∑ x_2 : Fin d,
            ∑ x_3 : Fin tr.commonDenom,
              (if I = (tr.coinSlot x x_2 (coinAdd tr.commonDenom_pos x_1 x_3)).2 ∧
                  R = nextCoin tr.commonDenom_pos x_3 then (1 : ℝ) else 0) *
                (x₀ x / (tr.commonDenom : ℝ) *
                  (x₀ x_2 / (tr.commonDenom : ℝ)))) =
      ∑ A : Fin d,
        ∑ T : Fin tr.commonDenom,
          ∑ B : Fin d,
            ∑ S : Fin tr.commonDenom,
              (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧
                  R = nextCoin tr.commonDenom_pos T then (1 : ℝ) else 0) *
                (x₀ A / (tr.commonDenom : ℝ) *
                  (x₀ B / (tr.commonDenom : ℝ))) by
      apply Finset.sum_congr rfl
      intro A _
      calc
        (∑ S : Fin tr.commonDenom, ∑ B : Fin d, ∑ T : Fin tr.commonDenom,
          (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧
              R = nextCoin tr.commonDenom_pos T then (1 : ℝ) else 0) *
            (x₀ A / (tr.commonDenom : ℝ) *
              (x₀ B / (tr.commonDenom : ℝ))))
            = ∑ B : Fin d, ∑ S : Fin tr.commonDenom, ∑ T : Fin tr.commonDenom,
                (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧
                    R = nextCoin tr.commonDenom_pos T then (1 : ℝ) else 0) *
                  (x₀ A / (tr.commonDenom : ℝ) *
                    (x₀ B / (tr.commonDenom : ℝ))) := by
                rw [Finset.sum_comm]
        _ = ∑ B : Fin d, ∑ T : Fin tr.commonDenom, ∑ S : Fin tr.commonDenom,
                (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧
                    R = nextCoin tr.commonDenom_pos T then (1 : ℝ) else 0) *
                  (x₀ A / (tr.commonDenom : ℝ) *
                    (x₀ B / (tr.commonDenom : ℝ))) := by
                apply Finset.sum_congr rfl
                intro B _
                rw [Finset.sum_comm]
        _ = ∑ T : Fin tr.commonDenom, ∑ B : Fin d, ∑ S : Fin tr.commonDenom,
                (if I = (tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)).2 ∧
                    R = nextCoin tr.commonDenom_pos T then (1 : ℝ) else 0) *
                  (x₀ A / (tr.commonDenom : ℝ) *
                    (x₀ B / (tr.commonDenom : ℝ))) := by
                rw [Finset.sum_comm]]
  rw [hprod2]
  rw [hcons1, hcons2]
  have hmR : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  simp only [PLPPTransitions.balanceField]
  field_simp [hmR]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  ring_nf

private theorem derandomized_replicated_expanded_zero {d : ℕ}
    (tr : PLPPTransitions d) (eq : SimplexEquilibrium tr)
    (I : Fin d) (R : Fin tr.commonDenom) :
    (∑ x : (Fin d × Fin tr.commonDenom) × (Fin d × Fin tr.commonDenom),
      ((((if (I, R) =
              ((tr.coinSlot x.1.1 x.2.1 (coinAdd tr.commonDenom_pos x.1.2 x.2.2)).1,
                nextCoin tr.commonDenom_pos x.1.2)
            then (1 : ℝ) else 0) +
          if (I, R) =
              ((tr.coinSlot x.1.1 x.2.1 (coinAdd tr.commonDenom_pos x.1.2 x.2.2)).2,
                nextCoin tr.commonDenom_pos x.2.2)
            then (1 : ℝ) else 0) -
        if (I, R) = x.1 then (1 : ℝ) else 0) -
      if (I, R) = x.2 then (1 : ℝ) else 0) *
        (eq.point x.1.1 / (tr.commonDenom : ℝ) *
          (eq.point x.2.1 / (tr.commonDenom : ℝ)))) = 0 := by
  rw [derandomized_replicated_expanded_eq tr eq.point I R]
  simp [eq.is_eq]

/-- The `coinSlot` fibers partition the `m` cyclic coin slots. -/
theorem PLPPTransitions.coinSlot_count_sum {d : ℕ} (tr : PLPPTransitions d)
    (i j : Fin d) :
    (∑ k : Fin d, ∑ l : Fin d,
      (Finset.univ.filter fun r : Fin tr.commonDenom =>
        tr.coinSlot i j r = (k, l)).card) = tr.commonDenom := by
  classical
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin tr.commonDenom)))
      (t := (Finset.univ : Finset (Fin d × Fin d)))
      (f := fun r : Fin tr.commonDenom => tr.coinSlot i j r)
      (fun _ _ => Finset.mem_univ _)
  calc
    (∑ k : Fin d, ∑ l : Fin d,
      (Finset.univ.filter fun r : Fin tr.commonDenom =>
        tr.coinSlot i j r = (k, l)).card)
        = ∑ p : Fin d × Fin d,
            (Finset.univ.filter fun r : Fin tr.commonDenom =>
              tr.coinSlot i j r = p).card := by
            rw [← Finset.sum_product']
            simp
    _ = tr.commonDenom := by
        simpa using h.symm

/-- One deterministic product-state reaction selected by the first coin
coordinate. -/
noncomputable def PLPPTransitions.derandomizedReaction {d : ℕ}
    (tr : PLPPTransitions d) (a b : Fin (d * tr.commonDenom)) :
    Kurtz.PPReaction (d * tr.commonDenom) where
  in1 := a
  in2 := b
  out1 :=
    let hm := tr.commonDenom_pos
    let a' := finProdEquiv d tr.commonDenom a
    let b' := finProdEquiv d tr.commonDenom b
    let out := tr.coinSlot a'.1 b'.1 (coinAdd hm a'.2 b'.2)
    finProdEncode d tr.commonDenom out.1 (nextCoin hm a'.2)
  out2 :=
    let hm := tr.commonDenom_pos
    let a' := finProdEquiv d tr.commonDenom a
    let b' := finProdEquiv d tr.commonDenom b
    let out := tr.coinSlot a'.1 b'.1 (coinAdd hm a'.2 b'.2)
    finProdEncode d tr.commonDenom out.2 (nextCoin hm b'.2)

theorem PLPPTransitions.derandomizedReaction_injective {d : ℕ}
    (tr : PLPPTransitions d) :
    Function.Injective
      (fun ab : Fin (d * tr.commonDenom) × Fin (d * tr.commonDenom) =>
        tr.derandomizedReaction ab.1 ab.2) := by
  intro a b h
  apply Prod.ext
  · exact congrArg (fun rxn : Kurtz.PPReaction (d * tr.commonDenom) => rxn.in1) h
  · exact congrArg (fun rxn : Kurtz.PPReaction (d * tr.commonDenom) => rxn.in2) h

@[simp] theorem PLPPTransitions.derandomizedReaction_in1 {d : ℕ}
    (tr : PLPPTransitions d) (a b : Fin (d * tr.commonDenom)) :
    (tr.derandomizedReaction a b).in1 = a := rfl

@[simp] theorem PLPPTransitions.derandomizedReaction_in2 {d : ℕ}
    (tr : PLPPTransitions d) (a b : Fin (d * tr.commonDenom)) :
    (tr.derandomizedReaction a b).in2 = b := rfl

private theorem PLPPTransitions.derandomizedReaction_coin_netChange_sum_encoded {d : ℕ}
    (tr : PLPPTransitions d) (A B : Fin d) (S T R : Fin tr.commonDenom) :
    (∑ I : Fin d,
      ((tr.derandomizedReaction
        (finProdEncode d tr.commonDenom A S)
        (finProdEncode d tr.commonDenom B T)).netChange
        (finProdEncode d tr.commonDenom I R) : ℝ)) =
      ((cyclicReaction tr.commonDenom tr.commonDenom_pos S T).netChange R : ℝ) := by
  classical
  let out := tr.coinSlot A B (coinAdd tr.commonDenom_pos S T)
  have hsum_out1 :
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom out.1 (nextCoin tr.commonDenom_pos S)
          then (1 : ℝ) else 0)) =
        if R = nextCoin tr.commonDenom_pos S then 1 else 0 := by
    calc
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom out.1 (nextCoin tr.commonDenom_pos S)
          then (1 : ℝ) else 0))
          = ∑ I : Fin d,
              (if I = out.1 ∧ R = nextCoin tr.commonDenom_pos S
                then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro I _
              simp only [finProdEncode_eq_encode]
      _ = if R = nextCoin tr.commonDenom_pos S then 1 else 0 :=
          sum_original_indicator out.1 (R = nextCoin tr.commonDenom_pos S)
  have hsum_out2 :
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom out.2 (nextCoin tr.commonDenom_pos T)
          then (1 : ℝ) else 0)) =
        if R = nextCoin tr.commonDenom_pos T then 1 else 0 := by
    calc
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom out.2 (nextCoin tr.commonDenom_pos T)
          then (1 : ℝ) else 0))
          = ∑ I : Fin d,
              (if I = out.2 ∧ R = nextCoin tr.commonDenom_pos T
                then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro I _
              simp only [finProdEncode_eq_encode]
      _ = if R = nextCoin tr.commonDenom_pos T then 1 else 0 :=
          sum_original_indicator out.2 (R = nextCoin tr.commonDenom_pos T)
  have hsum_in1 :
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom A S then (1 : ℝ) else 0)) =
        if R = S then 1 else 0 := by
    calc
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom A S then (1 : ℝ) else 0))
          = ∑ I : Fin d, (if I = A ∧ R = S then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro I _
              simp only [finProdEncode_eq_encode]
      _ = if R = S then 1 else 0 := sum_original_indicator A (R = S)
  have hsum_in2 :
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom B T then (1 : ℝ) else 0)) =
        if R = T then 1 else 0 := by
    calc
      (∑ I : Fin d,
        (if finProdEncode d tr.commonDenom I R =
            finProdEncode d tr.commonDenom B T then (1 : ℝ) else 0))
          = ∑ I : Fin d, (if I = B ∧ R = T then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro I _
              simp only [finProdEncode_eq_encode]
      _ = if R = T then 1 else 0 := sum_original_indicator B (R = T)
  simp only [Kurtz.PPReaction.netChange, PLPPTransitions.derandomizedReaction, cyclicReaction,
    finProdEquiv_encode, Int.cast_sub, Int.cast_add, Int.cast_ite, Int.cast_one,
    Int.cast_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hsum_out1, hsum_out2, hsum_in1, hsum_in2]
  simp [nextCoin]
  rfl

private theorem PLPPTransitions.derandomizedReaction_coin_netChange_sum {d : ℕ}
    (tr : PLPPTransitions d) (a b : Fin (d * tr.commonDenom)) (R : Fin tr.commonDenom) :
    (∑ I : Fin d,
      ((tr.derandomizedReaction a b).netChange
        (finProdEncode d tr.commonDenom I R) : ℝ)) =
      ((cyclicReaction tr.commonDenom tr.commonDenom_pos
        (finProdCoin a) (finProdCoin b)).netChange R : ℝ) := by
  rw [← finProdEncode_orig_coin a, ← finProdEncode_orig_coin b]
  simpa using tr.derandomizedReaction_coin_netChange_sum_encoded
    (finProdOrig a) (finProdOrig b) (finProdCoin a) (finProdCoin b) R

/-- The de-randomized protocol on d*m states.

State space: Fin d × Fin m, represented as Fin (d * m).
Transition: (q_i, r)(q_j, r') → (q_k, r+1)(q_l, r'+1)
where (k,l) = coinSlot(i, j, r+r').  The sum selector is essential:
after fixing either output coin coordinate, the other input coin still
ranges over all slots, so the deterministic slots average back to α. -/
noncomputable def PLPPTransitions.derandomize {d : ℕ}
    (tr : PLPPTransitions d) : Kurtz.PopProtocol (d * tr.commonDenom) where
  reactions := Finset.univ.image fun ab : Fin (d * tr.commonDenom) × Fin (d * tr.commonDenom) =>
    tr.derandomizedReaction ab.1 ab.2

/-- The deterministic product protocol viewed again as a PLPP with transition
probabilities in `{0,1}`. This is the object used by the isolated-computation
API in `Stochastic.lean`. -/
noncomputable def PLPPTransitions.derandomizeTransitions {d : ℕ}
    (tr : PLPPTransitions d) : PLPPTransitions (d * tr.commonDenom) where
  α a b c e :=
    let hm := tr.commonDenom_pos
    let a' := finProdEquiv d tr.commonDenom a
    let b' := finProdEquiv d tr.commonDenom b
    let out := tr.coinSlot a'.1 b'.1 (coinAdd hm a'.2 b'.2)
    let cExpected := finProdEncode d tr.commonDenom out.1 (nextCoin hm a'.2)
    let eExpected := finProdEncode d tr.commonDenom out.2 (nextCoin hm b'.2)
    if c = cExpected ∧ e = eExpected then 1 else 0
  nonneg := by
    intro a b c e
    dsimp
    split_ifs <;> norm_num
  sum_one := by
    intro a b
    dsimp
    let hm := tr.commonDenom_pos
    let a' := finProdEquiv d tr.commonDenom a
    let b' := finProdEquiv d tr.commonDenom b
    let out := tr.coinSlot a'.1 b'.1 (coinAdd hm a'.2 b'.2)
    let cExpected := finProdEncode d tr.commonDenom out.1 (nextCoin hm a'.2)
    let eExpected := finProdEncode d tr.commonDenom out.2 (nextCoin hm b'.2)
    have hc_mem : cExpected ∈ (Finset.univ : Finset (Fin (d * tr.commonDenom))) :=
      Finset.mem_univ _
    have he_mem : eExpected ∈ (Finset.univ : Finset (Fin (d * tr.commonDenom))) :=
      Finset.mem_univ _
    calc
      (∑ c : Fin (d * tr.commonDenom), ∑ e : Fin (d * tr.commonDenom),
        (if c = cExpected ∧ e = eExpected then (1 : ℚ) else 0))
          = ∑ c : Fin (d * tr.commonDenom),
              (if c = cExpected then (1 : ℚ) else 0) := by
              apply Finset.sum_congr rfl
              intro c _
              by_cases hc : c = cExpected
              · simp [hc, he_mem]
              · simp [hc]
      _ = 1 := by
          simp [hc_mem]

private theorem deterministic_cons1_sum {n : ℕ} (x : Fin n → ℝ) (r : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
      (if r = i then (1 : ℝ) else 0) * (x i * x j)) =
      x r * (∑ j : Fin n, x j) := by
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      (if r = i then (1 : ℝ) else 0) * (x i * x j))
        = ∑ i : Fin n,
            ((if r = i then (1 : ℝ) else 0) * x i) *
              (∑ j : Fin n, x j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            by_cases h : r = i <;> simp [h]
    _ = (∑ i : Fin n, (if r = i then (1 : ℝ) else 0) * x i) *
          (∑ j : Fin n, x j) := by
        rw [Finset.sum_mul]
    _ = x r * (∑ j : Fin n, x j) := by
        simp

private theorem deterministic_cons2_sum {n : ℕ} (x : Fin n → ℝ) (r : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
      (if r = j then (1 : ℝ) else 0) * (x i * x j)) =
      (∑ i : Fin n, x i) * x r := by
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      (if r = j then (1 : ℝ) else 0) * (x i * x j))
        = ∑ i : Fin n,
            x i * (∑ j : Fin n, (if r = j then (1 : ℝ) else 0) * x j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            by_cases h : r = j <;> simp [h]
    _ = (∑ i : Fin n, x i) *
          (∑ j : Fin n, (if r = j then (1 : ℝ) else 0) * x j) := by
        rw [Finset.sum_mul]
    _ = (∑ i : Fin n, x i) * x r := by
        simp

private theorem deterministic_cons1_sum_mul {n : ℕ} (x : Fin n → ℝ) (r : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
      (if r = i then (1 : ℝ) else 0) * x i * x j) =
      x r * (∑ j : Fin n, x j) := by
  simpa [mul_assoc] using deterministic_cons1_sum x r

private theorem deterministic_cons2_sum_mul {n : ℕ} (x : Fin n → ℝ) (r : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n,
      (if r = j then (1 : ℝ) else 0) * x i * x j) =
      (∑ i : Fin n, x i) * x r := by
  simpa [mul_assoc] using deterministic_cons2_sum x r

private theorem PLPPTransitions.derandomizeTransitions_alpha_real {d : ℕ}
    (tr : PLPPTransitions d)
    (a b c e : Fin (d * tr.commonDenom)) :
    (tr.derandomizeTransitions.α a b c e : ℝ) =
      if c = (tr.derandomizedReaction a b).out1 ∧
          e = (tr.derandomizedReaction a b).out2 then 1 else 0 := by
  dsimp [PLPPTransitions.derandomizeTransitions, PLPPTransitions.derandomizedReaction]
  by_cases h :
      c =
          finProdEncode d tr.commonDenom
            (tr.coinSlot ((finProdEquiv d tr.commonDenom) a).1
              ((finProdEquiv d tr.commonDenom) b).1
              (coinAdd tr.commonDenom_pos ((finProdEquiv d tr.commonDenom) a).2
                ((finProdEquiv d tr.commonDenom) b).2)).1
            (nextCoin tr.commonDenom_pos ((finProdEquiv d tr.commonDenom) a).2) ∧
        e =
          finProdEncode d tr.commonDenom
            (tr.coinSlot ((finProdEquiv d tr.commonDenom) a).1
              ((finProdEquiv d tr.commonDenom) b).1
              (coinAdd tr.commonDenom_pos ((finProdEquiv d tr.commonDenom) a).2
                ((finProdEquiv d tr.commonDenom) b).2)).2
            (nextCoin tr.commonDenom_pos ((finProdEquiv d tr.commonDenom) b).2)
  · simp [h]
  · simp [h]

private theorem PLPPTransitions.derandomizeTransitions_alpha_sum_out1 {d : ℕ}
    (tr : PLPPTransitions d)
    (a b r : Fin (d * tr.commonDenom)) :
    (∑ e : Fin (d * tr.commonDenom),
      (tr.derandomizeTransitions.α a b r e : ℝ)) =
      if r = (tr.derandomizedReaction a b).out1 then 1 else 0 := by
  classical
  by_cases hr : r = (tr.derandomizedReaction a b).out1
  · simp [PLPPTransitions.derandomizeTransitions_alpha_real, hr]
  · simp [PLPPTransitions.derandomizeTransitions_alpha_real, hr]

private theorem PLPPTransitions.derandomizeTransitions_alpha_sum_out2 {d : ℕ}
    (tr : PLPPTransitions d)
    (a b r : Fin (d * tr.commonDenom)) :
    (∑ c : Fin (d * tr.commonDenom),
      (tr.derandomizeTransitions.α a b c r : ℝ)) =
      if r = (tr.derandomizedReaction a b).out2 then 1 else 0 := by
  classical
  by_cases hr : r = (tr.derandomizedReaction a b).out2
  · simp [PLPPTransitions.derandomizeTransitions_alpha_real, hr]
  · simp [PLPPTransitions.derandomizeTransitions_alpha_real, hr]

theorem PLPPTransitions.derandomizeTransitions_balanceField_eq_meanFieldDrift {d : ℕ}
    (tr : PLPPTransitions d) :
    tr.derandomizeTransitions.balanceField = tr.derandomize.meanFieldDrift := by
  classical
  ext x r
  rw [PLPPTransitions.balanceField, Kurtz.PopProtocol.meanFieldDrift,
    PLPPTransitions.derandomize]
  rw [Finset.sum_image]
  · rw [Fintype.sum_prod_type]
    simp only [Kurtz.PPReaction.massActionRate, Kurtz.PPReaction.netChange,
      Int.cast_sub, Int.cast_add, Int.cast_ite, Int.cast_one, Int.cast_zero]
    simp_rw [PLPPTransitions.derandomizeTransitions_alpha_sum_out1,
      PLPPTransitions.derandomizeTransitions_alpha_sum_out2]
    simp only [PLPPTransitions.derandomizedReaction_in1,
      PLPPTransitions.derandomizedReaction_in2]
    have hprod_expand : ∀ a b : Fin (d * tr.commonDenom),
        x a * x b *
          ((if r = (tr.derandomizedReaction a b).out1 then (1 : ℝ) else 0) +
            if r = (tr.derandomizedReaction a b).out2 then (1 : ℝ) else 0) =
        (if r = (tr.derandomizedReaction a b).out1 then (1 : ℝ) else 0) *
            (x a * x b) +
          (if r = (tr.derandomizedReaction a b).out2 then (1 : ℝ) else 0) *
            (x a * x b) := by
      intro a b
      ring
    have hnet_expand : ∀ a b : Fin (d * tr.commonDenom),
          ((((if r = (tr.derandomizedReaction a b).out1 then (1 : ℝ) else 0) +
                  if r = (tr.derandomizedReaction a b).out2 then (1 : ℝ) else 0) -
                if r = a then (1 : ℝ) else 0) -
              if r = b then (1 : ℝ) else 0) *
            (x a * x b) =
          (if r = (tr.derandomizedReaction a b).out1 then (1 : ℝ) else 0) *
              (x a * x b) +
            (if r = (tr.derandomizedReaction a b).out2 then (1 : ℝ) else 0) *
              (x a * x b) -
            (if r = a then (1 : ℝ) else 0) * (x a * x b) -
            (if r = b then (1 : ℝ) else 0) * (x a * x b) := by
      intro a b
      ring
    conv_lhs =>
      arg 1
      arg 2
      intro a
      arg 2
      intro b
      rw [hprod_expand a b]
    ring_nf
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [deterministic_cons1_sum_mul, deterministic_cons2_sum_mul]
    rw [show
      (∑ x_1 : Fin (d * tr.commonDenom),
        ∑ x_2 : Fin (d * tr.commonDenom),
          ((if r = (tr.derandomizedReaction x_1 x_2).out1 then (1 : ℝ) else 0) *
              x x_1 * x x_2 +
            (if r = (tr.derandomizedReaction x_1 x_2).out2 then (1 : ℝ) else 0) *
              x x_1 * x x_2)) =
        (∑ x_1 : Fin (d * tr.commonDenom),
          ∑ x_2 : Fin (d * tr.commonDenom),
            (if r = (tr.derandomizedReaction x_1 x_2).out1 then (1 : ℝ) else 0) *
              x x_1 * x x_2) +
        (∑ x_1 : Fin (d * tr.commonDenom),
          ∑ x_2 : Fin (d * tr.commonDenom),
            (if r = (tr.derandomizedReaction x_1 x_2).out2 then (1 : ℝ) else 0) *
              x x_1 * x x_2) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x_1 _
        rw [Finset.sum_add_distrib]]
    rw [show
      (∑ x_1 : Fin (d * tr.commonDenom),
        ∑ x_2 : Fin (d * tr.commonDenom),
          x x_1 * x x_2 *
            (if r = (tr.derandomizedReaction x_1 x_2).out2 then (1 : ℝ) else 0)) =
        (∑ x_1 : Fin (d * tr.commonDenom),
          ∑ x_2 : Fin (d * tr.commonDenom),
            (if r = (tr.derandomizedReaction x_1 x_2).out2 then (1 : ℝ) else 0) *
              x x_1 * x x_2) by
        apply Finset.sum_congr rfl
        intro x_1 _
        apply Finset.sum_congr rfl
        intro x_2 _
        ring]
    rw [show (∑ i : Fin (d * tr.commonDenom), x i) * x r =
        x r * (∑ k : Fin (d * tr.commonDenom), x k) by ring]
    ring_nf
    have hfirst_sum :
      (∑ x_1 : Fin (d * tr.commonDenom),
        ∑ x_2 : Fin (d * tr.commonDenom),
          (x x_1 *
              if r = (tr.derandomizedReaction x_1 x_2).out1 then (1 : ℝ) else 0) *
            x x_2) =
        (∑ x_1 : Fin (d * tr.commonDenom),
          ∑ x_2 : Fin (d * tr.commonDenom),
            (if r = (tr.derandomizedReaction x_1 x_2).out1 then (1 : ℝ) else 0) *
              x x_1 * x x_2) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      apply Finset.sum_congr rfl
      intro x_2 _
      ring
    have hsecond_sum :
      (∑ x_1 : Fin (d * tr.commonDenom),
        ∑ x_2 : Fin (d * tr.commonDenom),
          (x x_1 *
              if r = (tr.derandomizedReaction x_1 x_2).out2 then (1 : ℝ) else 0) *
            x x_2) =
        (∑ x_1 : Fin (d * tr.commonDenom),
          ∑ x_2 : Fin (d * tr.commonDenom),
            (if r = (tr.derandomizedReaction x_1 x_2).out2 then (1 : ℝ) else 0) *
              x x_1 * x x_2) := by
      apply Finset.sum_congr rfl
      intro x_1 _
      apply Finset.sum_congr rfl
      intro x_2 _
      ring
    conv_lhs =>
      rw [hfirst_sum]
    ring_nf
    conv_lhs =>
      rw [hsecond_sum]
    conv_rhs =>
      rw [hsecond_sum]
      rw [hfirst_sum]
    ring
  · intro a _ b _ h
    exact tr.derandomizedReaction_injective h

/-- Lift an original PLPP state uniformly over the cyclic coin coordinate. -/
noncomputable def PLPPTransitions.uniformLift {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) :
    Fin (d * tr.commonDenom) → ℝ :=
  fun idx => x (finProdOrig idx) / (tr.commonDenom : ℝ)

theorem PLPPTransitions.uniformLift_sum {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) :
    ∑ idx : Fin (d * tr.commonDenom), tr.uniformLift x idx =
      ∑ i : Fin d, x i := by
  classical
  have hm_ne : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  rw [← Equiv.sum_comp (finProdEquiv d tr.commonDenom).symm]
  simp only [PLPPTransitions.uniformLift, finProdOrig, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x₀ : Fin d, ∑ _r : Fin tr.commonDenom,
      x x₀ / (tr.commonDenom : ℝ))
        = ∑ x₀ : Fin d, (tr.commonDenom : ℝ) *
            (x x₀ / (tr.commonDenom : ℝ)) := by
            apply Finset.sum_congr rfl
            intro x₀ _
            simp [Finset.sum_const]
    _ = ∑ x₀ : Fin d, x x₀ := by
        apply Finset.sum_congr rfl
        intro x₀ _
        field_simp [hm_ne]

/-- Uniform lift is a continuous finite-dimensional linear map. -/
theorem PLPPTransitions.continuous_uniformLift {d : ℕ}
    (tr : PLPPTransitions d) :
    Continuous tr.uniformLift := by
  refine continuous_pi fun idx => ?_
  simp only [PLPPTransitions.uniformLift]
  exact (continuous_apply (finProdOrig idx)).div_const _

/-- Uniform lift preserves addition. -/
theorem PLPPTransitions.uniformLift_add {d : ℕ}
    (tr : PLPPTransitions d) (x z : Fin d → ℝ) :
    tr.uniformLift (x + z) = tr.uniformLift x + tr.uniformLift z := by
  ext idx
  simp [PLPPTransitions.uniformLift, add_div]

/-- Marginal over the cyclic coin coordinate, returning the original-state
distribution of a product-state vector. -/
noncomputable def PLPPTransitions.originalMarginal {d : ℕ}
    (tr : PLPPTransitions d) (y : Fin (d * tr.commonDenom) → ℝ) :
    Fin d → ℝ :=
  fun i => ∑ r : Fin tr.commonDenom, y (finProdEncode d tr.commonDenom i r)

/-- Marginal over the original coordinate, returning the cyclic-coin
distribution of a product-state vector. -/
noncomputable def PLPPTransitions.coinMarginal {d : ℕ}
    (tr : PLPPTransitions d) (y : Fin (d * tr.commonDenom) → ℝ) :
    Fin tr.commonDenom → ℝ :=
  fun r => ∑ i : Fin d, y (finProdEncode d tr.commonDenom i r)

/-- The original-state marginal sums to the total mass of the product-state
vector. -/
theorem PLPPTransitions.originalMarginal_sum {d : ℕ}
    (tr : PLPPTransitions d) (y : Fin (d * tr.commonDenom) → ℝ) :
    ∑ i : Fin d, tr.originalMarginal y i =
      ∑ idx : Fin (d * tr.commonDenom), y idx := by
  classical
  rw [← Equiv.sum_comp (finProdEquiv d tr.commonDenom).symm]
  simp [PLPPTransitions.originalMarginal, finProdEncode, Fintype.sum_prod_type]

/-- The original-state marginal maps the product simplex to the original
simplex. -/
theorem PLPPTransitions.originalMarginal_mem_simplex {d : ℕ}
    (tr : PLPPTransitions d) {y : Fin (d * tr.commonDenom) → ℝ}
    (hy : y ∈ Simplex (d * tr.commonDenom)) :
    tr.originalMarginal y ∈ Simplex d := by
  classical
  constructor
  · intro i
    exact Finset.sum_nonneg fun r _ => hy.1 (finProdEncode d tr.commonDenom i r)
  · rw [tr.originalMarginal_sum y]
    exact hy.2

/-- The original-state marginal is a continuous linear finite-sum map. -/
theorem PLPPTransitions.continuous_originalMarginal {d : ℕ}
    (tr : PLPPTransitions d) :
    Continuous tr.originalMarginal := by
  refine continuous_pi fun i => ?_
  simp only [PLPPTransitions.originalMarginal]
  exact continuous_finset_sum _ fun r _ => continuous_apply _

/-- The original-state marginal is additive. -/
theorem PLPPTransitions.originalMarginal_add {d : ℕ}
    (tr : PLPPTransitions d)
    (y z : Fin (d * tr.commonDenom) → ℝ) :
    tr.originalMarginal (y + z) = tr.originalMarginal y + tr.originalMarginal z := by
  ext i
  simp [PLPPTransitions.originalMarginal, Finset.sum_add_distrib]

/-- The original-state marginal preserves subtraction. -/
theorem PLPPTransitions.originalMarginal_sub {d : ℕ}
    (tr : PLPPTransitions d)
    (y z : Fin (d * tr.commonDenom) → ℝ) :
    tr.originalMarginal (y - z) = tr.originalMarginal y - tr.originalMarginal z := by
  ext i
  simp [PLPPTransitions.originalMarginal, Finset.sum_sub_distrib]

/-- The coin marginal is additive. -/
theorem PLPPTransitions.coinMarginal_add {d : ℕ}
    (tr : PLPPTransitions d)
    (y z : Fin (d * tr.commonDenom) → ℝ) :
    tr.coinMarginal (y + z) = tr.coinMarginal y + tr.coinMarginal z := by
  ext r
  simp [PLPPTransitions.coinMarginal, Finset.sum_add_distrib]

/-- The coin marginal preserves subtraction. -/
theorem PLPPTransitions.coinMarginal_sub {d : ℕ}
    (tr : PLPPTransitions d)
    (y z : Fin (d * tr.commonDenom) → ℝ) :
    tr.coinMarginal (y - z) = tr.coinMarginal y - tr.coinMarginal z := by
  ext r
  simp [PLPPTransitions.coinMarginal, Finset.sum_sub_distrib]

theorem PLPPTransitions.originalMarginal_uniformLift {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) :
    tr.originalMarginal (tr.uniformLift x) = x := by
  classical
  ext i
  have hm_ne : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  simp only [PLPPTransitions.originalMarginal, PLPPTransitions.uniformLift,
    finProdOrig_encode]
  calc
    (∑ _r : Fin tr.commonDenom, x i / (tr.commonDenom : ℝ))
        = (tr.commonDenom : ℝ) * (x i / (tr.commonDenom : ℝ)) := by
            simp [Finset.sum_const]
    _ = x i := by field_simp [hm_ne]

theorem PLPPTransitions.coinMarginal_uniformLift {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ)
    (hsum : ∑ i : Fin d, x i = 1) :
    tr.coinMarginal (tr.uniformLift x) =
      fun _r : Fin tr.commonDenom => 1 / (tr.commonDenom : ℝ) := by
  classical
  ext r
  simp only [PLPPTransitions.coinMarginal, PLPPTransitions.uniformLift,
    finProdOrig_encode]
  calc
    (∑ i : Fin d, x i / (tr.commonDenom : ℝ))
        = (∑ i : Fin d, x i) / (tr.commonDenom : ℝ) := by
            rw [Finset.sum_div]
    _ = 1 / (tr.commonDenom : ℝ) := by rw [hsum]

private theorem product_coin_grouped_sum {d m : ℕ}
    (f : Fin m → Fin m → ℝ) (y : Fin (d * m) → ℝ) :
    (∑ a : Fin (d * m), ∑ b : Fin (d * m),
      f (finProdCoin a) (finProdCoin b) * (y a * y b)) =
      ∑ S : Fin m, ∑ T : Fin m,
        f S T *
          ((∑ A : Fin d, y (finProdEncode d m A S)) *
            (∑ B : Fin d, y (finProdEncode d m B T))) := by
  classical
  let e : Fin (d * m) ≃ Fin m × Fin d :=
    (finProdEquiv d m).trans (Equiv.prodComm (Fin d) (Fin m))
  calc
    (∑ a : Fin (d * m), ∑ b : Fin (d * m),
      f (finProdCoin a) (finProdCoin b) * (y a * y b))
        = ∑ p : Fin m × Fin d, ∑ q : Fin m × Fin d,
            f p.1 q.1 *
              (y (finProdEncode d m p.2 p.1) *
                y (finProdEncode d m q.2 q.1)) := by
          rw [← Equiv.sum_comp e.symm]
          apply Finset.sum_congr rfl
          intro p _
          rw [← Equiv.sum_comp e.symm]
          apply Finset.sum_congr rfl
          intro q _
          rcases p with ⟨S, A⟩
          rcases q with ⟨T, B⟩
          simp [e, finProdCoin, finProdEncode]
    _ = ∑ S : Fin m, ∑ A : Fin d, ∑ T : Fin m, ∑ B : Fin d,
          f S T * (y (finProdEncode d m A S) * y (finProdEncode d m B T)) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro S _
          apply Finset.sum_congr rfl
          intro A _
          rw [Fintype.sum_prod_type]
    _ = ∑ S : Fin m, ∑ T : Fin m, ∑ A : Fin d, ∑ B : Fin d,
          f S T * (y (finProdEncode d m A S) * y (finProdEncode d m B T)) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [Finset.sum_comm]
    _ = ∑ S : Fin m, ∑ T : Fin m,
        f S T *
          ((∑ A : Fin d, y (finProdEncode d m A S)) *
            (∑ B : Fin d, y (finProdEncode d m B T))) := by
          apply Finset.sum_congr rfl
          intro S _
          apply Finset.sum_congr rfl
          intro T _
          calc
            (∑ A : Fin d, ∑ B : Fin d,
              f S T * (y (finProdEncode d m A S) * y (finProdEncode d m B T)))
                = f S T * ∑ A : Fin d, ∑ B : Fin d,
                    y (finProdEncode d m A S) * y (finProdEncode d m B T) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro A _
                    rw [Finset.mul_sum]
            _ = f S T *
                ((∑ A : Fin d, y (finProdEncode d m A S)) *
                  (∑ B : Fin d, y (finProdEncode d m B T))) := by
                congr 1
                calc
                  (∑ A : Fin d, ∑ B : Fin d,
                    y (finProdEncode d m A S) * y (finProdEncode d m B T))
                      = ∑ A : Fin d,
                          y (finProdEncode d m A S) *
                            (∑ B : Fin d, y (finProdEncode d m B T)) := by
                          apply Finset.sum_congr rfl
                          intro A _
                          rw [← Finset.mul_sum]
                  _ = (∑ A : Fin d, y (finProdEncode d m A S)) *
                        (∑ B : Fin d, y (finProdEncode d m B T)) := by
                      rw [Finset.sum_mul]

/-- The cyclic-coin marginal of the deterministic product protocol evolves
independently of the original-state coordinate.  At the vector-field level,
the product protocol induces exactly the cyclic protocol on the coin marginal. -/
theorem PLPPTransitions.coinMarginal_derandomize_meanFieldDrift {d : ℕ}
    (tr : PLPPTransitions d) (y : Fin (d * tr.commonDenom) → ℝ) :
    tr.coinMarginal (tr.derandomize.meanFieldDrift y) =
      (cyclicProtocol tr.commonDenom tr.commonDenom_pos).meanFieldDrift
        (tr.coinMarginal y) := by
  classical
  ext R
  let f : Fin tr.commonDenom → Fin tr.commonDenom → ℝ :=
    fun S T => ((cyclicReaction tr.commonDenom tr.commonDenom_pos S T).netChange R : ℝ)
  calc
    tr.coinMarginal (tr.derandomize.meanFieldDrift y) R
        = ∑ a : Fin (d * tr.commonDenom), ∑ b : Fin (d * tr.commonDenom),
            f (finProdCoin a) (finProdCoin b) * (y a * y b) := by
          simp only [PLPPTransitions.coinMarginal, Kurtz.PopProtocol.meanFieldDrift,
            PLPPTransitions.derandomize, Kurtz.PPReaction.massActionRate]
          have himage : ∀ I : Fin d,
              (∑ rxn ∈ Finset.univ.image
                (fun ab : Fin (d * tr.commonDenom) × Fin (d * tr.commonDenom) =>
                  tr.derandomizedReaction ab.1 ab.2),
                ((rxn.netChange (finProdEncode d tr.commonDenom I R) : ℝ) *
                  (y rxn.in1 * y rxn.in2))) =
              ∑ ab : Fin (d * tr.commonDenom) × Fin (d * tr.commonDenom),
                (((tr.derandomizedReaction ab.1 ab.2).netChange
                    (finProdEncode d tr.commonDenom I R) : ℝ) *
                  (y (tr.derandomizedReaction ab.1 ab.2).in1 *
                    y (tr.derandomizedReaction ab.1 ab.2).in2)) := by
            intro I
            rw [Finset.sum_image]
            intro a _ b _ h
            exact tr.derandomizedReaction_injective h
          simp_rw [himage]
          · rw [Finset.sum_comm]
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [← Finset.sum_mul]
            rw [tr.derandomizedReaction_coin_netChange_sum a b R]
            rfl
    _ = (cyclicProtocol tr.commonDenom tr.commonDenom_pos).meanFieldDrift
        (tr.coinMarginal y) R := by
          rw [product_coin_grouped_sum f y]
          simp only [f, Kurtz.PopProtocol.meanFieldDrift, cyclicProtocol,
            Kurtz.PPReaction.massActionRate, PLPPTransitions.coinMarginal]
          rw [Finset.sum_image]
          · rw [Fintype.sum_prod_type]
            simp [cyclicReaction]
          · intro a _ b _ h
            exact cyclicReaction_injective tr.commonDenom tr.commonDenom_pos h

/-- The same coin-marginal independence statement for the derandomized
protocol viewed as a `{0,1}` PLPP. -/
theorem PLPPTransitions.coinMarginal_derandomized_drift {d : ℕ}
    (tr : PLPPTransitions d) (y : Fin (d * tr.commonDenom) → ℝ) :
    tr.coinMarginal (tr.derandomizeTransitions.balanceField y) =
      (cyclicProtocol tr.commonDenom tr.commonDenom_pos).meanFieldDrift
        (tr.coinMarginal y) := by
  rw [PLPPTransitions.derandomizeTransitions_balanceField_eq_meanFieldDrift]
  exact tr.coinMarginal_derandomize_meanFieldDrift y

/-- Formal linearization of the PLPP balance field at `x` in direction `z`.
For these quadratic mass-action vector fields this is the Jacobian action,
written without invoking calculus:
`F(x + z) - F(x) - F(z)`. -/
noncomputable def PLPPTransitions.balanceFieldFormalLinearizationAt {n : ℕ}
    (tr : PLPPTransitions n) (x z : Fin n → ℝ) : Fin n → ℝ :=
  tr.balanceField (x + z) - tr.balanceField x - tr.balanceField z

/-- Formal linearization of a population-protocol mean-field drift at `x` in
direction `z`, again using the quadratic polarization formula. -/
noncomputable def Kurtz.PopProtocol.meanFieldFormalLinearizationAt {n : ℕ}
    (pp : Kurtz.PopProtocol n) (x z : Fin n → ℝ) : Fin n → ℝ :=
  pp.meanFieldDrift (x + z) - pp.meanFieldDrift x - pp.meanFieldDrift z

/-- The coin marginal intertwines the formal linearization of the
derandomized product drift with the formal linearization of the cyclic coin
protocol.  This is the Jacobian-level version of coin-marginal independence. -/
theorem PLPPTransitions.coinMarginal_derandomized_formalLinearization {d : ℕ}
    (tr : PLPPTransitions d) (y z : Fin (d * tr.commonDenom) → ℝ) :
    tr.coinMarginal
        (tr.derandomizeTransitions.balanceFieldFormalLinearizationAt y z) =
      (cyclicProtocol tr.commonDenom tr.commonDenom_pos).meanFieldFormalLinearizationAt
        (tr.coinMarginal y) (tr.coinMarginal z) := by
  simp [PLPPTransitions.balanceFieldFormalLinearizationAt,
    Kurtz.PopProtocol.meanFieldFormalLinearizationAt, tr.coinMarginal_sub,
    tr.coinMarginal_add, tr.coinMarginal_derandomized_drift]

/-- Marked states lifted from original states to all cyclic coin states. -/
noncomputable def PLPPTransitions.derandomizedMarked {d : ℕ}
    (tr : PLPPTransitions d) (marked : Finset (Fin d)) :
    Finset (Fin (d * tr.commonDenom)) :=
  Finset.univ.filter fun idx => finProdOrig idx ∈ marked

theorem PLPPTransitions.uniformLift_marked_sum {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) (marked : Finset (Fin d)) :
    ∑ idx ∈ tr.derandomizedMarked marked, tr.uniformLift x idx =
      ∑ i ∈ marked, x i := by
  classical
  have hm_ne : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  simp only [PLPPTransitions.derandomizedMarked, PLPPTransitions.uniformLift]
  rw [Finset.sum_filter]
  rw [← Equiv.sum_comp (finProdEquiv d tr.commonDenom).symm]
  simp only [finProdOrig, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x₀ : Fin d, ∑ _r : Fin tr.commonDenom,
      if x₀ ∈ marked then x x₀ / (tr.commonDenom : ℝ) else 0)
        = ∑ x₀ : Fin d,
            if x₀ ∈ marked then
              (tr.commonDenom : ℝ) * (x x₀ / (tr.commonDenom : ℝ))
            else 0 := by
            apply Finset.sum_congr rfl
            intro x₀ _
            by_cases hx : x₀ ∈ marked
            · simp [hx, Finset.sum_const]
            · simp [hx]
    _ = ∑ x₀ : Fin d, if x₀ ∈ marked then x x₀ else 0 := by
        apply Finset.sum_congr rfl
        intro x₀ _
        by_cases hx : x₀ ∈ marked
        · simp [hx]
          field_simp [hm_ne]
        · simp [hx]
    _ = ∑ i ∈ marked, x i := by
        rw [← Finset.sum_filter]
        simp

set_option maxHeartbeats 800000 in
/-- On the coin-uniform submanifold, the derandomized product protocol's
`PopProtocol` mean-field drift is exactly the uniform lift of the original
PLPP balance field. -/
theorem PLPPTransitions.derandomize_meanField_uniformLift_eq {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ)
    (idx : Fin (d * tr.commonDenom)) :
    tr.derandomize.meanFieldDrift (tr.uniformLift x) idx =
      (1 / (tr.commonDenom : ℝ)) * tr.balanceField x (finProdOrig idx) := by
  classical
  rw [Kurtz.PopProtocol.meanFieldDrift, PLPPTransitions.derandomize]
  rw [Finset.sum_image]
  · rw [← Equiv.sum_comp
        (Equiv.prodCongr
          (finProdEquiv d tr.commonDenom).symm
          (finProdEquiv d tr.commonDenom).symm)]
    simpa [PLPPTransitions.derandomizedReaction, Kurtz.PPReaction.netChange,
      Kurtz.PPReaction.massActionRate, PLPPTransitions.uniformLift,
      finProdOrig, finProdCoin, finProdEncode, Prod.ext_iff, eq_comm] using
        derandomized_replicated_expanded_eq tr x (finProdOrig idx) (finProdCoin idx)
  · intro a _ b _ h
    exact tr.derandomizedReaction_injective h

/-- The same uniform-lift vector-field identity for the derandomized protocol
viewed as a `{0,1}` PLPP.  This is the tangent-vector statement for the
coin-uniform submanifold: at `uniformLift x`, every product coordinate has
velocity `balanceField x / m`. -/
theorem PLPPTransitions.derandomizeTransitions_balanceField_uniformLift_eq {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ)
    (idx : Fin (d * tr.commonDenom)) :
    tr.derandomizeTransitions.balanceField (tr.uniformLift x) idx =
      (1 / (tr.commonDenom : ℝ)) * tr.balanceField x (finProdOrig idx) := by
  rw [PLPPTransitions.derandomizeTransitions_balanceField_eq_meanFieldDrift]
  exact tr.derandomize_meanField_uniformLift_eq x idx

/-- The derandomized PLPP vector field is tangent to the coin-uniform
submanifold.  Equivalently, at a uniform lift the vector field is the uniform
lift of the original PLPP vector field. -/
theorem PLPPTransitions.derandomizeTransitions_balanceField_uniformLift {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) :
    tr.derandomizeTransitions.balanceField (tr.uniformLift x) =
      tr.uniformLift (tr.balanceField x) := by
  ext idx
  rw [tr.derandomizeTransitions_balanceField_uniformLift_eq x idx]
  simp [PLPPTransitions.uniformLift, div_eq_mul_inv, mul_comm]

/-- On coin-uniform directions, the original-state marginal intertwines the
formal linearization of the product drift with the formal linearization of the
original PLPP balance field.  This is the precise Jacobian-level statement
covered by the already-proved uniform-submanifold identities. -/
theorem PLPPTransitions.originalMarginal_derandomized_formalLinearization_uniformLift {d : ℕ}
    (tr : PLPPTransitions d) (x z : Fin d → ℝ) :
    tr.originalMarginal
        (tr.derandomizeTransitions.balanceFieldFormalLinearizationAt
          (tr.uniformLift x) (tr.uniformLift z)) =
      tr.balanceFieldFormalLinearizationAt x z := by
  rw [PLPPTransitions.balanceFieldFormalLinearizationAt]
  rw [← tr.uniformLift_add x z]
  simp [PLPPTransitions.balanceFieldFormalLinearizationAt,
    tr.derandomizeTransitions_balanceField_uniformLift, tr.originalMarginal_sub,
    tr.originalMarginal_uniformLift]

/-- On the coin-uniform submanifold, the original-state marginal evolves by
the original PLPP balance field.  The `1/m` from each product coordinate
cancels after summing over the `m` coin coordinates. -/
theorem PLPPTransitions.originalMarginal_derandomized_drift_uniformLift {d : ℕ}
    (tr : PLPPTransitions d) (x : Fin d → ℝ) (I : Fin d) :
    tr.originalMarginal
        (tr.derandomizeTransitions.balanceField (tr.uniformLift x)) I =
      tr.balanceField x I := by
  classical
  have hm_ne : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  simp only [PLPPTransitions.originalMarginal]
  simp_rw [tr.derandomizeTransitions_balanceField_uniformLift_eq x]
  simp only [finProdOrig_encode]
  calc
    (∑ _r : Fin tr.commonDenom,
      (1 / (tr.commonDenom : ℝ)) * tr.balanceField x I)
        = (tr.commonDenom : ℝ) *
            ((1 / (tr.commonDenom : ℝ)) * tr.balanceField x I) := by
            simp [Finset.sum_const]
    _ = tr.balanceField x I := by field_simp [hm_ne]

/-- If an original trajectory solves the PLPP balance equation, then its
uniform lift solves the derandomized PLPP balance equation.  This is the
ODE-level forward-invariance witness for trajectories that start in the
coin-uniform submanifold. -/
theorem PLPPTransitions.uniformLift_solves_derandomized_ode {d : ℕ}
    (tr : PLPPTransitions d) (sol : ℝ → Fin d → ℝ)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t) :
    ∀ t ≥ 0, HasDerivAt (fun s => tr.uniformLift (sol s))
      (tr.derandomizeTransitions.balanceField (tr.uniformLift (sol t))) t := by
  intro t ht
  rw [tr.derandomizeTransitions_balanceField_uniformLift]
  rw [hasDerivAt_pi]
  intro idx
  have hcoord := (hasDerivAt_pi.mp (hsol_ode t ht)) (finProdOrig idx)
  have hscaled :
      HasDerivAt
        (fun s => sol s (finProdOrig idx) * (tr.commonDenom : ℝ)⁻¹)
        (tr.balanceField (sol t) (finProdOrig idx) * (tr.commonDenom : ℝ)⁻¹) t :=
    hcoord.mul_const _
  simpa [PLPPTransitions.uniformLift, div_eq_mul_inv] using hscaled

/-- The derandomized product balance field is Lipschitz on bounded balls.
This is the exact regularity input needed for Picard uniqueness on compact
time intervals, and follows from the generic PLPP balance-field lemma applied
to the derandomized transition table. -/
theorem PLPPTransitions.derandomizeTransitions_balanceField_lipschitz_on_ball {d : ℕ}
    (tr : PLPPTransitions d) (R : ℝ) (hR : 0 < R) :
    ∃ L > 0, ∀ x y : Fin (d * tr.commonDenom) → ℝ, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖tr.derandomizeTransitions.balanceField x -
          tr.derandomizeTransitions.balanceField y‖ ≤ L * ‖x - y‖ :=
  tr.derandomizeTransitions.balanceField_lipschitz_on_ball R hR

/-- A closed-ball `LipschitzOnWith` form of
`derandomizeTransitions_balanceField_lipschitz_on_ball`, matching Mathlib's
ODE uniqueness API. -/
theorem PLPPTransitions.derandomizeTransitions_balanceField_lipschitzOn_closedBall {d : ℕ}
    (tr : PLPPTransitions d) (R : ℝ) (hR : 0 < R) :
    ∃ K : NNReal,
      LipschitzOnWith K tr.derandomizeTransitions.balanceField
        (Metric.closedBall (0 : Fin (d * tr.commonDenom) → ℝ) R) := by
  obtain ⟨L, hL_pos, hLip⟩ :=
    tr.derandomizeTransitions_balanceField_lipschitz_on_ball R hR
  refine ⟨⟨L, le_of_lt hL_pos⟩, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact hLip x y (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hy)

/-- ODE uniqueness for the derandomized balance equation on a bounded time
interval, assuming both candidate trajectories remain in a common closed ball.
This is the reusable Picard-uniqueness step for trajectories on the
coin-uniform submanifold. -/
theorem PLPPTransitions.derandomized_ode_unique_on_Icc_of_norm_le {d : ℕ}
    (tr : PLPPTransitions d) {a b R : ℝ} (hR : 0 < R)
    (f g : ℝ → Fin (d * tr.commonDenom) → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_ode : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt f (tr.derandomizeTransitions.balanceField (f t))
        (Set.Ici t) t)
    (hf_bound : ∀ t ∈ Set.Ico a b, ‖f t‖ ≤ R)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_ode : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt g (tr.derandomizeTransitions.balanceField (g t))
        (Set.Ici t) t)
    (hg_bound : ∀ t ∈ Set.Ico a b, ‖g t‖ ≤ R)
    (hinit : f a = g a) :
    Set.EqOn f g (Set.Icc a b) := by
  obtain ⟨K, hLip⟩ :=
    tr.derandomizeTransitions_balanceField_lipschitzOn_closedBall R hR
  refine ODE_solution_unique_of_mem_Icc_right
    (v := fun _ x => tr.derandomizeTransitions.balanceField x)
    (s := fun _ => Metric.closedBall (0 : Fin (d * tr.commonDenom) → ℝ) R)
    (K := K) ?_ hf_cont hf_ode ?_ hg_cont hg_ode ?_ hinit
  · intro _ _
    exact hLip
  · intro t ht
    simpa [Metric.mem_closedBall, dist_eq_norm] using hf_bound t ht
  · intro t ht
    simpa [Metric.mem_closedBall, dist_eq_norm] using hg_bound t ht

/-- If a derandomized trajectory and a lifted original trajectory start at
the same product state and both remain in a common bounded ball on `[0,T]`,
then Picard uniqueness identifies them throughout `[0,T]`. -/
theorem PLPPTransitions.derandomized_ode_eq_uniformLift_on_Icc_of_norm_le {d : ℕ}
    (tr : PLPPTransitions d) {T R : ℝ} (_hT : 0 ≤ T) (hR : 0 < R)
    (sol : ℝ → Fin d → ℝ) (ysol : ℝ → Fin (d * tr.commonDenom) → ℝ)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    (hysol_cont : ContinuousOn ysol (Set.Icc 0 T))
    (hysol_ode : ∀ t ≥ 0,
      HasDerivAt ysol (tr.derandomizeTransitions.balanceField (ysol t)) t)
    (hlift_cont : ContinuousOn (fun t => tr.uniformLift (sol t)) (Set.Icc 0 T))
    (hysol_bound : ∀ t ∈ Set.Ico 0 T, ‖ysol t‖ ≤ R)
    (hlift_bound : ∀ t ∈ Set.Ico 0 T, ‖tr.uniformLift (sol t)‖ ≤ R)
    (hinit : ysol 0 = tr.uniformLift (sol 0)) :
    Set.EqOn ysol (fun t => tr.uniformLift (sol t)) (Set.Icc 0 T) := by
  refine tr.derandomized_ode_unique_on_Icc_of_norm_le hR ysol
    (fun t => tr.uniformLift (sol t)) hysol_cont ?_ hysol_bound
    hlift_cont ?_ hlift_bound hinit
  · intro t ht
    exact (hysol_ode t ht.1).hasDerivWithinAt
  · intro t ht
    exact (tr.uniformLift_solves_derandomized_ode sol hsol_ode t ht.1).hasDerivWithinAt

/-- Replicate an original simplex point uniformly over the cyclic coin
coordinate. -/
noncomputable def SimplexEquilibrium.replicatedPoint {d : ℕ}
    {tr : PLPPTransitions d} (eq : SimplexEquilibrium tr) :
    Fin (d * tr.commonDenom) → ℝ :=
  fun idx => eq.point (finProdOrig idx) / (tr.commonDenom : ℝ)

/-- The replicated equilibrium is the uniform lift of the original equilibrium
point. -/
theorem SimplexEquilibrium.replicatedPoint_eq_uniformLift {d : ℕ}
    {tr : PLPPTransitions d} (eq : SimplexEquilibrium tr) :
    eq.replicatedPoint = tr.uniformLift eq.point := rfl

theorem SimplexEquilibrium.replicatedPoint_nonneg {d : ℕ}
    {tr : PLPPTransitions d} (eq : SimplexEquilibrium tr) :
    ∀ idx, 0 ≤ eq.replicatedPoint idx := by
  intro idx
  dsimp [SimplexEquilibrium.replicatedPoint]
  exact div_nonneg (eq.nonneg _) (Nat.cast_nonneg _)

theorem SimplexEquilibrium.replicatedPoint_sum_one {d : ℕ}
    {tr : PLPPTransitions d} (eq : SimplexEquilibrium tr) :
    ∑ idx : Fin (d * tr.commonDenom), eq.replicatedPoint idx = 1 := by
  classical
  have hm_ne : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  rw [← Equiv.sum_comp (finProdEquiv d tr.commonDenom).symm]
  simp only [SimplexEquilibrium.replicatedPoint, finProdOrig, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin d, ∑ _r : Fin tr.commonDenom,
      eq.point x / (tr.commonDenom : ℝ))
        = ∑ x : Fin d, (tr.commonDenom : ℝ) *
            (eq.point x / (tr.commonDenom : ℝ)) := by
            apply Finset.sum_congr rfl
            intro x _
            simp [Finset.sum_const]
    _ = ∑ x : Fin d, eq.point x := by
        apply Finset.sum_congr rfl
        intro x _
        field_simp [hm_ne]
    _ = 1 := eq.sum_one

theorem SimplexEquilibrium.originalMarginal_replicatedPoint {d : ℕ}
    {tr : PLPPTransitions d} (eq : SimplexEquilibrium tr) :
    tr.originalMarginal eq.replicatedPoint = eq.point := by
  classical
  ext i
  have hm_ne : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  simp only [PLPPTransitions.originalMarginal, SimplexEquilibrium.replicatedPoint,
    finProdOrig_encode]
  calc
    (∑ _r : Fin tr.commonDenom, eq.point i / (tr.commonDenom : ℝ))
        = (tr.commonDenom : ℝ) * (eq.point i / (tr.commonDenom : ℝ)) := by
            simp [Finset.sum_const]
    _ = eq.point i := by field_simp [hm_ne]

theorem SimplexEquilibrium.coinMarginal_replicatedPoint {d : ℕ}
    {tr : PLPPTransitions d} (eq : SimplexEquilibrium tr) :
    tr.coinMarginal eq.replicatedPoint =
      fun _r : Fin tr.commonDenom => 1 / (tr.commonDenom : ℝ) := by
  classical
  ext r
  simp only [PLPPTransitions.coinMarginal, SimplexEquilibrium.replicatedPoint,
    finProdOrig_encode]
  calc
    (∑ i : Fin d, eq.point i / (tr.commonDenom : ℝ))
        = (∑ i : Fin d, eq.point i) / (tr.commonDenom : ℝ) := by
            rw [Finset.sum_div]
    _ = 1 / (tr.commonDenom : ℝ) := by rw [eq.sum_one]

theorem SimplexEquilibrium.replicatedPoint_marked_sum {d : ℕ}
    {tr : PLPPTransitions d} (eq : SimplexEquilibrium tr)
    (marked : Finset (Fin d)) :
    ∑ idx ∈ tr.derandomizedMarked marked, eq.replicatedPoint idx =
      ∑ i ∈ marked, eq.point i := by
  classical
  have hm_ne : (tr.commonDenom : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt tr.commonDenom_pos)
  simp only [PLPPTransitions.derandomizedMarked, SimplexEquilibrium.replicatedPoint]
  rw [Finset.sum_filter]
  rw [← Equiv.sum_comp (finProdEquiv d tr.commonDenom).symm]
  simp only [finProdOrig, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : Fin d, ∑ _r : Fin tr.commonDenom,
      if x ∈ marked then eq.point x / (tr.commonDenom : ℝ) else 0)
        = ∑ x : Fin d,
            if x ∈ marked then
              (tr.commonDenom : ℝ) * (eq.point x / (tr.commonDenom : ℝ))
            else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x ∈ marked
            · simp [hx, Finset.sum_const]
            · simp [hx]
    _ = ∑ x : Fin d, if x ∈ marked then eq.point x else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ marked
        · simp [hx]
          field_simp [hm_ne]
        · simp [hx]
    _ = ∑ i ∈ marked, eq.point i := by
        rw [← Finset.sum_filter]
        simp

/-- On the coin-uniform submanifold, derandomized isolated convergence follows
from the original isolated convergence plus Picard uniqueness for the
derandomized product ODE.

This deliberately does not claim full-basin convergence.  It covers exactly
solutions that start as a uniform lift of an original trajectory; the
finite-interval boundedness and continuity hypotheses are the analytic inputs
needed to invoke Mathlib's closed-ball ODE uniqueness theorem on every compact
time interval. -/
theorem PLPPTransitions.derandomized_uniformLift_solution_tendsto_replicatedPoint {d : ℕ}
    {tr : PLPPTransitions d} {marked : Finset (Fin d)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin d → ℝ)
    (ysol : ℝ → Fin (d * tr.commonDenom) → ℝ)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t ≥ 0, HasDerivAt sol (tr.balanceField (sol t)) t)
    (hysol_ode : ∀ t ≥ 0,
      HasDerivAt ysol (tr.derandomizeTransitions.balanceField (ysol t)) t)
    (hysol_cont : ∀ T ≥ 0, ContinuousOn ysol (Set.Icc 0 T))
    (hlift_cont : ∀ T ≥ 0, ContinuousOn (fun t => tr.uniformLift (sol t)) (Set.Icc 0 T))
    (hbound : ∀ T ≥ 0, ∃ R > 0,
      (∀ t ∈ Set.Ico 0 T, ‖ysol t‖ ≤ R) ∧
        (∀ t ∈ Set.Ico 0 T, ‖tr.uniformLift (sol t)‖ ≤ R))
    (hinit : ysol 0 = tr.uniformLift (sol 0)) :
    Filter.Tendsto ysol Filter.atTop (nhds hcomp.eq.replicatedPoint) := by
  have hconv := hcomp.converges sol hsol_init hsol_ode
  have hlift_tendsto :
      Filter.Tendsto (fun t => tr.uniformLift (sol t)) Filter.atTop
        (nhds hcomp.eq.replicatedPoint) := by
    have hcont := tr.continuous_uniformLift
    have htendsto := (hcont.tendsto hcomp.eq.point).comp hconv
    simpa [SimplexEquilibrium.replicatedPoint_eq_uniformLift] using htendsto
  refine hlift_tendsto.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  obtain ⟨R, hR_pos, hysol_bound, hlift_bound⟩ := hbound t ht
  have heq_on :=
    tr.derandomized_ode_eq_uniformLift_on_Icc_of_norm_le ht hR_pos
      sol ysol hsol_ode (hysol_cont t ht) hysol_ode (hlift_cont t ht)
      hysol_bound hlift_bound hinit
  exact (heq_on ⟨ht, le_rfl⟩).symm

/-! ## Correctness: equilibrium preservation

The key theorem: the de-randomized protocol has equilibrium
  ν* = (ν_1/m, ..., ν_1/m, ..., ν_d/m, ..., ν_d/m)
where (ν_1,...,ν_d) is the PLPP equilibrium, and each ν_i is
repeated m times (once per coin state). -/

/-- If x* is a simplex equilibrium of the original PLPP, then the
"replicated" vector x*_I,R = x*_I / m is a simplex equilibrium of the
de-randomized protocol. -/
theorem derandomize_preserves_equilibrium {d : ℕ}
    (tr : PLPPTransitions d)
    (eq : SimplexEquilibrium tr) :
    let m := tr.commonDenom
    let pp := tr.derandomize
    let ν_star : Fin (d * m) → ℝ := eq.replicatedPoint
    pp.meanFieldDrift ν_star = 0 := by
  classical
  dsimp
  ext idx
  rw [Kurtz.PopProtocol.meanFieldDrift, PLPPTransitions.derandomize]
  rw [Finset.sum_image]
  · rw [← Equiv.sum_comp
        (Equiv.prodCongr
          (finProdEquiv d tr.commonDenom).symm
          (finProdEquiv d tr.commonDenom).symm)]
    simpa [PLPPTransitions.derandomizedReaction, Kurtz.PPReaction.netChange,
      Kurtz.PPReaction.massActionRate, SimplexEquilibrium.replicatedPoint,
      finProdOrig, finProdCoin, finProdEncode, Prod.ext_iff, eq_comm] using
        derandomized_replicated_expanded_zero tr eq (finProdOrig idx) (finProdCoin idx)
  · intro a _ b _ h
    exact tr.derandomizedReaction_injective h

/-- Conditional continuum derandomization.

All algebraic fields are discharged by the uniform-lift lemmas.  The remaining
assumption is exactly the ODE invariance/reduction statement for the
coin-uniform submanifold:
`t ↦ uniformLift (C.sol t)` must solve the derandomized PLPP balance equation.
This is the only missing piece for the unconditional continuum theorem. -/
theorem derandomize_preserves_continuum_computation_of_ode {d : ℕ}
    {tr : PLPPTransitions d} {marked : Finset (Fin d)} {ν : ℝ}
    (C : PLPPContinuumComputation tr marked ν)
    (hode : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => tr.uniformLift (C.sol s))
        (tr.derandomizeTransitions.balanceField (tr.uniformLift (C.sol t))) t) :
    Nonempty (PLPPContinuumComputation tr.derandomizeTransitions
      (tr.derandomizedMarked marked) ν) := by
  classical
  refine ⟨{
    sol := fun t => tr.uniformLift (C.sol t)
    init_rational := ?_
    init_simplex := ?_
    init_nonneg := ?_
    simplex := ?_
    nonneg := ?_
    ode := hode
    readout_tendsto := ?_
  }⟩
  · intro idx
    obtain ⟨q, hq⟩ := C.init_rational (finProdOrig idx)
    refine ⟨q / (tr.commonDenom : ℚ), ?_⟩
    dsimp [PLPPTransitions.uniformLift]
    rw [hq]
    norm_num
  · rw [tr.uniformLift_sum]
    exact C.init_simplex
  · intro idx
    dsimp [PLPPTransitions.uniformLift]
    exact div_nonneg (C.init_nonneg _) (Nat.cast_nonneg _)
  · intro t ht
    rw [tr.uniformLift_sum]
    exact C.simplex t ht
  · intro t ht idx
    dsimp [PLPPTransitions.uniformLift]
    exact div_nonneg (C.nonneg t ht _) (Nat.cast_nonneg _)
  · have hread :
        (fun t => ∑ idx ∈ tr.derandomizedMarked marked,
            tr.uniformLift (C.sol t) idx) =
          fun t => ∑ i ∈ marked, C.sol t i := by
        funext t
        rw [tr.uniformLift_marked_sum]
    simpa [hread] using C.readout_tendsto

/-- Continuum derandomization for the deterministic product protocol, viewed as
a `{0,1}` PLPP on product states.  The uniform lift of the original ODE
trajectory solves the derandomized PLPP balance equation because that balance
field is the PopProtocol mean-field drift, and the drift has already been
computed on the coin-uniform submanifold. -/
theorem derandomize_preserves_continuum_computation {d : ℕ}
    {tr : PLPPTransitions d} {marked : Finset (Fin d)} {ν : ℝ}
    (C : PLPPContinuumComputation tr marked ν) :
    Nonempty (PLPPContinuumComputation tr.derandomizeTransitions
      (tr.derandomizedMarked marked) ν) := by
  classical
  refine derandomize_preserves_continuum_computation_of_ode C ?_
  intro t ht
  rw [hasDerivAt_pi]
  intro idx
  have hcoord := (hasDerivAt_pi.mp (C.ode t ht)) (finProdOrig idx)
  have hscaled :
      HasDerivAt
        (fun s => C.sol s (finProdOrig idx) * (tr.commonDenom : ℝ)⁻¹)
        (tr.balanceField (C.sol t) (finProdOrig idx) * (tr.commonDenom : ℝ)⁻¹) t :=
    hcoord.mul_const _
  have hfield :
      (tr.derandomizeTransitions.balanceField (tr.uniformLift (C.sol t))) idx =
        (1 / (tr.commonDenom : ℝ)) * tr.balanceField (C.sol t) (finProdOrig idx) := by
    rw [PLPPTransitions.derandomizeTransitions_balanceField_eq_meanFieldDrift]
    exact tr.derandomize_meanField_uniformLift_eq (C.sol t) idx
  rw [hfield]
  simpa [PLPPTransitions.uniformLift, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hscaled

/-- Readout-level derandomization from the isolated API.

This is the sound composition route for Koegler's actual p.93 argument:
an isolated computation plus a concrete rational-initialized ODE trajectory in
its basin first gives a `PLPPContinuumComputation`; the already-proved
uniform-lift derandomization theorem then gives a continuum computation for
the deterministic product protocol.

The extra trajectory hypotheses are necessary because
`PLPPIsolatedComputation` records stability of all basin trajectories, but it
does not itself contain a rational initial condition or an ODE existence
witness. -/
theorem derandomize_preserves_isolated_as_continuum_of_solution {d : ℕ}
    {tr : PLPPTransitions d} {marked : Finset (Fin d)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν)
    (sol : ℝ → Fin d → ℝ)
    (init_rational : ∀ i, ∃ q : ℚ, sol 0 i = (q : ℝ))
    (init_simplex : ∑ i, sol 0 i = 1)
    (init_nonneg : ∀ i, 0 ≤ sol 0 i)
    (simplex : ∀ t, 0 ≤ t → ∑ i, sol t i = 1)
    (nonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol t i)
    (hsol_init : sol 0 ∈ hcomp.basin)
    (hsol_ode : ∀ t, 0 ≤ t → HasDerivAt sol (tr.balanceField (sol t)) t) :
    Nonempty (PLPPContinuumComputation tr.derandomizeTransitions
      (tr.derandomizedMarked marked) ν) :=
  by
    let C : PLPPContinuumComputation tr marked ν :=
      { sol := sol
        init_rational := init_rational
        init_simplex := init_simplex
        init_nonneg := init_nonneg
        simplex := simplex
        nonneg := nonneg
        ode := hsol_ode
        readout_tendsto := by
          have hconv := hcomp.converges sol hsol_init hsol_ode
          have hread_cont : Continuous fun y : Fin d → ℝ => ∑ i ∈ marked, y i :=
            continuous_finset_sum _ fun i _ => continuous_apply i
          simpa [hcomp.target_eq] using (hread_cont.tendsto hcomp.eq.point).comp hconv }
    exact derandomize_preserves_continuum_computation C

/-- Koegler's cyclic-coin Lyapunov term from thesis p.93:
`g(y) = ∑_R (coinMarginal_R(y) - 1/m)^2`. -/
noncomputable def PLPPTransitions.coinSqLyapunov {d : ℕ}
    (tr : PLPPTransitions d) (y : Fin (d * tr.commonDenom) → ℝ) : ℝ :=
  ∑ R : Fin tr.commonDenom,
    (tr.coinMarginal y R - 1 / (tr.commonDenom : ℝ)) ^ 2

/-- The defect in Koegler thesis p.93:
`∑_R b_{I,R}(y) - b_I(originalMarginal y)`.

This is zero on the coin-uniform submanifold, by the already-proved
uniform-lift drift identity.  Koegler's proof needs the stronger local
estimate that this defect is bounded by a constant times the square of the
coin-marginal deviation. -/
noncomputable def PLPPTransitions.originalMarginalDriftDefect {d : ℕ}
    (tr : PLPPTransitions d) (y : Fin (d * tr.commonDenom) → ℝ)
    (I : Fin d) : ℝ :=
  tr.originalMarginal (tr.derandomizeTransitions.balanceField y) I -
    tr.balanceField (tr.originalMarginal y) I

/-- The local "some basic computations" estimate in Koegler thesis p.93.

This is the estimate used by the combined Lyapunov function
`Ltilde(originalMarginal y) + K * coinSqLyapunov y`: the product protocol's
original-marginal drift differs from the original PLPP drift only by a term
quadratic in the cyclic-coin marginal error. -/
structure PLPPTransitions.KoeglerMarginalDefectBoundAt {d : ℕ}
    {tr : PLPPTransitions d} {marked : Finset (Fin d)} {ν : ℝ}
    (hcomp : PLPPIsolatedComputation tr marked ν) where
  beta : ℝ
  beta_pos : 0 < beta
  radius : ℝ
  radius_pos : 0 < radius
  bound :
    ∀ y : Fin (d * tr.commonDenom) → ℝ,
      y ∈ Simplex (d * tr.commonDenom) →
      ‖y - hcomp.eq.replicatedPoint‖ < radius →
      ∀ I : Fin d,
        |tr.originalMarginalDriftDefect y I| ≤ beta * tr.coinSqLyapunov y

end Ripple
