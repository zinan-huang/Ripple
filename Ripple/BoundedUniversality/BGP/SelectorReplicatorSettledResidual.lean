import Ripple.BoundedUniversality.BGP.SelectorReplicatorEncoder
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStartHaltExact
import Ripple.BoundedUniversality.BGP.MUReplicatorSettledConstruction
import Ripple.BoundedUniversality.BGP.ContractFlagAtomicMU
import Ripple.BoundedUniversality.BGP.SelectorReplicatorUTubeMU
import Ripple.BoundedUniversality.BGP.IntComputable
import Ripple.BoundedUniversality.BGP.BGPParams38
import Ripple.BoundedUniversality.BGP.EncBoxCore
import Ripple.BoundedUniversality.BGP.SelectorDuhamelWrite
import Ripple.BoundedUniversality.BGP.SelectorReplicatorSettledZ

/-!
# Selector-replicator settled residual wrapper

This file removes the outer `MUReplicatorSettledHaltFacts` hypothesis from the
realized selector-replicator headline.  The remaining assumptions are the
shape-correct analytic residuals consumed by `muReplicatorSettledHaltFacts_param`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Filter Set
open scoped BigOperators Topology

/-- The realized selector-replicator solution family with the finite-horizon
bound supplied by `selector_replicator_finiteHorizonBound_MU`. -/
abbrev solMUReplRealizedFinite
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ)) :
    MUReplicatorSolFamily eta heta Mcy κ₀ g₀ :=
  solMUReplRealized eta heta Mcy κ₀ g₀ HP Kq R selectorInitX0
    (fun w => selector_replicator_finiteHorizonBound_MU eta heta Mcy κ₀ g₀ HP Kq R
      selectorInitX0 w hκ0 hg0 hKq0)

private def ratConstPresenter (q : ℚ) : ℤ × ℕ :=
  (q.num, q.den)

private theorem ratConstPresenter_den_ne_zero (q : ℚ) :
    (ratConstPresenter q).2 ≠ 0 := by
  simp [ratConstPresenter, q.den_nz]

private theorem ratConstPresenter_spec (q : ℚ) :
    q = (ratConstPresenter q).1 / ((ratConstPresenter q).2 : ℚ) := by
  simpa [ratConstPresenter] using (Rat.num_div_den q).symm

private theorem replInitComputable_fin_prod_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∏ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact Computable.const 1
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∏ i : Fin d, f i.succ a :=
        replInitComputable_fin_prod_nat (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_mul.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.prod_univ_succ]

private theorem replInitComputable_fin_sum_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∑ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact Computable.const 0
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∑ i : Fin d, f i.succ a :=
        replInitComputable_fin_sum_nat (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_add.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.sum_univ_succ]

private def replInitSqNat (n : ℕ) : ℕ := n * n

private theorem computable_replInitSqNat : Computable replInitSqNat :=
  Primrec.nat_mul.to_comp.comp Computable.id Computable.id

private theorem computable_replInitNat_pow_two : Computable fun n : ℕ => n ^ 2 :=
  computable_replInitSqNat.of_eq fun n => by simp [replInitSqNat, pow_two]

private theorem computable_replInitF_apply {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hf : Computable f) (i : Fin n) : Computable fun w => f w i :=
  Computable.fin_app.comp hf (Computable.const i)

private theorem computable_replInitFinLambda {α σ : Type*} [Primcodable α] [Primcodable σ]
    {n : ℕ} {f : α → Fin n → σ}
    (hf : ∀ i, Computable fun a => f a i) : Computable f := by
  have hv : Computable fun a => List.Vector.ofFn fun i => f a i :=
    Computable.vector_ofFn hf
  have he : Computable (Equiv.vectorEquivFin σ n) := Primrec.of_equiv_symm.to_comp
  exact (he.comp hv).of_eq fun a => by
    funext i
    exact List.Vector.get_ofFn (fun i => f a i) i

private noncomputable def euclSphereDprod {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∏ i : Fin n, (f w i).2 ^ 2

private noncomputable def euclSphereSsum {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∑ i : Fin n, (f w i).1.natAbs ^ 2 *
    (euclSphereDprod f w / ((f w i).2 ^ 2))

private noncomputable def euclSphereDen {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  euclSphereSsum f w + euclSphereDprod f w

private noncomputable def euclSpherePresenter {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : Fin (n + 1) → ℤ × ℕ :=
  let D := euclSphereDprod f w
  let S := euclSphereSsum f w
  Fin.cases
    (Int.ofNat S + (-1 : ℤ) * Int.ofNat D, euclSphereDen f w)
    (fun i => (2 * (f w i).1 * Int.ofNat D, (f w i).2 * euclSphereDen f w))

private noncomputable def rationalSphereInitQ {n : ℕ}
    (x : ℕ → Fin n → ℚ) (w : ℕ) : Fin (n + 1) → ℚ :=
  let den : ℚ := (∑ i : Fin n, x w i ^ 2) + 1
  Fin.cases (((∑ i : Fin n, x w i ^ 2) - 1) / den)
    (fun i => 2 * x w i / den)

private theorem euclSphereDprod_pos {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < euclSphereDprod f w := by
  unfold euclSphereDprod
  exact Finset.prod_pos fun i _hi =>
    Nat.pow_pos (Nat.pos_of_ne_zero (hden w i))

private theorem euclSphereDprod_cast_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((euclSphereDprod f w : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt (euclSphereDprod_pos (f := f) hden w)

private theorem euclSphereDen_pos {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < euclSphereDen f w := by
  unfold euclSphereDen
  exact Nat.add_pos_right _ (euclSphereDprod_pos (f := f) hden w)

private theorem euclSphereDen_cast_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((euclSphereDen f w : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt (euclSphereDen_pos (f := f) hden w)

private theorem euclSphereDprod_divisor {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) (i : Fin n) :
    (f w i).2 ^ 2 ∣ euclSphereDprod f w := by
  unfold euclSphereDprod
  exact Finset.dvd_prod_of_mem (fun i : Fin n => (f w i).2 ^ 2) (Finset.mem_univ i)

private theorem euclSphereSsum_cast_eq {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((euclSphereSsum f w : ℕ) : ℚ) =
      (euclSphereDprod f w : ℚ) *
        ∑ i : Fin n, (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
  unfold euclSphereSsum
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hdvd : (f w i).2 ^ 2 ∣ euclSphereDprod f w :=
    euclSphereDprod_divisor f w i
  have hdQ : (((f w i).2 ^ 2 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (hden w i)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_div hdvd hdQ, Nat.cast_pow]
  have hnabs : (((f w i).1.natAbs : ℕ) : ℚ) ^ 2 = ((f w i).1 : ℚ) ^ 2 := by
    rw [show (((f w i).1.natAbs : ℕ) : ℚ) = ((|(f w i).1| : ℤ) : ℚ) by
      exact (Nat.cast_natAbs (α := ℚ) (f w i).1)]
    rw [Int.cast_abs]
    rw [sq_abs]
  rw [hnabs]
  field_simp [pow_ne_zero 2 (by exact_mod_cast hden w i)]

private theorem euclSpherePresenter_den_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) :
    ∀ w j, (euclSpherePresenter f w j).2 ≠ 0 := by
  intro w j
  refine Fin.cases ?_ ?_ j
  · change euclSphereDen f w ≠ 0
    exact ne_of_gt (euclSphereDen_pos (f := f) hden w)
  · intro i
    change (f w i).2 * euclSphereDen f w ≠ 0
    exact Nat.mul_ne_zero (hden w i) (ne_of_gt (euclSphereDen_pos (f := f) hden w))

private theorem computable_euclSphereDprod {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (euclSphereDprod f) := by
  unfold euclSphereDprod
  refine replInitComputable_fin_prod_nat ?_
  intro i
  exact computable_replInitNat_pow_two.comp
    (Computable.snd.comp (computable_replInitF_apply hf i))

private theorem computable_euclSphereSsum {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (euclSphereSsum f) := by
  unfold euclSphereSsum
  refine replInitComputable_fin_sum_nat ?_
  intro i
  have hfi := computable_replInitF_apply hf i
  have hn : Computable fun w => (f w i).1.natAbs :=
    computable_int_natAbs.comp (Computable.fst.comp hfi)
  have hn2 : Computable fun w => (f w i).1.natAbs ^ 2 :=
    computable_replInitNat_pow_two.comp hn
  have hd2 : Computable fun w => (f w i).2 ^ 2 :=
    computable_replInitNat_pow_two.comp (Computable.snd.comp hfi)
  have hquot : Computable fun w => euclSphereDprod f w / ((f w i).2 ^ 2) :=
    Primrec.nat_div.to_comp.comp (computable_euclSphereDprod hf) hd2
  exact Primrec.nat_mul.to_comp.comp hn2 hquot

private theorem computable_euclSphereDen {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (euclSphereDen f) := by
  unfold euclSphereDen
  exact Primrec.nat_add.to_comp.comp (computable_euclSphereSsum hf)
    (computable_euclSphereDprod hf)

private theorem computable_euclSpherePresenter {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (euclSpherePresenter f) := by
  classical
  have hD := computable_euclSphereDprod hf
  have hS := computable_euclSphereSsum hf
  have hDen := computable_euclSphereDen hf
  have hDInt : Computable fun w => Int.ofNat (euclSphereDprod f w) :=
    computable_int_ofNat.comp hD
  have hSInt : Computable fun w => Int.ofNat (euclSphereSsum f w) :=
    computable_int_ofNat.comp hS
  have hNegD : Computable fun w => (-1 : ℤ) * Int.ofNat (euclSphereDprod f w) :=
    computable2_int_mul.comp (Computable.const (-1 : ℤ)) hDInt
  have hnum0 : Computable fun w =>
      Int.ofNat (euclSphereSsum f w) + (-1 : ℤ) * Int.ofNat (euclSphereDprod f w) :=
    computable2_int_add.comp hSInt hNegD
  have h0 : Computable fun w =>
      (Int.ofNat (euclSphereSsum f w) + (-1 : ℤ) * Int.ofNat (euclSphereDprod f w),
        euclSphereDen f w) :=
    Computable.pair hnum0 hDen
  refine computable_replInitFinLambda fun j => ?_
  refine Fin.cases ?_ ?_ j
  · exact h0.of_eq fun w => by simp [euclSpherePresenter]
  · intro i
    have hfi := computable_replInitF_apply hf i
    have hn : Computable fun w => (f w i).1 := Computable.fst.comp hfi
    have hd : Computable fun w => (f w i).2 := Computable.snd.comp hfi
    have h2n : Computable fun w => 2 * (f w i).1 :=
      computable2_int_mul.comp (Computable.const 2) hn
    have hnum : Computable fun w => 2 * (f w i).1 * Int.ofNat (euclSphereDprod f w) :=
      computable2_int_mul.comp h2n hDInt
    have hden : Computable fun w => (f w i).2 * euclSphereDen f w :=
      Primrec.nat_mul.to_comp.comp hd hDen
    exact (Computable.pair hnum hden).of_eq fun w => by
      simp [euclSpherePresenter]

private theorem rationalSphereInitQ_presented_of_eucl_presented {n : ℕ}
    {x : ℕ → Fin n → ℚ}
    (hx_presented : ∃ f : ℕ → Fin n → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x w i = (f w i).1 / ((f w i).2 : ℚ)) :
    ∃ g : ℕ → Fin (n + 1) → ℤ × ℕ, Computable g ∧
      ∀ w j, (g w j).2 ≠ 0 ∧
        rationalSphereInitQ x w j = (g w j).1 / ((g w j).2 : ℚ) := by
  classical
  obtain ⟨f, hf, hfval⟩ := hx_presented
  have hden : ∀ w i, (f w i).2 ≠ 0 := fun w i => (hfval w i).1
  refine ⟨euclSpherePresenter f, computable_euclSpherePresenter hf, ?_⟩
  intro w j
  refine ⟨euclSpherePresenter_den_ne_zero (f := f) hden w j, ?_⟩
  have hD : ((euclSphereDprod f w : ℕ) : ℚ) ≠ 0 :=
    euclSphereDprod_cast_ne_zero (f := f) hden w
  have hDen : ((euclSphereDen f w : ℕ) : ℚ) ≠ 0 :=
    euclSphereDen_cast_ne_zero (f := f) hden w
  have hsum :
      (∑ i : Fin n, x w i ^ 2) =
        (euclSphereSsum f w : ℚ) / (euclSphereDprod f w : ℚ) := by
    calc
      (∑ i : Fin n, x w i ^ 2)
          = ∑ i : Fin n, (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [(hfval w i).2]
      _ = (euclSphereSsum f w : ℚ) / (euclSphereDprod f w : ℚ) := by
          have hS := euclSphereSsum_cast_eq (f := f) hden w
          have hSdiv :
              (euclSphereSsum f w : ℚ) / (euclSphereDprod f w : ℚ) =
                ∑ i : Fin n, (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
            rw [hS]
            field_simp [hD]
          exact hSdiv.symm
  refine Fin.cases ?_ ?_ j
  · simp [rationalSphereInitQ, euclSpherePresenter, hsum, euclSphereDen]
    field_simp [hD, hDen]
    ring
  · intro i
    have hdi : ((f w i).2 : ℚ) ≠ 0 := by exact_mod_cast hden w i
    simp [rationalSphereInitQ, euclSpherePresenter, hsum, (hfval w i).2, euclSphereDen]
    field_simp [hD, hDen, hdi]

private noncomputable def selectorReplicatorEuclPresenter {d : ℕ}
    (V : Type) [Fintype V] (f : ℕ → Fin d → ℤ × ℕ)
    (warmGainInit : ℚ) (w : ℕ) : Fin (selectorDim d V) → ℤ × ℕ :=
  Fin.append
    (Fin.append
      (fun k : Fin 4 =>
        if k = 0 then ratConstPresenter 0 else
        if k = 1 then ratConstPresenter 1 else
        if k = 2 then ratConstPresenter 0 else ratConstPresenter 1)
      (Fin.append
        (fun _ : Fin 2 => ratConstPresenter 1)
        (Fin.append (f w) (Fin.append (f w) (fun _ : Fin 1 => ratConstPresenter 0)))))
    (Fin.append
      (fun _ : Fin (Fintype.card V) => ratConstPresenter (1 / (Fintype.card V : ℚ)))
      (Fin.append
        (fun _ : Fin 1 => ratConstPresenter 0)
        (fun _ : Fin 1 => ratConstPresenter warmGainInit)))

private theorem selectorReplicatorEuclPresenter_den_ne_zero {d : ℕ}
    (V : Type) [Fintype V] {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (warmGainInit : ℚ) :
    ∀ w j, (selectorReplicatorEuclPresenter V f warmGainInit w j).2 ≠ 0 := by
  intro w j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k <;> simp [selectorReplicatorEuclPresenter, ratConstPresenter_den_ne_zero]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k <;> simp [selectorReplicatorEuclPresenter, ratConstPresenter_den_ne_zero]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simpa [selectorReplicatorEuclPresenter] using hden w i
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simpa [selectorReplicatorEuclPresenter] using hden w i
          · intro a
            fin_cases a
            simp [selectorReplicatorEuclPresenter, ratConstPresenter_den_ne_zero]
  · intro jt
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp [selectorReplicatorEuclPresenter, ratConstPresenter_den_ne_zero]
    · intro tail
      fin_cases tail <;>
        simp [selectorReplicatorEuclPresenter, Fin.addCases, Fin.append, ratConstPresenter]

private theorem computable_selectorReplicatorEuclPresenter {d : ℕ}
    (V : Type) [Fintype V] {f : ℕ → Fin d → ℤ × ℕ}
    (hf : Computable f) (warmGainInit : ℚ) :
    Computable (selectorReplicatorEuclPresenter V f warmGainInit) := by
  classical
  refine computable_replInitFinLambda fun j => ?_
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k
      · exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenter]
      · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenter]
      · exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenter]
      · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenter]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k
        · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
            simp [selectorReplicatorEuclPresenter]
        · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
            simp [selectorReplicatorEuclPresenter]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          exact (computable_replInitF_apply hf i).of_eq fun w => by
            simp [selectorReplicatorEuclPresenter]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            exact (computable_replInitF_apply hf i).of_eq fun w => by
              simp [selectorReplicatorEuclPresenter]
          · intro a
            fin_cases a
            exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
              simp [selectorReplicatorEuclPresenter]
  · intro jt
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      exact (Computable.const (ratConstPresenter (1 / (Fintype.card V : ℚ)))).of_eq
        fun w => by simp [selectorReplicatorEuclPresenter]
    · intro tail
      fin_cases tail
      · exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenter, Fin.addCases, Fin.append]
      · exact (Computable.const (ratConstPresenter warmGainInit)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenter, Fin.addCases, Fin.append]

private theorem selectorReplicatorEuclPresenter_spec {d : ℕ}
    (V : Type) [Fintype V] {x₀ : ℕ → Fin d → ℚ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hfval : ∀ w i, (f w i).2 ≠ 0 ∧
      x₀ w i = (f w i).1 / ((f w i).2 : ℚ))
    (warmGainInit : ℚ) (w : ℕ) (j : Fin (selectorDim d V)) :
    selectorReplicatorEuclInitQ d V x₀ w warmGainInit j =
      (selectorReplicatorEuclPresenter V f warmGainInit w j).1 /
        ((selectorReplicatorEuclPresenter V f warmGainInit w j).2 : ℚ) := by
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
          ratConstPresenter_spec (0 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
          ratConstPresenter_spec (1 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
          ratConstPresenter_spec (0 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
          ratConstPresenter_spec (1 : ℚ)
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k
        · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
            ratConstPresenter_spec (1 : ℚ)
        · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
            ratConstPresenter_spec (1 : ℚ)
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter, (hfval w i).2]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter, (hfval w i).2]
          · intro a
            fin_cases a
            simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
              ratConstPresenter_spec (0 : ℚ)
  · intro jt
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
        ratConstPresenter_spec (1 / (Fintype.card V : ℚ))
    · intro tail
      fin_cases tail
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
          ratConstPresenter_spec (0 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenter] using
          ratConstPresenter_spec warmGainInit

theorem selectorReplicatorEuclInitQ_presented_of_x0_presented {d : ℕ}
    (V : Type) [Fintype V] {x₀ : ℕ → Fin d → ℚ} (warmGainInit : ℚ)
    (hx₀_presented : ∃ f : ℕ → Fin d → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x₀ w i = (f w i).1 / ((f w i).2 : ℚ)) :
    ∃ g : ℕ → Fin (selectorDim d V) → ℤ × ℕ, Computable g ∧
      ∀ w j, (g w j).2 ≠ 0 ∧
        selectorReplicatorEuclInitQ d V x₀ w warmGainInit j =
          (g w j).1 / ((g w j).2 : ℚ) := by
  classical
  obtain ⟨f, hf, hfval⟩ := hx₀_presented
  refine ⟨selectorReplicatorEuclPresenter V f warmGainInit,
    computable_selectorReplicatorEuclPresenter V hf warmGainInit, ?_⟩
  intro w j
  exact ⟨selectorReplicatorEuclPresenter_den_ne_zero V (fun w i => (hfval w i).1)
      warmGainInit w j,
    selectorReplicatorEuclPresenter_spec V hfval warmGainInit w j⟩

theorem selectorReplicatorSphereInitQ_presented_of_x0_presented {d : ℕ}
    (V : Type) [Fintype V] {x₀ : ℕ → Fin d → ℚ} (warmGainInit : ℚ)
    (hx₀_presented : ∃ f : ℕ → Fin d → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x₀ w i = (f w i).1 / ((f w i).2 : ℚ)) :
    ∃ g : ℕ → Fin (selectorDim d V + 1) → ℤ × ℕ, Computable g ∧
      ∀ w j, (g w j).2 ≠ 0 ∧
        selectorReplicatorSphereInitQ d V x₀ w warmGainInit j =
          (g w j).1 / ((g w j).2 : ℚ) := by
  simpa [rationalSphereInitQ, selectorReplicatorSphereInitQ] using
    rationalSphereInitQ_presented_of_eucl_presented
      (selectorReplicatorEuclInitQ_presented_of_x0_presented V warmGainInit hx₀_presented)

theorem selectorReplicatorSphereInitQ_selectorInitX0_presented (g₀ : ℚ) :
    ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
      Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ) :=
  selectorReplicatorSphereInitQ_presented_of_x0_presented UniversalLocalView g₀
    selectorInitX0_presented

/-- Continuity of the concrete universal readout along any continuous `u`
trajectory. -/
theorem universalPval_continuous_of_cont_u
    (eta : ℚ) (heta : 0 < eta) (v : UniversalLocalView)
    {u : ℝ → Fin d_U → ℝ}
    (hu : ∀ i, Continuous fun t => u t i) :
    Continuous fun t => universalPval eta heta v (u t) := by
  let poly :=
    viewSelectorPolyN universalViewSpecN
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v
  have hucont : Continuous u := continuous_pi hu
  have hpoly :
      Continuous fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) poly := by
    convert
      (MvPolynomial.continuous_eval
        (p := MvPolynomial.map (algebraMap ℚ ℝ) poly)).comp hucont
      using 1
    ext t
    exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (u t) poly
  simpa [universalPval, LambdaN, evalPoly4, poly] using hpoly.sub continuous_const

private theorem mvPolynomial_eval₂_continuous_of_cont_u
    {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) {u : ℝ → σ → ℝ}
    (hu : ∀ i : σ, Continuous fun t => u t i) :
    Continuous fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) p := by
  have hucont : Continuous u := continuous_pi hu
  convert
    (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) p)).comp hucont
    using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (u t) p

private theorem mvPolynomial_eval₂_hasDerivAt
    {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) {u : ℝ → σ → ℝ} {u' : σ → ℝ} {t : ℝ}
    (hu : ∀ i : σ, HasDerivAt (fun τ => u τ i) (u' i) t) :
    HasDerivAt
      (fun τ => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u τ) p)
      ((∑ i : σ,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) (MvPolynomial.pderiv i p) * u' i)) t := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using (hasDerivAt_const t ((algebraMap ℚ ℝ) a))
  | add p q hp hq =>
      convert hp.add hq using 1
      · ext τ
        simp [MvPolynomial.eval₂_add]
      · simp [MvPolynomial.eval₂_add, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
      have hprod := hp.mul (hu n)
      have hsum1 :
          (∑ x : σ,
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) p *
                MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t)
                  (Pi.single (M := fun _ : σ => MvPolynomial σ ℚ) x 1 n) * u' x) =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) p * u' n := by
        classical
        have hcongr :
            (∑ x : σ,
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) p *
                MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t)
                  (Pi.single (M := fun _ : σ => MvPolynomial σ ℚ) x 1 n) * u' x) =
            ∑ x : σ,
              if n = x then MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) p * u' x else 0 := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          by_cases hnx : n = x
          · subst x
            simp
          · simp [hnx]
        rw [hcongr, Finset.sum_ite_eq]
        simp
      have hsum2 :
          (∑ x : σ,
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) (MvPolynomial.pderiv x p) *
                u t n * u' x) =
            (∑ x : σ,
                MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) (MvPolynomial.pderiv x p) * u' x) *
              u t n := by
        calc
          (∑ x : σ,
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) (MvPolynomial.pderiv x p) *
                u t n * u' x)
              = ∑ x : σ,
                  (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) (MvPolynomial.pderiv x p) * u' x) *
                    u t n := by
                    refine Finset.sum_congr rfl ?_
                    intro x _hx
                    ring
          _ = (∑ x : σ,
                MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) (MvPolynomial.pderiv x p) * u' x) *
              u t n := by
              rw [Finset.sum_mul]
      have hsum :
          (∑ i : σ,
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t)
                (MvPolynomial.pderiv i (p * MvPolynomial.X n)) * u' i) =
            (∑ i : σ,
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) (MvPolynomial.pderiv i p) * u' i) *
              u t n +
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t) p * u' n := by
        simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, add_mul]
        rw [Finset.sum_add_distrib, hsum1, hsum2]
      convert hprod using 1
      ext τ
      simp [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]

theorem universalPval_hasDerivAt_of_u_hasDerivAt
    (eta : ℚ) (heta : 0 < eta) (v : UniversalLocalView)
    {u : ℝ → Fin d_U → ℝ} {u' : Fin d_U → ℝ} {t : ℝ}
    (hu : ∀ i : Fin d_U, HasDerivAt (fun τ => u τ i) (u' i) t) :
    HasDerivAt
      (fun τ => universalPval eta heta v (u τ))
      ((∑ i : Fin d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (u t)
            (MvPolynomial.pderiv i
              (viewSelectorPolyN universalViewSpecN
                (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) * u' i)) t := by
  let poly :=
    viewSelectorPolyN universalViewSpecN
      (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v
  have hpoly := mvPolynomial_eval₂_hasDerivAt poly hu
  convert hpoly.sub (hasDerivAt_const t (1 / 2 : ℝ)) using 1
  simp [poly]

def selectorMU_uDerivRHS
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (t : ℝ) (i : Fin d_U) : ℝ :=
  bgpParams38.A * (sol w).α t *
    bGateU bgpParams38.L ((sol w).μ t) t *
      ((sol w).z t i - (sol w).u t i)

def selectorMU_universalPvalDerivRHS
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (v : UniversalLocalView) (t : ℝ) : ℝ :=
  ∑ i : Fin d_U,
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
      (MvPolynomial.pderiv i
        (viewSelectorPolyN universalViewSpecN
          (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) *
      selectorMU_uDerivRHS sol w t i

/-- Coefficient box-bound for one partial derivative of one selector payoff
polynomial.  This is a finite constant determined by the fixed selector
polynomial and the chosen coordinate box. -/
def selectorMU_pvalPderivBoxBound
    (eta : ℚ) (heta : 0 < eta)
    (v : UniversalLocalView) (i : Fin d_U) (r : Fin d_U → ℝ) : ℝ :=
  EncBoxCore.mvPolynomialBoxBound
    (MvPolynomial.pderiv i
      (viewSelectorPolyN universalViewSpecN
        (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) r

/-- Sum of the coefficient box-bounds of the selector payoff gradient. -/
def selectorMU_pvalGradBoxBound
    (eta : ℚ) (heta : 0 < eta)
    (v : UniversalLocalView) (r : Fin d_U → ℝ) : ℝ :=
  ∑ i : Fin d_U, selectorMU_pvalPderivBoxBound eta heta v i r

theorem selectorMU_pvalPderivBoxBound_nonneg
    (eta : ℚ) (heta : 0 < eta)
    (v : UniversalLocalView) (i : Fin d_U) {r : Fin d_U → ℝ}
    (hr0 : ∀ k : Fin d_U, 0 ≤ r k) :
    0 ≤ selectorMU_pvalPderivBoxBound eta heta v i r := by
  simpa [selectorMU_pvalPderivBoxBound] using
    EncBoxCore.mvPolynomialBoxBound_nonneg
      (MvPolynomial.pderiv i
        (viewSelectorPolyN universalViewSpecN
          (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) hr0

theorem selectorMU_pvalGradBoxBound_nonneg
    (eta : ℚ) (heta : 0 < eta)
    (v : UniversalLocalView) {r : Fin d_U → ℝ}
    (hr0 : ∀ k : Fin d_U, 0 ≤ r k) :
    0 ≤ selectorMU_pvalGradBoxBound eta heta v r := by
  dsimp [selectorMU_pvalGradBoxBound]
  exact Finset.sum_nonneg fun i _ =>
    selectorMU_pvalPderivBoxBound_nonneg eta heta v i hr0

theorem selectorMU_pval_pderiv_eval_abs_le_boxBound
    (eta : ℚ) (heta : 0 < eta)
    (v : UniversalLocalView) (i : Fin d_U)
    (x r : Fin d_U → ℝ)
    (hr0 : ∀ k : Fin d_U, 0 ≤ r k)
    (hx : ∀ k : Fin d_U, |x k| ≤ r k) :
    |MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
      (MvPolynomial.pderiv i
        (viewSelectorPolyN universalViewSpecN
          (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v))| ≤
      selectorMU_pvalPderivBoxBound eta heta v i r := by
  simpa [selectorMU_pvalPderivBoxBound] using
    EncBoxCore.mvPolynomial_eval₂_abs_le_boxBound
      (MvPolynomial.pderiv i
        (viewSelectorPolyN universalViewSpecN
          (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v))
      hr0 hx

/-- Pure factor bound for the concrete `u`-RHS.  The dynamic/tube facts only
have to provide bounds for the four displayed factors. -/
theorem selectorMU_uDerivRHS_abs_le_of_factor_bounds
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (t : ℝ) (i : Fin d_U)
    {Aabs alphB gateB zuB Ubound : ℝ}
    (hA : |bgpParams38.A| ≤ Aabs)
    (halpha : |(sol w).α t| ≤ alphB)
    (hgate : |bGateU bgpParams38.L ((sol w).μ t) t| ≤ gateB)
    (hzu : |(sol w).z t i - (sol w).u t i| ≤ zuB)
    (hAabs_nonneg : 0 ≤ Aabs)
    (halphB_nonneg : 0 ≤ alphB)
    (hgateB_nonneg : 0 ≤ gateB)
    (hU : Aabs * alphB * gateB * zuB ≤ Ubound) :
    |selectorMU_uDerivRHS sol w t i| ≤ Ubound := by
  let gate : ℝ := bGateU bgpParams38.L ((sol w).μ t) t
  let zu : ℝ := (sol w).z t i - (sol w).u t i
  have hAα :
      |bgpParams38.A * (sol w).α t| ≤ Aabs * alphB := by
    rw [abs_mul]
    exact mul_le_mul hA halpha (abs_nonneg _) hAabs_nonneg
  have hAα_nonneg : 0 ≤ Aabs * alphB :=
    mul_nonneg hAabs_nonneg halphB_nonneg
  have hAαg :
      |bgpParams38.A * (sol w).α t * gate| ≤
        Aabs * alphB * gateB := by
    rw [abs_mul]
    exact mul_le_mul hAα (by simpa [gate] using hgate) (abs_nonneg _) hAα_nonneg
  have hAαg_nonneg : 0 ≤ Aabs * alphB * gateB :=
    mul_nonneg hAα_nonneg hgateB_nonneg
  have hcore :
      |bgpParams38.A * (sol w).α t * gate * zu| ≤
        Aabs * alphB * gateB * zuB := by
    rw [abs_mul]
    exact mul_le_mul hAαg (by simpa [zu] using hzu) (abs_nonneg _) hAαg_nonneg
  exact le_trans (by simpa [selectorMU_uDerivRHS, gate, zu] using hcore) hU

/-- Pointwise write-prefix decay for the concrete `u`-RHS.  This exposes the
field estimate already used inside the prefix drift theorem, in the form needed
by payoff-speed and active-QSS variation bounds. -/
theorem selectorMU_uDerivRHS_abs_le_write_prefix_decay
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (i : Fin d_U) {Bzu : ℝ}
    (hBzu0 : 0 ≤ Bzu)
    (hzu : ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |(sol w).z t i - (sol w).u t i| ≤ Bzu) :
    ∀ t ∈ Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |selectorMU_uDerivRHS sol w t i| ≤
        Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) := by
  intro t ht
  have ha0 : 0 ≤ selectorMUWriteStartTime j :=
    selectorMUWriteStartTime_nonneg j
  have ht0 : 0 ≤ t := le_trans ha0 ht.1
  have hαt : (sol w).α t = Real.exp (bgpParams38.cα * t) := by
    rw [(sol w).alpha_eq_exp selectorSchedule_domain_of_nonneg_structural ht0]
  have hμt : (sol w).μ t = bgpParams38.cμ * t := by
    rw [(sol w).mu_eq_linear selectorSchedule_domain_of_nonneg_structural ht0,
      (sol w).μ_at_zero, zero_add]
  have hsin : (1 : ℝ) / 2 ≤ Real.sin t :=
    sin_window_ge j
      (by simpa [selectorMUWriteStartTime] using ht.1)
      (by
        have ht_read : t ≤ selectorMUWriteReadTime j :=
          le_trans ht.2 (selectorMUWriteHold_le_read j)
        simpa [selectorMUWriteReadTime] using ht_read)
  have hcoef0 :
      0 ≤ bgpParams38.A * (sol w).α t *
        bGateU bgpParams38.L ((sol w).μ t) t := by
    rw [hαt]
    exact mul_nonneg
      (mul_nonneg (by norm_num [bgpParams38]) (Real.exp_pos _).le)
      (bGateU_pos bgpParams38.L ((sol w).μ t) t).le
  have hcoef_le :
      bgpParams38.A * (sol w).α t *
          bGateU bgpParams38.L ((sol w).μ t) t
        ≤ Real.exp (-(selectorUSettledRate * t)) := by
    have h :=
      gateU_integrand_le_settled_exp_repl
        (sol := (sol w)) (A := bgpParams38.A) (cμ := bgpParams38.cμ)
        (cα := bgpParams38.cα)
        ht0 (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
        (by norm_num [bgpParams38])
        hαt hμt hsin
    rw [show selectorUSettledRate
          = bgpParams38.cμ * (3 / 4 : ℝ) ^ bgpParams38.L - bgpParams38.cα from by
        norm_num [selectorUSettledRate, bgpParams38]]
    simpa [bgpParams38] using h
  have hdec :
      Real.exp (-(selectorUSettledRate * t))
        ≤ Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) := by
    apply Real.exp_le_exp.mpr
    have hmul :
        selectorUSettledRate * selectorMUWriteStartTime j ≤
          selectorUSettledRate * t :=
      mul_le_mul_of_nonneg_left ht.1 selectorUSettledRate_pos.le
    linarith
  calc
    |selectorMU_uDerivRHS sol w t i|
        = (bgpParams38.A * (sol w).α t *
            bGateU bgpParams38.L ((sol w).μ t) t) *
            |(sol w).z t i - (sol w).u t i| := by
          rw [selectorMU_uDerivRHS, abs_mul, abs_of_nonneg hcoef0]
    _ ≤ Real.exp (-(selectorUSettledRate * t)) * Bzu :=
          mul_le_mul hcoef_le (hzu t ht) (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) * Bzu :=
          mul_le_mul_of_nonneg_right hdec hBzu0
    _ = Bzu * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) := by
          ring

/-- Finite-sum source estimate for selector payoff speed.  Callers can plug in
any concrete coordinate-wise polynomial-gradient and `u`-RHS bounds. -/
theorem selectorMU_universalPvalDerivRHS_abs_le_of_coord_bounds
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (G U : Fin d_U → ℝ)
    (hG_nonneg : ∀ i : Fin d_U, 0 ≤ G i)
    (hgrad :
      ∀ i : Fin d_U,
        |MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
          (MvPolynomial.pderiv i
            (viewSelectorPolyN universalViewSpecN
              (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v))| ≤
          G i)
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHS sol w t i| ≤ U i) :
    |selectorMU_universalPvalDerivRHS eta heta sol w v t| ≤
      ∑ i : Fin d_U, G i * U i := by
  classical
  unfold selectorMU_universalPvalDerivRHS
  calc
    |∑ i : Fin d_U,
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
          (MvPolynomial.pderiv i
            (viewSelectorPolyN universalViewSpecN
              (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) *
          selectorMU_uDerivRHS sol w t i|
        ≤ ∑ i : Fin d_U,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
            (MvPolynomial.pderiv i
              (viewSelectorPolyN universalViewSpecN
                (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) *
            selectorMU_uDerivRHS sol w t i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d_U, G i * U i := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        rw [abs_mul]
        exact mul_le_mul (hgrad i) (huRHS i) (abs_nonneg _) (hG_nonneg i)

/-- Uniform-coordinate version of
`selectorMU_universalPvalDerivRHS_abs_le_of_coord_bounds`. -/
theorem selectorMU_universalPvalDerivRHS_abs_le_card_mul_of_uniform_coord_bounds
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    {G U : ℝ}
    (hG_nonneg : 0 ≤ G)
    (hgrad :
      ∀ i : Fin d_U,
        |MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u t)
          (MvPolynomial.pderiv i
            (viewSelectorPolyN universalViewSpecN
              (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v))| ≤
          G)
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHS sol w t i| ≤ U) :
    |selectorMU_universalPvalDerivRHS eta heta sol w v t| ≤
      (d_U : ℝ) * G * U := by
  have h :=
    selectorMU_universalPvalDerivRHS_abs_le_of_coord_bounds
      eta heta (sol := sol) w v t
      (fun _ : Fin d_U => G) (fun _ : Fin d_U => U)
      (fun _ => hG_nonneg) hgrad huRHS
  simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using h

/-- Selector payoff speed bounded by the fixed gradient box-bound times a
uniform bound on every coordinate of the `u` RHS. -/
theorem selectorMU_universalPvalDerivRHS_abs_le_gradBoxBound_mul_uniform_uRHS
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (r : Fin d_U → ℝ) {URhs : ℝ}
    (hr0 : ∀ k : Fin d_U, 0 ≤ r k)
    (hu_coord : ∀ k : Fin d_U, |(sol w).u t k| ≤ r k)
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHS sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHS eta heta sol w v t| ≤
      selectorMU_pvalGradBoxBound eta heta v r * URhs := by
  have h :=
    selectorMU_universalPvalDerivRHS_abs_le_of_coord_bounds
      eta heta (sol := sol) w v t
      (fun i : Fin d_U => selectorMU_pvalPderivBoxBound eta heta v i r)
      (fun _ : Fin d_U => URhs)
      (fun i => selectorMU_pvalPderivBoxBound_nonneg eta heta v i hr0)
      (fun i =>
        selectorMU_pval_pderiv_eval_abs_le_boxBound
          eta heta v i ((sol w).u t) r hr0 hu_coord)
      huRHS
  calc
    |selectorMU_universalPvalDerivRHS eta heta sol w v t|
        ≤ ∑ i : Fin d_U,
          selectorMU_pvalPderivBoxBound eta heta v i r * URhs := h
    _ = selectorMU_pvalGradBoxBound eta heta v r * URhs := by
        simp [selectorMU_pvalGradBoxBound, Finset.sum_mul]

/-- Triangle bound for the derivative RHS of a payoff gap. -/
theorem selectorMU_universalPvalGapDerivRHS_abs_le_of_view_bounds
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (t : ℝ)
    (B : UniversalLocalView → ℝ)
    (hB : ∀ x : UniversalLocalView,
      |selectorMU_universalPvalDerivRHS eta heta sol w x t| ≤ B x) :
    |selectorMU_universalPvalDerivRHS eta heta sol w c t -
      selectorMU_universalPvalDerivRHS eta heta sol w v t| ≤ B c + B v := by
  calc
    |selectorMU_universalPvalDerivRHS eta heta sol w c t -
      selectorMU_universalPvalDerivRHS eta heta sol w v t|
        ≤ |selectorMU_universalPvalDerivRHS eta heta sol w c t| +
          |selectorMU_universalPvalDerivRHS eta heta sol w v t| :=
            abs_sub _ _
    _ ≤ B c + B v := add_le_add (hB c) (hB v)

/-- A configuration tube gives a coordinate-wise absolute-value box for the
current `u` vector. -/
theorem selectorMU_abs_u_le_tube_radius_add_enc_abs
    {ρ : ℝ} {cfg : UConf} {x : Fin d_U → ℝ}
    (hutube : UTube ρ cfg x) :
    ∀ i : Fin d_U, |x i| ≤ ρ + |(confEncU cfg i : ℝ)| := by
  intro i
  calc
    |x i|
        = |(x i - (confEncU cfg i : ℝ)) + (confEncU cfg i : ℝ)| := by
            ring_nf
    _ ≤ |x i - (confEncU cfg i : ℝ)| + |(confEncU cfg i : ℝ)| :=
          abs_add_le _ _
    _ ≤ ρ + |(confEncU cfg i : ℝ)| :=
          add_le_add (hutube i) (le_rfl)

/-- Combine a full-coordinate `z` tube around an encoding with the matching
`u`-tube to obtain an explicit `|z-u|` envelope. -/
theorem selectorMU_zu_abs_le_of_z_close_and_u_utube
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) {a b Rz ρ : ℝ} (cfg : UConf)
    (hz : ∀ t, t ∈ Icc a b -> ∀ i : Fin d_U,
      |(sol w).z t i - (confEncU cfg i : ℝ)| ≤ Rz)
    (hu : ∀ t, t ∈ Icc a b -> UTube ρ cfg ((sol w).u t)) :
    ∀ t, t ∈ Icc a b -> ∀ i : Fin d_U,
      |(sol w).z t i - (sol w).u t i| ≤ Rz + ρ := by
  intro t ht i
  have hz_i := hz t ht i
  have hu_i := hu t ht i
  calc
    |(sol w).z t i - (sol w).u t i|
        = |((sol w).z t i - (confEncU cfg i : ℝ)) +
            ((confEncU cfg i : ℝ) - (sol w).u t i)| := by
            ring_nf
    _ ≤ |(sol w).z t i - (confEncU cfg i : ℝ)| +
          |(confEncU cfg i : ℝ) - (sol w).u t i| :=
          abs_add_le _ _
    _ ≤ Rz + ρ :=
          add_le_add hz_i (by simpa [abs_sub_comm] using hu_i)

/-- Prefix `u`-RHS decay with an explicit `z`-tube and matching `u`-tube,
avoiding any finite-horizon `|z-u|` choice witness. -/
theorem selectorMU_uDerivRHS_abs_le_write_prefix_decay_of_z_close_utube
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) {Rz ρ : ℝ} (cfg : UConf)
    (hRz0 : 0 ≤ Rz) (hρ0 : 0 ≤ ρ)
    (hz : ∀ t, t ∈ Icc (selectorMUWriteStartTime j)
        (selectorMUWriteHoldTime j) -> ∀ i : Fin d_U,
      |(sol w).z t i - (confEncU cfg i : ℝ)| ≤ Rz)
    (hu : ∀ t, t ∈ Icc (selectorMUWriteStartTime j)
        (selectorMUWriteHoldTime j) -> UTube ρ cfg ((sol w).u t)) :
    ∀ t, t ∈ Icc (selectorMUWriteStartTime j)
        (selectorMUWriteHoldTime j) -> ∀ i : Fin d_U,
      |selectorMU_uDerivRHS sol w t i| ≤
        (Rz + ρ) * Real.exp (-(selectorUSettledRate * selectorMUWriteStartTime j)) := by
  intro t ht i
  exact
    selectorMU_uDerivRHS_abs_le_write_prefix_decay
      (sol := sol) w j i (Bzu := Rz + ρ) (add_nonneg hRz0 hρ0)
      (fun τ hτ =>
        selectorMU_zu_abs_le_of_z_close_and_u_utube
          (sol := sol) w cfg hz hu τ hτ i)
      t ht

/-- Payoff-speed bound using the active/full `u`-tube as the coordinate box. -/
theorem selectorMU_universalPvalDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHS
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) (ρ : ℝ) {URhs : ℝ}
    (hρ0 : 0 ≤ ρ)
    (hutube : UTube ρ cfg ((sol w).u t))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHS sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHS eta heta sol w v t| ≤
      selectorMU_pvalGradBoxBound eta heta v
          (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) *
        URhs := by
  exact
    selectorMU_universalPvalDerivRHS_abs_le_gradBoxBound_mul_uniform_uRHS
      eta heta (sol := sol) w v t
      (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)
      (by intro k; exact add_nonneg hρ0 (abs_nonneg _))
      (selectorMU_abs_u_le_tube_radius_add_enc_abs hutube)
      huRHS

/-- Payoff-gap speed bound using a shared `u`-tube coordinate box and a uniform
bound on every `u` RHS coordinate. -/
theorem selectorMU_universalPvalGapDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHS
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (t : ℝ)
    (cfg : UConf) (ρ : ℝ) {URhs : ℝ}
    (hρ0 : 0 ≤ ρ)
    (hutube : UTube ρ cfg ((sol w).u t))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHS sol w t i| ≤ URhs) :
    |selectorMU_universalPvalDerivRHS eta heta sol w c t -
      selectorMU_universalPvalDerivRHS eta heta sol w v t| ≤
      (selectorMU_pvalGradBoxBound eta heta c
          (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) +
        selectorMU_pvalGradBoxBound eta heta v
          (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)) *
        URhs := by
  let r : Fin d_U → ℝ := fun k => ρ + |(confEncU cfg k : ℝ)|
  have hview :
      ∀ x : UniversalLocalView,
        |selectorMU_universalPvalDerivRHS eta heta sol w x t| ≤
          selectorMU_pvalGradBoxBound eta heta x r * URhs := by
    intro x
    simpa [r] using
      selectorMU_universalPvalDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHS
        eta heta (sol := sol) w x t cfg ρ hρ0 hutube huRHS
  have hgap :=
    selectorMU_universalPvalGapDerivRHS_abs_le_of_view_bounds
      eta heta (sol := sol) w c v t
      (fun x : UniversalLocalView =>
        selectorMU_pvalGradBoxBound eta heta x r * URhs)
      hview
  calc
    |selectorMU_universalPvalDerivRHS eta heta sol w c t -
      selectorMU_universalPvalDerivRHS eta heta sol w v t|
        ≤ selectorMU_pvalGradBoxBound eta heta c r * URhs +
          selectorMU_pvalGradBoxBound eta heta v r * URhs := hgap
    _ = (selectorMU_pvalGradBoxBound eta heta c r +
          selectorMU_pvalGradBoxBound eta heta v r) * URhs := by
          ring
    _ = (selectorMU_pvalGradBoxBound eta heta c
            (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) +
          selectorMU_pvalGradBoxBound eta heta v
            (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)) *
          URhs := by
          rfl

theorem selectorMU_universalPval_hasDerivAt_of_sol_u_hasDerivAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (v : UniversalLocalView) {t : ℝ}
    (ht : t ∈ selectorSchedule.domain) :
    HasDerivAt
      (fun τ => universalPval eta heta v ((sol w).u τ))
      (selectorMU_universalPvalDerivRHS eta heta sol w v t) t := by
  simpa [selectorMU_universalPvalDerivRHS, selectorMU_uDerivRHS] using
    universalPval_hasDerivAt_of_u_hasDerivAt eta heta v
      (fun i => (sol w).u_hasDeriv t ht i)

theorem selectorMU_universalPval_gap_hasDerivAt_of_sol_u_hasDerivAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) {t : ℝ}
    (ht : t ∈ selectorSchedule.domain) :
    HasDerivAt
      (fun τ =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ))
      (selectorMU_universalPvalDerivRHS eta heta sol w c t -
        selectorMU_universalPvalDerivRHS eta heta sol w v t) t := by
  exact
    (selectorMU_universalPval_hasDerivAt_of_sol_u_hasDerivAt
      (sol := sol) w c ht).sub
      (selectorMU_universalPval_hasDerivAt_of_sol_u_hasDerivAt
        (sol := sol) w v ht)

theorem selectorMU_uDerivRHS_continuous
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (i : Fin d_U) :
    Continuous fun τ : ℝ => selectorMU_uDerivRHS sol w τ i := by
  have hq : Continuous fun τ : ℝ => qPulse bgpParams38.L τ := by
    simp only [qPulse]
    exact ((continuous_const.add Real.continuous_sin).div_const 2).pow bgpParams38.L
  have hgateU : Continuous fun τ : ℝ =>
      bGateU bgpParams38.L ((sol w).μ τ) τ := by
    simp only [bGateU]
    exact Real.continuous_exp.comp ((((sol w).cont_μ).mul hq).neg)
  exact (((continuous_const.mul ((sol w).cont_α)).mul hgateU).mul
    (((sol w).cont_z i).sub ((sol w).cont_u i)))

theorem selectorMU_universalPvalDerivRHS_continuous
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (v : UniversalLocalView) :
    Continuous fun τ : ℝ => selectorMU_universalPvalDerivRHS eta heta sol w v τ := by
  classical
  unfold selectorMU_universalPvalDerivRHS
  refine continuous_finsetSum Finset.univ ?_
  intro i _hi
  have hpoly :
      Continuous fun τ : ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ((sol w).u τ)
          (MvPolynomial.pderiv i
            (viewSelectorPolyN universalViewSpecN
              (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)) :=
    mvPolynomial_eval₂_continuous_of_cont_u _ (fun k => (sol w).cont_u k)
  exact hpoly.mul (selectorMU_uDerivRHS_continuous sol w i)

/-- `MUReplicatorBoxInputs` for the realized selector-replicator solution. -/
def muReplicatorBoxInputs_realized
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ)) :
    MUReplicatorBoxInputs eta heta Mcy κ₀ g₀
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  refine
  { hcr_cont := by fun_prop
    hcg_cont := by fun_prop
    hP_cont := ?_
    hcr_nonneg := ?_
    hlam_sum0 := ?_
    hlam_init_nonneg := ?_
    hz0 := ?_ }
  · intro w v
    exact universalPval_continuous_of_cont_u eta heta v
      (fun i => (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R
        hκ0 hg0 hKq0 w).cont_u i)
  · intro t
    exact mul_nonneg
      (pow_nonneg (by nlinarith [Real.neg_one_le_cos t]) Mcy) hκ0
  · intro w
    have hinit := solMUReplRealized_initial_values eta heta Mcy κ₀ g₀ HP Kq R
      (fun w => selector_replicator_finiteHorizonBound_MU eta heta Mcy κ₀ g₀ HP Kq R
        selectorInitX0 w hκ0 hg0 hKq0) w
    calc
      (∑ v : UniversalLocalView,
          (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R
            hκ0 hg0 hKq0 w).lam v 0)
          = ∑ _v : UniversalLocalView,
              ((1 / (Fintype.card UniversalLocalView : ℚ)) : ℝ) := by
            apply Finset.sum_congr rfl
            intro v _hv
            exact hinit.2.2.1 v
      _ = 1 := by
        simp [Finset.sum_const]
  · intro w v
    have hinit := solMUReplRealized_initial_values eta heta Mcy κ₀ g₀ HP Kq R
      (fun w => selector_replicator_finiteHorizonBound_MU eta heta Mcy κ₀ g₀ HP Kq R
        selectorInitX0 w hκ0 hg0 hKq0) w
    rw [hinit.2.2.1 v]
    have hcard_pos : (0 : ℚ) < Fintype.card UniversalLocalView := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩)
    have hnonneg : (0 : ℚ) ≤ 1 / (Fintype.card UniversalLocalView : ℚ) := by
      positivity
    exact_mod_cast hnonneg
  · intro w
    have hinit := solMUReplRealized_initial_values eta heta Mcy κ₀ g₀ HP Kq R
      (fun w => selector_replicator_finiteHorizonBound_MU eta heta Mcy κ₀ g₀ HP Kq R
        selectorInitX0 w hκ0 hg0 hKq0) w
    rw [hinit.1 haltCoordU, selectorInitX0_cast_enc]
    exact enc_haltCoordU_mem_unit (selectorInitConfig w)

/-- Shape-correct analytic residuals for constructing halt-coordinate settled
facts.  This bundle deliberately omits the full spread/u-tube data needed only
by non-halt readout paths. -/
structure MUReplicatorSettledHaltResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)
  Bz : ℕ → ℕ → ℝ
  Bzmax : ℝ
  δnext : ℕ → ℕ → ℝ
  holdPrefix : ℕ → ℕ → ℝ
  hBz_nonneg : ∀ w j, 0 ≤ Bz w j
  hBz_bdd : ∀ w, ∀ᶠ j in atTop, Bz w j ≤ Bzmax
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  hholdPrefix_nonneg : ∀ w j, 0 ≤ holdPrefix w j
  p_hz_start : ∀ w j,
    |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz w j
  p_hoff : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  p_hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δnext w j
  p_hfiniteHold : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      holdPrefix w j
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

/-- Prefix u-tube residual supplied by the existing P4 coarse budget.

This is deliberately weaker than `MUReplicatorSettledHaltResiduals.hutube_win`:
the current coarse theorem reaches only `selectorMUWriteHoldTime`, while
`hutube_win` runs to `selectorMUWriteReadTime`. -/
structure SelectorMUWritePrefixUTubeResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  coarseUTube :
    ∀ w, SelectorMUCoarseUTubeBudget sol (fun j : ℕ => solMUReplStaticCfg w j) w

namespace SelectorMUWritePrefixUTubeResidual

/-- Projection from the existing coarse budget to the prefix write-window tube. -/
theorem hutube_prefix
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUWritePrefixUTubeResidual sol) :
    ∀ w j, ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t) := by
  intro w j t ht
  simpa using (res.coarseUTube w).coarse_utube_all j t ht

/-- Endpoint projection, useful for write-hold tube consumers. -/
theorem hutube_write_hold
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUWritePrefixUTubeResidual sol) :
    ∀ w j, UTube r_LE_U (solMUReplStaticCfg w j)
      ((sol w).u (selectorMUWriteHoldTime j)) := by
  intro w j
  simpa using (res.coarseUTube w).coarse_utube_write_hold j

/-- Coordinate endpoint projection, matching the legacy `hutube_write` shape. -/
theorem hutube_write_hold_coord
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUWritePrefixUTubeResidual sol) :
    ∀ w j i,
      |(sol w).u (selectorMUWriteHoldTime j) i -
        stackMachineEncodingU.enc (solMUReplStaticCfg w j) i| ≤ r_LE_U := by
  intro w j i
  exact res.hutube_write_hold w j i

end SelectorMUWritePrefixUTubeResidual

/-- Full write-window u-tube interface split into the banked prefix tube and
the remaining settled-tail tube.

The prefix half is supplied by `SelectorMUWritePrefixUTubeResidual`.  The tail
half remains a real residual: current drift estimates do not preserve the same
radius `r_LE_U` without slack. -/
structure SelectorMUWriteFullUTubeResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  prefixTube : SelectorMUWritePrefixUTubeResidual sol
  hutube_tail : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)

namespace SelectorMUWriteFullUTubeResidual

/-- Forget the split full-window u-tube residual to the exact `hutube_win`
shape required by `MUReplicatorSettledHaltResiduals`. -/
theorem hutube_win
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUWriteFullUTubeResidual sol) :
    ∀ w j, ∀ t ∈ Ico (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t) := by
  intro w j t ht
  by_cases hlt : t < selectorMUWriteHoldTime j
  · exact res.prefixTube.hutube_prefix w j t ⟨ht.1, hlt⟩
  · exact res.hutube_tail w j t ⟨le_of_not_gt hlt, le_of_lt ht.2⟩

end SelectorMUWriteFullUTubeResidual

/-- Halt residual bundle with the full-window u-tube obligation split into the
banked prefix coarse tube plus an honest settled-tail tube. -/
structure MUReplicatorSettledHaltResidualsSplitUTube
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  Bz : ℕ → ℕ → ℝ
  Bzmax : ℝ
  δnext : ℕ → ℕ → ℝ
  holdPrefix : ℕ → ℕ → ℝ
  hBz_nonneg : ∀ w j, 0 ≤ Bz w j
  hBz_bdd : ∀ w, ∀ᶠ j in atTop, Bz w j ≤ Bzmax
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  hholdPrefix_nonneg : ∀ w j, 0 ≤ holdPrefix w j
  p_hz_start : ∀ w j,
    |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤ Bz w j
  p_hoff : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  p_hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δnext w j
  p_hfiniteHold : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      holdPrefix w j
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

/-- Forget the split-u-tube residual to the existing residual bundle. -/
def MUReplicatorSettledHaltResidualsSplitUTube.toResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltResidualsSplitUTube sol) :
    MUReplicatorSettledHaltResiduals sol where
  hqL_full := res.hqL_full
  hutube_win := res.fullUTube.hutube_win
  Bz := res.Bz
  Bzmax := res.Bzmax
  δnext := res.δnext
  holdPrefix := res.holdPrefix
  hBz_nonneg := res.hBz_nonneg
  hBz_bdd := res.hBz_bdd
  hδnext := res.hδnext
  hδnext_nonneg := res.hδnext_nonneg
  hholdPrefix_nonneg := res.hholdPrefix_nonneg
  p_hz_start := res.p_hz_start
  p_hoff := res.p_hoff
  p_hnextWrite := res.p_hnextWrite
  p_hfiniteHold := res.p_hfiniteHold
  p_hloser := res.p_hloser

private theorem abs_sub_le_one_of_unit_interval_pair {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |x - y| ≤ (1 : ℝ) := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Forward halt-coordinate z-box from `MUReplicatorBoxInputs`. -/
theorem MUReplicatorBoxInputs.halt_z_mem_Icc
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w t, 0 ≤ t → (sol w).z t haltCoordU ∈ Icc (0 : ℝ) 1 := by
  intro w t ht
  have hzbox :=
    selector_replicator_flag_box_on_nonneg_repl (sol w)
      boxInputs.hcr_cont boxInputs.hcg_cont (boxInputs.hP_cont w)
      boxInputs.hcr_nonneg (boxInputs.hlam_sum0 w)
      (boxInputs.hlam_init_nonneg w) (boxInputs.hz0 w)
  exact ⟨hzbox.2 t ht, hzbox.1 t ht⟩

/-- Forward halt-coordinate mix-target box from `MUReplicatorBoxInputs`. -/
theorem MUReplicatorBoxInputs.halt_mixTarget_mem_Icc
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w t, 0 ≤ t →
      selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU ∈ Icc (0 : ℝ) 1 := by
  classical
  intro w t ht
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  have hsum_forward : ∀ s : ℝ, 0 ≤ s →
      (∑ v : UniversalLocalView, (sol w).lam v s) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
  have hlam_nonneg_forward :
      ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s → 0 ≤ (sol w).lam v s :=
    replicator_lam_nonneg
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) boxInputs.hcr_nonneg hode
      (boxInputs.hlam_init_nonneg w)
  exact selectorMixTarget_haltCoord_mem_Icc_of_lam_sum_eq_one
    (sol w).u (sol w).lam t
    (fun v => hlam_nonneg_forward v t ht)
    (hsum_forward t ht)

/-- Coarse unit bound for the pre-settled halt-coordinate z-start mismatch. -/
theorem MUReplicatorBoxInputs.hz_writeHold_static_next_le_one
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j,
      |(sol w).z (selectorMUWriteHoldTime j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
          (1 : ℝ) := by
  intro w j
  have ht0 : 0 ≤ selectorMUWriteHoldTime j := by
    unfold selectorMUWriteHoldTime
    positivity
  exact abs_sub_le_one_of_unit_interval_pair
    (boxInputs.halt_z_mem_Icc w (selectorMUWriteHoldTime j) ht0)
    (enc_haltCoordU_mem_unit (solMUReplStaticCfg w (j + 1)))

/-- Coarse unit bound for the finite-prefix self-hold patch. -/
theorem MUReplicatorBoxInputs.hfiniteHold_one
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤ (1 : ℝ) := by
  intro w j t ht
  have ha0 : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have ht0 : 0 ≤ t := le_trans ha0 ht.1
  exact abs_sub_le_one_of_unit_interval_pair
    (boxInputs.halt_z_mem_Icc w t ht0)
    (boxInputs.halt_z_mem_Icc w (selectorMUInterReadStart j) ha0)

/-- Thinner settled halt residual bundle with the coarse box-bounded z-start and
finite-prefix hold fields discharged by `MUReplicatorBoxInputs`.

The remaining fields are the genuine settled concentration, tube, and
full-window tracking residuals. -/
structure MUReplicatorSettledHaltBoxReducedResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)
  δnext : ℕ → ℕ → ℝ
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  p_hoff : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  p_hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δnext w j
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

namespace MUReplicatorSettledHaltBoxReducedResiduals

/-- Fill the original residual bundle using unit box bounds for `Bz` and the
finite-prefix hold patch. -/
def toSettledHaltResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltBoxReducedResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltResiduals sol where
  hqL_full := res.hqL_full
  hutube_win := res.hutube_win
  Bz := fun _ _ => (1 : ℝ)
  Bzmax := (1 : ℝ)
  δnext := res.δnext
  holdPrefix := fun _ _ => (1 : ℝ)
  hBz_nonneg := by
    intro w j
    norm_num
  hBz_bdd := by
    intro w
    filter_upwards [] with j
    exact le_rfl
  hδnext := res.hδnext
  hδnext_nonneg := res.hδnext_nonneg
  hholdPrefix_nonneg := by
    intro w j
    norm_num
  p_hz_start := by
    intro w j
    exact boxInputs.hz_writeHold_static_next_le_one w j
  p_hoff := res.p_hoff
  p_hnextWrite := res.p_hnextWrite
  p_hfiniteHold := by
    intro w j t ht
    exact boxInputs.hfiniteHold_one w j t ht
  p_hloser := res.p_hloser

end MUReplicatorSettledHaltBoxReducedResiduals

/-- Combined thinner settled halt residual bundle: coarse box-bounded z-start
and finite-prefix hold fields are discharged by `MUReplicatorBoxInputs`, while
the full write-window u-tube is split into the banked prefix tube and the
remaining settled-tail tube. -/
structure MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  δnext : ℕ → ℕ → ℝ
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  p_hoff : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  p_hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δnext w j
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

namespace MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals

/-- Forget the combined thin residual to the box-reduced residual shape. -/
def toBoxReducedResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals sol) :
    MUReplicatorSettledHaltBoxReducedResiduals sol where
  hqL_full := res.hqL_full
  hutube_win := res.fullUTube.hutube_win
  δnext := res.δnext
  hδnext := res.hδnext
  hδnext_nonneg := res.hδnext_nonneg
  p_hoff := res.p_hoff
  p_hnextWrite := res.p_hnextWrite
  p_hloser := res.p_hloser

/-- Fill the original residual bundle from the combined thin residual and box
inputs. -/
def toSettledHaltResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltResiduals sol :=
  res.toBoxReducedResiduals.toSettledHaltResiduals boxInputs

end MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals

/-- Start of the clean z-off middle piece in the inter-read interval. -/
def selectorMUZOffStart (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + Real.pi

/-- End of the clean z-off middle piece in the inter-read interval. -/
def selectorMUZOffEnd (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * ((j : ℝ) + 1)

theorem selectorMUInterReadStart_le_zOffStart (j : ℕ) :
    selectorMUInterReadStart j ≤ selectorMUZOffStart j := by
  unfold selectorMUInterReadStart selectorMUWriteReadTime selectorMUZOffStart
  linarith [Real.pi_pos]

theorem selectorMUZOffStart_le_zOffEnd (j : ℕ) :
    selectorMUZOffStart j ≤ selectorMUZOffEnd j := by
  unfold selectorMUZOffStart selectorMUZOffEnd
  linarith [Real.pi_pos]

theorem selectorMUZOffEnd_le_nextWriteStart (j : ℕ) :
    selectorMUZOffEnd j ≤ selectorMUNextWriteStart j := by
  unfold selectorMUZOffEnd selectorMUNextWriteStart selectorMUWriteHoldTime
  push_cast
  linarith [Real.pi_pos]

/-- Sine is nonpositive on the clean z-off middle interval. -/
theorem selectorMU_sin_nonpos_zOffMiddle (j : ℕ) {t : ℝ}
    (hlo : selectorMUZOffStart j ≤ t) (hhi : t ≤ selectorMUZOffEnd j) :
    Real.sin t ≤ 0 := by
  apply sin_window_nonpos j
  · simpa [selectorMUZOffStart] using hlo
  · unfold selectorMUZOffEnd at hhi
    nlinarith

/-- On the left inter-read edge `[Read_j,ZOffStart_j]`, the sine phase has
already passed the half-height point, hence `sin t ≤ 1/2`. -/
theorem selectorMU_sin_le_half_leftEdge
    (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j)) :
    Real.sin t ≤ (1 : ℝ) / 2 := by
  obtain ⟨hl, hr⟩ := ht
  set s := t - 2 * Real.pi * (j : ℝ) with hs
  have hsin_t : Real.sin t = Real.sin s := by
    have ht_eq : t = s + (j : ℕ) * (2 * Real.pi) := by
      rw [hs]
      ring
    rw [ht_eq, Real.sin_add_nat_mul_two_pi]
  rw [hsin_t]
  have hs_lo : (5 : ℝ) * Real.pi / 6 ≤ s := by
    rw [hs]
    unfold selectorMUInterReadStart selectorMUWriteReadTime at hl
    linarith
  have hs_hi : s ≤ Real.pi := by
    rw [hs]
    unfold selectorMUZOffStart at hr
    linarith
  let y : ℝ := Real.pi - s
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    linarith
  have hy_le : y ≤ Real.pi / 6 := by
    dsimp [y]
    linarith
  have hsin_y : Real.sin s = Real.sin y := by
    have hs_eq : s = Real.pi - y := by
      dsimp [y]
      ring
    rw [hs_eq, Real.sin_pi_sub]
  rw [hsin_y]
  have hmem_y : y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos, hy_nonneg, hy_le]
  have hmem_end : Real.pi / 6 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hmono := Real.strictMonoOn_sin.monotoneOn hmem_y hmem_end hy_le
  rwa [Real.sin_pi_div_six] at hmono

/-- On the prewrite edge `[ZOffEnd_j,W_{j+1}]`, the sine phase is in the first
small positive arc, hence `sin t ≤ 1/2`. -/
theorem selectorMU_sin_le_half_prewrite
    (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc (selectorMUZOffEnd j)
        (selectorMUWriteStartTime (j + 1))) :
    Real.sin t ≤ (1 : ℝ) / 2 := by
  obtain ⟨hl, hr⟩ := ht
  set s := t - 2 * Real.pi * ((j : ℝ) + 1) with hs
  have hsin : Real.sin t = Real.sin s := by
    have ht_eq : t = s + (j + 1 : ℕ) * (2 * Real.pi) := by
      rw [hs]
      push_cast
      ring_nf
    rw [ht_eq, Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  have hs0 : 0 ≤ s := by
    rw [hs]
    unfold selectorMUZOffEnd at hl
    linarith
  have hs1 : s ≤ Real.pi / 6 := by
    rw [hs]
    unfold selectorMUWriteStartTime at hr
    push_cast at hr
    linarith
  have hmem_s : s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos, hs0, hs1]
  have hmem_end : Real.pi / 6 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hmono := Real.strictMonoOn_sin.monotoneOn hmem_s hmem_end hs1
  rwa [Real.sin_pi_div_six] at hmono

private theorem selectorMUZOffEnd_le_writeStartTime_succ_local (j : ℕ) :
    selectorMUZOffEnd j ≤ selectorMUWriteStartTime (j + 1) := by
  unfold selectorMUZOffEnd selectorMUWriteStartTime
  push_cast
  linarith [Real.pi_pos]

/-- Explicit scalar cap for the weighted inter-read z-source integral on
`[Read_j,W_{j+1}]`, where `W` is the true z-write start.  The three summands
correspond to the left half-phase edge, the clean z-off middle, and the
prewrite half-phase edge. -/
def selectorInterReadSourceCap (Bamp : ℝ) (j : ℕ) : ℝ :=
  Bamp *
    (Real.exp (-(selectorInterReadUActiveMassLower j)) *
        (Real.pi / 6) * Real.exp ((50 : ℝ) * selectorMUZOffStart j) +
      Real.pi * Real.exp (-((200 : ℝ) * selectorMUZOffStart j)) +
      (Real.pi / 6) *
        Real.exp ((50 : ℝ) * selectorMUWriteStartTime (j + 1)))

theorem selectorInterReadSourceCap_nonneg {Bamp : ℝ} (hBamp0 : 0 ≤ Bamp)
    (j : ℕ) :
    0 ≤ selectorInterReadSourceCap Bamp j := by
  dsimp [selectorInterReadSourceCap]
  positivity

/-- Schedule-only source cap for the inter-read propagation from the read
endpoint to the next true z-write start.  The only non-schedule input is the
local all-coordinate amplitude bound `hamp`. -/
theorem selector_replicator_interRead_source_integral_le_envelope
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ Mcy)
      (fun t => ((1 + Real.sin t) / 2) ^ Mcy)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (j : ℕ) {Bamp : ℝ} (hBamp0 : 0 ≤ Bamp)
    (hamp : ∀ τ ∈ Icc (selectorMUWriteReadTime j)
        (selectorMUWriteStartTime (j + 1)), ∀ i : Fin d_U,
      |selectorMixTarget branchU sol.u sol.lam τ i - sol.z τ i| ≤ Bamp) :
    ∀ i : Fin d_U,
      (∫ τ in (selectorMUWriteReadTime j)..(selectorMUWriteStartTime (j + 1)),
        Real.exp (-(∫ s in τ..(selectorMUWriteStartTime (j + 1)),
          bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s)) *
        |bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ *
          (selectorMixTarget branchU sol.u sol.lam τ i - sol.z τ i)|) ≤
      selectorInterReadSourceCap Bamp j := by
  intro i
  let R : ℝ := selectorMUWriteReadTime j
  let Z0 : ℝ := selectorMUZOffStart j
  let Z1 : ℝ := selectorMUZOffEnd j
  let W : ℝ := selectorMUWriteStartTime (j + 1)
  let kU : ℝ → ℝ := fun s =>
    bgpParams38.A * sol.α s * bGateU bgpParams38.L (sol.μ s) s
  let kZ : ℝ → ℝ := fun τ =>
    bgpParams38.A * sol.α τ * bGateZ bgpParams38.L (sol.μ τ) τ
  let diff : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU sol.u sol.lam τ i - sol.z τ i
  let kernel : ℝ → ℝ := fun τ => Real.exp (-(∫ s in τ..W, kU s))
  let source : ℝ → ℝ := fun τ => kernel τ * |kZ τ * diff τ|
  let leftTerm : ℝ :=
    Bamp * (Real.exp (-(selectorInterReadUActiveMassLower j)) *
      (Real.pi / 6) * Real.exp ((50 : ℝ) * Z0))
  let midTerm : ℝ :=
    Bamp * (Real.pi * Real.exp (-((200 : ℝ) * Z0)))
  let rightTerm : ℝ :=
    Bamp * ((Real.pi / 6) * Real.exp ((50 : ℝ) * W))
  have hRZ0 : R ≤ Z0 := by
    simpa [R, Z0] using selectorMUInterReadStart_le_zOffStart j
  have hZ0Z1 : Z0 ≤ Z1 := by
    simpa [Z0, Z1] using selectorMUZOffStart_le_zOffEnd j
  have hZ1W : Z1 ≤ W := by
    simpa [Z1, W] using selectorMUZOffEnd_le_writeStartTime_succ_local j
  have hRW : R ≤ W := le_trans hRZ0 (le_trans hZ0Z1 hZ1W)
  have hR0 : 0 ≤ R := by
    dsimp [R, selectorMUWriteReadTime]
    positivity
  have hkU_cont : Continuous kU := by
    have hq : Continuous fun s : ℝ => qPulse bgpParams38.L s := by
      simp only [qPulse]
      exact ((continuous_const.add Real.continuous_sin).div_const 2).pow
        bgpParams38.L
    have hgateU : Continuous fun s : ℝ =>
        bGateU bgpParams38.L (sol.μ s) s := by
      simp only [bGateU]
      exact Real.continuous_exp.comp (((sol.cont_μ).mul hq).neg)
    simpa [kU, mul_assoc] using
      ((continuous_const.mul sol.cont_α).mul hgateU)
  have hkU_nonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ kU s := by
    intro s hs0
    have hαs : sol.α s = Real.exp (bgpParams38.cα * s) := by
      rw [sol.alpha_eq_exp selectorSchedule_domain_of_nonneg_structural hs0]
    dsimp [kU]
    rw [hαs]
    exact mul_nonneg
      (mul_nonneg (by norm_num [bgpParams38]) (Real.exp_pos _).le)
      (bGateU_pos bgpParams38.L (sol.μ s) s).le
  have hKderiv : ∀ τ : ℝ,
      HasDerivAt (fun u : ℝ => ∫ s in u..W, kU s) (-(kU τ)) τ := by
    intro τ
    exact intervalIntegral.integral_hasDerivAt_left
      (hkU_cont.intervalIntegrable τ W)
      (hkU_cont.stronglyMeasurableAtFilter _ _)
      hkU_cont.continuousAt
  have hK_cont : Continuous fun τ : ℝ => ∫ s in τ..W, kU s := by
    apply continuous_iff_continuousAt.mpr
    intro τ
    exact (hKderiv τ).continuousAt
  have hkernel_cont : Continuous kernel := by
    dsimp [kernel]
    exact Real.continuous_exp.comp (continuous_neg.comp hK_cont)
  have hkZ_cont : Continuous kZ := by
    simpa [kZ] using selector_replicator_gateZ_integrand_continuous sol
  have hdiff_cont : Continuous diff := by
    dsimp [diff]
    exact (sol.cont_mixTarget i).sub (sol.cont_z i)
  have hsource_cont : Continuous source := by
    dsimp [source]
    exact hkernel_cont.mul ((hkZ_cont.mul hdiff_cont).abs)
  have hI : ∀ a b : ℝ, IntervalIntegrable source MeasureTheory.volume a b :=
    fun a b => hsource_cont.intervalIntegrable a b
  have hkZ_nonneg : ∀ τ ∈ Icc R W, 0 ≤ kZ τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hR0 hτ.1
    simpa [kZ] using
      selector_replicator_gateZ_integrand_nonneg sol
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38])
        hτ0
  have hkernel_le_one : ∀ τ ∈ Icc R W, kernel τ ≤ 1 := by
    intro τ hτ
    have htail_nonneg : 0 ≤ ∫ s in τ..W, kU s := by
      apply intervalIntegral.integral_nonneg hτ.2
      intro s hs
      exact hkU_nonneg s (le_trans (le_trans hR0 hτ.1) hs.1)
    dsimp [kernel]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr htail_nonneg)
  have hfull_left : ∀ τ ∈ Icc R Z0, τ ∈ Icc R W := by
    intro τ hτ
    exact ⟨hτ.1, le_trans hτ.2 (le_trans hZ0Z1 hZ1W)⟩
  have hfull_mid : ∀ τ ∈ Icc Z0 Z1, τ ∈ Icc R W := by
    intro τ hτ
    exact ⟨le_trans hRZ0 hτ.1, le_trans hτ.2 hZ1W⟩
  have hfull_right : ∀ τ ∈ Icc Z1 W, τ ∈ Icc R W := by
    intro τ hτ
    exact ⟨le_trans hRZ0 (le_trans hZ0Z1 hτ.1), hτ.2⟩
  have hleftPoint : ∀ τ ∈ Icc R Z0,
      source τ ≤
        Real.exp (-(selectorInterReadUActiveMassLower j)) *
          (Real.exp ((50 : ℝ) * Z0) * Bamp) := by
    intro τ hτ
    have hfull := hfull_left τ hτ
    have hτ0 : 0 ≤ τ := le_trans hR0 hτ.1
    have hτU : τ ∈ Icc (selectorMUWriteReadTime j) (selectorMUUActiveStart j) := by
      constructor
      · simpa [R] using hτ.1
      · have hZ0U :
            Z0 ≤ selectorMUUActiveStart j := by
          dsimp [Z0, selectorMUZOffStart, selectorMUUActiveStart]
          linarith [Real.pi_pos]
        exact le_trans hτ.2 hZ0U
    have hker :
        kernel τ ≤ Real.exp (-(selectorInterReadUActiveMassLower j)) := by
      simpa [kernel, W, kU] using
        selectorInterRead_kernel_le_uActiveMass sol j hτU
    have hleftEdge :
        τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j) := by
      simpa [R, Z0, selectorMUInterReadStart] using hτ
    have hrate₀ :
        kZ τ ≤ Real.exp ((50 : ℝ) * τ) := by
      simpa [kZ] using
        selector_replicator_gateZ_integrand_le_halfphase_exp sol hτ0
          (selectorMU_sin_le_half_leftEdge j hleftEdge)
    have hrate_mono :
        Real.exp ((50 : ℝ) * τ) ≤
          Real.exp ((50 : ℝ) * Z0) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hτ.2 (by norm_num : (0 : ℝ) ≤ 50))
    have hrate :
        kZ τ ≤ Real.exp ((50 : ℝ) * Z0) :=
      le_trans hrate₀ hrate_mono
    have hdiff : |diff τ| ≤ Bamp := by
      simpa [diff] using hamp τ (by simpa [R, W] using hfull) i
    have hfield :
        |kZ τ * diff τ| ≤ Real.exp ((50 : ℝ) * Z0) * Bamp := by
      calc
        |kZ τ * diff τ| = kZ τ * |diff τ| := by
          rw [abs_mul, abs_of_nonneg (hkZ_nonneg τ hfull)]
        _ ≤ Real.exp ((50 : ℝ) * Z0) * Bamp :=
          mul_le_mul hrate hdiff (abs_nonneg _) (Real.exp_pos _).le
    calc
      source τ = kernel τ * |kZ τ * diff τ| := rfl
      _ ≤ kernel τ * (Real.exp ((50 : ℝ) * Z0) * Bamp) :=
        mul_le_mul_of_nonneg_left hfield (Real.exp_pos _).le
      _ ≤ Real.exp (-(selectorInterReadUActiveMassLower j)) *
          (Real.exp ((50 : ℝ) * Z0) * Bamp) :=
        mul_le_mul_of_nonneg_right hker
          (mul_nonneg (Real.exp_pos _).le hBamp0)
  have hmidPoint : ∀ τ ∈ Icc Z0 Z1,
      source τ ≤ Real.exp (-((200 : ℝ) * Z0)) * Bamp := by
    intro τ hτ
    have hfull := hfull_mid τ hτ
    have hτ0 : 0 ≤ τ := le_trans hR0 hfull.1
    have hrate₀ :
        kZ τ ≤ Real.exp (-((200 : ℝ) * τ)) := by
      simpa [kZ] using
        selector_replicator_gateZ_integrand_le_offphase_exp sol hτ0
          (selectorMU_sin_nonpos_zOffMiddle j
            (by simpa [Z0] using hτ.1)
            (by simpa [Z1] using hτ.2))
    have hrate_mono :
        Real.exp (-((200 : ℝ) * τ)) ≤
          Real.exp (-((200 : ℝ) * Z0)) := by
      exact Real.exp_le_exp.mpr (by nlinarith [hτ.1])
    have hrate :
        kZ τ ≤ Real.exp (-((200 : ℝ) * Z0)) :=
      le_trans hrate₀ hrate_mono
    have hdiff : |diff τ| ≤ Bamp := by
      simpa [diff] using hamp τ (by simpa [R, W] using hfull) i
    have hfield :
        |kZ τ * diff τ| ≤ Real.exp (-((200 : ℝ) * Z0)) * Bamp := by
      calc
        |kZ τ * diff τ| = kZ τ * |diff τ| := by
          rw [abs_mul, abs_of_nonneg (hkZ_nonneg τ hfull)]
        _ ≤ Real.exp (-((200 : ℝ) * Z0)) * Bamp :=
          mul_le_mul hrate hdiff (abs_nonneg _) (Real.exp_pos _).le
    calc
      source τ = kernel τ * |kZ τ * diff τ| := rfl
      _ ≤ 1 * |kZ τ * diff τ| :=
        mul_le_mul_of_nonneg_right (hkernel_le_one τ hfull) (abs_nonneg _)
      _ ≤ 1 * (Real.exp (-((200 : ℝ) * Z0)) * Bamp) :=
        mul_le_mul_of_nonneg_left hfield (by norm_num)
      _ = Real.exp (-((200 : ℝ) * Z0)) * Bamp := by ring
  have hrightPoint : ∀ τ ∈ Icc Z1 W,
      source τ ≤ Real.exp ((50 : ℝ) * W) * Bamp := by
    intro τ hτ
    have hfull := hfull_right τ hτ
    have hτ0 : 0 ≤ τ := le_trans hR0 hfull.1
    have hpre :
        τ ∈ Icc (selectorMUZOffEnd j) (selectorMUWriteStartTime (j + 1)) := by
      simpa [Z1, W] using hτ
    have hrate₀ :
        kZ τ ≤ Real.exp ((50 : ℝ) * τ) := by
      simpa [kZ] using
        selector_replicator_gateZ_integrand_le_halfphase_exp sol hτ0
          (selectorMU_sin_le_half_prewrite j hpre)
    have hrate_mono :
        Real.exp ((50 : ℝ) * τ) ≤
          Real.exp ((50 : ℝ) * W) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hτ.2 (by norm_num : (0 : ℝ) ≤ 50))
    have hrate :
        kZ τ ≤ Real.exp ((50 : ℝ) * W) :=
      le_trans hrate₀ hrate_mono
    have hdiff : |diff τ| ≤ Bamp := by
      simpa [diff] using hamp τ (by simpa [R, W] using hfull) i
    have hfield :
        |kZ τ * diff τ| ≤ Real.exp ((50 : ℝ) * W) * Bamp := by
      calc
        |kZ τ * diff τ| = kZ τ * |diff τ| := by
          rw [abs_mul, abs_of_nonneg (hkZ_nonneg τ hfull)]
        _ ≤ Real.exp ((50 : ℝ) * W) * Bamp :=
          mul_le_mul hrate hdiff (abs_nonneg _) (Real.exp_pos _).le
    calc
      source τ = kernel τ * |kZ τ * diff τ| := rfl
      _ ≤ 1 * |kZ τ * diff τ| :=
        mul_le_mul_of_nonneg_right (hkernel_le_one τ hfull) (abs_nonneg _)
      _ ≤ 1 * (Real.exp ((50 : ℝ) * W) * Bamp) :=
        mul_le_mul_of_nonneg_left hfield (by norm_num)
      _ = Real.exp ((50 : ℝ) * W) * Bamp := by ring
  have hleftInt :
      (∫ τ in R..Z0, source τ) ≤ leftTerm := by
    let C : ℝ := Real.exp (-(selectorInterReadUActiveMassLower j)) *
      (Real.exp ((50 : ℝ) * Z0) * Bamp)
    have hmono :
        (∫ τ in R..Z0, source τ) ≤ ∫ _τ in R..Z0, C :=
      intervalIntegral.integral_mono_on hRZ0 (hI R Z0)
        _root_.intervalIntegrable_const
        (by
          intro τ hτ
          simpa [C] using hleftPoint τ hτ)
    have hconst : (∫ _τ in R..Z0, C) = C * (Z0 - R) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hlen : Z0 - R = Real.pi / 6 := by
      dsimp [Z0, R, selectorMUZOffStart, selectorMUWriteReadTime]
      ring
    calc
      (∫ τ in R..Z0, source τ) ≤ ∫ _τ in R..Z0, C := hmono
      _ = C * (Z0 - R) := hconst
      _ = leftTerm := by
        dsimp [C, leftTerm]
        rw [hlen]
        ring
  have hmidInt :
      (∫ τ in Z0..Z1, source τ) ≤ midTerm := by
    let C : ℝ := Real.exp (-((200 : ℝ) * Z0)) * Bamp
    have hmono :
        (∫ τ in Z0..Z1, source τ) ≤ ∫ _τ in Z0..Z1, C :=
      intervalIntegral.integral_mono_on hZ0Z1 (hI Z0 Z1)
        _root_.intervalIntegrable_const
        (by
          intro τ hτ
          simpa [C] using hmidPoint τ hτ)
    have hconst : (∫ _τ in Z0..Z1, C) = C * (Z1 - Z0) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hlen : Z1 - Z0 = Real.pi := by
      dsimp [Z1, Z0, selectorMUZOffEnd, selectorMUZOffStart]
      ring
    calc
      (∫ τ in Z0..Z1, source τ) ≤ ∫ _τ in Z0..Z1, C := hmono
      _ = C * (Z1 - Z0) := hconst
      _ = midTerm := by
        dsimp [C, midTerm]
        rw [hlen]
        ring
  have hrightInt :
      (∫ τ in Z1..W, source τ) ≤ rightTerm := by
    let C : ℝ := Real.exp ((50 : ℝ) * W) * Bamp
    have hmono :
        (∫ τ in Z1..W, source τ) ≤ ∫ _τ in Z1..W, C :=
      intervalIntegral.integral_mono_on hZ1W (hI Z1 W)
        _root_.intervalIntegrable_const
        (by
          intro τ hτ
          simpa [C] using hrightPoint τ hτ)
    have hconst : (∫ _τ in Z1..W, C) = C * (W - Z1) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hlen : W - Z1 = Real.pi / 6 := by
      dsimp [W, Z1, selectorMUWriteStartTime, selectorMUZOffEnd]
      push_cast
      ring
    calc
      (∫ τ in Z1..W, source τ) ≤ ∫ _τ in Z1..W, C := hmono
      _ = C * (W - Z1) := hconst
      _ = rightTerm := by
        dsimp [C, rightTerm]
        rw [hlen]
        ring
  have hsplit_left_mid :
      (∫ τ in R..Z1, source τ) =
        (∫ τ in R..Z0, source τ) + ∫ τ in Z0..Z1, source τ := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hI R Z0) (hI Z0 Z1)).symm
  have hsplit_all :
      (∫ τ in R..W, source τ) =
        (∫ τ in R..Z1, source τ) + ∫ τ in Z1..W, source τ := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hI R Z1) (hI Z1 W)).symm
  have hsum :
      (∫ τ in R..W, source τ) ≤ leftTerm + midTerm + rightTerm := by
    calc
      (∫ τ in R..W, source τ)
          = (∫ τ in R..Z1, source τ) + ∫ τ in Z1..W, source τ := hsplit_all
      _ = ((∫ τ in R..Z0, source τ) + ∫ τ in Z0..Z1, source τ) +
            ∫ τ in Z1..W, source τ := by
          rw [hsplit_left_mid]
      _ ≤ (leftTerm + midTerm) + rightTerm :=
          add_le_add (add_le_add hleftInt hmidInt) hrightInt
      _ = leftTerm + midTerm + rightTerm := by ring
  change (∫ τ in R..W, source τ) ≤ selectorInterReadSourceCap Bamp j
  calc
    (∫ τ in R..W, source τ) ≤ leftTerm + midTerm + rightTerm := hsum
    _ = selectorInterReadSourceCap Bamp j := by
      dsimp [leftTerm, midTerm, rightTerm, selectorInterReadSourceCap, Z0, W]
      ring

/-- Absolute halt-coordinate z-field integrand used by the `hoff` residual. -/
def selectorMUHoffIntegrand
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w : ℕ) (τ : ℝ) : ℝ :=
  |bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ *
    (selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
      (sol w).z τ haltCoordU)|

/-- Continuity of the absolute halt-coordinate field integrand used by `hoff`. -/
theorem selectorMUHoffIntegrand_continuous
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀} (w : ℕ) :
    Continuous fun τ : ℝ => selectorMUHoffIntegrand sol w τ := by
  unfold selectorMUHoffIntegrand
  exact ((selector_replicator_gateZ_integrand_continuous (sol w)).mul
    (((sol w).cont_mixTarget haltCoordU).sub ((sol w).cont_z haltCoordU))).abs

/-- The z-gate coefficient whose integral controls the left/right `hoff` caps. -/
def selectorMUHoffGateCoeff
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w : ℕ) (τ : ℝ) : ℝ :=
  bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ

/-- Schedule-only upper bound for a Hoff z-gate coefficient integral. -/
theorem selectorMUHoffGateCoeff_integral_le_exp_upper
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) {a b : ℝ}
    (hab : a ≤ b)
    (ha0 : 0 ≤ a) :
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ) ≤
      (b - a) * Real.exp (bgpParams38.cα * b) := by
  let C : ℝ := Real.exp (bgpParams38.cα * b)
  have hcont : Continuous fun τ : ℝ => selectorMUHoffGateCoeff sol w τ := by
    simpa [selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hpoint : ∀ τ ∈ Icc a b, selectorMUHoffGateCoeff sol w τ ≤ C := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hα : (sol w).α τ = Real.exp (bgpParams38.cα * τ) :=
      (sol w).alpha_eq_exp selectorSchedule_domain_of_nonneg_structural hτ0
    have hμ_nonneg : 0 ≤ (sol w).μ τ := by
      rw [(sol w).mu_eq_linear selectorSchedule_domain_of_nonneg_structural hτ0,
        (sol w).μ_at_zero]
      norm_num [bgpParams38]
      exact hτ0
    have hgate : bGateZ bgpParams38.L ((sol w).μ τ) τ ≤ 1 :=
      bGateZ_le_one bgpParams38.L hμ_nonneg τ
    have hα_le : Real.exp (bgpParams38.cα * τ) ≤ C := by
      dsimp [C]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hτ.2 (by norm_num [bgpParams38]))
    have hα_nonneg : 0 ≤ Real.exp (bgpParams38.cα * τ) := (Real.exp_pos _).le
    calc
      selectorMUHoffGateCoeff sol w τ
          = Real.exp (bgpParams38.cα * τ) *
              bGateZ bgpParams38.L ((sol w).μ τ) τ := by
            simp [selectorMUHoffGateCoeff, hα, bgpParams38]
      _ ≤ Real.exp (bgpParams38.cα * τ) * 1 :=
            mul_le_mul_of_nonneg_left hgate hα_nonneg
      _ = Real.exp (bgpParams38.cα * τ) := by ring
      _ ≤ C := hα_le
  calc
    (∫ τ in a..b, selectorMUHoffGateCoeff sol w τ)
        ≤ ∫ _τ in a..b, C := by
          exact intervalIntegral.integral_mono_on hab
            (hcont.intervalIntegrable a b)
            (continuous_const.intervalIntegrable a b) hpoint
    _ = (b - a) * C := by
          simp [intervalIntegral.integral_const]
    _ = (b - a) * Real.exp (bgpParams38.cα * b) := rfl

/-- Early z-write specialization of `selectorMUHoffGateCoeff_integral_le_exp_upper`. -/
theorem selectorMUHoffGateCoeff_integral_early_le_exp_upper
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w j : ℕ) :
    (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
      selectorMUHoffGateCoeff sol w τ) ≤
      (selectorMUWriteHoldTime j - selectorMUEarlyWriteSubStart j) *
        Real.exp (bgpParams38.cα * selectorMUWriteHoldTime j) := by
  exact selectorMUHoffGateCoeff_integral_le_exp_upper sol w
    (selectorMUEarlySubStart_le_writeHold j)
    (le_trans (selectorMUWriteStartTime_nonneg j)
      (selectorMUWriteStart_le_earlySubStart j))

/-- Left `hoff` cap from a z-gate coefficient integral cap. -/
theorem selectorMUHoff_hcapLeft_of_gate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    {capLeft : ℕ → ℕ → ℝ}
    (hgateLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffGateCoeff sol w τ) ≤ capLeft w j) :
    ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrand sol w τ) ≤ capLeft w j := by
  intro w j t ht
  have ha0 : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have hmix_box : ∀ τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_mixTarget_mem_Icc w τ (le_trans ha0 hτ.1)
  have hz_box : ∀ τ ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (sol w).z τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_z_mem_Icc w τ (le_trans ha0 hτ.1)
  have hfield :=
    flag_fieldIntegral_bound_of_gate_integral_repl
      (sol w) haltCoordU
      (a := selectorMUInterReadStart j) (b := selectorMUZOffStart j)
      (δhold := capLeft w j)
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (by
        intro τ hτ
        exact selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38])
          (le_trans ha0 hτ.1))
      hmix_box hz_box
      (by
        intro τ hτ
        simpa [selectorMUHoffGateCoeff] using hgateLeft w j τ hτ)
  simpa [selectorMUHoffIntegrand, selectorMUHoffGateCoeff] using hfield t ht

/-- Right `hoff` cap from a z-gate coefficient integral cap. -/
theorem selectorMUHoff_hcapRight_of_gate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    {capRight : ℕ → ℕ → ℝ}
    (hgateRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j)
      (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffGateCoeff sol w τ) ≤ capRight w j) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffIntegrand sol w τ) ≤ capRight w j := by
  intro w j henc_const t ht
  have ha0 : 0 ≤ selectorMUZOffEnd j := by
    unfold selectorMUZOffEnd
    positivity
  have hmix_box : ∀ τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_mixTarget_mem_Icc w τ (le_trans ha0 hτ.1)
  have hz_box : ∀ τ ∈ Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (sol w).z τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_z_mem_Icc w τ (le_trans ha0 hτ.1)
  have hfield :=
    flag_fieldIntegral_bound_of_gate_integral_repl
      (sol w) haltCoordU
      (a := selectorMUZOffEnd j) (b := selectorMUNextWriteStart j)
      (δhold := capRight w j)
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (by
        intro τ hτ
        exact selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38])
          (le_trans ha0 hτ.1))
      hmix_box hz_box
      (by
        intro τ hτ
        simpa [selectorMUHoffGateCoeff] using hgateRight w j henc_const τ hτ)
  simpa [selectorMUHoffIntegrand, selectorMUHoffGateCoeff] using hfield t ht

/-- Concrete z-off envelope on the middle inter-read interval. -/
def selectorMUHoffMiddleEnvelope (τ : ℝ) : ℝ :=
  bgpParams38.A *
    Real.exp (-((bgpParams38.cμ * (1 / 2 : ℝ) ^ bgpParams38.L - bgpParams38.cα) * τ))

/-- Scalar residual for the middle z-off envelope integral. -/
structure SelectorMUHoffMiddleEnvelopeResidual where
  capMid : ℕ → ℕ → ℝ
  henvInt : ∀ w j, ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
    (∫ τ in (selectorMUZOffStart j)..t, selectorMUHoffMiddleEnvelope τ) ≤ capMid w j

/-- Integral-form producer for the inter-read halt-coordinate self drift.

This is the exact upstream hypothesis consumed by
`flag_drift_bound_on_interval_repl`.  It is narrower than carrying the
pointwise `p_hoff` drift directly, and it avoids claiming that the whole
inter-read interval is z-offphase. -/
structure SelectorMUHoffFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hfieldInt : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      |bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ *
        (selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU -
          (sol w).z τ haltCoordU)|) ≤
        selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffFieldIntegralResidual

/-- Convert the field-integral producer into the current `p_hoff` shape. -/
theorem p_hoff
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffFieldIntegralResidual sol) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
        Icc (selectorMUInterReadStart j)
        (selectorMUNextWriteStart j),
      |(sol w).z t haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
        selectorReplicatorHoldEnvelope j := by
  intro w j henc_const t ht
  have hleft_nonneg : 0 ≤ selectorMUInterReadStart j := by
    unfold selectorMUInterReadStart selectorMUWriteReadTime
    positivity
  have hdom : ∀ s ∈ Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j), s ∈ selectorSchedule.domain := by
    intro s hs
    exact selectorSchedule_domain_of_nonneg_structural s (le_trans hleft_nonneg hs.1)
  exact
    flag_drift_bound_on_interval_repl (sol w) haltCoordU
      (selectorMUInterReadStart_le_nextWriteStart j) hdom
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (res.hfieldInt w j henc_const) t ht

end SelectorMUHoffFieldIntegralResidual

/-- Phase-split form of the `hoff` field-integral residual.

The middle piece is the true z-offphase interval; the two cap pieces remain
explicit residuals.  The `hsplitInt` field is an aggregation bridge back to the
current full-integral residual, so this interface does not depend on proving
interval splitting in this file. -/
structure SelectorMUHoffSplitFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capMid : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capLeft w j
  hoffMid : ∀ w j, ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
    (∫ τ in (selectorMUZOffStart j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capMid w j
  hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capRight w j
  hsplitInt : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capLeft w j + capMid w j + capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitFieldIntegralResidual

/-- Forget the phase-split residual to the current full-integral residual. -/
def toFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitFieldIntegralResidual sol) :
    SelectorMUHoffFieldIntegralResidual sol where
  hfieldInt := by
    intro w j henc_const t ht
    exact le_trans
      (by simpa [selectorMUHoffIntegrand] using res.hsplitInt w j henc_const t ht)
      (res.hsum_le w j henc_const)

end SelectorMUHoffSplitFieldIntegralResidual

/-- Middle z-offphase field-integral estimate.

This discharges the `hoffMid` component from a scalar exponential-envelope
integral residual.  The cap pieces and final cap-sum budget remain separate. -/
theorem selectorMUHoff_middle_offphase_of_envelope
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (env : SelectorMUHoffMiddleEnvelopeResidual) :
    ∀ w j, ∀ t ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (∫ τ in (selectorMUZOffStart j)..t,
        selectorMUHoffIntegrand sol w τ) ≤ env.capMid w j := by
  intro w j t ht
  have ha0 : 0 ≤ selectorMUZOffStart j := by
    unfold selectorMUZOffStart
    positivity
  have hdom : ∀ s : ℝ, 0 ≤ s → s ∈ selectorSchedule.domain :=
    selectorSchedule_domain_of_nonneg_structural
  have hα : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (sol w).α τ = Real.exp (bgpParams38.cα * τ) := by
    intro τ hτ
    exact (sol w).alpha_eq_exp hdom (le_trans ha0 hτ.1)
  have hμ : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (sol w).μ τ = bgpParams38.cμ * τ := by
    intro τ hτ
    rw [(sol w).mu_eq_linear hdom (le_trans ha0 hτ.1), (sol w).μ_at_zero]
    ring
  have hsin : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      Real.sin τ ≤ 0 := by
    intro τ hτ
    exact selectorMU_sin_nonpos_zOffMiddle j hτ.1 hτ.2
  have hmix_box : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_mixTarget_mem_Icc w τ (le_trans ha0 hτ.1)
  have hz_box : ∀ τ ∈ Icc (selectorMUZOffStart j) (selectorMUZOffEnd j),
      (sol w).z τ haltCoordU ∈ Icc (0 : ℝ) 1 := by
    intro τ hτ
    exact boxInputs.halt_z_mem_Icc w τ (le_trans ha0 hτ.1)
  have hfield :=
    flag_fieldIntegral_bound_of_offphase_envelope_repl
      (sol w) haltCoordU
      (a := selectorMUZOffStart j) (b := selectorMUZOffEnd j)
      (A := bgpParams38.A) (cμ := bgpParams38.cμ) (cα := bgpParams38.cα)
      (δhold := env.capMid w j)
      (selectorMUZOffStart_le_zOffEnd j) ha0
      (by norm_num [bgpParams38]) (by norm_num [bgpParams38])
      (by rfl)
      (selector_replicator_gateZ_integrand_continuous (sol w))
      (by
        intro τ hτ
        exact selector_replicator_gateZ_integrand_nonneg (sol w)
          selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38])
          (le_trans ha0 hτ.1))
      hα hμ hsin hmix_box hz_box
      (by
        intro τ hτ
        simpa [selectorMUHoffMiddleEnvelope] using env.henvInt w j τ hτ)
  simpa [selectorMUHoffIntegrand] using hfield t ht

/-- The full inter-read field integral is bounded by the sum of the left cap,
middle offphase envelope, and right cap.

No extra monotonicity residual is needed: the only nonnegativity used below is
recovered by evaluating component residuals on zero-length intervals. -/
theorem selectorMUHoff_hsplitInt_of_caps
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    {capLeft capRight : ℕ → ℕ → ℝ}
    (env : SelectorMUHoffMiddleEnvelopeResidual)
    (hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrand sol w τ) ≤ capLeft w j)
    (hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffIntegrand sol w τ) ≤ capRight w j) :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrand sol w τ) ≤
        capLeft w j + env.capMid w j + capRight w j := by
  intro w j henc_const t ht
  let f : ℝ → ℝ := fun τ => selectorMUHoffIntegrand sol w τ
  have hf_cont : Continuous f := by
    simpa [f] using selectorMUHoffIntegrand_continuous (sol := sol) w
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hmid := selectorMUHoff_middle_offphase_of_envelope
    (sol := sol) boxInputs env
  have hmid_nonneg : 0 ≤ env.capMid w j := by
    have h := env.henvInt w j (selectorMUZOffStart j)
      ⟨le_rfl, selectorMUZOffStart_le_zOffEnd j⟩
    simpa [selectorMUHoffMiddleEnvelope] using h
  have hright_nonneg : 0 ≤ capRight w j := by
    have h := hcapRight w j henc_const (selectorMUZOffEnd j)
      ⟨le_rfl, selectorMUZOffEnd_le_nextWriteStart j⟩
    simpa [f] using h
  change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
    capLeft w j + env.capMid w j + capRight w j
  by_cases ht_left : t ≤ selectorMUZOffStart j
  · have hleft := hcapLeft w j t ⟨ht.1, ht_left⟩
    have hleft' : (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤ capLeft w j := by
      simpa [f] using hleft
    linarith
  · have hb_t : selectorMUZOffStart j ≤ t := le_of_not_ge ht_left
    by_cases ht_mid : t ≤ selectorMUZOffEnd j
    · have hleft := hcapLeft w j (selectorMUZOffStart j)
        ⟨selectorMUInterReadStart_le_zOffStart j, le_rfl⟩
      have hleft' :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) ≤
            capLeft w j := by
        simpa [f] using hleft
      have hmid_t := hmid w j t ⟨hb_t, ht_mid⟩
      have hmid_t' :
          (∫ τ in (selectorMUZOffStart j)..t, f τ) ≤ env.capMid w j := by
        simpa [f] using hmid_t
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffStart j))
        (hI (selectorMUZOffStart j) t)
      calc
        (∫ τ in (selectorMUInterReadStart j)..t, f τ)
            = (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
              (∫ τ in (selectorMUZOffStart j)..t, f τ) := by
                exact hadd.symm
        _ ≤ capLeft w j + env.capMid w j := add_le_add hleft' hmid_t'
        _ ≤ capLeft w j + env.capMid w j + capRight w j := by linarith
    · have hc_t : selectorMUZOffEnd j ≤ t := le_of_not_ge ht_mid
      have hleft := hcapLeft w j (selectorMUZOffStart j)
        ⟨selectorMUInterReadStart_le_zOffStart j, le_rfl⟩
      have hleft' :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) ≤
            capLeft w j := by
        simpa [f] using hleft
      have hmid_full := hmid w j (selectorMUZOffEnd j)
        ⟨selectorMUZOffStart_le_zOffEnd j, le_rfl⟩
      have hmid_full' :
          (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ) ≤
            env.capMid w j := by
        simpa [f] using hmid_full
      have hright := hcapRight w j henc_const t ⟨hc_t, ht.2⟩
      have hright' :
          (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤ capRight w j := by
        simpa [f] using hright
      have hadd_ab_bc := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffStart j))
        (hI (selectorMUZOffStart j) (selectorMUZOffEnd j))
      have hadd_ac_ct := intervalIntegral.integral_add_adjacent_intervals
        (hI (selectorMUInterReadStart j) (selectorMUZOffEnd j))
        (hI (selectorMUZOffEnd j) t)
      have hdecomp_ac :
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffEnd j), f τ) =
            (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
            (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ) := by
        exact hadd_ab_bc.symm
      calc
        (∫ τ in (selectorMUInterReadStart j)..t, f τ)
            = (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffEnd j), f τ) +
              (∫ τ in (selectorMUZOffEnd j)..t, f τ) := by
                exact hadd_ac_ct.symm
        _ = ((∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ) +
              (∫ τ in (selectorMUZOffStart j)..(selectorMUZOffEnd j), f τ)) +
              (∫ τ in (selectorMUZOffEnd j)..t, f τ) := by
                rw [hdecomp_ac]
        _ ≤ (capLeft w j + env.capMid w j) + capRight w j :=
              add_le_add (add_le_add hleft' hmid_full') hright'
        _ = capLeft w j + env.capMid w j + capRight w j := by ring

/-- Split `hoff` residual with the middle field discharged by the scalar
offphase-envelope residual.

The left and right caps, plus the full split aggregation bridge, remain
explicit residuals because those subwindows are not wholly z-offphase. -/
structure SelectorMUHoffSplitMiddleEnvelopeResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  env : SelectorMUHoffMiddleEnvelopeResidual
  hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capLeft w j
  hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capRight w j
  hsplitInt : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capLeft w j + env.capMid w j + capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + env.capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitMiddleEnvelopeResidual

/-- Fill the original split field-integral residual by deriving the middle
z-offphase estimate from the scalar envelope residual. -/
def toSplitFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffSplitFieldIntegralResidual sol where
  capLeft := res.capLeft
  capMid := res.env.capMid
  capRight := res.capRight
  hcapLeft := res.hcapLeft
  hoffMid := selectorMUHoff_middle_offphase_of_envelope boxInputs res.env
  hcapRight := res.hcapRight
  hsplitInt := res.hsplitInt
  hsum_le := res.hsum_le

/-- Directly forget to the full inter-read field-integral residual. -/
def toFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffFieldIntegralResidual sol :=
  (res.toSplitFieldIntegralResidual boxInputs).toFieldIntegralResidual

end SelectorMUHoffSplitMiddleEnvelopeResidual

/-- Split `hoff` residual with the middle offphase field discharged and the
full split aggregation derived, not carried.

This is narrower than `SelectorMUHoffSplitMiddleEnvelopeResidual`: it removes
the `hsplitInt` field. -/
structure SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  env : SelectorMUHoffMiddleEnvelopeResidual
  hcapLeft : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capLeft w j
  hcapRight : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffIntegrand sol w τ) ≤ capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + env.capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual

/-- Fill the current split-middle residual by deriving the full split integral. -/
def toSplitMiddleEnvelopeResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffSplitMiddleEnvelopeResidual sol where
  capLeft := res.capLeft
  capRight := res.capRight
  env := res.env
  hcapLeft := res.hcapLeft
  hcapRight := res.hcapRight
  hsplitInt :=
    selectorMUHoff_hsplitInt_of_caps boxInputs res.env res.hcapLeft res.hcapRight
  hsum_le := res.hsum_le

/-- Directly forget to the full inter-read field-integral residual. -/
def toFieldIntegralResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffFieldIntegralResidual sol :=
  (res.toSplitMiddleEnvelopeResidual boxInputs).toFieldIntegralResidual boxInputs

end SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual

/-- No-split `hoff` residual with left/right caps stated as z-gate coefficient
integral caps.

Only the left/right cap shape is changed here.  The middle offphase envelope
and the scalar cap-budget `hsum_le` remain explicit. -/
structure SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  capLeft : ℕ → ℕ → ℝ
  capRight : ℕ → ℕ → ℝ
  env : SelectorMUHoffMiddleEnvelopeResidual
  hcapLeftGate : ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j)
      (selectorMUZOffStart j),
    (∫ τ in (selectorMUInterReadStart j)..t,
      selectorMUHoffGateCoeff sol w τ) ≤ capLeft w j
  hcapRightGate : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j)
      (selectorMUNextWriteStart j),
    (∫ τ in (selectorMUZOffEnd j)..t,
      selectorMUHoffGateCoeff sol w τ) ≤ capRight w j
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    capLeft w j + env.capMid w j + capRight w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual

/-- Convert gate-coefficient cap inputs to the current no-split `hoff`
residual. -/
def toNoSplitResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual sol where
  capLeft := res.capLeft
  capRight := res.capRight
  env := res.env
  hcapLeft := selectorMUHoff_hcapLeft_of_gate boxInputs res.hcapLeftGate
  hcapRight := selectorMUHoff_hcapRight_of_gate boxInputs res.hcapRightGate
  hsum_le := res.hsum_le

end SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual

/-- Actual left `hoff` field cap over `[readStart, zOffStart]`. -/
def selectorMUHoffCapLeftField
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w j : ℕ) : ℝ :=
  ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
    selectorMUHoffIntegrand sol w τ

/-- Actual right `hoff` field cap over `[zOffEnd, nextWriteStart]`. -/
def selectorMUHoffCapRightField
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w j : ℕ) : ℝ :=
  ∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
    selectorMUHoffIntegrand sol w τ

/-- Left `hoff` actual cap from a supplied write-error integral. -/
theorem selectorMUHoffCapLeftField_le_of_error_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (M : ℝ)
    (herrorInt :
      (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        selectorMUHoffGateCoeff sol w τ *
          |(sol w).z τ haltCoordU - M|) ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
            selectorMUHoffGateCoeff sol w τ *
              |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)) :
    selectorMUHoffCapLeftField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        2 * (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUInterReadStart, selectorMUWriteReadTime]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hscalar := stack_write_field_cap_bound_of_error_integral
    y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont (by
      simpa [a, b, y, m, k] using herrorInt)
  have hcap_le :
      selectorMUHoffCapLeftField sol w j ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    unfold selectorMUHoffCapLeftField
    have hleft_int : IntervalIntegrable
        (fun τ => selectorMUHoffIntegrand sol w τ) MeasureTheory.volume a b := by
      exact (selectorMUHoffIntegrand_continuous (sol := sol) w).intervalIntegrable a b
    have hright_int : IntervalIntegrable (fun τ => k τ * |m τ - y τ|)
        MeasureTheory.volume a b := by
      exact (hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro τ hτ
    have hk0 : 0 ≤ k τ := hk_nonneg τ hτ
    calc
      selectorMUHoffIntegrand sol w τ
          = |k τ * (m τ - y τ)| := by
            simp [selectorMUHoffIntegrand, selectorMUHoffGateCoeff, k, m, y]
      _ = k τ * |m τ - y τ| := by
            rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ k τ * |m τ - y τ| := le_rfl
  exact le_trans hcap_le (by simpa [a, b, y, m, k] using hscalar)

/-- Left `hoff` actual cap from the z-write ODE. -/
theorem selectorMUHoffCapLeftField_le_initial_add_target
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (M : ℝ) :
    selectorMUHoffCapLeftField sol w j ≤
      |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
        2 * (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUInterReadStart, selectorMUWriteReadTime]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hy_ode : ∀ τ ∈ Set.Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUInterReadStart, selectorMUWriteReadTime]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have herrorInt :
      (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        selectorMUHoffGateCoeff sol w τ *
          |(sol w).z τ haltCoordU - M|) ≤
        |(sol w).z (selectorMUInterReadStart j) haltCoordU - M| +
          (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
            selectorMUHoffGateCoeff sol w τ *
              |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
    have h := stack_write_error_integral_le_initial_add_target
      y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont hy_ode
    simpa [a, b, y, m, k] using h
  exact selectorMUHoffCapLeftField_le_of_error_integral w j M herrorInt

/-- Right `hoff` actual cap from a supplied write-error integral. -/
theorem selectorMUHoffCapRightField_le_of_error_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (M : ℝ)
    (herrorInt :
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |(sol w).z τ haltCoordU - M|) ≤
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
            selectorMUHoffGateCoeff sol w τ *
              |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|)) :
    selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUNextWriteStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUZOffEnd_le_nextWriteStart j
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUZOffEnd]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hscalar := stack_write_field_cap_bound_of_error_integral
    y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont (by
      simpa [a, b, y, m, k] using herrorInt)
  have hcap_le :
      selectorMUHoffCapRightField sol w j ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    unfold selectorMUHoffCapRightField
    have hleft_int : IntervalIntegrable
        (fun τ => selectorMUHoffIntegrand sol w τ) MeasureTheory.volume a b := by
      exact (selectorMUHoffIntegrand_continuous (sol := sol) w).intervalIntegrable a b
    have hright_int : IntervalIntegrable (fun τ => k τ * |m τ - y τ|)
        MeasureTheory.volume a b := by
      exact (hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro τ hτ
    have hk0 : 0 ≤ k τ := hk_nonneg τ hτ
    calc
      selectorMUHoffIntegrand sol w τ
          = |k τ * (m τ - y τ)| := by
            simp [selectorMUHoffIntegrand, selectorMUHoffGateCoeff, k, m, y]
      _ = k τ * |m τ - y τ| := by
            rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ k τ * |m τ - y τ| := le_rfl
  exact le_trans hcap_le (by simpa [a, b, y, m, k] using hscalar)

/-- Right `hoff` actual cap from the z-write ODE. -/
theorem selectorMUHoffCapRightField_le_initial_add_target
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (M : ℝ) :
    selectorMUHoffCapRightField sol w j ≤
      |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
        2 * (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
          selectorMUHoffGateCoeff sol w τ *
            |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUNextWriteStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUZOffEnd_le_nextWriteStart j
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUZOffEnd]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hy_ode : ∀ τ ∈ Set.Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have ha0 : 0 ≤ a := by
      simp [a, selectorMUZOffEnd]
      positivity
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have herrorInt :
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        selectorMUHoffGateCoeff sol w τ *
          |(sol w).z τ haltCoordU - M|) ≤
        |(sol w).z (selectorMUZOffEnd j) haltCoordU - M| +
          (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
            selectorMUHoffGateCoeff sol w τ *
              |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - M|) := by
    have h := stack_write_error_integral_le_initial_add_target
      y m k M a b hab hk_cont hk_nonneg hy_cont hm_cont hy_ode
    simpa [a, b, y, m, k] using h
  exact selectorMUHoffCapRightField_le_of_error_integral w j M herrorInt

/-- Local continuity helper used by the edge total-variation bounds below. -/
private theorem selectorMU_mixTargetDerivRHS_continuous_for_edge
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (s : Fin d_U) :
    Continuous fun τ : ℝ =>
      SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ s := by
  classical
  have hP : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => universalPval eta heta v ((sol w).u τ) := by
    intro v
    exact universalPval_continuous_of_cont_u eta heta v (fun i => (sol w).cont_u i)
  have hphi : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView,
        (sol w).lam v τ * universalPval eta heta v ((sol w).u τ) := by
    exact continuous_finset_sum Finset.univ (fun v _ =>
      ((sol w).cont_lam v).mul (hP v))
  have hbranch : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => BranchData.evalBranch (branchU v) ((sol w).u τ) s := by
    intro v
    simp only [BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u s)).add continuous_const
  have hq : Continuous fun τ : ℝ => qPulse bgpParams38.L τ := by
    simp only [qPulse]
    exact ((continuous_const.add Real.continuous_sin).div_const 2).pow bgpParams38.L
  have hgateU : Continuous fun τ : ℝ =>
      bGateU bgpParams38.L ((sol w).μ τ) τ := by
    simp only [bGateU]
    exact Real.continuous_exp.comp ((((sol w).cont_μ).mul hq).neg)
  have hcr : Continuous fun τ : ℝ =>
      ((1 + Real.cos τ) / 2) ^ Mcy := by
    fun_prop
  have hcg : Continuous fun τ : ℝ =>
      ((1 + Real.sin τ) / 2) ^ Mcy := by
    fun_prop
  have hgain : Continuous fun τ : ℝ =>
      (g₀ : ℝ) * Real.exp (bgpParams38.cα * τ) := by
    fun_prop
  dsimp [SelectorReplicatorDynSol.mixTargetDerivRHS]
  refine continuous_finset_sum Finset.univ ?_
  intro v _hv
  exact (((hcr.mul continuous_const).mul
      (continuous_const.sub ((sol w).cont_lam v))).add
        (((hcg.mul hgain).mul ((sol w).cont_lam v)).mul
          ((hP v).sub hphi))).mul (hbranch v) |>.add
    ((((sol w).cont_lam v).mul continuous_const).mul
      ((((continuous_const.mul (sol w).cont_α).mul hgateU).mul
        (((sol w).cont_z s).sub ((sol w).cont_u s)))))

/-- Left `hoff` cap from exact target tracking: the write rate disappears and
only the initial target error plus total variation of the moving mix target
remain. -/
theorem selectorMUHoffCapLeftField_le_initial_tracking_add_mixTargetDerivRHS
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) :
    selectorMUHoffCapLeftField sol w j ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUInterReadStart j) haltCoordU -
        (sol w).z (selectorMUInterReadStart j) haltCoordU| +
      (∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j),
        |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) := by
  let a : ℝ := selectorMUInterReadStart j
  let b : ℝ := selectorMUZOffStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let mdot : ℝ → ℝ := fun τ =>
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUInterReadStart_le_zOffStart j
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have hmdot_cont : Continuous mdot := by
    simpa [mdot] using
      selectorMU_mixTargetDerivRHS_continuous_for_edge (sol := sol) w haltCoordU
  have ha0 : 0 ≤ a := by
    simp [a, selectorMUInterReadStart, selectorMUWriteReadTime]
    positivity
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hm_deriv : ∀ τ ∈ Set.Icc a b, HasDerivAt m (mdot τ) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hdom : τ ∈ selectorSchedule.domain :=
      selectorSchedule_domain_of_nonneg_structural τ hτ0
    simpa [m, mdot] using
      SelectorReplicatorDynSol.mixTarget_hasDerivAt_ode (sol w) hdom haltCoordU
  have hy_ode : ∀ τ ∈ Set.Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have hscalar := stack_write_tracking_total_variation_le
    y m k mdot hab hk_cont hk_nonneg hm_cont hmdot_cont hm_deriv hy_ode
  have hcap_le :
      selectorMUHoffCapLeftField sol w j ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    unfold selectorMUHoffCapLeftField
    have hleft_int : IntervalIntegrable
        (fun τ => selectorMUHoffIntegrand sol w τ) MeasureTheory.volume a b := by
      exact (selectorMUHoffIntegrand_continuous (sol := sol) w).intervalIntegrable a b
    have hright_int : IntervalIntegrable (fun τ => k τ * |m τ - y τ|)
        MeasureTheory.volume a b := by
      exact (hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro τ hτ
    have hk0 : 0 ≤ k τ := hk_nonneg τ hτ
    calc
      selectorMUHoffIntegrand sol w τ
          = |k τ * (m τ - y τ)| := by
            simp [selectorMUHoffIntegrand, selectorMUHoffGateCoeff, k, m, y]
      _ = k τ * |m τ - y τ| := by
            rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ k τ * |m τ - y τ| := le_rfl
  exact le_trans hcap_le (by simpa [a, b, y, m, k, mdot] using hscalar)

/-- Right `hoff` cap from exact target tracking: the write rate disappears and
only the initial target error plus total variation of the moving mix target
remain. -/
theorem selectorMUHoffCapRightField_le_initial_tracking_add_mixTargetDerivRHS
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) :
    selectorMUHoffCapRightField sol w j ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUZOffEnd j) haltCoordU -
        (sol w).z (selectorMUZOffEnd j) haltCoordU| +
      (∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j),
        |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) := by
  let a : ℝ := selectorMUZOffEnd j
  let b : ℝ := selectorMUNextWriteStart j
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  let mdot : ℝ → ℝ := fun τ =>
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUZOffEnd_le_nextWriteStart j
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have hmdot_cont : Continuous mdot := by
    simpa [mdot] using
      selectorMU_mixTargetDerivRHS_continuous_for_edge (sol := sol) w haltCoordU
  have ha0 : 0 ≤ a := by
    simp [a, selectorMUZOffEnd]
    positivity
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hm_deriv : ∀ τ ∈ Set.Icc a b, HasDerivAt m (mdot τ) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    have hdom : τ ∈ selectorSchedule.domain :=
      selectorSchedule_domain_of_nonneg_structural τ hτ0
    simpa [m, mdot] using
      SelectorReplicatorDynSol.mixTarget_hasDerivAt_ode (sol w) hdom haltCoordU
  have hy_ode : ∀ τ ∈ Set.Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ (selectorSchedule_domain_of_nonneg_structural τ hτ0) haltCoordU
  have hscalar := stack_write_tracking_total_variation_le
    y m k mdot hab hk_cont hk_nonneg hm_cont hmdot_cont hm_deriv hy_ode
  have hcap_le :
      selectorMUHoffCapRightField sol w j ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    unfold selectorMUHoffCapRightField
    have hleft_int : IntervalIntegrable
        (fun τ => selectorMUHoffIntegrand sol w τ) MeasureTheory.volume a b := by
      exact (selectorMUHoffIntegrand_continuous (sol := sol) w).intervalIntegrable a b
    have hright_int : IntervalIntegrable (fun τ => k τ * |m τ - y τ|)
        MeasureTheory.volume a b := by
      exact (hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro τ hτ
    have hk0 : 0 ≤ k τ := hk_nonneg τ hτ
    calc
      selectorMUHoffIntegrand sol w τ
          = |k τ * (m τ - y τ)| := by
            simp [selectorMUHoffIntegrand, selectorMUHoffGateCoeff, k, m, y]
      _ = k τ * |m τ - y τ| := by
            rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ k τ * |m τ - y τ| := le_rfl
  exact le_trans hcap_le (by simpa [a, b, y, m, k, mdot] using hscalar)

/-- Active right-write suffix field cap from target variation.

This is the exact-tracking replacement for bounding the active suffix by a
Hoff-weighted loser-mass integral.  The remaining scalar obligation is the
total variation of the moving mixture target on the suffix. -/
theorem selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_target_deriv
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) (m' : ℝ → ℝ)
    (hm'_cont : Continuous m')
    (hm_deriv : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)),
      HasDerivAt
        (fun σ => selectorMixTarget branchU (sol w).u (sol w).lam σ haltCoordU)
        (m' τ) τ) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffIntegrand sol w τ) ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
        (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)), |m' τ|) := by
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let b : ℝ := selectorMUWriteHoldTime (j + 1)
  let y : ℝ → ℝ := fun τ => (sol w).z τ haltCoordU
  let m : ℝ → ℝ := fun τ =>
    selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU
  let k : ℝ → ℝ := fun τ => selectorMUHoffGateCoeff sol w τ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUEarlySubStart_le_writeHold (j + 1)
  have hk_cont : Continuous k := by
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_continuous (sol w)
  have hm_cont : Continuous m := by
    simpa [m] using (sol w).cont_mixTarget haltCoordU
  have hy_cont : Continuous y := by
    simpa [y] using (sol w).cont_z haltCoordU
  have ha0 : 0 ≤ a := by
    exact le_trans (selectorMUWriteStartTime_nonneg (j + 1))
      (by simpa [a] using selectorMUWriteStart_le_earlySubStart (j + 1))
  have hk_nonneg : ∀ τ ∈ Set.Icc a b, 0 ≤ k τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans ha0 hτ.1
    simpa [k, selectorMUHoffGateCoeff] using
      selector_replicator_gateZ_integrand_nonneg (sol w)
        selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) hτ0
  have hy_ode : ∀ τ ∈ Set.Icc a b,
      HasDerivAt y (k τ * (m τ - y τ)) τ := by
    intro τ hτ
    have hstart : selectorMUWriteStartTime (j + 1) ≤ τ :=
      le_trans (selectorMUWriteStart_le_earlySubStart (j + 1))
        (by simpa [a] using hτ.1)
    have hdom : τ ∈ selectorSchedule.domain :=
      selectorMU_hdom_writeHold w (j + 1) τ ⟨hstart, by simpa [b] using hτ.2⟩
    simpa [y, m, k, selectorMUHoffGateCoeff] using
      (sol w).z_hasDeriv τ hdom haltCoordU
  have hm_deriv' : ∀ τ ∈ Set.Icc a b, HasDerivAt m (m' τ) τ := by
    intro τ hτ
    simpa [m, a, b] using hm_deriv τ (by simpa [a, b] using hτ)
  have hscalar := stack_write_field_cap_le_initial_tracking_add_target_deriv
    y m k m' a b hab hk_cont hk_nonneg hy_cont hm_cont hm'_cont hy_ode hm_deriv'
  have hcap_le :
      (∫ τ in a..b, selectorMUHoffIntegrand sol w τ) ≤
        ∫ τ in a..b, k τ * |m τ - y τ| := by
    have hleft_int : IntervalIntegrable
        (fun τ => selectorMUHoffIntegrand sol w τ) MeasureTheory.volume a b := by
      exact (selectorMUHoffIntegrand_continuous (sol := sol) w).intervalIntegrable a b
    have hright_int : IntervalIntegrable (fun τ => k τ * |m τ - y τ|)
        MeasureTheory.volume a b := by
      exact (hk_cont.mul ((hm_cont.sub hy_cont).abs)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft_int hright_int
    intro τ hτ
    have hk0 : 0 ≤ k τ := hk_nonneg τ hτ
    calc
      selectorMUHoffIntegrand sol w τ
          = |k τ * (m τ - y τ)| := by
            simp [selectorMUHoffIntegrand, selectorMUHoffGateCoeff, k, m, y]
      _ = k τ * |m τ - y τ| := by
            rw [abs_mul, abs_of_nonneg hk0]
      _ ≤ k τ * |m τ - y τ| := le_rfl
  exact le_trans hcap_le (by simpa [a, b, y, m, k] using hscalar)

/-- Active right-write suffix field cap with the concrete selector-mixture ODE
RHS as the target derivative. -/
theorem selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_mixTargetDerivRHS
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ)
    (hm'_cont : Continuous fun τ : ℝ =>
      SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffIntegrand sol w τ) ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
        (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) := by
  refine selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_target_deriv
    (sol := sol) w j
    (fun τ => SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU)
    hm'_cont ?_
  intro τ hτ
  have hstart : selectorMUWriteStartTime (j + 1) ≤ τ :=
    le_trans (selectorMUWriteStart_le_earlySubStart (j + 1)) hτ.1
  have hdom : τ ∈ selectorSchedule.domain :=
    selectorMU_hdom_writeHold w (j + 1) τ ⟨hstart, hτ.2⟩
  simpa using SelectorReplicatorDynSol.mixTarget_hasDerivAt_ode (sol w) hdom haltCoordU

/-- Continuity of the concrete selector-mixture ODE RHS for the universal
replicator solution family. -/
theorem selectorMU_mixTargetDerivRHS_continuous
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (s : Fin d_U) :
    Continuous fun τ : ℝ =>
      SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ s := by
  classical
  have hP : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => universalPval eta heta v ((sol w).u τ) := by
    intro v
    exact universalPval_continuous_of_cont_u eta heta v (fun i => (sol w).cont_u i)
  have hphi : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView,
        (sol w).lam v τ * universalPval eta heta v ((sol w).u τ) := by
    exact continuous_finset_sum Finset.univ (fun v _ =>
      ((sol w).cont_lam v).mul (hP v))
  have hbranch : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => BranchData.evalBranch (branchU v) ((sol w).u τ) s := by
    intro v
    simp only [BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u s)).add continuous_const
  have hq : Continuous fun τ : ℝ => qPulse bgpParams38.L τ := by
    simp only [qPulse]
    exact ((continuous_const.add Real.continuous_sin).div_const 2).pow bgpParams38.L
  have hgateU : Continuous fun τ : ℝ =>
      bGateU bgpParams38.L ((sol w).μ τ) τ := by
    simp only [bGateU]
    exact Real.continuous_exp.comp ((((sol w).cont_μ).mul hq).neg)
  have hcr : Continuous fun τ : ℝ =>
      ((1 + Real.cos τ) / 2) ^ Mcy := by
    fun_prop
  have hcg : Continuous fun τ : ℝ =>
      ((1 + Real.sin τ) / 2) ^ Mcy := by
    fun_prop
  have hgain : Continuous fun τ : ℝ =>
      (g₀ : ℝ) * Real.exp (bgpParams38.cα * τ) := by
    fun_prop
  dsimp [SelectorReplicatorDynSol.mixTargetDerivRHS]
  refine continuous_finset_sum Finset.univ ?_
  intro v _hv
  exact (((hcr.mul continuous_const).mul
      (continuous_const.sub ((sol w).cont_lam v))).add
        (((hcg.mul hgain).mul ((sol w).cont_lam v)).mul
          ((hP v).sub hphi))).mul (hbranch v) |>.add
    ((((sol w).cont_lam v).mul continuous_const).mul
      ((((continuous_const.mul (sol w).cont_α).mul hgateU).mul
        (((sol w).cont_z s).sub ((sol w).cont_u s)))))

/-- Halt-coordinate centered form of the concrete selector-mixture target
derivative.  The active transport and centered scale-spread terms vanish
because every universal branch writes the halt coordinate by a constant action. -/
theorem selectorMU_mixTargetDerivRHS_halt_eq_centered_lam
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (τ : ℝ) (c : UniversalLocalView)
    (hlam : (∑ v : UniversalLocalView, (sol w).lam v τ) = 1) :
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU =
      ∑ v : UniversalLocalView,
        ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
            ((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
              (sol w).lam v τ *
                (universalPval eta heta v ((sol w).u τ) -
                  ∑ w' : UniversalLocalView,
                    (sol w).lam w' τ *
                      universalPval eta heta w' ((sol w).u τ))) *
          (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
            BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)) := by
  classical
  letI : Nonempty UniversalLocalView := ⟨c⟩
  have hcenter :=
    SelectorReplicatorDynSol.mixTargetDerivRHS_eq_centered
      (sol := sol w) τ haltCoordU c hlam
  simpa [MachineInstance.branchU_halt_scale_eq_zero, mul_assoc] using hcenter

/-- Box-input version of `selectorMU_mixTargetDerivRHS_halt_eq_centered_lam`.
The selector mass condition is discharged from the simplex-replicator ODE. -/
theorem selectorMU_mixTargetDerivRHS_halt_eq_centered_lam_of_boxInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView) :
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU =
      ∑ v : UniversalLocalView,
        ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
            ((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
              (sol w).lam v τ *
                (universalPval eta heta v ((sol w).u τ) -
                  ∑ w' : UniversalLocalView,
                    (sol w).lam w' τ *
                      universalPval eta heta w' ((sol w).u τ))) *
          (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
            BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  have hsum_forward : ∀ s : ℝ, 0 ≤ s →
      (∑ v : UniversalLocalView, (sol w).lam v s) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
  exact selectorMU_mixTargetDerivRHS_halt_eq_centered_lam
    (sol := sol) w τ c (hsum_forward τ hτ0)

/-- Halt-coordinate active target derivative in the cancellation-preserving
gap/reset covariance coordinates. -/
theorem selectorMU_mixTargetDerivRHS_halt_eq_gap_covariance_sub_reset_defect_of_boxInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView) :
    SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU =
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ)) *
            ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
              ∑ w' : UniversalLocalView,
                (sol w).lam w' τ *
                  (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
      (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView,
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
          ∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  have hsum_forward : ∀ s : ℝ, 0 ≤ s →
      (∑ v : UniversalLocalView, (sol w).lam v s) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun v s => (sol w).lam v s)
      (P := fun v s => universalPval eta heta v ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun v => (sol w).cont_lam v)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
  have hcenter :=
    selectorMU_mixTargetDerivRHS_halt_eq_centered_lam_of_boxInputs
      (sol := sol) boxInputs w (τ := τ) hτ0 c
  have hgap :=
    SelectorDynSol.replicator_centered_rhs_eq_gap_covariance_sub_reset_defect
      (V := UniversalLocalView)
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (P := fun v : UniversalLocalView => universalPval eta heta v ((sol w).u τ))
      (B := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
      (cr := ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)))
      c (hsum_forward τ hτ0)
  exact hcenter.trans (by
    simpa [one_div, mul_assoc] using hgap)

/-- Fixed-coordinate active selector ODE in gap-tracking coordinates.

This rewrites the MU selector equation for `λ_v` as the linear defect toward the
active branch `c`, plus the mean-gap forcing term. -/
theorem selectorMU_lam_hasDerivAt_gapTrackingResidual_add_meanGap_of_boxInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (c v : UniversalLocalView) :
    HasDerivAt ((sol w).lam v)
      ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
          (((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
          (sol w).lam v τ +
        (((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
          (∑ x : UniversalLocalView,
            (sol w).lam x τ *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta x ((sol w).u τ))) *
          (sol w).lam v τ) τ := by
  classical
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  let cr : ℝ := ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  let cg : ℝ :=
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let P : UniversalLocalView → ℝ := fun u =>
    universalPval eta heta u ((sol w).u τ)
  let lam : UniversalLocalView → ℝ := fun u => (sol w).lam u τ
  have hode : ∀ v : UniversalLocalView, ∀ s : ℝ, 0 ≤ s →
      HasDerivAt ((sol w).lam v)
        ((((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v s)
          + (((1 + Real.sin s) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s))) *
            (sol w).lam v s *
              (universalPval eta heta v ((sol w).u s)
                - ∑ u : UniversalLocalView,
                    (sol w).lam u s * universalPval eta heta u ((sol w).u s))) s := by
    intro v s hs
    simpa [selectorSchedule] using
      (sol w).lam_hasDeriv v s (by simpa [selectorSchedule] using hs)
  have hsum_forward : ∀ s : ℝ, 0 ≤ s →
      (∑ u : UniversalLocalView, (sol w).lam u s) = 1 :=
    replicator_sum_lam_eq_one
      (lam := fun u s => (sol w).lam u s)
      (P := fun u s => universalPval eta heta u ((sol w).u s))
      (cr := fun s => ((1 + Real.cos s) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := fun s =>
        ((1 + Real.sin s) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * s)))
      boxInputs.hcr_cont boxInputs.hcg_cont
      (fun u => (sol w).cont_lam u)
      (boxInputs.hP_cont w) hode (boxInputs.hlam_sum0 w)
  have hrewrite :=
    SelectorDynSol.replicatorLamRHS_eq_gapTrackingResidual_add_meanGap
      (V := UniversalLocalView)
      (lam := lam) (P := P) (cr := cr) (cg := cg) (c := c) (v := v)
      (by simpa [lam] using hsum_forward τ hτ0)
  have hbase := hode v τ hτ0
  convert hbase using 1
  · simpa [cr, cg, P, lam, one_div, mul_assoc, mul_left_comm, mul_comm]
      using hrewrite.symm

/-- On the active suffix `[2πj + π/4, 2πj + π/2]`, the reset clock cosine is
nonnegative. -/
theorem selectorMU_activeSuffix_cos_nonneg (j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)) :
    0 ≤ Real.cos τ := by
  set x : ℝ := τ - 2 * Real.pi * (j : ℝ) with hx
  have hcos : Real.cos τ = Real.cos x := by
    have hrewrite : τ = x + (j : ℕ) * (2 * Real.pi) := by
      rw [hx]
      ring
    conv_lhs => rw [hrewrite]
    rw [Real.cos_add_nat_mul_two_pi]
  have hx_left : Real.pi / 4 ≤ x := by
    rw [hx]
    have hleft := hτ.1
    simp [selectorMUEarlyWriteSubStart] at hleft
    linarith
  have hx_right : x ≤ Real.pi / 2 := by
    rw [hx]
    have hright := hτ.2
    simp [selectorMUWriteHoldTime] at hright
    linarith
  have hx_neg : -(Real.pi / 2) ≤ x := by
    linarith [Real.pi_pos, hx_left]
  have hcosx : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le hx_neg hx_right
  rwa [hcos]

/-- The reset half-clock is bounded below by `1/2` on the active suffix. -/
theorem selectorMU_activeSuffix_resetBase_half_le (j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)) :
    (1 / 2 : ℝ) ≤ (1 + Real.cos τ) / 2 := by
  have hcos : 0 ≤ Real.cos τ :=
    selectorMU_activeSuffix_cos_nonneg j hτ
  linarith

/-- If the reset scale is positive, the concrete reset coefficient is strictly
positive throughout the active suffix. -/
theorem selectorMU_activeSuffix_resetCoeff_pos
    {Mcy : ℕ} {κ₀ : ℚ} (hκ₀_pos : 0 < (κ₀ : ℝ))
    (j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)) :
    0 < ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) := by
  have hbase_half :
      (1 / 2 : ℝ) ≤ (1 + Real.cos τ) / 2 :=
    selectorMU_activeSuffix_resetBase_half_le j hτ
  have hbase_pos : 0 < (1 + Real.cos τ) / 2 :=
    lt_of_lt_of_le (by norm_num) hbase_half
  exact mul_pos (pow_pos hbase_pos Mcy) hκ₀_pos

/-- The active gap-tracking sink `cr + cg * δ` is strictly positive whenever the
gap term `δ` is nonnegative. -/
theorem selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonneg
    {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (j : ℕ) {τ δ : ℝ}
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j))
    (hδ_nonneg : 0 ≤ δ) :
    0 <
      (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
        (((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) * δ := by
  have hcr_pos :
      0 < ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) :=
    selectorMU_activeSuffix_resetCoeff_pos hκ₀_pos j hτ
  have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
    nlinarith [Real.neg_one_le_sin τ]
  have hcg_nonneg :
      0 ≤ ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) := by
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  exact add_pos_of_pos_of_nonneg hcr_pos (mul_nonneg hcg_nonneg hδ_nonneg)

/-- Concrete reset coefficient on the active suffix. -/
def selectorMU_activeCr (Mcy : ℕ) (κ₀ : ℚ) (τ : ℝ) : ℝ :=
  ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)

/-- Concrete gap-amplifier coefficient on the active suffix. -/
def selectorMU_activeCg (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) : ℝ :=
  ((1 + Real.sin τ) / 2) ^ Mcy *
    ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))

/-- The active per-view quasi-steady-state denominator `cr + cg * gap`. -/
def selectorMU_activeSink
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  selectorMU_activeCr Mcy κ₀ τ +
    selectorMU_activeCg Mcy g₀ τ *
      (universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ))

/-- Active per-view quasi-steady-state target for the lambda ODE. -/
def selectorMU_activeQSS
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  (selectorMU_activeCr Mcy κ₀ τ *
      (Fintype.card UniversalLocalView : ℝ)⁻¹) /
    selectorMU_activeSink eta heta sol w c v τ

def selectorMU_activeCrDeriv (Mcy : ℕ) (κ₀ : ℚ) (τ : ℝ) : ℝ :=
  deriv (fun s : ℝ => selectorMU_activeCr Mcy κ₀ s) τ

def selectorMU_activeCgDeriv (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) : ℝ :=
  deriv (fun s : ℝ => selectorMU_activeCg Mcy g₀ s) τ

/-- The active gain profile is bounded by its exponential gain envelope. -/
theorem selectorMU_activeCg_abs_le_exp_gain
    (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) :
    |selectorMU_activeCg Mcy g₀ τ| ≤
      |(g₀ : ℝ)| * Real.exp (bgpParams38.cα * τ) := by
  let base : ℝ := (1 + Real.sin τ) / 2
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    nlinarith [Real.neg_one_le_sin τ]
  have hbase1 : base ≤ 1 := by
    dsimp [base]
    nlinarith [Real.sin_le_one τ]
  have hbase_pow_abs : |base ^ Mcy| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hbase0 _)]
    exact pow_le_one₀ hbase0 hbase1
  have hexp_nonneg : 0 ≤ Real.exp (bgpParams38.cα * τ) :=
    (Real.exp_pos _).le
  calc
    |selectorMU_activeCg Mcy g₀ τ|
        = |base ^ Mcy| * (|(g₀ : ℝ)| * Real.exp (bgpParams38.cα * τ)) := by
            rw [selectorMU_activeCg, abs_mul, abs_mul,
              abs_of_nonneg hexp_nonneg]
    _ ≤ 1 * (|(g₀ : ℝ)| * Real.exp (bgpParams38.cα * τ)) :=
        mul_le_mul_of_nonneg_right hbase_pow_abs
          (mul_nonneg (abs_nonneg _) hexp_nonneg)
    _ = |(g₀ : ℝ)| * Real.exp (bgpParams38.cα * τ) := by ring

/-- Crude uniform derivative bound for the active reset profile. -/
theorem selectorMU_activeCrDeriv_abs_le
    (Mcy : ℕ) (κ₀ : ℚ) (τ : ℝ) :
    |selectorMU_activeCrDeriv Mcy κ₀ τ| ≤ (Mcy : ℝ) * |(κ₀ : ℝ)| := by
  let base : ℝ := (1 + Real.cos τ) / 2
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    nlinarith [Real.neg_one_le_cos τ]
  have hbase1 : base ≤ 1 := by
    dsimp [base]
    nlinarith [Real.cos_le_one τ]
  have hbase_deriv :
      HasDerivAt (fun s : ℝ => (1 + Real.cos s) / 2)
        (-(Real.sin τ / 2)) τ := by
    convert ((hasDerivAt_const (x := τ) (c := (1 : ℝ))).add
      (Real.hasDerivAt_cos τ)).div_const 2 using 1
    ring
  have hcr :
      HasDerivAt (fun s : ℝ => selectorMU_activeCr Mcy κ₀ s)
        ((Mcy : ℝ) * base ^ (Mcy - 1) * (-(Real.sin τ / 2)) *
          (κ₀ : ℝ)) τ := by
    dsimp [selectorMU_activeCr, base]
    convert (hbase_deriv.pow Mcy).mul_const (κ₀ : ℝ) using 1
  have hderiv :
      selectorMU_activeCrDeriv Mcy κ₀ τ =
        (Mcy : ℝ) * base ^ (Mcy - 1) * (-(Real.sin τ / 2)) *
          (κ₀ : ℝ) := by
    simpa [selectorMU_activeCrDeriv] using hcr.deriv
  have hbase_pow_abs : |base ^ (Mcy - 1)| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hbase0 _)]
    exact pow_le_one₀ hbase0 hbase1
  have hsin_half_abs : |-(Real.sin τ / 2)| ≤ 1 := by
    rw [abs_neg, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [Real.abs_sin_le_one τ]
  have hM_nonneg : 0 ≤ (Mcy : ℝ) := Nat.cast_nonneg Mcy
  calc
    |selectorMU_activeCrDeriv Mcy κ₀ τ|
        = |(Mcy : ℝ) * base ^ (Mcy - 1) * (-(Real.sin τ / 2)) *
            (κ₀ : ℝ)| := by rw [hderiv]
    _ = (Mcy : ℝ) * |base ^ (Mcy - 1)| *
          |-(Real.sin τ / 2)| * |(κ₀ : ℝ)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hM_nonneg]
    _ ≤ (Mcy : ℝ) * 1 * 1 * |(κ₀ : ℝ)| := by
          have hprod :
              (Mcy : ℝ) * (|base ^ (Mcy - 1)| * |-(Real.sin τ / 2)|) ≤
                (Mcy : ℝ) * (1 * 1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hbase_pow_abs hsin_half_abs (abs_nonneg _) zero_le_one)
              hM_nonneg
          exact mul_le_mul_of_nonneg_right
            (by simpa [mul_assoc] using hprod) (abs_nonneg _)
    _ = (Mcy : ℝ) * |(κ₀ : ℝ)| := by ring

/-- Crude derivative bound for the active gain profile, with the exponential
gain envelope factored out. -/
theorem selectorMU_activeCgDeriv_abs_le_exp_gain
    (Mcy : ℕ) (g₀ : ℚ) (τ : ℝ) :
    |selectorMU_activeCgDeriv Mcy g₀ τ| ≤
      ((Mcy : ℝ) + 300) *
        (|(g₀ : ℝ)| * Real.exp (bgpParams38.cα * τ)) := by
  let base : ℝ := (1 + Real.sin τ) / 2
  let gain : ℝ := |(g₀ : ℝ)| * Real.exp (bgpParams38.cα * τ)
  let baseDeriv : ℝ := Real.cos τ / 2
  let gainDeriv : ℝ := (g₀ : ℝ) *
    (bgpParams38.cα * Real.exp (bgpParams38.cα * τ))
  have hbase0 : 0 ≤ base := by
    dsimp [base]
    nlinarith [Real.neg_one_le_sin τ]
  have hbase1 : base ≤ 1 := by
    dsimp [base]
    nlinarith [Real.sin_le_one τ]
  have hbase_pow_abs_pred : |base ^ (Mcy - 1)| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hbase0 _)]
    exact pow_le_one₀ hbase0 hbase1
  have hbase_pow_abs : |base ^ Mcy| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hbase0 _)]
    exact pow_le_one₀ hbase0 hbase1
  have hbase_deriv :
      HasDerivAt (fun s : ℝ => (1 + Real.sin s) / 2) baseDeriv τ := by
    dsimp [baseDeriv]
    convert ((hasDerivAt_const (x := τ) (c := (1 : ℝ))).add
      (Real.hasDerivAt_sin τ)).div_const 2 using 1
    ring
  have hexp_deriv :
      HasDerivAt (fun s : ℝ =>
        (g₀ : ℝ) * Real.exp (bgpParams38.cα * s)) gainDeriv τ := by
    simpa [gainDeriv, mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id τ).const_mul bgpParams38.cα).exp.const_mul
        (g₀ : ℝ))
  have hcg :
      HasDerivAt (fun s : ℝ => selectorMU_activeCg Mcy g₀ s)
        ((Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) +
          base ^ Mcy * gainDeriv) τ := by
    dsimp [selectorMU_activeCg, base]
    convert (hbase_deriv.pow Mcy).mul hexp_deriv using 1
  have hderiv :
      selectorMU_activeCgDeriv Mcy g₀ τ =
        (Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) +
          base ^ Mcy * gainDeriv := by
    simpa [selectorMU_activeCgDeriv] using hcg.deriv
  have hcos_half_abs : |baseDeriv| ≤ 1 := by
    dsimp [baseDeriv]
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [Real.abs_cos_le_one τ]
  have hα_abs : |bgpParams38.cα| ≤ (300 : ℝ) := by
    norm_num [bgpParams38]
  have hexp_nonneg : 0 ≤ Real.exp (bgpParams38.cα * τ) :=
    (Real.exp_pos _).le
  have hgain_nonneg : 0 ≤ gain := by
    dsimp [gain]
    exact mul_nonneg (abs_nonneg _) hexp_nonneg
  have hM_nonneg : 0 ≤ (Mcy : ℝ) := Nat.cast_nonneg Mcy
  have hterm_base :
      |(Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))| ≤
        (Mcy : ℝ) * gain := by
    calc
      |(Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))|
          = (Mcy : ℝ) * |base ^ (Mcy - 1)| * |baseDeriv| * gain := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul,
                abs_of_nonneg hM_nonneg, abs_of_nonneg hexp_nonneg]
      _ ≤ (Mcy : ℝ) * 1 * 1 * gain := by
          have hprod :
              (Mcy : ℝ) * (|base ^ (Mcy - 1)| * |baseDeriv|) ≤
                (Mcy : ℝ) * (1 * 1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hbase_pow_abs_pred hcos_half_abs
                (abs_nonneg _) zero_le_one) hM_nonneg
          exact mul_le_mul_of_nonneg_right
            (by simpa [mul_assoc] using hprod) hgain_nonneg
      _ = (Mcy : ℝ) * gain := by ring
  have hterm_exp :
      |base ^ Mcy * gainDeriv| ≤ (300 : ℝ) * gain := by
    have hgainDeriv_abs : |gainDeriv| ≤ (300 : ℝ) * gain := by
      calc
        |gainDeriv|
            = |(g₀ : ℝ)| *
                (|bgpParams38.cα| * Real.exp (bgpParams38.cα * τ)) := by
                dsimp [gainDeriv]
                rw [abs_mul, abs_mul, abs_of_nonneg hexp_nonneg]
        _ ≤ |(g₀ : ℝ)| * ((300 : ℝ) * Real.exp (bgpParams38.cα * τ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hα_abs hexp_nonneg)
              (abs_nonneg _)
        _ = (300 : ℝ) * gain := by
            dsimp [gain]
            ring
    calc
      |base ^ Mcy * gainDeriv|
          = |base ^ Mcy| * |gainDeriv| := by rw [abs_mul]
      _ ≤ 1 * ((300 : ℝ) * gain) :=
          mul_le_mul hbase_pow_abs hgainDeriv_abs (abs_nonneg _) zero_le_one
      _ = (300 : ℝ) * gain := by ring
  calc
    |selectorMU_activeCgDeriv Mcy g₀ τ|
        = |((Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) +
            base ^ Mcy * gainDeriv)| := by rw [hderiv]
    _ ≤ |(Mcy : ℝ) * base ^ (Mcy - 1) * baseDeriv *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))| +
          |base ^ Mcy * gainDeriv| :=
        abs_add_le _ _
    _ ≤ (Mcy : ℝ) * gain + (300 : ℝ) * gain := add_le_add hterm_base hterm_exp
    _ = ((Mcy : ℝ) + 300) * gain := by ring_nf

/-- Chain-rule RHS for the active denominator. -/
def selectorMU_activeSinkDerivRHS
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  let delta :=
    universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ)
  let delta' :=
    selectorMU_universalPvalDerivRHS eta heta sol w c τ -
      selectorMU_universalPvalDerivRHS eta heta sol w v τ
  selectorMU_activeCrDeriv Mcy κ₀ τ +
    selectorMU_activeCgDeriv Mcy g₀ τ * delta +
      selectorMU_activeCg Mcy g₀ τ * delta'

/-- Quotient-rule RHS for the active quasi-steady-state target. -/
def selectorMU_activeQSSDerivRHS
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ) : ℝ :=
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  let r := selectorMU_activeCr Mcy κ₀ τ * card⁻¹
  let r' := selectorMU_activeCrDeriv Mcy κ₀ τ * card⁻¹
  let k := selectorMU_activeSink eta heta sol w c v τ
  let k' := selectorMU_activeSinkDerivRHS eta heta sol w c v τ
  (r' * k - r * k') / (k ^ 2)

/-- Scalar quotient estimate for an active QSS derivative after rewriting
`qss = rho / (N * (rho + delta))`. -/
theorem selectorMU_activeQSSDeriv_abs_le_rho_delta
    {N gamma rho rhoD delta deltaD : ℝ}
    (hN_pos : 0 < N)
    (hgamma_pos : 0 < gamma)
    (hrho_nonneg : 0 ≤ rho)
    (hdelta_gap : gamma ≤ delta) :
    |(1 / N) * ((rhoD * delta - rho * deltaD) / (rho + delta) ^ 2)| ≤
      (1 / N) * (|rhoD| / gamma + rho * |deltaD| / gamma ^ 2) := by
  let R : ℝ := rho + delta
  have hdelta_nonneg : 0 ≤ delta := le_trans hgamma_pos.le hdelta_gap
  have hR_ge_delta : delta ≤ R := by dsimp [R]; linarith
  have hR_ge_gamma : gamma ≤ R := le_trans hdelta_gap hR_ge_delta
  have hR_pos : 0 < R := lt_of_lt_of_le hgamma_pos hR_ge_gamma
  have hR2_pos : 0 < R ^ 2 := sq_pos_of_pos hR_pos
  have hgamma2_pos : 0 < gamma ^ 2 := sq_pos_of_pos hgamma_pos
  have hnum_abs :
      |rhoD * delta - rho * deltaD| ≤ |rhoD| * delta + rho * |deltaD| := by
    calc
      |rhoD * delta - rho * deltaD|
          ≤ |rhoD * delta| + |rho * deltaD| :=
              abs_sub (rhoD * delta) (rho * deltaD)
      _ = |rhoD| * delta + rho * |deltaD| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hdelta_nonneg,
            abs_of_nonneg hrho_nonneg]
  have hdelta_div :
      delta / R ^ 2 ≤ 1 / gamma := by
    rw [div_le_iff₀ hR2_pos]
    field_simp [ne_of_gt hgamma_pos]
    have hmul : delta * gamma ≤ R * R :=
      mul_le_mul hR_ge_delta hR_ge_gamma hgamma_pos.le hR_pos.le
    nlinarith [hmul]
  have hR2_inv :
      1 / R ^ 2 ≤ 1 / gamma ^ 2 := by
    rw [div_le_div_iff₀ hR2_pos hgamma2_pos]
    have hsq : gamma * gamma ≤ R * R :=
      mul_le_mul hR_ge_gamma hR_ge_gamma hgamma_pos.le hR_pos.le
    nlinarith [hsq]
  have hcore :
      |(rhoD * delta - rho * deltaD) / R ^ 2| ≤
        |rhoD| / gamma + rho * |deltaD| / gamma ^ 2 := by
    calc
      |(rhoD * delta - rho * deltaD) / R ^ 2|
          = |rhoD * delta - rho * deltaD| / R ^ 2 := by
              rw [abs_div, abs_of_nonneg hR2_pos.le]
      _ ≤ (|rhoD| * delta + rho * |deltaD|) / R ^ 2 :=
              div_le_div_of_nonneg_right hnum_abs hR2_pos.le
      _ = |rhoD| * (delta / R ^ 2) +
            (rho * |deltaD|) * (1 / R ^ 2) := by
              field_simp [ne_of_gt hR2_pos]
      _ ≤ |rhoD| * (1 / gamma) +
            (rho * |deltaD|) * (1 / gamma ^ 2) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hdelta_div (abs_nonneg rhoD))
                (mul_le_mul_of_nonneg_left hR2_inv
                  (mul_nonneg hrho_nonneg (abs_nonneg deltaD)))
      _ = |rhoD| / gamma + rho * |deltaD| / gamma ^ 2 := by
              ring
  have hNinv_nonneg : 0 ≤ 1 / N := by positivity
  calc
    |(1 / N) * ((rhoD * delta - rho * deltaD) / (rho + delta) ^ 2)|
        = (1 / N) * |(rhoD * delta - rho * deltaD) / R ^ 2| := by
            rw [abs_mul, abs_of_nonneg hNinv_nonneg]
    _ ≤ (1 / N) * (|rhoD| / gamma + rho * |deltaD| / gamma ^ 2) :=
        mul_le_mul_of_nonneg_left hcore hNinv_nonneg

/-- Pointwise active-QSS derivative bound, reducing the analytic work to scalar
bounds on the active reset derivative and on the amplified payoff-gap
derivative. -/
theorem selectorMU_activeQSSDerivRHS_abs_le_of_deltaD_bound
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ)
    {gamma CrD DeltaD : ℝ}
    (hgamma_pos : 0 < gamma)
    (hcr_nonneg : 0 ≤ selectorMU_activeCr Mcy κ₀ τ)
    (hdelta_floor :
      gamma ≤
        selectorMU_activeCg Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)))
    (hcrD : |selectorMU_activeCrDeriv Mcy κ₀ τ| ≤ CrD)
    (hdeltaD :
      |selectorMU_activeCgDeriv Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)) +
        selectorMU_activeCg Mcy g₀ τ *
          (selectorMU_universalPvalDerivRHS eta heta sol w c τ -
            selectorMU_universalPvalDerivRHS eta heta sol w v τ)| ≤ DeltaD) :
    |selectorMU_activeQSSDerivRHS eta heta sol w c v τ| ≤
      (1 / (Fintype.card UniversalLocalView : ℝ)) *
        (CrD / gamma + selectorMU_activeCr Mcy κ₀ τ * DeltaD / gamma ^ 2) := by
  classical
  let card : ℝ := Fintype.card UniversalLocalView
  let cr : ℝ := selectorMU_activeCr Mcy κ₀ τ
  let crD : ℝ := selectorMU_activeCrDeriv Mcy κ₀ τ
  let delta : ℝ :=
    selectorMU_activeCg Mcy g₀ τ *
      (universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ))
  let deltaD : ℝ :=
    selectorMU_activeCgDeriv Mcy g₀ τ *
        (universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)) +
      selectorMU_activeCg Mcy g₀ τ *
        (selectorMU_universalPvalDerivRHS eta heta sol w c τ -
          selectorMU_universalPvalDerivRHS eta heta sol w v τ)
  have hcard_pos : 0 < card := by
    dsimp [card]
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨defaultLocalViewU⟩ :
        0 < Fintype.card UniversalLocalView)
  have hqss_eq :
      selectorMU_activeQSSDerivRHS eta heta sol w c v τ =
        (1 / card) * ((crD * delta - cr * deltaD) / (cr + delta) ^ 2) := by
    dsimp [selectorMU_activeQSSDerivRHS, selectorMU_activeSinkDerivRHS,
      selectorMU_activeSink, card, cr, crD, delta, deltaD]
    ring
  have hbase :=
    selectorMU_activeQSSDeriv_abs_le_rho_delta
      (N := card) (gamma := gamma) (rho := cr) (rhoD := crD)
      (delta := delta) (deltaD := deltaD)
      hcard_pos hgamma_pos (by simpa [cr] using hcr_nonneg)
      (by simpa [delta] using hdelta_floor)
  have hcore :
      |crD| / gamma + cr * |deltaD| / gamma ^ 2 ≤
        CrD / gamma + cr * DeltaD / gamma ^ 2 := by
    have hgamma2_nonneg : 0 ≤ gamma ^ 2 := sq_nonneg gamma
    exact add_le_add
      (div_le_div_of_nonneg_right (by simpa [crD] using hcrD) hgamma_pos.le)
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by simpa [deltaD] using hdeltaD)
          (by simpa [cr] using hcr_nonneg))
        hgamma2_nonneg)
  have hNinv_nonneg : 0 ≤ 1 / card := by positivity
  calc
    |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|
        = |(1 / card) * ((crD * delta - cr * deltaD) / (cr + delta) ^ 2)| := by
            rw [hqss_eq]
    _ ≤ (1 / card) * (|crD| / gamma + cr * |deltaD| / gamma ^ 2) := hbase
    _ ≤ (1 / card) * (CrD / gamma + cr * DeltaD / gamma ^ 2) :=
        mul_le_mul_of_nonneg_left hcore hNinv_nonneg
    _ =
        (1 / (Fintype.card UniversalLocalView : ℝ)) *
          (CrD / gamma + selectorMU_activeCr Mcy κ₀ τ * DeltaD / gamma ^ 2) := by
        rfl

/-- Pointwise active-QSS derivative bound with the denominator derivative split
into a scalar active-gain derivative bound and a payoff-gap derivative bound. -/
theorem selectorMU_activeQSSDerivRHS_abs_le_of_gap_and_pvalDeriv_bounds
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ)
    {gamma CrD CgD GapB PGapD : ℝ}
    (hgamma_pos : 0 < gamma)
    (hcr_nonneg : 0 ≤ selectorMU_activeCr Mcy κ₀ τ)
    (hcg_nonneg : 0 ≤ selectorMU_activeCg Mcy g₀ τ)
    (hdelta_floor :
      gamma ≤
        selectorMU_activeCg Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)))
    (hcrD : |selectorMU_activeCrDeriv Mcy κ₀ τ| ≤ CrD)
    (hcgD : |selectorMU_activeCgDeriv Mcy g₀ τ| ≤ CgD)
    (hgapB :
      |universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)| ≤ GapB)
    (hpGapD :
      |selectorMU_universalPvalDerivRHS eta heta sol w c τ -
        selectorMU_universalPvalDerivRHS eta heta sol w v τ| ≤ PGapD) :
    |selectorMU_activeQSSDerivRHS eta heta sol w c v τ| ≤
      (1 / (Fintype.card UniversalLocalView : ℝ)) *
        (CrD / gamma +
          selectorMU_activeCr Mcy κ₀ τ *
            (CgD * GapB + selectorMU_activeCg Mcy g₀ τ * PGapD) /
              gamma ^ 2) := by
  let gap : ℝ :=
    universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ)
  let pGapD : ℝ :=
    selectorMU_universalPvalDerivRHS eta heta sol w c τ -
      selectorMU_universalPvalDerivRHS eta heta sol w v τ
  let cg : ℝ := selectorMU_activeCg Mcy g₀ τ
  let cgD : ℝ := selectorMU_activeCgDeriv Mcy g₀ τ
  have hCgD_nonneg : 0 ≤ CgD :=
    le_trans (abs_nonneg cgD) (by simpa [cgD] using hcgD)
  have hGapB_nonneg : 0 ≤ GapB :=
    le_trans (abs_nonneg gap) (by simpa [gap] using hgapB)
  have hPGapD_nonneg : 0 ≤ PGapD :=
    le_trans (abs_nonneg pGapD) (by simpa [pGapD] using hpGapD)
  have hterm1 :
      |cgD * gap| ≤ CgD * GapB := by
    rw [abs_mul]
    exact mul_le_mul (by simpa [cgD] using hcgD)
      (by simpa [gap] using hgapB) (abs_nonneg gap) hCgD_nonneg
  have hterm2 :
      |cg * pGapD| ≤ cg * PGapD := by
    rw [abs_mul, abs_of_nonneg hcg_nonneg]
    exact mul_le_mul le_rfl (by simpa [pGapD] using hpGapD)
      (abs_nonneg pGapD) hcg_nonneg
  have hdeltaD :
      |selectorMU_activeCgDeriv Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)) +
        selectorMU_activeCg Mcy g₀ τ *
          (selectorMU_universalPvalDerivRHS eta heta sol w c τ -
            selectorMU_universalPvalDerivRHS eta heta sol w v τ)| ≤
        CgD * GapB + selectorMU_activeCg Mcy g₀ τ * PGapD := by
    calc
      |selectorMU_activeCgDeriv Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)) +
        selectorMU_activeCg Mcy g₀ τ *
          (selectorMU_universalPvalDerivRHS eta heta sol w c τ -
            selectorMU_universalPvalDerivRHS eta heta sol w v τ)|
          = |cgD * gap + cg * pGapD| := by
              rfl
      _ ≤ |cgD * gap| + |cg * pGapD| := abs_add_le _ _
      _ ≤ CgD * GapB + cg * PGapD := add_le_add hterm1 hterm2
      _ = CgD * GapB + selectorMU_activeCg Mcy g₀ τ * PGapD := by
          rfl
  exact
    selectorMU_activeQSSDerivRHS_abs_le_of_deltaD_bound
      eta heta (sol := sol) w c v τ
      hgamma_pos hcr_nonneg hdelta_floor hcrD hdeltaD

/-- Pointwise active-QSS derivative bound whose payoff-gap derivative is
discharged by a shared `u`-tube gradient box and a uniform `u`-RHS bound. -/
theorem selectorMU_activeQSSDerivRHS_abs_le_of_utube_uRHS_bounds
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w : ℕ) (c v : UniversalLocalView) (τ : ℝ)
    (cfg : UConf) {ρ gamma CrD CgD GapB URhs : ℝ}
    (hρ0 : 0 ≤ ρ)
    (hgamma_pos : 0 < gamma)
    (hcr_nonneg : 0 ≤ selectorMU_activeCr Mcy κ₀ τ)
    (hcg_nonneg : 0 ≤ selectorMU_activeCg Mcy g₀ τ)
    (hdelta_floor :
      gamma ≤
        selectorMU_activeCg Mcy g₀ τ *
          (universalPval eta heta c ((sol w).u τ) -
            universalPval eta heta v ((sol w).u τ)))
    (hcrD : |selectorMU_activeCrDeriv Mcy κ₀ τ| ≤ CrD)
    (hcgD : |selectorMU_activeCgDeriv Mcy g₀ τ| ≤ CgD)
    (hgapB :
      |universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)| ≤ GapB)
    (hutube : UTube ρ cfg ((sol w).u τ))
    (huRHS : ∀ i : Fin d_U,
      |selectorMU_uDerivRHS sol w τ i| ≤ URhs) :
    |selectorMU_activeQSSDerivRHS eta heta sol w c v τ| ≤
      (1 / (Fintype.card UniversalLocalView : ℝ)) *
        (CrD / gamma +
          selectorMU_activeCr Mcy κ₀ τ *
            (CgD * GapB +
              selectorMU_activeCg Mcy g₀ τ *
                ((selectorMU_pvalGradBoxBound eta heta c
                    (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|) +
                  selectorMU_pvalGradBoxBound eta heta v
                    (fun k : Fin d_U => ρ + |(confEncU cfg k : ℝ)|)) *
                  URhs)) /
              gamma ^ 2) := by
  have hpGapD :=
    selectorMU_universalPvalGapDerivRHS_abs_le_utube_gradBoxBound_mul_uniform_uRHS
      eta heta (sol := sol) w c v τ cfg ρ hρ0 hutube huRHS
  exact
    selectorMU_activeQSSDerivRHS_abs_le_of_gap_and_pvalDeriv_bounds
      eta heta (sol := sol) w c v τ
      hgamma_pos hcr_nonneg hcg_nonneg hdelta_floor hcrD hcgD hgapB hpGapD

/-- The active quasi-steady-state target is differentiable along a selector
solution, with a concrete chain-rule RHS. -/
theorem selectorMU_activeQSS_hasDerivAt_of_sol_u_hasDerivAt
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c v : UniversalLocalView) {τ : ℝ}
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j))
    (hdelta_nonneg :
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    HasDerivAt
      (fun s => selectorMU_activeQSS eta heta sol w c v s)
      (selectorMU_activeQSSDerivRHS eta heta sol w c v τ) τ := by
  classical
  have hτ0 : 0 ≤ τ := by
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (le_trans (selectorMUWriteStart_le_earlySubStart j) hτ.1)
  have hdom : τ ∈ selectorSchedule.domain :=
    selectorSchedule_domain_of_nonneg_structural τ hτ0
  have hcr_diff :
      DifferentiableAt ℝ (fun s : ℝ => selectorMU_activeCr Mcy κ₀ s) τ := by
    dsimp [selectorMU_activeCr]
    fun_prop
  have hcg_diff :
      DifferentiableAt ℝ (fun s : ℝ => selectorMU_activeCg Mcy g₀ s) τ := by
    dsimp [selectorMU_activeCg]
    fun_prop
  have hcr :
      HasDerivAt (fun s : ℝ => selectorMU_activeCr Mcy κ₀ s)
        (selectorMU_activeCrDeriv Mcy κ₀ τ) τ := by
    simpa [selectorMU_activeCrDeriv] using hcr_diff.hasDerivAt
  have hcg :
      HasDerivAt (fun s : ℝ => selectorMU_activeCg Mcy g₀ s)
        (selectorMU_activeCgDeriv Mcy g₀ τ) τ := by
    simpa [selectorMU_activeCgDeriv] using hcg_diff.hasDerivAt
  have hdelta :
      HasDerivAt
        (fun s =>
          universalPval eta heta c ((sol w).u s) -
            universalPval eta heta v ((sol w).u s))
        (selectorMU_universalPvalDerivRHS eta heta sol w c τ -
          selectorMU_universalPvalDerivRHS eta heta sol w v τ) τ :=
    selectorMU_universalPval_gap_hasDerivAt_of_sol_u_hasDerivAt
      (sol := sol) w c v hdom
  have hk :
      HasDerivAt
        (fun s => selectorMU_activeSink eta heta sol w c v s)
        (selectorMU_activeSinkDerivRHS eta heta sol w c v τ) τ := by
    convert hcr.add (hcg.mul hdelta) using 1
    simp [selectorMU_activeSinkDerivRHS]
    ring
  have hr :
      HasDerivAt
        (fun s => selectorMU_activeCr Mcy κ₀ s *
          (Fintype.card UniversalLocalView : ℝ)⁻¹)
        (selectorMU_activeCrDeriv Mcy κ₀ τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹) τ :=
    hcr.mul_const _
  have hk_pos : 0 < selectorMU_activeSink eta heta sol w c v τ := by
    simpa [selectorMU_activeSink, selectorMU_activeCr, selectorMU_activeCg] using
      selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonneg
        (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀)
        hκ₀_pos hg₀_nonneg j hτ hdelta_nonneg
  have hq := hr.div hk (ne_of_gt hk_pos)
  simpa [selectorMU_activeQSS, selectorMU_activeQSSDerivRHS, pow_two] using hq

theorem selectorMU_activeCr_continuous (Mcy : ℕ) (κ₀ : ℚ) :
    Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ := by
  dsimp [selectorMU_activeCr]
  fun_prop

theorem selectorMU_activeCg_continuous (Mcy : ℕ) (g₀ : ℚ) :
    Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ := by
  dsimp [selectorMU_activeCg]
  fun_prop

theorem selectorMU_activeCrDeriv_continuous (Mcy : ℕ) (κ₀ : ℚ) :
    Continuous fun τ : ℝ => selectorMU_activeCrDeriv Mcy κ₀ τ := by
  have hcd : ContDiff ℝ 1 (fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ) := by
    dsimp [selectorMU_activeCr]
    fun_prop
  simpa [selectorMU_activeCrDeriv] using hcd.continuous_deriv le_rfl

theorem selectorMU_activeCgDeriv_continuous (Mcy : ℕ) (g₀ : ℚ) :
    Continuous fun τ : ℝ => selectorMU_activeCgDeriv Mcy g₀ τ := by
  have hcd : ContDiff ℝ 1 (fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ) := by
    dsimp [selectorMU_activeCg]
    fun_prop
  simpa [selectorMU_activeCgDeriv] using hcd.continuous_deriv le_rfl

theorem selectorMU_activeSink_continuous
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) :
    Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
  have hcr := selectorMU_activeCr_continuous Mcy κ₀
  have hcg := selectorMU_activeCg_continuous Mcy g₀
  have hdelta :
      Continuous fun τ : ℝ =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ) :=
    (universalPval_continuous_of_cont_u eta heta c (fun i => (sol w).cont_u i)).sub
      (universalPval_continuous_of_cont_u eta heta v (fun i => (sol w).cont_u i))
  simpa [selectorMU_activeSink] using hcr.add (hcg.mul hdelta)

theorem selectorMU_activeSinkDerivRHS_continuous
    (eta : ℚ) (heta : 0 < eta) {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (w : ℕ) (c v : UniversalLocalView) :
    Continuous fun τ : ℝ => selectorMU_activeSinkDerivRHS eta heta sol w c v τ := by
  have hcrD := selectorMU_activeCrDeriv_continuous Mcy κ₀
  have hcgD := selectorMU_activeCgDeriv_continuous Mcy g₀
  have hcg := selectorMU_activeCg_continuous Mcy g₀
  have hdelta :
      Continuous fun τ : ℝ =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ) :=
    (universalPval_continuous_of_cont_u eta heta c (fun i => (sol w).cont_u i)).sub
      (universalPval_continuous_of_cont_u eta heta v (fun i => (sol w).cont_u i))
  have hdeltaD :
      Continuous fun τ : ℝ =>
        selectorMU_universalPvalDerivRHS eta heta sol w c τ -
          selectorMU_universalPvalDerivRHS eta heta sol w v τ :=
    (selectorMU_universalPvalDerivRHS_continuous eta heta sol w c).sub
      (selectorMU_universalPvalDerivRHS_continuous eta heta sol w v)
  simpa [selectorMU_activeSinkDerivRHS, add_assoc] using
    hcrD.add ((hcgD.mul hdelta).add (hcg.mul hdeltaD))

theorem selectorMU_activeQSSDerivRHS_continuousOn_of_gap_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c v : UniversalLocalView)
    (hdelta_nonneg :
      ∀ τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
        0 ≤ universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)) :
    ContinuousOn
      (fun τ : ℝ => selectorMU_activeQSSDerivRHS eta heta sol w c v τ)
      (Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)) := by
  let s : Set ℝ := Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)
  let card : ℝ := (Fintype.card UniversalLocalView : ℝ)
  have hcr := selectorMU_activeCr_continuous Mcy κ₀
  have hcrD := selectorMU_activeCrDeriv_continuous Mcy κ₀
  have hk := selectorMU_activeSink_continuous eta heta sol w c v
  have hkD := selectorMU_activeSinkDerivRHS_continuous eta heta sol w c v
  have hk_pos :
      ∀ τ ∈ s, 0 < selectorMU_activeSink eta heta sol w c v τ := by
    intro τ hτ
    simpa [s, selectorMU_activeSink, selectorMU_activeCr, selectorMU_activeCg] using
      selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonneg
        (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀)
        hκ₀_pos hg₀_nonneg j (by simpa [s] using hτ)
        (by simpa [s] using hdelta_nonneg τ hτ)
  have hden_ne :
      ∀ τ ∈ s, selectorMU_activeSink eta heta sol w c v τ ^ 2 ≠ 0 := by
    intro τ hτ
    exact pow_ne_zero 2 (ne_of_gt (hk_pos τ hτ))
  have hnum :
      Continuous fun τ : ℝ =>
        (selectorMU_activeCrDeriv Mcy κ₀ τ * card⁻¹) *
            selectorMU_activeSink eta heta sol w c v τ -
          (selectorMU_activeCr Mcy κ₀ τ * card⁻¹) *
            selectorMU_activeSinkDerivRHS eta heta sol w c v τ :=
    ((hcrD.mul continuous_const).mul hk).sub
      ((hcr.mul continuous_const).mul hkD)
  have hden :
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ ^ 2 :=
    hk.pow 2
  simpa [s, card, selectorMU_activeQSSDerivRHS] using
    hnum.continuousOn.div hden.continuousOn hden_ne

/-- Fixed-coordinate active selector ODE in forced quasi-steady-state form.

This is the division-bearing form consumed by the scalar Duhamel estimate.  The
denominator is nonzero because the active reset coefficient is strictly
positive on the suffix and the payoff gap is nonnegative. -/
theorem selectorMU_lam_hasDerivAt_forcedQSS_of_boxInputs_activeSuffix
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j))
    (c v : UniversalLocalView)
    (hdelta_nonneg :
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    HasDerivAt ((sol w).lam v)
      (((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
            (((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta v ((sol w).u τ))) *
          (((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹) /
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) -
            (sol w).lam v τ) +
        (((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
          (∑ x : UniversalLocalView,
            (sol w).lam x τ *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta x ((sol w).u τ))) *
          (sol w).lam v τ) τ := by
  classical
  let cr : ℝ := ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  let cg : ℝ :=
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let delta : ℝ :=
    universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ)
  let meanGap : ℝ :=
    ∑ x : UniversalLocalView,
      (sol w).lam x τ *
        (universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta x ((sol w).u τ))
  let yv : ℝ := (sol w).lam v τ
  haveI : Nonempty UniversalLocalView := ⟨defaultLocalViewU⟩
  have hcard_ne : (Fintype.card UniversalLocalView : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card UniversalLocalView ≠ 0)
  have hk_pos : 0 < cr + cg * delta := by
    simpa [cr, cg, delta] using
      selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonneg
        (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀)
        hκ₀_pos hg₀_nonneg j hτ
        (by simpa [delta] using hdelta_nonneg)
  have hk_ne : cr + cg * delta ≠ 0 := ne_of_gt hk_pos
  have hqss_eq :
      (cr + cg * delta) *
          ((cr * (Fintype.card UniversalLocalView : ℝ)⁻¹) /
              (cr + cg * delta) - yv) +
        cg * meanGap * yv =
      cr * (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          (cr + cg * delta) * yv +
        cg * meanGap * yv := by
    field_simp [hk_ne]
  have hlin :=
    selectorMU_lam_hasDerivAt_gapTrackingResidual_add_meanGap_of_boxInputs
      (sol := sol) boxInputs w hτ0 c v
  convert hlin using 1

/-- The fixed-coordinate active QSS target is continuous on the active suffix
whenever the active payoff gap is nonnegative there. -/
theorem selectorMU_activeSuffix_qss_continuousOn_of_gap_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c v : UniversalLocalView)
    (hdelta_nonneg :
      ∀ τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
        0 ≤ universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)) :
    ContinuousOn
      (fun τ =>
        ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (Fintype.card UniversalLocalView : ℝ)⁻¹) /
          ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
            (((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta v ((sol w).u τ))))
      (Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)) := by
  classical
  let s : Set ℝ := Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)
  let cr : ℝ → ℝ := fun τ =>
    ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  let cg : ℝ → ℝ := fun τ =>
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let delta : ℝ → ℝ := fun τ =>
    universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ)
  have hcr_cont : Continuous cr := by
    simpa [cr] using boxInputs.hcr_cont
  have hcg_cont : Continuous cg := by
    simpa [cg] using boxInputs.hcg_cont
  have hdelta_cont : Continuous delta := by
    simpa [delta] using (boxInputs.hP_cont w c).sub (boxInputs.hP_cont w v)
  have hden_ne : ∀ τ ∈ s, cr τ + cg τ * delta τ ≠ 0 :=
    fun τ hτ => ne_of_gt
      (selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonneg
        (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀)
        hκ₀_pos hg₀_nonneg j (by simpa [s] using hτ)
        (by simpa [delta, s] using hdelta_nonneg τ hτ))
  have hnum_cont : ContinuousOn (fun τ => cr τ * (Fintype.card UniversalLocalView : ℝ)⁻¹) s :=
    (hcr_cont.mul continuous_const).continuousOn
  have hden_cont : ContinuousOn (fun τ => cr τ + cg τ * delta τ) s :=
    (hcr_cont.add (hcg_cont.mul hdelta_cont)).continuousOn
  simpa [s, cr, cg, delta] using hnum_cont.div hden_cont hden_ne

/-- Fixed-coordinate active λ-defect integral estimate on the active suffix.

This is the scalar Duhamel producer for the branch-residual surface.  The target
derivative is kept as an explicit `m'` hypothesis; discharging that derivative
is the remaining QSS-calculus step, while the ODE rewrite, sink positivity, and
closed-interval continuity are discharged here. -/
theorem selectorMU_activeSuffix_lam_defect_integral_le_initial_qss_tracking_add_qssDeriv_add_meanGap_forcing_of_boxInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c v : UniversalLocalView) (m' : ℝ → ℝ)
    (hm'_cont :
      ContinuousOn m' (Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)))
    (hdelta_nonneg :
      ∀ τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
        0 ≤ universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ))
    (hm_deriv :
      ∀ τ ∈ Ioo (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
        HasDerivAt
          (fun τ =>
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
                (Fintype.card UniversalLocalView : ℝ)⁻¹) /
              ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
                (((1 + Real.sin τ) / 2) ^ Mcy *
                  ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                  (universalPval eta heta c ((sol w).u τ) -
                    universalPval eta heta v ((sol w).u τ))))
          (m' τ) τ) :
    (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
      |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
          (((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
          (sol w).lam v τ|) ≤
      |(((((1 + Real.cos (selectorMUEarlyWriteSubStart j)) / 2) ^ Mcy *
              (κ₀ : ℝ)) *
            (Fintype.card UniversalLocalView : ℝ)⁻¹) /
          ((((1 + Real.cos (selectorMUEarlyWriteSubStart j)) / 2) ^ Mcy *
              (κ₀ : ℝ)) +
            (((1 + Real.sin (selectorMUEarlyWriteSubStart j)) / 2) ^ Mcy *
              ((g₀ : ℝ) *
                Real.exp (bgpParams38.cα * selectorMUEarlyWriteSubStart j))) *
              (universalPval eta heta c
                  ((sol w).u (selectorMUEarlyWriteSubStart j)) -
                universalPval eta heta v
                  ((sol w).u (selectorMUEarlyWriteSubStart j)))) -
            (sol w).lam v (selectorMUEarlyWriteSubStart j))| +
      (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        |m' τ|) +
      (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        |(((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
              (sol w).lam v τ|) := by
  classical
  let a : ℝ := selectorMUEarlyWriteSubStart j
  let b : ℝ := selectorMUWriteHoldTime j
  let cr : ℝ → ℝ := fun τ =>
    ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  let cg : ℝ → ℝ := fun τ =>
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let delta : ℝ → ℝ := fun τ =>
    universalPval eta heta c ((sol w).u τ) -
      universalPval eta heta v ((sol w).u τ)
  let meanGap : ℝ → ℝ := fun τ =>
    ∑ x : UniversalLocalView,
      (sol w).lam x τ *
        (universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta x ((sol w).u τ))
  let k : ℝ → ℝ := fun τ => cr τ + cg τ * delta τ
  let r : ℝ → ℝ := fun τ =>
    cr τ * (Fintype.card UniversalLocalView : ℝ)⁻¹
  let f : ℝ → ℝ := fun τ => cg τ * meanGap τ * (sol w).lam v τ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUEarlySubStart_le_writeHold j
  have ha0 : 0 ≤ a := by
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [a] using selectorMUWriteStart_le_earlySubStart j)
  have hk_cont : ContinuousOn k (Icc a b) := by
    have hcr_cont : Continuous cr := by simpa [cr] using boxInputs.hcr_cont
    have hcg_cont : Continuous cg := by simpa [cg] using boxInputs.hcg_cont
    have hdelta_cont : Continuous delta := by
      simpa [delta] using (boxInputs.hP_cont w c).sub (boxInputs.hP_cont w v)
    exact (hcr_cont.add (hcg_cont.mul hdelta_cont)).continuousOn
  have hk_pos : ∀ τ ∈ Icc a b, 0 < k τ := by
    intro τ hτ
    exact
      (by
        simpa [a, b, k, cr, cg, delta] using
          selectorMU_activeSuffix_sinkCoeff_pos_of_gap_nonneg
            (Mcy := Mcy) (κ₀ := κ₀) (g₀ := g₀)
            hκ₀_pos hg₀_nonneg j (by simpa [a, b] using hτ)
            (by simpa [a, b, delta] using
              hdelta_nonneg τ (by simpa [a, b] using hτ)))
  have hk_nonneg : ∀ τ ∈ Icc a b, 0 ≤ k τ := fun τ hτ => (hk_pos τ hτ).le
  have hy_cont : ContinuousOn (fun τ => (sol w).lam v τ) (Icc a b) :=
    ((sol w).cont_lam v).continuousOn
  have hm_cont : ContinuousOn (fun τ => r τ / k τ) (Icc a b) := by
    simpa [a, b, r, k, cr, cg, delta] using
      selectorMU_activeSuffix_qss_continuousOn_of_gap_nonneg
        (sol := sol) boxInputs hκ₀_pos hg₀_nonneg w j c v hdelta_nonneg
  have hmean_cont : Continuous meanGap := by
    simpa [meanGap] using
      continuous_finset_sum Finset.univ (fun x _ =>
        ((sol w).cont_lam x).mul
          ((boxInputs.hP_cont w c).sub (boxInputs.hP_cont w x)))
  have hf_cont : ContinuousOn f (Icc a b) := by
    have hcg_cont : Continuous cg := by simpa [cg] using boxInputs.hcg_cont
    simpa [f] using ((hcg_cont.mul hmean_cont).mul ((sol w).cont_lam v)).continuousOn
  have hy_ode : ∀ τ ∈ Ioo a b,
      HasDerivAt ((sol w).lam v) (k τ * (r τ / k τ - (sol w).lam v τ) + f τ) τ := by
    intro τ hτ
    have hτIcc : τ ∈ Icc a b := ⟨hτ.1.le, hτ.2.le⟩
    have hτ0 : 0 ≤ τ := le_trans ha0 hτIcc.1
    have hδ : 0 ≤ delta τ := by
      simpa [a, b, delta] using hdelta_nonneg τ (by simpa [a, b] using hτIcc)
    simpa [a, b, k, r, f, cr, cg, delta, meanGap] using
      selectorMU_lam_hasDerivAt_forcedQSS_of_boxInputs_activeSuffix
        (sol := sol) boxInputs hκ₀_pos hg₀_nonneg w j hτ0
        (by simpa [a, b] using hτIcc) c v hδ
  have hstack :=
    stack_write_linear_defect_integral_le_initial_tracking_add_target_deriv_add_forcing_on
      (y := fun τ => (sol w).lam v τ) (k := k) (r := r) (f := f) (m' := m')
      (a := a) (b := b) hab hk_cont hk_nonneg hk_pos hy_cont hm_cont
      hf_cont (by simpa [a, b] using hm'_cont) hy_ode
      (by
        intro τ hτ
        simpa [a, b, r, k, cr, cg, delta] using hm_deriv τ (by simpa [a, b] using hτ))
  simpa [a, b, cr, cg, delta, meanGap, k, r, f] using hstack

/-- Fixed-coordinate active λ-defect estimate with the concrete QSS derivative
RHS discharged. -/
theorem selectorMU_activeSuffix_lam_defect_integral_le_initial_activeQSS_tracking_add_activeQSSDeriv_add_meanGap_forcing_of_boxInputs
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c v : UniversalLocalView)
    (hdelta_nonneg :
      ∀ τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
        0 ≤ universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ)) :
    (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
      |selectorMU_activeCr Mcy κ₀ τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) ≤
      |selectorMU_activeQSS eta heta sol w c v (selectorMUEarlyWriteSubStart j) -
        (sol w).lam v (selectorMUEarlyWriteSubStart j)| +
      (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
      (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|) := by
  have hm'_cont :
      ContinuousOn
        (fun τ : ℝ => selectorMU_activeQSSDerivRHS eta heta sol w c v τ)
        (Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j)) :=
    selectorMU_activeQSSDerivRHS_continuousOn_of_gap_nonneg
      (sol := sol) hκ₀_pos hg₀_nonneg w j c v hdelta_nonneg
  have hm_deriv :
      ∀ τ ∈ Ioo (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j),
        HasDerivAt
          (fun τ =>
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
                (Fintype.card UniversalLocalView : ℝ)⁻¹) /
              ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
                (((1 + Real.sin τ) / 2) ^ Mcy *
                  ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                  (universalPval eta heta c ((sol w).u τ) -
                    universalPval eta heta v ((sol w).u τ))))
          (selectorMU_activeQSSDerivRHS eta heta sol w c v τ) τ := by
    intro τ hτ
    have hτIcc :
        τ ∈ Icc (selectorMUEarlyWriteSubStart j) (selectorMUWriteHoldTime j) :=
      ⟨hτ.1.le, hτ.2.le⟩
    simpa [selectorMU_activeQSS, selectorMU_activeSink, selectorMU_activeCr,
      selectorMU_activeCg] using
      selectorMU_activeQSS_hasDerivAt_of_sol_u_hasDerivAt
        (sol := sol) hκ₀_pos hg₀_nonneg w j c v hτIcc
        (hdelta_nonneg τ hτIcc)
  have hbase :=
    selectorMU_activeSuffix_lam_defect_integral_le_initial_qss_tracking_add_qssDeriv_add_meanGap_forcing_of_boxInputs
      (sol := sol) boxInputs hκ₀_pos hg₀_nonneg w j c v
      (fun τ : ℝ => selectorMU_activeQSSDerivRHS eta heta sol w c v τ)
      hm'_cont hdelta_nonneg hm_deriv
  simpa [selectorMU_activeQSS, selectorMU_activeSink, selectorMU_activeCr,
    selectorMU_activeCg] using hbase

private theorem activeBranchResidual_pointwise_le_unweighted_defect_add_forcing
    {V : Type} [Fintype V]
    (lam gap D defect : V → ℝ) (cg : ℝ)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hcg_nonneg : 0 ≤ cg)
    (hD_le_one : ∀ v : V, D v ≤ 1)
    (hgap_nonneg : ∀ v : V, 0 ≤ gap v) :
    (∑ v : V, D v * |defect v|) +
        cg * (∑ v : V, lam v * gap v) * (∑ v : V, lam v * D v) ≤
      (∑ v : V, |defect v|) +
        (∑ v : V, |cg * (∑ x : V, lam x * gap x) * lam v|) := by
  classical
  let meanGap : ℝ := ∑ v : V, lam v * gap v
  have hmean_nonneg : 0 ≤ meanGap := by
    dsimp [meanGap]
    exact Finset.sum_nonneg (fun v _hv => mul_nonneg (hlam_nonneg v) (hgap_nonneg v))
  have hA_nonneg : 0 ≤ cg * meanGap := mul_nonneg hcg_nonneg hmean_nonneg
  have hdef :
      (∑ v : V, D v * |defect v|) ≤ ∑ v : V, |defect v| := by
    calc
      (∑ v : V, D v * |defect v|)
          ≤ ∑ v : V, 1 * |defect v| := by
              refine Finset.sum_le_sum ?_
              intro v _hv
              exact mul_le_mul_of_nonneg_right (hD_le_one v) (abs_nonneg _)
      _ = ∑ v : V, |defect v| := by simp
  have hDmean_le :
      (∑ v : V, lam v * D v) ≤ ∑ v : V, lam v := by
    calc
      (∑ v : V, lam v * D v)
          ≤ ∑ v : V, lam v * 1 := by
              refine Finset.sum_le_sum ?_
              intro v _hv
              exact mul_le_mul_of_nonneg_left (hD_le_one v) (hlam_nonneg v)
      _ = ∑ v : V, lam v := by simp
  have hforcing_eq :
      (∑ v : V, |cg * meanGap * lam v|) =
        (cg * meanGap) * (∑ v : V, lam v) := by
    calc
      (∑ v : V, |cg * meanGap * lam v|)
          = ∑ v : V, (cg * meanGap) * lam v := by
              refine Finset.sum_congr rfl ?_
              intro v _hv
              rw [abs_of_nonneg (mul_nonneg hA_nonneg (hlam_nonneg v))]
      _ = (cg * meanGap) * (∑ v : V, lam v) := by
              exact (Finset.mul_sum Finset.univ (fun v : V => lam v)
                (cg * meanGap)).symm
  have hforcing :
      cg * meanGap * (∑ v : V, lam v * D v) ≤
        ∑ v : V, |cg * meanGap * lam v| := by
    calc
      cg * meanGap * (∑ v : V, lam v * D v)
          ≤ cg * meanGap * (∑ v : V, lam v) := by
              exact mul_le_mul_of_nonneg_left hDmean_le hA_nonneg
      _ = ∑ v : V, |cg * meanGap * lam v| := by
              rw [hforcing_eq]
  simpa [meanGap] using add_le_add hdef hforcing

private theorem activeBranchResidual_pointwise_le_filtered_defect_add_forcing
    {V : Type} [Fintype V] [DecidableEq V]
    (c : V) (lam gap D defect : V → ℝ) (cg : ℝ)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hcg_nonneg : 0 ≤ cg)
    (hD_le_one : ∀ v : V, D v ≤ 1)
    (hD_self : D c = 0)
    (hgap_nonneg : ∀ v : V, 0 ≤ gap v) :
    (∑ v : V, D v * |defect v|) +
        cg * (∑ v : V, lam v * gap v) * (∑ v : V, lam v * D v) ≤
      (Finset.univ.filter (fun v : V => v ≠ c)).sum
          (fun v => |defect v|) +
        (Finset.univ.filter (fun v : V => v ≠ c)).sum
          (fun v => |cg * (∑ x : V, lam x * gap x) * lam v|) := by
  classical
  let meanGap : ℝ := ∑ v : V, lam v * gap v
  let S : Finset V := Finset.univ.filter (fun v : V => v ≠ c)
  have hmean_nonneg : 0 ≤ meanGap := by
    dsimp [meanGap]
    exact Finset.sum_nonneg (fun v _hv => mul_nonneg (hlam_nonneg v) (hgap_nonneg v))
  have hA_nonneg : 0 ≤ cg * meanGap := mul_nonneg hcg_nonneg hmean_nonneg
  have hdef_if :
      (∑ v : V, D v * |defect v|) ≤
        ∑ v : V, if v = c then 0 else |defect v| := by
    refine Finset.sum_le_sum ?_
    intro v _hv
    by_cases hvc : v = c
    · subst hvc
      simp [hD_self]
    · simpa [hvc] using
        mul_le_mul_of_nonneg_right (hD_le_one v) (abs_nonneg (defect v))
  have hdef_filter :
      (∑ v : V, if v = c then 0 else |defect v|) =
        S.sum (fun v => |defect v|) := by
    dsimp [S]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro v _hv
    by_cases hvc : v = c <;> simp [hvc]
  have hdef :
      (∑ v : V, D v * |defect v|) ≤ S.sum (fun v => |defect v|) :=
    hdef_if.trans_eq hdef_filter
  have hDmean_if :
      (∑ v : V, lam v * D v) ≤
        ∑ v : V, if v = c then 0 else lam v := by
    refine Finset.sum_le_sum ?_
    intro v _hv
    by_cases hvc : v = c
    · subst hvc
      simp [hD_self]
    · simpa [hvc] using
        mul_le_mul_of_nonneg_left (hD_le_one v) (hlam_nonneg v)
  have hDmean_filter :
      (∑ v : V, if v = c then 0 else lam v) =
        S.sum (fun v => lam v) := by
    dsimp [S]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro v _hv
    by_cases hvc : v = c <;> simp [hvc]
  have hDmean_le :
      (∑ v : V, lam v * D v) ≤ S.sum (fun v => lam v) :=
    hDmean_if.trans_eq hDmean_filter
  have hforcing_eq :
      S.sum (fun v => |cg * meanGap * lam v|) =
        (cg * meanGap) * S.sum (fun v => lam v) := by
    calc
      S.sum (fun v => |cg * meanGap * lam v|)
          = S.sum (fun v => (cg * meanGap) * lam v) := by
              refine Finset.sum_congr rfl ?_
              intro v _hv
              rw [abs_of_nonneg (mul_nonneg hA_nonneg (hlam_nonneg v))]
      _ = (cg * meanGap) * S.sum (fun v => lam v) := by
              exact (Finset.mul_sum S (fun v : V => lam v)
                (cg * meanGap)).symm
  have hforcing :
      cg * meanGap * (∑ v : V, lam v * D v) ≤
        S.sum (fun v => |cg * meanGap * lam v|) := by
    calc
      cg * meanGap * (∑ v : V, lam v * D v)
          ≤ cg * meanGap * S.sum (fun v => lam v) := by
              exact mul_le_mul_of_nonneg_left hDmean_le hA_nonneg
      _ = S.sum (fun v => |cg * meanGap * lam v|) := by
              rw [hforcing_eq]
  simpa [meanGap, S] using add_le_add hdef hforcing

/-- Pointwise active branch-residual bound for the halt-target-one orientation,
with the branch residual reduced to unweighted QSS defects plus the mean-gap
forcing surface. -/
theorem selectorMU_activeBranchResidual_pointwise_le_unweighted_defect_add_forcing
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) ≤
      (∑ v : UniversalLocalView,
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (∑ v : UniversalLocalView,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|) := by
  classical
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hcg_nonneg : 0 ≤ selectorMU_activeCg Mcy g₀ τ := by
    dsimp [selectorMU_activeCg]
    have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
      nlinarith [Real.neg_one_le_sin τ]
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  have hD_le_one : ∀ v : UniversalLocalView,
      BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU ≤ 1 := by
    intro v
    have hc_le_one :
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU ≤ 1 :=
      (branchU_halt_target_mem_Icc c ((sol w).u τ)).2
    have hv_nonneg :
        0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU :=
      (branchU_halt_target_mem_Icc v ((sol w).u τ)).1
    linarith
  exact
    activeBranchResidual_pointwise_le_unweighted_defect_add_forcing
      (V := UniversalLocalView)
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (gap := fun v : UniversalLocalView =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ))
      (D := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
      (defect := fun v : UniversalLocalView =>
        selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ)
      (cg := selectorMU_activeCg Mcy g₀ τ)
      (fun v => hlam_forward w v τ hτ0)
      hcg_nonneg hD_le_one hdelta_nonneg

/-- Pointwise active branch-residual bound for the halt-target-one orientation,
paying only the non-active-view coordinates.  This keeps the cancellation
`D c = 0`, which is essential because the active coordinate has QSS target
`1 / card` rather than mass close to `1`. -/
theorem selectorMU_activeBranchResidual_pointwise_le_filtered_defect_add_forcing
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) ≤
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView,
                (sol w).lam x τ *
                  (universalPval eta heta c ((sol w).u τ) -
                    universalPval eta heta x ((sol w).u τ))) *
              (sol w).lam v τ|) := by
  classical
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hcg_nonneg : 0 ≤ selectorMU_activeCg Mcy g₀ τ := by
    dsimp [selectorMU_activeCg]
    have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
      nlinarith [Real.neg_one_le_sin τ]
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  have hD_le_one : ∀ v : UniversalLocalView,
      BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU ≤ 1 := by
    intro v
    have hc_le_one :
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU ≤ 1 :=
      (branchU_halt_target_mem_Icc c ((sol w).u τ)).2
    have hv_nonneg :
        0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU :=
      (branchU_halt_target_mem_Icc v ((sol w).u τ)).1
    linarith
  exact
    activeBranchResidual_pointwise_le_filtered_defect_add_forcing
      (V := UniversalLocalView)
      c
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (gap := fun v : UniversalLocalView =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ))
      (D := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
      (defect := fun v : UniversalLocalView =>
        selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ)
      (cg := selectorMU_activeCg Mcy g₀ τ)
      (fun v => hlam_forward w v τ hτ0)
      hcg_nonneg hD_le_one (by simp) hdelta_nonneg

/-- Integral form of
`selectorMU_activeBranchResidual_pointwise_le_filtered_defect_add_forcing`.

This is the active-residual reduction that keeps the `v = c` cancellation. -/
theorem selectorMU_activeBranchResidual_integral_le_filtered_defect_add_forcing
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
    let filteredBound : ℝ → ℝ := fun τ =>
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView,
                (sol w).lam x τ *
                  (universalPval eta heta c ((sol w).u τ) -
                    universalPval eta heta x ((sol w).u τ))) *
              (sol w).lam v τ|)
    (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        residualBound τ) ≤
      ∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        filteredBound τ := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let S : Finset UniversalLocalView := Finset.univ.filter (fun v => v ≠ c)
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      (B c τ - B v τ) *
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B c τ - B v τ))
  let filteredBound : ℝ → ℝ := fun τ =>
    S.sum (fun v =>
      |selectorMU_activeCr Mcy κ₀ τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
    S.sum (fun v =>
      |selectorMU_activeCg Mcy g₀ τ *
          (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
          (sol w).lam v τ|)
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold j
  have hE0 : 0 ≤ E := by
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [E] using selectorMUWriteStart_le_earlySubStart j)
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hB : ∀ v : UniversalLocalView, Continuous (B v) := by
    intro v
    simp only [B, BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u haltCoordU)).add continuous_const
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hP c).sub (hP v))
  have hDmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (B c τ - B v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hB c).sub (hB v))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ =>
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
    intro v
    exact ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hresidual_cont : Continuous residualBound := by
    have hbranch : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          (B c τ - B v τ) *
            |selectorMU_activeCr Mcy κ₀ τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
              selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hB c).sub (hB v)).mul (hdefect_cont v)
    exact hbranch.add ((hcg.mul hPmean).mul hDmean)
  have hfiltered_cont : Continuous filteredBound := by
    have hdefSum : Continuous fun τ : ℝ =>
        S.sum (fun v =>
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) := by
      refine continuous_finsetSum S ?_
      intro v _hv
      exact hdefect_cont v
    have hforceSum : Continuous fun τ : ℝ =>
        S.sum (fun v =>
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
              (sol w).lam v τ|) := by
      refine continuous_finsetSum S ?_
      intro v _hv
      exact ((hcg.mul hPmean).mul (hlam v)).abs
    exact hdefSum.add hforceSum
  have hleft_int : IntervalIntegrable residualBound MeasureTheory.volume E H :=
    hresidual_cont.intervalIntegrable E H
  have hright_int : IntervalIntegrable filteredBound MeasureTheory.volume E H :=
    hfiltered_cont.intervalIntegrable E H
  have hpoint : ∀ τ ∈ Set.Icc E H, residualBound τ ≤ filteredBound τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hE0 hτ.1
    have hraw :=
      selectorMU_activeBranchResidual_pointwise_le_filtered_defect_add_forcing
        (sol := sol) boxInputs hg₀_nonneg w hτ0 c
        (hdelta_nonneg τ (by simpa [E, H] using hτ))
    simpa [residualBound, filteredBound, S, P, B] using hraw
  dsimp only
  change
    (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, filteredBound τ
  exact intervalIntegral.integral_mono_on hEH hleft_int hright_int hpoint

/-- Filtered active branch-residual integral controlled by active-QSS tracking
only on the non-active-view coordinates. -/
theorem selectorMU_activeBranchResidual_integral_le_filtered_activeQSS_sums_add_forcing
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let E : ℝ := selectorMUEarlyWriteSubStart j
    let H : ℝ := selectorMUWriteHoldTime j
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
    let forcingInt : UniversalLocalView → ℝ := fun v =>
      ∫ τ in E..H,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|
    (∫ τ in E..H, residualBound τ) ≤
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
            (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
            forcingInt v) +
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v => forcingInt v) := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let S : Finset UniversalLocalView := Finset.univ.filter (fun v => v ≠ c)
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let defectFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCr Mcy κ₀ τ *
        (Fintype.card UniversalLocalView : ℝ)⁻¹ -
      selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|
  let forcingFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCg Mcy g₀ τ *
        (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
        (sol w).lam v τ|
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView, (B c τ - B v τ) * defectFun v τ) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B c τ - B v τ))
  let filteredBound : ℝ → ℝ := fun τ =>
    S.sum (fun v => defectFun v τ) + S.sum (fun v => forcingFun v τ)
  let forcingInt : UniversalLocalView → ℝ := fun v =>
    ∫ τ in E..H, forcingFun v τ
  have hred :
      (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, filteredBound τ := by
    have h :=
      selectorMU_activeBranchResidual_integral_le_filtered_defect_add_forcing
        (sol := sol) boxInputs hg₀_nonneg w j c hdelta_nonneg
    simpa [E, H, residualBound, filteredBound, defectFun, forcingFun,
      forcingInt, S, P, B] using h
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro x _hx
    exact (hlam x).mul ((hP c).sub (hP x))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous (defectFun v) := by
    intro v
    simpa [defectFun] using
      ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hforcing_cont : ∀ v : UniversalLocalView,
      Continuous (forcingFun v) := by
    intro v
    simpa [forcingFun] using ((hcg.mul hPmean).mul (hlam v)).abs
  have hdefSum_int : IntervalIntegrable
      (fun τ : ℝ => S.sum (fun v => defectFun v τ))
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum S
      (fun v _hv => hdefect_cont v)).intervalIntegrable E H
  have hforceSum_int : IntervalIntegrable
      (fun τ : ℝ => S.sum (fun v => forcingFun v τ))
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum S
      (fun v _hv => hforcing_cont v)).intervalIntegrable E H
  have hsplit :
      (∫ τ in E..H, filteredBound τ) =
        (∫ τ in E..H, S.sum (fun v => defectFun v τ)) +
        (∫ τ in E..H, S.sum (fun v => forcingFun v τ)) := by
    dsimp [filteredBound]
    rw [intervalIntegral.integral_add]
    · exact hdefSum_int
    · exact hforceSum_int
  have hdef_split :
      (∫ τ in E..H, S.sum (fun v => defectFun v τ)) =
        S.sum (fun v => ∫ τ in E..H, defectFun v τ) := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hdefect_cont v).intervalIntegrable E H
  have hforce_split :
      (∫ τ in E..H, S.sum (fun v => forcingFun v τ)) =
        S.sum (fun v => ∫ τ in E..H, forcingFun v τ) := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hforcing_cont v).intervalIntegrable E H
  have hdef_le :
      S.sum (fun v => ∫ τ in E..H, defectFun v τ) ≤
        S.sum (fun v =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v) := by
    refine Finset.sum_le_sum ?_
    intro v _hv
    have hv :=
      selectorMU_activeSuffix_lam_defect_integral_le_initial_activeQSS_tracking_add_activeQSSDeriv_add_meanGap_forcing_of_boxInputs
        (sol := sol) boxInputs hκ₀_pos hg₀_nonneg w j c v
        (fun τ hτ => hdelta_nonneg τ hτ v)
    simpa [E, H, defectFun, forcingFun, forcingInt, P] using hv
  calc
    (∫ τ in E..H, residualBound τ)
        ≤ ∫ τ in E..H, filteredBound τ := hred
    _ =
        S.sum (fun v => ∫ τ in E..H, defectFun v τ) +
        S.sum (fun v => ∫ τ in E..H, forcingFun v τ) := by
          rw [hsplit, hdef_split, hforce_split]
    _ ≤
        S.sum (fun v =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v) +
        S.sum (fun v => forcingInt v) := by
          simpa [forcingInt] using
            add_le_add_right hdef_le (S.sum (fun v => forcingInt v))

/-- Integral form of
`selectorMU_activeBranchResidual_pointwise_le_unweighted_defect_add_forcing`.

It reduces the cancellation-preserving branch residual to unweighted QSS defects
plus one copy of the mean-gap forcing surface. -/
theorem selectorMU_activeBranchResidual_integral_le_unweighted_defect_add_forcing
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
    let unweightedBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (∑ v : UniversalLocalView,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|)
    (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        residualBound τ) ≤
      ∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        unweightedBound τ := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      (B c τ - B v τ) *
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B c τ - B v τ))
  let unweightedBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      |selectorMU_activeCr Mcy κ₀ τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (∑ v : UniversalLocalView,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
            (sol w).lam v τ|)
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold j
  have hE0 : 0 ≤ E := by
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [E] using selectorMUWriteStart_le_earlySubStart j)
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hB : ∀ v : UniversalLocalView, Continuous (B v) := by
    intro v
    simp only [B, BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u haltCoordU)).add continuous_const
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hP c).sub (hP v))
  have hDmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (B c τ - B v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hB c).sub (hB v))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ =>
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
    intro v
    exact ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hresidual_cont : Continuous residualBound := by
    have hbranch : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          (B c τ - B v τ) *
            |selectorMU_activeCr Mcy κ₀ τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
              selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hB c).sub (hB v)).mul (hdefect_cont v)
    exact hbranch.add ((hcg.mul hPmean).mul hDmean)
  have hunweighted_cont : Continuous unweightedBound := by
    have hdefSum : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact hdefect_cont v
    have hforceSum : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
              (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hcg.mul hPmean).mul (hlam v)).abs
    exact hdefSum.add hforceSum
  have hleft_int : IntervalIntegrable residualBound MeasureTheory.volume E H :=
    hresidual_cont.intervalIntegrable E H
  have hright_int : IntervalIntegrable unweightedBound MeasureTheory.volume E H :=
    hunweighted_cont.intervalIntegrable E H
  have hpoint : ∀ τ ∈ Set.Icc E H, residualBound τ ≤ unweightedBound τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hE0 hτ.1
    have hraw :=
      selectorMU_activeBranchResidual_pointwise_le_unweighted_defect_add_forcing
        (sol := sol) boxInputs hg₀_nonneg w hτ0 c
        (hdelta_nonneg τ (by simpa [E, H] using hτ))
    simpa [residualBound, unweightedBound, P, B] using hraw
  dsimp only
  change
    (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, unweightedBound τ
  exact intervalIntegral.integral_mono_on hEH hleft_int hright_int hpoint

/-- Active branch-residual integral controlled by per-view active-QSS tracking,
active-QSS derivative, and the mean-gap forcing surface. -/
theorem selectorMU_activeBranchResidual_integral_le_activeQSS_sums_add_forcing
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let E : ℝ := selectorMUEarlyWriteSubStart j
    let H : ℝ := selectorMUWriteHoldTime j
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
    let forcingInt : UniversalLocalView → ℝ := fun v =>
      ∫ τ in E..H,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|
    (∫ τ in E..H, residualBound τ) ≤
      (∑ v : UniversalLocalView,
        (|selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
            (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
            forcingInt v)) +
      ∑ v : UniversalLocalView, forcingInt v := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let defectFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCr Mcy κ₀ τ *
        (Fintype.card UniversalLocalView : ℝ)⁻¹ -
      selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|
  let forcingFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCg Mcy g₀ τ *
        (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
        (sol w).lam v τ|
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView, (B c τ - B v τ) * defectFun v τ) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B c τ - B v τ))
  let unweightedBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView, defectFun v τ) +
      (∑ v : UniversalLocalView, forcingFun v τ)
  let forcingInt : UniversalLocalView → ℝ := fun v =>
    ∫ τ in E..H, forcingFun v τ
  have hred :
      (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, unweightedBound τ := by
    have h :=
      selectorMU_activeBranchResidual_integral_le_unweighted_defect_add_forcing
        (sol := sol) boxInputs hg₀_nonneg w j c hdelta_nonneg
    simpa [E, H, residualBound, unweightedBound, defectFun, forcingFun,
      forcingInt, P, B] using h
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro x _hx
    exact (hlam x).mul ((hP c).sub (hP x))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous (defectFun v) := by
    intro v
    simpa [defectFun] using
      ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hforcing_cont : ∀ v : UniversalLocalView,
      Continuous (forcingFun v) := by
    intro v
    simpa [forcingFun] using ((hcg.mul hPmean).mul (hlam v)).abs
  have hdefSum_int : IntervalIntegrable
      (fun τ : ℝ => ∑ v : UniversalLocalView, defectFun v τ)
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum Finset.univ
      (fun v _hv => hdefect_cont v)).intervalIntegrable E H
  have hforceSum_int : IntervalIntegrable
      (fun τ : ℝ => ∑ v : UniversalLocalView, forcingFun v τ)
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum Finset.univ
      (fun v _hv => hforcing_cont v)).intervalIntegrable E H
  have hsplit :
      (∫ τ in E..H, unweightedBound τ) =
        (∫ τ in E..H, ∑ v : UniversalLocalView, defectFun v τ) +
        (∫ τ in E..H, ∑ v : UniversalLocalView, forcingFun v τ) := by
    dsimp [unweightedBound]
    rw [intervalIntegral.integral_add]
    · exact hdefSum_int
    · exact hforceSum_int
  have hdef_split :
      (∫ τ in E..H, ∑ v : UniversalLocalView, defectFun v τ) =
        ∑ v : UniversalLocalView, ∫ τ in E..H, defectFun v τ := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hdefect_cont v).intervalIntegrable E H
  have hforce_split :
      (∫ τ in E..H, ∑ v : UniversalLocalView, forcingFun v τ) =
        ∑ v : UniversalLocalView, ∫ τ in E..H, forcingFun v τ := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hforcing_cont v).intervalIntegrable E H
  have hdef_le :
      (∑ v : UniversalLocalView, ∫ τ in E..H, defectFun v τ) ≤
        ∑ v : UniversalLocalView,
          (|selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v) := by
    change
      Finset.univ.sum (fun v : UniversalLocalView =>
          ∫ τ in E..H, defectFun v τ) ≤
        Finset.univ.sum (fun v : UniversalLocalView =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v)
    refine Finset.sum_le_sum ?_
    intro v _hv
    have hv :=
      selectorMU_activeSuffix_lam_defect_integral_le_initial_activeQSS_tracking_add_activeQSSDeriv_add_meanGap_forcing_of_boxInputs
        (sol := sol) boxInputs hκ₀_pos hg₀_nonneg w j c v
        (fun τ hτ => hdelta_nonneg τ hτ v)
    simpa [E, H, defectFun, forcingFun, forcingInt, P] using hv
  calc
    (∫ τ in E..H, residualBound τ)
        ≤ ∫ τ in E..H, unweightedBound τ := hred
    _ =
        (∑ v : UniversalLocalView, ∫ τ in E..H, defectFun v τ) +
        (∑ v : UniversalLocalView, ∫ τ in E..H, forcingFun v τ) := by
          rw [hsplit, hdef_split, hforce_split]
    _ ≤
        (∑ v : UniversalLocalView,
          (|selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v)) +
        ∑ v : UniversalLocalView, forcingInt v := by
          simpa [forcingInt] using add_le_add_right hdef_le

/-- Pointwise active branch-residual bound for the halt-target-zero orientation. -/
theorem selectorMU_activeBranchResidual_pointwise_le_unweighted_defect_add_forcing_flip
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)) ≤
      (∑ v : UniversalLocalView,
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (∑ v : UniversalLocalView,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|) := by
  classical
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hcg_nonneg : 0 ≤ selectorMU_activeCg Mcy g₀ τ := by
    dsimp [selectorMU_activeCg]
    have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
      nlinarith [Real.neg_one_le_sin τ]
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  have hD_le_one : ∀ v : UniversalLocalView,
      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU ≤ 1 := by
    intro v
    have hv_le_one :
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU ≤ 1 :=
      (branchU_halt_target_mem_Icc v ((sol w).u τ)).2
    have hc_nonneg :
        0 ≤ BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU :=
      (branchU_halt_target_mem_Icc c ((sol w).u τ)).1
    linarith
  exact
    activeBranchResidual_pointwise_le_unweighted_defect_add_forcing
      (V := UniversalLocalView)
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (gap := fun v : UniversalLocalView =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ))
      (D := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)
      (defect := fun v : UniversalLocalView =>
        selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ)
      (cg := selectorMU_activeCg Mcy g₀ τ)
      (fun v => hlam_forward w v τ hτ0)
      hcg_nonneg hD_le_one hdelta_nonneg

/-- Flipped pointwise active branch-residual bound, paying only the
non-active-view coordinates. -/
theorem selectorMU_activeBranchResidual_pointwise_le_filtered_defect_add_forcing_flip
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)) ≤
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView,
                (sol w).lam x τ *
                  (universalPval eta heta c ((sol w).u τ) -
                    universalPval eta heta x ((sol w).u τ))) *
              (sol w).lam v τ|) := by
  classical
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hcg_nonneg : 0 ≤ selectorMU_activeCg Mcy g₀ τ := by
    dsimp [selectorMU_activeCg]
    have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
      nlinarith [Real.neg_one_le_sin τ]
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  have hD_le_one : ∀ v : UniversalLocalView,
      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU ≤ 1 := by
    intro v
    have hv_le_one :
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU ≤ 1 :=
      (branchU_halt_target_mem_Icc v ((sol w).u τ)).2
    have hc_nonneg :
        0 ≤ BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU :=
      (branchU_halt_target_mem_Icc c ((sol w).u τ)).1
    linarith
  exact
    activeBranchResidual_pointwise_le_filtered_defect_add_forcing
      (V := UniversalLocalView)
      c
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (gap := fun v : UniversalLocalView =>
        universalPval eta heta c ((sol w).u τ) -
          universalPval eta heta v ((sol w).u τ))
      (D := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)
      (defect := fun v : UniversalLocalView =>
        selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ)
      (cg := selectorMU_activeCg Mcy g₀ τ)
      (fun v => hlam_forward w v τ hτ0)
      hcg_nonneg hD_le_one (by simp) hdelta_nonneg

/-- Integral form of the filtered flipped active branch-residual reduction. -/
theorem selectorMU_activeBranchResidual_integral_le_filtered_defect_add_forcing_flip
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))
    let filteredBound : ℝ → ℝ := fun τ =>
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView,
                (sol w).lam x τ *
                  (universalPval eta heta c ((sol w).u τ) -
                    universalPval eta heta x ((sol w).u τ))) *
              (sol w).lam v τ|)
    (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        residualBound τ) ≤
      ∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        filteredBound τ := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let S : Finset UniversalLocalView := Finset.univ.filter (fun v => v ≠ c)
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      (B v τ - B c τ) *
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B v τ - B c τ))
  let filteredBound : ℝ → ℝ := fun τ =>
    S.sum (fun v =>
      |selectorMU_activeCr Mcy κ₀ τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
    S.sum (fun v =>
      |selectorMU_activeCg Mcy g₀ τ *
          (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
          (sol w).lam v τ|)
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold j
  have hE0 : 0 ≤ E := by
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [E] using selectorMUWriteStart_le_earlySubStart j)
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hB : ∀ v : UniversalLocalView, Continuous (B v) := by
    intro v
    simp only [B, BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u haltCoordU)).add continuous_const
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hP c).sub (hP v))
  have hDmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (B v τ - B c τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hB v).sub (hB c))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ =>
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
    intro v
    exact ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hresidual_cont : Continuous residualBound := by
    have hbranch : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          (B v τ - B c τ) *
            |selectorMU_activeCr Mcy κ₀ τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
              selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hB v).sub (hB c)).mul (hdefect_cont v)
    exact hbranch.add ((hcg.mul hPmean).mul hDmean)
  have hfiltered_cont : Continuous filteredBound := by
    have hdefSum : Continuous fun τ : ℝ =>
        S.sum (fun v =>
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) := by
      refine continuous_finsetSum S ?_
      intro v _hv
      exact hdefect_cont v
    have hforceSum : Continuous fun τ : ℝ =>
        S.sum (fun v =>
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
              (sol w).lam v τ|) := by
      refine continuous_finsetSum S ?_
      intro v _hv
      exact ((hcg.mul hPmean).mul (hlam v)).abs
    exact hdefSum.add hforceSum
  have hleft_int : IntervalIntegrable residualBound MeasureTheory.volume E H :=
    hresidual_cont.intervalIntegrable E H
  have hright_int : IntervalIntegrable filteredBound MeasureTheory.volume E H :=
    hfiltered_cont.intervalIntegrable E H
  have hpoint : ∀ τ ∈ Set.Icc E H, residualBound τ ≤ filteredBound τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hE0 hτ.1
    have hraw :=
      selectorMU_activeBranchResidual_pointwise_le_filtered_defect_add_forcing_flip
        (sol := sol) boxInputs hg₀_nonneg w hτ0 c
        (hdelta_nonneg τ (by simpa [E, H] using hτ))
    simpa [residualBound, filteredBound, S, P, B] using hraw
  dsimp only
  change
    (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, filteredBound τ
  exact intervalIntegral.integral_mono_on hEH hleft_int hright_int hpoint

/-- Filtered flipped active branch-residual integral controlled by active-QSS
tracking only on the non-active-view coordinates. -/
theorem selectorMU_activeBranchResidual_integral_le_filtered_activeQSS_sums_add_forcing_flip
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let E : ℝ := selectorMUEarlyWriteSubStart j
    let H : ℝ := selectorMUWriteHoldTime j
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))
    let forcingInt : UniversalLocalView → ℝ := fun v =>
      ∫ τ in E..H,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|
    (∫ τ in E..H, residualBound τ) ≤
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
            (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
            forcingInt v) +
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ c)).sum
        (fun v => forcingInt v) := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let S : Finset UniversalLocalView := Finset.univ.filter (fun v => v ≠ c)
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let defectFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCr Mcy κ₀ τ *
        (Fintype.card UniversalLocalView : ℝ)⁻¹ -
      selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|
  let forcingFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCg Mcy g₀ τ *
        (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
        (sol w).lam v τ|
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView, (B v τ - B c τ) * defectFun v τ) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B v τ - B c τ))
  let filteredBound : ℝ → ℝ := fun τ =>
    S.sum (fun v => defectFun v τ) + S.sum (fun v => forcingFun v τ)
  let forcingInt : UniversalLocalView → ℝ := fun v =>
    ∫ τ in E..H, forcingFun v τ
  have hred :
      (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, filteredBound τ := by
    have h :=
      selectorMU_activeBranchResidual_integral_le_filtered_defect_add_forcing_flip
        (sol := sol) boxInputs hg₀_nonneg w j c hdelta_nonneg
    simpa [E, H, residualBound, filteredBound, defectFun, forcingFun,
      forcingInt, S, P, B] using h
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro x _hx
    exact (hlam x).mul ((hP c).sub (hP x))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous (defectFun v) := by
    intro v
    simpa [defectFun] using
      ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hforcing_cont : ∀ v : UniversalLocalView,
      Continuous (forcingFun v) := by
    intro v
    simpa [forcingFun] using ((hcg.mul hPmean).mul (hlam v)).abs
  have hdefSum_int : IntervalIntegrable
      (fun τ : ℝ => S.sum (fun v => defectFun v τ))
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum S
      (fun v _hv => hdefect_cont v)).intervalIntegrable E H
  have hforceSum_int : IntervalIntegrable
      (fun τ : ℝ => S.sum (fun v => forcingFun v τ))
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum S
      (fun v _hv => hforcing_cont v)).intervalIntegrable E H
  have hsplit :
      (∫ τ in E..H, filteredBound τ) =
        (∫ τ in E..H, S.sum (fun v => defectFun v τ)) +
        (∫ τ in E..H, S.sum (fun v => forcingFun v τ)) := by
    dsimp [filteredBound]
    rw [intervalIntegral.integral_add]
    · exact hdefSum_int
    · exact hforceSum_int
  have hdef_split :
      (∫ τ in E..H, S.sum (fun v => defectFun v τ)) =
        S.sum (fun v => ∫ τ in E..H, defectFun v τ) := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hdefect_cont v).intervalIntegrable E H
  have hforce_split :
      (∫ τ in E..H, S.sum (fun v => forcingFun v τ)) =
        S.sum (fun v => ∫ τ in E..H, forcingFun v τ) := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hforcing_cont v).intervalIntegrable E H
  have hdef_le :
      S.sum (fun v => ∫ τ in E..H, defectFun v τ) ≤
        S.sum (fun v =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v) := by
    refine Finset.sum_le_sum ?_
    intro v _hv
    have hv :=
      selectorMU_activeSuffix_lam_defect_integral_le_initial_activeQSS_tracking_add_activeQSSDeriv_add_meanGap_forcing_of_boxInputs
        (sol := sol) boxInputs hκ₀_pos hg₀_nonneg w j c v
        (fun τ hτ => hdelta_nonneg τ hτ v)
    simpa [E, H, defectFun, forcingFun, forcingInt, P] using hv
  calc
    (∫ τ in E..H, residualBound τ)
        ≤ ∫ τ in E..H, filteredBound τ := hred
    _ =
        S.sum (fun v => ∫ τ in E..H, defectFun v τ) +
        S.sum (fun v => ∫ τ in E..H, forcingFun v τ) := by
          rw [hsplit, hdef_split, hforce_split]
    _ ≤
        S.sum (fun v =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v) +
        S.sum (fun v => forcingInt v) := by
          simpa [forcingInt] using
            add_le_add_right hdef_le (S.sum (fun v => forcingInt v))

/-- Integral form of the flipped active branch-residual reduction. -/
theorem selectorMU_activeBranchResidual_integral_le_unweighted_defect_add_forcing_flip
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))
    let unweightedBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (∑ v : UniversalLocalView,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|)
    (∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        residualBound τ) ≤
      ∫ τ in (selectorMUEarlyWriteSubStart j)..(selectorMUWriteHoldTime j),
        unweightedBound τ := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      (B v τ - B c τ) *
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B v τ - B c τ))
  let unweightedBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      |selectorMU_activeCr Mcy κ₀ τ *
          (Fintype.card UniversalLocalView : ℝ)⁻¹ -
        selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      (∑ v : UniversalLocalView,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
            (sol w).lam v τ|)
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold j
  have hE0 : 0 ≤ E := by
    exact le_trans (selectorMUWriteStartTime_nonneg j)
      (by simpa [E] using selectorMUWriteStart_le_earlySubStart j)
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hB : ∀ v : UniversalLocalView, Continuous (B v) := by
    intro v
    simp only [B, BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u haltCoordU)).add continuous_const
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hP c).sub (hP v))
  have hDmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, (sol w).lam v τ * (B v τ - B c τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hB v).sub (hB c))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ =>
        |selectorMU_activeCr Mcy κ₀ τ *
            (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
    intro v
    exact ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hresidual_cont : Continuous residualBound := by
    have hbranch : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          (B v τ - B c τ) *
            |selectorMU_activeCr Mcy κ₀ τ *
                (Fintype.card UniversalLocalView : ℝ)⁻¹ -
              selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hB v).sub (hB c)).mul (hdefect_cont v)
    exact hbranch.add ((hcg.mul hPmean).mul hDmean)
  have hunweighted_cont : Continuous unweightedBound := by
    have hdefSum : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact hdefect_cont v
    have hforceSum : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          |selectorMU_activeCg Mcy g₀ τ *
              (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
              (sol w).lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hcg.mul hPmean).mul (hlam v)).abs
    exact hdefSum.add hforceSum
  have hleft_int : IntervalIntegrable residualBound MeasureTheory.volume E H :=
    hresidual_cont.intervalIntegrable E H
  have hright_int : IntervalIntegrable unweightedBound MeasureTheory.volume E H :=
    hunweighted_cont.intervalIntegrable E H
  have hpoint : ∀ τ ∈ Set.Icc E H, residualBound τ ≤ unweightedBound τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hE0 hτ.1
    have hraw :=
      selectorMU_activeBranchResidual_pointwise_le_unweighted_defect_add_forcing_flip
        (sol := sol) boxInputs hg₀_nonneg w hτ0 c
        (hdelta_nonneg τ (by simpa [E, H] using hτ))
    simpa [residualBound, unweightedBound, P, B] using hraw
  dsimp only
  change
    (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, unweightedBound τ
  exact intervalIntegral.integral_mono_on hEH hleft_int hright_int hpoint

/-- Flipped active branch-residual integral controlled by per-view active-QSS
tracking, active-QSS derivative, and the mean-gap forcing surface. -/
theorem selectorMU_activeBranchResidual_integral_le_activeQSS_sums_add_forcing_flip
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hκ₀_pos : 0 < (κ₀ : ℝ)) (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart j)
        (selectorMUWriteHoldTime j), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let E : ℝ := selectorMUEarlyWriteSubStart j
    let H : ℝ := selectorMUWriteHoldTime j
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |selectorMU_activeCr Mcy κ₀ τ *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))
    let forcingInt : UniversalLocalView → ℝ := fun v =>
      ∫ τ in E..H,
        |selectorMU_activeCg Mcy g₀ τ *
            (∑ x : UniversalLocalView,
              (sol w).lam x τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta x ((sol w).u τ))) *
            (sol w).lam v τ|
    (∫ τ in E..H, residualBound τ) ≤
      (∑ v : UniversalLocalView,
        (|selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
            (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
            forcingInt v)) +
      ∑ v : UniversalLocalView, forcingInt v := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart j
  let H : ℝ := selectorMUWriteHoldTime j
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let defectFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCr Mcy κ₀ τ *
        (Fintype.card UniversalLocalView : ℝ)⁻¹ -
      selectorMU_activeSink eta heta sol w c v τ * (sol w).lam v τ|
  let forcingFun : UniversalLocalView → ℝ → ℝ := fun v τ =>
    |selectorMU_activeCg Mcy g₀ τ *
        (∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ)) *
        (sol w).lam v τ|
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView, (B v τ - B c τ) * defectFun v τ) +
      selectorMU_activeCg Mcy g₀ τ *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, (sol w).lam v τ * (B v τ - B c τ))
  let unweightedBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView, defectFun v τ) +
      (∑ v : UniversalLocalView, forcingFun v τ)
  let forcingInt : UniversalLocalView → ℝ := fun v =>
    ∫ τ in E..H, forcingFun v τ
  have hred :
      (∫ τ in E..H, residualBound τ) ≤ ∫ τ in E..H, unweightedBound τ := by
    have h :=
      selectorMU_activeBranchResidual_integral_le_unweighted_defect_add_forcing_flip
        (sol := sol) boxInputs hg₀_nonneg w j c hdelta_nonneg
    simpa [E, H, residualBound, unweightedBound, defectFun, forcingFun,
      forcingInt, P, B] using h
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hlam : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => (sol w).lam v τ := by
    intro v
    exact (sol w).cont_lam v
  have hcr : Continuous fun τ : ℝ => selectorMU_activeCr Mcy κ₀ τ :=
    selectorMU_activeCr_continuous Mcy κ₀
  have hcg : Continuous fun τ : ℝ => selectorMU_activeCg Mcy g₀ τ :=
    selectorMU_activeCg_continuous Mcy g₀
  have hsink : ∀ v : UniversalLocalView,
      Continuous fun τ : ℝ => selectorMU_activeSink eta heta sol w c v τ := by
    intro v
    exact selectorMU_activeSink_continuous eta heta sol w c v
  have hPmean : Continuous fun τ : ℝ =>
      ∑ x : UniversalLocalView, (sol w).lam x τ * (P c τ - P x τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro x _hx
    exact (hlam x).mul ((hP c).sub (hP x))
  have hdefect_cont : ∀ v : UniversalLocalView,
      Continuous (defectFun v) := by
    intro v
    simpa [defectFun] using
      ((hcr.mul continuous_const).sub ((hsink v).mul (hlam v))).abs
  have hforcing_cont : ∀ v : UniversalLocalView,
      Continuous (forcingFun v) := by
    intro v
    simpa [forcingFun] using ((hcg.mul hPmean).mul (hlam v)).abs
  have hdefSum_int : IntervalIntegrable
      (fun τ : ℝ => ∑ v : UniversalLocalView, defectFun v τ)
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum Finset.univ
      (fun v _hv => hdefect_cont v)).intervalIntegrable E H
  have hforceSum_int : IntervalIntegrable
      (fun τ : ℝ => ∑ v : UniversalLocalView, forcingFun v τ)
      MeasureTheory.volume E H := by
    exact (continuous_finsetSum Finset.univ
      (fun v _hv => hforcing_cont v)).intervalIntegrable E H
  have hsplit :
      (∫ τ in E..H, unweightedBound τ) =
        (∫ τ in E..H, ∑ v : UniversalLocalView, defectFun v τ) +
        (∫ τ in E..H, ∑ v : UniversalLocalView, forcingFun v τ) := by
    dsimp [unweightedBound]
    rw [intervalIntegral.integral_add]
    · exact hdefSum_int
    · exact hforceSum_int
  have hdef_split :
      (∫ τ in E..H, ∑ v : UniversalLocalView, defectFun v τ) =
        ∑ v : UniversalLocalView, ∫ τ in E..H, defectFun v τ := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hdefect_cont v).intervalIntegrable E H
  have hforce_split :
      (∫ τ in E..H, ∑ v : UniversalLocalView, forcingFun v τ) =
        ∑ v : UniversalLocalView, ∫ τ in E..H, forcingFun v τ := by
    rw [intervalIntegral.integral_finsetSum]
    intro v _hv
    exact (hforcing_cont v).intervalIntegrable E H
  have hdef_le :
      (∑ v : UniversalLocalView, ∫ τ in E..H, defectFun v τ) ≤
        ∑ v : UniversalLocalView,
          (|selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v) := by
    change
      Finset.univ.sum (fun v : UniversalLocalView =>
          ∫ τ in E..H, defectFun v τ) ≤
        Finset.univ.sum (fun v : UniversalLocalView =>
          |selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v)
    refine Finset.sum_le_sum ?_
    intro v _hv
    have hv :=
      selectorMU_activeSuffix_lam_defect_integral_le_initial_activeQSS_tracking_add_activeQSSDeriv_add_meanGap_forcing_of_boxInputs
        (sol := sol) boxInputs hκ₀_pos hg₀_nonneg w j c v
        (fun τ hτ => hdelta_nonneg τ hτ v)
    simpa [E, H, defectFun, forcingFun, forcingInt, P] using hv
  calc
    (∫ τ in E..H, residualBound τ)
        ≤ ∫ τ in E..H, unweightedBound τ := hred
    _ =
        (∑ v : UniversalLocalView, ∫ τ in E..H, defectFun v τ) +
        (∑ v : UniversalLocalView, ∫ τ in E..H, forcingFun v τ) := by
          rw [hsplit, hdef_split, hforce_split]
    _ ≤
        (∑ v : UniversalLocalView,
          (|selectorMU_activeQSS eta heta sol w c v E - (sol w).lam v E| +
              (∫ τ in E..H, |selectorMU_activeQSSDerivRHS eta heta sol w c v τ|) +
              forcingInt v)) +
        ∑ v : UniversalLocalView, forcingInt v := by
          simpa [forcingInt] using add_le_add_right hdef_le

/-- Pointwise active-suffix covariance bound in concrete BGP coordinates.

This is the cancellation-preserving branch-residual surface: the reset and
selection terms are combined before taking absolute values.  The only explicit
mathematical inputs are the active-view orientations for the halt target and
the payoff gap. -/
theorem selectorMU_activeGapCovariance_abs_le_branchResiduals_add_meanGapProduct_of_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView)
    (hD_nonneg : ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
    (hdelta_nonneg : ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    |((((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ)) *
            ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
              ∑ w' : UniversalLocalView,
                (sol w).lam w' τ *
                  (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
      (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView,
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
          ∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))|
      ≤
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
              (sol w).lam v τ|) +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) := by
  classical
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
    nlinarith [Real.neg_one_le_sin τ]
  have hcg_nonneg :
      0 ≤ ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) := by
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  exact
    SelectorDynSol.activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct
      (V := UniversalLocalView)
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (P := fun v : UniversalLocalView =>
        universalPval eta heta v ((sol w).u τ))
      (B := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
      (cr := ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)))
      (c := c)
      (hsum_forward w τ hτ0)
      (fun v => hlam_forward w v τ hτ0)
      hcg_nonneg hD_nonneg hdelta_nonneg

/-- Pointwise active-suffix covariance bound with the halt-branch orientation
flipped.

This is the cancellation-preserving surface needed when the active halt target
is `0`: the nonnegative branch gap is then `B_v - B_c`, not `B_c - B_v`. -/
theorem selectorMU_activeGapCovariance_abs_le_branchResiduals_add_meanGapProduct_flip_of_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView)
    (hD_nonneg : ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)
    (hdelta_nonneg : ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    |((((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ)) *
            ((BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) -
              ∑ w' : UniversalLocalView,
                (sol w).lam w' τ *
                  (BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))) -
      (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView,
              (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)) -
          ∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)))|
      ≤
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
              (sol w).lam v τ|) +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)) := by
  classical
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
    nlinarith [Real.neg_one_le_sin τ]
  have hcg_nonneg :
      0 ≤ ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) := by
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  exact
    SelectorDynSol.activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct_flip
      (V := UniversalLocalView)
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (P := fun v : UniversalLocalView =>
        universalPval eta heta v ((sol w).u τ))
      (B := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
      (cr := ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)))
      (c := c)
      (hsum_forward w τ hτ0)
      (fun v => hlam_forward w v τ hτ0)
      hcg_nonneg hD_nonneg hdelta_nonneg

/-- Pointwise active-suffix covariance bound with the original cap orientation
on the left and flipped branch residuals on the right.

This is the form consumed when the active halt target is `0`: the cap reduction
still presents the active variation with `B_c - B_v`, while the nonnegative
branch residual coordinate is `B_v - B_c`. -/
theorem selectorMU_activeGapCovariance_abs_le_branchResiduals_add_meanGapProduct_flip_original_of_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w : ℕ) {τ : ℝ} (hτ0 : 0 ≤ τ) (c : UniversalLocalView)
    (hD_nonneg : ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)
    (hdelta_nonneg : ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    |((((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ)) *
            ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
              ∑ w' : UniversalLocalView,
                (sol w).lam w' τ *
                  (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
      (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView,
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
          ∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))|
      ≤
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
              (sol w).lam v τ|) +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)) := by
  classical
  have hsum_forward := solMURepl_static_lam_sum_forward (sol := sol) boxInputs
  have hlam_forward := solMURepl_static_lam_nonneg_forward (sol := sol) boxInputs
  have hsin_base_nonneg : 0 ≤ (1 + Real.sin τ) / 2 := by
    nlinarith [Real.neg_one_le_sin τ]
  have hcg_nonneg :
      0 ≤ ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) := by
    exact mul_nonneg (pow_nonneg hsin_base_nonneg Mcy)
      (mul_nonneg hg₀_nonneg (Real.exp_pos _).le)
  exact
    SelectorDynSol.activeCenteredVariation_abs_le_branchResiduals_add_meanGapProduct_flip_original
      (V := UniversalLocalView)
      (lam := fun v : UniversalLocalView => (sol w).lam v τ)
      (P := fun v : UniversalLocalView =>
        universalPval eta heta v ((sol w).u τ))
      (B := fun v : UniversalLocalView =>
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
      (cr := ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ))
      (cg := ((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)))
      (c := c)
      (hsum_forward w τ hτ0)
      (fun v => hlam_forward w v τ hτ0)
      hcg_nonneg hD_nonneg hdelta_nonneg

/-- Integral active-suffix covariance bound in branch-residual coordinates.

This lifts the pointwise cancellation-preserving bound across the active suffix.
The orientation hypotheses remain explicit and pointwise on the suffix. -/
theorem selectorMUHoff_activeGapCovarianceVariation_le_branchResiduals_add_meanGapProduct_of_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hD_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let activeCov : ℝ → ℝ := fun τ =>
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ)) *
            ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
              ∑ w' : UniversalLocalView,
                (sol w).lam w' τ *
                  (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
      (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView,
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
          ∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) *
          |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
              (sol w).lam v τ|) +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)), |activeCov τ|)
      ≤
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)), residualBound τ) := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUWriteHoldTime (j + 1)
  let lam : UniversalLocalView → ℝ → ℝ := fun v τ => (sol w).lam v τ
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let cr : ℝ → ℝ := fun τ => ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  let cg : ℝ → ℝ := fun τ =>
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let activeCov : ℝ → ℝ := fun τ =>
    cg τ *
        (∑ v : UniversalLocalView,
          lam v τ * (P c τ - P v τ) *
            ((B c τ - B v τ) -
              ∑ w' : UniversalLocalView, lam w' τ * (B c τ - B w' τ))) -
      cr τ *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView, (B c τ - B v τ)) -
          ∑ v : UniversalLocalView, lam v τ * (B c τ - B v τ))
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      (B c τ - B v τ) *
        |cr τ * (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          (cr τ + cg τ * (P c τ - P v τ)) * lam v τ|) +
      cg τ *
        (∑ v : UniversalLocalView, lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, lam v τ * (B c τ - B v τ))
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold (j + 1)
  have hE0 : 0 ≤ E := by
    exact le_trans (selectorMUWriteStartTime_nonneg (j + 1))
      (by simpa [E] using selectorMUWriteStart_le_earlySubStart (j + 1))
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hB : ∀ v : UniversalLocalView, Continuous (B v) := by
    intro v
    simp only [B, BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u haltCoordU)).add continuous_const
  have hlam : ∀ v : UniversalLocalView, Continuous (lam v) := by
    intro v
    simpa [lam] using (sol w).cont_lam v
  have hcr : Continuous cr := by
    simpa [cr] using boxInputs.hcr_cont
  have hcg : Continuous cg := by
    simpa [cg] using boxInputs.hcg_cont
  have hDmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, lam v τ * (B c τ - B v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hB c).sub (hB v))
  have hPmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, lam v τ * (P c τ - P v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hP c).sub (hP v))
  have hcovSum : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView,
        lam v τ * (P c τ - P v τ) *
          ((B c τ - B v τ) -
            ∑ w' : UniversalLocalView, lam w' τ * (B c τ - B w' τ)) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact ((hlam v).mul ((hP c).sub (hP v))).mul
      (((hB c).sub (hB v)).sub hDmean)
  have hresetDef : Continuous fun τ : ℝ =>
      ((Fintype.card UniversalLocalView : ℝ)⁻¹ *
          ∑ v : UniversalLocalView, (B c τ - B v τ)) -
        ∑ v : UniversalLocalView, lam v τ * (B c τ - B v τ) := by
    have hDsum : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView, (B c τ - B v τ) := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact (hB c).sub (hB v)
    exact (continuous_const.mul hDsum).sub hDmean
  have hactive_cont : Continuous activeCov := by
    exact (hcg.mul hcovSum).sub (hcr.mul hresetDef)
  have hresidual_cont : Continuous residualBound := by
    have hbranch : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          (B c τ - B v τ) *
            |cr τ * (Fintype.card UniversalLocalView : ℝ)⁻¹ -
              (cr τ + cg τ * (P c τ - P v τ)) * lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hB c).sub (hB v)).mul
        (((hcr.mul continuous_const).sub
          (((hcr.add (hcg.mul ((hP c).sub (hP v)))).mul (hlam v)))).abs)
    exact hbranch.add ((hcg.mul hPmean).mul hDmean)
  have hleft_int : IntervalIntegrable (fun τ => |activeCov τ|)
      MeasureTheory.volume E H :=
    hactive_cont.abs.intervalIntegrable E H
  have hright_int : IntervalIntegrable residualBound MeasureTheory.volume E H :=
    hresidual_cont.intervalIntegrable E H
  have hpoint : ∀ τ ∈ Set.Icc E H, |activeCov τ| ≤ residualBound τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hE0 hτ.1
    have hraw :=
      selectorMU_activeGapCovariance_abs_le_branchResiduals_add_meanGapProduct_of_nonneg
        (sol := sol) boxInputs hg₀_nonneg w hτ0 c
        (hD_nonneg τ (by simpa [E, H] using hτ))
        (hdelta_nonneg τ (by simpa [E, H] using hτ))
    simpa [activeCov, residualBound, lam, P, B, cr, cg] using hraw
  dsimp only
  change
    (∫ τ in E..H, |activeCov τ|) ≤ ∫ τ in E..H, residualBound τ
  exact intervalIntegral.integral_mono_on hEH hleft_int hright_int hpoint

/-- Integral active-suffix covariance bound with flipped branch residuals.

The left-hand active variation keeps the orientation used by the cap theorem
(`B_c - B_v`).  The right-hand residual uses the nonnegative branch coordinate
`B_v - B_c`, which is the available orientation when the active halt target is
`0`. -/
theorem selectorMUHoff_activeGapCovarianceVariation_le_branchResiduals_add_meanGapProduct_flip_original_of_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (hg₀_nonneg : 0 ≤ (g₀ : ℝ))
    (w j : ℕ) (c : UniversalLocalView)
    (hD_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
        BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)
    (hdelta_nonneg : ∀ τ ∈ Set.Icc (selectorMUEarlyWriteSubStart (j + 1))
        (selectorMUWriteHoldTime (j + 1)), ∀ v : UniversalLocalView,
      0 ≤ universalPval eta heta c ((sol w).u τ) -
        universalPval eta heta v ((sol w).u τ)) :
    let activeCov : ℝ → ℝ := fun τ =>
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ)) *
            ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
              ∑ w' : UniversalLocalView,
                (sol w).lam w' τ *
                  (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
      (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView,
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
          ∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU))
    let residualBound : ℝ → ℝ := fun τ =>
      (∑ v : UniversalLocalView,
        (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
          BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU) *
          |(((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (Fintype.card UniversalLocalView : ℝ)⁻¹ -
            ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) +
              (((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ))) *
              (sol w).lam v τ|) +
      (((1 + Real.sin τ) / 2) ^ Mcy *
        ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (universalPval eta heta c ((sol w).u τ) -
              universalPval eta heta v ((sol w).u τ))) *
        (∑ v : UniversalLocalView,
          (sol w).lam v τ *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU))
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)), |activeCov τ|)
      ≤
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)), residualBound τ) := by
  classical
  let E : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let H : ℝ := selectorMUWriteHoldTime (j + 1)
  let lam : UniversalLocalView → ℝ → ℝ := fun v τ => (sol w).lam v τ
  let P : UniversalLocalView → ℝ → ℝ := fun v τ =>
    universalPval eta heta v ((sol w).u τ)
  let B : UniversalLocalView → ℝ → ℝ := fun v τ =>
    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU
  let cr : ℝ → ℝ := fun τ => ((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)
  let cg : ℝ → ℝ := fun τ =>
    ((1 + Real.sin τ) / 2) ^ Mcy *
      ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))
  let activeCov : ℝ → ℝ := fun τ =>
    cg τ *
        (∑ v : UniversalLocalView,
          lam v τ * (P c τ - P v τ) *
            ((B c τ - B v τ) -
              ∑ w' : UniversalLocalView, lam w' τ * (B c τ - B w' τ))) -
      cr τ *
        (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
            ∑ v : UniversalLocalView, (B c τ - B v τ)) -
          ∑ v : UniversalLocalView, lam v τ * (B c τ - B v τ))
  let residualBound : ℝ → ℝ := fun τ =>
    (∑ v : UniversalLocalView,
      (B v τ - B c τ) *
        |cr τ * (Fintype.card UniversalLocalView : ℝ)⁻¹ -
          (cr τ + cg τ * (P c τ - P v τ)) * lam v τ|) +
      cg τ *
        (∑ v : UniversalLocalView, lam v τ * (P c τ - P v τ)) *
        (∑ v : UniversalLocalView, lam v τ * (B v τ - B c τ))
  have hEH : E ≤ H := by
    simpa [E, H] using selectorMUEarlySubStart_le_writeHold (j + 1)
  have hE0 : 0 ≤ E := by
    exact le_trans (selectorMUWriteStartTime_nonneg (j + 1))
      (by simpa [E] using selectorMUWriteStart_le_earlySubStart (j + 1))
  have hP : ∀ v : UniversalLocalView, Continuous (P v) := by
    intro v
    simpa [P] using boxInputs.hP_cont w v
  have hB : ∀ v : UniversalLocalView, Continuous (B v) := by
    intro v
    simp only [B, BranchData.evalBranch, BranchAction.evalReal]
    exact (continuous_const.mul ((sol w).cont_u haltCoordU)).add continuous_const
  have hlam : ∀ v : UniversalLocalView, Continuous (lam v) := by
    intro v
    simpa [lam] using (sol w).cont_lam v
  have hcr : Continuous cr := by
    simpa [cr] using boxInputs.hcr_cont
  have hcg : Continuous cg := by
    simpa [cg] using boxInputs.hcg_cont
  have hDmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, lam v τ * (B c τ - B v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hB c).sub (hB v))
  have hDmeanFlip : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, lam v τ * (B v τ - B c τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hB v).sub (hB c))
  have hPmean : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView, lam v τ * (P c τ - P v τ) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact (hlam v).mul ((hP c).sub (hP v))
  have hcovSum : Continuous fun τ : ℝ =>
      ∑ v : UniversalLocalView,
        lam v τ * (P c τ - P v τ) *
          ((B c τ - B v τ) -
            ∑ w' : UniversalLocalView, lam w' τ * (B c τ - B w' τ)) := by
    refine continuous_finsetSum Finset.univ ?_
    intro v _hv
    exact ((hlam v).mul ((hP c).sub (hP v))).mul
      (((hB c).sub (hB v)).sub hDmean)
  have hresetDef : Continuous fun τ : ℝ =>
      ((Fintype.card UniversalLocalView : ℝ)⁻¹ *
          ∑ v : UniversalLocalView, (B c τ - B v τ)) -
        ∑ v : UniversalLocalView, lam v τ * (B c τ - B v τ) := by
    have hDsum : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView, (B c τ - B v τ) := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact (hB c).sub (hB v)
    exact (continuous_const.mul hDsum).sub hDmean
  have hactive_cont : Continuous activeCov := by
    exact (hcg.mul hcovSum).sub (hcr.mul hresetDef)
  have hresidual_cont : Continuous residualBound := by
    have hbranch : Continuous fun τ : ℝ =>
        ∑ v : UniversalLocalView,
          (B v τ - B c τ) *
            |cr τ * (Fintype.card UniversalLocalView : ℝ)⁻¹ -
              (cr τ + cg τ * (P c τ - P v τ)) * lam v τ| := by
      refine continuous_finsetSum Finset.univ ?_
      intro v _hv
      exact ((hB v).sub (hB c)).mul
        (((hcr.mul continuous_const).sub
          (((hcr.add (hcg.mul ((hP c).sub (hP v)))).mul (hlam v)))).abs)
    exact hbranch.add ((hcg.mul hPmean).mul hDmeanFlip)
  have hleft_int : IntervalIntegrable (fun τ => |activeCov τ|)
      MeasureTheory.volume E H :=
    hactive_cont.abs.intervalIntegrable E H
  have hright_int : IntervalIntegrable residualBound MeasureTheory.volume E H :=
    hresidual_cont.intervalIntegrable E H
  have hpoint : ∀ τ ∈ Set.Icc E H, |activeCov τ| ≤ residualBound τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := le_trans hE0 hτ.1
    have hraw :=
      selectorMU_activeGapCovariance_abs_le_branchResiduals_add_meanGapProduct_flip_original_of_nonneg
        (sol := sol) boxInputs hg₀_nonneg w hτ0 c
        (hD_nonneg τ (by simpa [E, H] using hτ))
        (hdelta_nonneg τ (by simpa [E, H] using hτ))
    simpa [activeCov, residualBound, lam, P, B, cr, cg] using hraw
  dsimp only
  change
    (∫ τ in E..H, |activeCov τ|) ≤ ∫ τ in E..H, residualBound τ
  exact intervalIntegral.integral_mono_on hEH hleft_int hright_int hpoint

theorem selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_concrete_mixTargetVariation
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (w j : ℕ) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffIntegrand sol w τ) ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
        (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) := by
  exact selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_mixTargetDerivRHS
    (sol := sol) w j (selectorMU_mixTargetDerivRHS_continuous (sol := sol) w haltCoordU)

/-- Active right-write suffix cap with the target variation rewritten as the
halt-coordinate centered lambda RHS.  This is the algebraic surface for the
remaining analytic estimate. -/
theorem selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_centered_mixTargetVariation
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) (c : UniversalLocalView) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffIntegrand sol w τ) ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
        (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        abs (∑ v : UniversalLocalView,
          ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
                (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
              ((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
                (sol w).lam v τ *
                  (universalPval eta heta v ((sol w).u τ) -
                    ∑ w' : UniversalLocalView,
                      (sol w).lam w' τ *
                        universalPval eta heta w' ((sol w).u τ))) *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)))) := by
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let b : ℝ := selectorMUWriteHoldTime (j + 1)
  have hbase :=
    selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_concrete_mixTargetVariation
      (sol := sol) w j
  have hvar :
      (∫ τ in a..b,
        |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) =
      (∫ τ in a..b,
        abs (∑ v : UniversalLocalView,
          ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
                (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
              ((1 + Real.sin τ) / 2) ^ Mcy *
                ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
                (sol w).lam v τ *
                  (universalPval eta heta v ((sol w).u τ) -
                    ∑ w' : UniversalLocalView,
                      (sol w).lam w' τ *
                        universalPval eta heta w' ((sol w).u τ))) *
            (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
              BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)))) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hab : a ≤ b := by
      simpa [a, b] using selectorMUEarlySubStart_le_writeHold (j + 1)
    have hτIcc : τ ∈ Set.Icc a b := by
      rwa [uIcc_of_le hab] at hτ
    have ha0 : 0 ≤ a := by
      exact le_trans (selectorMUWriteStartTime_nonneg (j + 1))
        (by simpa [a] using selectorMUWriteStart_le_earlySubStart (j + 1))
    have hτ0 : 0 ≤ τ := le_trans ha0 hτIcc.1
    exact congrArg abs
      (selectorMU_mixTargetDerivRHS_halt_eq_centered_lam_of_boxInputs
        (sol := sol) boxInputs w (τ := τ) hτ0 c)
  calc
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffIntegrand sol w τ)
        ≤ |selectorMixTarget branchU (sol w).u (sol w).lam
              (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
            (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
          (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
              (selectorMUWriteHoldTime (j + 1)),
            |SelectorReplicatorDynSol.mixTargetDerivRHS (sol w) τ haltCoordU|) := hbase
    _ = |selectorMixTarget branchU (sol w).u (sol w).lam
              (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
            (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
          (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
              (selectorMUWriteHoldTime (j + 1)),
            abs (∑ v : UniversalLocalView,
              ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
                    (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
                  ((1 + Real.sin τ) / 2) ^ Mcy *
                    ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
                    (sol w).lam v τ *
                      (universalPval eta heta v ((sol w).u τ) -
                        ∑ w' : UniversalLocalView,
                          (sol w).lam w' τ *
                            universalPval eta heta w' ((sol w).u τ))) *
                (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)))) := by
          rw [hvar]

/-- The centered active-suffix variation equals the cancellation-preserving
gap/reset covariance variation. -/
theorem selectorMUHoff_activeSuffix_centeredVariation_eq_gap_covarianceVariation
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) (c : UniversalLocalView) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs (∑ v : UniversalLocalView,
        ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
              (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
            ((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
              (sol w).lam v τ *
                (universalPval eta heta v ((sol w).u τ) -
                  ∑ w' : UniversalLocalView,
                    (sol w).lam w' τ *
                      universalPval eta heta w' ((sol w).u τ))) *
          (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
            BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)))) =
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      abs ((((1 + Real.sin τ) / 2) ^ Mcy *
          ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
          (∑ v : UniversalLocalView,
            (sol w).lam v τ *
              (universalPval eta heta c ((sol w).u τ) -
                universalPval eta heta v ((sol w).u τ)) *
              ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                ∑ w' : UniversalLocalView,
                  (sol w).lam w' τ *
                    (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
        (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
          (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
              ∑ v : UniversalLocalView,
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
            ∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))) := by
  let a : ℝ := selectorMUEarlyWriteSubStart (j + 1)
  let b : ℝ := selectorMUWriteHoldTime (j + 1)
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hab : a ≤ b := by
    simpa [a, b] using selectorMUEarlySubStart_le_writeHold (j + 1)
  have hτIcc : τ ∈ Set.Icc a b := by
    rwa [uIcc_of_le hab] at hτ
  have ha0 : 0 ≤ a := by
    exact le_trans (selectorMUWriteStartTime_nonneg (j + 1))
      (by simpa [a] using selectorMUWriteStart_le_earlySubStart (j + 1))
  have hτ0 : 0 ≤ τ := le_trans ha0 hτIcc.1
  have hcenter :=
    selectorMU_mixTargetDerivRHS_halt_eq_centered_lam_of_boxInputs
      (sol := sol) boxInputs w (τ := τ) hτ0 c
  have hgap :=
    selectorMU_mixTargetDerivRHS_halt_eq_gap_covariance_sub_reset_defect_of_boxInputs
      (sol := sol) boxInputs w (τ := τ) hτ0 c
  exact congrArg abs (hcenter.symm.trans hgap)

/-- Active right-write suffix cap with the target variation rewritten in
gap/reset covariance coordinates. -/
theorem selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_gap_covarianceVariation
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (w j : ℕ) (c : UniversalLocalView) :
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffIntegrand sol w τ) ≤
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
        (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
      (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
          (selectorMUWriteHoldTime (j + 1)),
        abs ((((1 + Real.sin τ) / 2) ^ Mcy *
            ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
            (∑ v : UniversalLocalView,
              (sol w).lam v τ *
                (universalPval eta heta c ((sol w).u τ) -
                  universalPval eta heta v ((sol w).u τ)) *
                ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                  ∑ w' : UniversalLocalView,
                    (sol w).lam w' τ *
                      (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                        BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
          (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
            (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
                ∑ v : UniversalLocalView,
                  (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
              ∑ v : UniversalLocalView,
                (sol w).lam v τ *
                  (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                    BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))) := by
  have hbase :=
    selectorMUHoff_activeSuffix_integrand_le_initial_tracking_add_centered_mixTargetVariation
      (sol := sol) boxInputs w j c
  have hvar :=
    selectorMUHoff_activeSuffix_centeredVariation_eq_gap_covarianceVariation
      (sol := sol) boxInputs w j c
  calc
    (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
        (selectorMUWriteHoldTime (j + 1)),
      selectorMUHoffIntegrand sol w τ)
        ≤ |selectorMixTarget branchU (sol w).u (sol w).lam
            (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
          (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
          (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
              (selectorMUWriteHoldTime (j + 1)),
            abs (∑ v : UniversalLocalView,
              ((((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ) *
                    (1 / (Fintype.card UniversalLocalView : ℝ) - (sol w).lam v τ) +
                  ((1 + Real.sin τ) / 2) ^ Mcy *
                    ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ)) *
                    (sol w).lam v τ *
                      (universalPval eta heta v ((sol w).u τ) -
                        ∑ w' : UniversalLocalView,
                          (sol w).lam w' τ *
                            universalPval eta heta w' ((sol w).u τ))) *
                (BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU -
                  BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU)))) := hbase
    _ = |selectorMixTarget branchU (sol w).u (sol w).lam
            (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU -
          (sol w).z (selectorMUEarlyWriteSubStart (j + 1)) haltCoordU| +
        (∫ τ in (selectorMUEarlyWriteSubStart (j + 1))..
            (selectorMUWriteHoldTime (j + 1)),
          abs ((((1 + Real.sin τ) / 2) ^ Mcy *
              ((g₀ : ℝ) * Real.exp (bgpParams38.cα * τ))) *
              (∑ v : UniversalLocalView,
                (sol w).lam v τ *
                  (universalPval eta heta c ((sol w).u τ) -
                    universalPval eta heta v ((sol w).u τ)) *
                  ((BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU) -
                    ∑ w' : UniversalLocalView,
                      (sol w).lam w' τ *
                        (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                          BranchData.evalBranch (branchU w') ((sol w).u τ) haltCoordU))) -
            (((1 + Real.cos τ) / 2) ^ Mcy * (κ₀ : ℝ)) *
              (((Fintype.card UniversalLocalView : ℝ)⁻¹ *
                  ∑ v : UniversalLocalView,
                    (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)) -
                ∑ v : UniversalLocalView,
                  (sol w).lam v τ *
                    (BranchData.evalBranch (branchU c) ((sol w).u τ) haltCoordU -
                      BranchData.evalBranch (branchU v) ((sol w).u τ) haltCoordU)))) := by
          rw [hvar]

/-- Partial left field cap bounded by the full left field cap. -/
theorem selectorMUHoff_hcapLeft_of_field_cap
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀} :
    ∀ w j, ∀ t ∈ Icc (selectorMUInterReadStart j) (selectorMUZOffStart j),
      (∫ τ in (selectorMUInterReadStart j)..t,
        selectorMUHoffIntegrand sol w τ) ≤
          selectorMUHoffCapLeftField sol w j := by
  intro w j t ht
  let f : ℝ → ℝ := fun τ => selectorMUHoffIntegrand sol w τ
  have hf_cont : Continuous f := by
    simpa [f] using selectorMUHoffIntegrand_continuous (sol := sol) w
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hI (selectorMUInterReadStart j) t)
    (hI t (selectorMUZOffStart j))
  have htail_nonneg : 0 ≤ ∫ τ in t..selectorMUZOffStart j, f τ := by
    apply intervalIntegral.integral_nonneg ht.2
    intro τ hτ
    exact abs_nonneg _
  change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
    selectorMUHoffCapLeftField sol w j
  unfold selectorMUHoffCapLeftField
  change (∫ τ in (selectorMUInterReadStart j)..t, f τ) ≤
    ∫ τ in (selectorMUInterReadStart j)..(selectorMUZOffStart j), f τ
  linarith

/-- Partial right field cap bounded by the full right field cap. -/
theorem selectorMUHoff_hcapRight_of_field_cap
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀} :
    ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUZOffEnd j) (selectorMUNextWriteStart j),
      (∫ τ in (selectorMUZOffEnd j)..t,
        selectorMUHoffIntegrand sol w τ) ≤
          selectorMUHoffCapRightField sol w j := by
  intro w j _henc_const t ht
  let f : ℝ → ℝ := fun τ => selectorMUHoffIntegrand sol w τ
  have hf_cont : Continuous f := by
    simpa [f] using selectorMUHoffIntegrand_continuous (sol := sol) w
  have hI : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf_cont.intervalIntegrable x y
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hI (selectorMUZOffEnd j) t)
    (hI t (selectorMUNextWriteStart j))
  have htail_nonneg : 0 ≤ ∫ τ in t..selectorMUNextWriteStart j, f τ := by
    apply intervalIntegral.integral_nonneg ht.2
    intro τ hτ
    exact abs_nonneg _
  change (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤
    selectorMUHoffCapRightField sol w j
  unfold selectorMUHoffCapRightField
  change (∫ τ in (selectorMUZOffEnd j)..t, f τ) ≤
    ∫ τ in (selectorMUZOffEnd j)..(selectorMUNextWriteStart j), f τ
  linarith

/-- No-split `hoff` residual with canonical actual field caps.

This is the honest scalar-budget surface: the cap quantities are not arbitrary,
and they are not replaced by the much coarser positive-sine gate integrals. -/
structure SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  env : SelectorMUHoffMiddleEnvelopeResidual
  hsum_le : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j →
    selectorMUHoffCapLeftField sol w j + env.capMid w j +
      selectorMUHoffCapRightField sol w j ≤ selectorReplicatorHoldEnvelope j

namespace SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual

/-- Fill the existing no-split residual from canonical field caps. -/
def toNoSplitResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual sol) :
    SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual sol where
  capLeft := fun w j => selectorMUHoffCapLeftField sol w j
  capRight := fun w j => selectorMUHoffCapRightField sol w j
  env := res.env
  hcapLeft := selectorMUHoff_hcapLeft_of_field_cap
  hcapRight := selectorMUHoff_hcapRight_of_field_cap
  hsum_le := res.hsum_le

end SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual

/-- Box-reduced residual with `p_hoff` replaced by the exact field-integral
producer used by `flag_drift_bound_on_interval_repl`. -/
structure MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)
  δnext : ℕ → ℕ → ℝ
  hδnext : ∀ w, Tendsto (δnext w) atTop (𝓝 0)
  hδnext_nonneg : ∀ w j, 0 ≤ δnext w j
  hoff_integral : SelectorMUHoffFieldIntegralResidual sol
  p_hnextWrite : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j)
      (selectorMUNextRead j),
    |(sol w).z t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δnext w j
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

namespace MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals

/-- Forget the integral-form `hoff` residual to the current box-reduced
interface. -/
def toBoxReducedResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals sol) :
    MUReplicatorSettledHaltBoxReducedResiduals sol where
  hqL_full := res.hqL_full
  hutube_win := res.hutube_win
  δnext := res.δnext
  hδnext := res.hδnext
  hδnext_nonneg := res.hδnext_nonneg
  p_hoff := res.hoff_integral.p_hoff
  p_hnextWrite := res.p_hnextWrite
  p_hloser := res.p_hloser

end MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals

/-- Propagate a halt-coordinate next-write bound over the settled write window
from a small left endpoint and a uniform moving-target bound. -/
theorem solMURepl_nextWrite_window_of_start_and_mix
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (δstart δmix : ℕ → ℕ → ℝ)
    (hstart : ∀ w j,
      |(sol w).z (selectorMUNextWriteStart j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          δstart w j)
    (hmix : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          δmix w j) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          δstart w j + δmix w j := by
  intro w j t ht
  let target : ℝ := stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU
  have hdom_sub : ∀ τ ∈ Icc (selectorMUNextWriteStart j) t,
      τ ∈ selectorSchedule.domain := by
    intro τ hτ
    have hτfull : τ ∈ Icc (selectorMUWriteHoldTime (j + 1))
        (selectorMUWriteReadTime (j + 1)) := by
      simpa [selectorMUNextWriteStart, selectorMUNextRead] using
        (⟨hτ.1, le_trans hτ.2 ht.2⟩ :
          τ ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j))
    exact solMURepl_static_hdom_write w (j + 1) τ hτfull
  have hgZ0_sub : ∀ τ ∈ Icc (selectorMUNextWriteStart j) t,
      0 ≤ bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ := by
    intro τ hτ
    have hτfull : τ ∈ Icc (selectorMUWriteHoldTime (j + 1))
        (selectorMUWriteReadTime (j + 1)) := by
      simpa [selectorMUNextWriteStart, selectorMUNextRead] using
        (⟨hτ.1, le_trans hτ.2 ht.2⟩ :
          τ ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j))
    exact solMURepl_static_hgZ0 sol w (j + 1) τ hτfull
  have hmix_sub : ∀ τ ∈ Icc (selectorMUNextWriteStart j) t,
      |selectorMixTarget branchU (sol w).u (sol w).lam τ haltCoordU - target| ≤
        δmix w j := by
    intro τ hτ
    simpa [target] using hmix w j τ ⟨hτ.1, le_trans hτ.2 ht.2⟩
  have hzh_zero : ∀ τ ∈ Icc t t,
      |(sol w).z τ haltCoordU - (sol w).z t haltCoordU| ≤ (0 : ℝ) := by
    intro τ hτ
    have hτ_eq : τ = t := le_antisymm hτ.2 hτ.1
    simp [hτ_eq]
  have hz_after :=
    z_after_write_bound_repl
      (sol := sol w) (s := haltCoordU)
      (a := selectorMUNextWriteStart j) (m := t) (b := t)
      (M := target) (δw := δmix w j) (δzh := 0)
      ht.1 hdom_sub (solMURepl_static_hgZ_cont sol w) hgZ0_sub
      hmix_sub hzh_zero
  have hz_raw := hz_after t ⟨le_rfl, le_rfl⟩
  have hmass_nonneg :
      0 ≤ ∫ τ in selectorMUNextWriteStart j..t,
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ := by
    apply intervalIntegral.integral_nonneg ht.1
    intro τ hτ
    exact hgZ0_sub τ hτ
  have hexp_le_one :
      Real.exp (-(∫ τ in selectorMUNextWriteStart j..t,
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hterm :
      Real.exp (-(∫ τ in selectorMUNextWriteStart j..t,
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ)) *
        |(sol w).z (selectorMUNextWriteStart j) haltCoordU - target| ≤
          δstart w j := by
    have hmul := mul_le_mul hexp_le_one
      (by simpa [target] using hstart w j) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using hmul
  have hz_target :
      |(sol w).z t haltCoordU - target| ≤ δstart w j + δmix w j := by
    linarith
  simpa [target] using hz_target

/-- Narrower next-write interface: prove only the left endpoint and the moving
selector target, not the whole z trajectory. -/
structure MUReplicatorNextWriteStartMixResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  δstart : ℕ → ℕ → ℝ
  δmix : ℕ → ℕ → ℝ
  hδstart : ∀ w, Tendsto (δstart w) atTop (𝓝 0)
  hδmix : ∀ w, Tendsto (δmix w) atTop (𝓝 0)
  hδstart_nonneg : ∀ w j, 0 ≤ δstart w j
  hδmix_nonneg : ∀ w j, 0 ≤ δmix w j
  p_hnextStart : ∀ w j,
    |(sol w).z (selectorMUNextWriteStart j) haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δstart w j
  p_hnextMix : ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
    |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δmix w j

namespace MUReplicatorNextWriteStartMixResidual

def δnext
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) : ℕ → ℕ → ℝ :=
  fun w j => res.δstart w j + res.δmix w j

theorem hδnext
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) :
    ∀ w, Tendsto (res.δnext w) atTop (𝓝 0) := by
  intro w
  simpa [δnext] using (res.hδstart w).add (res.hδmix w)

theorem hδnext_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) :
    ∀ w j, 0 ≤ res.δnext w j := by
  intro w j
  exact add_nonneg (res.hδstart_nonneg w j) (res.hδmix_nonneg w j)

theorem p_hnextWrite
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartMixResidual sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |(sol w).z t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          res.δnext w j := by
  intro w j t ht
  simpa [δnext] using
    solMURepl_nextWrite_window_of_start_and_mix
      (sol := sol) res.δstart res.δmix res.p_hnextStart res.p_hnextMix w j t ht

end MUReplicatorNextWriteStartMixResidual

/-- Narrowest next-write residual: only the left-endpoint halt-coordinate
bound remains external.  The moving selector-target bound is derived from the
settled concentration residual. -/
structure MUReplicatorNextWriteStartOnlyResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  δstart : ℕ → ℕ → ℝ
  hδstart : ∀ w, Tendsto (δstart w) atTop (𝓝 0)
  hδstart_nonneg : ∀ w j, 0 ≤ δstart w j
  p_hnextStart : ∀ w j,
    |(sol w).z (selectorMUNextWriteStart j) haltCoordU -
      stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
        δstart w j

/-- Next-write start residual generated from a halt-exact write-reach endpoint
at `selectorMUWriteHoldTime`.

The fields are exactly the endpoint theorem inputs, indexed by word `w` and
cycle `j`.  No concentration, stability, or integral premise is manufactured:
all such analytic facts are carried explicitly. -/
structure MUReplicatorNextWriteStartWriteReachResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  a : ℕ → ℕ → ℝ
  θ : ℕ → ℕ → ℝ
  Λ : ℕ → ℕ → ℝ
  Bz0 : ℕ → ℕ → ℝ
  δw : ℕ → ℕ → ℝ
  εmix : ℕ → ℕ → ℝ
  hwrite_le : ∀ w j, a w j ≤ selectorMUWriteHoldTime j
  hdom_write : ∀ w j, ∀ t ∈ Icc (a w j) (selectorMUWriteHoldTime j),
    t ∈ selectorSchedule.domain
  hgZ_cont : ∀ w, Continuous fun t : ℝ =>
    bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hgZ0 : ∀ w j, ∀ t ∈ Icc (a w j) (selectorMUWriteHoldTime j),
    0 ≤ bgpParams38.A * (sol w).α t * bGateZ bgpParams38.L ((sol w).μ t) t
  hmix_stable_z_write : ∀ w j,
    ∀ t ∈ Icc (a w j) (selectorMUWriteHoldTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam (θ w j) haltCoordU| ≤ δw w j
  hz_start_mismatch_bound : ∀ w j,
    |(sol w).z (a w j) haltCoordU -
      selectorMixTarget branchU (sol w).u (sol w).lam (θ w j) haltCoordU| ≤ Bz0 w j
  hwriteInt_lbd_z : ∀ w j,
    Λ w j ≤ ∫ τ in (a w j)..(selectorMUWriteHoldTime j),
      bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ
  hmix_halt : ∀ w j,
    |selectorMixTarget branchU (sol w).u (sol w).lam (θ w j) haltCoordU -
      BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
        ((sol w).u (θ w j)) haltCoordU| ≤ εmix w j
  hwrite_tendsto : ∀ w, Tendsto (fun j =>
    Real.exp (-(Λ w j)) * Bz0 w j) atTop (𝓝 0)
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hεmix : ∀ w, Tendsto (εmix w) atTop (𝓝 0)
  hBz0_nonneg : ∀ w j, 0 ≤ Bz0 w j
  hδw_nonneg : ∀ w j, 0 ≤ δw w j
  hεmix_nonneg : ∀ w j, 0 ≤ εmix w j

namespace MUReplicatorNextWriteStartWriteReachResidual

/-- The start-only radius obtained by applying the write-hold endpoint estimate
to cycle `j + 1`. -/
def δstart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartWriteReachResidual sol) : ℕ → ℕ → ℝ :=
  fun w j =>
    selectorReplicatorHStartRhoHalt (res.Λ w) (res.Bz0 w)
      (res.δw w) (res.εmix w) (j + 1)

theorem hδstart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartWriteReachResidual sol) :
    ∀ w, Tendsto (res.δstart w) atTop (𝓝 0) := by
  intro w
  have hbase :
      Tendsto (selectorReplicatorHStartRhoHalt (res.Λ w) (res.Bz0 w)
        (res.δw w) (res.εmix w)) atTop (𝓝 0) :=
    selectorReplicatorHStartRhoHalt_tendsto_zero
      (res.hwrite_tendsto w) (res.hδw w) (res.hεmix w)
  simpa [δstart] using hbase.comp (Filter.tendsto_add_atTop_nat 1)

theorem hδstart_nonneg
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartWriteReachResidual sol) :
    ∀ w j, 0 ≤ res.δstart w j := by
  intro w j
  unfold δstart selectorReplicatorHStartRhoHalt
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (Real.exp_nonneg _) (res.hBz0_nonneg w (j + 1)))
      (res.hδw_nonneg w (j + 1)))
    (res.hεmix_nonneg w (j + 1))

/-- The write-hold endpoint estimate for the next cycle. -/
theorem p_hnextStart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartWriteReachResidual sol) :
    ∀ w j,
      |(sol w).z (selectorMUNextWriteStart j) haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          res.δstart w j := by
  intro w j
  let cfg : ℕ → UConf := fun n => solMUReplStaticCfg w n
  have hcfg_step : ∀ n, cfg (n + 1) = M_U.step (cfg n) := by
    intro n
    dsimp [cfg]
    exact (solMUReplStaticCfg_step w n).symm
  have h :=
    selector_replicator_haltExact_endpoint_of_writeReach
      (sol := sol w) (cfg := cfg) (hcfg_step := hcfg_step)
      (a := res.a w) (m := fun k => selectorMUWriteHoldTime k) (θ := res.θ w)
      (Λ := res.Λ w) (Bz0 := res.Bz0 w)
      (δw := res.δw w) (εmix := res.εmix w)
      (ham := res.hwrite_le w)
      (hdom_write := res.hdom_write w)
      (hgZ_cont := res.hgZ_cont w)
      (hgZ0 := res.hgZ0 w)
      (hmix_stable_z_write := res.hmix_stable_z_write w)
      (hz_start_mismatch_bound := res.hz_start_mismatch_bound w)
      (hwriteInt_lbd_z := res.hwriteInt_lbd_z w)
      (hmix_halt := res.hmix_halt w) (j + 1)
  simpa [δstart, selectorMUNextWriteStart, cfg, Nat.add_assoc] using h

/-- Convert finite-window write-reach endpoint inputs into the start-only
next-write residual by applying the endpoint theorem to cycle `j + 1`. -/
def toStartOnlyResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartWriteReachResidual sol) :
    MUReplicatorNextWriteStartOnlyResidual sol where
  δstart := res.δstart
  hδstart := res.hδstart
  hδstart_nonneg := res.hδstart_nonneg
  p_hnextStart := res.p_hnextStart

end MUReplicatorNextWriteStartWriteReachResidual

/-- The static early z-write lower bound supplies the write-integral field in
the next-start input residual. -/
theorem selectorMU_nextStart_hwriteInt_hold_lbd_z
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) :
    ∀ w j,
      selectorEarlyWriteIntLower j ≤
        ∫ τ in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
          bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ := by
  intro w j
  exact selector_early_writeIntegral_lower_lbd_repl (sol w) j
    solMURepl_static_hdom_nonneg (solMURepl_static_hgZ_cont sol w)

/-- Convenience producer for the next-write-start write-reach residual from
the existing hstart-shaped inputs.

It keeps the old start time and frozen mix sample:
`selectorMUWriteStartTime j` and `selectorMUWriteReadTime j`, but uses the new
endpoint interval only up to `selectorMUWriteHoldTime j`. -/
structure MUReplicatorNextWriteStartFromHStartInputsResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  Bz0 : ℕ → ℕ → ℝ
  Bz0max : ℝ
  δw : ℕ → ℕ → ℝ
  εmix : ℕ → ℕ → ℝ
  hmix_stable_z_write : ∀ w j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteReadTime j) haltCoordU| ≤ δw w j
  hz_start_mismatch_bound : ∀ w j,
    |(sol w).z (selectorMUWriteStartTime j) haltCoordU -
      selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUWriteReadTime j) haltCoordU| ≤ Bz0 w j
  hwriteInt_hold_lbd_z : ∀ w j,
    selectorEarlyWriteIntLower j ≤
      ∫ τ in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ
  hmix_halt : ∀ w j,
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUWriteReadTime j) haltCoordU -
      BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
        ((sol w).u (selectorMUWriteReadTime j)) haltCoordU| ≤ εmix w j
  hBz0_nonneg : ∀ w j, 0 ≤ Bz0 w j
  hBz0_bdd : ∀ w, ∀ᶠ j in atTop, Bz0 w j ≤ Bz0max
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hεmix : ∀ w, Tendsto (εmix w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j, 0 ≤ δw w j
  hεmix_nonneg : ∀ w j, 0 ≤ εmix w j

namespace MUReplicatorNextWriteStartFromHStartInputsResidual

/-- Convert old hstart-shaped fields plus the early write integral lower bound
into the endpoint write-reach residual used by `nextStart`. -/
def toWriteReachResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartFromHStartInputsResidual sol) :
    MUReplicatorNextWriteStartWriteReachResidual sol where
  a := fun _w j => selectorMUWriteStartTime j
  θ := fun _w j => selectorMUWriteReadTime j
  Λ := fun _w j => selectorEarlyWriteIntLower j
  Bz0 := res.Bz0
  δw := res.δw
  εmix := res.εmix
  hwrite_le := by
    intro _w j
    exact selectorMUWriteStart_le_hold j
  hdom_write := selectorMU_hdom_writeHold
  hgZ_cont := by
    intro w
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  hgZ0 := by
    intro w j t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0
  hmix_stable_z_write := by
    intro w j t ht
    exact res.hmix_stable_z_write w j t
      ⟨ht.1, le_trans ht.2 (selectorMUWriteHold_le_read j)⟩
  hz_start_mismatch_bound := by
    intro w j
    exact res.hz_start_mismatch_bound w j
  hwriteInt_lbd_z := by
    intro w j
    exact res.hwriteInt_hold_lbd_z w j
  hmix_halt := by
    intro w j
    exact res.hmix_halt w j
  hwrite_tendsto := by
    intro w
    have hΛ :
        Tendsto ((fun _w j => selectorEarlyWriteIntLower j) w) atTop atTop := by
      simpa using selectorEarlyWriteIntLower_tendsto_atTop
    simpa [selectorZWriteContraction] using
      solMURepl_expNegLambda_Bz0_tendsto_zero
        (Λ := fun _w j => selectorEarlyWriteIntLower j)
        (Bz0 := res.Bz0) w (Bz0max := res.Bz0max) hΛ
        (Filter.Eventually.of_forall (res.hBz0_nonneg w))
        (res.hBz0_bdd w)
  hδw := res.hδw
  hεmix := res.hεmix
  hBz0_nonneg := res.hBz0_nonneg
  hδw_nonneg := res.hδw_nonneg
  hεmix_nonneg := res.hεmix_nonneg

/-- Directly produce the current start-only residual. -/
def toStartOnlyResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartFromHStartInputsResidual sol) :
    MUReplicatorNextWriteStartOnlyResidual sol :=
  res.toWriteReachResidual.toStartOnlyResidual

end MUReplicatorNextWriteStartFromHStartInputsResidual

/-- Next-start inputs with the static early-write integral lower bound removed
from the external surface. -/
structure MUReplicatorNextWriteStartStaticWriteIntResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  Bz0 : ℕ → ℕ → ℝ
  Bz0max : ℝ
  δw : ℕ → ℕ → ℝ
  εmix : ℕ → ℕ → ℝ
  hmix_stable_z_write : ∀ w j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteReadTime j) haltCoordU| ≤ δw w j
  hz_start_mismatch_bound : ∀ w j,
    |(sol w).z (selectorMUWriteStartTime j) haltCoordU -
      selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUWriteReadTime j) haltCoordU| ≤ Bz0 w j
  hmix_halt : ∀ w j,
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUWriteReadTime j) haltCoordU -
      BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
        ((sol w).u (selectorMUWriteReadTime j)) haltCoordU| ≤ εmix w j
  hBz0_nonneg : ∀ w j, 0 ≤ Bz0 w j
  hBz0_bdd : ∀ w, ∀ᶠ j in atTop, Bz0 w j ≤ Bz0max
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hεmix : ∀ w, Tendsto (εmix w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j, 0 ≤ δw w j
  hεmix_nonneg : ∀ w j, 0 ≤ εmix w j

namespace MUReplicatorNextWriteStartStaticWriteIntResidual

/-- Fill the hstart-shaped next-start residual using the static early write
integral lower bound. -/
def toHStartInputsResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartStaticWriteIntResidual sol) :
    MUReplicatorNextWriteStartFromHStartInputsResidual sol where
  Bz0 := res.Bz0
  Bz0max := res.Bz0max
  δw := res.δw
  εmix := res.εmix
  hmix_stable_z_write := res.hmix_stable_z_write
  hz_start_mismatch_bound := res.hz_start_mismatch_bound
  hwriteInt_hold_lbd_z := selectorMU_nextStart_hwriteInt_hold_lbd_z _
  hmix_halt := res.hmix_halt
  hBz0_nonneg := res.hBz0_nonneg
  hBz0_bdd := res.hBz0_bdd
  hδw := res.hδw
  hεmix := res.hεmix
  hδw_nonneg := res.hδw_nonneg
  hεmix_nonneg := res.hεmix_nonneg

end MUReplicatorNextWriteStartStaticWriteIntResidual

/-- Static halt-only settled loser-mass radius used by the residual interface. -/
def solMUReplStaticHaltEpsLam
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w j : ℕ) : ℝ :=
  epsLamSettled (V := UniversalLocalView)
    (1 / (Fintype.card UniversalLocalView : ℝ))
    (selectorReplicatorGapVal eta heta)
    (Fintype.card UniversalLocalView : ℝ)
    (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
      Real.exp ((selectorReplicatorGapVal eta heta) *
        ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
        (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
    (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

/-- Static halt-only settled loser-mass radius tends to zero under the same
construction-side assumptions used by the halt settled construction. -/
theorem solMUReplStaticHaltEpsLam_tendsto_zero
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      1 / (Fintype.card UniversalLocalView : ℝ) ≤
        (sol w).lam (localViewU (solMUReplStaticCfg w j)) t)
    (hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
        (selectorMUWriteReadTime j),
      UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)) :
    ∀ w, Tendsto (fun j => solMUReplStaticHaltEpsLam sol w j)
      atTop (𝓝 0) := by
  intro w
  let inputs : SelectorReplicatorHaltConcInputs sol solMUReplStaticCfg :=
    { Lmin := fun _ _ => 1 / (Fintype.card UniversalLocalView : ℝ)
      gap := fun _ _ => selectorReplicatorGapVal eta heta
      R0 := fun _ _ => (Fintype.card UniversalLocalView : ℝ)
      Kreset := fun w j =>
        ∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
          Real.exp ((selectorReplicatorGapVal eta heta) *
            ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
          (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ))
      hLmin_pos := fun _ _ => solMURepl_concLmin_floor
      hqL := hqL_full
      hgap := selector_replicator_hgap_of_utube herr hutube_win
      hRa := fun w j v hv =>
        solMURepl_concR0_card_bound boxInputs w j
          (hqL_full w j _ ⟨le_refl _, selectorMUWriteStart_le_read j⟩) v hv
      hKreset := fun _ _ => le_rfl }
  have h :=
    solMURepl_settled_haltEpsLam_tendsto_zero inputs w hg₀
      (solMURepl_static_hgap0 eta heta herr)
      (by
        filter_upwards [] with j
        exact le_rfl)
      solMURepl_concLmin_floor
      (by
        filter_upwards [] with j
        exact le_rfl)
      (R0max := (Fintype.card UniversalLocalView : ℝ))
      (by
        filter_upwards [] with j
        positivity)
      (by
        filter_upwards [] with j
        exact le_rfl)
      (by
        intro j
        rfl)
      hκ₀_nonneg solMURepl_static_hCratio_nonneg
      (solMURepl_static_hratio_bound hκ₀_nonneg hg₀.le hscale w)
  simpa [inputs, solMUReplStaticHaltEpsLam, solMUReplSettledHaltEpsLam] using h

/-- Next-cycle halt-coordinate moving-target bound from the settled loser-mass
residual on cycle `j + 1`. -/
theorem solMURepl_p_hnextMix_of_p_hloser
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
          solMUReplStaticHaltEpsLam sol w j) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          (Fintype.card UniversalLocalView : ℝ) *
            solMUReplStaticHaltEpsLam sol w (j + 1) := by
  intro w j t ht
  have ht_next : t ∈ Icc (selectorMUWriteHoldTime (j + 1))
      (selectorMUWriteReadTime (j + 1)) := by
    simpa [selectorMUNextWriteStart, selectorMUNextRead] using ht
  have hsum := solMURepl_static_hsum boxInputs w (j + 1) t ht_next
  have hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs w (j + 1) t ht_next
  have hloser_nonneg :
      0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t) := by
    exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
  have heps_nonneg : 0 ≤ solMUReplStaticHaltEpsLam sol w (j + 1) :=
    le_trans hloser_nonneg (p_hloser w (j + 1) t ht_next)
  have hwrong : ∀ v : UniversalLocalView,
      v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
        (sol w).lam v t ≤ solMUReplStaticHaltEpsLam sol w (j + 1) := by
    intro v hv
    have hsingle :
        (sol w).lam v t ≤
          (Finset.univ.filter (fun u : UniversalLocalView =>
            u ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun u => (sol w).lam u t) :=
      Finset.single_le_sum (fun u _hu => hlam_nonneg u) (by simp [hv])
    exact le_trans hsingle (p_hloser w (j + 1) t ht_next)
  have hraw :=
    selectorMixTarget_halt_to_next_of_concentration
      (sol w).u (sol w).lam t (solMUReplStaticCfg w (j + 1))
      heps_nonneg hsum hlam_nonneg hwrong
  simpa [solMUReplStaticHaltEpsLam, solMUReplStaticCfg_step w (j + 1),
    Nat.add_assoc] using hraw

/-- Box-reduced halt residual with `p_hnextWrite` split into a next-write start
bound and a moving-target bound. -/
structure MUReplicatorSettledHaltBoxReducedNextWriteResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  hutube_win : ∀ w j, ∀ t ∈ Set.Ico (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    UTube r_LE_U (solMUReplStaticCfg w j) ((sol w).u t)
  nextWrite : MUReplicatorNextWriteStartMixResidual sol
  p_hoff : ∀ w j, selectorMUHaltEncConstW solMUReplStaticCfg w j → ∀ t ∈
      Icc (selectorMUInterReadStart j)
      (selectorMUNextWriteStart j),
    |(sol w).z t haltCoordU - (sol w).z (selectorMUInterReadStart j) haltCoordU| ≤
      selectorReplicatorHoldEnvelope j
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

namespace MUReplicatorSettledHaltBoxReducedNextWriteResiduals

/-- Forget the split-next-write residual to the existing box-reduced interface. -/
def toBoxReducedResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltBoxReducedNextWriteResiduals sol) :
    MUReplicatorSettledHaltBoxReducedResiduals sol where
  hqL_full := res.hqL_full
  hutube_win := res.hutube_win
  δnext := res.nextWrite.δnext
  hδnext := res.nextWrite.hδnext
  hδnext_nonneg := res.nextWrite.hδnext_nonneg
  p_hoff := res.p_hoff
  p_hnextWrite := res.nextWrite.p_hnextWrite
  p_hloser := res.p_hloser

end MUReplicatorSettledHaltBoxReducedNextWriteResiduals

/-- Combined headline residual after all current non-circular reductions:
box-bounded z-start and finite-prefix hold are discharged, full-window u-tube is
split into prefix plus tail, `hoff` is represented by the true field integral,
and `hnextWrite` is represented by start plus moving-target bounds. -/
structure MUReplicatorSettledHaltThinResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  hoff_integral : SelectorMUHoffFieldIntegralResidual sol
  nextWrite : MUReplicatorNextWriteStartMixResidual sol
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

namespace MUReplicatorSettledHaltThinResiduals

/-- Forget the combined thin residual to the box-reduced/split-u-tube shape. -/
def toBoxReducedSplitUTubeResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinResiduals sol) :
    MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals sol where
  hqL_full := res.hqL_full
  fullUTube := res.fullUTube
  δnext := res.nextWrite.δnext
  hδnext := res.nextWrite.hδnext
  hδnext_nonneg := res.nextWrite.hδnext_nonneg
  p_hoff := res.hoff_integral.p_hoff
  p_hnextWrite := res.nextWrite.p_hnextWrite
  p_hloser := res.p_hloser

/-- Fill the original residual bundle from the combined thin residual and box
inputs. -/
def toSettledHaltResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltResiduals sol :=
  res.toBoxReducedSplitUTubeResiduals.toSettledHaltResiduals boxInputs

end MUReplicatorSettledHaltThinResiduals

/-- Remaining halt-coordinate settled concentration frontier.

This bundles the two concentration facts that are still not discharged by the
current static/ODE plumbing.  The loser-mass field deliberately keeps the
current prefix-reset radius used by `SelectorReplicatorHaltConcInputs`; it is
not replaced by a stronger or different full-window reset coefficient. -/
structure MUReplicatorSettledHaltConcentrationResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLamSettled (V := UniversalLocalView)
          (1 / (Fintype.card UniversalLocalView : ℝ))
          (selectorReplicatorGapVal eta heta)
          (Fintype.card UniversalLocalView : ℝ)
          (∫ t in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
            Real.exp ((selectorReplicatorGapVal eta heta) *
              ((sol w).G t - (sol w).G (selectorMUWriteStartTime j))) *
              (((1 + Real.cos t) / 2) ^ Mcy * (κ₀ : ℝ)))
          (sol w).G (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j)

namespace MUReplicatorSettledHaltConcentrationResiduals

/-- The loser-mass concentration residual implies the next-cycle moving
selector-target bound, with the static halt-only settled radius. -/
theorem p_hnextMix
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (res : MUReplicatorSettledHaltConcentrationResiduals sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          (Fintype.card UniversalLocalView : ℝ) *
            solMUReplStaticHaltEpsLam sol w (j + 1) :=
  solMURepl_p_hnextMix_of_p_hloser boxInputs (by
    intro w j t ht
    simpa [solMUReplStaticHaltEpsLam] using res.p_hloser w j t ht)

end MUReplicatorSettledHaltConcentrationResiduals

/-- Generic halt-coordinate concentration rate.

Unlike `MUReplicatorSettledHaltConcentrationResiduals`, this interface does not
force the loser-mass radius to be the old prefix-reset `epsLamSettled`
expression.  It is the shape needed by routes that prove concentration with a
different, but still vanishing, per-cycle radius. -/
structure MUReplicatorSettledHaltConcentrationRateResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  epsLam : ℕ → ℕ → ℝ
  hqL_full : ∀ w j, ∀ t ∈ Set.Icc (selectorMUWriteStartTime j)
      (selectorMUWriteReadTime j),
    1 / (Fintype.card UniversalLocalView : ℝ) ≤
      (sol w).lam (localViewU (solMUReplStaticCfg w j)) t
  hεLam : ∀ w, Tendsto (epsLam w) atTop (𝓝 0)
  p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
      (selectorMUWriteReadTime j),
    (Finset.univ.filter (fun v : UniversalLocalView =>
      v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
        epsLam w j

def selectorSettledHaltDeltaRate (epsLam : ℕ → ℕ → ℝ) (w j : ℕ) : ℝ :=
  (Fintype.card UniversalLocalView : ℝ) * epsLam w j

/-- Next-cycle moving-target bound from a generic settled loser-mass rate. -/
theorem solMURepl_p_hnextMix_of_loser_rate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    {epsLam : ℕ → ℕ → ℝ}
    (p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
          epsLam w j) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          selectorSettledHaltDeltaRate epsLam w (j + 1) := by
  intro w j t ht
  have ht_next : t ∈ Icc (selectorMUWriteHoldTime (j + 1))
      (selectorMUWriteReadTime (j + 1)) := by
    simpa [selectorMUNextWriteStart, selectorMUNextRead] using ht
  have hsum := solMURepl_static_hsum boxInputs w (j + 1) t ht_next
  have hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs w (j + 1) t ht_next
  have hloser_nonneg :
      0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
          (fun v => (sol w).lam v t) := by
    exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
  have heps_nonneg : 0 ≤ epsLam w (j + 1) :=
    le_trans hloser_nonneg (p_hloser w (j + 1) t ht_next)
  have hwrong : ∀ v : UniversalLocalView,
      v ≠ localViewU (solMUReplStaticCfg w (j + 1)) →
        (sol w).lam v t ≤ epsLam w (j + 1) := by
    intro v hv
    have hsingle :
        (sol w).lam v t ≤
          (Finset.univ.filter (fun u : UniversalLocalView =>
            u ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
              (fun u => (sol w).lam u t) :=
      Finset.single_le_sum (fun u _hu => hlam_nonneg u) (by simp [hv])
    exact le_trans hsingle (p_hloser w (j + 1) t ht_next)
  have hraw :=
    selectorMixTarget_halt_to_next_of_concentration
      (sol w).u (sol w).lam t (solMUReplStaticCfg w (j + 1))
      heps_nonneg hsum hlam_nonneg hwrong
  simpa [selectorSettledHaltDeltaRate, solMUReplStaticCfg_step w (j + 1),
    Nat.add_assoc] using hraw

/-- Same-cycle halt-coordinate mix-to-branch estimate from a generic loser-mass
rate at the frozen hstart sample `selectorMUWriteReadTime j`. -/
theorem solMURepl_hmix_halt_of_loser_rate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    {epsLam : ℕ → ℕ → ℝ}
    (p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
          epsLam w j) :
    ∀ w j,
      |selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteReadTime j) haltCoordU -
        BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
          ((sol w).u (selectorMUWriteReadTime j)) haltCoordU| ≤
            selectorSettledHaltDeltaRate epsLam w j := by
  intro w j
  have ht : selectorMUWriteReadTime j ∈
      Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
    ⟨selectorMUWriteHold_le_read j, le_rfl⟩
  have hsum := solMURepl_static_hsum boxInputs w j (selectorMUWriteReadTime j) ht
  have hlam_nonneg :=
    solMURepl_static_hlam_nonneg boxInputs w j (selectorMUWriteReadTime j) ht
  have hloser_nonneg :
      0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum
          (fun v => (sol w).lam v (selectorMUWriteReadTime j)) := by
    exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
  have heps_nonneg : 0 ≤ epsLam w j :=
    le_trans hloser_nonneg (p_hloser w j (selectorMUWriteReadTime j) ht)
  have hwrong : ∀ v : UniversalLocalView,
      v ≠ localViewU (solMUReplStaticCfg w j) →
        (sol w).lam v (selectorMUWriteReadTime j) ≤ epsLam w j := by
    intro v hv
    have hsingle :
        (sol w).lam v (selectorMUWriteReadTime j) ≤
          (Finset.univ.filter (fun u : UniversalLocalView =>
            u ≠ localViewU (solMUReplStaticCfg w j))).sum
              (fun u => (sol w).lam u (selectorMUWriteReadTime j)) :=
      Finset.single_le_sum (fun u _hu => hlam_nonneg u) (by simp [hv])
    exact le_trans hsingle (p_hloser w j (selectorMUWriteReadTime j) ht)
  have hraw :=
    selectorMixTarget_halt_to_next_of_concentration
      (sol w).u (sol w).lam (selectorMUWriteReadTime j)
      (solMUReplStaticCfg w j) heps_nonneg hsum hlam_nonneg hwrong
  have hexact :=
    branchU_haltCoord_exact_independent (solMUReplStaticCfg w j)
      ((sol w).u (selectorMUWriteReadTime j))
  calc
    |selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUWriteReadTime j) haltCoordU -
      BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
        ((sol w).u (selectorMUWriteReadTime j)) haltCoordU|
        = |selectorMixTarget branchU (sol w).u (sol w).lam
            (selectorMUWriteReadTime j) haltCoordU -
          stackMachineEncodingU.enc (M_U.step (solMUReplStaticCfg w j)) haltCoordU| := by
      rw [hexact]
    _ ≤ selectorSettledHaltDeltaRate epsLam w j := by
      simpa [selectorSettledHaltDeltaRate] using hraw

/-- Same-cycle halt-coordinate mix-to-branch estimate from a generic loser-mass
rate, at any settled-window time. -/
theorem solMURepl_hmix_halt_on_settled_of_loser_rate
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    {epsLam : ℕ → ℕ → ℝ}
    (p_hloser : ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
      (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) ≤
          epsLam w j) :
    ∀ w j, ∀ t ∈ Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
          ((sol w).u t) haltCoordU| ≤ selectorSettledHaltDeltaRate epsLam w j := by
  intro w j t ht
  have hsum := solMURepl_static_hsum boxInputs w j t ht
  have hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs w j t ht
  have hloser_nonneg :
      0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
        v ≠ localViewU (solMUReplStaticCfg w j))).sum (fun v => (sol w).lam v t) := by
    exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
  have heps_nonneg : 0 ≤ epsLam w j :=
    le_trans hloser_nonneg (p_hloser w j t ht)
  have hwrong : ∀ v : UniversalLocalView,
      v ≠ localViewU (solMUReplStaticCfg w j) → (sol w).lam v t ≤ epsLam w j := by
    intro v hv
    have hsingle :
        (sol w).lam v t ≤
          (Finset.univ.filter (fun u : UniversalLocalView =>
            u ≠ localViewU (solMUReplStaticCfg w j))).sum (fun u => (sol w).lam u t) :=
      Finset.single_le_sum (fun u _hu => hlam_nonneg u) (by simp [hv])
    exact le_trans hsingle (p_hloser w j t ht)
  have hraw :=
    selectorMixTarget_halt_to_next_of_concentration
      (sol w).u (sol w).lam t (solMUReplStaticCfg w j)
      heps_nonneg hsum hlam_nonneg hwrong
  have hexact :=
    branchU_haltCoord_exact_independent (solMUReplStaticCfg w j) ((sol w).u t)
  calc
    |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
      BranchData.evalBranch (branchU (localViewU (solMUReplStaticCfg w j)))
        ((sol w).u t) haltCoordU|
        = |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc (M_U.step (solMUReplStaticCfg w j)) haltCoordU| := by
      rw [hexact]
    _ ≤ selectorSettledHaltDeltaRate epsLam w j := by
      simpa [selectorSettledHaltDeltaRate] using hraw

/-- Coarse box bound for the next-start z-start mismatch.  The static early
write integral makes this bounded radius vanish after contraction. -/
theorem MUReplicatorBoxInputs.nextStart_hz_start_mismatch_le_one
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    ∀ w j,
      |(sol w).z (selectorMUWriteStartTime j) haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteReadTime j) haltCoordU| ≤ (1 : ℝ) := by
  intro w j
  have hz := boxInputs.halt_z_mem_Icc w (selectorMUWriteStartTime j)
    (selectorMUWriteStartTime_nonneg j)
  have hread0 : 0 ≤ selectorMUWriteReadTime j :=
    le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_read j)
  have hm := boxInputs.halt_mixTarget_mem_Icc w (selectorMUWriteReadTime j) hread0
  exact abs_sub_le_one_of_unit_interval_pair hz hm

namespace MUReplicatorSettledHaltConcentrationRateResiduals

/-- The generic loser-mass rate implies the next-cycle moving selector-target
bound. -/
theorem p_hnextMix
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (res : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    ∀ w j, ∀ t ∈ Icc (selectorMUNextWriteStart j) (selectorMUNextRead j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 2)) haltCoordU| ≤
          selectorSettledHaltDeltaRate res.epsLam w (j + 1) :=
  solMURepl_p_hnextMix_of_loser_rate boxInputs res.p_hloser

end MUReplicatorSettledHaltConcentrationRateResiduals

/-- Hstart-shaped next-start input residual with the halt-coordinate mix radius
provided by the generic concentration-rate residual. -/
structure MUReplicatorNextWriteStartFromHStartRateInputsResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  Bz0 : ℕ → ℕ → ℝ
  Bz0max : ℝ
  δw : ℕ → ℕ → ℝ
  hmix_stable_z_write : ∀ w j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteReadTime j) haltCoordU| ≤ δw w j
  hz_start_mismatch_bound : ∀ w j,
    |(sol w).z (selectorMUWriteStartTime j) haltCoordU -
      selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUWriteReadTime j) haltCoordU| ≤ Bz0 w j
  hwriteInt_hold_lbd_z : ∀ w j,
    selectorEarlyWriteIntLower j ≤
      ∫ τ in (selectorMUWriteStartTime j)..(selectorMUWriteHoldTime j),
        bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ
  hBz0_nonneg : ∀ w j, 0 ≤ Bz0 w j
  hBz0_bdd : ∀ w, ∀ᶠ j in atTop, Bz0 w j ≤ Bz0max
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j, 0 ≤ δw w j

namespace MUReplicatorNextWriteStartFromHStartRateInputsResidual

/-- Fill the existing hstart-input residual by deriving the halt-coordinate
mix radius from the generic concentration-rate residual. -/
def toHStartInputsResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartFromHStartRateInputsResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    MUReplicatorNextWriteStartFromHStartInputsResidual sol where
  Bz0 := res.Bz0
  Bz0max := res.Bz0max
  δw := res.δw
  εmix := selectorSettledHaltDeltaRate concRate.epsLam
  hmix_stable_z_write := res.hmix_stable_z_write
  hz_start_mismatch_bound := res.hz_start_mismatch_bound
  hwriteInt_hold_lbd_z := res.hwriteInt_hold_lbd_z
  hmix_halt := solMURepl_hmix_halt_of_loser_rate boxInputs concRate.p_hloser
  hBz0_nonneg := res.hBz0_nonneg
  hBz0_bdd := res.hBz0_bdd
  hδw := res.hδw
  hεmix := by
    intro w
    simpa [selectorSettledHaltDeltaRate] using
      Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ)
        (concRate.hεLam w)
  hδw_nonneg := res.hδw_nonneg
  hεmix_nonneg := by
    intro w j
    have ht : selectorMUWriteHoldTime j ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
      ⟨le_rfl, selectorMUWriteHold_le_read j⟩
    have hlam_nonneg :=
      solMURepl_static_hlam_nonneg boxInputs w j (selectorMUWriteHoldTime j) ht
    have hloser_nonneg :
        0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j))).sum
            (fun v => (sol w).lam v (selectorMUWriteHoldTime j)) := by
      exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
    have heps_nonneg : 0 ≤ concRate.epsLam w j :=
      le_trans hloser_nonneg
        (concRate.p_hloser w j (selectorMUWriteHoldTime j) ht)
    exact mul_nonneg (Nat.cast_nonneg _) heps_nonneg

/-- Directly produce the current start-only residual. -/
def toStartOnlyResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartFromHStartRateInputsResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    MUReplicatorNextWriteStartOnlyResidual sol :=
  (res.toHStartInputsResidual boxInputs concRate).toStartOnlyResidual

end MUReplicatorNextWriteStartFromHStartRateInputsResidual

/-- Next-start inputs with both the static early-write integral lower bound and
the halt-coordinate mix radius discharged by existing static/rate adapters. -/
structure MUReplicatorNextWriteStartStaticWriteIntRateResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  Bz0 : ℕ → ℕ → ℝ
  Bz0max : ℝ
  δw : ℕ → ℕ → ℝ
  hmix_stable_z_write : ∀ w j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteReadTime j) haltCoordU| ≤ δw w j
  hz_start_mismatch_bound : ∀ w j,
    |(sol w).z (selectorMUWriteStartTime j) haltCoordU -
      selectorMixTarget branchU (sol w).u (sol w).lam
        (selectorMUWriteReadTime j) haltCoordU| ≤ Bz0 w j
  hBz0_nonneg : ∀ w j, 0 ≤ Bz0 w j
  hBz0_bdd : ∀ w, ∀ᶠ j in atTop, Bz0 w j ≤ Bz0max
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j, 0 ≤ δw w j

namespace MUReplicatorNextWriteStartStaticWriteIntRateResidual

/-- Forget to the rate-input next-start surface by filling the static
early-write integral lower bound. -/
def toRateInputsResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartStaticWriteIntRateResidual sol) :
    MUReplicatorNextWriteStartFromHStartRateInputsResidual sol where
  Bz0 := res.Bz0
  Bz0max := res.Bz0max
  δw := res.δw
  hmix_stable_z_write := res.hmix_stable_z_write
  hz_start_mismatch_bound := res.hz_start_mismatch_bound
  hwriteInt_hold_lbd_z := selectorMU_nextStart_hwriteInt_hold_lbd_z _
  hBz0_nonneg := res.hBz0_nonneg
  hBz0_bdd := res.hBz0_bdd
  hδw := res.hδw
  hδw_nonneg := res.hδw_nonneg

/-- Fill the original hstart-input surface from the combined static/rate
residual. -/
def toHStartInputsResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartStaticWriteIntRateResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    MUReplicatorNextWriteStartFromHStartInputsResidual sol :=
  res.toRateInputsResidual.toHStartInputsResidual boxInputs concRate

end MUReplicatorNextWriteStartStaticWriteIntRateResidual

/-- Next-start residual reduced to the single remaining frozen-mix stability
input.  The z-start mismatch is bounded by the box, the write-integral lower
bound is static, and the halt-mix radius comes from the concentration rate. -/
structure MUReplicatorNextWriteStartStableMixResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  δw : ℕ → ℕ → ℝ
  hmix_stable_z_write : ∀ w j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteReadTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteReadTime j) haltCoordU| ≤ δw w j
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j, 0 ≤ δw w j

namespace MUReplicatorNextWriteStartStableMixResidual

/-- Fill the combined static/rate next-start surface from just the stable-mix
residual and the forward halt-coordinate box. -/
def toStaticWriteIntRateResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartStableMixResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorNextWriteStartStaticWriteIntRateResidual sol where
  Bz0 := fun _w _j => (1 : ℝ)
  Bz0max := (1 : ℝ)
  δw := res.δw
  hmix_stable_z_write := res.hmix_stable_z_write
  hz_start_mismatch_bound := boxInputs.nextStart_hz_start_mismatch_le_one
  hBz0_nonneg := by
    intro w j
    norm_num
  hBz0_bdd := by
    intro w
    filter_upwards [] with j
    exact le_rfl
  hδw := res.hδw
  hδw_nonneg := res.hδw_nonneg

end MUReplicatorNextWriteStartStableMixResidual

/-- Next-start residual with the mix frozen at the actual write-hold endpoint.

This removes the unneeded tail interval from the stability hypothesis and uses
`selectorMUWriteHoldTime j` as the sample consumed by the write-reach endpoint
theorem. -/
structure MUReplicatorNextWriteStartHoldStableMixResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  δw : ℕ → ℕ → ℝ
  hmix_stable_z_write_hold : ∀ w j, ∀ t ∈
    Icc (selectorMUWriteStartTime j) (selectorMUWriteHoldTime j),
      |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
        selectorMixTarget branchU (sol w).u (sol w).lam
          (selectorMUWriteHoldTime j) haltCoordU| ≤ δw w j
  hδw : ∀ w, Tendsto (δw w) atTop (𝓝 0)
  hδw_nonneg : ∀ w j, 0 ≤ δw w j

namespace MUReplicatorNextWriteStartHoldStableMixResidual

/-- Convert the write-hold-frozen stability residual directly to the generic
write-reach endpoint residual. -/
def toWriteReachResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartHoldStableMixResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    MUReplicatorNextWriteStartWriteReachResidual sol where
  a := fun _w j => selectorMUWriteStartTime j
  θ := fun _w j => selectorMUWriteHoldTime j
  Λ := fun _w j => selectorEarlyWriteIntLower j
  Bz0 := fun _w _j => (1 : ℝ)
  δw := res.δw
  εmix := selectorSettledHaltDeltaRate concRate.epsLam
  hwrite_le := by
    intro _w j
    exact selectorMUWriteStart_le_hold j
  hdom_write := selectorMU_hdom_writeHold
  hgZ_cont := by
    intro w
    exact selector_replicator_gateZ_integrand_continuous (sol w)
  hgZ0 := by
    intro w j t ht
    have ht0 : 0 ≤ t := le_trans (selectorMUWriteStartTime_nonneg j) ht.1
    exact selector_replicator_gateZ_integrand_nonneg (sol w)
      selectorSchedule_domain_of_nonneg_structural (by norm_num [bgpParams38]) ht0
  hmix_stable_z_write := res.hmix_stable_z_write_hold
  hz_start_mismatch_bound := by
    intro w j
    have hz := boxInputs.halt_z_mem_Icc w (selectorMUWriteStartTime j)
      (selectorMUWriteStartTime_nonneg j)
    have hhold0 : 0 ≤ selectorMUWriteHoldTime j :=
      le_trans (selectorMUWriteStartTime_nonneg j) (selectorMUWriteStart_le_hold j)
    have hm := boxInputs.halt_mixTarget_mem_Icc w (selectorMUWriteHoldTime j) hhold0
    exact abs_sub_le_one_of_unit_interval_pair hz hm
  hwriteInt_lbd_z := selectorMU_nextStart_hwriteInt_hold_lbd_z sol
  hmix_halt := by
    intro w j
    exact solMURepl_hmix_halt_on_settled_of_loser_rate boxInputs
      concRate.p_hloser w j (selectorMUWriteHoldTime j)
      ⟨le_rfl, selectorMUWriteHold_le_read j⟩
  hwrite_tendsto := by
    intro w
    have hΛ :
        Tendsto ((fun _w j => selectorEarlyWriteIntLower j) w) atTop atTop := by
      simpa using selectorEarlyWriteIntLower_tendsto_atTop
    simpa [selectorZWriteContraction] using
      solMURepl_expNegLambda_Bz0_tendsto_zero
        (Λ := fun _w j => selectorEarlyWriteIntLower j)
        (Bz0 := fun _w _j => (1 : ℝ)) w (Bz0max := (1 : ℝ)) hΛ
        (Filter.Eventually.of_forall (fun _j => by norm_num))
        (Filter.Eventually.of_forall (fun _j => le_rfl))
  hδw := res.hδw
  hεmix := by
    intro w
    simpa [selectorSettledHaltDeltaRate] using
      Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ)
        (concRate.hεLam w)
  hBz0_nonneg := by
    intro _w _j
    norm_num
  hδw_nonneg := res.hδw_nonneg
  hεmix_nonneg := by
    intro w j
    have ht : selectorMUWriteHoldTime j ∈
        Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
      ⟨le_rfl, selectorMUWriteHold_le_read j⟩
    have hlam_nonneg :=
      solMURepl_static_hlam_nonneg boxInputs w j (selectorMUWriteHoldTime j) ht
    have hloser_nonneg :
        0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w j))).sum
            (fun v => (sol w).lam v (selectorMUWriteHoldTime j)) := by
      exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
    have heps_nonneg : 0 ≤ concRate.epsLam w j :=
      le_trans hloser_nonneg
        (concRate.p_hloser w j (selectorMUWriteHoldTime j) ht)
    exact mul_nonneg (Nat.cast_nonneg _) heps_nonneg

/-- Directly produce the start-only residual. -/
def toStartOnlyResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartHoldStableMixResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    MUReplicatorNextWriteStartOnlyResidual sol :=
  (res.toWriteReachResidual boxInputs concRate).toStartOnlyResidual

end MUReplicatorNextWriteStartHoldStableMixResidual

namespace MUReplicatorNextWriteStartOnlyResidual

/-- Fill the start+mix next-write residual from the start-only residual and
the settled concentration frontier. -/
def toStartMixResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartOnlyResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (conc : MUReplicatorSettledHaltConcentrationResiduals sol)
    (fullUTube : SelectorMUWriteFullUTubeResidual sol) :
    MUReplicatorNextWriteStartMixResidual sol where
  δstart := res.δstart
  δmix := fun w j =>
    (Fintype.card UniversalLocalView : ℝ) * solMUReplStaticHaltEpsLam sol w (j + 1)
  hδstart := res.hδstart
  hδmix := by
    intro w
    have heps :=
      solMUReplStaticHaltEpsLam_tendsto_zero
        boxInputs herr hκ₀_nonneg hg₀ hscale conc.hqL_full
        fullUTube.hutube_win w
    have hshift := heps.comp (Filter.tendsto_add_atTop_nat 1)
    simpa using
      Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ) hshift
  hδstart_nonneg := res.hδstart_nonneg
  hδmix_nonneg := by
    intro w j
    have ht_next : selectorMUWriteHoldTime (j + 1) ∈
        Icc (selectorMUWriteHoldTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
      ⟨le_rfl, selectorMUWriteHold_le_read (j + 1)⟩
    have hlam_nonneg :=
      solMURepl_static_hlam_nonneg boxInputs w (j + 1)
        (selectorMUWriteHoldTime (j + 1)) ht_next
    have hloser_nonneg :
        0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v (selectorMUWriteHoldTime (j + 1))) := by
      exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
    have heps_nonneg : 0 ≤ solMUReplStaticHaltEpsLam sol w (j + 1) :=
      le_trans hloser_nonneg (by
        simpa [solMUReplStaticHaltEpsLam] using
          conc.p_hloser w (j + 1) (selectorMUWriteHoldTime (j + 1)) ht_next)
    exact mul_nonneg (by positivity) heps_nonneg
  p_hnextStart := res.p_hnextStart
  p_hnextMix := by
    intro w j t ht
    simpa using
      MUReplicatorSettledHaltConcentrationResiduals.p_hnextMix boxInputs conc w j t ht

end MUReplicatorNextWriteStartOnlyResidual

namespace MUReplicatorNextWriteStartOnlyResidual

/-- Fill the start+mix next-write residual from the start-only residual and a
generic settled concentration rate. -/
def toStartMixRateResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorNextWriteStartOnlyResidual sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (conc : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    MUReplicatorNextWriteStartMixResidual sol where
  δstart := res.δstart
  δmix := fun w j => selectorSettledHaltDeltaRate conc.epsLam w (j + 1)
  hδstart := res.hδstart
  hδmix := by
    intro w
    have hshift := (conc.hεLam w).comp (Filter.tendsto_add_atTop_nat 1)
    simpa [selectorSettledHaltDeltaRate] using
      Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ) hshift
  hδstart_nonneg := res.hδstart_nonneg
  hδmix_nonneg := by
    intro w j
    have ht_next : selectorMUWriteHoldTime (j + 1) ∈
        Icc (selectorMUWriteHoldTime (j + 1))
          (selectorMUWriteReadTime (j + 1)) :=
      ⟨le_rfl, selectorMUWriteHold_le_read (j + 1)⟩
    have hlam_nonneg :=
      solMURepl_static_hlam_nonneg boxInputs w (j + 1)
        (selectorMUWriteHoldTime (j + 1)) ht_next
    have hloser_nonneg :
        0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
          v ≠ localViewU (solMUReplStaticCfg w (j + 1)))).sum
            (fun v => (sol w).lam v (selectorMUWriteHoldTime (j + 1))) := by
      exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
    have heps_nonneg : 0 ≤ conc.epsLam w (j + 1) :=
      le_trans hloser_nonneg
        (conc.p_hloser w (j + 1) (selectorMUWriteHoldTime (j + 1)) ht_next)
    exact mul_nonneg (by positivity) heps_nonneg
  p_hnextStart := res.p_hnextStart
  p_hnextMix := by
    intro w j t ht
    simpa using
      MUReplicatorSettledHaltConcentrationRateResiduals.p_hnextMix
        boxInputs conc w j t ht

end MUReplicatorNextWriteStartOnlyResidual

/-- Gate-mass lower bound used by the generic-rate read-start producer. -/
theorem selectorSettledWriteIntLower_le_gateZ_integral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) :
    ∀ w j,
      selectorSettledWriteIntLower j ≤
        ∫ τ in selectorMUWriteHoldTime j..selectorMUWriteReadTime j,
          bgpParams38.A * (sol w).α τ * bGateZ bgpParams38.L ((sol w).μ τ) τ := by
  intro w j
  have hdom_nonneg := solMURepl_static_hdom_nonneg
  have hgZ_cont := solMURepl_static_hgZ_cont sol w
  have hgZ0 := solMURepl_static_hgZ0 sol
  have hsub := selector_settled_writeIntegral_lower_lbd_repl (sol w) j
    hdom_nonneg hgZ_cont
  have hcont_int : ∀ a b : ℝ,
      IntervalIntegrable
        (fun t : ℝ => bgpParams38.A * (sol w).α t *
          bGateZ bgpParams38.L ((sol w).μ t) t)
        MeasureTheory.volume a b :=
    fun a b => hgZ_cont.intervalIntegrable a b
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont_int (selectorMUWriteHoldTime j) (selectorMUSettledWriteSubEnd j))
    (hcont_int (selectorMUSettledWriteSubEnd j) (selectorMUWriteReadTime j))
  have htail_nonneg :
      0 ≤ ∫ t in selectorMUSettledWriteSubEnd j..selectorMUWriteReadTime j,
          bgpParams38.A * (sol w).α t *
            bGateZ bgpParams38.L ((sol w).μ t) t := by
    apply intervalIntegral.integral_nonneg (selectorMUSettledSubEnd_le_read j)
    intro t ht
    exact hgZ0 w j t
      ⟨le_trans (selectorMUWriteHold_le_settledSubEnd j) ht.1, ht.2⟩
  linarith

/-- Direct read-start residual from a generic settled concentration rate.

This bypasses `MUReplicatorSettledHaltFacts`, whose current public shape fixes
the concentration radius to the prefix-reset `epsLamSettled` expression. -/
def mu_replicator_late_start_read_start_of_rate_concentration_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (conc : MUReplicatorSettledHaltConcentrationRateResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol where
  Bz_read := fun w j =>
    solMUReplSettledRho (fun j => selectorSettledWriteIntLower j)
      (fun _j => (1 : ℝ))
      (selectorSettledHaltDeltaRate conc.epsLam w) j
  hz_read_start := by
    intro w j
    let δ : ℕ → ℝ := selectorSettledHaltDeltaRate conc.epsLam w
    have heps_nonneg : 0 ≤ conc.epsLam w j := by
      have ht : selectorMUWriteHoldTime j ∈
          Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
        ⟨le_rfl, selectorMUWriteHold_le_read j⟩
      have hlam_nonneg :=
        solMURepl_static_hlam_nonneg boxInputs w j (selectorMUWriteHoldTime j) ht
      have hloser_nonneg :
          0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j))).sum
              (fun v => (sol w).lam v (selectorMUWriteHoldTime j)) := by
        exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
      exact le_trans hloser_nonneg
        (conc.p_hloser w j (selectorMUWriteHoldTime j) ht)
    have hmix : ∀ t ∈ Icc (selectorMUWriteHoldTime j)
        (selectorMUWriteReadTime j),
        |selectorMixTarget branchU (sol w).u (sol w).lam t haltCoordU -
          stackMachineEncodingU.enc (solMUReplStaticCfg w (j + 1)) haltCoordU| ≤
            δ j := by
      intro t ht
      have hsum := solMURepl_static_hsum boxInputs w j t ht
      have hlam_nonneg := solMURepl_static_hlam_nonneg boxInputs w j t ht
      have hwrong : ∀ v : UniversalLocalView, v ≠ localViewU (solMUReplStaticCfg w j) →
          (sol w).lam v t ≤ conc.epsLam w j := by
        intro v hv
        have hsingle :
            (sol w).lam v t ≤
              (Finset.univ.filter (fun u : UniversalLocalView =>
                u ≠ localViewU (solMUReplStaticCfg w j))).sum
                  (fun u => (sol w).lam u t) :=
          Finset.single_le_sum (fun u _hu => hlam_nonneg u) (by simp [hv])
        exact le_trans hsingle (conc.p_hloser w j t ht)
      have hraw :=
        selectorMixTarget_halt_to_next_of_concentration
          (sol w).u (sol w).lam t (solMUReplStaticCfg w j)
          heps_nonneg hsum hlam_nonneg hwrong
      simpa [δ, selectorSettledHaltDeltaRate, solMUReplStaticCfg_step w j] using hraw
    have hendpoint :=
      z_write_settled_endpoint (sol w) (fun j => solMUReplStaticCfg w j)
        (fun j => selectorSettledWriteIntLower j) (fun _j => (1 : ℝ)) δ
        j haltCoordU
        (solMURepl_static_hdom_write w j) (solMURepl_static_hgZ_cont sol w)
        (solMURepl_static_hgZ0 sol w j) hmix
        (boxInputs.hz_writeHold_static_next_le_one w j)
        (selectorSettledWriteIntLower_le_gateZ_integral sol w j)
    simpa [δ, solMUReplSettledRho, selectorMUWriteReadTime] using hendpoint
  hBz_read_tendsto := by
    intro w
    have hctr :
        Tendsto
          (fun j : ℕ =>
            selectorZWriteContraction (fun j => selectorSettledWriteIntLower j)
              (fun _j => (1 : ℝ)) j) atTop (𝓝 0) := by
      simpa using
        solMURepl_expNegLambda_Bz0_tendsto_zero
          (Λ := fun _w j => selectorSettledWriteIntLower j)
          (Bz0 := fun _w _j => (1 : ℝ)) (w := 0) (Bz0max := (1 : ℝ))
          (by simpa using selectorSettledWriteIntLower_tendsto_atTop)
          (Filter.Eventually.of_forall (fun _j => by norm_num))
          (Filter.Eventually.of_forall (fun _j => le_rfl))
    have hδ :
        Tendsto (selectorSettledHaltDeltaRate conc.epsLam w) atTop (𝓝 0) := by
      simpa [selectorSettledHaltDeltaRate] using
        Filter.Tendsto.const_mul (Fintype.card UniversalLocalView : ℝ)
          (conc.hεLam w)
    simpa [solMUReplSettledRho, selectorZWriteContraction] using hctr.add hδ
  hBz_read_nonneg := by
    intro w j
    have heps_nonneg : 0 ≤ conc.epsLam w j := by
      have ht : selectorMUWriteHoldTime j ∈
          Icc (selectorMUWriteHoldTime j) (selectorMUWriteReadTime j) :=
        ⟨le_rfl, selectorMUWriteHold_le_read j⟩
      have hlam_nonneg :=
        solMURepl_static_hlam_nonneg boxInputs w j (selectorMUWriteHoldTime j) ht
      have hloser_nonneg :
          0 ≤ (Finset.univ.filter (fun v : UniversalLocalView =>
            v ≠ localViewU (solMUReplStaticCfg w j))).sum
              (fun v => (sol w).lam v (selectorMUWriteHoldTime j)) := by
        exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
      exact le_trans hloser_nonneg
        (conc.p_hloser w j (selectorMUWriteHoldTime j) ht)
    dsimp [solMUReplSettledRho, selectorSettledHaltDeltaRate]
    exact add_nonneg (mul_nonneg (Real.exp_pos _).le (by norm_num))
      (mul_nonneg (Nat.cast_nonneg _) heps_nonneg)


/-- Fully thin residual with the remaining concentration frontier bundled. -/
structure MUReplicatorSettledHaltThinConcentrationResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  conc : MUReplicatorSettledHaltConcentrationResiduals sol
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  hoff_integral : SelectorMUHoffFieldIntegralResidual sol
  nextWrite : MUReplicatorNextWriteStartMixResidual sol

namespace MUReplicatorSettledHaltThinConcentrationResiduals

/-- Forget the bundled-concentration thin residual to the existing thin
residual. -/
def toThinResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinConcentrationResiduals sol) :
    MUReplicatorSettledHaltThinResiduals sol where
  hqL_full := res.conc.hqL_full
  fullUTube := res.fullUTube
  hoff_integral := res.hoff_integral
  nextWrite := res.nextWrite
  p_hloser := res.conc.p_hloser

/-- Fill the original residual bundle from the bundled-concentration thin
residual. -/
def toSettledHaltResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinConcentrationResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltResiduals sol :=
  res.toThinResiduals.toSettledHaltResiduals boxInputs

end MUReplicatorSettledHaltThinConcentrationResiduals

/-- Fully thin residual with only the next-write start bound left external;
the moving selector-target part is derived from concentration. -/
structure MUReplicatorSettledHaltThinStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  conc : MUReplicatorSettledHaltConcentrationResiduals sol
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  hoff_integral : SelectorMUHoffFieldIntegralResidual sol
  nextStart : MUReplicatorNextWriteStartOnlyResidual sol

namespace MUReplicatorSettledHaltThinStartResiduals

/-- Fill the bundled-concentration thin residual from the start-only
next-write interface. -/
def toThinConcentrationResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ)) :
    MUReplicatorSettledHaltThinConcentrationResiduals sol where
  conc := res.conc
  fullUTube := res.fullUTube
  hoff_integral := res.hoff_integral
  nextWrite :=
    res.nextStart.toStartMixResidual boxInputs herr hκ₀_nonneg hg₀ hscale
      res.conc res.fullUTube

end MUReplicatorSettledHaltThinStartResiduals

/-- Fully thin residual where the remaining `nextStart` endpoint is supplied by
halt-exact write-reach data on the next cycle's write-hold endpoint. -/
structure MUReplicatorSettledHaltThinWriteReachStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  conc : MUReplicatorSettledHaltConcentrationResiduals sol
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  hoff_integral : SelectorMUHoffFieldIntegralResidual sol
  nextStartReach : MUReplicatorNextWriteStartWriteReachResidual sol

namespace MUReplicatorSettledHaltThinWriteReachStartResiduals

/-- Forget the write-reach-start residual to the current thin-start interface. -/
def toThinStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinWriteReachStartResiduals sol) :
    MUReplicatorSettledHaltThinStartResiduals sol where
  conc := res.conc
  fullUTube := res.fullUTube
  hoff_integral := res.hoff_integral
  nextStart := res.nextStartReach.toStartOnlyResidual

end MUReplicatorSettledHaltThinWriteReachStartResiduals

/-- Fully thin residual in the current split/start-input shape.

This is the public residual shape after the middle `hoff` interval and the
`nextStart` endpoint have both been reduced to their sharper producer
interfaces. -/
structure MUReplicatorSettledHaltThinSplitStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  conc : MUReplicatorSettledHaltConcentrationResiduals sol
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  hoffSplit : SelectorMUHoffSplitMiddleEnvelopeResidual sol
  nextStartInputs : MUReplicatorNextWriteStartFromHStartInputsResidual sol

namespace MUReplicatorSettledHaltThinSplitStartResiduals

/-- Forget the split/start-input residual to the write-reach-start interface. -/
def toThinWriteReachStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinWriteReachStartResiduals sol where
  conc := res.conc
  fullUTube := res.fullUTube
  hoff_integral := res.hoffSplit.toFieldIntegralResidual boxInputs
  nextStartReach := res.nextStartInputs.toWriteReachResidual

/-- Forget the split/start-input residual directly to the thin-start interface. -/
def toThinStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinStartResiduals sol :=
  (res.toThinWriteReachStartResiduals boxInputs).toThinStartResiduals

end MUReplicatorSettledHaltThinSplitStartResiduals

/-- Fully thin residual in the split/start-input shape with the `hoff`
aggregation bridge derived from phase caps. -/
structure MUReplicatorSettledHaltThinNoSplitStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  conc : MUReplicatorSettledHaltConcentrationResiduals sol
  fullUTube : SelectorMUWriteFullUTubeResidual sol
  hoffNoSplit : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual sol
  nextStartInputs : MUReplicatorNextWriteStartFromHStartInputsResidual sol

namespace MUReplicatorSettledHaltThinNoSplitStartResiduals

/-- Fill the current split/start residual by deriving the `hoff` split
aggregation bridge. -/
def toThinSplitStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinNoSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinSplitStartResiduals sol where
  conc := res.conc
  fullUTube := res.fullUTube
  hoffSplit := res.hoffNoSplit.toSplitMiddleEnvelopeResidual boxInputs
  nextStartInputs := res.nextStartInputs

/-- Forget the no-split/start-input residual directly to the thin-start
interface. -/
def toThinStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinNoSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinStartResiduals sol :=
  (res.toThinSplitStartResiduals boxInputs).toThinStartResiduals boxInputs

end MUReplicatorSettledHaltThinNoSplitStartResiduals

/-- Fully thin residual in the no-split `hoff`/hstart-input shape with a
generic settled concentration rate.

This is the rate-shaped public surface: it does not carry `fullUTube`, and it
does not force loser mass to be bounded by the old fixed `epsLamSettled`
expression. -/
structure MUReplicatorSettledHaltThinRateNoSplitStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffNoSplit : SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual sol
  nextStartInputs : MUReplicatorNextWriteStartFromHStartInputsResidual sol

namespace MUReplicatorSettledHaltThinRateNoSplitStartResiduals

/-- Start-only next-write residual obtained from the hstart-input producer. -/
def nextStartOnly
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateNoSplitStartResiduals sol) :
    MUReplicatorNextWriteStartOnlyResidual sol :=
  res.nextStartInputs.toStartOnlyResidual

/-- Rate-based next-write residual. -/
def nextWrite
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateNoSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorNextWriteStartMixResidual sol :=
  res.nextStartOnly.toStartMixRateResidual boxInputs res.concRate

/-- No-split `hoff` residual converted to the full field-integral residual. -/
def hoffIntegral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateNoSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffFieldIntegralResidual sol :=
  res.hoffNoSplit.toFieldIntegralResidual boxInputs

/-- Generic-rate read-start residual. -/
def lateStart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateNoSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_rate_concentration_residual
    boxInputs res.concRate

/-- Assemble the late-start final data consumed by
`bgp_MU_replicator_settled_late_start`. -/
def toLateStartHaltFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateNoSplitStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorLateStartHaltFacts sol :=
  let nextW := res.nextWrite boxInputs
  let hoff := res.hoffIntegral boxInputs
  { cfg := solMUReplStaticCfg
    hcfg := solMUReplStaticCfg_eq
    readStart := res.lateStart boxInputs
    δnext := nextW.δnext
    holdPrefix := fun _ _ => (1 : ℝ)
    hδnext := nextW.hδnext
    hδnext_nonneg := nextW.hδnext_nonneg
    hholdPrefix_nonneg := by
      intro w j
      norm_num
    hoff := hoff.p_hoff
    hnextWrite := by
      intro w j t ht
      simpa [nextW] using nextW.p_hnextWrite w j t ht
    hfiniteHold := by
      intro w j t ht
      exact boxInputs.hfiniteHold_one w j t ht }

end MUReplicatorSettledHaltThinRateNoSplitStartResiduals

/-- Rate-shaped residual whose `hoff` left/right caps are supplied as z-gate
coefficient integral caps. -/
structure MUReplicatorSettledHaltThinRateGateCapStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffGateCap : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual sol
  nextStartInputs : MUReplicatorNextWriteStartFromHStartInputsResidual sol

namespace MUReplicatorSettledHaltThinRateGateCapStartResiduals

/-- Forget the gate-cap `hoff` input shape to the current rate no-split/start
surface. -/
def toRateNoSplitStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateGateCapStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinRateNoSplitStartResiduals sol where
  concRate := res.concRate
  hoffNoSplit := res.hoffGateCap.toNoSplitResidual boxInputs
  nextStartInputs := res.nextStartInputs

end MUReplicatorSettledHaltThinRateGateCapStartResiduals

/-- Rate-shaped gate-cap residual whose next-start halt-coordinate mix radius is
derived from the same generic concentration-rate residual. -/
structure MUReplicatorSettledHaltThinRateGateCapRateStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffGateCap : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual sol
  nextStartRateInputs : MUReplicatorNextWriteStartFromHStartRateInputsResidual sol

namespace MUReplicatorSettledHaltThinRateGateCapRateStartResiduals

/-- Forget to the current rate/gate-cap/start residual surface. -/
def toRateGateCapStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateGateCapRateStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinRateGateCapStartResiduals sol where
  concRate := res.concRate
  hoffGateCap := res.hoffGateCap
  nextStartInputs :=
    res.nextStartRateInputs.toHStartInputsResidual boxInputs res.concRate

end MUReplicatorSettledHaltThinRateGateCapRateStartResiduals

/-- Rate/gate-cap residual with the static early-write integral lower bound
discharged from the next-start surface. -/
structure MUReplicatorSettledHaltThinRateGateCapStaticWriteIntStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffGateCap : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual sol
  nextStartStatic : MUReplicatorNextWriteStartStaticWriteIntResidual sol

namespace MUReplicatorSettledHaltThinRateGateCapStaticWriteIntStartResiduals

/-- Forget the static-write-integral next-start shape to the current gate-cap
headline surface. -/
def toGateCapStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateGateCapStaticWriteIntStartResiduals sol) :
    MUReplicatorSettledHaltThinRateGateCapStartResiduals sol where
  concRate := res.concRate
  hoffGateCap := res.hoffGateCap
  nextStartInputs := res.nextStartStatic.toHStartInputsResidual

end MUReplicatorSettledHaltThinRateGateCapStaticWriteIntStartResiduals

/-- Rate/gate-cap residual with both static early-write integral and halt-mix
rate adapters applied to the next-start surface. -/
structure MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffGateCap : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual sol
  nextStartStaticRate : MUReplicatorNextWriteStartStaticWriteIntRateResidual sol

namespace MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals

/-- Forget to the rate/gate-cap next-start surface. -/
def toRateGateCapStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals sol) :
    MUReplicatorSettledHaltThinRateGateCapRateStartResiduals sol where
  concRate := res.concRate
  hoffGateCap := res.hoffGateCap
  nextStartRateInputs := res.nextStartStaticRate.toRateInputsResidual

/-- Forget directly to the current gate-cap headline surface. -/
def toGateCapStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinRateGateCapStartResiduals sol :=
  (res.toRateGateCapStartResidual).toRateGateCapStartResidual boxInputs

end MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals

/-- Rate/gate-cap residual whose next-start surface is reduced to the remaining
frozen-mix stability input. -/
structure MUReplicatorSettledHaltThinRateGateCapStableMixStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffGateCap : SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual sol
  nextStartStable : MUReplicatorNextWriteStartStableMixResidual sol

namespace MUReplicatorSettledHaltThinRateGateCapStableMixStartResiduals

/-- Forget to the combined static/rate next-start surface. -/
def toStaticWriteIntRateStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateGateCapStableMixStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals sol where
  concRate := res.concRate
  hoffGateCap := res.hoffGateCap
  nextStartStaticRate := res.nextStartStable.toStaticWriteIntRateResidual boxInputs

end MUReplicatorSettledHaltThinRateGateCapStableMixStartResiduals

/-- Rate residual with honest field-cap `hoff` and next-start reduced to the
remaining frozen-mix stability input. -/
structure MUReplicatorSettledHaltThinRateFieldCapStableMixStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffFieldCap : SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual sol
  nextStartStable : MUReplicatorNextWriteStartStableMixResidual sol

namespace MUReplicatorSettledHaltThinRateFieldCapStableMixStartResiduals

/-- Forget the field-cap/stable-mix headline surface to the current rate
no-split residual. -/
def toRateNoSplitStartResidual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateFieldCapStableMixStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorSettledHaltThinRateNoSplitStartResiduals sol where
  concRate := res.concRate
  hoffNoSplit := res.hoffFieldCap.toNoSplitResidual
  nextStartInputs :=
    (res.nextStartStable.toStaticWriteIntRateResidual boxInputs).toHStartInputsResidual
      boxInputs res.concRate

end MUReplicatorSettledHaltThinRateFieldCapStableMixStartResiduals

/-- Rate residual with honest field-cap `hoff` and next-start reduced to
write-hold-frozen prefix stability. -/
structure MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) where
  concRate : MUReplicatorSettledHaltConcentrationRateResiduals sol
  hoffFieldCap : SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual sol
  nextStartHoldStable : MUReplicatorNextWriteStartHoldStableMixResidual sol

namespace MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals

/-- Start-only next-write residual from the hold-frozen stability input. -/
def nextStartOnly
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorNextWriteStartOnlyResidual sol :=
  res.nextStartHoldStable.toStartOnlyResidual boxInputs res.concRate

/-- Rate-based next-write residual. -/
def nextWrite
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorNextWriteStartMixResidual sol :=
  (res.nextStartOnly boxInputs).toStartMixRateResidual boxInputs res.concRate

/-- Field-cap `hoff` residual converted to the full field-integral residual. -/
def hoffIntegral
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    SelectorMUHoffFieldIntegralResidual sol :=
  res.hoffFieldCap.toNoSplitResidual.toFieldIntegralResidual boxInputs

/-- Generic-rate read-start residual. -/
def lateStart
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_rate_concentration_residual
    boxInputs res.concRate

/-- Assemble the late-start final data consumed by
`bgp_MU_replicator_settled_late_start`. -/
def toLateStartHaltFacts
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (res : MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals sol)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol) :
    MUReplicatorLateStartHaltFacts sol :=
  let nextW := res.nextWrite boxInputs
  let hoff := res.hoffIntegral boxInputs
  { cfg := solMUReplStaticCfg
    hcfg := solMUReplStaticCfg_eq
    readStart := res.lateStart boxInputs
    δnext := nextW.δnext
    holdPrefix := fun _ _ => (1 : ℝ)
    hδnext := nextW.hδnext
    hδnext_nonneg := nextW.hδnext_nonneg
    hholdPrefix_nonneg := by
      intro _w _j
      norm_num
    hoff := hoff.p_hoff
    hnextWrite := by
      intro w j t ht
      simpa [nextW] using nextW.p_hnextWrite w j t ht
    hfiniteHold := by
      intro w j t ht
      exact boxInputs.hfiniteHold_one w j t ht }

end MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals

/-- Construct the halt-only settled facts from the honest residual bundle. -/
def muReplicatorSettledHaltFacts_of_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_param (sol := sol) boxInputs herr hκ₀_nonneg hg₀ hscale
    res.hqL_full res.hutube_win res.Bz res.Bzmax res.δnext res.holdPrefix
    res.hBz_nonneg res.hBz_bdd res.hδnext res.hδnext_nonneg res.hholdPrefix_nonneg
    res.p_hz_start res.p_hoff res.p_hnextWrite res.p_hfiniteHold res.p_hloser

/-- Halt-facts producer from the thinner box-reduced residual interface. -/
def muReplicatorSettledHaltFacts_of_boxReduced_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_residual
    (sol := sol) boxInputs herr hκ₀_nonneg hg₀ hscale
    (res.toSettledHaltResiduals boxInputs)

/-- Halt-facts producer using the split-u-tube residual interface. -/
def muReplicatorSettledHaltFacts_of_splitUTube_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀)
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltResidualsSplitUTube sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_residual sol boxInputs herr hκ₀_nonneg hg₀ hscale
    res.toResidual

/-- Halt-facts producer using the combined box-reduced and split-u-tube
residual interface. -/
def muReplicatorSettledHaltFacts_of_boxReduced_splitUTube_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_residual
    (sol := sol) boxInputs herr hκ₀_nonneg hg₀ hscale
    (res.toSettledHaltResiduals boxInputs)

/-- Halt-facts producer using the integral-`hoff` box-reduced residual
interface. -/
def muReplicatorSettledHaltFacts_of_boxReduced_integralHoff_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_boxReduced_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toBoxReducedResiduals

/-- Halt-facts producer using the split-next-write box-reduced residual
interface. -/
def muReplicatorSettledHaltFacts_of_boxReduced_nextWrite_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedNextWriteResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_boxReduced_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toBoxReducedResiduals

/-- Halt-facts producer from the combined thin residual interface. -/
def muReplicatorSettledHaltFacts_of_thin_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_residual
    (sol := sol) boxInputs herr hκ₀_nonneg hg₀ hscale
    (res.toSettledHaltResiduals boxInputs)

/-- Halt-facts producer from the bundled-concentration thin residual
interface. -/
def muReplicatorSettledHaltFacts_of_thin_concentration_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinConcentrationResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_thin_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toThinResiduals

/-- Halt-facts producer from the thin residual with start-only next-write
frontier. -/
def muReplicatorSettledHaltFacts_of_thin_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinStartResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_thin_concentration_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale
    (res.toThinConcentrationResiduals boxInputs herr hκ₀_nonneg hg₀ hscale)

/-- Halt-facts producer from the thinner write-reach-start residual interface. -/
def muReplicatorSettledHaltFacts_of_thin_writeReach_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinWriteReachStartResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_thin_start_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toThinStartResiduals

/-- Halt-facts producer from the current split-`hoff`/hstart-input interface. -/
def muReplicatorSettledHaltFacts_of_thin_split_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinSplitStartResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_thin_start_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale (res.toThinStartResiduals boxInputs)

/-- Halt-facts producer from the no-split `hoff`/hstart-input interface. -/
def muReplicatorSettledHaltFacts_of_thin_nosplit_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinNoSplitStartResiduals sol) :
    MUReplicatorSettledHaltFacts sol :=
  muReplicatorSettledHaltFacts_of_thin_split_start_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale
    (res.toThinSplitStartResiduals boxInputs)

/-- Existing settled halt residuals imply the selector/MU late-start read-start
residual.  This stays on the selector side and does not bridge to
`Paper3Main`'s contract iterator solution type.
-/
def mu_replicator_late_start_read_start_of_settled_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_settled_facts
    (muReplicatorSettledHaltFacts_of_residual
      (sol := sol) boxInputs herr hκ₀_nonneg hg₀ hscale res)

/-- Late-start read-start producer using the box-reduced residual interface. -/
def mu_replicator_late_start_read_start_of_boxReduced_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_settled_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale (res.toSettledHaltResiduals boxInputs)

/-- Late-start read-start producer using the split-u-tube residual interface. -/
def mu_replicator_late_start_read_start_of_splitUTube_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltResidualsSplitUTube sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_settled_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toResidual

/-- Late-start read-start producer using the combined box-reduced and
split-u-tube residual interface. -/
def mu_replicator_late_start_read_start_of_boxReduced_splitUTube_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_settled_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale (res.toSettledHaltResiduals boxInputs)

/-- Late-start read-start producer using the integral-`hoff` residual
interface. -/
def mu_replicator_late_start_read_start_of_boxReduced_integralHoff_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_boxReduced_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toBoxReducedResiduals

/-- Late-start read-start producer using the split-next-write residual
interface. -/
def mu_replicator_late_start_read_start_of_boxReduced_nextWrite_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltBoxReducedNextWriteResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_boxReduced_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toBoxReducedResiduals

/-- Late-start read-start producer using the combined thin residual interface. -/
def mu_replicator_late_start_read_start_of_thin_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_settled_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale (res.toSettledHaltResiduals boxInputs)

/-- Late-start read-start producer from the bundled-concentration thin residual
interface. -/
def mu_replicator_late_start_read_start_of_thin_concentration_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinConcentrationResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_thin_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toThinResiduals

/-- Late-start read-start producer from the thin residual with start-only
next-write frontier. -/
def mu_replicator_late_start_read_start_of_thin_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinStartResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_thin_concentration_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale
    (res.toThinConcentrationResiduals boxInputs herr hκ₀_nonneg hg₀ hscale)

/-- Late-start read-start producer from the thinner write-reach-start residual
interface. -/
def mu_replicator_late_start_read_start_of_thin_writeReach_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinWriteReachStartResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_thin_start_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale res.toThinStartResiduals

/-- Late-start read-start producer from the current split-`hoff`/hstart-input
interface. -/
def mu_replicator_late_start_read_start_of_thin_split_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinSplitStartResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_thin_start_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale (res.toThinStartResiduals boxInputs)

/-- Late-start read-start producer from the no-split `hoff`/hstart-input
interface. -/
def mu_replicator_late_start_read_start_of_thin_nosplit_start_residual
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    {sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀}
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀ sol)
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (hκ₀_nonneg : 0 ≤ (κ₀ : ℝ))
    (hg₀ : 0 < (g₀ : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (res : MUReplicatorSettledHaltThinNoSplitStartResiduals sol) :
    MUReplicatorLateStartReadStartResidual sol :=
  mu_replicator_late_start_read_start_of_thin_split_start_residual
    boxInputs herr hκ₀_nonneg hg₀ hscale
    (res.toThinSplitStartResiduals boxInputs)

open MachineInstance in
/-- Realized selector/MU late-start read-start residual with box inputs
discharged by the concrete realized selector-replicator solution.
-/
def mu_replicator_late_start_read_start_realized_of_settled_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  mu_replicator_late_start_read_start_of_settled_residual
    (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    herr hκ0 hg0 hscale res

open MachineInstance in
/-- Realized selector/MU late-start read-start residual using the combined
box-reduced and split-u-tube residual interface. -/
def mu_replicator_late_start_read_start_realized_of_boxReduced_splitUTube_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  mu_replicator_late_start_read_start_of_boxReduced_splitUTube_residual
    (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    herr hκ0 hg0 hscale res

open MachineInstance in
/-- Realized selector/MU late-start read-start residual using the combined thin
residual interface. -/
def mu_replicator_late_start_read_start_realized_of_thin_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  mu_replicator_late_start_read_start_of_thin_residual
    (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    herr hκ0 hg0 hscale res

open MachineInstance in
/-- Realized selector/MU late-start read-start residual using the
bundled-concentration thin residual interface. -/
def mu_replicator_late_start_read_start_realized_of_thin_concentration_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinConcentrationResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  mu_replicator_late_start_read_start_of_thin_concentration_residual
    (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    herr hκ0 hg0 hscale res

open MachineInstance in
/-- Realized selector/MU late-start read-start residual using the thin residual
with start-only next-write frontier. -/
def mu_replicator_late_start_read_start_realized_of_thin_start_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  mu_replicator_late_start_read_start_of_thin_start_residual
    (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    herr hκ0 hg0 hscale res

open MachineInstance in
/-- Realized selector/MU late-start read-start residual using the thinner
write-reach-start residual interface. -/
def mu_replicator_late_start_read_start_realized_of_thin_writeReach_start_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinWriteReachStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  mu_replicator_late_start_read_start_of_thin_writeReach_start_residual
    (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    herr hκ0 hg0 hscale res

open MachineInstance in
/-- Realized selector/MU late-start read-start residual using the no-split
`hoff`/hstart-input residual interface. -/
def mu_replicator_late_start_read_start_realized_of_thin_nosplit_start_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinNoSplitStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  mu_replicator_late_start_read_start_of_thin_nosplit_start_residual
    (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    herr hκ0 hg0 hscale res

open MachineInstance in
/-- Realized selector/MU late-start read-start residual using the generic-rate
no-split residual interface. -/
def mu_replicator_late_start_read_start_realized_of_thin_rate_nosplit_start_residual
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateNoSplitStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    MUReplicatorLateStartReadStartResidual
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0) :=
  res.lateStart
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)

open MachineInstance in
/-- Realized headline with `MUReplicatorSettledHaltFacts` discharged by the
parametric settled construction. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (boxInputs : MUReplicatorBoxInputs eta heta Mcy κ₀ g₀
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))
    (res : MUReplicatorSettledHaltResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_discharged_halt
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0 init_presented boxInputs
    (muReplicatorSettledHaltFacts_of_residual
      (sol := solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
      boxInputs herr hκ0 hg0 hscale res)

#print axioms universalPval_continuous_of_cont_u
#print axioms muReplicatorBoxInputs_realized
#print axioms selectorMUHoffGateCoeff
#print axioms selectorMUHoff_hcapLeft_of_gate
#print axioms selectorMUHoff_hcapRight_of_gate
#print axioms SelectorMUWritePrefixUTubeResidual
#print axioms SelectorMUWritePrefixUTubeResidual.hutube_prefix
#print axioms SelectorMUWritePrefixUTubeResidual.hutube_write_hold
#print axioms SelectorMUWritePrefixUTubeResidual.hutube_write_hold_coord
#print axioms SelectorMUWriteFullUTubeResidual
#print axioms SelectorMUWriteFullUTubeResidual.hutube_win
#print axioms MUReplicatorSettledHaltResidualsSplitUTube
#print axioms MUReplicatorSettledHaltResidualsSplitUTube.toResidual
#print axioms MUReplicatorBoxInputs.halt_z_mem_Icc
#print axioms MUReplicatorBoxInputs.halt_mixTarget_mem_Icc
#print axioms MUReplicatorBoxInputs.hz_writeHold_static_next_le_one
#print axioms MUReplicatorBoxInputs.hfiniteHold_one
#print axioms MUReplicatorSettledHaltBoxReducedResiduals
#print axioms MUReplicatorSettledHaltBoxReducedResiduals.toSettledHaltResiduals
#print axioms MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals
#print axioms MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals.toBoxReducedResiduals
#print axioms MUReplicatorSettledHaltBoxReducedSplitUTubeResiduals.toSettledHaltResiduals
#print axioms selectorMUZOffStart
#print axioms selectorMUZOffEnd
#print axioms selectorMUInterReadStart_le_zOffStart
#print axioms selectorMUZOffStart_le_zOffEnd
#print axioms selectorMUZOffEnd_le_nextWriteStart
#print axioms selectorMU_sin_nonpos_zOffMiddle
#print axioms selectorMUHoffIntegrand
#print axioms selectorMUHoffIntegrand_continuous
#print axioms selectorMUHoffMiddleEnvelope
#print axioms SelectorMUHoffMiddleEnvelopeResidual
#print axioms SelectorMUHoffFieldIntegralResidual
#print axioms SelectorMUHoffFieldIntegralResidual.p_hoff
#print axioms SelectorMUHoffSplitFieldIntegralResidual
#print axioms SelectorMUHoffSplitFieldIntegralResidual.toFieldIntegralResidual
#print axioms selectorMUHoff_middle_offphase_of_envelope
#print axioms selectorMUHoff_hsplitInt_of_caps
#print axioms SelectorMUHoffSplitMiddleEnvelopeResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeResidual.toSplitFieldIntegralResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeResidual.toFieldIntegralResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual.toSplitMiddleEnvelopeResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeNoSplitResidual.toFieldIntegralResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeGateCapNoSplitResidual.toNoSplitResidual
#print axioms selectorMUHoffCapLeftField
#print axioms selectorMUHoffCapRightField
#print axioms selectorMUHoff_hcapLeft_of_field_cap
#print axioms selectorMUHoff_hcapRight_of_field_cap
#print axioms SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual
#print axioms SelectorMUHoffSplitMiddleEnvelopeFieldCapNoSplitResidual.toNoSplitResidual
#print axioms MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals
#print axioms MUReplicatorSettledHaltBoxReducedIntegralHoffResiduals.toBoxReducedResiduals
#print axioms solMURepl_nextWrite_window_of_start_and_mix
#print axioms MUReplicatorNextWriteStartMixResidual
#print axioms MUReplicatorNextWriteStartMixResidual.δnext
#print axioms MUReplicatorNextWriteStartMixResidual.hδnext
#print axioms MUReplicatorNextWriteStartMixResidual.hδnext_nonneg
#print axioms MUReplicatorNextWriteStartMixResidual.p_hnextWrite
#print axioms MUReplicatorNextWriteStartOnlyResidual
#print axioms MUReplicatorNextWriteStartWriteReachResidual
#print axioms MUReplicatorNextWriteStartWriteReachResidual.δstart
#print axioms MUReplicatorNextWriteStartWriteReachResidual.hδstart
#print axioms MUReplicatorNextWriteStartWriteReachResidual.hδstart_nonneg
#print axioms MUReplicatorNextWriteStartWriteReachResidual.p_hnextStart
#print axioms MUReplicatorNextWriteStartWriteReachResidual.toStartOnlyResidual
#print axioms MUReplicatorNextWriteStartFromHStartInputsResidual
#print axioms MUReplicatorNextWriteStartFromHStartInputsResidual.toWriteReachResidual
#print axioms MUReplicatorNextWriteStartFromHStartInputsResidual.toStartOnlyResidual
#print axioms selectorMU_nextStart_hwriteInt_hold_lbd_z
#print axioms MUReplicatorNextWriteStartStaticWriteIntResidual
#print axioms MUReplicatorNextWriteStartStaticWriteIntResidual.toHStartInputsResidual
#print axioms solMUReplStaticHaltEpsLam
#print axioms solMUReplStaticHaltEpsLam_tendsto_zero
#print axioms solMURepl_p_hnextMix_of_p_hloser
#print axioms MUReplicatorSettledHaltBoxReducedNextWriteResiduals
#print axioms MUReplicatorSettledHaltBoxReducedNextWriteResiduals.toBoxReducedResiduals
#print axioms MUReplicatorSettledHaltThinResiduals
#print axioms MUReplicatorSettledHaltThinResiduals.toBoxReducedSplitUTubeResiduals
#print axioms MUReplicatorSettledHaltThinResiduals.toSettledHaltResiduals
#print axioms MUReplicatorSettledHaltConcentrationResiduals
#print axioms MUReplicatorSettledHaltConcentrationResiduals.p_hnextMix
#print axioms MUReplicatorNextWriteStartOnlyResidual.toStartMixResidual
#print axioms MUReplicatorSettledHaltConcentrationRateResiduals
#print axioms selectorSettledHaltDeltaRate
#print axioms solMURepl_p_hnextMix_of_loser_rate
#print axioms solMURepl_hmix_halt_of_loser_rate
#print axioms solMURepl_hmix_halt_on_settled_of_loser_rate
#print axioms MUReplicatorBoxInputs.nextStart_hz_start_mismatch_le_one
#print axioms MUReplicatorSettledHaltConcentrationRateResiduals.p_hnextMix
#print axioms MUReplicatorNextWriteStartFromHStartRateInputsResidual
#print axioms MUReplicatorNextWriteStartFromHStartRateInputsResidual.toHStartInputsResidual
#print axioms MUReplicatorNextWriteStartFromHStartRateInputsResidual.toStartOnlyResidual
#print axioms MUReplicatorNextWriteStartStaticWriteIntRateResidual
#print axioms MUReplicatorNextWriteStartStaticWriteIntRateResidual.toRateInputsResidual
#print axioms MUReplicatorNextWriteStartStaticWriteIntRateResidual.toHStartInputsResidual
#print axioms MUReplicatorNextWriteStartStableMixResidual
#print axioms MUReplicatorNextWriteStartStableMixResidual.toStaticWriteIntRateResidual
#print axioms MUReplicatorNextWriteStartHoldStableMixResidual
#print axioms MUReplicatorNextWriteStartHoldStableMixResidual.toWriteReachResidual
#print axioms MUReplicatorNextWriteStartHoldStableMixResidual.toStartOnlyResidual
#print axioms MUReplicatorNextWriteStartOnlyResidual.toStartMixRateResidual
#print axioms selectorSettledWriteIntLower_le_gateZ_integral
#print axioms mu_replicator_late_start_read_start_of_rate_concentration_residual
#print axioms MUReplicatorSettledHaltThinConcentrationResiduals
#print axioms MUReplicatorSettledHaltThinConcentrationResiduals.toThinResiduals
#print axioms MUReplicatorSettledHaltThinConcentrationResiduals.toSettledHaltResiduals
#print axioms MUReplicatorSettledHaltThinStartResiduals
#print axioms MUReplicatorSettledHaltThinStartResiduals.toThinConcentrationResiduals
#print axioms MUReplicatorSettledHaltThinWriteReachStartResiduals
#print axioms MUReplicatorSettledHaltThinWriteReachStartResiduals.toThinStartResiduals
#print axioms MUReplicatorSettledHaltThinSplitStartResiduals
#print axioms MUReplicatorSettledHaltThinSplitStartResiduals.toThinWriteReachStartResiduals
#print axioms MUReplicatorSettledHaltThinSplitStartResiduals.toThinStartResiduals
#print axioms MUReplicatorSettledHaltThinNoSplitStartResiduals
#print axioms MUReplicatorSettledHaltThinNoSplitStartResiduals.toThinSplitStartResiduals
#print axioms MUReplicatorSettledHaltThinNoSplitStartResiduals.toThinStartResiduals
#print axioms MUReplicatorSettledHaltThinRateNoSplitStartResiduals
#print axioms MUReplicatorSettledHaltThinRateNoSplitStartResiduals.nextStartOnly
#print axioms MUReplicatorSettledHaltThinRateNoSplitStartResiduals.nextWrite
#print axioms MUReplicatorSettledHaltThinRateNoSplitStartResiduals.hoffIntegral
#print axioms MUReplicatorSettledHaltThinRateNoSplitStartResiduals.lateStart
#print axioms MUReplicatorSettledHaltThinRateNoSplitStartResiduals.toLateStartHaltFacts
#print axioms MUReplicatorSettledHaltThinRateGateCapStartResiduals
#print axioms MUReplicatorSettledHaltThinRateGateCapStartResiduals.toRateNoSplitStartResidual
#print axioms MUReplicatorSettledHaltThinRateGateCapRateStartResiduals
#print axioms
  MUReplicatorSettledHaltThinRateGateCapRateStartResiduals.toRateGateCapStartResidual
#print axioms MUReplicatorSettledHaltThinRateGateCapStaticWriteIntStartResiduals
#print axioms
  MUReplicatorSettledHaltThinRateGateCapStaticWriteIntStartResiduals.toGateCapStartResidual
#print axioms MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals
#print axioms
  MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals.toRateGateCapStartResidual
#print axioms
  MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals.toGateCapStartResidual
#print axioms MUReplicatorSettledHaltThinRateGateCapStableMixStartResiduals
#print axioms
  MUReplicatorSettledHaltThinRateGateCapStableMixStartResiduals.toStaticWriteIntRateStartResidual
#print axioms MUReplicatorSettledHaltThinRateFieldCapStableMixStartResiduals
#print axioms
  MUReplicatorSettledHaltThinRateFieldCapStableMixStartResiduals.toRateNoSplitStartResidual
#print axioms MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals
#print axioms
  MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals.nextStartOnly
#print axioms
  MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals.nextWrite
#print axioms
  MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals.hoffIntegral
#print axioms
  MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals.lateStart
#print axioms
  MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals.toLateStartHaltFacts
#print axioms muReplicatorSettledHaltFacts_of_residual
#print axioms muReplicatorSettledHaltFacts_of_boxReduced_residual
#print axioms muReplicatorSettledHaltFacts_of_splitUTube_residual
#print axioms muReplicatorSettledHaltFacts_of_boxReduced_splitUTube_residual
#print axioms muReplicatorSettledHaltFacts_of_boxReduced_integralHoff_residual
#print axioms muReplicatorSettledHaltFacts_of_boxReduced_nextWrite_residual
#print axioms muReplicatorSettledHaltFacts_of_thin_residual
#print axioms muReplicatorSettledHaltFacts_of_thin_concentration_residual
#print axioms muReplicatorSettledHaltFacts_of_thin_start_residual
#print axioms muReplicatorSettledHaltFacts_of_thin_writeReach_start_residual
#print axioms muReplicatorSettledHaltFacts_of_thin_split_start_residual
#print axioms muReplicatorSettledHaltFacts_of_thin_nosplit_start_residual
#print axioms mu_replicator_late_start_read_start_of_settled_residual
#print axioms mu_replicator_late_start_read_start_of_boxReduced_residual
#print axioms mu_replicator_late_start_read_start_of_splitUTube_residual
#print axioms mu_replicator_late_start_read_start_of_boxReduced_splitUTube_residual
#print axioms mu_replicator_late_start_read_start_of_boxReduced_integralHoff_residual
#print axioms mu_replicator_late_start_read_start_of_boxReduced_nextWrite_residual
#print axioms mu_replicator_late_start_read_start_of_thin_residual
#print axioms mu_replicator_late_start_read_start_of_thin_concentration_residual
#print axioms mu_replicator_late_start_read_start_of_thin_start_residual
#print axioms mu_replicator_late_start_read_start_of_thin_writeReach_start_residual
#print axioms mu_replicator_late_start_read_start_of_thin_split_start_residual
#print axioms mu_replicator_late_start_read_start_of_thin_nosplit_start_residual
#print axioms mu_replicator_late_start_read_start_realized_of_settled_residual
#print axioms mu_replicator_late_start_read_start_realized_of_boxReduced_splitUTube_residual
#print axioms mu_replicator_late_start_read_start_realized_of_thin_residual
#print axioms mu_replicator_late_start_read_start_realized_of_thin_concentration_residual
#print axioms mu_replicator_late_start_read_start_realized_of_thin_start_residual
#print axioms mu_replicator_late_start_read_start_realized_of_thin_writeReach_start_residual
#print axioms mu_replicator_late_start_read_start_realized_of_thin_nosplit_start_residual
#print axioms mu_replicator_late_start_read_start_realized_of_thin_rate_nosplit_start_residual
#print axioms bgp_MU_replicator_settled_realized_hfin_init_residual_halt

open MachineInstance in
/-- Realized residual headline with both `MUReplicatorBoxInputs` and
`MUReplicatorSettledHaltFacts` discharged. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_discharged
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView selectorInitX0 w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (res : MUReplicatorSettledHaltResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr init_presented
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    res

#print axioms bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_discharged

open MachineInstance in
/-- Realized residual headline with box inputs, halt facts, and rational initial
presentation discharged.  The remaining residual bundle is the honest settled
analysis interface. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_discharged
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_discharged
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr
    (selectorReplicatorSphereInitQ_selectorInitX0_presented g₀) res

#print axioms selectorReplicatorSphereInitQ_selectorInitX0_presented
#print axioms bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_discharged

open MachineInstance in
/-- Realized residual headline with box inputs and rational initial
presentation discharged, using the combined thin residual interface. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_discharged_thin
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_discharged
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr
    (res.toSettledHaltResiduals
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_discharged_thin

open MachineInstance in
/-- Realized residual headline with box inputs and rational initial
presentation discharged, using the thin residual interface with the remaining
concentration frontier bundled. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_conc
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinConcentrationResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_discharged_thin
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr
    res.toThinResiduals

#print axioms bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_conc

open MachineInstance in
/-- Realized residual headline with box inputs and rational initial
presentation discharged, using the thin residual interface where the next-write
moving selector target is derived from concentration. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_conc
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr
    (res.toThinConcentrationResiduals
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
      herr hκ0 hg0 hscale)

#print axioms bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_start

open MachineInstance in
/-- Realized residual headline using the thin interface where the next-write
start endpoint is supplied by halt-exact write-reach data. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_writeReach_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinWriteReachStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr
    res.toThinStartResiduals

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_writeReach_start

open MachineInstance in
/-- Realized residual headline in the current split-`hoff`/hstart-input shape. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_split_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinSplitStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_writeReach_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr
    (res.toThinWriteReachStartResiduals
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_split_start

open MachineInstance in
/-- Realized residual headline in the no-split `hoff`/hstart-input shape.

The split aggregation inequality is derived from the left cap, middle
offphase-envelope cap, and right cap. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_nosplit_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (hscale : (κ₀ : ℝ) ≤ ((3 / 4 : ℝ) ^ Mcy) * (g₀ : ℝ))
    (herr : (gateSelectorAtomsCoordN (universalGateAtoms eta heta)).errSel < 1 / 2)
    (res : MUReplicatorSettledHaltThinNoSplitStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_split_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hscale herr
    (res.toThinSplitStartResiduals
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_nosplit_start

open MachineInstance in
/-- Realized residual headline in the generic-rate no-split `hoff`/hstart-input
shape.

This is the rate-shaped successor to the old no-split headline: the final
simulation route consumes the generic read-start radius directly, so no
comparison with the old fixed `epsLamSettled` loser-mass bound is required. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_nosplit_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateNoSplitStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_discharged_late_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0
    (selectorReplicatorSphereInitQ_selectorInitX0_presented g₀)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (res.toLateStartHaltFacts
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_nosplit_start

open MachineInstance in
/-- Realized residual headline in the generic-rate/gate-cap `hoff` shape. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateGateCapStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_nosplit_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0
    (res.toRateNoSplitStartResidual
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_start

open MachineInstance in
/-- Realized headline with the next-start halt-mix radius derived from the same
generic concentration-rate residual. -/
theorem
    bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_rate_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateGateCapRateStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0
    (res.toRateGateCapStartResidual
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_rate_start

open MachineInstance in
/-- Realized residual headline in the generic-rate/gate-cap shape with the
static early write-integral lower bound discharged from `nextStartInputs`. -/
theorem bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_static_writeint_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateGateCapStaticWriteIntStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0
    res.toGateCapStartResidual

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_static_writeint_start

open MachineInstance in
/-- Realized headline with static early-write integral and rate-derived halt
mix radius both discharged from `nextStartInputs`. -/
theorem
    bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_static_rate_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateGateCapStaticWriteIntRateStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_rate_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0
    res.toRateGateCapStartResidual

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_static_rate_start

open MachineInstance in
/-- Realized headline with `nextStartInputs` reduced to the remaining
frozen-mix stability surface. -/
theorem
    bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_stablemix_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateGateCapStableMixStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_static_rate_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0
    (res.toStaticWriteIntRateStartResidual
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_gatecap_stablemix_start

open MachineInstance in
/-- Realized headline with honest field-cap `hoff` and `nextStartInputs`
reduced to the remaining frozen-mix stability surface. -/
theorem
    bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_fieldcap_stablemix_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateFieldCapStableMixStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_nosplit_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0 hKq0
    (res.toRateNoSplitStartResidual
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_fieldcap_stablemix_start

open MachineInstance in
/-- Realized headline with honest field-cap `hoff` and next-start reduced to
write-hold-frozen prefix stability. -/
theorem
    bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_fieldcap_holdstable_start
    (eta : ℚ) (heta : 0 < eta) (Mcy : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 < (g₀ : ℝ))
    (hKq0 : 0 ≤ (Kq : ℝ))
    (res : MUReplicatorSettledHaltThinRateFieldCapHoldStableStartResiduals
      (solMUReplRealizedFinite eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_MU_replicator_settled_realized_hfin_init_discharged_late_start
    eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0
    (selectorReplicatorSphereInitQ_selectorInitX0_presented g₀)
    (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0)
    (res.toLateStartHaltFacts
      (muReplicatorBoxInputs_realized eta heta Mcy κ₀ g₀ HP Kq R hκ0 hg0.le hKq0))

#print axioms
  bgp_MU_replicator_settled_realized_hfin_init_residual_halt_box_init_thin_rate_fieldcap_holdstable_start

end Ripple.BoundedUniversality.BGP
