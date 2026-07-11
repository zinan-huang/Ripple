import Ripple.BoundedUniversality.BGP.SelectorReplicatorEncoder
import Ripple.BoundedUniversality.BGP.SelectorInitTube
import Ripple.BoundedUniversality.BGP.IntComputable

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorWarmPresenter
------------------------------------------
Computable rational presenters for selector-replicator stereographic initial
vectors when the warm-gain coordinate depends on the input index.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators

private def ratConstPresenter (q : ℚ) : ℤ × ℕ :=
  (q.num, q.den)

private theorem ratConstPresenter_den_ne_zero (q : ℚ) :
    (ratConstPresenter q).2 ≠ 0 := by
  simp [ratConstPresenter, q.den_nz]

private theorem ratConstPresenter_spec (q : ℚ) :
    q = (ratConstPresenter q).1 / ((ratConstPresenter q).2 : ℚ) := by
  simpa [ratConstPresenter] using (Rat.num_div_den q).symm

private theorem warmPresenterComputable_fin_prod_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∏ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact Computable.const 1
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∏ i : Fin d, f i.succ a :=
        warmPresenterComputable_fin_prod_nat (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_mul.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.prod_univ_succ]

private theorem warmPresenterComputable_fin_sum_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∑ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact Computable.const 0
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∑ i : Fin d, f i.succ a :=
        warmPresenterComputable_fin_sum_nat (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_add.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.sum_univ_succ]

private def warmPresenterSqNat (n : ℕ) : ℕ := n * n

private theorem computable_warmPresenterSqNat : Computable warmPresenterSqNat :=
  Primrec.nat_mul.to_comp.comp Computable.id Computable.id

private theorem computable_warmPresenterNat_pow_two : Computable fun n : ℕ => n ^ 2 :=
  computable_warmPresenterSqNat.of_eq fun n => by simp [warmPresenterSqNat, pow_two]

private theorem computable_warmPresenterF_apply {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hf : Computable f) (i : Fin n) : Computable fun w => f w i :=
  Computable.fin_app.comp hf (Computable.const i)

private theorem computable_warmPresenterFinLambda {α σ : Type*} [Primcodable α]
    [Primcodable σ] {n : ℕ} {f : α → Fin n → σ}
    (hf : ∀ i, Computable fun a => f a i) : Computable f := by
  have hv : Computable fun a => List.Vector.ofFn fun i => f a i :=
    Computable.vector_ofFn hf
  have he : Computable (Equiv.vectorEquivFin σ n) := Primrec.of_equiv_symm.to_comp
  exact (he.comp hv).of_eq fun a => by
    funext i
    exact List.Vector.get_ofFn (fun i => f a i) i

private noncomputable def warmEuclSphereDprod {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∏ i : Fin n, (f w i).2 ^ 2

private noncomputable def warmEuclSphereSsum {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∑ i : Fin n, (f w i).1.natAbs ^ 2 *
    (warmEuclSphereDprod f w / ((f w i).2 ^ 2))

private noncomputable def warmEuclSphereDen {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  warmEuclSphereSsum f w + warmEuclSphereDprod f w

private noncomputable def warmEuclSpherePresenter {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : Fin (n + 1) → ℤ × ℕ :=
  let D := warmEuclSphereDprod f w
  let S := warmEuclSphereSsum f w
  Fin.cases
    (Int.ofNat S + (-1 : ℤ) * Int.ofNat D, warmEuclSphereDen f w)
    (fun i => (2 * (f w i).1 * Int.ofNat D, (f w i).2 * warmEuclSphereDen f w))

private noncomputable def warmRationalSphereInitQ {n : ℕ}
    (x : ℕ → Fin n → ℚ) (w : ℕ) : Fin (n + 1) → ℚ :=
  let den : ℚ := (∑ i : Fin n, x w i ^ 2) + 1
  Fin.cases (((∑ i : Fin n, x w i ^ 2) - 1) / den)
    (fun i => 2 * x w i / den)

private theorem warmEuclSphereDprod_pos {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < warmEuclSphereDprod f w := by
  unfold warmEuclSphereDprod
  exact Finset.prod_pos fun i _hi =>
    Nat.pow_pos (Nat.pos_of_ne_zero (hden w i))

private theorem warmEuclSphereDprod_cast_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((warmEuclSphereDprod f w : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt (warmEuclSphereDprod_pos (f := f) hden w)

private theorem warmEuclSphereDen_pos {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < warmEuclSphereDen f w := by
  unfold warmEuclSphereDen
  exact Nat.add_pos_right _ (warmEuclSphereDprod_pos (f := f) hden w)

private theorem warmEuclSphereDen_cast_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((warmEuclSphereDen f w : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt (warmEuclSphereDen_pos (f := f) hden w)

private theorem warmEuclSphereDprod_divisor {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) (i : Fin n) :
    (f w i).2 ^ 2 ∣ warmEuclSphereDprod f w := by
  unfold warmEuclSphereDprod
  exact Finset.dvd_prod_of_mem (fun i : Fin n => (f w i).2 ^ 2) (Finset.mem_univ i)

private theorem warmEuclSphereSsum_cast_eq {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((warmEuclSphereSsum f w : ℕ) : ℚ) =
      (warmEuclSphereDprod f w : ℚ) *
        ∑ i : Fin n, (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
  unfold warmEuclSphereSsum
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hdvd : (f w i).2 ^ 2 ∣ warmEuclSphereDprod f w :=
    warmEuclSphereDprod_divisor f w i
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

private theorem warmEuclSpherePresenter_den_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) :
    ∀ w j, (warmEuclSpherePresenter f w j).2 ≠ 0 := by
  intro w j
  refine Fin.cases ?_ ?_ j
  · change warmEuclSphereDen f w ≠ 0
    exact ne_of_gt (warmEuclSphereDen_pos (f := f) hden w)
  · intro i
    change (f w i).2 * warmEuclSphereDen f w ≠ 0
    exact Nat.mul_ne_zero (hden w i) (ne_of_gt (warmEuclSphereDen_pos (f := f) hden w))

private theorem computable_warmEuclSphereDprod {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (warmEuclSphereDprod f) := by
  unfold warmEuclSphereDprod
  refine warmPresenterComputable_fin_prod_nat ?_
  intro i
  exact computable_warmPresenterNat_pow_two.comp
    (Computable.snd.comp (computable_warmPresenterF_apply hf i))

private theorem computable_warmEuclSphereSsum {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (warmEuclSphereSsum f) := by
  unfold warmEuclSphereSsum
  refine warmPresenterComputable_fin_sum_nat ?_
  intro i
  have hfi := computable_warmPresenterF_apply hf i
  have hn : Computable fun w => (f w i).1.natAbs :=
    computable_int_natAbs.comp (Computable.fst.comp hfi)
  have hn2 : Computable fun w => (f w i).1.natAbs ^ 2 :=
    computable_warmPresenterNat_pow_two.comp hn
  have hd2 : Computable fun w => (f w i).2 ^ 2 :=
    computable_warmPresenterNat_pow_two.comp (Computable.snd.comp hfi)
  have hquot : Computable fun w => warmEuclSphereDprod f w / ((f w i).2 ^ 2) :=
    Primrec.nat_div.to_comp.comp (computable_warmEuclSphereDprod hf) hd2
  exact Primrec.nat_mul.to_comp.comp hn2 hquot

private theorem computable_warmEuclSphereDen {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (warmEuclSphereDen f) := by
  unfold warmEuclSphereDen
  exact Primrec.nat_add.to_comp.comp (computable_warmEuclSphereSsum hf)
    (computable_warmEuclSphereDprod hf)

private theorem computable_warmEuclSpherePresenter {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (warmEuclSpherePresenter f) := by
  classical
  have hD := computable_warmEuclSphereDprod hf
  have hS := computable_warmEuclSphereSsum hf
  have hDen := computable_warmEuclSphereDen hf
  have hDInt : Computable fun w => Int.ofNat (warmEuclSphereDprod f w) :=
    computable_int_ofNat.comp hD
  have hSInt : Computable fun w => Int.ofNat (warmEuclSphereSsum f w) :=
    computable_int_ofNat.comp hS
  have hNegD : Computable fun w => (-1 : ℤ) * Int.ofNat (warmEuclSphereDprod f w) :=
    computable2_int_mul.comp (Computable.const (-1 : ℤ)) hDInt
  have hnum0 : Computable fun w =>
      Int.ofNat (warmEuclSphereSsum f w) + (-1 : ℤ) * Int.ofNat (warmEuclSphereDprod f w) :=
    computable2_int_add.comp hSInt hNegD
  have h0 : Computable fun w =>
      (Int.ofNat (warmEuclSphereSsum f w) + (-1 : ℤ) * Int.ofNat (warmEuclSphereDprod f w),
        warmEuclSphereDen f w) :=
    Computable.pair hnum0 hDen
  refine computable_warmPresenterFinLambda fun j => ?_
  refine Fin.cases ?_ ?_ j
  · exact h0.of_eq fun w => by simp [warmEuclSpherePresenter]
  · intro i
    have hfi := computable_warmPresenterF_apply hf i
    have hn : Computable fun w => (f w i).1 := Computable.fst.comp hfi
    have hd : Computable fun w => (f w i).2 := Computable.snd.comp hfi
    have h2n : Computable fun w => 2 * (f w i).1 :=
      computable2_int_mul.comp (Computable.const 2) hn
    have hnum : Computable fun w => 2 * (f w i).1 * Int.ofNat (warmEuclSphereDprod f w) :=
      computable2_int_mul.comp h2n hDInt
    have hden : Computable fun w => (f w i).2 * warmEuclSphereDen f w :=
      Primrec.nat_mul.to_comp.comp hd hDen
    exact (Computable.pair hnum hden).of_eq fun w => by
      simp [warmEuclSpherePresenter]

private theorem warmRationalSphereInitQ_presented_of_eucl_presented {n : ℕ}
    {x : ℕ → Fin n → ℚ}
    (hx_presented : ∃ f : ℕ → Fin n → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x w i = (f w i).1 / ((f w i).2 : ℚ)) :
    ∃ g : ℕ → Fin (n + 1) → ℤ × ℕ, Computable g ∧
      ∀ w j, (g w j).2 ≠ 0 ∧
        warmRationalSphereInitQ x w j = (g w j).1 / ((g w j).2 : ℚ) := by
  classical
  obtain ⟨f, hf, hfval⟩ := hx_presented
  have hden : ∀ w i, (f w i).2 ≠ 0 := fun w i => (hfval w i).1
  refine ⟨warmEuclSpherePresenter f, computable_warmEuclSpherePresenter hf, ?_⟩
  intro w j
  refine ⟨warmEuclSpherePresenter_den_ne_zero (f := f) hden w j, ?_⟩
  have hD : ((warmEuclSphereDprod f w : ℕ) : ℚ) ≠ 0 :=
    warmEuclSphereDprod_cast_ne_zero (f := f) hden w
  have hDen : ((warmEuclSphereDen f w : ℕ) : ℚ) ≠ 0 :=
    warmEuclSphereDen_cast_ne_zero (f := f) hden w
  have hsum :
      (∑ i : Fin n, x w i ^ 2) =
        (warmEuclSphereSsum f w : ℚ) / (warmEuclSphereDprod f w : ℚ) := by
    calc
      (∑ i : Fin n, x w i ^ 2)
          = ∑ i : Fin n, (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [(hfval w i).2]
      _ = (warmEuclSphereSsum f w : ℚ) / (warmEuclSphereDprod f w : ℚ) := by
          have hS := warmEuclSphereSsum_cast_eq (f := f) hden w
          have hSdiv :
              (warmEuclSphereSsum f w : ℚ) / (warmEuclSphereDprod f w : ℚ) =
                ∑ i : Fin n, (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
            rw [hS]
            field_simp [hD]
          exact hSdiv.symm
  refine Fin.cases ?_ ?_ j
  · simp [warmRationalSphereInitQ, warmEuclSpherePresenter, hsum, warmEuclSphereDen]
    field_simp [hD, hDen]
    ring
  · intro i
    have hdi : ((f w i).2 : ℚ) ≠ 0 := by exact_mod_cast hden w i
    simp [warmRationalSphereInitQ, warmEuclSpherePresenter, hsum, (hfval w i).2,
      warmEuclSphereDen]
    field_simp [hD, hDen, hdi]

private noncomputable def selectorReplicatorEuclPresenterWarm {d : ℕ}
    (V : Type) [Fintype V] (f : ℕ → Fin d → ℤ × ℕ)
    (warm : ℕ → ℤ × ℕ) (w : ℕ) : Fin (selectorDim d V) → ℤ × ℕ :=
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
        (fun _ : Fin 1 => warm w)))

private theorem selectorReplicatorEuclPresenterWarm_den_ne_zero {d : ℕ}
    (V : Type) [Fintype V] {f : ℕ → Fin d → ℤ × ℕ}
    {warm : ℕ → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (hwarm_den : ∀ w, (warm w).2 ≠ 0) :
    ∀ w j, (selectorReplicatorEuclPresenterWarm V f warm w j).2 ≠ 0 := by
  intro w j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k <;> simp [selectorReplicatorEuclPresenterWarm, ratConstPresenter_den_ne_zero]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k <;> simp [selectorReplicatorEuclPresenterWarm, ratConstPresenter_den_ne_zero]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simpa [selectorReplicatorEuclPresenterWarm] using hden w i
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simpa [selectorReplicatorEuclPresenterWarm] using hden w i
          · intro a
            fin_cases a
            simp [selectorReplicatorEuclPresenterWarm, ratConstPresenter_den_ne_zero]
  · intro jt
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp [selectorReplicatorEuclPresenterWarm, ratConstPresenter_den_ne_zero]
    · intro tail
      fin_cases tail
      · simp [selectorReplicatorEuclPresenterWarm, Fin.addCases, Fin.append,
          ratConstPresenter_den_ne_zero]
      · simpa [selectorReplicatorEuclPresenterWarm, Fin.addCases, Fin.append] using hwarm_den w

private theorem computable_selectorReplicatorEuclPresenterWarm {d : ℕ}
    (V : Type) [Fintype V] {f : ℕ → Fin d → ℤ × ℕ}
    {warm : ℕ → ℤ × ℕ} (hf : Computable f) (hwarm : Computable warm) :
    Computable (selectorReplicatorEuclPresenterWarm V f warm) := by
  classical
  refine computable_warmPresenterFinLambda fun j => ?_
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k
      · exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenterWarm]
      · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenterWarm]
      · exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenterWarm]
      · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenterWarm]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k
        · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
            simp [selectorReplicatorEuclPresenterWarm]
        · exact (Computable.const (ratConstPresenter 1)).of_eq fun w => by
            simp [selectorReplicatorEuclPresenterWarm]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          exact (computable_warmPresenterF_apply hf i).of_eq fun w => by
            simp [selectorReplicatorEuclPresenterWarm]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            exact (computable_warmPresenterF_apply hf i).of_eq fun w => by
              simp [selectorReplicatorEuclPresenterWarm]
          · intro a
            fin_cases a
            exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
              simp [selectorReplicatorEuclPresenterWarm]
  · intro jt
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      exact (Computable.const (ratConstPresenter (1 / (Fintype.card V : ℚ)))).of_eq
        fun w => by simp [selectorReplicatorEuclPresenterWarm]
    · intro tail
      fin_cases tail
      · exact (Computable.const (ratConstPresenter 0)).of_eq fun w => by
          simp [selectorReplicatorEuclPresenterWarm, Fin.addCases, Fin.append]
      · exact hwarm.of_eq fun w => by
          simp [selectorReplicatorEuclPresenterWarm, Fin.addCases, Fin.append]

private theorem selectorReplicatorEuclPresenterWarm_spec {d : ℕ}
    (V : Type) [Fintype V] {x₀ : ℕ → Fin d → ℚ}
    {warmGainQ : ℕ → ℚ} {f : ℕ → Fin d → ℤ × ℕ} {warm : ℕ → ℤ × ℕ}
    (hfval : ∀ w i, (f w i).2 ≠ 0 ∧
      x₀ w i = (f w i).1 / ((f w i).2 : ℚ))
    (hwarm_val : ∀ w, (warm w).2 ≠ 0 ∧
      warmGainQ w = (warm w).1 / ((warm w).2 : ℚ))
    (w : ℕ) (j : Fin (selectorDim d V)) :
    selectorReplicatorEuclInitQ d V x₀ w (warmGainQ w) j =
      (selectorReplicatorEuclPresenterWarm V f warm w j).1 /
        ((selectorReplicatorEuclPresenterWarm V f warm w j).2 : ℚ) := by
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
          ratConstPresenter_spec (0 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
          ratConstPresenter_spec (1 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
          ratConstPresenter_spec (0 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
          ratConstPresenter_spec (1 : ℚ)
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k
        · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
            ratConstPresenter_spec (1 : ℚ)
        · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
            ratConstPresenter_spec (1 : ℚ)
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm,
            (hfval w i).2]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm,
              (hfval w i).2]
          · intro a
            fin_cases a
            simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
              ratConstPresenter_spec (0 : ℚ)
  · intro jt
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
        ratConstPresenter_spec (1 / (Fintype.card V : ℚ))
    · intro tail
      fin_cases tail
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
          ratConstPresenter_spec (0 : ℚ)
      · simpa [selectorReplicatorEuclInitQ, selectorReplicatorEuclPresenterWarm] using
          (hwarm_val w).2

theorem selectorReplicatorEuclInitQ_presented_of_x0_presented_warm {d : ℕ}
    (V : Type) [Fintype V] {x₀ : ℕ → Fin d → ℚ} {warmGainQ : ℕ → ℚ}
    (hx₀_presented : ∃ f : ℕ → Fin d → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x₀ w i = (f w i).1 / ((f w i).2 : ℚ))
    (hwarm_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ warmGainQ w = (g w).1 / ((g w).2 : ℚ)) :
    ∃ h : ℕ → Fin (selectorDim d V) → ℤ × ℕ, Computable h ∧
      ∀ w j, (h w j).2 ≠ 0 ∧
        selectorReplicatorEuclInitQ d V x₀ w (warmGainQ w) j =
          (h w j).1 / ((h w j).2 : ℚ) := by
  classical
  obtain ⟨f, hf, hfval⟩ := hx₀_presented
  obtain ⟨warm, hwarm, hwarm_val⟩ := hwarm_presented
  refine ⟨selectorReplicatorEuclPresenterWarm V f warm,
    computable_selectorReplicatorEuclPresenterWarm V hf hwarm, ?_⟩
  intro w j
  exact ⟨selectorReplicatorEuclPresenterWarm_den_ne_zero V
      (fun w i => (hfval w i).1) (fun w => (hwarm_val w).1) w j,
    selectorReplicatorEuclPresenterWarm_spec V hfval hwarm_val w j⟩

theorem selectorReplicatorSphereInitQ_presented_of_x0_presented_warm {d : ℕ}
    (V : Type) [Fintype V] {x₀ : ℕ → Fin d → ℚ} {warmGainQ : ℕ → ℚ}
    (hx₀_presented : ∃ f : ℕ → Fin d → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x₀ w i = (f w i).1 / ((f w i).2 : ℚ))
    (hwarm_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ warmGainQ w = (g w).1 / ((g w).2 : ℚ)) :
    ∃ h : ℕ → Fin (selectorDim d V + 1) → ℤ × ℕ, Computable h ∧
      ∀ w j, (h w j).2 ≠ 0 ∧
        selectorReplicatorSphereInitQ d V x₀ w (warmGainQ w) j =
          (h w j).1 / ((h w j).2 : ℚ) := by
  simpa [warmRationalSphereInitQ, selectorReplicatorSphereInitQ] using
    warmRationalSphereInitQ_presented_of_eucl_presented
      (selectorReplicatorEuclInitQ_presented_of_x0_presented_warm V
        hx₀_presented hwarm_presented)

end Ripple.BoundedUniversality.BGP
