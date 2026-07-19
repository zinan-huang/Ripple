import Ripple.BoundedUniversality.BGP.SelectorReplicatorCC
import Ripple.BoundedUniversality.BGP.SelectorReplicatorWarmPresenter
import Ripple.BoundedUniversality.BGP.WarmIndexComputable
import Ripple.BoundedUniversality.BGP.HeadlineNWRealization

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorCCPresenter
----------------------------------------
Computable rational presenters for the CC stereographic initial data.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MachineInstance

private theorem ccPresenterComputable_fin_prod_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∏ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact Computable.const 1
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∏ i : Fin d, f i.succ a :=
        ccPresenterComputable_fin_prod_nat
          (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_mul.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.prod_univ_succ]

private theorem ccPresenterComputable_fin_sum_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∑ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact Computable.const 0
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∑ i : Fin d, f i.succ a :=
        ccPresenterComputable_fin_sum_nat
          (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_add.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.sum_univ_succ]

private def ccPresenterSqNat (n : ℕ) : ℕ := n * n

private theorem computable_ccPresenterSqNat : Computable ccPresenterSqNat :=
  Primrec.nat_mul.to_comp.comp Computable.id Computable.id

private theorem computable_ccPresenterNat_pow_two :
    Computable fun n : ℕ => n ^ 2 :=
  computable_ccPresenterSqNat.of_eq fun n => by
    simp [ccPresenterSqNat, pow_two]

private theorem computable_ccPresenterF_apply {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) (i : Fin n) :
    Computable fun w => f w i :=
  Computable.fin_app.comp hf (Computable.const i)

private theorem computable_ccPresenterFinLambda {α σ : Type*} [Primcodable α]
    [Primcodable σ] {n : ℕ} {f : α → Fin n → σ}
    (hf : ∀ i, Computable fun a => f a i) : Computable f := by
  have hv : Computable fun a => List.Vector.ofFn fun i => f a i :=
    Computable.vector_ofFn hf
  have he : Computable (Equiv.vectorEquivFin σ n) := Primrec.of_equiv_symm.to_comp
  exact (he.comp hv).of_eq fun a => by
    funext i
    exact List.Vector.get_ofFn (fun i => f a i) i

private noncomputable def ccEuclSphereDprod {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∏ i : Fin n, (f w i).2 ^ 2

private noncomputable def ccEuclSphereSsum {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∑ i : Fin n, (f w i).1.natAbs ^ 2 *
    (ccEuclSphereDprod f w / ((f w i).2 ^ 2))

private noncomputable def ccEuclSphereDen {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : ℕ :=
  ccEuclSphereSsum f w + ccEuclSphereDprod f w

private noncomputable def ccEuclSpherePresenter {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) : Fin (n + 1) → ℤ × ℕ :=
  let D := ccEuclSphereDprod f w
  let S := ccEuclSphereSsum f w
  Fin.cases
    (Int.ofNat S + (-1 : ℤ) * Int.ofNat D, ccEuclSphereDen f w)
    (fun i => (2 * (f w i).1 * Int.ofNat D,
      (f w i).2 * ccEuclSphereDen f w))

private noncomputable def ccRationalSphereInitQ {n : ℕ}
    (x : ℕ → Fin n → ℚ) (w : ℕ) : Fin (n + 1) → ℚ :=
  let den : ℚ := (∑ i : Fin n, x w i ^ 2) + 1
  Fin.cases (((∑ i : Fin n, x w i ^ 2) - 1) / den)
    (fun i => 2 * x w i / den)

private theorem ccEuclSphereDprod_pos {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < ccEuclSphereDprod f w := by
  unfold ccEuclSphereDprod
  exact Finset.prod_pos fun i _hi =>
    Nat.pow_pos (Nat.pos_of_ne_zero (hden w i))

private theorem ccEuclSphereDprod_cast_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((ccEuclSphereDprod f w : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt (ccEuclSphereDprod_pos (f := f) hden w)

private theorem ccEuclSphereDen_pos {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < ccEuclSphereDen f w := by
  unfold ccEuclSphereDen
  exact Nat.add_pos_right _ (ccEuclSphereDprod_pos (f := f) hden w)

private theorem ccEuclSphereDen_cast_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((ccEuclSphereDen f w : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt (ccEuclSphereDen_pos (f := f) hden w)

private theorem ccEuclSphereDprod_divisor {n : ℕ}
    (f : ℕ → Fin n → ℤ × ℕ) (w : ℕ) (i : Fin n) :
    (f w i).2 ^ 2 ∣ ccEuclSphereDprod f w := by
  unfold ccEuclSphereDprod
  exact Finset.dvd_prod_of_mem (fun i : Fin n => (f w i).2 ^ 2)
    (Finset.mem_univ i)

private theorem ccEuclSphereSsum_cast_eq {n : ℕ} {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((ccEuclSphereSsum f w : ℕ) : ℚ) =
      (ccEuclSphereDprod f w : ℚ) *
        ∑ i : Fin n, (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
  unfold ccEuclSphereSsum
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hdvd : (f w i).2 ^ 2 ∣ ccEuclSphereDprod f w :=
    ccEuclSphereDprod_divisor f w i
  have hdQ : (((f w i).2 ^ 2 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (hden w i)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_div hdvd hdQ, Nat.cast_pow]
  have hnabs :
      (((f w i).1.natAbs : ℕ) : ℚ) ^ 2 = ((f w i).1 : ℚ) ^ 2 := by
    rw [show (((f w i).1.natAbs : ℕ) : ℚ) =
        ((|(f w i).1| : ℤ) : ℚ) by
      exact (Nat.cast_natAbs (α := ℚ) (f w i).1)]
    rw [Int.cast_abs]
    rw [sq_abs]
  rw [hnabs]
  field_simp [pow_ne_zero 2 (by exact_mod_cast hden w i)]

private theorem ccEuclSpherePresenter_den_ne_zero {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) :
    ∀ w j, (ccEuclSpherePresenter f w j).2 ≠ 0 := by
  intro w j
  refine Fin.cases ?_ ?_ j
  · change ccEuclSphereDen f w ≠ 0
    exact ne_of_gt (ccEuclSphereDen_pos (f := f) hden w)
  · intro i
    change (f w i).2 * ccEuclSphereDen f w ≠ 0
    exact Nat.mul_ne_zero (hden w i)
      (ne_of_gt (ccEuclSphereDen_pos (f := f) hden w))

private theorem computable_ccEuclSphereDprod {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (ccEuclSphereDprod f) := by
  unfold ccEuclSphereDprod
  refine ccPresenterComputable_fin_prod_nat ?_
  intro i
  exact computable_ccPresenterNat_pow_two.comp
    (Computable.snd.comp (computable_ccPresenterF_apply hf i))

private theorem computable_ccEuclSphereSsum {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (ccEuclSphereSsum f) := by
  unfold ccEuclSphereSsum
  refine ccPresenterComputable_fin_sum_nat ?_
  intro i
  have hfi := computable_ccPresenterF_apply hf i
  have hn : Computable fun w => (f w i).1.natAbs :=
    computable_int_natAbs.comp (Computable.fst.comp hfi)
  have hn2 : Computable fun w => (f w i).1.natAbs ^ 2 :=
    computable_ccPresenterNat_pow_two.comp hn
  have hd2 : Computable fun w => (f w i).2 ^ 2 :=
    computable_ccPresenterNat_pow_two.comp (Computable.snd.comp hfi)
  have hquot :
      Computable fun w => ccEuclSphereDprod f w / ((f w i).2 ^ 2) :=
    Primrec.nat_div.to_comp.comp (computable_ccEuclSphereDprod hf) hd2
  exact Primrec.nat_mul.to_comp.comp hn2 hquot

private theorem computable_ccEuclSphereDen {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (ccEuclSphereDen f) := by
  unfold ccEuclSphereDen
  exact Primrec.nat_add.to_comp.comp (computable_ccEuclSphereSsum hf)
    (computable_ccEuclSphereDprod hf)

private theorem computable_ccEuclSpherePresenter {n : ℕ}
    {f : ℕ → Fin n → ℤ × ℕ} (hf : Computable f) :
    Computable (ccEuclSpherePresenter f) := by
  classical
  have hD := computable_ccEuclSphereDprod hf
  have hS := computable_ccEuclSphereSsum hf
  have hDen := computable_ccEuclSphereDen hf
  have hDInt : Computable fun w => Int.ofNat (ccEuclSphereDprod f w) :=
    computable_int_ofNat.comp hD
  have hSInt : Computable fun w => Int.ofNat (ccEuclSphereSsum f w) :=
    computable_int_ofNat.comp hS
  have hNegD : Computable fun w => (-1 : ℤ) * Int.ofNat
      (ccEuclSphereDprod f w) :=
    computable2_int_mul.comp (Computable.const (-1 : ℤ)) hDInt
  have hnum0 : Computable fun w =>
      Int.ofNat (ccEuclSphereSsum f w) +
        (-1 : ℤ) * Int.ofNat (ccEuclSphereDprod f w) :=
    computable2_int_add.comp hSInt hNegD
  have h0 : Computable fun w =>
      (Int.ofNat (ccEuclSphereSsum f w) +
          (-1 : ℤ) * Int.ofNat (ccEuclSphereDprod f w),
        ccEuclSphereDen f w) :=
    Computable.pair hnum0 hDen
  refine computable_ccPresenterFinLambda fun j => ?_
  refine Fin.cases ?_ ?_ j
  · exact h0.of_eq fun w => by
      simp [ccEuclSpherePresenter]
  · intro i
    have hfi := computable_ccPresenterF_apply hf i
    have hn : Computable fun w => (f w i).1 := Computable.fst.comp hfi
    have hd : Computable fun w => (f w i).2 := Computable.snd.comp hfi
    have h2n : Computable fun w => 2 * (f w i).1 :=
      computable2_int_mul.comp (Computable.const 2) hn
    have hnum :
        Computable fun w => 2 * (f w i).1 *
          Int.ofNat (ccEuclSphereDprod f w) :=
      computable2_int_mul.comp h2n hDInt
    have hden : Computable fun w => (f w i).2 * ccEuclSphereDen f w :=
      Primrec.nat_mul.to_comp.comp hd hDen
    exact (Computable.pair hnum hden).of_eq fun w => by
      simp [ccEuclSpherePresenter]

private theorem ccRationalSphereInitQ_presented_of_eucl_presented {n : ℕ}
    {x : ℕ → Fin n → ℚ}
    (hx_presented : ∃ f : ℕ → Fin n → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x w i = (f w i).1 / ((f w i).2 : ℚ)) :
    ∃ g : ℕ → Fin (n + 1) → ℤ × ℕ, Computable g ∧
      ∀ w j, (g w j).2 ≠ 0 ∧
        ccRationalSphereInitQ x w j = (g w j).1 / ((g w j).2 : ℚ) := by
  classical
  obtain ⟨f, hf, hfval⟩ := hx_presented
  have hden : ∀ w i, (f w i).2 ≠ 0 := fun w i => (hfval w i).1
  refine ⟨ccEuclSpherePresenter f, computable_ccEuclSpherePresenter hf, ?_⟩
  intro w j
  refine ⟨ccEuclSpherePresenter_den_ne_zero (f := f) hden w j, ?_⟩
  have hD : ((ccEuclSphereDprod f w : ℕ) : ℚ) ≠ 0 :=
    ccEuclSphereDprod_cast_ne_zero (f := f) hden w
  have hDen : ((ccEuclSphereDen f w : ℕ) : ℚ) ≠ 0 :=
    ccEuclSphereDen_cast_ne_zero (f := f) hden w
  have hsum :
      (∑ i : Fin n, x w i ^ 2) =
        (ccEuclSphereSsum f w : ℚ) / (ccEuclSphereDprod f w : ℚ) := by
    calc
      (∑ i : Fin n, x w i ^ 2)
          = ∑ i : Fin n,
              (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [(hfval w i).2]
      _ = (ccEuclSphereSsum f w : ℚ) / (ccEuclSphereDprod f w : ℚ) := by
          have hS := ccEuclSphereSsum_cast_eq (f := f) hden w
          have hSdiv :
              (ccEuclSphereSsum f w : ℚ) / (ccEuclSphereDprod f w : ℚ) =
                ∑ i : Fin n,
                  (((f w i).1 : ℚ) / ((f w i).2 : ℚ)) ^ 2 := by
            rw [hS]
            field_simp [hD]
          exact hSdiv.symm
  refine Fin.cases ?_ ?_ j
  · simp [ccRationalSphereInitQ, ccEuclSpherePresenter, hsum, ccEuclSphereDen]
    field_simp [hD, hDen]
    ring
  · intro i
    have hdi : ((f w i).2 : ℚ) ≠ 0 := by exact_mod_cast hden w i
    simp [ccRationalSphereInitQ, ccEuclSpherePresenter, hsum, (hfval w i).2,
      ccEuclSphereDen]
    field_simp [hD, hDen, hdi]

private noncomputable def selectorReplicatorEuclPresenterCC {n : ℕ}
    (old : ℕ → Fin n → ℤ × ℕ) (cmu calpha : ℕ → ℤ × ℕ)
    (w : ℕ) : Fin (n + 2) → ℤ × ℕ :=
  Fin.append (old w) (fun k : Fin 2 => if k = 0 then cmu w else calpha w)

private theorem selectorReplicatorEuclPresenterCC_den_ne_zero {n : ℕ}
    {old : ℕ → Fin n → ℤ × ℕ} {cmu calpha : ℕ → ℤ × ℕ}
    (hold_den : ∀ w i, (old w i).2 ≠ 0)
    (hcmu_den : ∀ w, (cmu w).2 ≠ 0)
    (hcalpha_den : ∀ w, (calpha w).2 ≠ 0) :
    ∀ w j, (selectorReplicatorEuclPresenterCC old cmu calpha w j).2 ≠ 0 := by
  intro w j
  refine Fin.addCases (m := n) (n := 2) ?_ ?_ j
  · intro i
    simpa [selectorReplicatorEuclPresenterCC] using hold_den w i
  · intro k
    fin_cases k
    · simpa [selectorReplicatorEuclPresenterCC] using hcmu_den w
    · simpa [selectorReplicatorEuclPresenterCC] using hcalpha_den w

private theorem computable_selectorReplicatorEuclPresenterCC {n : ℕ}
    {old : ℕ → Fin n → ℤ × ℕ} {cmu calpha : ℕ → ℤ × ℕ}
    (hold : Computable old) (hcmu : Computable cmu)
    (hcalpha : Computable calpha) :
    Computable (selectorReplicatorEuclPresenterCC old cmu calpha) := by
  classical
  refine computable_ccPresenterFinLambda fun j => ?_
  refine Fin.addCases (m := n) (n := 2) ?_ ?_ j
  · intro i
    exact (computable_ccPresenterF_apply hold i).of_eq fun w => by
      simp [selectorReplicatorEuclPresenterCC]
  · intro k
    fin_cases k
    · exact hcmu.of_eq fun w => by
        simp [selectorReplicatorEuclPresenterCC]
    · exact hcalpha.of_eq fun w => by
        simp [selectorReplicatorEuclPresenterCC]

theorem selectorReplicatorEuclInitQCC_presented {d : ℕ}
    (V : Type) [Fintype V] {x0 : ℕ → Fin d → ℚ}
    {warmGainQ cmuInitQ calphaInitQ : ℕ → ℚ}
    (hx0_presented : ∃ f : ℕ → Fin d → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x0 w i = (f w i).1 / ((f w i).2 : ℚ))
    (hwarm_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ warmGainQ w = (g w).1 / ((g w).2 : ℚ))
    (hcmu_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ cmuInitQ w = (g w).1 / ((g w).2 : ℚ))
    (hcalpha_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ calphaInitQ w = (g w).1 / ((g w).2 : ℚ)) :
    ∃ h : ℕ → Fin (selectorDimCC d V) → ℤ × ℕ, Computable h ∧
      ∀ w j, (h w j).2 ≠ 0 ∧
        selectorReplicatorEuclInitQCC d V x0 w
          (warmGainQ w) (cmuInitQ w) (calphaInitQ w) j =
          (h w j).1 / ((h w j).2 : ℚ) := by
  classical
  obtain ⟨old, hold, hold_val⟩ :=
    selectorReplicatorEuclInitQ_presented_of_x0_presented_warm
      (d := d) (x₀ := x0) (warmGainQ := warmGainQ)
      V hx0_presented hwarm_presented
  obtain ⟨cmu, hcmu, hcmu_val⟩ := hcmu_presented
  obtain ⟨calpha, hcalpha, hcalpha_val⟩ := hcalpha_presented
  refine ⟨selectorReplicatorEuclPresenterCC old cmu calpha,
    computable_selectorReplicatorEuclPresenterCC hold hcmu hcalpha, ?_⟩
  intro w j
  refine ⟨selectorReplicatorEuclPresenterCC_den_ne_zero
    (fun w i => (hold_val w i).1)
    (fun w => (hcmu_val w).1)
    (fun w => (hcalpha_val w).1) w j, ?_⟩
  refine Fin.addCases (m := selectorDim d V) (n := 2) ?_ ?_ j
  · intro i
    simp [selectorReplicatorEuclInitQCC, selectorReplicatorEuclPresenterCC,
      (hold_val w i).2]
  · intro k
    fin_cases k
    · simp [selectorReplicatorEuclInitQCC, selectorReplicatorEuclPresenterCC,
        (hcmu_val w).2]
    · simp [selectorReplicatorEuclInitQCC, selectorReplicatorEuclPresenterCC,
        (hcalpha_val w).2]

theorem selectorReplicatorSphereInitQCC_presented_of_x0_presented_warm_rates
    {d : ℕ} (V : Type) [Fintype V] {x0 : ℕ → Fin d → ℚ}
    {warmGainQ cmuInitQ calphaInitQ : ℕ → ℚ}
    (hx0_presented : ∃ f : ℕ → Fin d → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ x0 w i = (f w i).1 / ((f w i).2 : ℚ))
    (hwarm_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ warmGainQ w = (g w).1 / ((g w).2 : ℚ))
    (hcmu_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ cmuInitQ w = (g w).1 / ((g w).2 : ℚ))
    (hcalpha_presented : ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ calphaInitQ w = (g w).1 / ((g w).2 : ℚ)) :
    ∃ h : ℕ → Fin (selectorDimCC d V + 1) → ℤ × ℕ, Computable h ∧
      ∀ w j, (h w j).2 ≠ 0 ∧
        selectorReplicatorSphereInitQCC d V x0 w
          (warmGainQ w) (cmuInitQ w) (calphaInitQ w) j =
          (h w j).1 / ((h w j).2 : ℚ) := by
  simpa [ccRationalSphereInitQ, selectorReplicatorSphereInitQCC] using
    ccRationalSphereInitQ_presented_of_eucl_presented
      (selectorReplicatorEuclInitQCC_presented
        (d := d) (x0 := x0) (warmGainQ := warmGainQ)
        (cmuInitQ := cmuInitQ) (calphaInitQ := calphaInitQ)
        V hx0_presented hwarm_presented hcmu_presented hcalpha_presented)

theorem bgpHeadlineInitPresentedCC :
    ∃ f : ℕ → Fin (selectorDimCC d_U UniversalLocalView + 1) → ℤ × ℕ,
      Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧
        selectorReplicatorSphereInitQCC d_U UniversalLocalView selectorInitX0 w
          (bgpWarmGainQNW w) (bgpNWCmuInitQ w) (bgpNWCalphaInitQ w) i =
          (f w i).1 / ((f w i).2 : ℚ) :=
  selectorReplicatorSphereInitQCC_presented_of_x0_presented_warm_rates
    (d := d_U) (x0 := selectorInitX0)
    (warmGainQ := bgpWarmGainQNW)
    (cmuInitQ := bgpNWCmuInitQ)
    (calphaInitQ := bgpNWCalphaInitQ)
    UniversalLocalView
    selectorInitX0_presented
    bgpWarmGainQNW_presented
    (by simpa only [bgpNWCmuInitQ] using cmuInitQ_presented)
    (by simpa only [bgpNWCalphaInitQ] using calphaInitQ_presented)

open UniversalMachine in
/-- **A5 with the init hypothesis discharged**: the NW consumer needs only the
halt/nonhalt readout facts (produced by the Seg B–F chain migration). -/
theorem bgp_headline_unconditional_of_NW_readout
    (hhalt : ∀ w, undecidableMachine.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T,
        3 / 4 ≤ ((bgpHeadlineSolFamNW w) w).z t haltCoordU ∧
          ((bgpHeadlineSolFamNW w) w).z t haltCoordU ≤ 1)
    (hnonhalt : ∀ w, ¬ undecidableMachine.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T,
        0 ≤ ((bgpHeadlineSolFamNW w) w).z t haltCoordU ∧
          ((bgpHeadlineSolFamNW w) w).z t haltCoordU ≤ 1 / 4) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P undecidableMachine) :=
  bgp_headline_unconditional_of_NW_readout_explicit
    bgpHeadlineInitPresentedCC hhalt hnonhalt

end Ripple.BoundedUniversality.BGP
