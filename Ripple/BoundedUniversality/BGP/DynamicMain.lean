import Ripple.BoundedUniversality.BGP.DynamicAssembly
import Ripple.BoundedUniversality.BGP.MainAssembled

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Real

private abbrev dynTailDim (d : ℕ) : ℕ := d + (d + 1)
private abbrev dynGateTailDim (d : ℕ) : ℕ := 2 + dynTailDim d
private abbrev dynDim (d : ℕ) : ℕ := 4 + dynGateTailDim d

private noncomputable def dynA (d : ℕ) : Fin (dynDim d) :=
  Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d (Fin.natAdd d (0 : Fin 1))))

private noncomputable def dynTupleTraj {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) : Fin (dynDim d) → ℝ :=
  Fin.append
    (fun k : Fin 4 =>
      if k = 0 then Real.sin t else
      if k = 1 then Real.cos t else
      if k = 2 then sol.μ t else sol.α t)
    (Fin.append
      (fun k : Fin 2 =>
        if k = 0 then bGateZ L (sol.μ t) t else bGateU L (sol.μ t) t)
      (Fin.append (sol.z t) (Fin.append (sol.u t) (fun _ : Fin 1 => La.a t))))

private lemma dynTupleTraj_a {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynA d) = La.a t := by
  simp [dynTupleTraj, dynA, dynTailDim, dynGateTailDim]

private noncomputable def dynEuclInitR {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (dynDim d) → ℝ :=
  Fin.append
    (fun k : Fin 4 => if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
    (Fin.append
      (fun _ : Fin 2 => 1)
      (Fin.append
        (fun i : Fin d => ((f w i).1 : ℝ) / ((f w i).2 : ℝ))
        (Fin.append
          (fun i : Fin d => ((f w i).1 : ℝ) / ((f w i).2 : ℝ))
          (fun _ : Fin 1 => 0))))

private noncomputable def dynSphereDprod {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∏ i : Fin d, (f w i).2 ^ 2

private noncomputable def dynSphereSsum {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∑ i : Fin d, (f w i).1.natAbs ^ 2 *
    (dynSphereDprod f w / ((f w i).2 ^ 2))

private noncomputable def dynSphereDen {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : ℕ :=
  5 * dynSphereDprod f w + 2 * dynSphereSsum f w

private noncomputable def dynSphereEuclPresenter {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (dynDim d) → ℤ × ℕ :=
  let D := dynSphereDprod f w
  let S := dynSphereSsum f w
  let den := 5 * D + 2 * S
  Fin.append
    (fun k : Fin 4 =>
      if k = 0 then (0, 1) else
      if k = 1 then (2 * Int.ofNat D, den) else
      if k = 2 then (0, 1) else (2 * Int.ofNat D, den))
    (Fin.append
      (fun _ : Fin 2 => (2 * Int.ofNat D, den))
      (Fin.append
        (fun i : Fin d => (2 * (f w i).1 * Int.ofNat D, (f w i).2 * den))
        (Fin.append
          (fun i : Fin d => (2 * (f w i).1 * Int.ofNat D, (f w i).2 * den))
          (fun _ : Fin 1 => (0, 1)))))

private noncomputable def dynSpherePresenter {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (dynDim d + 1) → ℤ × ℕ :=
  let D := dynSphereDprod f w
  let S := dynSphereSsum f w
  Fin.cases (Int.ofNat (3 * D + 2 * S), 5 * D + 2 * S) (dynSphereEuclPresenter f w)

private noncomputable def dynSphereInitQ {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (dynDim d + 1) → ℚ :=
  fun j => (dynSpherePresenter f w j).1 / ((dynSpherePresenter f w j).2 : ℚ)

private lemma dynSphereDprod_pos {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < dynSphereDprod f w := by
  unfold dynSphereDprod
  exact Finset.prod_pos fun i _hi =>
    Nat.pow_pos (Nat.pos_of_ne_zero (hden w i))

private lemma dynSphereDprod_cast_ne_zero {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((dynSphereDprod f w : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt (dynSphereDprod_pos (f := f) hden w)

private lemma dynSphereDen_pos {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < dynSphereDen f w := by
  unfold dynSphereDen
  exact Nat.add_pos_left (Nat.mul_pos (by norm_num) (dynSphereDprod_pos (f := f) hden w)) _

private lemma dynSphereDen_cast_ne_zero {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((dynSphereDen f w : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt (dynSphereDen_pos (f := f) hden w)

private lemma dynSphereDprod_divisor {d : ℕ} (f : ℕ → Fin d → ℤ × ℕ)
    (w : ℕ) (i : Fin d) :
    (f w i).2 ^ 2 ∣ dynSphereDprod f w := by
  unfold dynSphereDprod
  exact Finset.dvd_prod_of_mem (fun i : Fin d => (f w i).2 ^ 2) (Finset.mem_univ i)

private lemma dynSphereSsum_cast_eq {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((dynSphereSsum f w : ℕ) : ℝ) =
      (dynSphereDprod f w : ℝ) *
        ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
  unfold dynSphereSsum
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hdvd : (f w i).2 ^ 2 ∣ dynSphereDprod f w :=
    dynSphereDprod_divisor f w i
  have hdR : (((f w i).2 ^ 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (hden w i)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_div hdvd hdR, Nat.cast_pow]
  have hnabs : (((f w i).1.natAbs : ℕ) : ℝ) ^ 2 = ((f w i).1 : ℝ) ^ 2 := by
    rw [show (((f w i).1.natAbs : ℕ) : ℝ) = ((|(f w i).1| : ℤ) : ℝ) by
      exact (Nat.cast_natAbs (α := ℝ) (f w i).1)]
    rw [Int.cast_abs]
    rw [sq_abs]
  rw [hnabs]
  field_simp [pow_ne_zero 2 (by exact_mod_cast hden w i)]

private lemma dynEuclInitR_sum_sq {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    (∑ i : Fin (dynDim d), dynEuclInitR f w i ^ 2) =
      4 + 2 * (dynSphereSsum f w : ℝ) / (dynSphereDprod f w : ℝ) := by
  rw [show (∑ i : Fin (dynDim d), dynEuclInitR f w i ^ 2) =
      (∑ k : Fin 4, dynEuclInitR f w (Fin.castAdd (dynGateTailDim d) k) ^ 2) +
      (∑ t : Fin (dynGateTailDim d), dynEuclInitR f w (Fin.natAdd 4 t) ^ 2) by
        simpa [dynDim] using
          (Fin.sum_univ_add
            (fun i : Fin (4 + dynGateTailDim d) => dynEuclInitR f w i ^ 2))]
  have hcore :
      (∑ k : Fin 4, dynEuclInitR f w (Fin.castAdd (dynGateTailDim d) k) ^ 2) = 2 := by
    rw [Fin.sum_univ_four]
    simp [dynEuclInitR]
    norm_num
  have htail :
      (∑ t : Fin (dynGateTailDim d), dynEuclInitR f w (Fin.natAdd 4 t) ^ 2) =
        2 + 2 * ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
    rw [show (∑ t : Fin (dynGateTailDim d), dynEuclInitR f w (Fin.natAdd 4 t) ^ 2) =
        (∑ k : Fin 2, dynEuclInitR f w (Fin.natAdd 4 (Fin.castAdd (dynTailDim d) k)) ^ 2) +
        (∑ t : Fin (dynTailDim d), dynEuclInitR f w (Fin.natAdd 4 (Fin.natAdd 2 t)) ^ 2) by
          simpa [dynGateTailDim] using
            (Fin.sum_univ_add
              (fun t : Fin (2 + dynTailDim d) =>
                dynEuclInitR f w (Fin.natAdd 4 t) ^ 2))]
    have hgates :
        (∑ k : Fin 2, dynEuclInitR f w
          (Fin.natAdd 4 (Fin.castAdd (dynTailDim d) k)) ^ 2) = 2 := by
      rw [Fin.sum_univ_two]
      simp [dynEuclInitR]
      norm_num
    have hzu :
        (∑ t : Fin (dynTailDim d), dynEuclInitR f w
          (Fin.natAdd 4 (Fin.natAdd 2 t)) ^ 2) =
          2 * ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
      rw [show (∑ t : Fin (dynTailDim d), dynEuclInitR f w
          (Fin.natAdd 4 (Fin.natAdd 2 t)) ^ 2) =
          (∑ i : Fin d, dynEuclInitR f w
            (Fin.natAdd 4 (Fin.natAdd 2 (Fin.castAdd (d + 1) i))) ^ 2) +
          (∑ t : Fin (d + 1), dynEuclInitR f w
            (Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d t))) ^ 2) by
            simpa [dynTailDim] using
              (Fin.sum_univ_add
                (fun t : Fin (d + (d + 1)) =>
                  dynEuclInitR f w (Fin.natAdd 4 (Fin.natAdd 2 t)) ^ 2))]
      rw [show (∑ t : Fin (d + 1), dynEuclInitR f w
          (Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d t))) ^ 2) =
          (∑ i : Fin d, dynEuclInitR f w
            (Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d (Fin.castAdd 1 i)))) ^ 2) +
          (∑ k : Fin 1, dynEuclInitR f w
            (Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d (Fin.natAdd d k)))) ^ 2) by
            simpa using
              (Fin.sum_univ_add
                (fun t : Fin (d + 1) =>
                  dynEuclInitR f w (Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d t))) ^ 2))]
      have hzsum :
          (∑ i : Fin d, dynEuclInitR f w
            (Fin.natAdd 4 (Fin.natAdd 2 (Fin.castAdd (d + 1) i))) ^ 2) =
            ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp [dynEuclInitR]
      have husum :
          (∑ i : Fin d, dynEuclInitR f w
            (Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d (Fin.castAdd 1 i)))) ^ 2) =
            ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp [dynEuclInitR]
      have hasum :
          (∑ k : Fin 1, dynEuclInitR f w
            (Fin.natAdd 4 (Fin.natAdd 2 (Fin.natAdd d (Fin.natAdd d k)))) ^ 2) = 0 := by
        rw [Fin.sum_univ_one]
        norm_num [dynEuclInitR]
      rw [hzsum, husum, hasum]
      ring
    rw [hgates, hzu]
  rw [hcore, htail, dynSphereSsum_cast_eq (f := f) hden w]
  field_simp [dynSphereDprod_cast_ne_zero (f := f) hden w]
  ring_nf

private theorem dynSphereInitQ_cast_eq_stereo_dynEuclInitR {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) :
    ∀ w j, ((dynSphereInitQ f w j : ℚ) : ℝ) = stereo (dynEuclInitR f w) j := by
  intro w j
  have hD : ((dynSphereDprod f w : ℕ) : ℝ) ≠ 0 :=
    dynSphereDprod_cast_ne_zero (f := f) hden w
  have hDen : ((dynSphereDen f w : ℕ) : ℝ) ≠ 0 :=
    dynSphereDen_cast_ne_zero (f := f) hden w
  have hsum := dynEuclInitR_sum_sq (f := f) hden w
  refine Fin.cases ?_ ?_ j
  · simp [dynSphereInitQ, dynSpherePresenter, stereo]
    rw [stereoDenom, hsum]
    field_simp [hD, hDen]
    ring_nf
  · intro k
    refine Fin.addCases (m := 4) (n := dynGateTailDim d) ?_ ?_ k
    · intro c
      fin_cases c <;>
        simp [dynSphereInitQ, dynSpherePresenter, dynSphereEuclPresenter, stereo] <;>
        rw [stereoDenom, hsum] <;>
        field_simp [hD, hDen] <;>
        simp [dynEuclInitR] <;>
        ring_nf
    · intro tail
      refine Fin.addCases (m := 2) (n := dynTailDim d) ?_ ?_ tail
      · intro g
        fin_cases g <;>
          simp [dynSphereInitQ, dynSpherePresenter, dynSphereEuclPresenter, stereo] <;>
          rw [stereoDenom, hsum] <;>
          field_simp [hD, hDen] <;>
          simp [dynEuclInitR] <;>
          ring_nf
      · intro tail2
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail2
        · intro i
          have hdNat : (f w i).2 ≠ 0 := hden w i
          have hdR : (((f w i).2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdNat
          have hDenR :
              5 * (dynSphereDprod f w : ℝ) + 2 * (dynSphereSsum f w : ℝ) ≠ 0 := by
            simpa [dynSphereDen, Nat.cast_add, Nat.cast_mul] using hDen
          simp [dynSphereInitQ, dynSpherePresenter, dynSphereEuclPresenter, stereo]
          rw [stereoDenom, hsum]
          simp [dynEuclInitR]
          field_simp [hD, hdR, hDenR]
          ring
        · intro tail3
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail3
          · intro i
            have hdNat : (f w i).2 ≠ 0 := hden w i
            have hdR : (((f w i).2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdNat
            have hDenR :
                5 * (dynSphereDprod f w : ℝ) + 2 * (dynSphereSsum f w : ℝ) ≠ 0 := by
              simpa [dynSphereDen, Nat.cast_add, Nat.cast_mul] using hDen
            simp [dynSphereInitQ, dynSpherePresenter, dynSphereEuclPresenter, stereo]
            rw [stereoDenom, hsum]
            simp [dynEuclInitR]
            field_simp [hD, hdR, hDenR]
            ring
          · intro a
            fin_cases a
            simp [dynSphereInitQ, dynSpherePresenter, dynSphereEuclPresenter, stereo,
              dynEuclInitR]

private theorem stereo_sum_sq {nE : ℕ} (x : Fin nE → ℝ) :
    (∑ j : Fin (nE + 1), stereo x j ^ 2) = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [stereo, Fin.cases_zero, Fin.cases_succ]
  set r : ℝ := ∑ i : Fin nE, x i ^ 2 with hr
  have hden : r + 1 ≠ 0 := by
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    nlinarith
  have htail :
      (∑ i : Fin nE, (2 * x i / (r + 1)) ^ 2) =
        4 * r / (r + 1) ^ 2 := by
    simp only [div_pow, mul_pow]
    calc
      (∑ i : Fin nE, (2 ^ 2 * x i ^ 2) / (r + 1) ^ 2)
          = (∑ i : Fin nE, (4 / (r + 1) ^ 2) * x i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (4 / (r + 1) ^ 2) * r := by
            rw [← Finset.mul_sum]
      _ = 4 * r / (r + 1) ^ 2 := by ring
  simp only [stereoDenom, ← hr]
  rw [htail]
  field_simp [hden]
  ring

private theorem stereo_abs_le_one {nE : ℕ} (x : Fin nE → ℝ)
    (j : Fin (nE + 1)) : |stereo x j| ≤ 1 := by
  have hterm :
      stereo x j ^ 2 ≤ ∑ k : Fin (nE + 1), stereo x k ^ 2 :=
    Finset.single_le_sum
      (fun k _hk => sq_nonneg (stereo x k))
      (Finset.mem_univ j)
  have hsq : stereo x j ^ 2 ≤ 1 := by
    simpa [stereo_sum_sq x] using hterm
  exact (sq_le_one_iff_abs_le_one (stereo x j)).mp hsq

private theorem computable_fin_prod_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∏ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.prod_empty]
      exact Computable.const 1
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∏ i : Fin d, f i.succ a :=
        computable_fin_prod_nat (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_mul.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.prod_univ_succ]

private theorem computable_fin_sum_nat {α : Type*} [Primcodable α] :
    ∀ {d : ℕ} {f : Fin d → α → ℕ},
      (∀ i, Computable (f i)) → Computable fun a => ∑ i, f i a
  | 0, _f, _hf => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact Computable.const 0
  | d + 1, f, hf => by
      have h0 : Computable (f 0) := hf 0
      have ht : Computable fun a => ∑ i : Fin d, f i.succ a :=
        computable_fin_sum_nat (f := fun i => f i.succ) fun i => hf i.succ
      exact (Primrec.nat_add.to_comp.comp h0 ht).of_eq fun a => by
        rw [Fin.sum_univ_succ]

private def sqNat (n : ℕ) : ℕ := n * n

private theorem computable_sqNat : Computable sqNat :=
  Primrec.nat_mul.to_comp.comp Computable.id Computable.id

private theorem computable_nat_pow_two : Computable fun n : ℕ => n ^ 2 :=
  computable_sqNat.of_eq fun n => by simp [sqNat, pow_two]

private theorem computable_f_apply {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hf : Computable f) (i : Fin d) : Computable fun w => f w i :=
  Computable.fin_app.comp hf (Computable.const i)

private theorem computable_fin_lambda {α σ : Type*} [Primcodable α] [Primcodable σ]
    {n : ℕ} {f : α → Fin n → σ}
    (hf : ∀ i, Computable fun a => f a i) : Computable f := by
  have hv : Computable fun a => List.Vector.ofFn fun i => f a i :=
    Computable.vector_ofFn hf
  have he : Computable (Equiv.vectorEquivFin σ n) := Primrec.of_equiv_symm.to_comp
  exact (he.comp hv).of_eq fun a => by
    funext i
    exact List.Vector.get_ofFn (fun i => f a i) i

private theorem computable_dynSphereDprod {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (dynSphereDprod f) := by
  unfold dynSphereDprod
  refine computable_fin_prod_nat ?_
  intro i
  exact computable_nat_pow_two.comp (Computable.snd.comp (computable_f_apply hf i))

private theorem computable_dynSphereSsum {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (dynSphereSsum f) := by
  unfold dynSphereSsum
  refine computable_fin_sum_nat ?_
  intro i
  have hfi := computable_f_apply hf i
  have hn : Computable fun w => (f w i).1.natAbs :=
    computable_int_natAbs.comp (Computable.fst.comp hfi)
  have hn2 : Computable fun w => (f w i).1.natAbs ^ 2 :=
    computable_nat_pow_two.comp hn
  have hd2 : Computable fun w => (f w i).2 ^ 2 :=
    computable_nat_pow_two.comp (Computable.snd.comp hfi)
  have hquot : Computable fun w => dynSphereDprod f w / ((f w i).2 ^ 2) :=
    Primrec.nat_div.to_comp.comp (computable_dynSphereDprod hf) hd2
  exact Primrec.nat_mul.to_comp.comp hn2 hquot

private theorem computable_dynSphereDen {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (dynSphereDen f) := by
  unfold dynSphereDen
  exact Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 5) (computable_dynSphereDprod hf))
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (computable_dynSphereSsum hf))

private theorem computable_dynSphereEuclPresenter {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (dynSphereEuclPresenter f) := by
  classical
  have hD := computable_dynSphereDprod hf
  have hDen := computable_dynSphereDen hf
  have hDInt : Computable fun w => Int.ofNat (dynSphereDprod f w) :=
    computable_int_ofNat.comp hD
  have h2DInt : Computable fun w => 2 * Int.ofNat (dynSphereDprod f w) :=
    computable2_int_mul.comp (Computable.const 2) hDInt
  refine computable_fin_lambda fun j => ?_
  refine Fin.addCases (m := 4) (n := dynGateTailDim d) ?_ ?_ j
  · intro k
    fin_cases k
    · exact (Computable.const (0, 1)).of_eq fun w => by simp [dynSphereEuclPresenter]
    · exact (Computable.pair h2DInt hDen).of_eq fun w => by simp [dynSphereEuclPresenter, dynSphereDen]
    · exact (Computable.const (0, 1)).of_eq fun w => by simp [dynSphereEuclPresenter]
    · exact (Computable.pair h2DInt hDen).of_eq fun w => by simp [dynSphereEuclPresenter, dynSphereDen]
  · intro tail
    refine Fin.addCases (m := 2) (n := dynTailDim d) ?_ ?_ tail
    · intro k
      exact (Computable.pair h2DInt hDen).of_eq fun w => by
        fin_cases k <;> simp [dynSphereEuclPresenter, dynSphereDen]
    · intro tail2
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail2
      · intro i
        have hfi := computable_f_apply hf i
        have hn : Computable fun w => (f w i).1 := Computable.fst.comp hfi
        have hd : Computable fun w => (f w i).2 := Computable.snd.comp hfi
        have h2n : Computable fun w => (2 : ℤ) * (f w i).1 :=
          computable2_int_mul.comp (Computable.const 2) hn
        have hnum : Computable fun w => 2 * (f w i).1 * Int.ofNat (dynSphereDprod f w) :=
          computable2_int_mul.comp h2n hDInt
        have hden : Computable fun w => (f w i).2 * dynSphereDen f w :=
          Primrec.nat_mul.to_comp.comp hd hDen
        exact (Computable.pair hnum hden).of_eq fun w => by
          simp [dynSphereEuclPresenter, dynSphereDen]
      · intro tail3
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail3
        · intro i
          have hfi := computable_f_apply hf i
          have hn : Computable fun w => (f w i).1 := Computable.fst.comp hfi
          have hd : Computable fun w => (f w i).2 := Computable.snd.comp hfi
          have h2n : Computable fun w => (2 : ℤ) * (f w i).1 :=
            computable2_int_mul.comp (Computable.const 2) hn
          have hnum : Computable fun w => 2 * (f w i).1 * Int.ofNat (dynSphereDprod f w) :=
            computable2_int_mul.comp h2n hDInt
          have hden : Computable fun w => (f w i).2 * dynSphereDen f w :=
            Primrec.nat_mul.to_comp.comp hd hDen
          exact (Computable.pair hnum hden).of_eq fun w => by
            simp [dynSphereEuclPresenter, dynSphereDen]
        · intro k
          fin_cases k
          exact (Computable.const (0, 1)).of_eq fun w => by simp [dynSphereEuclPresenter]

private theorem computable_dynSpherePresenter {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (dynSpherePresenter f) := by
  classical
  have hD := computable_dynSphereDprod hf
  have hS := computable_dynSphereSsum hf
  have hDen := computable_dynSphereDen hf
  have h3D : Computable fun w => 3 * dynSphereDprod f w :=
    Primrec.nat_mul.to_comp.comp (Computable.const 3) hD
  have h2S : Computable fun w => 2 * dynSphereSsum f w :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) hS
  have hnumNat : Computable fun w => 3 * dynSphereDprod f w + 2 * dynSphereSsum f w :=
    Primrec.nat_add.to_comp.comp h3D h2S
  have hnumInt : Computable fun w => Int.ofNat (3 * dynSphereDprod f w + 2 * dynSphereSsum f w) :=
    computable_int_ofNat.comp hnumNat
  have h0 : Computable fun w =>
      (Int.ofNat (3 * dynSphereDprod f w + 2 * dynSphereSsum f w), dynSphereDen f w) :=
    Computable.pair hnumInt hDen
  have htail := computable_dynSphereEuclPresenter hf
  refine computable_fin_lambda fun j => ?_
  refine Fin.cases ?_ ?_ j
  · exact h0.of_eq fun w => by simp [dynSpherePresenter, dynSphereDen]
  · intro k
    exact (Computable.fin_app.comp htail (Computable.const k)).of_eq fun w => by
      simp [dynSpherePresenter]

private theorem computable_dynSphereInitQ_presenter {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    ∃ g : ℕ → Fin (dynDim d + 1) → ℤ × ℕ, Computable g ∧
      ∀ w i, dynSphereInitQ f w i = (g w i).1 / ((g w i).2 : ℚ) :=
  ⟨dynSpherePresenter f, computable_dynSpherePresenter hf, by
    intro w i
    rfl⟩

private lemma dynSpherePresenter_den_ne_zero {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) :
    ∀ w j, (dynSpherePresenter f w j).2 ≠ 0 := by
  intro w j
  refine Fin.cases ?_ ?_ j
  · change dynSphereDen f w ≠ 0
    exact ne_of_gt (dynSphereDen_pos (f := f) hden w)
  · intro k
    refine Fin.addCases (m := 4) (n := dynGateTailDim d) ?_ ?_ k
    · intro c
      fin_cases c
      · simp [dynSpherePresenter, dynSphereEuclPresenter]
      · change dynSphereDen f w ≠ 0
        exact ne_of_gt (dynSphereDen_pos (f := f) hden w)
      · simp [dynSpherePresenter, dynSphereEuclPresenter]
      · change dynSphereDen f w ≠ 0
        exact ne_of_gt (dynSphereDen_pos (f := f) hden w)
    · intro tail
      refine Fin.addCases (m := 2) (n := dynTailDim d) ?_ ?_ tail
      · intro g
        fin_cases g <;>
          change dynSphereDen f w ≠ 0 <;>
          exact ne_of_gt (dynSphereDen_pos (f := f) hden w)
      · intro tail2
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail2
        · intro i
          simpa [dynSpherePresenter, dynSphereEuclPresenter, dynSphereDen] using
            Nat.mul_ne_zero (hden w i)
              (ne_of_gt (dynSphereDen_pos (f := f) hden w))
        · intro tail3
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail3
          · intro i
            simpa [dynSpherePresenter, dynSphereEuclPresenter, dynSphereDen] using
              Nat.mul_ne_zero (hden w i)
                (ne_of_gt (dynSphereDen_pos (f := f) hden w))
          · intro a
            fin_cases a
            simp [dynSpherePresenter, dynSphereEuclPresenter]

private lemma dynTupleTraj_zero_eq_dynEuclInitR
    {Conf : Type} [Primcodable Conf] {Mch : DiscreteMachine Conf}
    {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (I : HaltIndicator Mch d E)
    {A K c₀ c₁ : ℚ} {Lstep R : ℕ} {f : ℕ → Fin d → ℤ × ℕ} {w : ℕ}
    (sol : DynIteratorSol d S.evalF A Lstep c₀ c₁ (orbitPoint Mch E w 0))
    (La : DynLatchSol sol I.evalH (K : ℝ) R)
    (hfval : ∀ w i, (f w i).2 ≠ 0 ∧
      E.enc (Mch.init w) i = ((f w i).1 : ℝ) / ((f w i).2 : ℝ)) :
    dynTupleTraj sol La 0 = dynEuclInitR f w := by
  funext j
  refine Fin.addCases (m := 4) (n := dynGateTailDim d) ?_ ?_ j
  · intro k
    fin_cases k <;> simp [dynTupleTraj, dynEuclInitR, sol.init_μ, sol.init_α]
  · intro tail
    refine Fin.addCases (m := 2) (n := dynTailDim d) ?_ ?_ tail
    · intro k
      fin_cases k <;> simp [dynTupleTraj, dynEuclInitR, bGateZ, bGateU, sol.init_μ]
    · intro tail2
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail2
      · intro i
        simp [dynTupleTraj, dynEuclInitR, sol.init_z, orbitPoint, hfval w i]
      · intro tail3
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail3
        · intro i
          simp [dynTupleTraj, dynEuclInitR, sol.init_u, orbitPoint, hfval w i]
        · intro a
          fin_cases a
          simp [dynTupleTraj, dynEuclInitR, La.init_a]

theorem main_assembled_dyn
    {Conf : Type} [Primcodable Conf] (M : UndecidableMachine Conf)
    (d : ℕ) (E : LatticeEncoding M.toDiscreteMachine d)
    (S : RobustRealExtension M.toDiscreteMachine d E)
    (stateCoord : Fin d) (haltLevels : Finset ℤ)
    (hfin : (Set.range fun c => E.enc c stateCoord).Finite)
    (hlevels : ∀ c : Conf, M.toDiscreteMachine.halted c = true ↔
      ∃ v ∈ haltLevels, E.enc c stateCoord = (v : ℝ))
    (hmargin : ∀ c : Conf, M.toDiscreteMachine.halted c = false →
      ∀ v ∈ haltLevels, 1 ≤ |E.enc c stateCoord - (v : ℝ)|)
    (D_K : ℝ) (hD : 0 < D_K)
    (hstepbox : ∀ (w j : ℕ) (i : Fin d),
      |orbitPoint M.toDiscreteMachine E w (j+1) i
        - orbitPoint M.toDiscreteMachine E w j i| ≤ D_K / 4)
    (hencoder : ∃ f : ℕ → Fin d → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧
        E.enc (M.toDiscreteMachine.init w) i
          = ((f w i).1 : ℝ) / ((f w i).2 : ℝ))
    (hstepSmall :
      2 * (S.ηstep : ℝ) < min ((S.r₀ : ℝ) / 2) (1 / 4) / 2)
    (hsupply : ∀ (A : ℚ) (L : ℕ) (c₀ c₁ : ℚ) (w : ℕ),
      0 < A → 0 < c₀ → 0 < c₁ →
      (c₀ : ℝ) * (1 / 2) ^ L > (c₁ : ℝ) →
      (c₁ : ℝ) > (c₀ : ℝ) * (1 / 4) ^ L →
      ∃ sol : DynIteratorSol d S.evalF A L c₀ c₁ (orbitPoint M.toDiscreteMachine E w 0),
        ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (2 * π * j) (2 * π * (j + 1)) →
          (∀ i, |orbitPoint M.toDiscreteMachine E w (j + 1) i
              - orbitPoint M.toDiscreteMachine E w j i| ≤ D_K) ∧
          (∀ i, |sol.z t i - orbitPoint M.toDiscreteMachine E w j i| ≤ D_K) ∧
          (∀ i, |sol.u t i - orbitPoint M.toDiscreteMachine E w j i| ≤ D_K) ∧
          (∀ i, |S.evalF (sol.u t) i - orbitPoint M.toDiscreteMachine E w j i| ≤ D_K)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  let _hstepbox := hstepbox
  obtain ⟨I, A, Lstep, c₀, c₁, K, R, hApos, hc₀pos, hc₁pos, hc₀c₁, hc₁c₀,
    hKpos, hper⟩ :=
    dyn_assembled_euclidean_simulation M.toDiscreteMachine d E S stateCoord haltLevels
      hfin hlevels hmargin D_K hD hstepSmall hsupply
  let Xdyn := dynAssembledField d S.F I.H A K c₀ c₁ Lstep R
  obtain ⟨Y, _htang, htransfer⟩ := compactification_exists (dynDim d) Xdyn
  obtain ⟨f, hf, hfval⟩ := hencoder
  have hden : ∀ w i, (f w i).2 ≠ 0 := fun w i => (hfval w i).1
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := dynDim d + 1
      vf := Y
      init := dynSphereInitQ f }
  choose sol La hhalt hnonhalt using hper
  have hode : ∀ w t, 0 ≤ t →
      HasDerivAt (dynTupleTraj (sol w) (La w))
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (dynTupleTraj (sol w) (La w) t) (Xdyn i)) t := by
    intro w t ht
    simpa [Xdyn, dynTupleTraj] using dynTupleTraj_ode S I (sol w) (La w) t ht
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (dynTupleTraj (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (dynTupleTraj (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (dynTupleTraj (sol w) (La w)) (hode w)
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (dynTupleTraj (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := ?_
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    rw [dynTupleTraj_zero_eq_dynEuclInitR S I (sol w) (La w) hfval]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    exact (dynSphereInitQ_cast_eq_stereo_dynEuclInitR (f := f) hden w j).symm
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact stereo_abs_le_one _ _
  · refine ⟨dynSpherePresenter f, computable_dynSpherePresenter hf, ?_⟩
    intro w j
    refine ⟨dynSpherePresenter_den_ne_zero (f := f) hden w j, rfl⟩
  · exact { hA := (dynA d).succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := hhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer (dynTupleTraj (sol w) (La w) (s w τ)) (dynA d)).1
        (by simpa [dynTupleTraj_a] using hLatch)
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := hnonhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer (dynTupleTraj (sol w) (La w) (s w τ)) (dynA d)).2
        (by simpa [dynTupleTraj_a] using hLatch)
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

end Ripple.BoundedUniversality.BGP
