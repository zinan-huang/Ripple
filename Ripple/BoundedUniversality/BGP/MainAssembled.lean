import Ripple.BoundedUniversality.BGP.BernsteinSeparator
import Ripple.BoundedUniversality.BGP.Existence
import Ripple.BoundedUniversality.BGP.IntComputable

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators

private abbrev asmTailDim (d : ℕ) : ℕ := d + (d + 1)
private abbrev asmDim (d : ℕ) : ℕ := 2 + asmTailDim d

private noncomputable def asmS (d : ℕ) : Fin (asmDim d) :=
  Fin.castAdd (asmTailDim d) (0 : Fin 2)

private noncomputable def asmC (d : ℕ) : Fin (asmDim d) :=
  Fin.castAdd (asmTailDim d) (1 : Fin 2)

private noncomputable def asmTailZ {d : ℕ} (i : Fin d) : Fin (asmTailDim d) :=
  Fin.castAdd (d + 1) i

private noncomputable def asmTailU {d : ℕ} (i : Fin d) : Fin (asmTailDim d) :=
  Fin.natAdd d (Fin.castAdd 1 i)

private noncomputable def asmTailA (d : ℕ) : Fin (asmTailDim d) :=
  Fin.natAdd d (Fin.natAdd d (0 : Fin 1))

private noncomputable def asmZ {d : ℕ} (i : Fin d) : Fin (asmDim d) :=
  Fin.natAdd 2 (asmTailZ i)

private noncomputable def asmU {d : ℕ} (i : Fin d) : Fin (asmDim d) :=
  Fin.natAdd 2 (asmTailU i)

private noncomputable def asmA (d : ℕ) : Fin (asmDim d) :=
  Fin.natAdd 2 (asmTailA d)

private noncomputable def renameZ {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin (asmDim d)) ℚ :=
  MvPolynomial.rename (asmZ (d := d)) p

private noncomputable def renameU {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin (asmDim d)) ℚ :=
  MvPolynomial.rename (asmU (d := d)) p

/-- The assembled Euclidean polynomial field: oscillator, phase-clock
iterator, and halt latch in one rational vector field. -/
def assembledField (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K : ℚ) (M R : ℕ) :
    Fin (asmDim d) → MvPolynomial (Fin (asmDim d)) ℚ :=
  Fin.append
    (fun k : Fin 2 =>
      if k = 0 then MvPolynomial.X (asmC d) else -MvPolynomial.X (asmS d))
    (Fin.append
      (fun i : Fin d =>
        MvPolynomial.C A *
          ((MvPolynomial.C (1 / 2 : ℚ) *
              ((1 : MvPolynomial (Fin (asmDim d)) ℚ) +
                MvPolynomial.X (asmS d))) ^ M) *
          (renameU (F i) - MvPolynomial.X (asmZ i)))
      (Fin.append
        (fun i : Fin d =>
          MvPolynomial.C A *
            ((MvPolynomial.C (1 / 2 : ℚ) *
                ((1 : MvPolynomial (Fin (asmDim d)) ℚ) -
                  MvPolynomial.X (asmS d))) ^ M) *
            (MvPolynomial.X (asmZ i) - MvPolynomial.X (asmU i)))
        (fun _ : Fin 1 =>
          MvPolynomial.C K *
            ((MvPolynomial.C (1 / 2 : ℚ) *
                ((1 : MvPolynomial (Fin (asmDim d)) ℚ) -
                  MvPolynomial.X (asmC d))) ^ R) *
            (renameZ Hp - MvPolynomial.X (asmA d)))))

private lemma assembledField_s (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K : ℚ) (M R : ℕ) :
    assembledField d F Hp A K M R (asmS d) = MvPolynomial.X (asmC d) := by
  simp [assembledField, asmS, asmC]

private lemma assembledField_c (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K : ℚ) (M R : ℕ) :
    assembledField d F Hp A K M R (asmC d) = -MvPolynomial.X (asmS d) := by
  simp [assembledField, asmS, asmC]

private lemma assembledField_z {d : ℕ} (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K : ℚ) (M R : ℕ) (i : Fin d) :
    assembledField d F Hp A K M R (asmZ i) =
      MvPolynomial.C A *
        ((MvPolynomial.C (1 / 2 : ℚ) *
            ((1 : MvPolynomial (Fin (asmDim d)) ℚ) +
              MvPolynomial.X (asmS d))) ^ M) *
        (renameU (F i) - MvPolynomial.X (asmZ i)) := by
  simp [assembledField, asmZ, asmTailZ]

private lemma assembledField_u {d : ℕ} (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K : ℚ) (M R : ℕ) (i : Fin d) :
    assembledField d F Hp A K M R (asmU i) =
      MvPolynomial.C A *
        ((MvPolynomial.C (1 / 2 : ℚ) *
            ((1 : MvPolynomial (Fin (asmDim d)) ℚ) -
              MvPolynomial.X (asmS d))) ^ M) *
        (MvPolynomial.X (asmZ i) - MvPolynomial.X (asmU i)) := by
  simp [assembledField, asmU, asmTailU]

private lemma assembledField_a (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K : ℚ) (M R : ℕ) :
    assembledField d F Hp A K M R (asmA d) =
      MvPolynomial.C K *
        ((MvPolynomial.C (1 / 2 : ℚ) *
            ((1 : MvPolynomial (Fin (asmDim d)) ℚ) -
              MvPolynomial.X (asmC d))) ^ R) *
        (renameZ Hp - MvPolynomial.X (asmA d)) := by
  simp [assembledField, asmA, asmTailA]

private lemma hasDerivAt_fin_append {m n : ℕ}
    {f : ℝ → Fin m → ℝ} {g : ℝ → Fin n → ℝ}
    {f' : Fin m → ℝ} {g' : Fin n → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun τ => Fin.append (f τ) (g τ)) (Fin.append f' g') t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.addCases (m := m) (n := n) ?_ ?_ i
  · intro k
    simpa [Fin.append_left] using hasDerivAt_pi.mp hf k
  · intro k
    simpa [Fin.append_right] using hasDerivAt_pi.mp hg k

private noncomputable def tupleTraj {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ) : Fin (asmDim d) → ℝ :=
  Fin.append
    (fun k : Fin 2 => if k = 0 then Real.sin t else Real.cos t)
    (Fin.append (sol.z t) (Fin.append (sol.u t) (fun _ : Fin 1 => L.a t)))

private lemma tupleTraj_s {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ) :
    tupleTraj sol L t (asmS d) = Real.sin t := by
  simp [tupleTraj, asmS]

private lemma tupleTraj_c {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ) :
    tupleTraj sol L t (asmC d) = Real.cos t := by
  simp [tupleTraj, asmC]

private lemma tupleTraj_z {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ) (i : Fin d) :
    tupleTraj sol L t (asmZ i) = sol.z t i := by
  simp [tupleTraj, asmZ, asmTailZ]

private lemma tupleTraj_u {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ) (i : Fin d) :
    tupleTraj sol L t (asmU i) = sol.u t i := by
  simp [tupleTraj, asmU, asmTailU]

private lemma tupleTraj_a {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ) :
    tupleTraj sol L t (asmA d) = L.a t := by
  simp [tupleTraj, asmA, asmTailA]

private lemma eval_renameU_tuple {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ)
    (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t) (renameU p) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.u t) p := by
  rw [renameU, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := p)
    (g₁ := tupleTraj sol L t ∘ asmU) (g₂ := sol.u t)
    (fun {i} {_c} _hi _hc => tupleTraj_u sol L t i)

private lemma eval_renameZ_tuple {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℝ} {M : ℕ}
    {x₀ : Fin d → ℝ} (sol : IteratorSol d Fr A M x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (L : LatchSol sol Hval K R) (t : ℝ)
    (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t) (renameZ p) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) p := by
  rw [renameZ, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := p)
    (g₁ := tupleTraj sol L t ∘ asmZ) (g₂ := sol.z t)
    (fun {i} {_c} _hi _hc => tupleTraj_z sol L t i)

private theorem tupleTraj_ode
    {Conf : Type} [Primcodable Conf] {Mch : DiscreteMachine Conf}
    {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (I : HaltIndicator Mch d E)
    {A K : ℚ} {M R : ℕ} {x₀ : Fin d → ℝ}
    (sol : IteratorSol d S.evalF (A : ℝ) M x₀)
    (L : LatchSol sol I.evalH (K : ℝ) R) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (tupleTraj sol L)
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t)
          (assembledField d S.F I.H A K M R i)) t := by
  intro t ht
  let clock' : Fin 2 → ℝ := fun k => if k = 0 then Real.cos t else -Real.sin t
  let z' : Fin d → ℝ := fun i =>
    (A : ℝ) * qPulse M t * (S.evalF (sol.u t) i - sol.z t i)
  let u' : Fin d → ℝ := fun i =>
    (A : ℝ) * rPulse M t * (sol.z t i - sol.u t i)
  let a' : Fin 1 → ℝ := fun _ =>
    (K : ℝ) * gPulse R t * (I.evalH (sol.z t) - L.a t)
  have hclock :
      HasDerivAt
        (fun τ => fun k : Fin 2 => if k = 0 then Real.sin τ else Real.cos τ)
        clock' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    · simpa [clock'] using Real.hasDerivAt_sin t
    · simpa [clock'] using Real.hasDerivAt_cos t
  have hz : HasDerivAt (fun τ => sol.z τ) z' t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact sol.ode_z t ht i
  have hu : HasDerivAt (fun τ => sol.u τ) u' t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact sol.ode_u t ht i
  have ha : HasDerivAt (fun τ => fun _ : Fin 1 => L.a τ) a' t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    exact L.ode_a t
  have hraw :
      HasDerivAt (tupleTraj sol L)
        (Fin.append clock' (Fin.append z' (Fin.append u' a'))) t := by
    simpa [tupleTraj, clock', z', u', a'] using
      hasDerivAt_fin_append hclock
        (hasDerivAt_fin_append hz (hasDerivAt_fin_append hu ha))
  refine hraw.congr_deriv ?_
  funext j
  refine Fin.addCases (m := 2) (n := asmTailDim d) ?_ ?_ j
  · intro k
    fin_cases k
    · change clock' 0 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t)
          (assembledField d S.F I.H A K M R (asmS d))
      simp [clock', assembledField_s, tupleTraj_c]
    · change clock' 1 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t)
          (assembledField d S.F I.H A K M R (asmC d))
      simp [clock', assembledField_c, tupleTraj_s]
  · intro tail
    refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
    · intro i
      simp only [Fin.append_left, Fin.append_right]
      change z' i =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t)
          (assembledField d S.F I.H A K M R (asmZ i))
      simp [z', assembledField_z, RobustRealExtension.evalF, qPulse,
        eval_renameU_tuple, tupleTraj_s, tupleTraj_z]
      ring_nf
      simp
    · intro tail2
      refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
      · intro i
        simp only [Fin.append_left, Fin.append_right]
        change u' i =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t)
            (assembledField d S.F I.H A K M R (asmU i))
        simp [u', assembledField_u, rPulse, tupleTraj_s, tupleTraj_z, tupleTraj_u]
        ring_nf
        simp
      · intro k
        fin_cases k
        simp only [Fin.append_left, Fin.append_right]
        change a' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (tupleTraj sol L t)
            (assembledField d S.F I.H A K M R (asmA d))
        simp [a', assembledField_a, HaltIndicator.evalH, gPulse,
          eval_renameZ_tuple, tupleTraj_c, tupleTraj_a]
        ring_nf
        simp

/-- The stereographic image lies on the unit sphere. -/
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

/-- Every coordinate of the stereographic image has absolute value at most one. -/
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

private noncomputable def sphereDprod {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∏ i : Fin d, (f w i).2 ^ 2

private noncomputable def sphereSsum {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : ℕ :=
  ∑ i : Fin d, (f w i).1.natAbs ^ 2 *
    (sphereDprod f w / ((f w i).2 ^ 2))

private noncomputable def sphereEuclPresenter {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (asmDim d) → ℤ × ℕ :=
  let D := sphereDprod f w
  let S := sphereSsum f w
  let den := D + S
  Fin.append
    (fun k : Fin 2 =>
      if k = 0 then (0, 1) else (Int.ofNat D, den))
    (Fin.append
      (fun i : Fin d => ((f w i).1 * Int.ofNat D, (f w i).2 * den))
      (Fin.append
        (fun i : Fin d => ((f w i).1 * Int.ofNat D, (f w i).2 * den))
        (fun _ : Fin 1 => (0, 1))))

private noncomputable def spherePresenter {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (asmDim d + 1) → ℤ × ℕ :=
  let D := sphereDprod f w
  let S := sphereSsum f w
  Fin.cases (Int.ofNat S, D + S) (sphereEuclPresenter f w)

private noncomputable def sphereInitQ {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (asmDim d + 1) → ℚ :=
  fun j => (spherePresenter f w j).1 / ((spherePresenter f w j).2 : ℚ)

private noncomputable def euclInitR {d : ℕ}
    (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) : Fin (asmDim d) → ℝ :=
  Fin.append
    (fun k : Fin 2 => if k = 0 then 0 else 1)
    (Fin.append
      (fun i : Fin d => ((f w i).1 : ℝ) / ((f w i).2 : ℝ))
      (Fin.append
        (fun i : Fin d => ((f w i).1 : ℝ) / ((f w i).2 : ℝ))
        (fun _ : Fin 1 => 0)))

private lemma euclInitR_s {d : ℕ} (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) :
    euclInitR f w (asmS d) = 0 := by
  simp [euclInitR, asmS]

private lemma euclInitR_c {d : ℕ} (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) :
    euclInitR f w (asmC d) = 1 := by
  simp [euclInitR, asmC]

private lemma euclInitR_z {d : ℕ} (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ)
    (i : Fin d) :
    euclInitR f w (asmZ i) = ((f w i).1 : ℝ) / ((f w i).2 : ℝ) := by
  simp [euclInitR, asmZ, asmTailZ]

private lemma euclInitR_u {d : ℕ} (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ)
    (i : Fin d) :
    euclInitR f w (asmU i) = ((f w i).1 : ℝ) / ((f w i).2 : ℝ) := by
  simp [euclInitR, asmU, asmTailU]

private lemma euclInitR_a {d : ℕ} (f : ℕ → Fin d → ℤ × ℕ) (w : ℕ) :
    euclInitR f w (asmA d) = 0 := by
  simp [euclInitR, asmA, asmTailA]

private lemma sphereDprod_pos {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < sphereDprod f w := by
  unfold sphereDprod
  exact Finset.prod_pos fun i _hi =>
    Nat.pow_pos (Nat.pos_of_ne_zero (hden w i))

private lemma sphereDprod_cast_ne_zero {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((sphereDprod f w : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt (sphereDprod_pos (f := f) hden w)

private lemma sphereDprod_add_sphereSsum_pos {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    0 < sphereDprod f w + sphereSsum f w := by
  exact Nat.lt_of_lt_of_le (sphereDprod_pos (f := f) hden w) (Nat.le_add_right _ _)

private lemma sphereDprod_add_sphereSsum_cast_ne_zero {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((sphereDprod f w + sphereSsum f w : ℕ) : ℝ) ≠ 0 := by
  exact_mod_cast ne_of_gt (sphereDprod_add_sphereSsum_pos (f := f) hden w)

private lemma sphereDprod_divisor {d : ℕ} (f : ℕ → Fin d → ℤ × ℕ)
    (w : ℕ) (i : Fin d) :
    (f w i).2 ^ 2 ∣ sphereDprod f w := by
  unfold sphereDprod
  exact Finset.dvd_prod_of_mem (fun i : Fin d => (f w i).2 ^ 2) (Finset.mem_univ i)

private lemma sphereSsum_cast_eq {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    ((sphereSsum f w : ℕ) : ℝ) =
      (sphereDprod f w : ℝ) *
        ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
  unfold sphereSsum
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hdvd : (f w i).2 ^ 2 ∣ sphereDprod f w :=
    sphereDprod_divisor f w i
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

private lemma euclInitR_sum_sq {d : ℕ} {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) (w : ℕ) :
    (∑ i : Fin (asmDim d), euclInitR f w i ^ 2) =
      1 + 2 * (sphereSsum f w : ℝ) / (sphereDprod f w : ℝ) := by
  rw [show (∑ i : Fin (asmDim d), euclInitR f w i ^ 2) =
      (∑ k : Fin 2, euclInitR f w (Fin.castAdd (asmTailDim d) k) ^ 2) +
      (∑ t : Fin (asmTailDim d), euclInitR f w (Fin.natAdd 2 t) ^ 2) by
        simpa [asmDim] using
          (Fin.sum_univ_add
            (fun i : Fin (2 + asmTailDim d) => euclInitR f w i ^ 2))]
  have htail :
      (∑ t : Fin (asmTailDim d), euclInitR f w (Fin.natAdd 2 t) ^ 2) =
        2 * ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
    rw [show (∑ t : Fin (asmTailDim d), euclInitR f w (Fin.natAdd 2 t) ^ 2) =
        (∑ i : Fin d, euclInitR f w (asmZ i) ^ 2) +
        (∑ t : Fin (d + 1), euclInitR f w (Fin.natAdd 2 (Fin.natAdd d t)) ^ 2) by
          simpa [asmTailDim, asmZ, asmTailZ] using
            (Fin.sum_univ_add
              (fun t : Fin (d + (d + 1)) =>
                euclInitR f w (Fin.natAdd 2 t) ^ 2))]
    rw [show (∑ t : Fin (d + 1), euclInitR f w (Fin.natAdd 2 (Fin.natAdd d t)) ^ 2) =
        (∑ i : Fin d, euclInitR f w (asmU i) ^ 2) +
        (∑ k : Fin 1, euclInitR f w (Fin.natAdd 2 (Fin.natAdd d (Fin.natAdd d k))) ^ 2) by
          simpa [asmU, asmTailU] using
            (Fin.sum_univ_add
              (fun t : Fin (d + 1) =>
                euclInitR f w (Fin.natAdd 2 (Fin.natAdd d t)) ^ 2))]
    have hzsum :
        (∑ i : Fin d, euclInitR f w (asmZ i) ^ 2) =
          ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [euclInitR_z]
    have husum :
        (∑ i : Fin d, euclInitR f w (asmU i) ^ 2) =
          ∑ i : Fin d, (((f w i).1 : ℝ) / ((f w i).2 : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [euclInitR_u]
    have hasum :
        (∑ k : Fin 1,
          euclInitR f w (Fin.natAdd 2 (Fin.natAdd d (Fin.natAdd d k))) ^ 2) = 0 := by
      rw [Fin.sum_univ_one]
      change euclInitR f w (asmA d) ^ 2 = 0
      rw [euclInitR_a]
      norm_num
    rw [hzsum, husum, hasum]
    ring
  have hclock :
      (∑ k : Fin 2, euclInitR f w (Fin.castAdd (asmTailDim d) k) ^ 2) = 1 := by
    rw [Fin.sum_univ_two]
    simp [euclInitR, asmTailDim]
  rw [hclock, htail, sphereSsum_cast_eq (f := f) hden w]
  field_simp [sphereDprod_cast_ne_zero (f := f) hden w]

private theorem sphereInitQ_cast_eq_stereo_euclInitR {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) :
    ∀ w j, ((sphereInitQ f w j : ℚ) : ℝ) = stereo (euclInitR f w) j := by
  intro w j
  have hD : ((sphereDprod f w : ℕ) : ℝ) ≠ 0 :=
    sphereDprod_cast_ne_zero (f := f) hden w
  have hDS : ((sphereDprod f w + sphereSsum f w : ℕ) : ℝ) ≠ 0 :=
    sphereDprod_add_sphereSsum_cast_ne_zero (f := f) hden w
  have hsum := euclInitR_sum_sq (f := f) hden w
  refine Fin.cases ?_ ?_ j
  · simp [sphereInitQ, spherePresenter, stereo]
    rw [stereoDenom, hsum]
    field_simp [hD, hDS]
    ring_nf
  · intro k
    refine Fin.addCases (m := 2) (n := asmTailDim d) ?_ ?_ k
    · intro c
      fin_cases c
      · simp [sphereInitQ, spherePresenter, sphereEuclPresenter, stereo]
        change (0 : ℝ) = 2 * euclInitR f w (asmS d) / stereoDenom (euclInitR f w)
        rw [euclInitR_s]
        simp
      · simp [sphereInitQ, spherePresenter, sphereEuclPresenter, stereo]
        change (sphereDprod f w : ℝ) /
            (sphereDprod f w + sphereSsum f w : ℝ) =
          2 * euclInitR f w (asmC d) / stereoDenom (euclInitR f w)
        rw [euclInitR_c, stereoDenom, hsum]
        field_simp [hD, hDS]
        ring
    · intro tail
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
      · intro i
        have hdNat : (f w i).2 ≠ 0 := hden w i
        have hdR : (((f w i).2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdNat
        have hdenProd :
            (((f w i).2 * (sphereDprod f w + sphereSsum f w) : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.mul_ne_zero hdNat
            (ne_of_gt (sphereDprod_add_sphereSsum_pos (f := f) hden w))
        simp [sphereInitQ, spherePresenter, sphereEuclPresenter, stereo]
        change ((f w i).1 : ℝ) * (sphereDprod f w : ℝ) /
            ((f w i).2 * (sphereDprod f w + sphereSsum f w : ℝ)) =
          2 * euclInitR f w (asmZ i) / stereoDenom (euclInitR f w)
        rw [euclInitR_z, stereoDenom, hsum]
        field_simp [hD, hDS, hdR, hdenProd]
        ring
      · intro tail2
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
        · intro i
          have hdNat : (f w i).2 ≠ 0 := hden w i
          have hdR : (((f w i).2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdNat
          have hdenProd :
              (((f w i).2 * (sphereDprod f w + sphereSsum f w) : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast Nat.mul_ne_zero hdNat
              (ne_of_gt (sphereDprod_add_sphereSsum_pos (f := f) hden w))
          simp [sphereInitQ, spherePresenter, sphereEuclPresenter, stereo]
          change ((f w i).1 : ℝ) * (sphereDprod f w : ℝ) /
              ((f w i).2 * (sphereDprod f w + sphereSsum f w : ℝ)) =
            2 * euclInitR f w (asmU i) / stereoDenom (euclInitR f w)
          rw [euclInitR_u, stereoDenom, hsum]
          field_simp [hD, hDS, hdR, hdenProd]
          ring
        · intro a
          fin_cases a
          simp [sphereInitQ, spherePresenter, sphereEuclPresenter, stereo]
          change (0 : ℝ) = 2 * euclInitR f w (asmA d) / stereoDenom (euclInitR f w)
          rw [euclInitR_a]
          simp

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

private theorem computable_sphereDprod {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (sphereDprod f) := by
  unfold sphereDprod
  refine computable_fin_prod_nat ?_
  intro i
  exact computable_nat_pow_two.comp (Computable.snd.comp (computable_f_apply hf i))

private theorem computable_sphereSsum {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (sphereSsum f) := by
  unfold sphereSsum
  refine computable_fin_sum_nat ?_
  intro i
  have hfi := computable_f_apply hf i
  have hn : Computable fun w => (f w i).1.natAbs :=
    computable_int_natAbs.comp (Computable.fst.comp hfi)
  have hn2 : Computable fun w => (f w i).1.natAbs ^ 2 :=
    computable_nat_pow_two.comp hn
  have hd2 : Computable fun w => (f w i).2 ^ 2 :=
    computable_nat_pow_two.comp (Computable.snd.comp hfi)
  have hquot : Computable fun w => sphereDprod f w / ((f w i).2 ^ 2) :=
    Primrec.nat_div.to_comp.comp (computable_sphereDprod hf) hd2
  exact Primrec.nat_mul.to_comp.comp hn2 hquot

private theorem computable_sphereEuclPresenter {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (sphereEuclPresenter f) := by
  classical
  have hD := computable_sphereDprod hf
  have hS := computable_sphereSsum hf
  have hDen : Computable fun w => sphereDprod f w + sphereSsum f w :=
    Primrec.nat_add.to_comp.comp hD hS
  have hDInt : Computable fun w => Int.ofNat (sphereDprod f w) :=
    computable_int_ofNat.comp hD
  refine computable_fin_lambda fun j => ?_
  refine Fin.addCases (m := 2) (n := asmTailDim d) ?_ ?_ j
  · intro k
    by_cases hk : k = 0
    · refine (Computable.const (0, 1)).of_eq ?_
      intro w
      simp [sphereEuclPresenter, hk]
    · refine (Computable.pair hDInt hDen).of_eq ?_
      intro w
      simp [sphereEuclPresenter, hk]
  · intro tail
    refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
    · intro i
      have hfi := computable_f_apply hf i
      have hn : Computable fun w => (f w i).1 := Computable.fst.comp hfi
      have hd : Computable fun w => (f w i).2 := Computable.snd.comp hfi
      have hnum : Computable fun w => (f w i).1 * Int.ofNat (sphereDprod f w) :=
        computable2_int_mul.comp hn hDInt
      have hden : Computable fun w => (f w i).2 *
          (sphereDprod f w + sphereSsum f w) :=
        Primrec.nat_mul.to_comp.comp hd hDen
      refine (Computable.pair hnum hden).of_eq ?_
      intro w
      simp [sphereEuclPresenter]
    · intro tail2
      refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
      · intro i
        have hfi := computable_f_apply hf i
        have hn : Computable fun w => (f w i).1 := Computable.fst.comp hfi
        have hd : Computable fun w => (f w i).2 := Computable.snd.comp hfi
        have hnum : Computable fun w => (f w i).1 * Int.ofNat (sphereDprod f w) :=
          computable2_int_mul.comp hn hDInt
        have hden : Computable fun w => (f w i).2 *
            (sphereDprod f w + sphereSsum f w) :=
          Primrec.nat_mul.to_comp.comp hd hDen
        refine (Computable.pair hnum hden).of_eq ?_
        intro w
        simp [sphereEuclPresenter]
      · intro k
        fin_cases k
        refine (Computable.const (0, 1)).of_eq ?_
        intro w
        simp [sphereEuclPresenter]

private theorem computable_spherePresenter {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    Computable (spherePresenter f) := by
  classical
  have hD := computable_sphereDprod hf
  have hS := computable_sphereSsum hf
  have hDen : Computable fun w => sphereDprod f w + sphereSsum f w :=
    Primrec.nat_add.to_comp.comp hD hS
  have hSInt : Computable fun w => Int.ofNat (sphereSsum f w) :=
    computable_int_ofNat.comp hS
  have h0 : Computable fun w =>
      (Int.ofNat (sphereSsum f w), sphereDprod f w + sphereSsum f w) :=
    Computable.pair hSInt hDen
  have htail := computable_sphereEuclPresenter hf
  refine computable_fin_lambda fun j => ?_
  refine Fin.cases ?_ ?_ j
  · exact h0.of_eq fun w => by simp [spherePresenter]
  · intro k
    exact (Computable.fin_app.comp htail (Computable.const k)).of_eq fun w => by
      simp [spherePresenter]

private theorem computable_sphereInitQ_presenter {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ} (hf : Computable f) :
    ∃ g : ℕ → Fin (asmDim d + 1) → ℤ × ℕ, Computable g ∧
      ∀ w i, sphereInitQ f w i = (g w i).1 / ((g w i).2 : ℚ) :=
  ⟨spherePresenter f, computable_spherePresenter hf, by
    intro w i
    rfl⟩

private lemma spherePresenter_den_ne_zero {d : ℕ}
    {f : ℕ → Fin d → ℤ × ℕ}
    (hden : ∀ w i, (f w i).2 ≠ 0) :
    ∀ w j, (spherePresenter f w j).2 ≠ 0 := by
  intro w j
  refine Fin.cases ?_ ?_ j
  · change sphereDprod f w + sphereSsum f w ≠ 0
    exact ne_of_gt (sphereDprod_add_sphereSsum_pos (f := f) hden w)
  · intro k
    refine Fin.addCases (m := 2) (n := asmTailDim d) ?_ ?_ k
    · intro c
      fin_cases c
      · simp [spherePresenter, sphereEuclPresenter]
      · change sphereDprod f w + sphereSsum f w ≠ 0
        exact ne_of_gt (sphereDprod_add_sphereSsum_pos (f := f) hden w)
    · intro tail
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
      · intro i
        simpa [spherePresenter, sphereEuclPresenter] using
          Nat.mul_ne_zero (hden w i)
            (ne_of_gt (sphereDprod_add_sphereSsum_pos (f := f) hden w))
      · intro tail2
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
        · intro i
          simpa [spherePresenter, sphereEuclPresenter] using
            Nat.mul_ne_zero (hden w i)
              (ne_of_gt (sphereDprod_add_sphereSsum_pos (f := f) hden w))
        · intro a
          fin_cases a
          simp [spherePresenter, sphereEuclPresenter]

private lemma tupleTraj_zero_eq_euclInitR
    {Conf : Type} [Primcodable Conf] {Mch : DiscreteMachine Conf}
    {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (I : HaltIndicator Mch d E)
    {A K : ℚ} {Mstep R : ℕ} {f : ℕ → Fin d → ℤ × ℕ} {w : ℕ}
    (sol : IteratorSol d S.evalF (A : ℝ) Mstep (orbitPoint Mch E w 0))
    (L : LatchSol sol I.evalH (K : ℝ) R)
    (hfval : ∀ w i, (f w i).2 ≠ 0 ∧
      E.enc (Mch.init w) i = ((f w i).1 : ℝ) / ((f w i).2 : ℝ)) :
    tupleTraj sol L 0 = euclInitR f w := by
  funext j
  refine Fin.addCases (m := 2) (n := asmTailDim d) ?_ ?_ j
  · intro k
    fin_cases k
    · change tupleTraj sol L 0 (asmS d) = euclInitR f w (asmS d)
      simp [tupleTraj_s, euclInitR_s]
    · change tupleTraj sol L 0 (asmC d) = euclInitR f w (asmC d)
      simp [tupleTraj_c, euclInitR_c]
  · intro tail
    refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
    · intro i
      change tupleTraj sol L 0 (asmZ i) = euclInitR f w (asmZ i)
      rw [tupleTraj_z, euclInitR_z, sol.init_z]
      simp [orbitPoint, hfval w i]
    · intro tail2
      refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
      · intro i
        change tupleTraj sol L 0 (asmU i) = euclInitR f w (asmU i)
        rw [tupleTraj_u, euclInitR_u, sol.init_u]
        simp [orbitPoint, hfval w i]
      · intro a
        fin_cases a
        change tupleTraj sol L 0 (asmA d) = euclInitR f w (asmA d)
        rw [tupleTraj_a, euclInitR_a, L.init_a]

theorem main_assembled
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
    (hsupply : ∀ (A : ℚ) (Mstep : ℕ) (w : ℕ), 0 < A →
      ∃ sol : IteratorSol d S.evalF (A : ℝ) Mstep
          (orbitPoint M.toDiscreteMachine E w 0),
        MovingBox S sol D_K) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  obtain ⟨I, A, Mstep, K, R, hApos, hKpos, hper⟩ :=
    assembled_euclidean_simulation M.toDiscreteMachine d E S stateCoord haltLevels
      hfin hlevels hmargin D_K hD hstepSmall hsupply
  let Xasm := assembledField d S.F I.H A K Mstep R
  obtain ⟨Y, _htang, htransfer⟩ := compactification_exists (asmDim d) Xasm
  obtain ⟨f, hf, hfval⟩ := hencoder
  have hden : ∀ w i, (f w i).2 ≠ 0 := fun w i => (hfval w i).1
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := asmDim d + 1
      vf := Y
      init := sphereInitQ f }
  choose sol L hhalt hnonhalt using hper
  have hode : ∀ w t, 0 ≤ t →
      HasDerivAt (tupleTraj (sol w) (L w))
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (tupleTraj (sol w) (L w) t) (Xasm i)) t := by
    intro w
    simpa [Xasm] using tupleTraj_ode S I (sol w) (L w)
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (tupleTraj (sol w) (L w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (tupleTraj (sol w) (L w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (tupleTraj (sol w) (L w)) (hode w)
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (tupleTraj (sol w) (L w) (s w τ))
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
    rw [tupleTraj_zero_eq_euclInitR S I (sol w) (L w) hfval]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    exact (sphereInitQ_cast_eq_stereo_euclInitR (f := f) hden w j).symm
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact stereo_abs_le_one _ _
  · refine ⟨spherePresenter f, computable_spherePresenter hf, ?_⟩
    intro w j
    refine ⟨spherePresenter_den_ne_zero (f := f) hden w j, rfl⟩
  · exact { hA := (asmA d).succ, h0 := 0, ne := by simp }
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
      (stereo_readout_transfer (tupleTraj (sol w) (L w) (s w τ)) (asmA d)).1
        (by simpa [tupleTraj_a] using hLatch)
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
      (stereo_readout_transfer (tupleTraj (sol w) (L w) (s w τ)) (asmA d)).2
        (by simpa [tupleTraj_a] using hLatch)
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg


end Ripple.BoundedUniversality.BGP
