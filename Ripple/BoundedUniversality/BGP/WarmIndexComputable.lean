import Ripple.BoundedUniversality.BGP.WarmIndexMU
import Ripple.BoundedUniversality.BGP.BGPParamsN

namespace Ripple.BoundedUniversality.BGP

noncomputable section

namespace MachineInstance

theorem cU_zero (w : ℕ) : MachineInstance.cU w 0 = M_U.init w := rfl

end MachineInstance

private def warmDepthRaw (c : MachineInstance.UConf) : ℕ :=
  let S := c.2.2
  max S.1.length (max S.2.1.length (max S.2.2.1.length S.2.2.2.length))

private theorem computable_warmDepthRaw :
    Computable warmDepthRaw := by
  have hS : Computable (fun c : MachineInstance.UConf => c.2.2) :=
    Computable.snd.comp Computable.snd
  have h0 : Computable (fun c : MachineInstance.UConf => c.2.2.1.length) :=
    Computable.list_length.comp (Computable.fst.comp hS)
  have h1 : Computable (fun c : MachineInstance.UConf => c.2.2.2.1.length) :=
    Computable.list_length.comp (Computable.fst.comp (Computable.snd.comp hS))
  have h2 : Computable (fun c : MachineInstance.UConf => c.2.2.2.2.1.length) :=
    Computable.list_length.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hS)))
  have h3 : Computable (fun c : MachineInstance.UConf => c.2.2.2.2.2.length) :=
    Computable.list_length.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hS)))
  have h23 : Computable
      (fun c : MachineInstance.UConf => max c.2.2.2.2.1.length c.2.2.2.2.2.length) :=
    Primrec.nat_max.to_comp.comp h2 h3
  have h123 : Computable
      (fun c : MachineInstance.UConf =>
        max c.2.2.2.1.length (max c.2.2.2.2.1.length c.2.2.2.2.2.length)) :=
    Primrec.nat_max.to_comp.comp h1 h23
  exact (Primrec.nat_max.to_comp.comp h0 h123).of_eq fun c => by
    simp [warmDepthRaw]

private theorem depthCoordU_toNat_le_warmDepthRaw
    (c : MachineInstance.UConf) (i : Fin MachineInstance.d_U) :
    Int.toNat (MachineInstance.depthCoordU c i) ≤ warmDepthRaw c := by
  fin_cases i <;>
    simp [MachineInstance.d_U, MachineInstance.depthCoordU,
      MachineInstance.coordStackIndexU, MachineInstance.coordStackKindU,
      MachineInstance.mainStackCoordU, MachineInstance.revStackCoordU,
      MachineInstance.auxStackCoordU, MachineInstance.dataStackCoordU,
      MachineInstance.stackIndexU, MachineInstance.stackKindOfIndexU,
      MachineInstance.indexedStackU, MachineInstance.mainStackU,
      MachineInstance.revStackU, MachineInstance.auxStackU,
      MachineInstance.dataStackU, warmDepthRaw]

private theorem warmDepthRaw_le_depthSup (c : MachineInstance.UConf) :
    warmDepthRaw c ≤
      Finset.univ.sup (fun i : Fin MachineInstance.d_U =>
        Int.toNat (MachineInstance.depthCoordU c i)) := by
  unfold warmDepthRaw
  apply max_le
  · simpa [MachineInstance.depthCoordU, MachineInstance.indexedStackU,
      MachineInstance.mainStackU] using
      (Finset.le_sup (f := fun i : Fin MachineInstance.d_U =>
        Int.toNat (MachineInstance.depthCoordU c i))
        (by simp : MachineInstance.mainStackCoordU ∈ (Finset.univ : Finset _)))
  · apply max_le
    · simpa [MachineInstance.depthCoordU, MachineInstance.indexedStackU,
        MachineInstance.revStackU] using
        (Finset.le_sup (f := fun i : Fin MachineInstance.d_U =>
          Int.toNat (MachineInstance.depthCoordU c i))
          (by simp : MachineInstance.revStackCoordU ∈ (Finset.univ : Finset _)))
    · apply max_le
      · simpa [MachineInstance.depthCoordU, MachineInstance.indexedStackU,
          MachineInstance.auxStackU] using
          (Finset.le_sup (f := fun i : Fin MachineInstance.d_U =>
            Int.toNat (MachineInstance.depthCoordU c i))
            (by simp : MachineInstance.auxStackCoordU ∈ (Finset.univ : Finset _)))
      · simpa [MachineInstance.depthCoordU, MachineInstance.indexedStackU,
          MachineInstance.dataStackU] using
          (Finset.le_sup (f := fun i : Fin MachineInstance.d_U =>
            Int.toNat (MachineInstance.depthCoordU c i))
            (by simp : MachineInstance.dataStackCoordU ∈ (Finset.univ : Finset _)))

private theorem depthSup_eq_warmDepthRaw (c : MachineInstance.UConf) :
    (Finset.univ.sup (fun i : Fin MachineInstance.d_U =>
      Int.toNat (MachineInstance.depthCoordU c i))) = warmDepthRaw c := by
  apply le_antisymm
  · exact Finset.sup_le fun i _ => depthCoordU_toNat_le_warmDepthRaw c i
  · exact warmDepthRaw_le_depthSup c

private theorem inputDepthU_eq_warmDepthRaw (w : ℕ) :
    MachineInstance.inputDepthU w = warmDepthRaw (MachineInstance.M_U.init w) := by
  rw [MachineInstance.inputDepthU]
  simp [MachineInstance.depthHeightU, MachineInstance.depthU,
    MachineInstance.cU_zero, depthSup_eq_warmDepthRaw]

theorem inputDepthU_computable : Computable MachineInstance.inputDepthU := by
  exact (computable_warmDepthRaw.comp MachineInstance.M_U.init_computable).of_eq
    fun w => by
      rw [inputDepthU_eq_warmDepthRaw]

private def warmPow6Nat : ℕ → ℕ :=
  Nat.rec 1 (fun _ ih => 6 * ih)

private theorem computable_warmPow6Nat : Computable warmPow6Nat := by
  have hstep : Primrec₂ (fun _ ih : ℕ => 6 * ih) :=
    Primrec.nat_mul.comp₂ (Primrec₂.const 6) Primrec₂.right
  exact (Primrec.nat_rec₁ 1 hstep).to_comp

private theorem warmPow6Nat_eq (w : ℕ) : warmPow6Nat w = 6 ^ w := by
  induction w with
  | zero => rfl
  | succ w ih =>
      calc
        warmPow6Nat (w + 1) = 6 * warmPow6Nat w := rfl
        _ = 6 * 6 ^ w := by rw [ih]
        _ = 6 ^ (w + 1) := by
          rw [pow_succ]
          exact Nat.mul_comm 6 (6 ^ w)

private def warmSixthPower (n : ℕ) : ℕ :=
  (((n * n) * n) * n) * n * n

private theorem computable_warmSixthPower : Computable warmSixthPower := by
  have h2 : Computable (fun n : ℕ => n * n) :=
    Primrec.nat_mul.to_comp.comp Computable.id Computable.id
  have h3 : Computable (fun n : ℕ => (n * n) * n) :=
    Primrec.nat_mul.to_comp.comp h2 Computable.id
  have h4 : Computable (fun n : ℕ => ((n * n) * n) * n) :=
    Primrec.nat_mul.to_comp.comp h3 Computable.id
  have h5 : Computable (fun n : ℕ => (((n * n) * n) * n) * n) :=
    Primrec.nat_mul.to_comp.comp h4 Computable.id
  exact (Primrec.nat_mul.to_comp.comp h5 Computable.id).of_eq fun n => by
    simp [warmSixthPower]

private theorem warmSixthPower_eq (n : ℕ) : warmSixthPower n = n ^ 6 := by
  simp [warmSixthPower, pow_succ]

theorem bgpScaleW_computable : Computable bgpScaleW := by
  have hInputLen : Computable (fun w : ℕ => MachineInstance.inputLenU 1 w) := by
    exact (Primrec.nat_add.to_comp.comp inputDepthU_computable (Computable.const 1)).of_eq
      fun w => by
        simp [MachineInstance.inputLenU]
  have hExp : Computable (fun w : ℕ => MachineInstance.inputLenU 1 w + 220) :=
    Primrec.nat_add.to_comp.comp hInputLen (Computable.const 220)
  have hPow : Computable (fun w : ℕ => warmPow6Nat (MachineInstance.inputLenU 1 w + 220)) :=
    computable_warmPow6Nat.comp hExp
  have hHead : Computable bgpHeadStartN :=
    hPow.of_eq fun w => by simp [bgpHeadStartN, warmPow6Nat_eq]
  exact (Primrec.nat_mul.to_comp.comp (Computable.const bgpScale) hHead).of_eq
    fun w => by simp [bgpScaleW]

private def paper3WarmGainQNWPresenter (w : ℕ) : ℤ × ℕ :=
  (Int.ofNat (1734736490 * bgpScaleW w ^ 6 * warmPow6Nat w), 1)

private theorem computable_paper3WarmGainQNWPresenter :
    Computable paper3WarmGainQNWPresenter := by
  have hscalePow : Computable (fun w : ℕ => bgpScaleW w ^ 6) := by
    exact (computable_warmSixthPower.comp bgpScaleW_computable).of_eq
      fun w => by rw [warmSixthPower_eq]
  have hbase : Computable (fun w : ℕ => 1734736490 * bgpScaleW w ^ 6) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 1734736490) hscalePow
  have hnumNat : Computable
      (fun w : ℕ => 1734736490 * bgpScaleW w ^ 6 * warmPow6Nat w) :=
    Primrec.nat_mul.to_comp.comp hbase computable_warmPow6Nat
  have hnumInt : Computable
      (fun w : ℕ => Int.ofNat (1734736490 * bgpScaleW w ^ 6 * warmPow6Nat w)) :=
    computable_int_ofNat.comp hnumNat
  exact (Computable.pair hnumInt (Computable.const 1)).of_eq fun w => rfl

theorem paper3WarmGainQNW_presented :
    ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧ paper3WarmGainQNW w = (g w).1 / ((g w).2 : ℚ) := by
  refine ⟨paper3WarmGainQNWPresenter, computable_paper3WarmGainQNWPresenter, ?_⟩
  intro w
  refine ⟨one_ne_zero, ?_⟩
  have hval : paper3WarmGainQNW w =
      ((1734736490 * bgpScaleW w ^ 6 * warmPow6Nat w : ℕ) : ℚ) := by
    unfold paper3WarmGainQNW
    rw [paper3WarmGainCNW_nat_eq, warmPow6Nat_eq]
    push_cast
    ring
  rw [hval]
  show ((1734736490 * bgpScaleW w ^ 6 * warmPow6Nat w : ℕ) : ℚ) =
    ((Int.ofNat (1734736490 * bgpScaleW w ^ 6 * warmPow6Nat w) : ℤ) : ℚ) /
      ((1 : ℕ) : ℚ)
  rw [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_one, div_one]

private def scaledBgpScaleWPresenter (c w : ℕ) : ℤ × ℕ :=
  (Int.ofNat (c * bgpScaleW w), 1)

private theorem computable_scaledBgpScaleWPresenter (c : ℕ) :
    Computable (scaledBgpScaleWPresenter c) := by
  have hnumNat : Computable (fun w : ℕ => c * bgpScaleW w) :=
    Primrec.nat_mul.to_comp.comp (Computable.const c) bgpScaleW_computable
  have hnumInt : Computable (fun w : ℕ => Int.ofNat (c * bgpScaleW w)) :=
    computable_int_ofNat.comp hnumNat
  exact (Computable.pair hnumInt (Computable.const 1)).of_eq fun w => rfl

theorem scaledBgpScaleW_presented (c : ℕ) :
    ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧
        ((c * bgpScaleW w : ℕ) : ℚ) = (g w).1 / ((g w).2 : ℚ) := by
  refine ⟨scaledBgpScaleWPresenter c, computable_scaledBgpScaleWPresenter c, ?_⟩
  intro w
  refine ⟨one_ne_zero, ?_⟩
  show ((c * bgpScaleW w : ℕ) : ℚ) =
    ((Int.ofNat (c * bgpScaleW w) : ℤ) : ℚ) / ((1 : ℕ) : ℚ)
  rw [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_one, div_one]

theorem cmuInitQ_presented :
    ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧
        ((1000 * bgpScaleW w : ℕ) : ℚ) = (g w).1 / ((g w).2 : ℚ) :=
  scaledBgpScaleW_presented 1000

theorem calphaInitQ_presented :
    ∃ g : ℕ → ℤ × ℕ, Computable g ∧
      ∀ w, (g w).2 ≠ 0 ∧
        ((300 * bgpScaleW w : ℕ) : ℚ) = (g w).1 / ((g w).2 : ℚ) :=
  scaledBgpScaleW_presented 300

end

end Ripple.BoundedUniversality.BGP
