/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma18PhysicalStage
import Tri.Lemma19FullPoolJoint

/-!
# Sequential handoff from Lemma 18 to Lemma 19

The decisive Lemma 18 stage has a random physical endpoint.  This file starts
the full-pool Lemma 19 continuation at that endpoint.  Its remaining
population and early immutable-label prefix are therefore endpoint-dependent.

The early prefix is represented by an additive witness
`lemma19EarlyPrefix z + 2 = z.inactive.ids.card`; no natural subtraction enters
the theorem statements.
-/

namespace Tri

open scoped ENNReal

noncomputable section

variable {α β : Type*}

/-- Bind two endpoint kernels.  The continuation estimate only has to hold on
positive-mass successful prefix endpoints. -/
theorem terminalFailureMass_bind_le_add_of_support
    (p : PMF α) (K : α → PMF β)
    (P : α → Prop) [DecidablePred P]
    (Q : β → Prop) [DecidablePred Q]
    (εpre εpost : ℝ≥0∞)
    (hpre : terminalFailureMass p P ≤ εpre)
    (hpost :
      ∀ z, p z ≠ 0 → P z →
        terminalFailureMass (K z) Q ≤ εpost) :
    terminalFailureMass (p.bind K) Q ≤ εpre + εpost := by
  rw [terminalFailureMass_bind]
  have hgood :
      ∑' z, (if P z then p z * εpost else 0) ≤ εpost := by
    calc
      ∑' z, (if P z then p z * εpost else 0)
          ≤ ∑' z, p z * εpost := by
            exact ENNReal.tsum_le_tsum fun z => by
              by_cases hz : P z <;> simp [hz]
      _ = (∑' z, p z) * εpost :=
        ENNReal.tsum_mul_right
      _ = εpost := by rw [PMF.tsum_coe, one_mul]
  calc
    expect p (fun z => terminalFailureMass (K z) Q)
        ≤
      ∑' z,
        ((if P z then 0 else p z) +
          (if P z then p z * εpost else 0)) := by
        unfold expect
        exact ENNReal.tsum_le_tsum fun z => by
          by_cases hp : p z = 0
          · simp [hp]
          · by_cases hz : P z
            · simp only [if_pos hz, zero_add]
              exact mul_le_mul_left' (hpost z hp hz) _
            · simp only [if_neg hz, add_zero]
              calc
                p z * terminalFailureMass (K z) Q
                    ≤ p z * 1 :=
                  mul_le_mul_left'
                    (terminalFailureMass_le_one (K z) Q) _
                _ = p z := mul_one _
    _ =
        terminalFailureMass p P +
          ∑' z, (if P z then p z * εpost else 0) := by
      unfold terminalFailureMass
      rw [← ENNReal.tsum_add]
    _ ≤ εpre + εpost :=
      add_le_add hpre hgood

/-- Early prefix leaving exactly two identities outside the prefix whenever
the inactive pool has at least two identities. -/
noncomputable def lemma19EarlyPrefix
    {n : ℕ} (s : InfectionRevealPhysicalState n) : ℕ :=
  by
    classical
    exact
      if h :
          ∃ k, k + 2 = s.inactive.ids.card
        then h.choose
        else 0

theorem lemma19EarlyPrefix_spec
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (hpool : 2 ≤ s.inactive.ids.card) :
    lemma19EarlyPrefix s + 2 = s.inactive.ids.card := by
  have hexists :
      ∃ k, k + 2 = s.inactive.ids.card := by
    obtain ⟨k, hk⟩ :=
      Nat.exists_eq_add_of_le hpool
    exact ⟨k, by omega⟩
  simp only [lemma19EarlyPrefix, dif_pos hexists]
  exact hexists.choose_spec

theorem lemma19EarlyPrefix_pos
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (hpool : 3 ≤ s.inactive.ids.card) :
    0 < lemma19EarlyPrefix s := by
  have hspec := lemma19EarlyPrefix_spec s (by omega)
  omega

/-- Endpoint-dependent full-activation continuation. -/
noncomputable def lemma19FullActivationKernel
    (n : ℕ) (h3 : 3 ≤ n) :
    InfectionRevealPhysicalState n →
      PMF (InfectionRevealPhysicalState n) :=
  fun s =>
    lemma17PhysicalStageKernel
      n h3 s.inactive.ids.card n 0
      (infectionLateStages s.inactive.ids.card *
        (1024 * n)) s

/-- Exact closed error supplied by the full-pool Lemma 19 continuation. -/
noncomputable def lemma19FullActivationError
    {n : ℕ} (H M : ℕ) (L : ℝ) (w : ℝ≥0∞)
    (s : InfectionRevealPhysicalState n) : ℝ≥0∞ :=
  ((infectionLateError s.inactive.ids.card +
      ((s.inactive.ids.card : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))))) +
      (infectionAllActiveCubeCompl n n +
          infectionAllActiveCube n n * w) ^
            (infectionLateStages s.inactive.ids.card *
              (1024 * n)) /
        w ^ (H + 1)) +
    ENNReal.ofReal
      (Real.exp
        (-((M : ℝ) ^ 2 / (8 * (H : ℝ)))))

/-- Every Lemma 18 entry endpoint with at least three inactive identities
satisfies the closed full-activation Lemma 19 estimate. -/
theorem lemma18PhysicalEntry_full_activation_closed
    (n A D H Dlabel M targetGap : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hA : 4 ≤ A)
    (hH : 0 < H)
    (hquarterA : n ≤ 4 * A)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (z : InfectionRevealPhysicalState n)
    (hz : Lemma18PhysicalEntryGood A (2 * D) z)
    (hpool3 : 3 ≤ z.inactive.ids.card) :
    terminalFailureMass
        (lemma19FullActivationKernel n h3 z)
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤ lemma19FullActivationError H M L w z := by
  have htotal :=
    infectionReveal_active_add_inactive z
  have hlabels :=
    InfectionInactiveView.xIds_card_add_yIds_card
      z.inactive
  have hprefix :=
    lemma19EarlyPrefix_spec z (by omega)
  have hprefixCast :
      (lemma19EarlyPrefix z : ℝ≥0∞) + 2 =
        (z.inactive.ids.card : ℝ≥0∞) := by
    exact_mod_cast hprefix
  have hprefixLabels :
      lemma19EarlyPrefix z + 2 =
        z.inactive.xIds.card +
          z.inactive.yIds.card := by
    omega
  have hscalePool :
      L *
          ((z.inactive.xIds.card +
            z.inactive.yIds.card : ℕ) : ℝ)
        ≤ ((Dlabel : ℝ) / 2) ^ 2 := by
    calc
      L *
            ((z.inactive.xIds.card +
              z.inactive.yIds.card : ℕ) : ℝ)
          ≤ L * (n : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hL
            exact_mod_cast
              (show
                z.inactive.xIds.card +
                    z.inactive.yIds.card ≤ n by
                omega)
      _ ≤ ((Dlabel : ℝ) / 2) ^ 2 := hscale
  have hclosed :=
    lemma19PhysicalStage_full_activation_closed
      n z.inactive.ids.card
      (lemma19EarlyPrefix z)
      z.inactive.xIds.card z.inactive.yIds.card
      A H (2 * D) Dlabel M targetGap L
      h3 hA hH z hz.1.1
      (by exact htotal)
      (hquarterA.trans
        (Nat.mul_le_mul_left 4 hz.1.1))
      hz.1.2 hbudget hDlabel
      (lemma19EarlyPrefix_pos z hpool3)
      hprefixLabels hz.2 rfl rfl hscalePool
      w hw1 hwt
  simpa [lemma19FullActivationKernel,
    lemma19FullActivationError, hprefixCast] using hclosed

/-- Uniform envelope of the endpoint-dependent full-activation error. -/
noncomputable def lemma19FullActivationUniformError
    (n H M : ℕ) (L : ℝ) (w : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ z : InfectionRevealPhysicalState n,
    lemma19FullActivationError H M L w z

/-- Sequential Lemma 18-to-19 handoff for an arbitrary decisive-stage law.
The support upper bound turns `A + 4 ≤ n` into the three-identity reserve
needed by the full-pool immutable-label estimate. -/
theorem lemma18Endpoint_then_full_activation_closed
    (n A D H Dlabel M targetGap : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (hA : 4 ≤ A)
    (hH : 0 < H)
    (hstageRoom : A + 4 ≤ n)
    (hquarterA : n ≤ 4 * A)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (p : PMF (InfectionRevealPhysicalState n))
    (εpre : ℝ≥0∞)
    (hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * D))
        ≤ εpre)
    (hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1) :
    terminalFailureMass
        (p.bind (lemma19FullActivationKernel n h3))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        εpre +
          lemma19FullActivationUniformError
            n H M L w := by
  apply
    terminalFailureMass_bind_le_add_of_support
      p (lemma19FullActivationKernel n h3)
      (Lemma18PhysicalEntryGood A (2 * D))
      (Lemma19PhysicalStageRangeGood n targetGap)
      εpre
      (lemma19FullActivationUniformError n H M L w)
      hpre
  intro z hzp hzgood
  have htotal :=
    infectionReveal_active_add_inactive z
  have hpool3 : 3 ≤ z.inactive.ids.card := by
    have hzupper := hupper z hzp
    omega
  exact
    (lemma18PhysicalEntry_full_activation_closed
      n A D H Dlabel M targetGap L
      h3 hA hH hquarterA hbudget hDlabel
      hL hscale w hw1 hwt z hzgood hpool3).trans
      (le_iSup
        (fun u : InfectionRevealPhysicalState n =>
          lemma19FullActivationError H M L w u) z)

/-- Fully instantiated decisive Lemma 18 stage followed by the closed
full-activation Lemma 19 continuation. -/
theorem lemma18Paper_then_full_activation_closed
    (n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
      a k u nu uMajor R B A cStar r
      H Dlabel M targetGap : ℕ)
    (L : ℝ)
    (h3 : 3 ≤ n)
    (ha : 4 ≤ a)
    (hquarterClock : 4 * a ≤ n)
    (hquarterLate : n ≤ 4 * A)
    (hAeq : A = 2 * a)
    (hstageRoom : A + 4 ≤ n)
    (hcStar : 128 ≤ cStar)
    (hprefixRadius : rhoPrefix + 1 = D)
    (hendRadius : rhoEnd + 1 = 12 * D)
    (hprefixQa :
      qPrefix * (k + 1) ≤ rhoPrefix ^ 2)
    (hendQa :
      qEnd * (k + 1) ≤ rhoEnd ^ 2)
    (hmajorQa :
      qMajor * ((k + 1) + 1) ≤
        (60 * d * D) ^ 2)
    (huk : u + k + 1 = nu)
    (hmajorWindow :
      uMajor + (k + 1) + 1 = nu)
    (hRB : R + B = nu)
    (hquarterPool : 4 * (k + 1) ≤ nu + 1)
    (hmajorQuarter :
      4 * ((k + 1) + 1) ≤ nu + 1)
    (hpoolScale : nu ≤ k * d)
    (hpoolGap : R + 60 * d * D ≤ B)
    (hmeanActive : A ^ 3 ≤ r * n ^ 2)
    (hguardScale : 60 * D ≤ a)
    (hreactionScale : 1200 * cStar * r ≤ 7 * a)
    (hH : 0 < H)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ 2 * D)
    (hDlabel : 0 < Dlabel)
    (hL : 0 ≤ L)
    (hscale :
      L * (n : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2)
    (w : ℝ≥0∞) (hw1 : 1 ≤ w) (hwt : w ≠ ⊤)
    (s : InfectionRevealPhysicalState n)
    (hstartActive : a ≤ s.coarse.1.active)
    (hanchorActive : s.coarse.1.active + k = A)
    (hprior :
      s.coarse.1.ay ≤ s.coarse.1.ax + 14 * D)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        ((lemma17PhysicalStageKernel
            n h3 k A (30 * D) (cStar * n) s).bind
          (lemma19FullActivationKernel n h3))
        (Lemma19PhysicalStageRangeGood n targetGap)
      ≤
        (lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor) +
          lemma19FullActivationUniformError
            n H M L w := by
  let p :=
    lemma17PhysicalStageKernel
      n h3 k A (30 * D) (cStar * n) s
  have hpre :
      terminalFailureMass p
          (Lemma18PhysicalEntryGood A (2 * D))
        ≤
          lemma18StageError
              qPrefix qEnd a cStar r D +
            lemma16UrnError qMajor := by
    simpa [p] using
      lemma18PhysicalEntry_paper
        n qPrefix qEnd qMajor rhoPrefix rhoEnd D d
        a k u nu uMajor R B A cStar r
        h3 ha hquarterClock hAeq hstageRoom hcStar
        hprefixRadius hendRadius hprefixQa hendQa
        hmajorQa huk hmajorWindow hRB hquarterPool
        hmajorQuarter hpoolScale hpoolGap hmeanActive
        hguardScale hreactionScale s hstartActive
        hanchorActive hprior hx0 hy0 hk0
  have hupper :
      ∀ z, p z ≠ 0 →
        z.coarse.1.active ≤ A + 1 := by
    intro z hz
    exact
      lemma17PhysicalStageKernel_active_le
        n h3 k A (30 * D) (cStar * n)
        s z hanchorActive (by simpa [p] using hz)
  simpa [p] using
    lemma18Endpoint_then_full_activation_closed
      n A D H Dlabel M targetGap L
      h3 (by omega) hH hstageRoom hquarterLate
      hbudget hDlabel hL hscale w hw1 hwt
      p
      (lemma18StageError
          qPrefix qEnd a cStar r D +
        lemma16UrnError qMajor)
      hpre hupper

end

end Tri

#print axioms Tri.terminalFailureMass_bind_le_add_of_support
#print axioms Tri.lemma19EarlyPrefix_spec
#print axioms Tri.lemma19EarlyPrefix_pos
#print axioms Tri.lemma18PhysicalEntry_full_activation_closed
#print axioms Tri.lemma18Endpoint_then_full_activation_closed
#print axioms Tri.lemma18Paper_then_full_activation_closed
