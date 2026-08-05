/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17CustomLanding
import Tri.Lemma16To19Clock

/-!
# Raw physical clock of the custom Lemma 17 landing

The pure already-landed branch is the zero-remaining anchored frozen block.
The other branch is the ordinary projected physical stage.
-/

namespace Tri

noncomputable section

theorem lemma17TargetRemaining_eq_zero_of_le
    {n A : ℕ}
    (s : InfectionRevealPhysicalState n)
    (hlanded : A ≤ s.coarse.1.active) :
    lemma17TargetRemaining A s = 0 := by
  by_cases hactive : s.coarse.1.active ≤ A
  · have hspec :=
      lemma17TargetRemaining_spec s hactive
    omega
  · unfold lemma17TargetRemaining
    rw [dif_neg]
    intro hex
    obtain ⟨k, hk⟩ := hex
    omega

/-- The custom target landing is exactly one anchored raw physical block. -/
theorem lemma17TargetLandingKernel_eq_frozenPhysical
    (n : ℕ) (h3 : 3 ≤ n)
    (cStar A rho : ℕ)
    (s : InfectionRevealPhysicalState n) :
    lemma17TargetLandingKernel
        n h3 cStar A rho s =
      iter
        (freeze
          (PhysicalActivationCheckpoint s
            (lemma17TargetRemaining A s))
          (infectionRevealPhysicalStep n h3))
        (cStar * n) s := by
  by_cases hlanded : A ≤ s.coarse.1.active
  · have hzero :=
      lemma17TargetRemaining_eq_zero_of_le s hlanded
    rw [lemma17TargetLandingKernel, if_pos hlanded, hzero]
    exact
      (iter_freeze_of_mem s
        (show PhysicalActivationCheckpoint s 0 s by
          unfold PhysicalActivationCheckpoint
          omega)
        (cStar * n)).symm
  · unfold lemma17TargetLandingKernel
    rw [if_neg hlanded]
    exact
      lemma17PhysicalStageKernel_eq_frozenPhysical
        n h3 (lemma17TargetRemaining A s)
        A (19 * cStar * rho) (cStar * n) s

end

end Tri

#print axioms Tri.lemma17TargetRemaining_eq_zero_of_le
#print axioms
  Tri.lemma17TargetLandingKernel_eq_frozenPhysical
