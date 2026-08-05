/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionRevealPhysicalMixture

/-!
# Subtraction-free initial parameters for infection activation

The initial urn size and its two label counts are determined by the physical
state.  Only the complements leading to the first activation checkpoint need
to be chosen.  This package removes the repeated count-identification
hypotheses from downstream theorem interfaces.
-/

namespace Tri

namespace InfectionRevealPhysicalState

def initialNu
    {n : ℕ} (s : InfectionRevealPhysicalState n) : ℕ :=
  s.coarse.1.inactive

def initialR
    {n : ℕ} (s : InfectionRevealPhysicalState n) : ℕ :=
  s.coarse.1.iy

def initialB
    {n : ℕ} (s : InfectionRevealPhysicalState n) : ℕ :=
  s.coarse.1.ix

@[simp] theorem initialNu_eq_card
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    s.initialNu = s.inactive.ids.card :=
  s.hinactiveCard.symm

@[simp] theorem initialR_eq_card
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    s.initialR = s.inactive.yIds.card :=
  s.hinactiveY.symm

@[simp] theorem initialB_eq_card
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    s.initialB = s.inactive.xIds.card :=
  s.hinactiveX.symm

@[simp] theorem initialR_add_initialB
    {n : ℕ} (s : InfectionRevealPhysicalState n) :
    s.initialR + s.initialB = s.initialNu := by
  unfold initialR initialB initialNu
  simp only [InfectionCfg.inactive]
  omega

theorem initialNu_add_one
    {n : ℕ} (s : InfectionRevealPhysicalState n)
    (hseed : s.coarse.1.active = 1) :
    s.initialNu + 1 = n := by
  have htotal := s.coarse.2
  simp only [InfectionCfg.Inv, InfectionCfg.total] at htotal
  unfold initialNu
  omega

end InfectionRevealPhysicalState

/-- Minimal additive-witness package for the first activation checkpoint. -/
structure InfectionInitialParams
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (a16 : ℕ) where
  k16 : ℕ
  u16 : ℕ
  hseed : s.coarse.1.active = 1
  hk16 : k16 + 1 = a16
  hu16 : u16 + a16 = s.initialNu

namespace InfectionInitialParams

abbrev nu
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (_p : InfectionInitialParams s a16) : ℕ :=
  s.initialNu

abbrev R
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (_p : InfectionInitialParams s a16) : ℕ :=
  s.initialR

abbrev B
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (_p : InfectionInitialParams s a16) : ℕ :=
  s.initialB

@[simp] theorem hnu
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (p : InfectionInitialParams s a16) :
    p.nu + 1 = n :=
  s.initialNu_add_one p.hseed

@[simp] theorem hRB
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (p : InfectionInitialParams s a16) :
    p.R + p.B = p.nu :=
  s.initialR_add_initialB

@[simp] theorem hsplit16
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (p : InfectionInitialParams s a16) :
    p.u16 + p.k16 + 1 = p.nu := by
  rw [show p.u16 + p.k16 + 1 =
      p.u16 + (p.k16 + 1) by omega,
    p.hk16]
  exact p.hu16

theorem k16_pos
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (p : InfectionInitialParams s a16)
    (ha16 : 2 ≤ a16) :
    0 < p.k16 := by
  have hk := p.hk16
  omega

@[simp] theorem hx0
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (p : InfectionInitialParams s a16) :
    s.inactive.xIds.card = p.B :=
  s.hinactiveX

@[simp] theorem hy0
    {n : ℕ} {s : InfectionRevealPhysicalState n}
    {a16 : ℕ}
    (p : InfectionInitialParams s a16) :
    s.inactive.yIds.card = p.R :=
  s.hinactiveY

/-- Construct the checkpoint complements from the usual first-quarter
conditions. -/
noncomputable def mkOfQuarter
    {n a16 : ℕ}
    (s : InfectionRevealPhysicalState n)
    (hseed : s.coarse.1.active = 1)
    (ha16 : 1 ≤ a16)
    (hquarter : 4 * a16 ≤ n) :
    InfectionInitialParams s a16 := by
  have hnu := s.initialNu_add_one hseed
  have hk : ∃ k16 : ℕ, k16 + 1 = a16 := by
    obtain ⟨k16, hk16⟩ :=
      Nat.exists_eq_add_of_le ha16
    exact ⟨k16, by omega⟩
  have hfit : a16 ≤ s.initialNu := by
    omega
  have hu : ∃ u16 : ℕ,
      u16 + a16 = s.initialNu := by
    obtain ⟨u16, hu16⟩ :=
      Nat.exists_eq_add_of_le hfit
    exact ⟨u16, by omega⟩
  exact
    { k16 := Classical.choose hk
      u16 := Classical.choose hu
      hseed := hseed
      hk16 := Classical.choose_spec hk
      hu16 := Classical.choose_spec hu }

end InfectionInitialParams

end Tri

#print axioms Tri.InfectionRevealPhysicalState.initialNu_eq_card
#print axioms Tri.InfectionRevealPhysicalState.initialR_eq_card
#print axioms Tri.InfectionRevealPhysicalState.initialB_eq_card
#print axioms Tri.InfectionRevealPhysicalState.initialR_add_initialB
#print axioms Tri.InfectionRevealPhysicalState.initialNu_add_one
#print axioms Tri.InfectionInitialParams.hnu
#print axioms Tri.InfectionInitialParams.hRB
#print axioms Tri.InfectionInitialParams.hsplit16
#print axioms Tri.InfectionInitialParams.k16_pos
#print axioms Tri.InfectionInitialParams.hx0
#print axioms Tri.InfectionInitialParams.hy0
#print axioms Tri.InfectionInitialParams.mkOfQuarter
