import Ripple.sCRNUniversality.Computation.CTM.FourPhaseEncodingSafety

namespace Ripple.sCRNUniversality

namespace CTM

universe u

namespace FourPhaseSpecies

variable {Q : Type u}

theorem ctrlOf_injective :
    Function.Injective (ctrlOf (Q := Q)) := by
  intro st₁ st₂ h
  cases st₁ with
  | mk q₁ p₁ r₁ w₁ s₁ =>
    cases st₂ with
    | mk q₂ p₂ r₂ w₂ s₂ =>
      simp [ctrlOf] at h
      rcases h with ⟨hq, hp, hr, hw, hs⟩
      subst hq; subst hp; subst hr; subst hw; subst hs
      rfl

end FourPhaseSpecies

namespace FourPhaseEncoding

variable {Q : Type u} [DecidableEq Q] {s : Nat}

theorem enc_ctrlOf_eq_of_pos (c : MicroCfg Q s) (st : MicroState Q)
    (hpos : 0 < enc c (FourPhaseSpecies.ctrlOf st)) :
    st = c.state := by
  by_contra hne
  have hne' : FourPhaseSpecies.ctrlOf st ≠ FourPhaseSpecies.ctrlOf c.state := by
    intro heq
    exact hne (FourPhaseSpecies.ctrlOf_injective heq)
  have hzero : enc c (FourPhaseSpecies.ctrlOf st) = 0 := by
    cases st with
    | mk q phase readSymbol pendingWrite pendingState =>
      exact enc_ctrl_eq_zero_of_ne_ctrlOf c hne'
  rw [hzero] at hpos
  exact Nat.lt_irrefl 0 hpos

theorem guardedBy_enabledAt_enc_state_eq (c : MicroCfg Q s)
    (rho : Reaction (FourPhaseSpecies Q)) (st : MicroState Q)
    (hGuard : rho.GuardedBy (FourPhaseSpecies.ctrlOf st))
    (hEnabled : rho.enabled (enc c)) :
    st = c.state := by
  apply enc_ctrlOf_eq_of_pos c st
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one
    (le_trans hGuard (hEnabled _))

end FourPhaseEncoding

end CTM

end Ripple.sCRNUniversality
