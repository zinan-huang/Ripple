import Mathlib.Data.Fintype.Basic
import Mathlib.Data.NNRat.Order
import Ripple.sCRNUniversality.Core.Reaction

namespace Ripple.sCRNUniversality

structure Network (S : Type u) where
  I : Type v
  [fintypeI : Fintype I]
  rxn : I -> Reaction S

attribute [instance] Network.fintypeI

namespace Network

variable {S : Type u}

def allUnitRate (N : Network S) : Prop :=
  forall i : N.I, (N.rxn i).unitRate

def hasPositiveRates (N : Network S) : Prop :=
  forall i : N.I, (N.rxn i).hasPositiveRate

def equalRates (N : Network S) : Prop :=
  forall i j : N.I, (N.rxn i).k = (N.rxn j).k

end Network

namespace Reaction

variable {S : Type u}

theorem hasPositiveRate_of_unitRate {rho : Reaction S}
    (h : rho.unitRate) : rho.hasPositiveRate := by
  rw [unitRate] at h
  rw [hasPositiveRate, h]
  exact zero_lt_one

end Reaction

namespace Network

variable {S : Type u}

theorem hasPositiveRates_of_allUnitRate {N : Network S}
    (h : N.allUnitRate) : N.hasPositiveRates := by
  intro i
  exact Reaction.hasPositiveRate_of_unitRate (h i)

theorem equalRates_of_allUnitRate {N : Network S}
    (h : N.allUnitRate) : N.equalRates := by
  intro i j
  calc
    (N.rxn i).k = 1 := by
      simpa [Reaction.unitRate] using h i
    _ = (N.rxn j).k := by
      have hj : (N.rxn j).k = 1 := by
        simpa [Reaction.unitRate] using h j
      exact hj.symm

end Network

end Ripple.sCRNUniversality
