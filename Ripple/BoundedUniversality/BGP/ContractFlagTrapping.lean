/-
Ripple.BoundedUniversality.BGP.ContractFlagTrapping
-------------------------------
The [lo,hi] trapping invariant for the z-coordinate at a single coordinate,
via the banked `contract_z_hold_le` (ContractDuhamelHold).

**Key idea (pbook2 Q358):**  Center at M = (lo+hi)/2 with radius δ = (hi-lo)/2.
If z(a) ∈ [lo,hi] and w(τ) ∈ [lo,hi] for τ ∈ [a,b], then
  |z(a) - M| ≤ δ  and  |w(τ) - M| ≤ δ  for all τ ∈ [a,b],
so `contract_z_hold_le` gives |z(b) - M| ≤ δ, hence z(b) ∈ [lo,hi].

Specialization to [0,1]: M = 1/2, δ = 1/2.

No sorry/admit/native_decide/axiom.
-/

import Ripple.BoundedUniversality.BGP.ContractDuhamelHold

namespace Ripple.BoundedUniversality.BGP

open Real Set
open Ripple.BoundedUniversality.Core

noncomputable section

variable {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-! ## Generic interval helpers -/

/-- `x ∈ [lo,hi]` implies `|x - (lo+hi)/2| ≤ (hi-lo)/2`. -/
private theorem abs_sub_mid_le_of_mem_Icc {x lo hi : ℝ}
    (hx : x ∈ Icc lo hi) : |x - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- `|x - (lo+hi)/2| ≤ (hi-lo)/2` implies `x ∈ [lo,hi]`. -/
private theorem mem_Icc_of_abs_sub_mid_le {x lo hi : ℝ}
    (h : |x - (lo + hi) / 2| ≤ (hi - lo) / 2) : x ∈ Icc lo hi := by
  rw [abs_le] at h
  exact ⟨by linarith, by linarith⟩

/-! ## Generic interval trapping -/

/-- **Interval trapping for the z-coordinate.**  If `z(a) ∈ [lo,hi]` and the
moving target `w(τ) ∈ [lo,hi]` for all `τ ∈ [a,b]`, then `z(b) ∈ [lo,hi]`.

Centers the Duhamel hold at `M = (lo+hi)/2` with radius `δ = (hi-lo)/2`. -/
theorem contract_z_Icc_trapping
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (lo hi a b : ℝ) (hab : a ≤ b)
    (hk_cont : Continuous (zRate sol))
    (hA : 0 ≤ p.A) (hαnn : ∀ τ ∈ Icc a b, 0 ≤ sol.α τ)
    (hdom : Icc a b ⊆ sched.domain)
    (hzstart : sol.z a i ∈ Icc lo hi)
    (hwsup : ∀ τ ∈ Icc a b, sol.w τ i ∈ Icc lo hi) :
    sol.z b i ∈ Icc lo hi := by
  set M := (lo + hi) / 2
  set δ := (hi - lo) / 2
  have hzs : |sol.z a i - M| ≤ δ := abs_sub_mid_le_of_mem_Icc hzstart
  have hws : ∀ τ ∈ Icc a b, |sol.w τ i - M| ≤ δ :=
    fun τ hτ => abs_sub_mid_le_of_mem_Icc (hwsup τ hτ)
  have hhold := contract_z_hold_le sol i M a b hab hk_cont hA hαnn hdom hzs hws
  exact mem_Icc_of_abs_sub_mid_le hhold

/-! ## Specialization to `[0,1]` -/

/-- **Unit-interval trapping for the z-coordinate.**  If `z(a) ∈ [0,1]` and the
moving target `w(τ) ∈ [0,1]` for all `τ ∈ [a,b]`, then `z(b) ∈ [0,1]`.

This is `contract_z_Icc_trapping` with `lo = 0`, `hi = 1` (so `M = 1/2`,
`δ = 1/2`). -/
theorem contract_z_unit_trapping
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (i : Fin d) (a b : ℝ) (hab : a ≤ b)
    (hk_cont : Continuous (zRate sol))
    (hA : 0 ≤ p.A) (hαnn : ∀ τ ∈ Icc a b, 0 ≤ sol.α τ)
    (hdom : Icc a b ⊆ sched.domain)
    (hzstart : sol.z a i ∈ Icc 0 1)
    (hwsup : ∀ τ ∈ Icc a b, sol.w τ i ∈ Icc 0 1) :
    sol.z b i ∈ Icc 0 1 :=
  contract_z_Icc_trapping sol i 0 1 a b hab hk_cont hA hαnn hdom hzstart hwsup

end

end Ripple.BoundedUniversality.BGP
