/-
Ripple.BoundedUniversality.BGP.ContractTrackingPhys
-------------------------------
The PHYSICAL (window-aligned) tracking interface for the warmed contract route,
replacing the false legacy `ContractWindowTube`/`ContractZWindowTube` (which
demand current-config tubes over the full read band — warm-budget-limited and
wrong-config).  Mirrors `SelectorMURecur`'s sampling scheme:

* `u` / branch extraction on the STRONG-hold window `[2πj+π/6, 2πj+π/2]`,
  target `enc (c j)` (current config; `bGateU` super-suppressed there for all j);
* `z` / readout on the physical read band `[2πj+5π/6, 2πj+7π/6]`, target
  `enc (c (j+1))` (NEXT config — the `SelectorZRead` correction);
* the weighted boundary error is sampled at the strong-window START `2πj+π/6`.

Design cross-checked with the repo-connected channel (pbook Q57); the new defs
use only real `RobustStepContract` primitives (`localExtract`/`localView` +
`local_extract_correct`, `epsF`, `D`).  These connect to the banked window-aligned
tubes in `ContractWindowAssembly` (`contract_u_hold_via_integral`,
`contract_z_read_next_config`).
-/

import Ripple.BoundedUniversality.BGP.ContractWindowAssembly

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators

noncomputable section

/-- Strong branch/hold sample time (selector's `selectorMUGateStart`). -/
def contractStrongStart (j : ℕ) : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi / 6

/-- End of the strong branch/hold window (selector's `selectorMUGateHold`). -/
def contractStrongHold (j : ℕ) : ℝ := 2 * Real.pi * (j : ℝ) + Real.pi / 2

/-- Next cycle's strong sample time (selector's `selectorMUNextStart`). -/
def contractNextStrongStart (j : ℕ) : ℝ :=
  2 * Real.pi * ((j + 1 : ℕ) : ℝ) + Real.pi / 6

/-- Branch/local-extraction window `[2πj+π/6, 2πj+π/2]` (closed, for the
Duhamel/gate-integral lemmas). -/
def contractStrongWindow (j : ℕ) : Set ℝ :=
  Set.Icc (contractStrongStart j) (contractStrongHold j)

/-- Physical read window `[2πj+5π/6, 2πj+7π/6]` (= `bgpSchedulePhys.zActiveWindow j`). -/
def contractReadWindow (j : ℕ) : Set ℝ :=
  Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
    (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)

variable {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
  {E : StackMachineEncoding d nS M}
  {p : DynGateParams} {sched : PhaseSchedule}
  {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}

/-- Physical boundary error: sample only the `u` register at `2πj+π/6` (mirrors
`SelectorMURecur.muBoundaryError`). -/
def contractUSampleError (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (j : ℕ) (i : Fin d) : ℝ :=
  |sol.u (contractStrongStart j) i - E.enc (c j) i|

/-- Physical weighted bound (current-config `u` sample error, weighted). -/
def ContractWeightedBoundPhys (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (depth : ℕ → Fin d → ℤ) (W : ℕ → Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin d,
    (E.k : ℝ) ^ depth j i * contractUSampleError (E := E) sol c j i ≤ W j i

/-- Current-config `u` tube on the strong branch/hold window. -/
def ContractStrongWindowTube (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (rLE : Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ t ∈ contractStrongWindow j, ∀ i : Fin d,
    |sol.u t i - E.enc (c j) i| ≤ rLE i

/-- NEXT-config `z` read tube on the physical read band (replaces the false
current-config `ContractZWindowTube`). -/
def ContractZReadNextTube (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (ρ : ℕ → Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ t ∈ contractReadWindow j, ∀ i : Fin d,
    |sol.z t i - E.enc (c (j + 1)) i| ≤ ρ j i

/-- Branch lock on the strong branch window: the local extraction matches the
current config's local view (derivable from the `u`-tube via
`local_extract_correct`). -/
def ContractBranchLockedOn (S : RobustStepContract M E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (j : ℕ) : Prop :=
  ∀ t ∈ contractStrongWindow j,
    S.localExtract (sol.μ t) (sol.u t) = S.localView (c j)

/-- Physical one-step recurrence at the strong sample times. -/
def ContractRecurrenceAtPhys (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (amp η : ℕ → Fin d → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin d,
    contractUSampleError (E := E) sol c (j + 1) i ≤
      amp j i * contractUSampleError (E := E) sol c j i + η j i

/-- **Branch lock from the `u`-tube** — `ContractBranchLockedOn` is DERIVED, not
assumed: `local_extract_correct` turns a strong-window `EncodingTube` into the
local-view match. -/
theorem contractBranchLockedOn_of_strongTube (S : RobustStepContract M E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (j : ℕ)
    (hmu : ∀ t ∈ contractStrongWindow j, S.mu_min ≤ sol.μ t)
    (htube : ∀ t ∈ contractStrongWindow j,
      EncodingTube E (S.radius (sol.μ t)) (c j) (sol.u t)) :
    ContractBranchLockedOn S sol c j := by
  intro t ht
  exact S.local_extract_correct (hmu t ht) (htube t ht)

/-- **`hbranch_of_window`** discharge: `ContractStrongWindowTube` (u within `rLE`)
+ `rLE ≤ radius(μ)` gives the strong-window `EncodingTube`, hence
`ContractBranchLockedOn` (Q57 §4). -/
theorem contract_branch_of_strong_window_from_radius (S : RobustStepContract M E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (rLE : Fin d → ℝ) (j : ℕ)
    (hmu : ∀ t ∈ contractStrongWindow j, S.mu_min ≤ sol.μ t)
    (hrad : ∀ t ∈ contractStrongWindow j, ∀ i, rLE i ≤ S.radius (sol.μ t))
    (htube : ContractStrongWindowTube (E := E) sol c rLE j) :
    ContractBranchLockedOn (E := E) S sol c j :=
  contractBranchLockedOn_of_strongTube S sol c j hmu
    (fun t ht i => le_trans (htube t ht i) (hrad t ht i))

/-- **`hstrong_window_hold`** (Q57 §6): the current-config u-tube on the strong
window, from the banked `contract_u_hold_via_integral` + `sin_nonneg_strong_hold`.
Carries the per-coord start bound `E0` (the u-sample error), the strong-window
z-bound `Dz`, and the warmed budget `E0 + Dz·leak ≤ rLE`. -/
theorem contract_strong_window_tube_of_inputs
    (S : RobustStepContract M E)
    (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (c : ℕ → Conf) (rLE : Fin d → ℝ) (j : ℕ)
    (hA : 0 ≤ p.A) (hcμ : 0 ≤ p.cμ) (hαinit : 0 ≤ sol.init_α) (hμinit : 0 ≤ sol.init_μ)
    (hlam_pos : 0 < DynChiLeak.leakLambda p.cμ p.cα p.L)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain)
    (hαcont : Continuous sol.α) (hμcont : Continuous sol.μ)
    (E0 Dz : Fin d → ℝ) (hDz : ∀ i, 0 ≤ Dz i)
    (hustart : ∀ i, |sol.u (contractStrongStart j) i - E.enc (c j) i| ≤ E0 i)
    (hzsup : ∀ t ∈ contractStrongWindow j, ∀ i,
      |sol.z t i - E.enc (c j) i| ≤ Dz i)
    (hbudget : ∀ i,
      E0 i + Dz i * (p.A * sol.init_α * Real.exp (-(sol.init_μ * (1 / 2 : ℝ) ^ p.L))
        * Real.exp (-(DynChiLeak.leakLambda p.cμ p.cα p.L * contractStrongStart j))
        / DynChiLeak.leakLambda p.cμ p.cα p.L) ≤ rLE i) :
    ContractStrongWindowTube (E := E) sol c rLE j := by
  intro t ht i
  have haStart : (0 : ℝ) ≤ contractStrongStart j := by
    unfold contractStrongStart; positivity
  have hab : contractStrongStart j ≤ t := ht.1
  have hsin : ∀ τ ∈ Set.Icc (contractStrongStart j) t, 0 ≤ Real.sin τ := by
    intro τ hτ
    exact sin_nonneg_strong_hold j
      (by simpa [contractStrongStart] using hτ.1)
      (by
        have := ht.2
        simpa [contractStrongStart, contractStrongHold] using le_trans hτ.2 this)
  have hzsup' : ∀ τ ∈ Set.Icc (contractStrongStart j) t,
      |sol.z τ i - E.enc (c j) i| ≤ Dz i := by
    intro τ hτ
    exact hzsup τ ⟨hτ.1, le_trans hτ.2 ht.2⟩ i
  have hu := contract_u_hold_via_integral sol i (E.enc (c j) i)
    (contractStrongStart j) t hab haStart hA hcμ hαinit hμinit hlam_pos hdom
    (uRate_continuous sol hαcont hμcont) hsin (hDz i) (hustart i) hzsup'
  exact le_trans hu (hbudget i)

/-- **`ContractZReadNextTube` glue** (Q57 §5): split the read band at `2πj+π`.
The right half `[2πj+π, 2πj+7π/6]` (Z-off, sin≤0) is the banked
`contract_z_read_next_config`; the left half `[2πj+5π/6, 2πj+π]` is the
write-settle fact (z already written to the next config — the analog of the
selector settled-radius decay), carried here as `hz_left`. -/
theorem contract_z_read_next_full
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (ρ : ℕ → Fin d → ℝ) (j : ℕ)
    (hz_left : ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi), ∀ i,
      |sol.z t i - E.enc (c (j + 1)) i| ≤ ρ j i)
    (hz_right : ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi)
        (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6), ∀ i,
      |sol.z t i - E.enc (c (j + 1)) i| ≤ ρ j i) :
    ContractZReadNextTube (E := E) sol c ρ j := by
  intro t ht i
  rw [contractReadWindow, Set.mem_Icc] at ht
  by_cases htm : t ≤ 2 * Real.pi * (j : ℝ) + Real.pi
  · exact hz_left t ⟨ht.1, htm⟩ i
  · exact hz_right t ⟨le_of_not_ge htm, ht.2⟩ i

/-- **`ContractRecurrenceAtPhys` one-step** (Q57 §7, contract analog of
`selector_MU_hrec_step_general`): the next-cycle u-sample error is bounded by a
triangle through the read-band end value — `|u(strong j+1)−enc(c(j+1))| ≤
|u(strong j+1)−z(readEnd)| + |z(readEnd)−enc(c(j+1))|`.  The first term is the
U-write/copy error `ω` (the analog of selector's `hwrite`, the one remaining
analytic producer); the second is the banked next-config z-read `ζ`.  `hbudget`
folds `ω+ζ` into `amp·sampleError + η`. -/
theorem contract_hrec_step_phys
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (amp η ζ ω : ℕ → Fin d → ℝ) (j : ℕ)
    (hznext : ContractZReadNextTube (E := E) sol c ζ j)
    (hu_write_next : ∀ i,
      |sol.u (contractStrongStart (j + 1)) i
        - sol.z (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) i| ≤ ω j i)
    (hbudget : ∀ i,
      ω j i + ζ j i ≤ amp j i * contractUSampleError (E := E) sol c j i + η j i) :
    ContractRecurrenceAtPhys (E := E) sol c amp η j := by
  intro i
  have hread_end :
      (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) ∈ contractReadWindow j := by
    rw [contractReadWindow, Set.mem_Icc]
    exact ⟨by nlinarith [Real.pi_pos], le_refl _⟩
  have hz := hznext (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) hread_end i
  have htri :
      |sol.u (contractStrongStart (j + 1)) i - E.enc (c (j + 1)) i|
        ≤ ω j i + ζ j i := by
    refine le_trans (abs_sub_le
      (sol.u (contractStrongStart (j + 1)) i)
      (sol.z (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6) i)
      (E.enc (c (j + 1)) i)) ?_
    exact add_le_add (hu_write_next i) hz
  calc contractUSampleError (E := E) sol c (j + 1) i
      = |sol.u (contractStrongStart (j + 1)) i - E.enc (c (j + 1)) i| := rfl
    _ ≤ ω j i + ζ j i := htri
    _ ≤ amp j i * contractUSampleError (E := E) sol c j i + η j i := hbudget i

/-- **`hweighted_step`** (Q57 §8): coordinatewise weighted-bound induction (the
contract analog of selector's `mu_weighted_step`).  Pure `zpow` algebra:
`amp ≤ k^delta`, `dep(j+1)=dep j − delta`, and `hWstep` close it. -/
theorem contract_weighted_step_phys
    (sol : DynContractIteratorSol (Fin d) p sched F)
    (c : ℕ → Conf) (hk : 1 < (E.k : ℝ))
    (dep delta : ℕ → Fin d → ℤ) (amp η Wbound : ℕ → Fin d → ℝ)
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hWstep : ∀ j i,
      Wbound j i + (E.k : ℝ) ^ dep (j + 1) i * η j i ≤ Wbound (j + 1) i)
    (hamp : ∀ j i, amp j i ≤ (E.k : ℝ) ^ delta j i)
    (j : ℕ)
    (hw : ContractWeightedBoundPhys (E := E) sol c dep Wbound j)
    (hr : ContractRecurrenceAtPhys (E := E) sol c amp η j) :
    ContractWeightedBoundPhys (E := E) sol c dep Wbound (j + 1) := by
  intro i
  have hk0 : (0 : ℝ) ≤ (E.k : ℝ) := (zero_lt_one.trans hk).le
  have hk_ne : (E.k : ℝ) ≠ 0 := (zero_lt_one.trans hk).ne'
  have hpow_nonneg : 0 ≤ (E.k : ℝ) ^ dep (j + 1) i := zpow_nonneg hk0 _
  have hrec_weak :
      contractUSampleError (E := E) sol c (j + 1) i ≤
        (E.k : ℝ) ^ delta j i * contractUSampleError (E := E) sol c j i + η j i := by
    have herr_nonneg : 0 ≤ contractUSampleError (E := E) sol c j i := abs_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (hamp j i) herr_nonneg
    have hr_i := hr i
    linarith
  have hstep :
      (E.k : ℝ) ^ dep (j + 1) i * contractUSampleError (E := E) sol c (j + 1) i ≤
        (E.k : ℝ) ^ dep j i * contractUSampleError (E := E) sol c j i +
          (E.k : ℝ) ^ dep (j + 1) i * η j i := by
    calc
      (E.k : ℝ) ^ dep (j + 1) i * contractUSampleError (E := E) sol c (j + 1) i
          ≤ (E.k : ℝ) ^ dep (j + 1) i *
              ((E.k : ℝ) ^ delta j i * contractUSampleError (E := E) sol c j i + η j i) :=
            mul_le_mul_of_nonneg_left hrec_weak hpow_nonneg
      _ = (E.k : ℝ) ^ (dep (j + 1) i + delta j i) *
              contractUSampleError (E := E) sol c j i +
            (E.k : ℝ) ^ dep (j + 1) i * η j i := by
            rw [mul_add, ← mul_assoc, ← zpow_add₀ hk_ne]
      _ = (E.k : ℝ) ^ dep j i * contractUSampleError (E := E) sol c j i +
            (E.k : ℝ) ^ dep (j + 1) i * η j i := by
            have hd : dep (j + 1) i + delta j i = dep j i := by
              rw [hdepth j i]; abel
            rw [hd]
  calc
    (E.k : ℝ) ^ dep (j + 1) i * contractUSampleError (E := E) sol c (j + 1) i
        ≤ (E.k : ℝ) ^ dep j i * contractUSampleError (E := E) sol c j i +
            (E.k : ℝ) ^ dep (j + 1) i * η j i := hstep
    _ ≤ Wbound j i + (E.k : ℝ) ^ dep (j + 1) i * η j i := by linarith [hw i]
    _ ≤ Wbound (j + 1) i := hWstep j i

end

end Ripple.BoundedUniversality.BGP
