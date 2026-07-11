/-
Ripple.BoundedUniversality.BGP.RobustStepContract
-----------------------------
Interface foundation for the k-Lipschitz RobustStep layer.

Design notes read for this file:
* notes/gpt-life2-klipschitz-interface.md
* notes/gpt-life1-cycletracking.md
* notes/gpt-life-p13-encoding.md

Documented choices:
* The step map is a mu-indexed evaluated family
  `F : R -> (Fin d -> R) -> Fin d -> R`, not a fixed
  `MvPolynomial`.  This is the interface needed by the dynamic gate
  driver, where the precision parameter is supplied as `mu(t) = c0*t`.
  The notes also warn that exact infinite-lattice top-digit extraction
  cannot be done by one fixed polynomial, so polynomial realization data
  belongs below this contract.
* The extraction data is abstract: a contract supplies a finite local
  view type, a discrete `localView`, and a real-valued `localExtract`
  that agrees with it inside the tube.
* Reset coordinates still receive `coordDelta = 0` for compatibility
  with `DepthBudget`; their contract multiplier is `0`, so the
  zpow recurrence follows by weakening with the nonnegative previous
  coordinate error.
-/

import Ripple.BoundedUniversality.BGP.Interfaces
import Ripple.BoundedUniversality.BGP.DepthBudget

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## Four-coordinate demo layout and stack moves -/

/-- The four coordinates are `(left stack, scanned symbol, right stack, state)`. -/
def leftStackCoord : Fin 4 := ⟨0, by decide⟩

/-- The scanned-symbol coordinate. -/
def symbolCoord : Fin 4 := ⟨1, by decide⟩

/-- The right-stack coordinate. -/
def rightStackCoord : Fin 4 := ⟨2, by decide⟩

/-- The finite-state coordinate. -/
def stateCoord : Fin 4 := ⟨3, by decide⟩

/-- Number of stack coordinates in the legacy two-stack demo layout. -/
def demoStackCount : ℕ := 2

/-- Left stack index in the legacy two-stack demo layout. -/
def demoLeftStack : Fin demoStackCount := ⟨0, by decide⟩

/-- Right stack index in the legacy two-stack demo layout. -/
def demoRightStack : Fin demoStackCount := ⟨1, by decide⟩

/-- Coordinate projection for a stack index in the legacy four-coordinate demo. -/
def demoStackCoord (s : Fin demoStackCount) : Fin 4 :=
  if s.val = 0 then leftStackCoord else rightStackCoord

/-- A stack action during one discrete step. -/
inductive StackMove where
  | pop
  | push
  | stay
  deriving DecidableEq

namespace StackMove

/-- Depth/error exponent: pop exposes one digit, push buries one digit. -/
def delta : StackMove → ℤ
  | pop => 1
  | push => -1
  | stay => 0

end StackMove

/-- Which stack index, if any, is represented by a legacy four-coordinate coordinate. -/
def demoCoordStackIndex (i : Fin 4) : Option (Fin demoStackCount) :=
  if i = leftStackCoord then
    some demoLeftStack
  else if i = rightStackCoord then
    some demoRightStack
  else
    none

/-! ## Encoding contract -/

/--
Four-coordinate stack-machine encoding over an honest discrete machine.

The stack coordinates use base `k` with legal digits avoiding the top
digit `k-1`.  The field `stack_le_missingDigit` is the P13 missing-digit
gap bound: legal stack fractions lie below `(k-2)/(k-1)`, hence strictly
below `(k-1)/k`.
-/
structure StackMachineEncoding (d nS : ℕ) {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) where
  enc : Conf → Fin d → ℝ
  stackCoord : Fin nS → Fin d
  symbolCoord : Fin d
  stateCoord : Fin d
  coordStackIndex : Fin d → Option (Fin nS)
  coordStackIndex_stack : ∀ s, coordStackIndex (stackCoord s) = some s
  k : ℕ
  hk : 4 ≤ k
  moveType : Conf → Fin nS → StackMove
  stack_nonneg : ∀ c s, 0 ≤ enc c (stackCoord s)
  stack_le_missingDigit :
    ∀ c s, enc c (stackCoord s) ≤ ((k : ℝ) - 2) / ((k : ℝ) - 1)
  symbolCode : Conf → ℤ
  stateCode : Conf → ℤ
  symbol_enc : ∀ c, enc c symbolCoord = (symbolCode c : ℝ)
  state_enc : ∀ c, enc c stateCoord = (stateCode c : ℝ)
  symbol_margin : ∀ {c c'}, symbolCode c ≠ symbolCode c' →
    (1 : ℝ) ≤ |(symbolCode c : ℝ) - (symbolCode c' : ℝ)|
  state_margin : ∀ {c c'}, stateCode c ≠ stateCode c' →
    (1 : ℝ) ≤ |(stateCode c : ℝ) - (stateCode c' : ℝ)|

namespace StackMachineEncoding

variable {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}

/-- The base is strictly larger than one, in real form for zpow estimates. -/
theorem one_lt_base_real (E : StackMachineEncoding d nS M) : 1 < (E.k : ℝ) := by
  have hkNat : (1 : ℕ) < E.k := lt_of_lt_of_le (by norm_num) E.hk
  exact_mod_cast hkNat

private theorem stack_gap_lt {k : ℕ} (hk : 4 ≤ k) :
    ((k : ℝ) - 2) / ((k : ℝ) - 1) < ((k : ℝ) - 1) / (k : ℝ) := by
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by linarith
  have hkm1 : 0 < (k : ℝ) - 1 := by linarith
  rw [div_lt_div_iff₀ hkm1 hkpos]
  nlinarith

/-- Legal stack fractions lie in the P13 missing-digit range `[0, (k-1)/k)`. -/
theorem stack_lt_missing_digit_gap (E : StackMachineEncoding d nS M) (c : Conf)
    (s : Fin nS) :
    E.enc c (E.stackCoord s) < ((E.k : ℝ) - 1) / (E.k : ℝ) :=
  (E.stack_le_missingDigit c s).trans_lt (stack_gap_lt E.hk)

/-- Stack exponent for one machine-level stack at one configuration. -/
def stackDelta (E : StackMachineEncoding d nS M) (c : Conf) (s : Fin nS) : ℤ :=
  (E.moveType c s).delta

/-- Stack multiplier, spelled exactly as the depth budget expects. -/
def stackMultiplier (E : StackMachineEncoding d nS M) (c : Conf) (s : Fin nS) : ℝ :=
  (E.k : ℝ) ^ E.stackDelta c s

/-- Per-coordinate depth exponent.  Reset coordinates use exponent zero. -/
def coordDelta (E : StackMachineEncoding d nS M) (c : Conf) (i : Fin d) : ℤ :=
  match E.coordStackIndex i with
  | some s => E.stackDelta c s
  | none => 0

/--
Per-coordinate diagonal multiplier in the robust-step contract.  Stack
coordinates use `k ^ delta`; reset coordinates use multiplier zero.
-/
def coordMultiplier (E : StackMachineEncoding d nS M) (c : Conf) (i : Fin d) : ℝ :=
  match E.coordStackIndex i with
  | some s => E.stackMultiplier c s
  | none => 0

theorem coordMultiplier_stack (E : StackMachineEncoding d nS M) (c : Conf)
    (s : Fin nS) :
    E.coordMultiplier c (E.stackCoord s) = (E.k : ℝ) ^ E.stackDelta c s := by
  simp [coordMultiplier, stackMultiplier, E.coordStackIndex_stack s]

/-- The contract multiplier weakens to the zpow multiplier used by DepthBudget. -/
theorem coordMultiplier_error_le_zpow (E : StackMachineEncoding d nS M)
    (c : Conf) (i : Fin d) (x : Fin d → ℝ) :
    E.coordMultiplier c i * |x i - E.enc c i| ≤
      (E.k : ℝ) ^ E.coordDelta c i * |x i - E.enc c i| := by
  unfold coordMultiplier coordDelta stackMultiplier
  cases h : E.coordStackIndex i with
  | none =>
      simp [abs_nonneg]
  | some s =>
      simp

end StackMachineEncoding

/-! ## Stack-count smoke specializations -/

/-- Contract encoding specialized to four machine-level stacks. -/
abbrev FourStackMachineEncoding (d : ℕ) {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) : Type :=
  StackMachineEncoding d 4 M

/-- Smoke check: a four-stack encoding exposes genuine `Fin 4` stack indices. -/
theorem four_stack_encoding_instantiates
    {d : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : FourStackMachineEncoding d M) (s : Fin 4) :
    E.coordStackIndex (E.stackCoord s) = some s :=
  E.coordStackIndex_stack s

/-! ## Robust-step contract -/

/-- Coordinatewise tube around the exact encoding. -/
def EncodingTube {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M) (rho : ℝ) (c : Conf) (x : Fin d → ℝ) : Prop :=
  ∀ i, |x i - E.enc c i| ≤ rho

/--
The k-Lipschitz RobustStep contract box.

`radius` is generalized from the note's model
`1/(2*k^2) - exp(-mu)`: the interface only needs monotonicity and
eventual positivity.  `F` is evaluated at a precision parameter `mu`,
matching the dynamic-gate driver.
-/
structure RobustStepContract {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (E : StackMachineEncoding d nS M) where
  mu_min : ℝ
  radius : ℝ → ℝ
  radius_mono : ∀ {mu nu}, mu_min ≤ mu → mu ≤ nu → radius mu ≤ radius nu
  radius_pos : ∀ mu, mu_min ≤ mu → 0 < radius mu
  FiniteData : Type
  finiteDataDecidableEq : DecidableEq FiniteData
  localView : Conf → FiniteData
  localExtract : ℝ → (Fin d → ℝ) → FiniteData
  F : ℝ → (Fin d → ℝ) → Fin d → ℝ
  epsF : ℝ → Fin d → ℝ
  D : ℝ
  D_nonneg : 0 ≤ D
  local_extract_correct :
    ∀ {mu c x}, mu_min ≤ mu → EncodingTube E (radius mu) c x →
      localExtract mu x = localView c
  diagonal_bound :
    ∀ {mu c x}, mu_min ≤ mu → EncodingTube E (radius mu) c x → ∀ i,
      |F mu x i - E.enc (M.step c) i| ≤
        E.coordMultiplier c i * |x i - E.enc c i| + epsF mu i
  displacement_bound :
    ∀ {mu c x}, mu_min ≤ mu → EncodingTube E (radius mu) c x → ∀ i,
      |F mu x i - x i| ≤ D

namespace RobustStepContract

variable {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
variable {E : StackMachineEncoding d nS M}

/-- Diagonal contract weakened into the exact zpow recurrence shape. -/
theorem sampled_zpow_bound (S : RobustStepContract M E)
    {mu : ℝ} {c : Conf} {x : Fin d → ℝ}
    (hmu : S.mu_min ≤ mu) (htube : EncodingTube E (S.radius mu) c x)
    (i : Fin d) :
    |S.F mu x i - E.enc (M.step c) i| ≤
      (E.k : ℝ) ^ E.coordDelta c i * |x i - E.enc c i| + S.epsF mu i := by
  exact (S.diagonal_bound hmu htube i).trans
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (E.coordMultiplier_error_le_zpow c i x) (S.epsF mu i))

end RobustStepContract

/-! ## Cycle-tracking triangle chain -/

/-- Boundary coordinate error at cycle `j`. -/
def boundaryError {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M) (u : ℕ → Fin d → ℝ) (c : ℕ → Conf)
    (j : ℕ) (i : Fin d) : ℝ :=
  |u j i - E.enc (c j) i|

/-- Additive error produced by RobustStep plus the two half-cycle tracking errors. -/
def cycleEta {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M} (S : RobustStepContract M E)
    (mu kappa chi : ℕ → ℝ) (j : ℕ) (i : Fin d) : ℝ :=
  S.epsF (mu j) i + 2 * S.D * (kappa j + chi j)

/--
C3, pure triangle-chain form.  The hypotheses are the branch-locked
diagonal robust-step estimate at the sampled value and the two
half-cycle tracking estimates.
-/
theorem cycle_triangle_refined_recurrence
    {base D : ℝ} {delta : ℤ}
    {uNext zNext target nextExact prevErr eps kappa chi : ℝ}
    (hdiag : |target - nextExact| ≤ base ^ delta * prevErr + eps)
    (hz : |zNext - target| ≤ D * (kappa + chi))
    (hu : |uNext - zNext| ≤ D * (kappa + chi)) :
    |uNext - nextExact| ≤
      base ^ delta * prevErr + (eps + 2 * D * (kappa + chi)) := by
  have htri₁ : |uNext - nextExact| ≤ |uNext - zNext| + |zNext - nextExact| := by
    have hsum : uNext - nextExact = (uNext - zNext) + (zNext - nextExact) := by ring
    rw [hsum]
    exact abs_add_le _ _
  have htri₂ : |zNext - nextExact| ≤ |zNext - target| + |target - nextExact| := by
    have hsum : zNext - nextExact = (zNext - target) + (target - nextExact) := by ring
    rw [hsum]
    exact abs_add_le _ _
  calc
    |uNext - nextExact|
        ≤ |uNext - zNext| + |zNext - nextExact| := htri₁
    _ ≤ D * (kappa + chi) + (|zNext - target| + |target - nextExact|) := by
        exact add_le_add hu htri₂
    _ ≤ D * (kappa + chi) +
          (D * (kappa + chi) + (base ^ delta * prevErr + eps)) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (add_le_add hz hdiag) (D * (kappa + chi))
    _ = base ^ delta * prevErr + (eps + 2 * D * (kappa + chi)) := by ring

/--
C3, contract-specialized form.  This is the recurrence that plugs
directly into `DepthBudget.refined_unrolled` and
`DepthBudget.depth_aware_all_time_tube`.
-/
theorem contract_cycle_refined_recurrence
    {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M} (S : RobustStepContract M E)
    (u z : ℕ → Fin d → ℝ) (c : ℕ → Conf) (mu kappa chi : ℕ → ℝ)
    (i : Fin d)
    (hcstep : ∀ j, c (j + 1) = M.step (c j))
    (hmu : ∀ j, S.mu_min ≤ mu j)
    (htube : ∀ j, EncodingTube E (S.radius (mu j)) (c j) (u j))
    (htrack_z : ∀ j,
      |z (j + 1) i - S.F (mu j) (u j) i| ≤ S.D * (kappa j + chi j))
    (htrack_u : ∀ j,
      |u (j + 1) i - z (j + 1) i| ≤ S.D * (kappa j + chi j)) :
    ∀ j,
      boundaryError E u c (j + 1) i ≤
        (E.k : ℝ) ^ E.coordDelta (c j) i * boundaryError E u c j i +
          cycleEta S mu kappa chi j i := by
  intro j
  have hdiag₀ := S.sampled_zpow_bound (hmu j) (htube j) i
  have hdiag :
      |S.F (mu j) (u j) i - E.enc (c (j + 1)) i| ≤
        (E.k : ℝ) ^ E.coordDelta (c j) i *
            |u j i - E.enc (c j) i| + S.epsF (mu j) i := by
    simpa [hcstep j] using hdiag₀
  simpa [boundaryError, cycleEta] using
    (cycle_triangle_refined_recurrence
      (base := (E.k : ℝ)) (D := S.D) (delta := E.coordDelta (c j) i)
      (uNext := u (j + 1) i) (zNext := z (j + 1) i)
      (target := S.F (mu j) (u j) i) (nextExact := E.enc (c (j + 1)) i)
      (prevErr := |u j i - E.enc (c j) i|) (eps := S.epsF (mu j) i)
      (kappa := kappa j) (chi := chi j)
      hdiag (htrack_z j) (htrack_u j))

/-! ## C4: glue into DepthBudget -/

/--
C4, consolidated-decay version.  The caller packages the decay of
`epsF(mu_j)`, `kappa_j`, and `chi_j` into the single eta bound expected
by the depth-budget theorem.
-/
theorem demo_depth_aware_all_time_tube
    {dcoord nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding dcoord nS M} (S : RobustStepContract M E)
    (u z : ℕ → Fin dcoord → ℝ) (c : ℕ → Conf) (mu kappa chi : ℕ → ℝ)
    (i : Fin dcoord) (d : ℕ → ℤ)
    {d0 beta eta C : ℝ}
    (hcstep : ∀ j, c (j + 1) = M.step (c j))
    (hmu : ∀ j, S.mu_min ≤ mu j)
    (htube : ∀ j, EncodingTube E (S.radius (mu j)) (c j) (u j))
    (htrack_z : ∀ j,
      |z (j + 1) i - S.F (mu j) (u j) i| ≤ S.D * (kappa j + chi j))
    (htrack_u : ∀ j,
      |u (j + 1) i - z (j + 1) i| ≤ S.D * (kappa j + chi j))
    (hdepth : ∀ j, d (j + 1) = d j - E.coordDelta (c j) i)
    (hdnn : ∀ j, 0 ≤ d j)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecay : ∀ j, cycleEta S mu kappa chi j i ≤ C * Real.exp (-(eta) * j))
    (heta : beta * Real.log (E.k : ℝ) < eta)
    (hC : 0 ≤ C)
    (hbeta : 0 ≤ beta) :
    ∀ j, boundaryError E u c j i ≤
      DepthBudget.W (E.k : ℝ) d (fun j => boundaryError E u c j i) 0 +
        DepthBudget.geometricBudgetConstant (E.k : ℝ) d0 beta eta C := by
  exact DepthBudget.depth_aware_all_time_tube
    (e := fun j => boundaryError E u c j i)
    (d := d)
    (delta := fun j => E.coordDelta (c j) i)
    (eps := fun j => cycleEta S mu kappa chi j i)
    (k := (E.k : ℝ))
    (d0 := d0) (beta := beta) (eta := eta) (C := C)
    E.one_lt_base_real
    (contract_cycle_refined_recurrence S u z c mu kappa chi i
      hcstep hmu htube htrack_z htrack_u)
    hdepth
    (by intro j; exact abs_nonneg _)
    hdnn
    hgrow
    hdecay
    heta
    hC
    hbeta

/--
C4, component-decay version.  This is the common use shape: the robust
step error and the two half-cycle tracking errors each have exponential
decay, and their constants are bundled into the `C` required by
`DepthBudget.depth_aware_all_time_tube`.
-/
theorem demo_depth_aware_all_time_tube_from_components
    {dcoord nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding dcoord nS M} (S : RobustStepContract M E)
    (u z : ℕ → Fin dcoord → ℝ) (c : ℕ → Conf) (mu kappa chi : ℕ → ℝ)
    (i : Fin dcoord) (d : ℕ → ℤ)
    {d0 beta eta CF CK CChi C : ℝ}
    (hcstep : ∀ j, c (j + 1) = M.step (c j))
    (hmu : ∀ j, S.mu_min ≤ mu j)
    (htube : ∀ j, EncodingTube E (S.radius (mu j)) (c j) (u j))
    (htrack_z : ∀ j,
      |z (j + 1) i - S.F (mu j) (u j) i| ≤ S.D * (kappa j + chi j))
    (htrack_u : ∀ j,
      |u (j + 1) i - z (j + 1) i| ≤ S.D * (kappa j + chi j))
    (hdepth : ∀ j, d (j + 1) = d j - E.coordDelta (c j) i)
    (hdnn : ∀ j, 0 ≤ d j)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecayF : ∀ j, S.epsF (mu j) i ≤ CF * Real.exp (-(eta) * j))
    (hdecayK : ∀ j, S.D * kappa j ≤ CK * Real.exp (-(eta) * j))
    (hdecayChi : ∀ j, S.D * chi j ≤ CChi * Real.exp (-(eta) * j))
    (hCsum : CF + 2 * CK + 2 * CChi ≤ C)
    (heta : beta * Real.log (E.k : ℝ) < eta)
    (hC : 0 ≤ C)
    (hbeta : 0 ≤ beta) :
    ∀ j, boundaryError E u c j i ≤
      DepthBudget.W (E.k : ℝ) d (fun j => boundaryError E u c j i) 0 +
        DepthBudget.geometricBudgetConstant (E.k : ℝ) d0 beta eta C := by
  refine demo_depth_aware_all_time_tube S u z c mu kappa chi i d
    hcstep hmu htube htrack_z htrack_u hdepth hdnn hgrow ?_ heta hC hbeta
  intro j
  have hexp_nonneg : 0 ≤ Real.exp (-(eta) * (j : ℝ)) := (Real.exp_pos _).le
  calc
    cycleEta S mu kappa chi j i
        = S.epsF (mu j) i + 2 * (S.D * kappa j) + 2 * (S.D * chi j) := by
            simp [cycleEta]
            ring
    _ ≤ CF * Real.exp (-(eta) * (j : ℝ)) +
          2 * (CK * Real.exp (-(eta) * (j : ℝ))) +
          2 * (CChi * Real.exp (-(eta) * (j : ℝ))) := by
            nlinarith [hdecayF j, hdecayK j, hdecayChi j]
    _ = (CF + 2 * CK + 2 * CChi) * Real.exp (-(eta) * (j : ℝ)) := by ring
    _ ≤ C * Real.exp (-(eta) * (j : ℝ)) :=
        mul_le_mul_of_nonneg_right hCsum hexp_nonneg

end

end Ripple.BoundedUniversality.BGP
