/-
Ripple.BoundedUniversality.BGP.CycleTracking
------------------------
Moving-target / variable-mu cycle layer.

Design notes read end-to-end before this file was added:
* notes/gpt-life1-muvarying.md
* notes/gpt-life1-cycletracking.md

Documented choices/deviations:
* `PhaseClock.targeting_bound` already has the target-ball shape needed
  for M1.  The theorem `moving_target_bound` below is therefore a thin
  `g`-gain wrapper (`A = 1`, `φ = g`) with the contract-facing name.
* The variable-mu robust-step structure records both the monotone
  cycle-start precision and antitone scalar error envelope.  The stack
  recurrence uses the uniform cycle stack-row clause with
  `eps (muAt j)` at the window start; selector ripple is kept as a
  separate optional field and is not hidden in the matrix.
* The live-ODE recurrence follows the mu-varying note's safer chain:
  `eta_j = eps(mu_j) + 2 * kappa_j * D + (k + 1) * chi_j * D`.
  This is intentionally not simplified to the fixed-mu `2 * chi` shape.
-/

import Ripple.BoundedUniversality.BGP.RobustStepContract
import Ripple.BoundedUniversality.BGP.PhaseClock

namespace Ripple.BoundedUniversality.BGP

open Real intervalIntegral
open Ripple.BoundedUniversality.Core

noncomputable section

/-! ## M1: moving-target target-ball estimate -/

/--
M1, target-ball moving-target wrapper.

If `y' = g(t) * (w(t) - y(t))`, `g >= 0` on `[a,b]`, and the live
target stays in the fixed `delta`-ball around `c`, then `y b` is within
the exponentially damped initial error plus `delta`.
-/
theorem moving_target_bound
    (g w : ℝ → ℝ) (y : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hg_cont : Continuous g)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hw_cont : Continuous w)
    (c delta : ℝ) (hdelta : ∀ t ∈ Set.Icc a b, |w t - c| ≤ delta)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (g t * (w t - y t)) t) :
    |y b - c| ≤ Real.exp (-(∫ t in a..b, g t)) * |y a - c| + delta := by
  have hy' : ∀ t ∈ Set.Icc a b, HasDerivAt y (1 * g t * (w t - y t)) t := by
    intro t ht
    simpa [one_mul] using hy t ht
  simpa [one_mul] using
    (targeting_bound (A := 1) (hA := by norm_num) (φ := g) (w := w) (y := y)
      (a := a) (b := b) hab hg_cont hg0 hw_cont c delta
      hdelta hy')

/-! ## M2: variable-mu robust-step interface -/

/-- Optional selector ripple budget for a cycle. -/
def selectorRipple (theta : ℕ → ℝ) (j : ℕ) : ℝ := theta j

/--
Variable-`mu` robust-step contract for one live cycle layer.

The fields are deliberately trajectory-agnostic.  A caller supplies the
actual trajectory closure hypotheses (`u(t) in K_LE(c_j)`, etc.) to the
recurrence theorem, while this record supplies the uniform-in-cycle
robust-step clauses and working-domain primitives.
-/
structure VarMuRobustStep {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (E : StackMachineEncoding d nS M) where
  mu_min : ℝ
  mu : ℝ → ℝ
  muAt : ℕ → ℝ
  cycleStart : ℕ → ℝ
  cycleMid : ℕ → ℝ
  cycleEnd : ℕ → ℝ
  eps : ℝ → ℝ
  eps_antitone : ∀ {mu0 mu1 : ℝ}, mu0 ≤ mu1 → eps mu1 ≤ eps mu0
  theta : ℕ → ℝ
  K_LE : Conf → (Fin d → ℝ) → Prop
  K_work : (Fin d → ℝ) → Prop
  F : ℝ → (Fin d → ℝ) → Fin d → ℝ
  D : ℝ
  D_nonneg : 0 ≤ D
  muAt_start : ∀ j, muAt j = mu (cycleStart j)
  cycleEnd_start_next : ∀ j, cycleEnd j = cycleStart (j + 1)
  mu_mono_cycle :
    ∀ j t, t ∈ Set.Icc (cycleStart j) (cycleEnd j) → muAt j ≤ mu t
  K_LE_tube :
    ∀ {c x}, K_LE c x → EncodingTube E 0 c x ∨ EncodingTube E D c x
  uniform_stack_bound :
    ∀ {j t c x} (s : Fin nS),
      mu_min ≤ muAt j →
      t ∈ Set.Icc (cycleStart j) (cycleMid j) →
      K_LE c x →
      |F (mu t) x (E.stackCoord s) -
          E.enc (M.step c) (E.stackCoord s)| ≤
        (E.k : ℝ) ^ E.stackDelta c s *
            |x (E.stackCoord s) - E.enc c (E.stackCoord s)| +
          eps (muAt j)
  uniform_coord_bound_with_ripple :
    ∀ {j t c x} (i : Fin d),
      mu_min ≤ muAt j →
      t ∈ Set.Icc (cycleStart j) (cycleMid j) →
      K_LE c x →
      |F (mu t) x i - E.enc (M.step c) i| ≤
        (E.k : ℝ) ^ E.coordDelta c i * |x i - E.enc c i| +
          (eps (muAt j) + theta j)
  reset_bound_with_ripple :
    ∀ {j t c x} (i : Fin d),
      E.coordStackIndex i = none →
      mu_min ≤ muAt j →
      t ∈ Set.Icc (cycleStart j) (cycleMid j) →
      K_LE c x →
      |F (mu t) x i - E.enc (M.step c) i| ≤ eps (muAt j) + theta j
  F_work :
    ∀ {j t c x},
      mu_min ≤ muAt j →
      t ∈ Set.Icc (cycleStart j) (cycleMid j) →
      K_LE c x →
      K_work (F (mu t) x)
  displacement_bound :
    ∀ {_mu0 : ℝ} {x y : Fin d → ℝ} (i : Fin d),
      K_work x → K_work y → |x i - y i| ≤ D

namespace VarMuRobustStep

variable {d nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
variable {E : StackMachineEncoding d nS M}

/-- Boundary coordinate error for continuous-time samples at cycle starts. -/
def boundaryError (S : VarMuRobustStep M E)
    (u : ℝ → Fin d → ℝ) (c : ℕ → Conf) (j : ℕ) (i : Fin d) : ℝ :=
  |u (S.cycleStart j) i - E.enc (c j) i|

/-- The variable-mu live-target additive error from the design note. -/
def cycleEta (S : VarMuRobustStep M E)
    (kappa chi : ℕ → ℝ) (j : ℕ) : ℝ :=
  S.eps (S.muAt j) + 2 * kappa j * S.D + (((E.k : ℝ) + 1) * chi j * S.D)

private theorem stack_coordDelta_eq (E : StackMachineEncoding d nS M)
    (c : Conf) (s : Fin nS) :
    E.coordDelta c (E.stackCoord s) = E.stackDelta c s := by
  simp [StackMachineEncoding.coordDelta, E.coordStackIndex_stack s]

private theorem stack_zpow_le_base (E : StackMachineEncoding d nS M)
    (c : Conf) (s : Fin nS) :
    (E.k : ℝ) ^ E.stackDelta c s ≤ (E.k : ℝ) := by
  have hk1 : (1 : ℝ) < (E.k : ℝ) := E.one_lt_base_real
  have hkpos : 0 < (E.k : ℝ) := lt_trans zero_lt_one hk1
  cases hmove : E.moveType c s with
  | pop =>
      simp [StackMachineEncoding.stackDelta, StackMove.delta, hmove]
  | push =>
      have hinv : ((E.k : ℝ)⁻¹ : ℝ) ≤ 1 := inv_le_one_of_one_le₀ hk1.le
      have hle : ((E.k : ℝ)⁻¹ : ℝ) ≤ (E.k : ℝ) := hinv.trans hk1.le
      simpa [StackMachineEncoding.stackDelta, StackMove.delta, hmove] using hle
  | stay =>
      simpa [StackMachineEncoding.stackDelta, StackMove.delta, hmove] using hk1.le

/--
M3, one live variable-mu cycle recurrence for a stack coordinate.

The proof applies `moving_target_bound` on the `z` active half with the
live target `F (mu t) (u t)`, then applies it again on the `u` active
half with live target `z(t)`.  The `u`-hold drift enters multiplied by
the stack multiplier and is finally bounded by `k * chi_j * D`, producing
the required `(k+1)` coefficient.
-/
theorem variable_mu_cycle_recurrence
    (S : VarMuRobustStep M E)
    (u z : ℝ → Fin d → ℝ) (c : ℕ → Conf)
    (gZ gU : ℝ → ℝ)
    (kappa chi : ℕ → ℝ) (j : ℕ) (s : Fin nS)
    (hstart_mid : S.cycleStart j ≤ S.cycleMid j)
    (hmid_end : S.cycleMid j ≤ S.cycleEnd j)
    (hcstep : c (j + 1) = M.step (c j))
    (hmu_min : S.mu_min ≤ S.muAt j)
    (hchi_nonneg : 0 ≤ chi j)
    (hkappa_nonneg : 0 ≤ kappa j)
    (hgZ_cont : Continuous (fun t => gZ t))
    (hgZ_nonneg : ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j), 0 ≤ gZ t)
    (hwZ_cont : Continuous (fun t => S.F (S.mu t) (u t) (E.stackCoord s)))
    (hz_deriv : ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j),
      HasDerivAt (fun τ => z τ (E.stackCoord s))
        (gZ t * (S.F (S.mu t) (u t) (E.stackCoord s) -
          z t (E.stackCoord s))) t)
    (hgU_cont : Continuous (fun t => gU t))
    (hgU_nonneg : ∀ t ∈ Set.Icc (S.cycleMid j) (S.cycleEnd j), 0 ≤ gU t)
    (hwU_cont : Continuous (fun t => z t (E.stackCoord s)))
    (hu_deriv : ∀ t ∈ Set.Icc (S.cycleMid j) (S.cycleEnd j),
      HasDerivAt (fun τ => u τ (E.stackCoord s))
        (gU t * (z t (E.stackCoord s) - u t (E.stackCoord s))) t)
    (hz_decay :
      Real.exp (-(∫ t in (S.cycleStart j)..(S.cycleMid j), gZ t)) ≤ kappa j)
    (hu_decay :
      Real.exp (-(∫ t in (S.cycleMid j)..(S.cycleEnd j), gU t)) ≤ kappa j)
    (hz_start :
      |z (S.cycleStart j) (E.stackCoord s) -
          E.enc (c (j + 1)) (E.stackCoord s)| ≤ S.D)
    (hu_mid :
      |u (S.cycleMid j) (E.stackCoord s) -
          E.enc (c (j + 1)) (E.stackCoord s)| ≤ S.D)
    (hu_active :
      ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j), S.K_LE (c j) (u t))
    (hu_hold :
      ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j),
        |u t (E.stackCoord s) - u (S.cycleStart j) (E.stackCoord s)| ≤
          chi j * S.D)
    (hz_hold :
      ∀ t ∈ Set.Icc (S.cycleMid j) (S.cycleEnd j),
        |z t (E.stackCoord s) - z (S.cycleMid j) (E.stackCoord s)| ≤
          chi j * S.D) :
    boundaryError S u c (j + 1) (E.stackCoord s) ≤
      (E.k : ℝ) ^ E.coordDelta (c j) (E.stackCoord s) *
          boundaryError S u c j (E.stackCoord s) +
        cycleEta S kappa chi j := by
  let i := E.stackCoord s
  let p : ℝ := (E.k : ℝ) ^ E.stackDelta (c j) s
  let e : ℝ := boundaryError S u c j i
  let epsj : ℝ := S.eps (S.muAt j)
  let chiD : ℝ := chi j * S.D
  let deltaZ : ℝ := p * e + p * chiD + epsj
  have hkpos : 0 < (E.k : ℝ) := lt_trans zero_lt_one E.one_lt_base_real
  have hp_nonneg : 0 ≤ p := (zpow_pos hkpos _).le
  have hpow_le_k : p ≤ (E.k : ℝ) := by
    simpa [p] using stack_zpow_le_base E (c j) s
  have hchiD_nonneg : 0 ≤ chiD := mul_nonneg hchi_nonneg S.D_nonneg
  have htargetZ :
      ∀ t ∈ Set.Icc (S.cycleStart j) (S.cycleMid j),
        |S.F (S.mu t) (u t) i - E.enc (c (j + 1)) i| ≤ deltaZ := by
    intro t ht
    have hrob₀ := S.uniform_stack_bound (j := j) (t := t) (c := c j)
      (x := u t) s hmu_min ht (hu_active t ht)
    have hrob :
        |S.F (S.mu t) (u t) i - E.enc (c (j + 1)) i| ≤
          p * |u t i - E.enc (c j) i| + epsj := by
      simpa [i, p, epsj, hcstep] using hrob₀
    have hutri : |u t i - E.enc (c j) i| ≤
        e + |u t i - u (S.cycleStart j) i| := by
      have hsum :
          u t i - E.enc (c j) i =
            (u t i - u (S.cycleStart j) i) +
              (u (S.cycleStart j) i - E.enc (c j) i) := by ring
      calc
        |u t i - E.enc (c j) i|
            = |(u t i - u (S.cycleStart j) i) +
                (u (S.cycleStart j) i - E.enc (c j) i)| := by rw [hsum]
        _ ≤ |u t i - u (S.cycleStart j) i| +
              |u (S.cycleStart j) i - E.enc (c j) i| := abs_add_le _ _
        _ = |u t i - u (S.cycleStart j) i| + e := by rfl
        _ = e + |u t i - u (S.cycleStart j) i| := by ring
    have hholdi : |u t i - u (S.cycleStart j) i| ≤ chiD := by
      simpa [i, chiD] using hu_hold t ht
    have hmul : p * |u t i - E.enc (c j) i| ≤ p * (e + chiD) := by
      have hutri' : |u t i - E.enc (c j) i| ≤ e + chiD := by
        exact hutri.trans (by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hholdi e)
      exact mul_le_mul_of_nonneg_left
        hutri' hp_nonneg
    calc
      |S.F (S.mu t) (u t) i - E.enc (c (j + 1)) i|
          ≤ p * |u t i - E.enc (c j) i| + epsj := hrob
      _ ≤ p * (e + chiD) + epsj := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hmul epsj
      _ = deltaZ := by ring
  have hz_target := moving_target_bound
    (g := gZ) (w := fun t => S.F (S.mu t) (u t) i)
    (y := fun t => z t i)
    (a := S.cycleStart j) (b := S.cycleMid j) hstart_mid
    hgZ_cont hgZ_nonneg hwZ_cont (E.enc (c (j + 1)) i) deltaZ
    htargetZ hz_deriv
  have hz_initial_budget :
      Real.exp (-(∫ t in (S.cycleStart j)..(S.cycleMid j), gZ t)) *
          |z (S.cycleStart j) i - E.enc (c (j + 1)) i| ≤
        kappa j * S.D := by
    exact mul_le_mul hz_decay hz_start (abs_nonneg _) hkappa_nonneg
  have hz_mid_bound :
      |z (S.cycleMid j) i - E.enc (c (j + 1)) i| ≤
        kappa j * S.D + deltaZ := by
    calc
      |z (S.cycleMid j) i - E.enc (c (j + 1)) i|
          ≤ Real.exp (-(∫ t in (S.cycleStart j)..(S.cycleMid j), gZ t)) *
              |z (S.cycleStart j) i - E.enc (c (j + 1)) i| + deltaZ :=
            hz_target
      _ ≤ kappa j * S.D + deltaZ := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hz_initial_budget deltaZ
  have htargetU :
      ∀ t ∈ Set.Icc (S.cycleMid j) (S.cycleEnd j),
        |z t i - E.enc (c (j + 1)) i| ≤ kappa j * S.D + deltaZ + chiD := by
    intro t ht
    have htri : |z t i - E.enc (c (j + 1)) i| ≤
        |z t i - z (S.cycleMid j) i| +
          |z (S.cycleMid j) i - E.enc (c (j + 1)) i| := by
      have hsum :
          z t i - E.enc (c (j + 1)) i =
            (z t i - z (S.cycleMid j) i) +
              (z (S.cycleMid j) i - E.enc (c (j + 1)) i) := by ring
      rw [hsum]
      exact abs_add_le _ _
    calc
      |z t i - E.enc (c (j + 1)) i|
          ≤ |z t i - z (S.cycleMid j) i| +
              |z (S.cycleMid j) i - E.enc (c (j + 1)) i| := htri
      _ ≤ chiD + (kappa j * S.D + deltaZ) :=
            add_le_add (hz_hold t ht) hz_mid_bound
      _ = kappa j * S.D + deltaZ + chiD := by ring
  have hu_target := moving_target_bound
    (g := gU) (w := fun t => z t i)
    (y := fun t => u t i)
    (a := S.cycleMid j) (b := S.cycleEnd j) hmid_end
    hgU_cont hgU_nonneg hwU_cont (E.enc (c (j + 1)) i)
    (kappa j * S.D + deltaZ + chiD) htargetU hu_deriv
  have hu_initial_budget :
      Real.exp (-(∫ t in (S.cycleMid j)..(S.cycleEnd j), gU t)) *
          |u (S.cycleMid j) i - E.enc (c (j + 1)) i| ≤
        kappa j * S.D := by
    exact mul_le_mul hu_decay hu_mid (abs_nonneg _) hkappa_nonneg
  have hraw :
      |u (S.cycleEnd j) i - E.enc (c (j + 1)) i| ≤
        p * e + epsj + 2 * kappa j * S.D + (p + 1) * chiD := by
    calc
      |u (S.cycleEnd j) i - E.enc (c (j + 1)) i|
          ≤ Real.exp (-(∫ t in (S.cycleMid j)..(S.cycleEnd j), gU t)) *
              |u (S.cycleMid j) i - E.enc (c (j + 1)) i| +
                (kappa j * S.D + deltaZ + chiD) := hu_target
      _ ≤ kappa j * S.D + (kappa j * S.D + deltaZ + chiD) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hu_initial_budget (kappa j * S.D + deltaZ + chiD)
      _ = p * e + epsj + 2 * kappa j * S.D + (p + 1) * chiD := by
            ring
  have hchi_scale : (p + 1) * chiD ≤ (((E.k : ℝ) + 1) * chiD) := by
    have hp_le : p ≤ (E.k : ℝ) := by simpa [p] using hpow_le_k
    have hpk : p + 1 ≤ (E.k : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hpk hchiD_nonneg
  have hend_eq_start : S.cycleEnd j = S.cycleStart (j + 1) :=
    S.cycleEnd_start_next j
  have hcoord : E.coordDelta (c j) i = E.stackDelta (c j) s :=
    stack_coordDelta_eq E (c j) s
  calc
    boundaryError S u c (j + 1) i
        = |u (S.cycleEnd j) i - E.enc (c (j + 1)) i| := by
            simp [boundaryError, i, hend_eq_start]
    _ ≤ p * e + epsj + 2 * kappa j * S.D + (p + 1) * chiD := hraw
    _ ≤ p * e + epsj + 2 * kappa j * S.D + (((E.k : ℝ) + 1) * chiD) := by
            linarith
    _ = (E.k : ℝ) ^ E.coordDelta (c j) i * boundaryError S u c j i +
          cycleEta S kappa chi j := by
            simp [cycleEta, boundaryError, i, p, e, epsj, chiD, hcoord]
            ring

/--
M4, consolidated glue into `DepthBudget.depth_aware_all_time_tube` for
the variable-mu cycle eta.
-/
theorem variable_mu_depth_aware_all_time_tube
    (S : VarMuRobustStep M E)
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (kappa chi : ℕ → ℝ)
    {d0 beta eta C : ℝ}
    (hrec : ∀ j, e (j + 1) ≤ (E.k : ℝ) ^ delta j * e j + cycleEta S kappa chi j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j)
    (he : ∀ j, 0 ≤ e j)
    (hdnn : ∀ j, 0 ≤ d j)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecay : ∀ j, cycleEta S kappa chi j ≤ C * Real.exp (-(eta) * j))
    (heta : beta * Real.log (E.k : ℝ) < eta)
    (hC : 0 ≤ C)
    (hbeta : 0 ≤ beta) :
    ∀ j, e j ≤
      DepthBudget.W (E.k : ℝ) d e 0 +
        DepthBudget.geometricBudgetConstant (E.k : ℝ) d0 beta eta C := by
  exact DepthBudget.depth_aware_all_time_tube
    (e := e) (d := d) (delta := delta)
    (eps := fun j => cycleEta S kappa chi j)
    (k := (E.k : ℝ)) (d0 := d0) (beta := beta) (eta := eta) (C := C)
    E.one_lt_base_real hrec hdepth he hdnn hgrow hdecay heta hC hbeta

/--
M4 component-decay glue.  The caller supplies exponential decay of
`eps(mu_j)`, `kappa_j * D`, and `chi_j * D`; the `(k+1)` coefficient is
preserved in the bundled constant hypothesis.
-/
theorem variable_mu_depth_aware_all_time_tube_from_components
    (S : VarMuRobustStep M E)
    (e : ℕ → ℝ) (d delta : ℕ → ℤ) (kappa chi : ℕ → ℝ)
    {d0 beta eta CF CK CChi C : ℝ}
    (hrec : ∀ j, e (j + 1) ≤ (E.k : ℝ) ^ delta j * e j + cycleEta S kappa chi j)
    (hdepth : ∀ j, d (j + 1) = d j - delta j)
    (he : ∀ j, 0 ≤ e j)
    (hdnn : ∀ j, 0 ≤ d j)
    (hgrow : ∀ j, (d j : ℝ) ≤ d0 + beta * j)
    (hdecayF : ∀ j, S.eps (S.muAt j) ≤ CF * Real.exp (-(eta) * j))
    (hdecayK : ∀ j, kappa j * S.D ≤ CK * Real.exp (-(eta) * j))
    (hdecayChi : ∀ j, chi j * S.D ≤ CChi * Real.exp (-(eta) * j))
    (hCsum : CF + 2 * CK + ((E.k : ℝ) + 1) * CChi ≤ C)
    (heta : beta * Real.log (E.k : ℝ) < eta)
    (hC : 0 ≤ C)
    (hbeta : 0 ≤ beta) :
    ∀ j, e j ≤
      DepthBudget.W (E.k : ℝ) d e 0 +
        DepthBudget.geometricBudgetConstant (E.k : ℝ) d0 beta eta C := by
  refine variable_mu_depth_aware_all_time_tube S e d delta kappa chi
    hrec hdepth he hdnn hgrow ?_ heta hC hbeta
  intro j
  have hexp_nonneg : 0 ≤ Real.exp (-(eta) * (j : ℝ)) := (Real.exp_pos _).le
  calc
    cycleEta S kappa chi j
        = S.eps (S.muAt j) + 2 * (kappa j * S.D) +
            ((E.k : ℝ) + 1) * (chi j * S.D) := by
            simp [cycleEta]
            ring
    _ ≤ CF * Real.exp (-(eta) * (j : ℝ)) +
          2 * (CK * Real.exp (-(eta) * (j : ℝ))) +
          ((E.k : ℝ) + 1) * (CChi * Real.exp (-(eta) * (j : ℝ))) := by
            nlinarith [hdecayF j, hdecayK j, hdecayChi j]
    _ = (CF + 2 * CK + ((E.k : ℝ) + 1) * CChi) *
          Real.exp (-(eta) * (j : ℝ)) := by ring
    _ ≤ C * Real.exp (-(eta) * (j : ℝ)) :=
        mul_le_mul_of_nonneg_right hCsum hexp_nonneg

end VarMuRobustStep

end

end Ripple.BoundedUniversality.BGP
