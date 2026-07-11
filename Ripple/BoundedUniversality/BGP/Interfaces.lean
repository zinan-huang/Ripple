/-
Ripple.BoundedUniversality.BGP.Interfaces
---------------------
Faithful interface layer for the BGP-route formalization, mirroring
paper-draft/main.tex §2 and §4.  Revision 2 after adversarial round 1
(codex R1, 2026-06-11; log: notes/bgp-adversarial-rounds.md).

R1 fixes incorporated:
* R1#2: `DiscreteMachine` is now a genuine computational object —
  `Conf` primcodable, `step`/`halted`/`init` computable, `halted` a
  Bool.  A machine whose `halted` field smuggles an undecidable
  predicate is excluded; `haltsOn` is then honestly Σ₁.
* R1#3 (= self-audit S1): `haltsOn` is a DEF, not an overridable
  field.
* R1#1: `EventualThresholdSimulation` requires a computable
  numerator/denominator presentation of the initial encoder —
  noncomputable initial data smuggling the verdict (the exploit
  `init w = if haltsOn w then 1 else 0`) is excluded.  This is the
  positive-side mirror of the finite-advice theorem's honesty
  condition (`Ripple.BoundedUniversality.GPAC.Impossibility`, paper rem:honest-encoder).
* S2: `EventualThresholdSimulation` requires bounded trajectories —
  the compactified system's defining property; without it the
  unbounded Euclidean simulator satisfies the contract and the
  paper's headline is dropped.
* F1 fix retained: `LatticeEncoding` separation mandatory.
* F4 fix retained: `ThresholdReadout` concrete.
-/

import Ripple.BoundedUniversality.GPAC.PIVP
import Ripple.BoundedUniversality.Core.DiscreteSource
import Mathlib

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core

/-! ## The discrete machine -/

/-- An abstract deterministic machine with absorbing halt, as a
genuine computational object: configurations are primcodable, the
step map, halting test, and input encoding are computable.  For the
main theorem `Conf` is `Conf(U)` of a fixed universal TM. -/
structure DiscreteMachine (Conf : Type) [Primcodable Conf] where
  step : Conf → Conf
  halted : Conf → Bool
  halted_absorbing : ∀ c, halted c = true → step c = c
  init : ℕ → Conf
  step_computable : Computable step
  halted_computable : Computable halted
  init_computable : Computable init

/-- The halting predicate — a def, not an overridable field. -/
def DiscreteMachine.haltsOn {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (w : ℕ) : Prop :=
  ∃ n, M.halted (M.step^[n] (M.init w)) = true

/-- A machine whose (honestly Σ₁) halting predicate is undecidable. -/
structure UndecidableMachine (Conf : Type) [Primcodable Conf]
    extends DiscreteMachine Conf where
  undecidable : NoComputableBoolDecider toDiscreteMachine.haltsOn

/-! ## Lattice encoding (F1 fix: separation is mandatory) -/

/-- An injective configuration encoding into `ℝ^d` with UNIFORM L∞
separation.  thm:rationalised-step uses the BCGH integer encoding with
`sep = 1`.  The image is typically UNBOUNDED (integer tape encoding);
boundedness is recovered only after compactification — this is exactly
the dichotomy boundary (`Ripple.BoundedUniversality.GPAC.Impossibility`): a bounded image
with uniform separation would force finiteness (`packing_finite`). -/
structure LatticeEncoding {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (d : ℕ) where
  enc : Conf → Fin d → ℝ
  sep : ℝ
  sep_pos : 0 < sep
  separated : ∀ c c', c ≠ c' →
    ∃ i, sep ≤ |enc c i - enc c' i|
  /-- rationality of the encoding values (the encoder is
  configuration-local and exactly representable). -/
  enc_rat : ∀ c i, ∃ q : ℚ, enc c i = (q : ℝ)

/-- Injectivity is derived, not assumed. -/
theorem LatticeEncoding.enc_injective {Conf : Type} [Primcodable Conf]
    {M : DiscreteMachine Conf} {d : ℕ}
    (E : LatticeEncoding M d) : Function.Injective E.enc := by
  intro c c' h
  by_contra hne
  obtain ⟨i, hi⟩ := E.separated c c' hne
  rw [h] at hi
  simp only [sub_self, abs_zero] at hi
  linarith [E.sep_pos]

/-! ## Robust real extension (def:robust-modulus, strict-contraction form) -/

/-- def:robust-modulus.  `F` is given as POLYNOMIAL data over ℚ (not a
raw function — rationality and polynomiality are the paper's point),
and the snap condition is the strict-contraction form:
snap error `η_step` strictly below the uniform snap radius `r₀`,
which itself is strictly below half the lattice separation, so that
the snap balls of distinct configurations are disjoint and consecutive
snap outputs re-enter the snap basin.  These two strictness fields are
what make the structure refutable (cf. `no_robust_increment_freeze`
for the unbounded-ℕ fuel machine at d = 2 with the cast encoding). -/
structure RobustRealExtension {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding M d) where
  F : Fin d → MvPolynomial (Fin d) ℚ
  r₀ : ℚ
  ηstep : ℚ
  r₀_pos : 0 < r₀
  ηstep_pos : 0 < ηstep
  /-- strict contraction: snap error below snap radius. -/
  ηstep_lt_r₀ : ηstep < r₀
  /-- snap balls of distinct configurations are disjoint. -/
  two_r₀_lt_sep : 2 * (r₀ : ℝ) < E.sep
  /-- the snap condition of def:robust-modulus, uniform in `c`. -/
  snap : ∀ (c : Conf) (x : Fin d → ℝ),
    (∀ i, |x i - E.enc c i| ≤ (r₀ : ℝ)) →
    ∀ i, |MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (F i)
            - E.enc (M.step c) i| ≤ (ηstep : ℝ)

/-- Real evaluation of the step polynomial. -/
noncomputable def RobustRealExtension.evalF {Conf : Type}
    [Primcodable Conf] {M : DiscreteMachine Conf} {d : ℕ}
    {E : LatticeEncoding M d} (S : RobustRealExtension M d E)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (S.F i)

/-! ## Threshold readouts (F4 fix: concrete data, no Prop slots) -/

/-- Euclidean threshold readout: the latch coordinate `h` eventually
lies in `[3/4, 1]` on halting inputs and `[0, 1/4]` on non-halting
inputs.  Used by the assembled EUCLIDEAN simulator (pre-
compactification). -/
structure ThresholdReadout (n : ℕ) where
  h : Fin n

namespace ThresholdReadout

variable {n : ℕ} (R : ThresholdReadout n)

def HaltRegion : Set (Fin n → ℝ) := {y | 3/4 ≤ y R.h ∧ y R.h ≤ 1}

def NonhaltRegion : Set (Fin n → ℝ) := {y | 0 ≤ y R.h ∧ y R.h ≤ 1/4}

theorem disjoint_regions : Disjoint R.HaltRegion R.NonhaltRegion := by
  rw [Set.disjoint_iff]
  rintro y ⟨⟨h1, _⟩, ⟨_, h4⟩⟩
  simp only [Set.mem_empty_iff_false]
  linarith

end ThresholdReadout

/-- Chart threshold readout (R2#1): the COMPACTIFIED system's readout
is the rational chart observable `a(y) = y_A / (1 - y_0)` of thm:main,
expressed by the paper's polynomial inequalities — NOT the raw
coordinate (on the sphere the latch value is conformally squeezed,
and the raw-coordinate readout misclassifies; codex R2 exploit).
`hA` is the ambient latch index, `h0` the ambient `y₀` index. -/
structure ChartThresholdReadout (n : ℕ) where
  hA : Fin n
  h0 : Fin n
  ne : hA ≠ h0

namespace ChartThresholdReadout

variable {n : ℕ} (R : ChartThresholdReadout n)

/-- thm:main's `U_Halt`: `y₀ < 1 ∧ 3(1-y₀) ≤ 4 y_A ∧ y_A ≤ 1-y₀`. -/
def HaltRegion : Set (Fin n → ℝ) :=
  {y | y R.h0 < 1 ∧ 3 * (1 - y R.h0) ≤ 4 * y R.hA ∧ y R.hA ≤ 1 - y R.h0}

/-- thm:main's `U_Nonhalt`: `y₀ < 1 ∧ 0 ≤ y_A ∧ 4 y_A ≤ 1-y₀`. -/
def NonhaltRegion : Set (Fin n → ℝ) :=
  {y | y R.h0 < 1 ∧ 0 ≤ y R.hA ∧ 4 * y R.hA ≤ 1 - y R.h0}

theorem disjoint_regions : Disjoint R.HaltRegion R.NonhaltRegion := by
  rw [Set.disjoint_iff]
  rintro y ⟨⟨h0lt, h31, _⟩, ⟨_, _, h14⟩⟩
  simp only [Set.mem_empty_iff_false]
  linarith

end ChartThresholdReadout

/-- The simulation contract for the compactified assembled system:
BOUNDED trajectories, HONEST (computably presented) initial encoder,
eventual CHART-observable threshold readout in both directions,
against a FIXED undecidable machine (a parameter, not an existential
package — R2#8: the paper fixes the universal machine up front).
This is the shape that `bgp_robust_step_to_halting_pivp` should have
had; every component is data or a theorem obligation.

`encoder_presented` excludes the R1#1 exploit (initial data defined by
cases on the undecidable predicate).  `bounded` is the compactness
headline (S2).  `readout : ChartThresholdReadout` is the R2#1 fix:
on the sphere the latch is read through `a(y) = y_A/(1-y₀)`, expressed
by thm:main's polynomial inequalities.

The trajectory/ODE fields are inlined (rather than importing
`Ripple.BoundedUniversality.GPAC.StrongPIVPSemantics`) to keep this module's import
closure disjoint from the F4 refactor in flight; reconcile after. -/
structure EventualThresholdSimulation (P : Ripple.BoundedUniversality.GPAC.PIVP ℚ)
    {Conf : Type} [instPrim : Primcodable Conf]
    (machine : UndecidableMachine Conf) where
  traj : ℕ → ℝ → Fin P.n → ℝ
  init_at_zero : ∀ w : ℕ, traj w 0 = P.realInit w
  solves_ode : ∀ (w : ℕ) (t : ℝ), 0 ≤ t →
    HasDerivAt (traj w) (P.evalVF (traj w t)) t
  bounded : ∃ B : ℝ, 0 < B ∧ ∀ (w : ℕ) (t : ℝ) (i : Fin P.n),
    0 ≤ t → |traj w t i| ≤ B
  encoder_presented : ∃ f : ℕ → Fin P.n → ℤ × ℕ, Computable f ∧
    ∀ w i, (f w i).2 ≠ 0 ∧ P.init w i = (f w i).1 / ((f w i).2 : ℚ)
  readout : ChartThresholdReadout P.n
  correct_halt : ∀ w, machine.toDiscreteMachine.haltsOn w →
    ∃ T : ℝ, ∀ t ≥ T, traj w t ∈ readout.HaltRegion
  correct_nonhalt : ∀ w, ¬ machine.toDiscreteMachine.haltsOn w →
    ∃ T : ℝ, ∀ t ≥ T, traj w t ∈ readout.NonhaltRegion

end Ripple.BoundedUniversality.BGP
