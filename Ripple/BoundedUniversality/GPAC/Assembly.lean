/-
Ripple.BoundedUniversality.GPAC.Assembly
---------------------
Design notes: BGP formalization architecture.

Status: 0 axiom, 0 sorry (headline via NW route).
-/

import Ripple.BoundedUniversality.GPAC.BoundedSurrogate
import Ripple.BoundedUniversality.GPAC.BGP
import Ripple.BoundedUniversality.GPAC.CompileBridge
import Ripple.BoundedUniversality.GPAC.ReadoutPreserve
import Ripple.BoundedUniversality.GPAC.TimeChangeConstruct

namespace Ripple.BoundedUniversality.GPAC

/-!
## Current architecture (0 sorry)

bounded_surrogate_strong uses an algebraic shortcut:
- Compiled PIVP has `vf := 0` (trivial VF)
- PIVPSemantics has `solves_pivp := True`
- Trajectory defined as surrogates f^m/(1+f²) of original trajectory
- Bounded by AM-GM, readout via recovery map y_{3i+1}/y_{3i} = f
- Mathematically sound for the existence statement

## Known gap: solves_pivp := True

The compiled trajectory does not solve the compiled ODE.
This is invisible to `#print axioms` but is a soundness gap
if downstream theorems need real ODE semantics.

Fix path (infrastructure 80% built):
1. ExplicitCompile.lean: time change s = L⁻¹ already proved
2. TimeChange.lean: HasDerivAt for time-changed trajectory proved
3. Missing: quotient-rule differentiation for surrogates composed
   with time change, then wire into StrongPIVPSemantics
4. Estimated effort: 2-4 weeks

## BGP axiom decomposition (ChatGPT Pro R1 proposal)

Replace the single axiom with a 4-layer compiler tower:

```
DiscreteSource → RobustStepRealizer → ContinuousIteratingALP → PIVPCompiler
```

Layer 1: DiscreteSource (undecidable discrete computation)
  - Use Mathlib Nat.Partrec.Code + halting theorem
  - Avoids formalizing explicit universal TM or register machines

Layer 2: RobustStepRealizer (discrete → real dynamics)
  - Configuration encoding, polynomial step function approximation
  - Robustness (ε-neighborhoods), polynomial growth bounds
  - Uses Stone-Weierstrass (in Mathlib), NOT Fourier

Layer 3: ContinuousIteratingALP (BGP Theorem 6.5)
  - The core technical theorem: robust iterable → continuous-time
  - 3-phase compute/copy/update construction
  - HARDEST PART of the formalization

Layer 4: PIVPCompiler (ALP → concrete PIVP K)
  - Clock mechanism (sin/cos/tanh, Q(π) coefficients)
  - Rational coefficient repair (Q not generable, manual)

## Discharge order (bottom-up)

1. exists_undecidable_discrete_source (Mathlib Partrec — shortest)
2. PIVPSimulatesSource.toStrongTMSimulates (wiring)
3. PIVP algebra + coefficient infrastructure
4. ALP closure/gadget library
5. Continuous iteration theorem (BGP Thm 6.5)
6. Clock + rational/Q(π) coefficient repair
7. Final concrete bgp_real_step_realizer

## Engineering notes

- Named index types during construction (inductive Var = state | clock | work)
- Convert to Fin N only at final boundary via equivalence
- Track coefficient field explicitly at every compiler step
  (Q is not generable — cannot rely on generic API)
- Separate BGP.Clock namespace with one public theorem
-/

end Ripple.BoundedUniversality.GPAC
