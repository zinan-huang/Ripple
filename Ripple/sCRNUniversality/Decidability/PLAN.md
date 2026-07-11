# Theorem 4.2 — CRN/Petri Coverability Decidability

## Algorithm: Backward Coverability

Upward-closed set saturation via finite bases. Terminate by Dickson's lemma.

## Module DAG (from ChatGPT R2, refined)

```
StateOrder → FiniteBasis → BackwardPre → BackwardAlgorithm → Coverability
                 ↑              ↑
           PetriMonotone    WQOUpward
```

## Module Plan

| # | Module | Purpose | Est LOC |
|---|--------|---------|---------|
| 1 | StateOrder | Pointwise ≤ on State S, decidable, executable | 200-500 |
| 2 | FiniteBasis | Finite basis of upward-closed sets, minimal, up_minimal | 500-1500 |
| 3 | PetriMonotone | Petri firing is monotone (covers preserved) | 300-800 |
| 4 | BackwardPre | Predecessor computation: pre(t, b) | 300-800 |
| 5 | WQOUpward | Dickson → upward-closed chain stabilizes | 500-1500 |
| 6 | BackwardAlgorithm | Saturation loop with termination proof | 500-1500 |
| 7 | Coverability | coverable? : Bool + correctness = Thm 4.2 | 300-800 |

Total estimate: **2600-7400 LOC** (my estimate, tighter than ChatGPT's 26-43K).

ChatGPT's higher estimate includes extensive decidable instance proofs and
API surface. Many of those are already handled by Mathlib or can be done
with `decide`/`omega`.

## Key Decisions

1. **Basis = Finset (State S)** (not Set). Executable.
2. **Closure test = Boolean** (B.memUpBool m for all m in preBasis).
   Avoids needing Finset equality on normalized bases.
3. **Termination = WellFounded on Finset inclusion** via Dickson antichain bound.
4. **Use Fintype, not Finite** for species/transitions. Computable.

## Blocking Points

1. WQO → loop termination (Dickson + strict ascending chain bound)
2. Nat subtraction in predecessor (arithmetic-heavy)
3. up_minimal (normalization preserves upward closure)
4. Well-founded recursive saturate

## Status

- [x] 1. StateOrder (merged into FiniteBasis)
- [x] 2. FiniteBasis (FiniteBasis.lean)
- [x] 3. PetriMonotone (PetriMonotone.lean)
- [x] 4. BackwardPre (Predecessor.lean + Saturation.lean)
- [x] 5. WQOUpward (WQOUpward.lean)
- [x] 6. BackwardAlgorithm (BackwardAlgorithm.lean)
- [x] 7. Coverability (Coverability.lean)

## Sorry Inventory (0 remaining — ALL CLEAR)

All sorry entries resolved:
- `stateWQO`: one-line via `Pi.wellQuasiOrderedLE` (Dickson's lemma from Mathlib).
- `exists_fuel_saturates`: WellFounded.induction on `wellFounded_finset_upClosure`.
- `up_strict_of_not_closed`: contrapositive — if ↑(step B) ⊆ ↑B then isClosedStrong.

## Key Design Decision: isClosedStrong vs isClosed

The original `isClosed` (Saturation.lean) guards predecessor checks with `canProducePetri`.
This is incomplete for the backward coverability proof because when ¬canProducePetri,
the predecessor is still well-defined (Nat subtraction clamps to 0) and the upward
closure may not be backward-closed without checking those predecessors.

`isClosedStrong` (BackwardAlgorithm.lean) drops the guard and checks ALL transitions
unconditionally. This is necessary and sufficient for backward closure of ↑B.
