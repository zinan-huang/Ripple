# Termination of Backward Coverability Saturation

## Confirmed Approach (R4/R5)

### Theorem
In a WQO (X, ≤), every ascending chain U₀ ⊆ U₁ ⊆ ... of upward-closed
sets stabilizes.

### Proof
Assume ∀ n, U_n ⊊ U_{n+1}. Pick x_n ∈ U_{n+1} \ U_n.

By WQO, ∃ i < j with x_i ≤ x_j.
- x_i ∈ U_{i+1} ⊆ U_j (ascending chain, i+1 ≤ j)
- U_j upward-closed, x_i ∈ U_j, x_i ≤ x_j ⟹ x_j ∈ U_j
- But x_j ∉ U_j (by construction). Contradiction. ∎

### Lean Implementation

```lean
-- The semantic well-founded relation on finite bases
def upClosure [LE α] (B : Finset α) : Set α :=
  fun x => ∃ b ∈ B, b ≤ x

-- Key theorem: no infinite strictly ascending chain of upward closures
theorem wellFounded_finset_upClosure_strict
    [Preorder α] [WellQuasiOrderedLE α] :
    WellFounded (fun B' B : Finset α => upClosure B ⊂ upClosure B')

-- Use for saturation loop:
-- termination_by B
-- decreasing_by exact ⟨subset_proof, strict_proof⟩
```

### Key Lean Steps

1. Define `upClosure` and prove `IsUpperSet (upClosure B)`
2. Prove `wellFounded_strictSuperset_upperSets` for abstract upper sets
3. Derive `wellFounded_finset_upClosure_strict` via `WellFounded.comap`
4. Use in `saturate` definition with `termination_by`

### LOC Estimate for Termination Module

~200-500 LOC including:
- wellFounded_strictSuperset_upperSets (main theorem, ~80-150 lines)
- Comap to finite bases (~20-50 lines)
- Helper lemmas for upClosure API (~100-200 lines)
