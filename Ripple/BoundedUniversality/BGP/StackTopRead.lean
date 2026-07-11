import Ripple.BoundedUniversality.BGP.MachineInstance

/-!
Ripple.BoundedUniversality.BGP.StackTopRead
-----------------------
Top-read robustness for the fractional base-`B` stack encoding: the gate's stack-TOP read
amplifies an approximation error by **exactly one factor of `B`, independent of stack depth**.

This is the algebraic heart of all-cycle faithfulness for the clock-driven selector simulating
`M_U`.  The §3.3 audit flagged the headline's full-config depth-budget (`selector_MU_utube_all`'s
`hradius` with `dep = D − j`) as vacuous for `j > D`, and two ChatGPT rounds read the per-cycle
pop Jacobian `X' = B·X − c` as `mult = B`, concluding "finite-depth only".  That reading misses the
encoding's depth scaling: `stackCodeU` is FRACTIONAL (push `X' = (c + X)/B` divides; values in
`[0,1)`), so push (÷B) and pop (×B) are INVERSE.  A buried symbol's error is recovered — not
compounded — on exposure, and reading the top is a SINGLE factor of `B`.  The lemma below makes that
precise: the error bound `B·ε` carries NO dependence on the tail `L` (the stack depth).
-/

namespace Ripple.BoundedUniversality.BGP.MachineInstance

open Turing.PartrecToTM2

/-- **Stack-top read amplifies error by exactly `B`, independent of depth.**
If `Xtilde` approximates the code of `a :: L` within `ε`, then the recovered top contribution
`B·Xtilde − stackCodeU L` lies within `B·ε` of the top digit `dig a`.

Crucially the bound `B·ε` is INDEPENDENT of `L`: reading the top costs ONE factor of `B`, never
`B^(depth)`.  Proof: `stackCodeU_pop` gives `B·code(a::L) − dig a = code(L)` exactly, so
`(B·Xtilde − code(L)) − dig a = B·(Xtilde − code(a::L))`, whence the bound is `B·ε`. -/
theorem stackTop_read_error (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ) (a : Γ') (L : List Γ')
    {Xtilde ε : ℚ} (hX : |Xtilde - stackCodeU B dig (a :: L)| ≤ ε) :
    |((B : ℚ) * Xtilde - stackCodeU B dig L) - (dig a : ℚ)| ≤ (B : ℚ) * ε := by
  have hpop := stackCodeU_pop B hB dig a L
  have key : ((B : ℚ) * Xtilde - stackCodeU B dig L) - (dig a : ℚ)
      = (B : ℚ) * (Xtilde - stackCodeU B dig (a :: L)) := by
    rw [← hpop]; ring
  rw [key, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (B : ℚ))]
  exact mul_le_mul_of_nonneg_left hX (by positivity)

/-- **The exposed tail is bounded in `[0, 1)` at every depth.**  After a pop the recovered tail
`stackCodeU L` is nonneg and `< 1` (`≤ bot B / B < 1`), so the next top digit `dig a` is the
nearest integer to `B·code(a::L)`: the symbolic information sits in the leading digit, uniformly in
depth.  Together with `stackTop_read_error` this is why a uniform absolute write accuracy
`ε < 1/(2B)` suffices to read every top correctly, at any stack depth. -/
theorem exposed_tail_lt_one (dig : Γ' → ℕ)
    (hdig : ∀ g, dig g < bot B_U) (L : List Γ') :
    stackCodeU B_U dig L < 1 := by
  have h4 := B_U_ge_four
  have h := stackCodeU_lt_missing_digit B_U B_U_ge_four dig hdig L
  have hbot : ((B_U - 1 : ℕ) : ℚ) / (B_U : ℚ) < 1 := by
    have hBpos : (0 : ℚ) < (B_U : ℚ) := by exact_mod_cast (by omega : 0 < B_U)
    rw [div_lt_one hBpos]
    exact_mod_cast (by omega : (B_U - 1 : ℕ) < B_U)
  exact lt_of_lt_of_le h (le_of_lt hbot)

/-- **Push CONTRACTS the stack-code error by `1/B`.**  Writing the pushed symbol `a` on top of an
approximation `Xtilde` of `code(L)` within `e` gives `(dig a + Xtilde)/B`, which approximates
`code(a::L)` within `e/B`.  This is the burial half of burial/exposure cancellation — slope `1/B`,
matching the exposure-weighted tube's branch slope `B^(H_j − H_{j+1}) = B^(-1)` on a push (height +1). -/
theorem stackCode_push_error (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ) (a : Γ') (L : List Γ')
    {Xtilde e : ℚ} (hX : |Xtilde - stackCodeU B dig L| ≤ e) :
    |((dig a : ℚ) + Xtilde) / B - stackCodeU B dig (a :: L)| ≤ e / B := by
  have hBpos : (0 : ℚ) < B := by exact_mod_cast (by omega : 0 < B)
  have key : ((dig a : ℚ) + Xtilde) / B - stackCodeU B dig (a :: L)
      = (Xtilde - stackCodeU B dig L) / B := by
    rw [stackCodeU_push]; field_simp; ring
  rw [key, abs_div, abs_of_pos hBpos]
  gcongr

/-- **Pop EXPOSES with slope `B`.**  From an approximation `Xtilde` of `code(a::L)` within `e`, the
popped value `B·Xtilde − dig a` approximates `code(L)` within `B·e`.  Slope `B`, matching the
exposure-weighted tube's branch slope `B^(H_j − H_{j+1}) = B^(1)` on a pop (height −1).  Together with
`stackCode_push_error` (slope `1/B`), the `stackCodeU` encoding realises the exposure-tube hypothesis,
grounding the abstract `Ripple.BoundedUniversality.BGP.localview_tube_all` in the concrete fractional stack encoding. -/
theorem stackCode_pop_error (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ) (a : Γ') (L : List Γ')
    {Xtilde e : ℚ} (hX : |Xtilde - stackCodeU B dig (a :: L)| ≤ e) :
    |((B : ℚ) * Xtilde - (dig a : ℚ)) - stackCodeU B dig L| ≤ (B : ℚ) * e := by
  have hpop := stackCodeU_pop B hB dig a L
  have key : ((B : ℚ) * Xtilde - (dig a : ℚ)) - stackCodeU B dig L
      = (B : ℚ) * (Xtilde - stackCodeU B dig (a :: L)) := by
    rw [← hpop]; ring
  rw [key, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (B : ℚ))]
  exact mul_le_mul_of_nonneg_left hX (by positivity)

/-- **One PUSH cycle: the exposure-tube recurrence, dynamically.**  If the held analog value `u_old`
approximates the old stack `code(L)` within `e`, and the cycle WRITES the analog push result
`(dig a + u_old)/B` into `u_new` within the write defect `ξ` (the gate computed the push of symbol `a`),
then `u_new` approximates the new stack `code(a::L)` within `e/B + ξ` — i.e. the stack-code error
transforms with branch slope `1/B` plus the write defect.  This is the concrete per-cycle realisation
of `expWeight_nonexpansive`'s hypothesis on a push (height +1). -/
theorem cycle_push_error_transform (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ) (a : Γ') (L : List Γ')
    {u_old u_new e ξ : ℚ}
    (hold : |u_old - stackCodeU B dig L| ≤ e)
    (hwrite : |u_new - ((dig a : ℚ) + u_old) / B| ≤ ξ) :
    |u_new - stackCodeU B dig (a :: L)| ≤ e / B + ξ := by
  calc |u_new - stackCodeU B dig (a :: L)|
      ≤ |u_new - ((dig a : ℚ) + u_old) / B|
          + |((dig a : ℚ) + u_old) / B - stackCodeU B dig (a :: L)| := abs_sub_le _ _ _
    _ ≤ ξ + e / B := add_le_add hwrite (stackCode_push_error B hB dig a L hold)
    _ = e / B + ξ := by ring

/-- **One POP cycle: the exposure-tube recurrence, dynamically.**  If `u_old` approximates `code(a::L)`
within `e`, and the cycle writes the analog pop result `B·u_old − dig a` into `u_new` within `ξ`, then
`u_new` approximates the new stack `code(L)` within `B·e + ξ` — branch slope `B` plus write defect.
The concrete per-cycle realisation of `expWeight_nonexpansive`'s hypothesis on a pop (height −1). -/
theorem cycle_pop_error_transform (B : ℕ) (hB : 4 ≤ B) (dig : Γ' → ℕ) (a : Γ') (L : List Γ')
    {u_old u_new e ξ : ℚ}
    (hold : |u_old - stackCodeU B dig (a :: L)| ≤ e)
    (hwrite : |u_new - ((B : ℚ) * u_old - (dig a : ℚ))| ≤ ξ) :
    |u_new - stackCodeU B dig L| ≤ (B : ℚ) * e + ξ := by
  calc |u_new - stackCodeU B dig L|
      ≤ |u_new - ((B : ℚ) * u_old - (dig a : ℚ))|
          + |((B : ℚ) * u_old - (dig a : ℚ)) - stackCodeU B dig L| := abs_sub_le _ _ _
    _ ≤ ξ + (B : ℚ) * e := add_le_add hwrite (stackCode_pop_error B hB dig a L hold)
    _ = (B : ℚ) * e + ξ := by ring

end Ripple.BoundedUniversality.BGP.MachineInstance
