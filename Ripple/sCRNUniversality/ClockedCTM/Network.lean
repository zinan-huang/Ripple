/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.Lyapunov

/-!
# The repaired clocked CTM network `N♯(𝒞, l)` (SCWB Fig. 3.2, repaired)

Soloveichik, Cook, Winfree, Bruck, "Computation with finite stochastic chemical reaction
networks" (Caltech etr085v2), Fig. 3.2, with the three repairs of
`docs/audit/FIX3-SCWB-T32.md` §3.3 (defects F1–F3 of the figure are proved there).

A *clocked Turing machine* (CTM) is a finite set of states `Q` and a total transition
`next q b = (q', z)`: read the first tape bit `b`, delete it, append `z`, go to `q'`.

Species (`Sp Q L`, clock length `l = L + 1`):
* state species `S_{q,1}, S_{q,2}, S_{q,3}` (`s1 q`, `s2 q`, `s3 q`), `R_q` (`rq q`),
  `U_{q,b}` (`u q b`), the tick molecule `I` (`i`);
* clock `C_1, …, C_l` (`clk 0, …, clk L`), `A` (`acc`), `A*` (`accS`);
* memory `M, M†, M*, T, T†, T*, D, D*, B, B*, K_1, K_2` (`mem x`, `x : Mem`).

Reactions (`Rx Q L`), all bimolecular with two distinct reactants and rate constant 1:

| label | reaction |
|---|---|
| `tick` | `C_1 + A* → C_l + I + A*` |
| `up c`, `down c` | `C_c + A → C_{c+1} + A`, `C_{c+1} + A* → C_c + A*` |
| `eps q b` | `I + U_{q,b} → S_{q_b,1}` |
| `auto41 q b` | `U_{q,b} + S_{q_b,1} → 2 S_{q_b,1}` |
| `adv12 q`, `adv23 q` | `I + S_{q,1} → S_{q,2}`, `I + S_{q,2} → S_{q,3}` |
| `auto12 q`, `auto23 q` | `S_{q,1} + S_{q,2} → 2 S_{q,2}`, `S_{q,2} + S_{q,3} → 2 S_{q,3}` |
| `adv3 q` | `I + S_{q,3} → R_q` |
| `rt q`, `rm q` | `R_q + T → U_{q,0} + T`, `R_q + M → U_{q,1} + M` |
| `auto34 q b` | `S_{q,3} + U_{q,b} → 2 U_{q,b}` |
| `rsM q`, `rsT q`, `rsD q`, `rsB q` | `M† → M`, `T† → T`, `D* → D`, `B* → B`, catalysed by `S_{q,2}` |
| `pair`, `k2`, `k1` | `T + M → T* + M*`, `K_2 + M† → K_1`, `K_1 + M† → ∅` |
| `cMs`, `cTs`, `cT`, `cM`, `cD`, `cB` (`q b`) | `M* → M`, `T* → T†`, `T → T†`, `M → 3M†`, `D → 3K_{b+1} + D*`, `B → (z_b+1) M† + B*`, catalysed by `U_{q,b}` |

The network `net C L` depends only on the CTM `C` and the clock length.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

/-- A clocked Turing machine: total transition `next q b = (q', z)`. -/
structure CTM (Q : Type) where
  next : Q → Bool → Q × Bool

/-- Memory species. -/
inductive Mem
  | m | md | ms | t | td | ts | d | ds | b | bs | k1 | k2
  deriving DecidableEq, Fintype

/-- Species of `N♯`. -/
inductive Sp (Q : Type) (L : ℕ) where
  | s1 (q : Q)
  | s2 (q : Q)
  | s3 (q : Q)
  | rq (q : Q)
  | u (q : Q) (b : Bool)
  | i
  | clk (c : Fin (L + 1))
  | acc
  | accS
  | mem (x : Mem)
  deriving DecidableEq, Fintype

variable {Q : Type} {L : ℕ}

/-- Reaction labels of `N♯`. -/
inductive Rx (Q : Type) (L : ℕ) where
  | tick
  | up (c : Fin L)
  | down (c : Fin L)
  | eps (q : Q) (b : Bool)
  | auto41 (q : Q) (b : Bool)
  | adv12 (q : Q)
  | auto12 (q : Q)
  | adv23 (q : Q)
  | auto23 (q : Q)
  | adv3 (q : Q)
  | rt (q : Q)
  | rm (q : Q)
  | auto34 (q : Q) (b : Bool)
  | rsM (q : Q)
  | rsT (q : Q)
  | rsD (q : Q)
  | rsB (q : Q)
  | pair
  | k2
  | k1
  | cMs (q : Q) (b : Bool)
  | cTs (q : Q) (b : Bool)
  | cT (q : Q) (b : Bool)
  | cM (q : Q) (b : Bool)
  | cD (q : Q) (b : Bool)
  | cB (q : Q) (b : Bool)
  deriving DecidableEq, Fintype

variable [Fintype Q] [DecidableEq Q]

/-! ### Complexes and reactions -/

/-- The complex consisting of one molecule of `s`. -/
def one (s : Sp Q L) : Complex (Sp Q L) := fun s' => if s' = s then 1 else 0

@[simp] theorem one_apply (s s' : Sp Q L) : one s s' = if s' = s then 1 else 0 := rfl

/-- The unit-rate bimolecular reaction `s₁ + s₂ → out`. -/
def bimol (s₁ s₂ : Sp Q L) (out : Complex (Sp Q L)) : Reaction (Sp Q L) :=
  { l := one s₁ + one s₂, r := out, k := 1 }

/-- First reactant. -/
def src1 : Rx Q L → Sp Q L
  | .tick => .clk 0
  | .up c => .clk c.castSucc
  | .down c => .clk c.succ
  | .eps _ _ => .i
  | .auto41 q b => .u q b
  | .adv12 _ => .i
  | .auto12 q => .s1 q
  | .adv23 _ => .i
  | .auto23 q => .s2 q
  | .adv3 _ => .i
  | .rt q => .rq q
  | .rm q => .rq q
  | .auto34 q _ => .s3 q
  | .rsM q => .s2 q
  | .rsT q => .s2 q
  | .rsD q => .s2 q
  | .rsB q => .s2 q
  | .pair => .mem .t
  | .k2 => .mem .k2
  | .k1 => .mem .k1
  | .cMs q b => .u q b
  | .cTs q b => .u q b
  | .cT q b => .u q b
  | .cM q b => .u q b
  | .cD q b => .u q b
  | .cB q b => .u q b

/-- Second reactant. -/
def src2 (C : CTM Q) : Rx Q L → Sp Q L
  | .tick => .accS
  | .up _ => .acc
  | .down _ => .accS
  | .eps q b => .u q b
  | .auto41 q b => .s1 (C.next q b).1
  | .adv12 q => .s1 q
  | .auto12 q => .s2 q
  | .adv23 q => .s2 q
  | .auto23 q => .s3 q
  | .adv3 q => .s3 q
  | .rt _ => .mem .t
  | .rm _ => .mem .m
  | .auto34 q b => .u q b
  | .rsM _ => .mem .md
  | .rsT _ => .mem .td
  | .rsD _ => .mem .ds
  | .rsB _ => .mem .bs
  | .pair => .mem .m
  | .k2 => .mem .md
  | .k1 => .mem .md
  | .cMs _ _ => .mem .ms
  | .cTs _ _ => .mem .ts
  | .cT _ _ => .mem .t
  | .cM _ _ => .mem .m
  | .cD _ _ => .mem .d
  | .cB _ _ => .mem .b

/-- Products. -/
def out (C : CTM Q) : Rx Q L → Complex (Sp Q L)
  | .tick => one (.clk (Fin.last L)) + one .i + one .accS
  | .up c => one (.clk c.succ) + one .acc
  | .down c => one (.clk c.castSucc) + one .accS
  | .eps q b => one (.s1 (C.next q b).1)
  | .auto41 q b => one (.s1 (C.next q b).1) + one (.s1 (C.next q b).1)
  | .adv12 q => one (.s2 q)
  | .auto12 q => one (.s2 q) + one (.s2 q)
  | .adv23 q => one (.s3 q)
  | .auto23 q => one (.s3 q) + one (.s3 q)
  | .adv3 q => one (.rq q)
  | .rt q => one (.u q false) + one (.mem .t)
  | .rm q => one (.u q true) + one (.mem .m)
  | .auto34 q b => one (.u q b) + one (.u q b)
  | .rsM q => one (.s2 q) + one (.mem .m)
  | .rsT q => one (.s2 q) + one (.mem .t)
  | .rsD q => one (.s2 q) + one (.mem .d)
  | .rsB q => one (.s2 q) + one (.mem .b)
  | .pair => one (.mem .ts) + one (.mem .ms)
  | .k2 => one (.mem .k1)
  | .k1 => 0
  | .cMs q b => one (.u q b) + one (.mem .m)
  | .cTs q b => one (.u q b) + one (.mem .td)
  | .cT q b => one (.u q b) + one (.mem .td)
  | .cM q b => one (.u q b) + 3 • one (.mem .md)
  | .cD q b => one (.u q b) + 3 • one (.mem (if b then .k2 else .k1)) + one (.mem .ds)
  | .cB q b => one (.u q b) + ((C.next q b).2.toNat + 1) • one (.mem .md) + one (.mem .bs)

/-- The reactions of `N♯`. -/
def rxn (C : CTM Q) (i : Rx Q L) : Reaction (Sp Q L) := bimol (src1 i) (src2 C i) (out C i)

@[simp] theorem rxn_l (C : CTM Q) (i : Rx Q L) : (rxn C i).l = one (src1 i) + one (src2 C i) :=
  rfl

@[simp] theorem rxn_r (C : CTM Q) (i : Rx Q L) : (rxn C i).r = out C i := rfl

/-- **The repaired clocked CTM network** `N♯(C, L + 1)`. -/
def net (C : CTM Q) (L : ℕ) : Network (Sp Q L) where
  I := Rx Q L
  rxn := rxn C

theorem net_hasPositiveRates (C : CTM Q) (L : ℕ) : (net C L).hasPositiveRates := by
  intro i
  show (0 : Rate) < 1
  exact zero_lt_one

instance (C : CTM Q) (L : ℕ) : DecidableEq (net C L).I := by
  change DecidableEq (Rx Q L); infer_instance

theorem src1_ne_src2 (C : CTM Q) (i : Rx Q L) : src1 i ≠ src2 C i := by
  cases i with
  | up c => simp only [src1, src2, ne_eq, reduceCtorEq, not_false_eq_true]
  | down c => simp only [src1, src2, ne_eq, reduceCtorEq, not_false_eq_true]
  | _ => simp [src1, src2]

/-- Mass-action propensity of a reaction of `N♯` (unit rate constant). -/
theorem propensity_rxn (C : CTM Q) (i : Rx Q L) (z : State (Sp Q L)) :
    (rxn C i).propensity z = ((z (src1 i) * z (src2 C i) : ℕ) : Rate) := by
  have h := src1_ne_src2 C i
  unfold Reaction.propensity rxn bimol
  simp only [one_mul]
  rw [Finset.prod_eq_mul_of_mem (src1 i) (src2 C i) (Finset.mem_univ _) (Finset.mem_univ _) h]
  · simp [h, h.symm, Nat.cast_mul]
  · intro c _ hc
    simp [hc.1, hc.2]

/-- Unit-rate propensity as a natural number. -/
def rate (C : CTM Q) (i : Rx Q L) (z : State (Sp Q L)) : ℕ := z (src1 i) * z (src2 C i)

theorem enabled_iff (C : CTM Q) (i : Rx Q L) (z : State (Sp Q L)) :
    (rxn C i).enabled z ↔ rate C i z ≠ 0 := by
  have h := src1_ne_src2 C i
  constructor
  · intro hen
    have h1 := hen (src1 i)
    have h2 := hen (src2 C i)
    simp only [rxn, bimol, Pi.add_apply, one_apply, if_true, h, h.symm, if_false] at h1 h2
    simp only [rate, ne_eq, mul_eq_zero, not_or]
    omega
  · intro hr s
    simp only [rate, ne_eq, mul_eq_zero, not_or] at hr
    simp only [rxn, bimol, Pi.add_apply, one_apply]
    by_cases h1 : s = src1 i
    · subst h1; simp [h]; omega
    · by_cases h2 : s = src2 C i
      · subst h2; simp [h1]; omega
      · simp [h1, h2]

theorem fire_apply (C : CTM Q) (i : Rx Q L) (z : State (Sp Q L)) (s : Sp Q L) :
    (rxn C i).fire z s =
      z s - ((if s = src1 i then 1 else 0) + (if s = src2 C i then 1 else 0)) + out C i s := rfl

/-- Total unit-rate propensity. -/
def btot (C : CTM Q) (z : State (Sp Q L)) : ℕ := ∑ i : Rx Q L, rate C i z

theorem totalPropensity_eq (C : CTM Q) (z : State (Sp Q L)) :
    (net C L).totalPropensity z = (btot C z : Rate) := by
  unfold Network.totalPropensity btot
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => propensity_rxn C i z

/-- If some reaction is enabled the state is not terminal. -/
theorem not_terminal_of_rate (C : CTM Q) {z : State (Sp Q L)} {i : Rx Q L}
    (h : rate C i z ≠ 0) : ¬ (net C L).Terminal z :=
  fun hT => hT i ((enabled_iff C i z).mpr h)

theorem btot_pos_of_rate (C : CTM Q) {z : State (Sp Q L)} {i : Rx Q L}
    (h : rate C i z ≠ 0) : 0 < btot C z :=
  lt_of_lt_of_le (Nat.pos_of_ne_zero h)
    (Finset.single_le_sum (f := fun i => rate C i z) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))

/-- The jump-chain step by an enabled label. -/
theorem stateStep_of_rate (C : CTM Q) {z : State (Sp Q L)} {i : Rx Q L}
    (h : rate C i z ≠ 0) : stateStep (net C L) z (some i) = (rxn C i).fire z := by
  unfold stateStep
  rw [dif_neg (not_terminal_of_rate C h),
    fireOptionSanitized_of_enabled (net C L) z i (not_terminal_of_rate C h)
      ((enabled_iff C i z).mpr h)]
  rfl

theorem pmf_none (C : CTM Q) {z : State (Sp Q L)} (hT : ¬ (net C L).Terminal z) :
    massActionPMF (net C L) (net_hasPositiveRates C L) z none = 0 := by
  change massActionWeight (net C L) (net_hasPositiveRates C L) z none = 0
  simp only [massActionWeight, hT, dite_false]

open scoped ENNReal in
theorem pmf_some (C : CTM Q) {z : State (Sp Q L)} (hT : ¬ (net C L).Terminal z) (i : Rx Q L) :
    massActionPMF (net C L) (net_hasPositiveRates C L) z (some i) =
      (rate C i z : ℝ≥0∞) / (btot C z : ℝ≥0∞) := by
  change massActionWeight (net C L) (net_hasPositiveRates C L) z (some i) = _
  simp only [massActionWeight, hT, dite_false]
  have hB : (btot C z : NNReal) ≠ 0 := by
    have : ∃ j, rate C j z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hT fun j hj => (enabled_iff C j z).mp hj (h j)
    obtain ⟨j, hj⟩ := this
    exact_mod_cast (btot_pos_of_rate C hj).ne'
  rw [jumpProbAt, show (net C L).rxn i = rxn C i from rfl, propensity_rxn,
    totalPropensity_eq, ← ENNReal.coe_nnratCast, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_natCast, ENNReal.coe_div hB, ENNReal.coe_natCast, ENNReal.coe_natCast]
  rfl

end Ripple.sCRNUniversality.ClockedCTM
