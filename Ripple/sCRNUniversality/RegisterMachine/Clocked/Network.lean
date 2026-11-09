/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.RegisterMachine.Basic
import Ripple.sCRNUniversality.Stochastic.MassAction.PrefixMarginal

/-!
# The clocked register-machine network of SCWB Fig. 3.1

Soloveichik, Cook, Winfree, Bruck, "Computation with finite stochastic chemical reaction
networks" (Caltech etr085v2), Fig. 3.1: for a register machine `M` and clock length `l = L + 1`
(`L ≥ 1`), species `S_q`, `M_r`, the dummy catalyst `C`, clock species `C_1, …, C_l` (here
`clk 0, …, clk L`), `A`, `A*`, and reactions (all rate constants 1, all bimolecular):

* `inc_q : C + S_q → C + S_j + M_r` for `code q = inc r j`;
* `dec1_q : S_q + M_r → S_j`, `dec2_q : C_1 + S_q → C_l + S_k` for `code q = decJz r j k`;
* `up_c : C_c + A → C_{c+1} + A`, `down_c : C_{c+1} + A* → C_c + A*`.

The network `net M L` depends only on `M` and `L`; the accuracy count `a = #A`, the input and
the clock start enter through the initial state `enc a σ₀`.  This file also gives the reduced
description used by the error analysis (`docs/audit/FIX3-SCWB.md` §3): every state reachable
from an encoded state is `enc a σ` with `σ = ((q, y), c)`, the unit-rate propensity of reaction
`i` at `enc a σ` is the natural number `beta a i σ`, and an enabled reaction moves `enc a σ` to
`enc a (tgt i σ)`.
-/

namespace Ripple.sCRNUniversality.RegisterMachine

deriving instance DecidableEq for Instr

namespace Clocked

open Stochastic Stochastic.MassAction

variable {Reg Label : Type} [Fintype Reg] [DecidableEq Reg] [Fintype Label] [DecidableEq Label]

/-- Species of the clocked RM network. -/
inductive Sp (Reg Label : Type) (L : ℕ) where
  | st (q : Label)
  | reg (r : Reg)
  | dum
  | clk (c : Fin (L + 1))
  | acc
  | accS
  deriving DecidableEq

variable {L : ℕ}

/-- `Sp` as a sum type. -/
def spEquiv : Sp Reg Label L ≃ Label ⊕ Reg ⊕ Unit ⊕ Fin (L + 1) ⊕ Unit ⊕ Unit where
  toFun
    | .st q => .inl q
    | .reg r => .inr (.inl r)
    | .dum => .inr (.inr (.inl ()))
    | .clk c => .inr (.inr (.inr (.inl c)))
    | .acc => .inr (.inr (.inr (.inr (.inl ()))))
    | .accS => .inr (.inr (.inr (.inr (.inr ()))))
  invFun
    | .inl q => .st q
    | .inr (.inl r) => .reg r
    | .inr (.inr (.inl _)) => .dum
    | .inr (.inr (.inr (.inl c))) => .clk c
    | .inr (.inr (.inr (.inr (.inl _)))) => .acc
    | .inr (.inr (.inr (.inr (.inr _)))) => .accS
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with q | r | ⟨⟩ | c | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype (Sp Reg Label L) := Fintype.ofEquiv _ spEquiv.symm

/-- The complex `s₁ + s₂`. -/
def pair (s₁ s₂ : Sp Reg Label L) : Complex (Sp Reg Label L) :=
  fun s => (if s = s₁ then 1 else 0) + (if s = s₂ then 1 else 0)

/-- The unit-rate bimolecular reaction `s₁ + s₂ → out`. -/
def bimol (s₁ s₂ : Sp Reg Label L) (out : Complex (Sp Reg Label L)) :
    Reaction (Sp Reg Label L) :=
  { l := pair s₁ s₂, r := out, k := 1 }

/-- Mass-action propensity of a bimolecular reaction with distinct reactants. -/
theorem propensity_bimol {s₁ s₂ : Sp Reg Label L} (h : s₁ ≠ s₂)
    (out : Complex (Sp Reg Label L)) (z : State (Sp Reg Label L)) :
    (bimol s₁ s₂ out).propensity z = ((z s₁ * z s₂ : ℕ) : Rate) := by
  unfold Reaction.propensity bimol
  simp only [one_mul]
  rw [Finset.prod_eq_mul_of_mem s₁ s₂ (Finset.mem_univ _) (Finset.mem_univ _) h]
  · simp [pair, h, h.symm, Nat.cast_mul]
  · intro c _ hc
    simp [pair, hc.1, hc.2]

/-- Increment instructions `q ↦ inc r j`, as `(q, r, j)`. -/
def IncIdx (M : RM Reg Label) : Type :=
  {p : Label × Reg × Label // M.code p.1 = .inc p.2.1 p.2.2}

/-- Decrement instructions `q ↦ decJz r j k`, as `(q, r, j, k)`. -/
def DecIdx (M : RM Reg Label) : Type :=
  {p : Label × Reg × Label × Label // M.code p.1 = .decJz p.2.1 p.2.2.1 p.2.2.2}

instance (M : RM Reg Label) : Fintype (IncIdx M) := by unfold IncIdx; infer_instance
instance (M : RM Reg Label) : DecidableEq (IncIdx M) := by unfold IncIdx; infer_instance
instance (M : RM Reg Label) : Fintype (DecIdx M) := by unfold DecIdx; infer_instance
instance (M : RM Reg Label) : DecidableEq (DecIdx M) := by unfold DecIdx; infer_instance

/-- Reaction labels: `inc`, `dec1`, `dec2` per instruction, `up`, `down` per clock edge. -/
abbrev Idx (M : RM Reg Label) (L : ℕ) : Type :=
  IncIdx M ⊕ DecIdx M ⊕ DecIdx M ⊕ Fin L ⊕ Fin L

/-- The reactions of SCWB Fig. 3.1. -/
def rxnOf (M : RM Reg Label) (L : ℕ) : Idx M L → Reaction (Sp Reg Label L)
  | .inl p => bimol .dum (.st p.1.1)
      (fun s => pair .dum (.st p.1.2.2) s + if s = .reg p.1.2.1 then 1 else 0)
  | .inr (.inl d) => bimol (.st d.1.1) (.reg d.1.2.1) (fun s => if s = .st d.1.2.2.1 then 1 else 0)
  | .inr (.inr (.inl d)) => bimol (.clk 0) (.st d.1.1) (pair (.clk (Fin.last L)) (.st d.1.2.2.2))
  | .inr (.inr (.inr (.inl j))) => bimol (.clk j.castSucc) .acc (pair (.clk j.succ) .acc)
  | .inr (.inr (.inr (.inr j))) => bimol (.clk j.succ) .accS (pair (.clk j.castSucc) .accS)

/-- **The clocked register-machine network** `N(M, L+1)` of SCWB Fig. 3.1. -/
def net (M : RM Reg Label) (L : ℕ) : Network (Sp Reg Label L) where
  I := Idx M L
  rxn := rxnOf M L

theorem net_allUnitRate (M : RM Reg Label) (L : ℕ) : (net M L).allUnitRate := by
  intro i; rcases i with p | d | d | j | j <;> rfl

theorem net_hasPositiveRates (M : RM Reg Label) (L : ℕ) : (net M L).hasPositiveRates :=
  Network.hasPositiveRates_of_allUnitRate (net_allUnitRate M L)

instance (M : RM Reg Label) (L : ℕ) : DecidableEq (net M L).I := by
  change DecidableEq (Idx M L); infer_instance

/-! ### Reduced states -/

/-- Outer part of a reduced state: machine label and registers. -/
abbrev Outer (Reg Label : Type) := Label × (Reg → ℕ)

/-- Reduced state: outer part and clock position (`0` is `C_1`, `L` is `C_l`). -/
abbrev RState (Reg Label : Type) (L : ℕ) := Outer Reg Label × Fin (L + 1)

/-- The CRN state with one `S_q`, registers `y`, `C = 1`, one clock molecule at `c`, `#A = a`,
`#A* = 1`. -/
def enc (a : ℕ) (σ : RState Reg Label L) : State (Sp Reg Label L)
  | .st q => if q = σ.1.1 then 1 else 0
  | .reg r => σ.1.2 r
  | .dum => 1
  | .clk c => if c = σ.2 then 1 else 0
  | .acc => a
  | .accS => 1

omit [Fintype Reg] [DecidableEq Reg] [Fintype Label] in
theorem enc_injective (a : ℕ) : Function.Injective (enc (Reg := Reg) (Label := Label) (L := L) a) := by
  intro σ τ h
  obtain ⟨⟨q, y⟩, c⟩ := σ
  obtain ⟨⟨q', y'⟩, c'⟩ := τ
  have hq := congrFun h (.st q)
  have hc := congrFun h (.clk c)
  simp only [enc, if_true] at hq hc
  have hq' : q = q' := by by_contra hne; simp [hne] at hq
  have hc' : c = c' := by by_contra hne; simp [hne] at hc
  have hy : y = y' := funext fun r => congrFun h (.reg r)
  subst hq' hc' hy; rfl

/-- Unit-rate propensity of reaction `i` at `enc a σ`. -/
def beta (M : RM Reg Label) (a : ℕ) : Idx M L → RState Reg Label L → ℕ
  | .inl p, σ => if p.1.1 = σ.1.1 then 1 else 0
  | .inr (.inl d), σ => if d.1.1 = σ.1.1 then σ.1.2 d.1.2.1 else 0
  | .inr (.inr (.inl d)), σ => if (0 : Fin (L + 1)) = σ.2 ∧ d.1.1 = σ.1.1 then 1 else 0
  | .inr (.inr (.inr (.inl j))), σ => if j.castSucc = σ.2 then a else 0
  | .inr (.inr (.inr (.inr j))), σ => if j.succ = σ.2 then 1 else 0

/-- Target reduced state of reaction `i` from `σ` (meaningful when `beta a i σ ≠ 0`). -/
def tgt (M : RM Reg Label) : Idx M L → RState Reg Label L → RState Reg Label L
  | .inl p, σ => ((p.1.2.2, Function.update σ.1.2 p.1.2.1 (σ.1.2 p.1.2.1 + 1)), σ.2)
  | .inr (.inl d), σ => ((d.1.2.2.1, Function.update σ.1.2 d.1.2.1 (σ.1.2 d.1.2.1 - 1)), σ.2)
  | .inr (.inr (.inl d)), σ => ((d.1.2.2.2, σ.1.2), Fin.last L)
  | .inr (.inr (.inr (.inl j))), σ => (σ.1, j.succ)
  | .inr (.inr (.inr (.inr j))), σ => (σ.1, j.castSucc)

/-- Whether a label is a machine reaction (`inc`, `dec1`, `dec2`). -/
def isRM {M : RM Reg Label} : Idx M L → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr _)) => false

theorem propensity_enc (M : RM Reg Label) (a : ℕ) (i : Idx M L) (σ : RState Reg Label L) :
    ((net M L).rxn i).propensity (enc a σ) = (beta M a i σ : Rate) := by
  rcases i with p | d | d | j | j <;>
  · change (bimol _ _ _).propensity _ = _
    rw [propensity_bimol (by simp)]
    simp only [enc, beta]
    split_ifs <;> simp_all

theorem castSucc_ne_succ' {n : ℕ} (j : Fin n) : j.castSucc ≠ j.succ :=
  (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne

theorem succ_ne_castSucc' {n : ℕ} (j : Fin n) : j.succ ≠ j.castSucc :=
  (show j.castSucc < j.succ from Fin.castSucc_lt_succ).ne'

/-- An enabled reaction moves `enc a σ` to `enc a (tgt i σ)`. -/
theorem fire_enc (M : RM Reg Label) (a : ℕ) (i : Idx M L) (σ : RState Reg Label L)
    (hβ : beta M a i σ ≠ 0) :
    ((net M L).rxn i).fire (enc a σ) = enc a (tgt M i σ) := by
  obtain ⟨⟨q, y⟩, c⟩ := σ
  funext s
  rcases i with ⟨⟨q₀, r₀, j₀⟩, hp⟩ | ⟨⟨q₀, r₀, j₀, k₀⟩, hd⟩ | ⟨⟨q₀, r₀, j₀, k₀⟩, hd⟩ | j | j
  · simp only [beta, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hβ
    subst hβ
    cases s <;> simp only [net, rxnOf, bimol, Reaction.fire, pair, enc, tgt,
      Function.update_apply] <;> split_ifs <;> simp_all
  · simp only [beta, ne_eq, ite_eq_right_iff, Classical.not_imp] at hβ
    obtain ⟨hq, hy⟩ := hβ
    subst hq
    cases s <;> simp only [net, rxnOf, bimol, Reaction.fire, pair, enc, tgt,
      Function.update_apply] <;> split_ifs <;> simp_all <;> omega
  · simp only [beta, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hβ
    obtain ⟨hc, hq⟩ := hβ
    subst hc hq
    cases s <;> simp only [net, rxnOf, bimol, Reaction.fire, pair, enc, tgt] <;>
      split_ifs <;> simp_all <;> omega
  · have h1 := castSucc_ne_succ' j
    have h2 := succ_ne_castSucc' j
    by_cases hc : j.castSucc = c
    · subst hc
      have ha : 0 < a := by simp [beta] at hβ; omega
      clear hβ
      cases s <;> simp only [net, rxnOf, bimol, Reaction.fire, pair, enc, tgt] <;>
        split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    · simp [beta, hc] at hβ
  · have h1 := castSucc_ne_succ' j
    have h2 := succ_ne_castSucc' j
    by_cases hc : j.succ = c
    · subst hc
      cases s <;> simp only [net, rxnOf, bimol, Reaction.fire, pair, enc, tgt] <;>
        split_ifs <;> simp_all [Fin.ext_iff] <;> omega
    · simp [beta, hc] at hβ

end Clocked

end Ripple.sCRNUniversality.RegisterMachine
