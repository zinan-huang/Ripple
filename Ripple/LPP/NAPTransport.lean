/-
  Ripple.LPP.NAPTransport — the transportation construction behind Theorem 1 of
  the PP-to-NAP write-up, in abstract form.

  Setting. Species `V` (the lifted variables `v_α`), monomials `D` (the degree-`2m` monomials
  `δ`), a `LiftData` recording how a pair of species forms a monomial (`pair β γ = β + γ`,
  commutative and cancellative) and the positive normalisations `mult β` (the multinomial
  coefficients). A demand `p : D → V → ℚ` is the coefficient table `p_{α,δ}` of the pushforward
  of the lifted dynamics. A weighted protocol `w : Shape V → ℚ` assigns a rate to every reaction
  shape `r1 + r2 → p1 + p2`; its coefficient at `(δ, α)` is
  `Σ_{shapes with pair r1 r2 = δ} w · mult r1 · mult r2 · net α`, and `w` realises `p` if these agree
  (identity (2.1) of the write-up).

  Main theorem `exists_nap_realizing`: if for every `δ`
    (h0) `Σ_α p δ α = 0`,
    (h1) `p δ α < 0 → α` is a half of `δ`,
    (h2) `0 < p δ α → ∃ β γ, pair β γ = δ ∧ β ≠ α ∧ γ ≠ α` (per-monomial splittability),
  then there is a non-negative weighted protocol, all of whose positive-rate shapes are
  non-autocatalytic, realising `p`. The construction is the proportional transport
  `a_{st} = (−p_s) p_t / T` from consumed to produced species, routed directly through the pair
  `{s, δ−s}` or, when the target is the complement of the source, through a hub supplied by (h2).

  (h0) and (h1) hold for every pushforward (Lemma 2 of the write-up); (h2) is the criterion
  (equivalent to (C1),(C2) for cubing a quartic protocol, and automatic after the r²-trick).
-/

import Ripple.LPP.NAPProtocol

namespace Ripple
namespace NAPTransport

open Finset

/-- A reaction shape `r1 + r2 → p1 + p2`. -/
abbrev Shape (V : Type) := V × V × V × V

variable {V D : Type} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Net stoichiometric change of species `α` under the shape (rational-valued). -/
def net (sh : Shape V) (α : V) : ℚ :=
  (if sh.2.2.1 = α then 1 else 0) + (if sh.2.2.2 = α then 1 else 0)
    - (if sh.1 = α then 1 else 0) - (if sh.2.1 = α then 1 else 0)

/-- A shape is non-autocatalytic: no reactant is net-produced. -/
def ShapeNAP (sh : Shape V) : Prop := net sh sh.1 ≤ 0 ∧ net sh sh.2.1 ≤ 0

/-- Pairing of species into monomials and positive normalisations. -/
structure LiftData (V D : Type) where
  pair : V → V → D
  pair_comm : ∀ β γ, pair β γ = pair γ β
  pair_cancel : ∀ β γ γ', pair β γ = pair β γ' → γ = γ'
  mult : V → ℚ
  mult_pos : ∀ β, 0 < mult β

/-- A weighted protocol: the rate constant of each shape (`0` = absent). -/
abbrev WProtocol (V : Type) := Shape V → ℚ

/-- Every shape with positive rate is non-autocatalytic. -/
def WProtocol.IsNAP (w : WProtocol V) : Prop := ∀ sh, 0 < w sh → ShapeNAP sh

/-- Selector: the weight with which a shape contributes to the coefficient at `(δ, α)`. -/
def sel (L : LiftData V D) (δ : D) (α : V) (sh : Shape V) : ℚ :=
  if L.pair sh.1 sh.2.1 = δ then L.mult sh.1 * L.mult sh.2.1 * net sh α else 0

/-- Coefficient of the balance field of `w` at monomial `δ`, species `α`. -/
def coeffAt (L : LiftData V D) (w : WProtocol V) (δ : D) (α : V) : ℚ :=
  ∑ sh, w sh * sel L δ α sh

/-- `w` realises the demand table `p`. -/
def Realizes (L : LiftData V D) (w : WProtocol V) (p : D → V → ℚ) : Prop :=
  ∀ δ α, coeffAt L w δ α = p δ α

/-- The transfer shape `s + c → t + c`. -/
def transfer (s c t : V) : Shape V := (s, c, t, c)

theorem net_transfer (s c t α : V) :
    net (transfer s c t) α = (if t = α then 1 else 0) - (if s = α then 1 else 0) := by
  simp only [net, transfer]
  ring

theorem transfer_nap {s c t : V} (hts : t ≠ s) (htc : t ≠ c) : ShapeNAP (transfer s c t) := by
  refine ⟨?_, ?_⟩
  · show net (transfer s c t) s ≤ 0
    rw [net_transfer]
    simp [hts]
  · show net (transfer s c t) c ≤ 0
    rw [net_transfer]
    simp only [htc, if_false]
    split_ifs <;> norm_num

section Construction

variable (L : LiftData V D) (p : D → V → ℚ)

/-- The complement of a half `s` of `δ` (junk value `s` if `s` is not a half). -/
noncomputable def compl (δ : D) (s : V) : V :=
  if h : ∃ γ, L.pair s γ = δ then Classical.choose h else s

theorem pair_compl {δ : D} {s : V} (h : ∃ γ, L.pair s γ = δ) :
    L.pair s (compl L δ s) = δ := by
  unfold compl
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- A hub for `(δ, t)`: a half of `δ` different from `t` whose partner is also different from `t`. -/
noncomputable def hub (δ : D) (t : V) : V :=
  if h : ∃ β γ, L.pair β γ = δ ∧ β ≠ t ∧ γ ≠ t then Classical.choose h else t

theorem hub_spec {δ : D} {t : V} (h : ∃ β γ, L.pair β γ = δ ∧ β ≠ t ∧ γ ≠ t) :
    ∃ γ, L.pair (hub L δ t) γ = δ ∧ hub L δ t ≠ t ∧ γ ≠ t := by
  unfold hub
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Total positive mass of the demand at `δ`. -/
noncomputable def T (δ : D) : ℚ := ∑ t, max (p δ t) 0

/-- Proportional transport amount from `s` (consumed) to `t` (produced). -/
noncomputable def amount (δ : D) (s t : V) : ℚ := (-p δ s) * p δ t / T p δ

/-- Contribution of the shape `X` carrying the amount `a` (rate `a / (mult r1 · mult r2)`). -/
noncomputable def term (a : ℚ) (X sh : Shape V) : ℚ :=
  if sh = X then a / (L.mult X.1 * L.mult X.2.1) else 0

/-- The routed contribution of the pair `(s, t)` at `δ`: direct transfer, or a detour through
the hub when `t` is the complement of `s`. -/
noncomputable def contrib (δ : D) (s t : V) (sh : Shape V) : ℚ :=
  if p δ s < 0 ∧ 0 < p δ t then
    (if t = compl L δ s then
      term L (amount p δ s t) (transfer s (compl L δ s) (hub L δ t)) sh
        + term L (amount p δ s t) (transfer (hub L δ t) (compl L δ (hub L δ t)) t) sh
    else term L (amount p δ s t) (transfer s (compl L δ s) t) sh)
  else 0

/-- The transportation protocol. -/
noncomputable def wTransport : WProtocol V := fun sh => ∑ δ, ∑ s, ∑ t, contrib L p δ s t sh

theorem sum_term_sel (a : ℚ) (X : Shape V) (δ : D) (α : V) :
    ∑ sh, term L a X sh * sel L δ α sh
      = if L.pair X.1 X.2.1 = δ then a * net X α else 0 := by
  unfold term
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ X (fun sh => a / (L.mult X.1 * L.mult X.2.1) * sel L δ α sh)]
  simp only [Finset.mem_univ, if_true]
  unfold sel
  split_ifs
  · have h1 := L.mult_pos X.1
    have h2 := L.mult_pos X.2.1
    field_simp
  · simp

theorem sum_contrib_sel (h1 : ∀ δ α, p δ α < 0 → ∃ γ, L.pair α γ = δ)
    (h2 : ∀ δ α, 0 < p δ α → ∃ β γ, L.pair β γ = δ ∧ β ≠ α ∧ γ ≠ α)
    (δ δ' : D) (s t α : V) :
    ∑ sh, contrib L p δ s t sh * sel L δ' α sh
      = if (p δ s < 0 ∧ 0 < p δ t) ∧ δ = δ' then
          amount p δ s t * ((if t = α then 1 else 0) - (if s = α then 1 else 0))
        else 0 := by
  unfold contrib
  by_cases hpos : p δ s < 0 ∧ 0 < p δ t
  · have hs : L.pair s (compl L δ s) = δ := pair_compl L (h1 δ s hpos.1)
    simp only [if_pos hpos]
    by_cases htc : t = compl L δ s
    · obtain ⟨γ, hγ, hh1, hh2⟩ := hub_spec L (h2 δ t hpos.2)
      have hhub : L.pair (hub L δ t) (compl L δ (hub L δ t)) = δ := pair_compl L ⟨γ, hγ⟩
      simp only [if_pos htc]
      simp only [add_mul, Finset.sum_add_distrib, sum_term_sel, net_transfer]
      simp only [transfer, hs, hhub]
      by_cases hδ : δ = δ'
      · subst hδ
        simp [hpos]
        try ring
      · simp only [hδ, if_false, and_false, add_zero]
    · simp only [if_neg htc]
      rw [sum_term_sel, net_transfer]
      simp only [transfer, hs]
      by_cases hδ : δ = δ'
      · subst hδ
        simp [hpos]
      · simp only [hδ, if_false, and_false]
  · simp only [if_neg hpos]
    simp [hpos]

/-- Positive and negative masses agree when the demand sums to zero. -/
theorem sum_neg_eq_T (h0 : ∀ δ, ∑ α, p δ α = 0) (δ : D) :
    ∑ s, max (-p δ s) 0 = T p δ := by
  unfold T
  have : ∀ a : ℚ, max (-a) 0 = max a 0 - a := by
    intro a
    by_cases h : 0 ≤ a
    · rw [max_eq_right (by linarith), max_eq_left h]; ring
    · have h' : a < 0 := lt_of_not_ge h
      rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  simp only [this, Finset.sum_sub_distrib, h0 δ, sub_zero]

theorem T_pos_of_pos (δ : D) (α : V) (h : 0 < p δ α) : 0 < T p δ := by
  unfold T
  have hle : max (p δ α) 0 ≤ ∑ t, max (p δ t) 0 :=
    Finset.single_le_sum (f := fun t => max (p δ t) 0) (fun t _ => le_max_right _ _) (Finset.mem_univ α)
  rw [max_eq_left h.le] at hle
  linarith

theorem T_pos_of_neg (h0 : ∀ δ, ∑ α, p δ α = 0) (δ : D) (α : V) (h : p δ α < 0) :
    0 < T p δ := by
  rw [← sum_neg_eq_T p h0 δ]
  have hle : max (-p δ α) 0 ≤ ∑ t, max (-p δ t) 0 :=
    Finset.single_le_sum (f := fun t => max (-p δ t) 0) (fun t _ => le_max_right _ _) (Finset.mem_univ α)
  rw [max_eq_left (by linarith)] at hle
  linarith

theorem sum_ite_neg (δ : D) :
    ∑ s, (if p δ s < 0 then -p δ s else 0) = ∑ s, max (-p δ s) 0 := by
  apply Finset.sum_congr rfl
  intro s _
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]

theorem sum_ite_pos (δ : D) :
    ∑ t, (if 0 < p δ t then p δ t else 0) = T p δ := by
  unfold T
  apply Finset.sum_congr rfl
  intro t _
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith)]

theorem sum4_comm (f : Shape V → D → V → V → ℚ) :
    ∑ sh, ∑ δ, ∑ s, ∑ t, f sh δ s t = ∑ δ, ∑ s, ∑ t, ∑ sh, f sh δ s t := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]

/-- The transportation protocol realises the demand. -/
theorem wTransport_realizes (h0 : ∀ δ, ∑ α, p δ α = 0)
    (h1 : ∀ δ α, p δ α < 0 → ∃ γ, L.pair α γ = δ)
    (h2 : ∀ δ α, 0 < p δ α → ∃ β γ, L.pair β γ = δ ∧ β ≠ α ∧ γ ≠ α) :
    Realizes L (wTransport L p) p := by
  intro δ' α
  unfold coeffAt wTransport
  simp only [Finset.sum_mul]
  rw [sum4_comm (fun sh δ s t => contrib L p δ s t sh * sel L δ' α sh)]
  simp only [sum_contrib_sel L p h1 h2]
  rw [Finset.sum_eq_single δ']
  · simp only [and_true]
    -- split the summand
    have hsplit : ∀ s t, (if p δ' s < 0 ∧ 0 < p δ' t then
          amount p δ' s t * ((if t = α then 1 else 0) - (if s = α then 1 else 0)) else 0)
        = (if p δ' s < 0 ∧ 0 < p δ' t then amount p δ' s t * (if t = α then 1 else 0) else 0)
          - (if p δ' s < 0 ∧ 0 < p δ' t then amount p δ' s t * (if s = α then 1 else 0) else 0) := by
      intro s t
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_sub_distrib]
    have hA : ∀ s, ∑ t, (if p δ' s < 0 ∧ 0 < p δ' t then amount p δ' s t * (if t = α then 1 else 0) else 0)
        = if p δ' s < 0 ∧ 0 < p δ' α then amount p δ' s α else 0 := by
      intro s
      rw [Finset.sum_eq_single α]
      · simp
      · intro t _ ht
        simp [ht]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hB : ∑ s, ∑ t, (if p δ' s < 0 ∧ 0 < p δ' t then amount p δ' s t * (if s = α then 1 else 0) else 0)
        = ∑ t, (if p δ' α < 0 ∧ 0 < p δ' t then amount p δ' α t else 0) := by
      rw [Finset.sum_eq_single α]
      · simp
      · intro s _ hs
        simp [hs]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [hA, hB]
    unfold amount
    by_cases hα : 0 < p δ' α
    · have hT : 0 < T p δ' := T_pos_of_pos p δ' α hα
      have hnα : ¬ p δ' α < 0 := not_lt.mpr hα.le
      simp only [hα, and_true, hnα, false_and, if_false, Finset.sum_const_zero, sub_zero]
      have hs : ∀ s, (if p δ' s < 0 then -p δ' s * p δ' α / T p δ' else 0)
          = (if p δ' s < 0 then -p δ' s else 0) * p δ' α / T p δ' := by
        intro s; split_ifs <;> simp
      simp only [hs]
      rw [← Finset.sum_div, ← Finset.sum_mul, sum_ite_neg, sum_neg_eq_T p h0]
      field_simp
    · simp only [hα, and_false, if_false, Finset.sum_const_zero, zero_sub]
      by_cases hneg : p δ' α < 0
      · have hT : 0 < T p δ' := T_pos_of_neg p h0 δ' α hneg
        simp only [hneg, true_and]
        have ht : ∀ t, (if 0 < p δ' t then -p δ' α * p δ' t / T p δ' else 0)
            = -p δ' α * (if 0 < p δ' t then p δ' t else 0) / T p δ' := by
          intro t; split_ifs <;> simp
        simp only [ht]
        rw [← Finset.sum_div, ← Finset.mul_sum, sum_ite_pos]
        field_simp
      · have h0' : p δ' α = 0 := le_antisymm (not_lt.mp hα) (not_lt.mp hneg)
        simp [hneg, h0']
  · intro δ _ hδ
    simp [hδ]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem term_nonneg {a : ℚ} (ha : 0 ≤ a) (X sh : Shape V) : 0 ≤ term L a X sh := by
  unfold term
  split_ifs
  · exact div_nonneg ha (mul_pos (L.mult_pos X.1) (L.mult_pos X.2.1)).le
  · exact le_rfl

theorem amount_nonneg (δ : D) (s t : V) (hpos : p δ s < 0 ∧ 0 < p δ t) :
    0 ≤ amount p δ s t := by
  unfold amount
  have hT := T_pos_of_pos p δ t hpos.2
  have : 0 ≤ -p δ s * p δ t := mul_nonneg (by linarith [hpos.1]) hpos.2.le
  exact div_nonneg this hT.le

theorem contrib_nonneg (δ : D) (s t : V) (sh : Shape V) :
    0 ≤ contrib L p δ s t sh := by
  unfold contrib
  split_ifs with hpos htc
  · exact add_nonneg (term_nonneg L (amount_nonneg p δ s t hpos) _ _)
      (term_nonneg L (amount_nonneg p δ s t hpos) _ _)
  · exact term_nonneg L (amount_nonneg p δ s t hpos) _ _
  · exact le_rfl

theorem wTransport_nonneg (sh : Shape V) :
    0 ≤ wTransport L p sh := by
  unfold wTransport
  refine Finset.sum_nonneg fun δ _ => Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => ?_
  exact contrib_nonneg L p δ s t sh

theorem term_eq_zero_of_not_nap {a : ℚ} {X sh : Shape V} (hX : ShapeNAP X) (hsh : ¬ ShapeNAP sh) :
    term L a X sh = 0 := by
  unfold term
  rw [if_neg]
  intro h
  exact hsh (h ▸ hX)

theorem contrib_eq_zero_of_not_nap
    (h1 : ∀ δ α, p δ α < 0 → ∃ γ, L.pair α γ = δ)
    (h2 : ∀ δ α, 0 < p δ α → ∃ β γ, L.pair β γ = δ ∧ β ≠ α ∧ γ ≠ α)
    (δ : D) (s t : V) {sh : Shape V} (hsh : ¬ ShapeNAP sh) :
    contrib L p δ s t sh = 0 := by
  unfold contrib
  split_ifs with hpos htc
  · obtain ⟨γ, hγ, hh1, hh2⟩ := hub_spec L (h2 δ t hpos.2)
    have hs : L.pair s (compl L δ s) = δ := pair_compl L (h1 δ s hpos.1)
    have hhub : L.pair (hub L δ t) (compl L δ (hub L δ t)) = δ := pair_compl L ⟨γ, hγ⟩
    have hγ' : compl L δ (hub L δ t) = γ := L.pair_cancel _ _ _ (hhub.trans hγ.symm)
    -- hub ≠ s: otherwise its partner would be the complement of s, i.e. t
    have hhs : hub L δ t ≠ s := by
      intro h
      apply hh2
      rw [← hγ', h, ← htc]
    have hX1 : ShapeNAP (transfer s (compl L δ s) (hub L δ t)) :=
      transfer_nap hhs (by rw [← htc]; exact hh1)
    have hX2 : ShapeNAP (transfer (hub L δ t) (compl L δ (hub L δ t)) t) :=
      transfer_nap (Ne.symm hh1) (by rw [hγ']; exact Ne.symm hh2)
    rw [term_eq_zero_of_not_nap L hX1 hsh, term_eq_zero_of_not_nap L hX2 hsh, add_zero]
  · have hts : t ≠ s := by
      intro h; rw [h] at hpos; linarith [hpos.1, hpos.2]
    exact term_eq_zero_of_not_nap L (transfer_nap hts htc) hsh
  · rfl

theorem wTransport_isNAP
    (h1 : ∀ δ α, p δ α < 0 → ∃ γ, L.pair α γ = δ)
    (h2 : ∀ δ α, 0 < p δ α → ∃ β γ, L.pair β γ = δ ∧ β ≠ α ∧ γ ≠ α) :
    (wTransport L p).IsNAP := by
  intro sh hpos
  by_contra hsh
  have : wTransport L p sh = 0 := by
    unfold wTransport
    simp [contrib_eq_zero_of_not_nap L p h1 h2 _ _ _ hsh]
  linarith

/-- **Transportation theorem.** Under (h0)–(h2) the demand table is realised by a non-negative
weighted protocol all of whose reactions are non-autocatalytic. -/
theorem exists_nap_realizing (h0 : ∀ δ, ∑ α, p δ α = 0)
    (h1 : ∀ δ α, p δ α < 0 → ∃ γ, L.pair α γ = δ)
    (h2 : ∀ δ α, 0 < p δ α → ∃ β γ, L.pair β γ = δ ∧ β ≠ α ∧ γ ≠ α) :
    ∃ w : WProtocol V, (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧ Realizes L w p :=
  ⟨wTransport L p, wTransport_nonneg L p, wTransport_isNAP L p h1 h2,
    wTransport_realizes L p h0 h1 h2⟩

end Construction

/-! ## Necessity

If `δ` has a single pair of halves `{β, γ}` (up to order), any NAP realisation forces
`p δ β ≤ 0` and `p δ γ ≤ 0`: the only reactions with monomial `δ` have reactants `β, γ`, and a
non-autocatalytic reaction never net-produces a reactant. -/

theorem coeffAt_nonpos_of_unique_pair (L : LiftData V D) (w : WProtocol V)
    (hw : ∀ sh, 0 ≤ w sh) (hnap : w.IsNAP) (δ : D) (β : V)
    (huniq : ∀ sh : Shape V, L.pair sh.1 sh.2.1 = δ → sh.1 = β ∨ sh.2.1 = β) :
    coeffAt L w δ β ≤ 0 := by
  unfold coeffAt
  apply Finset.sum_nonpos
  intro sh _
  unfold sel
  split_ifs with hδ
  · by_cases hpos : (0 : ℚ) < w sh
    · have hn := hnap sh hpos
      have hnet : net sh β ≤ 0 := by
        rcases huniq sh hδ with h | h
        · rw [← h]; exact hn.1
        · rw [← h]; exact hn.2
      have hm : 0 ≤ L.mult sh.1 * L.mult sh.2.1 :=
        (mul_pos (L.mult_pos _) (L.mult_pos _)).le
      have := mul_nonpos_of_nonneg_of_nonpos hm hnet
      exact mul_nonpos_of_nonneg_of_nonpos hpos.le this
    · have hzero : w sh = 0 := le_antisymm (not_lt.mp hpos) (hw sh)
      rw [hzero, zero_mul]
  · simp

/-- Necessity: at a monomial whose every pair contains `β`, a realised demand is non-positive at `β`. -/
theorem realizes_nonpos_of_unique_pair (L : LiftData V D) (w : WProtocol V) (p : D → V → ℚ)
    (hw : ∀ sh, 0 ≤ w sh) (hnap : w.IsNAP) (hr : Realizes L w p) (δ : D) (β : V)
    (huniq : ∀ sh : Shape V, L.pair sh.1 sh.2.1 = δ → sh.1 = β ∨ sh.2.1 = β) :
    p δ β ≤ 0 := by
  rw [← hr δ β]
  exact coeffAt_nonpos_of_unique_pair L w hw hnap δ β huniq

/-! ## Instantiation: multi-indices of weight `m`

The species are the exponent vectors of weight `m` (entries bounded by `m`), monomials are exponent
vectors with entries bounded by `2m`, `pair` is addition, and `mult` is the multinomial coefficient.
This is the `LiftData` of the degree-`m` Veronese lift (`m = 3`: cubing, `m = 2`: squaring). -/

section MultiIndex

variable (n m : ℕ)

/-- Multi-indices of weight `m` on `n` species, with entries in `Fin (m+1)`. -/
def MI := {α : Fin n → Fin (m + 1) // ∑ j, (α j : ℕ) = m}

instance : Fintype (MI n m) := by unfold MI; infer_instance
instance : DecidableEq (MI n m) := by unfold MI; infer_instance

/-- Sum of two multi-indices, as a monomial of degree `2m`. -/
def MI.add (β γ : MI n m) : Fin n → Fin (2 * m + 1) :=
  fun j => ⟨(β.1 j : ℕ) + γ.1 j, by
    have h1 := (β.1 j).is_lt
    have h2 := (γ.1 j).is_lt
    omega⟩

theorem MI.add_comm (β γ : MI n m) : MI.add n m β γ = MI.add n m γ β := by
  funext j
  apply Fin.ext
  simp [MI.add, Nat.add_comm]

theorem MI.add_cancel (β γ γ' : MI n m) (h : MI.add n m β γ = MI.add n m β γ') : γ = γ' := by
  apply Subtype.ext
  funext j
  have hj := congrFun h j
  simp only [MI.add, Fin.mk.injEq] at hj
  exact Fin.ext (Nat.add_left_cancel hj)

/-- Multinomial coefficient `m! / ∏ α_j!`. -/
noncomputable def MI.mult (β : MI n m) : ℚ :=
  (Nat.factorial m : ℚ) / ∏ j, (Nat.factorial (β.1 j : ℕ) : ℚ)

theorem MI.mult_pos (β : MI n m) : 0 < MI.mult n m β := by
  unfold MI.mult
  apply div_pos
  · exact_mod_cast Nat.factorial_pos m
  · exact Finset.prod_pos fun j _ => by exact_mod_cast Nat.factorial_pos _

/-- The lift data of the degree-`m` Veronese lift. -/
noncomputable def veroneseLift : LiftData (MI n m) (Fin n → Fin (2 * m + 1)) where
  pair := MI.add n m
  pair_comm := MI.add_comm n m
  pair_cancel := MI.add_cancel n m
  mult := MI.mult n m
  mult_pos := MI.mult_pos n m

/-- **Theorem 1, sufficiency, for the Veronese lift.** Any demand table on degree-`2m` monomials and
weight-`m` species that sums to zero, is negative only at halves, and is per-monomial splittable, is
realised by a non-negative non-autocatalytic weighted protocol. -/
theorem exists_nap_realizing_veronese (p : (Fin n → Fin (2 * m + 1)) → MI n m → ℚ)
    (h0 : ∀ δ, ∑ α, p δ α = 0)
    (h1 : ∀ δ α, p δ α < 0 → ∃ γ, MI.add n m α γ = δ)
    (h2 : ∀ δ α, 0 < p δ α → ∃ β γ, MI.add n m β γ = δ ∧ β ≠ α ∧ γ ≠ α) :
    ∃ w : WProtocol (MI n m), (∀ sh, 0 ≤ w sh) ∧ w.IsNAP ∧ Realizes (veroneseLift n m) w p :=
  exists_nap_realizing (veroneseLift n m) p h0 h1 h2

end MultiIndex

end NAPTransport
end Ripple
