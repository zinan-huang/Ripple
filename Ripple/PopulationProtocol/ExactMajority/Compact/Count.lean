/-
# The compact state type of Nonuniform Majority and its `O(L)` count

`CompactState L K` is the set of normal forms of `normalize` (`Compact/Live.lean`): the agents of
the flat type `AgentState L K` whose dead fields hold their defaults. This file gives the type,
its encoding and decoding, and the count:

* `card_compactState_le`: `Fintype.card (CompactState L K) ≤ 73920 ((K + 53)(L + 1) + 4)`;
  at the paper's parameters `L = ⌈log₂ n⌉`, `K = 45` this is `73920 (98 ⌈log₂ n⌉ + 102)`,
  i.e. `O(log n)` states (`compact_state_count_clog`).

The constant `73920 = 2 · 3 · 11 · 5 · 2 · 7 · 2 · 8` is the product of the ranges of the eight
`O(1)` fields that every state keeps (`input`, `output`, `phase`, `role`, `assigned`,
`smallBias`, `full`, `opinions`); the factor `(K + 53)(L + 1) + 4` counts the at most one live
`Θ(L)` field (`bias`, `hour`, `minute` or `counter`, or none). The protocol on this type and the
transported correctness theorem are in `Compact/State.lean`.
-/

import Ripple.PopulationProtocol.ExactMajority.Compact.Live

namespace Ripple.PopulationProtocol.ExactMajority

namespace Compact

variable {L K : ℕ}

/-- The compact state type: normal forms of the flat agent state. -/
def CompactState (L K : ℕ) : Type := { a : AgentState L K // normalize a = a }

namespace CompactState

instance : DecidableEq (CompactState L K) := Subtype.instDecidableEq

instance : Fintype (CompactState L K) := Subtype.fintype _

/-- Encode a flat agent by its normal form. -/
def enc (a : AgentState L K) : CompactState L K := ⟨normalize a, normalize_normalize a⟩

/-- Decode (the underlying flat agent). -/
def emb (x : CompactState L K) : AgentState L K := x.1

@[simp] lemma emb_enc (a : AgentState L K) : emb (enc a) = normalize a := rfl

@[simp] lemma enc_emb (x : CompactState L K) : enc (emb x) = x := Subtype.ext x.2

lemma good_emb (x : CompactState L K) : Good (emb x) := by
  unfold emb
  rw [← x.2]
  exact good_normalize _

lemma enc_eq_enc_iff (a b : AgentState L K) : enc a = enc b ↔ normalize a = normalize b :=
  Subtype.ext_iff

end CompactState


/-! ### The state count -/

/-- The eight `O(1)` fields. -/
abbrev ConstFields :=
  Opinion × Output × Fin 11 × Role × Bool × Fin 7 × Bool × Fin 8

/-- The at most one live `Θ(L)` field. -/
abbrev BigField (L K : ℕ) :=
  Option (Bias L ⊕ Fin (L + 1) ⊕ Fin (K * (L + 1) + 1) ⊕ Fin (50 * (L + 1) + 1))

/-- The live `Θ(L)` field of an agent, following the live table. -/
def bigField (a : AgentState L K) : BigField L K :=
  let p := a.phase.val
  if liveHour p a.role (a.bias = .zero) then some (Sum.inr (Sum.inl a.hour))
  else if liveBias p a.role then some (Sum.inl a.bias)
  else if liveCounter p a.role (a.minute.val = K * (L + 1)) then
    some (Sum.inr (Sum.inr (Sum.inr a.counter)))
  else if liveMinute p a.role then some (Sum.inr (Sum.inr (Sum.inl a.minute)))
  else none

/-- The injection of the compact states into `ConstFields × BigField`. -/
def encodeCompact (x : CompactState L K) : ConstFields × BigField L K :=
  ((x.1.input, x.1.output, x.1.phase, x.1.role, x.1.assigned, x.1.smallBias, x.1.full,
    x.1.opinions), bigField x.1)

/-- Injectivity of the live-field encoding at one phase value. -/
def BigFieldInj (p : ℕ) : Prop :=
  ∀ (a a' : AgentState L K), a.phase.val = p →
    a.input = a'.input → a.output = a'.output → a.phase = a'.phase → a.role = a'.role →
    a.assigned = a'.assigned → a.smallBias = a'.smallBias → a.full = a'.full →
    a.opinions = a'.opinions → bigField a = bigField a' → normalize a = normalize a'

/-- Destructure both agents, fix the phase value, and split on the role and the live table. -/
local macro "bigfield_tac" : tactic => `(tactic| (
  intro a a' hp hin hout hph hrole hasg hsb hfull hop hbig
  rcases a with ⟨i, o, ph, r, g, b, sb, h, m, f, op, c⟩
  rcases a' with ⟨i', o', ph', r', g', b', sb', h', m', f', op', c'⟩
  simp only at hin hout hph hrole hasg hsb hfull hop hp
  subst hin hout hph hrole hasg hsb hfull hop
  obtain ⟨phv, hphv⟩ := ph
  simp only at hp
  subst hp
  cases r <;>
    simp [bigField, normalize, normalizeAtVal, liveBias, liveHour, liveMinute, liveCounter]
      at hbig ⊢ <;>
    (try split_ifs at hbig ⊢) <;> simp_all <;> (try (apply Fin.ext; omega))))

theorem bigFieldInj_zero : BigFieldInj (L := L) (K := K) 0 := by bigfield_tac
theorem bigFieldInj_one : BigFieldInj (L := L) (K := K) 1 := by bigfield_tac
theorem bigFieldInj_two : BigFieldInj (L := L) (K := K) 2 := by bigfield_tac
theorem bigFieldInj_three : BigFieldInj (L := L) (K := K) 3 := by bigfield_tac
theorem bigFieldInj_four : BigFieldInj (L := L) (K := K) 4 := by bigfield_tac
theorem bigFieldInj_five : BigFieldInj (L := L) (K := K) 5 := by bigfield_tac
theorem bigFieldInj_six : BigFieldInj (L := L) (K := K) 6 := by bigfield_tac
theorem bigFieldInj_seven : BigFieldInj (L := L) (K := K) 7 := by bigfield_tac
theorem bigFieldInj_eight : BigFieldInj (L := L) (K := K) 8 := by bigfield_tac
theorem bigFieldInj_nine : BigFieldInj (L := L) (K := K) 9 := by bigfield_tac
theorem bigFieldInj_ten : BigFieldInj (L := L) (K := K) 10 := by bigfield_tac

/-- Two normal forms with the same `O(1)` fields and the same live field are equal. -/
theorem normalize_eq_of_bigField_eq (a a' : AgentState L K)
    (hin : a.input = a'.input) (hout : a.output = a'.output) (hph : a.phase = a'.phase)
    (hrole : a.role = a'.role) (hasg : a.assigned = a'.assigned)
    (hsb : a.smallBias = a'.smallBias) (hfull : a.full = a'.full)
    (hop : a.opinions = a'.opinions) (hbig : bigField a = bigField a') :
    normalize a = normalize a' := by
  have hp := a.phase.2
  rcases hpv : a.phase.val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  · exact bigFieldInj_zero a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_one a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_two a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_three a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_four a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_five a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_six a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_seven a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_eight a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_nine a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · exact bigFieldInj_ten a a' hpv hin hout hph hrole hasg hsb hfull hop hbig
  · omega

theorem encodeCompact_injective : Function.Injective (encodeCompact (L := L) (K := K)) := by
  intro x y hxy
  simp only [encodeCompact, Prod.mk.injEq] at hxy
  obtain ⟨⟨hin, hout, hph, hrole, hasg, hsb, hfull, hop⟩, hbig⟩ := hxy
  apply Subtype.ext
  rw [← x.2, ← y.2]
  exact normalize_eq_of_bigField_eq _ _ hin hout hph hrole hasg hsb hfull hop hbig

lemma card_bias (L : ℕ) : Fintype.card (Bias L) = 2 * (L + 1) + 1 := by
  rw [Fintype.card_congr
    ({ toFun := Bias.toOption, invFun := Bias.ofOption,
       left_inv := Bias.ofOption_toOption, right_inv := Bias.toOption_ofOption } :
      Bias L ≃ Option (Sign × Fin (L + 1))), Fintype.card_option, Fintype.card_prod,
    Fintype.card_fin, show Fintype.card Sign = 2 from rfl]

lemma card_constFields : Fintype.card ConstFields = 73920 := by
  simp only [ConstFields, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  have h1 : Fintype.card Opinion = 2 := rfl
  have h2 : Fintype.card Output = 3 := rfl
  have h3 : Fintype.card Role = 5 := rfl
  rw [h1, h2, h3]

lemma card_bigField (L K : ℕ) : Fintype.card (BigField L K) = (K + 53) * (L + 1) + 4 := by
  simp only [BigField, Fintype.card_option, Fintype.card_sum, Fintype.card_fin, card_bias]
  ring

/-- **State count** (Doty et al. Theorem 3.1, `O(log n)` states): the compact state type has
at most `73920 ((K + 53)(L + 1) + 4)` elements. -/
theorem card_compactState_le (L K : ℕ) :
    Fintype.card (CompactState L K) ≤ 73920 * ((K + 53) * (L + 1) + 4) := by
  have h := Fintype.card_le_of_injective _ (encodeCompact_injective (L := L) (K := K))
  rwa [Fintype.card_prod, card_constFields, card_bigField] at h

/-- At the paper's parameters `L = ⌈log₂ n⌉`, `K = 45`: at most `73920 (98 ⌈log₂ n⌉ + 102)`
states, i.e. `O(log n)`. -/
theorem compact_state_count_clog (n : ℕ) :
    Fintype.card (CompactState (Nat.clog 2 n) 45) ≤ 73920 * (98 * Nat.clog 2 n + 102) := by
  have h := card_compactState_le (Nat.clog 2 n) 45
  have : (45 + 53) * (Nat.clog 2 n + 1) + 4 = 98 * Nat.clog 2 n + 102 := by ring
  rwa [this] at h

#print axioms card_compactState_le
#print axioms compact_state_count_clog

end Compact

end Ripple.PopulationProtocol.ExactMajority
