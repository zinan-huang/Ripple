/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# One-step bounds for the potentials of P3 Lemma 11

For the tree phase of P_EM (`TreeStepHyp`):

* `tick_mass_le`: the tick pairs have scheduler mass at most `2 / (n (n-1))` (P3 Lemma 4: the
  holders of the median and of rank `n-1` are unique);
* `expV_step` (timer potential `2^tExp`): `E[2^tExp(next)] ≤ (1 + 2/(n(n-1))) 2^tExp`;
* `ecV_step` (errorcount potential `Σ_{Unsettled} 2 · 2^{-ec}`, all agents computing):
  `E[V(next)] ≤ (1 + 2/n) V`;
* `phi_drift` (B41, P2 Lemma 6.1): with all agents computing and some Unsettled agent,
  `E[Φ(next)] + 1 ≤ Φ` for `Φ = n (n-1) · phiT`.
-/

import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingStep
import Ripple.PopulationProtocol.SSEM.UpperBound.TreeRankingTools

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped BigOperators ENNReal

variable {n : ℕ}

section Pot

variable {trank Rmax Emax Dmax : ℕ} {hn : 0 < n}

theorem step_self {P : Protocol (AgentState n) Opinion Output}
    (C : Config (AgentState n) Opinion n) (u : Fin n) : C.step P u u = C := by
  unfold Config.step; simp

/-- Sum of `uniformPair` over a set of off-diagonal pairs given by a predicate. -/
theorem sum_uniformPair_ite_le (hn2 : 2 ≤ n) (Q : Fin n × Fin n → Prop) [DecidablePred Q]
    (m : ℕ) (hcard : (Finset.univ.filter Q).card ≤ m) (hoff : ∀ p, Q p → p.1 ≠ p.2) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if Q p then 1 else 0) ≤
      (m : ℝ≥0∞) * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  have e : ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if Q p then 1 else 0) =
      pairSetMass n hn2 (Finset.univ.filter Q) := by
    unfold pairSetMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp
  rw [e, pairSetMass_eq_card_mul_inv_of_subset]
  · gcongr
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact (mem_offDiagonalPairs n p).mpr (hoff p hp.2)

/-- **The tick pairs have mass `≤ 2 / (n (n-1))`.** -/
theorem tick_mass_le (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (C : Config (AgentState n) Opinion n)
    (hT : TreeCore (kC C)) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if TickPair C p.1 p.2 then 1 else 0) ≤
      2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  have hcn : ceilHalf n < n := by unfold ceilHalf; omega
  refine (sum_uniformPair_ite_le hn2 (fun p => TickPair C p.1 p.2) 2 ?_ ?_).trans (by norm_num)
  · by_cases hex : ∃ a b, MedAt (C a).1 ∧ (C b).1.role = .Settled ∧ (C b).1.rank.val + 1 = n
    · obtain ⟨a, b, ha, hb1, hb2⟩ := hex
      have hsub : Finset.univ.filter (fun p : Fin n × Fin n => TickPair C p.1 p.2) ⊆
          {(a, b), (b, a)} := by
        intro p hp
        rw [Finset.mem_filter] at hp
        have hmed : ∀ x, MedAt (C x).1 → x = a := fun x hx =>
          hT.inj x a hx.1 ha.1 (Fin.ext (by have := hx.2; have := ha.2; simp only [kC]; omega))
        have hlst : ∀ x, (C x).1.role = .Settled → (C x).1.rank.val + 1 = n → x = b :=
          fun x hx1 hx2 => hT.inj x b hx1 hb1 (Fin.ext (by simp only [kC]; omega))
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hp.2 with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · left; rw [Prod.ext_iff]; exact ⟨hmed _ h1, hlst _ h2 h3⟩
        · right; rw [Prod.ext_iff]; exact ⟨hlst _ h2 h3, hmed _ h1⟩
      exact (Finset.card_le_card hsub).trans Finset.card_le_two
    · have : Finset.univ.filter (fun p : Fin n × Fin n => TickPair C p.1 p.2) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro p - (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · exact hex ⟨p.1, p.2, h1, h2, h3⟩
        · exact hex ⟨p.2, p.1, h1, h2, h3⟩
      rw [this]; simp
  · rintro ⟨u, v⟩ hp huv
    simp only at hp huv
    subst huv
    rcases hp with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩ <;> have := h1.2 <;> omega

/-- **Timer potential.** `V(C) = 2^tExp(C) · c` on the configurations where `Ok` holds. -/
theorem expV_step (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hT0 : 2 ≤ 7 * (trank + 4))
    (Ok : Config (AgentState n) Opinion n → Prop) [DecidablePred Ok] (c : ℝ≥0∞)
    (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) (hOk : Ok C)
    (hOk' : ∀ u v, u ≠ v →
      Ok (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v)) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        (fun C' : Config (AgentState n) Opinion n =>
          if Ok C' then 2 ^ tExp (7 * (trank + 4)) C' * c else 1)
        (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ≤
      (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) *
        (if Ok C then 2 ^ tExp (7 * (trank + 4)) C * c else 1) := by
  classical
  rw [if_pos hOk]
  set V := (2 : ℝ≥0∞) ^ tExp (7 * (trank + 4)) C * c
  have hpt : ∀ p : Fin n × Fin n,
      (if Ok (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) then
        2 ^ tExp (7 * (trank + 4))
          (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) * c
        else 1) ≤ V + V * (if TickPair C p.1 p.2 then 1 else 0) := by
    rintro ⟨u, v⟩
    by_cases huv : u = v
    · subst huv; rw [step_self, if_pos hOk]; exact le_self_add
    · rw [if_pos (hOk' u v huv)]
      have hle := tExp_step_le (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn) C h huv
        hT0 hn3
      simp only at hle ⊢
      split_ifs at hle ⊢ with htp
      · calc (2 : ℝ≥0∞) ^ tExp (7 * (trank + 4))
              (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) * c
            ≤ 2 ^ (tExp (7 * (trank + 4)) C + 1) * c :=
              mul_le_mul_right' (pow_le_pow_right₀ (by norm_num) hle) _
          _ = V + V * 1 := by simp only [V, pow_succ]; ring
      · calc (2 : ℝ≥0∞) ^ tExp (7 * (trank + 4))
              (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v) * c
            ≤ 2 ^ (tExp (7 * (trank + 4)) C + 0) * c :=
              mul_le_mul_right' (pow_le_pow_right₀ (by norm_num) hle) _
          _ = V + V * 0 := by simp [V]
  calc ∑ p : Fin n × Fin n, uniformPair n hn2 p * _
      ≤ ∑ p : Fin n × Fin n, uniformPair n hn2 p * (V + V * (if TickPair C p.1 p.2 then 1 else 0)) :=
        Finset.sum_le_sum fun p _ => mul_le_mul_left' (hpt p) _
    _ = V + V * ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if TickPair C p.1 p.2 then 1 else 0)
        := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, uniformPair_sum_one hn2,
          one_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro p _
        ring
    _ ≤ V + V * (2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) :=
        add_le_add le_rfl (mul_le_mul_left' (tick_mass_le hn2 hn3 C h.core) _)
    _ = (1 + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) * V := by ring

/-- The errorcount potential `Σ_{Unsettled} a · 2^{-ec}`. -/
noncomputable def ecV (a : ℝ≥0∞) (C : Config (AgentState n) Opinion n) : ℝ≥0∞ :=
  ∑ w, if (C w).1.role = .Unsettled then a * 2⁻¹ ^ (C w).1.errorcount else 0

theorem two_inv_pow_le {m m' : ℕ} (h : m ≤ m' + 1) :
    (2⁻¹ : ℝ≥0∞) ^ m' ≤ 2 * 2⁻¹ ^ m := by
  have e : (2⁻¹ : ℝ≥0∞) ^ m' = 2 * 2⁻¹ ^ (m' + 1) := by
    rw [pow_succ, ← mul_assoc, mul_comm 2, mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), mul_one]
  rw [e]
  exact mul_le_mul_left' (pow_le_pow_right_of_le_one' (by norm_num) h) _

/-- **Errorcount potential** (all agents computing): `E[V(next)] ≤ (1 + 2/n) V`. -/
theorem ecV_step (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hT0 : 2 ≤ 7 * (trank + 4)) (a : ℝ≥0∞)
    (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) (hc : AllCompK (kC C)) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        ecV a (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ≤
      (1 + 2 * (n : ℝ≥0∞)⁻¹) * ecV a C := by
  classical
  set t : Fin n → ℝ≥0∞ := fun w =>
    if (C w).1.role = .Unsettled then a * 2⁻¹ ^ (C w).1.errorcount else 0
  have hpt : ∀ p : Fin n × Fin n,
      ecV a (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) ≤
        ecV a C + (t p.1 + t p.2) := by
    rintro ⟨u, v⟩
    by_cases huv : u = v
    · subst huv; rw [step_self]; exact le_self_add
    · set C' := C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
        with hC'
      have hw : ∀ w, (if (C' w).1.role = .Unsettled then a * 2⁻¹ ^ (C' w).1.errorcount else 0)
          ≤ t w + (if w = u then t w else 0) + (if w = v then t w else 0) := by
        intro w
        by_cases hU : (C' w).1.role = .Unsettled
        · rw [if_pos hU]
          rcases tree_step_nonSettled (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
            C h huv hT0 hn3 w (by rw [hU]; decide) with ⟨hwu, hwv, e⟩ | ⟨hwp, hs⟩
          · have hU0 : (C w).1.role = .Unsettled := by rw [← e]; exact hU
            rw [if_neg hwu, if_neg hwv, add_zero, add_zero]
            have e' : C' w = C w := e
            simp only [t, if_pos hU0]
            rw [e']
          · rcases hs.unsettled hU with ⟨hU0, hle⟩ | ⟨hR, -⟩
            · have key : a * 2⁻¹ ^ (C' w).1.errorcount ≤ t w + t w := by
                simp only [t, if_pos hU0]
                calc a * 2⁻¹ ^ (C' w).1.errorcount
                    ≤ a * (2 * 2⁻¹ ^ (C w).1.errorcount) :=
                      mul_le_mul_left' (two_inv_pow_le hle) a
                  _ = _ := by ring
              rcases hwp with hwp | hwp
              · rw [if_pos hwp, if_neg (by rw [hwp]; exact huv), add_zero]; exact key
              · rw [if_neg (by rw [hwp]; exact Ne.symm huv), if_pos hwp, add_zero]; exact key
            · exact absurd hR (hc w)
        · rw [if_neg hU]; exact zero_le
      calc ecV a C'
          ≤ ∑ w, (t w + (if w = u then t w else 0) + (if w = v then t w else 0)) :=
            Finset.sum_le_sum fun w _ => hw w
        _ = ecV a C + (t u + t v) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
              Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
            simp only [ecV, t]
            ring
  calc ∑ p : Fin n × Fin n, uniformPair n hn2 p * _
      ≤ ∑ p : Fin n × Fin n, uniformPair n hn2 p * (ecV a C + (t p.1 + t p.2)) :=
        Finset.sum_le_sum fun p _ => mul_le_mul_left' (hpt p) _
    _ = ecV a C + 2 * (n : ℝ≥0∞)⁻¹ * ∑ w, t w := by
        rw [← uniformPair_sum_endpoints hn2 t]
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, uniformPair_sum_one hn2,
          one_mul]
    _ = (1 + 2 * (n : ℝ≥0∞)⁻¹) * ecV a C := by
        simp only [ecV, t]; ring

/-- The tree-ranking potential in interactions: `n (n-1) · phiT`. -/
noncomputable def phiE (C : Config (AgentState n) Opinion n) : ℝ≥0∞ :=
  ENNReal.ofReal (((n * (n - 1) : ℕ) : ℝ) * phiT (kC C))

/-- **B41 drift** (P2 Lemma 6.1 with Lemma 1.4 in drift form): with all agents computing and an
Unsettled agent present, `E[Φ(next)] + 1 ≤ Φ`. -/
theorem phi_drift (hn2 : 2 ≤ n) (hn3 : 3 ≤ n) (hT0 : 2 ≤ 7 * (trank + 4))
    (C : Config (AgentState n) Opinion n) (h : TreeStepHyp C) (hc : AllCompK (kC C))
    (hU : ∃ w, (C w).1.role = .Unsettled) :
    ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        phiE (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) + 1 ≤
      phiE C := by
  classical
  set k := kC C with hk
  set N : ℕ := n * (n - 1) with hN
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  -- rank 0 is assigned
  have h0 : Asg k 0 := by
    rcases h.core.hasRoot with h0 | ⟨v, hv, -⟩
    · exact h0
    · exact absurd hv (hc v)
  -- the least incomplete level
  have hex : ∃ d, 0 < unasg k d := by
    obtain ⟨w, hw⟩ := hU
    have h1 : 0 < (unsAg k).card :=
      Finset.card_pos.mpr ⟨w, by simp [unsAg, k, kC, hw]⟩
    rw [card_unsAg h.core hc] at h1
    obtain ⟨r, hr⟩ := Finset.card_pos.mp h1
    simp only [unasgAll, Finset.mem_filter, Finset.mem_range] at hr
    refine ⟨Nat.log 2 (r + 1), Finset.card_pos.mpr ⟨r, ?_⟩⟩
    exact mem_unasgSet.mpr ⟨hr.1, inLevel_log r, hr.2⟩
  set d₀ := Nat.find hex with hd₀
  have hpos : 0 < unasg k d₀ := Nat.find_spec hex
  have hmin : ∀ d', d' < d₀ → unasg k d' = 0 := fun d' hd' =>
    Nat.eq_zero_of_not_pos (Nat.find_min hex hd')
  have htop : d₀ ≤ topL n := by
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
    rw [mem_unasgSet] at hr
    exact inLevel_le_topL hr.1 hr.2.1
  set i := unasg k d₀ with hi
  have hrec := card_unasg_le_rec h.core h0 hmin
  have huns := card_uns_ge h.core hc htop
  set D : ℝ≥0∞ := ENNReal.ofReal ((N : ℝ) / ((i : ℝ) ^ 2 * uL n d₀)) with hD
  set Gd : Finset (Fin n × Fin n) := Rec k d₀ ×ˢ unsAg k ∪ unsAg k ×ˢ Rec k d₀ with hGd
  have hu1 := one_le_uL n d₀
  -- monotonicity and the drop
  have hmono : ∀ p : Fin n × Fin n,
      phiE (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) +
        (if p ∈ Gd then D else 0) ≤ phiE C := by
    rintro ⟨u, v⟩
    by_cases huv : u = v
    · subst huv
      have : (u, u) ∉ Gd := by
        simp only [Gd, Finset.mem_union, Finset.mem_product, mem_Rec, unsAg,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rintro (⟨⟨h1, -⟩, h2⟩ | ⟨h2, ⟨h1, -⟩⟩) <;> rw [h1] at h2 <;> exact absurd h2 (by decide)
      rw [step_self, if_neg this, add_zero]
    · obtain ⟨-, hm, hA, -⟩ := tree_step_core (trank := trank) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (hn := hn) C h huv hT0 hn3
      set C' := C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) u v
      by_cases hp : (u, v) ∈ Gd
      · rw [if_pos hp]
        -- the recruiter and its target
        have hrt : ∃ x, (x = u ∨ x = v) ∧ x ∈ Rec k d₀ ∧ Asg (kC C') (recTarget k x) := by
          simp only [Gd, Finset.mem_union, Finset.mem_product] at hp
          rcases hp with ⟨hx, hy⟩ | ⟨hy, hx⟩
          · have hx' := mem_Rec.mp hx
            have hy' : (k v).role = .Unsettled := by simpa [unsAg] using hy
            refine ⟨u, Or.inl rfl, hx, (hA _).mpr ?_⟩
            have := kstep_recruit_asg (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              huv (Or.inl ⟨hx'.1, hy', hx'.2.1, hx'.2.2.1⟩)
            rwa [if_pos hx'.1] at this
          · have hx' := mem_Rec.mp hx
            have hy' : (k u).role = .Unsettled := by simpa [unsAg] using hy
            refine ⟨v, Or.inr rfl, hx, (hA _).mpr ?_⟩
            have := kstep_recruit_asg (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
              huv (Or.inr ⟨hx'.1, hy', hx'.2.1, hx'.2.2.1⟩)
            rwa [if_neg (by rw [hy']; decide)] at this
        obtain ⟨x, -, hx, hxA⟩ := hrt
        obtain ⟨-, -, hlt, hlv, hna⟩ := mem_Rec.mp hx
        have hdrop := phiT_drop hm hlt hlv hna hxA
        show ENNReal.ofReal ((N : ℝ) * phiT (kC C')) + D ≤ ENNReal.ofReal ((N : ℝ) * phiT (kC C))
        have hq1 : 0 ≤ (N : ℝ) * phiT (kC C') :=
          mul_nonneg (Nat.cast_nonneg _) (phiT_nonneg _)
        have hq2 : 0 ≤ (N : ℝ) / ((i : ℝ) ^ 2 * uL n d₀) :=
          div_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _) (by linarith))
        rw [hD, ← ENNReal.ofReal_add hq1 hq2]
        apply ENNReal.ofReal_le_ofReal
        have : (N : ℝ) * phiT (kC C') + N / ((i : ℝ) ^ 2 * uL n d₀) =
            N * (phiT (kC C') + 1 / ((i : ℝ) ^ 2 * uL n d₀)) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hdrop hNpos.le
      · rw [if_neg hp, add_zero]
        unfold phiE
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (phiT_mono hm) hNpos.le
  -- the mass of the good pairs
  have hGoff : Gd ⊆ OffDiagonalPairs n := by
    intro p hp
    rw [mem_offDiagonalPairs]
    simp only [Gd, Finset.mem_union, Finset.mem_product, mem_Rec, unsAg,
      Finset.mem_filter, Finset.mem_univ, true_and] at hp
    intro e
    rcases hp with ⟨⟨h1, -⟩, h2⟩ | ⟨h2, ⟨h1, -⟩⟩
    · rw [e] at h1; rw [h1] at h2; exact absurd h2 (by decide)
    · rw [← e] at h1; rw [h1] at h2; exact absurd h2 (by decide)
  have hGcard : Gd.card = 2 * (Rec k d₀).card * (unsAg k).card := by
    rw [hGd, Finset.card_union_of_disjoint, Finset.card_product, Finset.card_product]
    · ring
    · rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_product, mem_Rec, unsAg, Finset.mem_filter, Finset.mem_univ,
        true_and] at h1 h2
      rw [h1.1.1] at h2
      exact absurd h2.1 (by decide)
  have hone : 1 ≤ ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if p ∈ Gd then D else 0) := by
    have e : ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if p ∈ Gd then D else 0) =
        pairSetMass n hn2 Gd * D := by
      unfold pairSetMass
      rw [Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Gd)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun p => p ∉ Gd)) (fun p hp => by
        rw [Finset.mem_filter] at hp; rw [if_neg hp.2, mul_zero]), add_zero]
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      apply Finset.sum_congr rfl
      intro p hp
      rw [if_pos hp]
    rw [e, pairSetMass_eq_card_mul_inv_of_subset n hn2 Gd hGoff, hGcard]
    have hreal : (1 : ℝ) ≤ ((2 * (Rec k d₀).card * (unsAg k).card : ℕ) : ℝ) * (1 / (N : ℝ)) *
        ((N : ℝ) / ((i : ℝ) ^ 2 * uL n d₀)) := by
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hpos
      have hrec' : (i : ℝ) ≤ 2 * (Rec k d₀).card := by exact_mod_cast hrec
      have e2 : ((2 * (Rec k d₀).card * (unsAg k).card : ℕ) : ℝ) * (1 / (N : ℝ)) *
          ((N : ℝ) / ((i : ℝ) ^ 2 * uL n d₀)) =
          (2 * (Rec k d₀).card * (unsAg k).card : ℝ) / ((i : ℝ) ^ 2 * uL n d₀) := by
        have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
        have hden : (i : ℝ) ^ 2 * uL n d₀ ≠ 0 :=
          (mul_pos (pow_pos (by linarith) 2) (by linarith)).ne'
        push_cast; field_simp
      rw [e2, le_div_iff₀ (mul_pos (pow_pos (by linarith) 2) (by linarith))]
      have hU0 : (0 : ℝ) ≤ (unsAg k).card := by positivity
      nlinarith
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (((2 * (Rec k d₀).card * (unsAg k).card : ℕ) : ℝ) * (1 / (N : ℝ)) *
          ((N : ℝ) / ((i : ℝ) ^ 2 * uL n d₀))) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, one_div, ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  calc ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        phiE (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) + 1
      ≤ ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        phiE (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) +
        ∑ p : Fin n × Fin n, uniformPair n hn2 p * (if p ∈ Gd then D else 0) :=
        add_le_add le_rfl hone
    _ = ∑ p : Fin n × Fin n, uniformPair n hn2 p *
        (phiE (C.step (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) p.1 p.2) +
          (if p ∈ Gd then D else 0)) := by
        rw [← Finset.sum_add_distrib]
        simp only [mul_add]
    _ ≤ ∑ p : Fin n × Fin n, uniformPair n hn2 p * phiE C :=
        Finset.sum_le_sum fun p _ => mul_le_mul_left' (hmono p) _
    _ = phiE C := by rw [← Finset.sum_mul, uniformPair_sum_one hn2, one_mul]

end Pot

end Ripple.PopulationProtocol.SSEM
