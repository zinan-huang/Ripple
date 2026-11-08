/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-7 exact-band transition facts

The cumulative cleared prefix is the guard that makes an exact band
non-increasing.  A gap-1 or gap-2 update can enter stage j only by copying its
sign from an exponent strictly below j.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandDefs

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase7BandTransition

open Phase7BandDefs
open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

def bandSt (σ : Sign) (j : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.dyadic σ j

instance (σ : Sign) (j : Fin (L + 1)) (a : AgentState L K) :
    Decidable (bandSt (L := L) (K := K) σ j a) := by
  unfold bandSt
  infer_instance

theorem bandCountN_eq_countP (σ : Sign) (j : Fin (L + 1))
    (c : Config (AgentState L K)) :
    bandCountN (L := L) (K := K) σ j c =
      Multiset.countP (bandSt (L := L) (K := K) σ j) c := by
  classical
  change (∑ a ∈ Finset.univ.filter (bandSt (L := L) (K := K) σ j), c.count a) = _
  calc
    (∑ a ∈ Finset.univ.filter (bandSt (L := L) (K := K) σ j), c.count a)
        = ∑ a : AgentState L K,
            if bandSt (L := L) (K := K) σ j a then c.count a else 0 :=
          Finset.sum_filter _ _
    _ = ∑ a : AgentState L K,
          (c.filter (bandSt (L := L) (K := K) σ j)).count a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Multiset.count_filter]
        rfl
    _ = (c.filter (bandSt (L := L) (K := K) σ j)).card :=
      Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP (bandSt (L := L) (K := K) σ j) c :=
      (Multiset.countP_eq_card_filter _ _).symm

private theorem countP_bandSt_pair (σ : Sign) (j : Fin (L + 1))
    (x y : AgentState L K) :
    Multiset.countP (bandSt (L := L) (K := K) σ j)
        ({x, y} : Multiset (AgentState L K)) =
      (if bandSt (L := L) (K := K) σ j x then 1 else 0) +
        (if bandSt (L := L) (K := K) σ j y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

private theorem not_bandSt_update_dyadic_of_sign_ne (σ ss : Sign)
    (j k : Fin (L + 1)) (a : AgentState L K) (hss : ss ≠ σ) :
    ¬ bandSt (L := L) (K := K) σ j
      ({a with bias := Bias.dyadic ss k} : AgentState L K) := by
  rintro ⟨_, hb⟩
  have hs : ss = σ := by injection hb
  exact hss hs

private theorem not_bandSt_update_dyadic_of_index_gt (σ ss : Sign)
    (j k : Fin (L + 1)) (a : AgentState L K) (hjk : j.val < k.val) :
    ¬ bandSt (L := L) (K := K) σ j
      ({a with bias := Bias.dyadic ss k} : AgentState L K) := by
  rintro ⟨_, hb⟩
  have hk : k = j := by injection hb
  have hv := congrArg Fin.val hk
  omega

/-- Exact-band non-increase for two Main agents transformed by cancelSplit,
assuming neither input carries sign σ below j. -/
private theorem cancelSplit_band_pair_le_of_clearBelow (σ : Sign)
    (j : Fin (L + 1)) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsBelow : ∀ k : Fin (L + 1), s.bias = Bias.dyadic σ k → j.val ≤ k.val)
    (htBelow : ∀ k : Fin (L + 1), t.bias = Bias.dyadic σ k → j.val ≤ k.val) :
    Multiset.countP (bandSt (L := L) (K := K) σ j)
        ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} :
          Multiset (AgentState L K)) ≤
      Multiset.countP (bandSt (L := L) (K := K) σ j)
        ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_bandSt_pair, countP_bandSt_pair]
  cases hsb : s.bias with
  | zero =>
      have hcs : cancelSplit L K s t = (s, t) := by
        unfold cancelSplit
        rw [hsb]
      rw [hcs]
  | dyadic ss i =>
    cases htb : t.bias with
    | zero =>
        have hcs : cancelSplit L K s t = (s, t) := by
          unfold cancelSplit
          rw [hsb, htb]
        rw [hcs]
    | dyadic tt k =>
      have hsBound : ss = σ → j.val ≤ i.val := by
        intro h
        exact hsBelow i (by rw [hsb, h])
      have htBound : tt = σ → j.val ≤ k.val := by
        intro h
        exact htBelow k (by rw [htb, h])
      by_cases hsgn : ss ≠ tt
      · by_cases h0 : i.val = k.val
        · have hcs : cancelSplit L K s t =
              ({s with bias := .zero}, {t with bias := .zero}) := by
            unfold cancelSplit
            rw [hsb, htb]
            simp only [if_pos hsgn, dif_pos h0]
          rw [hcs]
          simp [bandSt, hsM, htM, hsb, htb]
        · by_cases h1 : i.val + 1 = k.val
          · have hcs : cancelSplit L K s t =
                ({s with bias := .dyadic ss ⟨i.val + 1, by
                    have hk := k.2
                    omega⟩}, {t with bias := .zero}) := by
              unfold cancelSplit
              rw [hsb, htb]
              simp only [if_pos hsgn, dif_neg h0, dif_pos h1]
            rw [hcs]
            rcases ss with _ | _ <;> rcases tt with _ | _ <;> rcases σ with _ | _ <;>
              simp_all [bandSt] <;> split_ifs <;> simp_all <;> omega
          · by_cases h1' : k.val + 1 = i.val
            · have hcs : cancelSplit L K s t =
                  ({s with bias := .zero}, {t with bias := .dyadic tt ⟨k.val + 1, by
                      have hi := i.2
                      omega⟩}) := by
                unfold cancelSplit
                rw [hsb, htb]
                simp only [if_pos hsgn, dif_neg h0, dif_neg h1, dif_pos h1']
              rw [hcs]
              rcases ss with _ | _ <;> rcases tt with _ | _ <;> rcases σ with _ | _ <;>
                simp_all [bandSt] <;> split_ifs <;> simp_all <;> omega
            · by_cases h2 : i.val + 2 = k.val
              · have hcs : cancelSplit L K s t =
                    ({s with bias := .dyadic ss ⟨i.val + 1, by
                        have hk := k.2
                        omega⟩},
                     {t with bias := .dyadic ss ⟨i.val + 2, by
                        have hk := k.2
                        omega⟩}) := by
                  unfold cancelSplit
                  rw [hsb, htb]
                  simp only [if_pos hsgn, dif_neg h0, dif_neg h1, dif_neg h1',
                    dif_pos h2]
                rw [hcs]
                by_cases hssσ : ss = σ
                · have hbound : j.val ≤ i.val := hsBound hssσ
                  have ho1 : ¬ bandSt (L := L) (K := K) σ j
                      ({s with bias := .dyadic ss ⟨i.val + 1, by
                        have hk := k.2
                        omega⟩} : AgentState L K) :=
                    not_bandSt_update_dyadic_of_index_gt σ ss j _ s (by simp; omega)
                  have ho2 : ¬ bandSt (L := L) (K := K) σ j
                      ({t with bias := .dyadic ss ⟨i.val + 2, by
                        have hk := k.2
                        omega⟩} : AgentState L K) :=
                    not_bandSt_update_dyadic_of_index_gt σ ss j _ t (by simp; omega)
                  rw [if_neg ho1, if_neg ho2]
                  omega
                · have ho1 : ¬ bandSt (L := L) (K := K) σ j
                      ({s with bias := .dyadic ss ⟨i.val + 1, by
                        have hk := k.2
                        omega⟩} : AgentState L K) :=
                    not_bandSt_update_dyadic_of_sign_ne σ ss j _ s hssσ
                  have ho2 : ¬ bandSt (L := L) (K := K) σ j
                      ({t with bias := .dyadic ss ⟨i.val + 2, by
                        have hk := k.2
                        omega⟩} : AgentState L K) :=
                    not_bandSt_update_dyadic_of_sign_ne σ ss j _ t hssσ
                  rw [if_neg ho1, if_neg ho2]
                  omega
              · by_cases h2' : k.val + 2 = i.val
                · have hcs : cancelSplit L K s t =
                      ({s with bias := .dyadic tt ⟨k.val + 2, by
                          have hi := i.2
                          omega⟩},
                       {t with bias := .dyadic tt ⟨k.val + 1, by
                          have hi := i.2
                          omega⟩}) := by
                    unfold cancelSplit
                    rw [hsb, htb]
                    simp only [if_pos hsgn, dif_neg h0, dif_neg h1, dif_neg h1',
                      dif_neg h2, dif_pos h2']
                  rw [hcs]
                  by_cases httσ : tt = σ
                  · have hbound : j.val ≤ k.val := htBound httσ
                    have ho1 : ¬ bandSt (L := L) (K := K) σ j
                        ({s with bias := .dyadic tt ⟨k.val + 2, by
                          have hi := i.2
                          omega⟩} : AgentState L K) :=
                      not_bandSt_update_dyadic_of_index_gt σ tt j _ s (by simp; omega)
                    have ho2 : ¬ bandSt (L := L) (K := K) σ j
                        ({t with bias := .dyadic tt ⟨k.val + 1, by
                          have hi := i.2
                          omega⟩} : AgentState L K) :=
                      not_bandSt_update_dyadic_of_index_gt σ tt j _ t (by simp; omega)
                    rw [if_neg ho1, if_neg ho2]
                    omega
                  · have ho1 : ¬ bandSt (L := L) (K := K) σ j
                        ({s with bias := .dyadic tt ⟨k.val + 2, by
                          have hi := i.2
                          omega⟩} : AgentState L K) :=
                      not_bandSt_update_dyadic_of_sign_ne σ tt j _ s httσ
                    have ho2 : ¬ bandSt (L := L) (K := K) σ j
                        ({t with bias := .dyadic tt ⟨k.val + 1, by
                          have hi := i.2
                          omega⟩} : AgentState L K) :=
                      not_bandSt_update_dyadic_of_sign_ne σ tt j _ t httσ
                    rw [if_neg ho1, if_neg ho2]
                    omega
                · have hcs : cancelSplit L K s t = (s, t) := by
                    unfold cancelSplit
                    rw [hsb, htb]
                    simp only [if_pos hsgn, dif_neg h0, dif_neg h1, dif_neg h1',
                      dif_neg h2, dif_neg h2']
                  rw [hcs]
      · have hcs : cancelSplit L K s t = (s, t) := by
          unfold cancelSplit
          rw [hsb, htb]
          simp only [if_neg hsgn]
        rw [hcs]

/-- A mixed-role phase-7 interaction preserves each Main input exactly; a
non-Main input and output are outside every minority band. -/
private theorem Transition_band_pair_le_of_not_both_main (σ : Sign)
    (j : Fin (L + 1)) (s t : AgentState L K)
    (hs7 : s.phase.val = 7) (ht7 : t.phase.val = 7)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Multiset.countP (bandSt (L := L) (K := K) σ j)
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) ≤
      Multiset.countP (bandSt (L := L) (K := K) σ j)
        ({s, t} : Multiset (AgentState L K)) := by
  rw [countP_bandSt_pair, countP_bandSt_pair]
  obtain ⟨hr1, hr2⟩ :=
    PhaseOnlyWindows.Transition_role_phase7 (L := L) (K := K) s t hs7 ht7
  have hmain_fst : s.role = Role.main → (Transition L K s t).1 = s := by
    intro hsM
    have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
      (L := L) (K := K) s t hs7 ht7
    have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
    have hp7 : (Phase7Transition L K s t).1 = s := by
      unfold Phase7Transition
      simp only [if_neg hnb]
      rw [if_neg (show s.role ≠ Role.clock by rw [hsM]; decide)]
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
      (by rw [hp7, hs7]; decide)]
    exact hp7
  have hmain_snd : t.role = Role.main → (Transition L K s t).2 = t := by
    intro htM
    have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
      (L := L) (K := K) s t hs7 ht7
    have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs7
    have hp7 : (Phase7Transition L K s t).2 = t := by
      unfold Phase7Transition
      simp only [if_neg hnb]
      rw [if_neg (show t.role ≠ Role.clock by rw [htM]; decide)]
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
      (by rw [hp7, ht7]; decide)]
    exact hp7
  have side1 :
      (if bandSt (L := L) (K := K) σ j (Transition L K s t).1 then 1 else 0) ≤
        (if bandSt (L := L) (K := K) σ j s then 1 else 0) := by
    by_cases hsM : s.role = Role.main
    · rw [hmain_fst hsM]
    · have hout : ¬ bandSt (L := L) (K := K) σ j (Transition L K s t).1 := by
        intro h
        exact hsM (hr1 ▸ h.1)
      simp [hout]
  have side2 :
      (if bandSt (L := L) (K := K) σ j (Transition L K s t).2 then 1 else 0) ≤
        (if bandSt (L := L) (K := K) σ j t then 1 else 0) := by
    by_cases htM : t.role = Role.main
    · rw [hmain_snd htM]
    · have hout : ¬ bandSt (L := L) (K := K) σ j (Transition L K s t).2 := by
        intro h
        exact htM (hr2 ▸ h.1)
      simp [hout]
  omega

/-- The exact current band is non-increasing under every scheduled phase-7
step once the cumulative prefix below it is clear. -/
theorem bandCountN_stepOrSelf_le (σ : Sign) (j : Fin (L + 1)) (n : ℕ)
    (c : Config (AgentState L K))
    (hhonest : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c)
    (hclear : BandClear (L := L) (K := K) σ j.val c)
    (r₁ r₂ : AgentState L K) :
    bandCountN (L := L) (K := K) σ j
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤
      bandCountN (L := L) (K := K) σ j c := by
  classical
  obtain ⟨_, hphase⟩ := hhonest
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 : r₁ ∈ c :=
      Multiset.mem_of_le
        (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
    have hm2 : r₂ ∈ c :=
      Multiset.mem_of_le
        (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
    have h17 : r₁.phase.val = 7 := hphase r₁ hm1
    have h27 : r₂.phase.val = 7 := hphase r₂ hm2
    have hpair :
        Multiset.countP (bandSt (L := L) (K := K) σ j)
            ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} :
              Multiset (AgentState L K)) ≤
          Multiset.countP (bandSt (L := L) (K := K) σ j)
            ({r₁, r₂} : Multiset (AgentState L K)) := by
      by_cases hboth : r₁.role = Role.main ∧ r₂.role = Role.main
      · rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
          r₁ r₂ h17 h27 hboth.1 hboth.2]
        apply cancelSplit_band_pair_le_of_clearBelow σ j r₁ r₂ hboth.1 hboth.2
        · intro k hb
          by_contra hnot
          have hklt : k.val < j.val := by omega
          have hz := hclear k hklt
          rw [bandCountN_eq_countP, Multiset.countP_eq_zero] at hz
          exact hz r₁ hm1 ⟨hboth.1, hb⟩
        · intro k hb
          by_contra hnot
          have hklt : k.val < j.val := by omega
          have hz := hclear k hklt
          rw [bandCountN_eq_countP, Multiset.countP_eq_zero] at hz
          exact hz r₂ hm2 ⟨hboth.2, hb⟩
      · exact Transition_band_pair_le_of_not_both_main σ j r₁ r₂ h17 h27 hboth
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    rw [bandCountN_eq_countP, bandCountN_eq_countP, hc',
      Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le :
        Multiset.countP (bandSt (L := L) (K := K) σ j)
            ({r₁, r₂} : Multiset (AgentState L K)) ≤
          Multiset.countP (bandSt (L := L) (K := K) σ j) c :=
      Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- Every already-cleared lower band remains clear after a scheduled phase-7
step.  Apply current-band monotonicity separately at each lower index. -/
theorem bandClear_stepOrSelf (σ : Sign) (m n : ℕ)
    (c : Config (AgentState L K))
    (hhonest : PhaseOnlyWindows.Phase7Win (L := L) (K := K) n c)
    (hclear : BandClear (L := L) (K := K) σ m c)
    (r₁ r₂ : AgentState L K) :
    BandClear (L := L) (K := K) σ m
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  intro j hjm
  have hprefix : BandClear (L := L) (K := K) σ j.val c := by
    intro k hkj
    exact hclear k (by omega)
  have hle := bandCountN_stepOrSelf_le
    (L := L) (K := K) σ j n c hhonest hprefix r₁ r₂
  have hz := hclear j hjm
  omega

/-- The ordered eliminator/minority pair removes the exact-j minority in every
one of the five cancelSplit distance branches. -/
private theorem cancelSplit_band_pair_drop_left (σ ss : Sign)
    (j k : Fin (L + 1)) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsb : s.bias = Bias.dyadic ss k) (htb : t.bias = Bias.dyadic σ j)
    (hss : ss ≠ σ) (hnear1 : j.val ≤ k.val + 2) (hnear2 : k.val ≤ j.val + 2) :
    Multiset.countP (bandSt (L := L) (K := K) σ j)
          ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} :
            Multiset (AgentState L K)) + 1 ≤
      Multiset.countP (bandSt (L := L) (K := K) σ j)
        ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_bandSt_pair, countP_bandSt_pair]
  by_cases h0 : k.val = j.val
  · have hcs : cancelSplit L K s t =
        ({s with bias := .zero}, {t with bias := .zero}) := by
      unfold cancelSplit
      rw [hsb, htb]
      simp only [if_pos hss, dif_pos h0]
    rw [hcs]
    simp [bandSt, hsM, htM, hsb, htb, hss]
  · by_cases h1 : k.val + 1 = j.val
    · have hcs : cancelSplit L K s t =
          ({s with bias := .dyadic ss ⟨k.val + 1, by
              have hj := j.2
              omega⟩}, {t with bias := .zero}) := by
        unfold cancelSplit
        rw [hsb, htb]
        simp only [if_pos hss, dif_neg h0, dif_pos h1]
      rw [hcs]
      simp [bandSt, hsM, htM, hsb, htb, hss]
    · by_cases h1' : j.val + 1 = k.val
      · have hcs : cancelSplit L K s t =
            ({s with bias := .zero}, {t with bias := .dyadic σ ⟨j.val + 1, by
                have hk := k.2
                omega⟩}) := by
          unfold cancelSplit
          rw [hsb, htb]
          simp only [if_pos hss, dif_neg h0, dif_neg h1, dif_pos h1']
        rw [hcs]
        simp [bandSt, hsM, htM, hsb, htb, hss, Fin.ext_iff]
      · by_cases h2 : k.val + 2 = j.val
        · have hcs : cancelSplit L K s t =
              ({s with bias := .dyadic ss ⟨k.val + 1, by
                  have hj := j.2
                  omega⟩},
               {t with bias := .dyadic ss ⟨k.val + 2, by
                  have hj := j.2
                  omega⟩}) := by
            unfold cancelSplit
            rw [hsb, htb]
            simp only [if_pos hss, dif_neg h0, dif_neg h1, dif_neg h1',
              dif_pos h2]
          rw [hcs]
          simp [bandSt, hsM, htM, hsb, htb, hss]
        · by_cases h2' : j.val + 2 = k.val
          · have hcs : cancelSplit L K s t =
                ({s with bias := .dyadic σ ⟨j.val + 2, by
                    have hk := k.2
                    omega⟩},
                 {t with bias := .dyadic σ ⟨j.val + 1, by
                    have hk := k.2
                    omega⟩}) := by
              unfold cancelSplit
              rw [hsb, htb]
              simp only [if_pos hss, dif_neg h0, dif_neg h1, dif_neg h1',
                dif_neg h2, dif_pos h2']
            rw [hcs]
            simp [bandSt, hsM, htM, hsb, htb, hss, Fin.ext_iff]
          · omega

/-- The reverse ordered minority/eliminator pair has the same exact-j drop. -/
private theorem cancelSplit_band_pair_drop_right (σ ss : Sign)
    (j k : Fin (L + 1)) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsb : s.bias = Bias.dyadic σ j) (htb : t.bias = Bias.dyadic ss k)
    (hss : ss ≠ σ) (hnear1 : j.val ≤ k.val + 2) (hnear2 : k.val ≤ j.val + 2) :
    Multiset.countP (bandSt (L := L) (K := K) σ j)
          ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} :
            Multiset (AgentState L K)) + 1 ≤
      Multiset.countP (bandSt (L := L) (K := K) σ j)
        ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_bandSt_pair, countP_bandSt_pair]
  by_cases h0 : j.val = k.val
  · have hcs : cancelSplit L K s t =
        ({s with bias := .zero}, {t with bias := .zero}) := by
      unfold cancelSplit
      rw [hsb, htb]
      simp only [if_pos (show σ ≠ ss from fun h => hss h.symm), dif_pos h0]
    rw [hcs]
    simp [bandSt, hsM, htM, hsb, htb, hss]
  · by_cases h1 : j.val + 1 = k.val
    · have hcs : cancelSplit L K s t =
          ({s with bias := .dyadic σ ⟨j.val + 1, by
              have hk := k.2
              omega⟩}, {t with bias := .zero}) := by
        unfold cancelSplit
        rw [hsb, htb]
        simp only [if_pos (show σ ≠ ss from fun h => hss h.symm), dif_neg h0,
          dif_pos h1]
      rw [hcs]
      simp [bandSt, hsM, htM, hsb, htb, hss, Fin.ext_iff]
    · by_cases h1' : k.val + 1 = j.val
      · have hcs : cancelSplit L K s t =
            ({s with bias := .zero}, {t with bias := .dyadic ss ⟨k.val + 1, by
                have hj := j.2
                omega⟩}) := by
          unfold cancelSplit
          rw [hsb, htb]
          simp only [if_pos (show σ ≠ ss from fun h => hss h.symm), dif_neg h0,
            dif_neg h1, dif_pos h1']
        rw [hcs]
        simp [bandSt, hsM, htM, hsb, htb, hss]
      · by_cases h2 : j.val + 2 = k.val
        · have hcs : cancelSplit L K s t =
              ({s with bias := .dyadic σ ⟨j.val + 1, by
                  have hk := k.2
                  omega⟩},
               {t with bias := .dyadic σ ⟨j.val + 2, by
                  have hk := k.2
                  omega⟩}) := by
            unfold cancelSplit
            rw [hsb, htb]
            simp only [if_pos (show σ ≠ ss from fun h => hss h.symm), dif_neg h0,
              dif_neg h1, dif_neg h1', dif_pos h2]
          rw [hcs]
          simp [bandSt, hsM, htM, hsb, htb, hss, Fin.ext_iff]
        · by_cases h2' : k.val + 2 = j.val
          · have hcs : cancelSplit L K s t =
                ({s with bias := .dyadic ss ⟨k.val + 2, by
                    have hj := j.2
                    omega⟩},
                 {t with bias := .dyadic ss ⟨k.val + 1, by
                    have hj := j.2
                    omega⟩}) := by
              unfold cancelSplit
              rw [hsb, htb]
              simp only [if_pos (show σ ≠ ss from fun h => hss h.symm), dif_neg h0,
                dif_neg h1, dif_neg h1', dif_neg h2, dif_pos h2']
            rw [hcs]
            simp [bandSt, hsM, htM, hsb, htb, hss]
          · omega

/-- A scheduled pair in the ordered rectangle
elimWithin2(σ,j) × minorityAt7(σ,j) lowers the exact-j count by at least one. -/
theorem bandCountN_stepOrSelf_drop_left
    (n : ℕ) (σ : Sign) (l E7 : ℕ) (j : Fin (L + 1))
    (c : Config (AgentState L K))
    (hready : Phase7StageReady (L := L) (K := K) n σ l E7 j c)
    (p : AgentState L K × AgentState L K)
    (hp : p ∈
      (elimWithin2 (L := L) (K := K) σ j ×ˢ
        Phase7Convergence.minorityAt7 (L := L) (K := K) σ j))
    (happ : Protocol.Applicable c p.1 p.2) :
    bandCountN (L := L) (K := K) σ j
          (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1 ≤
      bandCountN (L := L) (K := K) σ j c := by
  classical
  rw [Finset.mem_product] at hp
  obtain ⟨hpelim, hpmin⟩ := hp
  rw [elimWithin2, Finset.mem_filter] at hpelim
  rw [Phase7Convergence.minorityAt7, Finset.mem_filter] at hpmin
  obtain ⟨_, hsM, ss, k, hss, hsb, hnear1, hnear2⟩ := hpelim
  obtain ⟨_, htM, htb⟩ := hpmin
  have hm1 : p.1 ∈ c :=
    Multiset.mem_of_le
      (show ({p.1, p.2} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
  have hm2 : p.2 ∈ c :=
    Multiset.mem_of_le
      (show ({p.1, p.2} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
  have hs7 : p.1.phase.val = 7 := hready.honest.2 p.1 hm1
  have ht7 : p.2.phase.val = 7 := hready.honest.2 p.2 hm2
  have hT := Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
    (L := L) (K := K) p.1 p.2 hs7 ht7 hsM htM
  have hpair :
      Multiset.countP (bandSt (L := L) (K := K) σ j)
            ({(Transition L K p.1 p.2).1, (Transition L K p.1 p.2).2} :
              Multiset (AgentState L K)) + 1 ≤
        Multiset.countP (bandSt (L := L) (K := K) σ j)
          ({p.1, p.2} : Multiset (AgentState L K)) := by
    rw [hT]
    exact cancelSplit_band_pair_drop_left σ ss j k p.1 p.2
      hsM htM hsb htb hss hnear1 hnear2
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2 =
      c - {p.1, p.2} + {(Transition L K p.1 p.2).1, (Transition L K p.1 p.2).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsub : ({p.1, p.2} : Multiset (AgentState L K)) ≤ c := happ
  rw [bandCountN_eq_countP, bandCountN_eq_countP, hc',
    Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le :
      Multiset.countP (bandSt (L := L) (K := K) σ j)
          ({p.1, p.2} : Multiset (AgentState L K)) ≤
        Multiset.countP (bandSt (L := L) (K := K) σ j) c :=
    Multiset.countP_le_of_le _ hsub
  omega

/-- The reverse ordered rectangle minorityAt7(σ,j) × elimWithin2(σ,j)
also lowers the exact-j count by at least one. -/
theorem bandCountN_stepOrSelf_drop_right
    (n : ℕ) (σ : Sign) (l E7 : ℕ) (j : Fin (L + 1))
    (c : Config (AgentState L K))
    (hready : Phase7StageReady (L := L) (K := K) n σ l E7 j c)
    (p : AgentState L K × AgentState L K)
    (hp : p ∈
      (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j ×ˢ
        elimWithin2 (L := L) (K := K) σ j))
    (happ : Protocol.Applicable c p.1 p.2) :
    bandCountN (L := L) (K := K) σ j
          (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1 ≤
      bandCountN (L := L) (K := K) σ j c := by
  classical
  rw [Finset.mem_product] at hp
  obtain ⟨hpmin, hpelim⟩ := hp
  rw [Phase7Convergence.minorityAt7, Finset.mem_filter] at hpmin
  rw [elimWithin2, Finset.mem_filter] at hpelim
  obtain ⟨_, hsM, hsb⟩ := hpmin
  obtain ⟨_, htM, ss, k, hss, htb, hnear1, hnear2⟩ := hpelim
  have hm1 : p.1 ∈ c :=
    Multiset.mem_of_le
      (show ({p.1, p.2} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
  have hm2 : p.2 ∈ c :=
    Multiset.mem_of_le
      (show ({p.1, p.2} : Multiset (AgentState L K)) ≤ c from happ) (by simp)
  have hs7 : p.1.phase.val = 7 := hready.honest.2 p.1 hm1
  have ht7 : p.2.phase.val = 7 := hready.honest.2 p.2 hm2
  have hT := Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
    (L := L) (K := K) p.1 p.2 hs7 ht7 hsM htM
  have hpair :
      Multiset.countP (bandSt (L := L) (K := K) σ j)
            ({(Transition L K p.1 p.2).1, (Transition L K p.1 p.2).2} :
              Multiset (AgentState L K)) + 1 ≤
        Multiset.countP (bandSt (L := L) (K := K) σ j)
          ({p.1, p.2} : Multiset (AgentState L K)) := by
    rw [hT]
    exact cancelSplit_band_pair_drop_right σ ss j k p.1 p.2
      hsM htM hsb htb hss hnear1 hnear2
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2 =
      c - {p.1, p.2} + {(Transition L K p.1 p.2).1, (Transition L K p.1 p.2).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsub : ({p.1, p.2} : Multiset (AgentState L K)) ≤ c := happ
  rw [bandCountN_eq_countP, bandCountN_eq_countP, hc',
    Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le :
      Multiset.countP (bandSt (L := L) (K := K) σ j)
          ({p.1, p.2} : Multiset (AgentState L K)) ≤
        Multiset.countP (bandSt (L := L) (K := K) σ j) c :=
    Multiset.countP_le_of_le _ hsub
  omega

#print axioms bandCountN_eq_countP
#print axioms bandCountN_stepOrSelf_le
#print axioms bandClear_stepOrSelf
#print axioms bandCountN_stepOrSelf_drop_left
#print axioms bandCountN_stepOrSelf_drop_right

end Phase7BandTransition
end Ripple.PopulationProtocol.ExactMajority
