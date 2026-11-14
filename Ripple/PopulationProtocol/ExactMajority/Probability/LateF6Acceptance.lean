-- Ripple/PopulationProtocol/ExactMajority/Probability/LateF6Acceptance.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5To6FuelProducer

/-!
Actual F6 acceptance and freezing in the mixed Phase-3/4/5 window.
The original-law stopping-prefix transport is in LateF6OriginalLaw.
A Phase-4 advance runs Init 5 but does not dispatch Phase 5 again.
-/

namespace Ripple.PopulationProtocol.ExactMajority
namespace LateF6Acceptance

variable {L K : ℕ}

def Window (a : AgentState L K) : Prop :=
  3 ≤ a.phase.val ∧ a.phase.val ≤ 5

def Eligible (a : AgentState L K) : Prop :=
  a.role = .main ∧ ∃ σ j, a.bias = .dyadic σ j ∧ j.val < L

def liftTo (a : AgentState L K) (p : Fin 11) : AgentState L K :=
  runInitsBetween L K a.phase.val p.val { a with phase := p }

private theorem init_window_fields (p : Fin 11) (a : AgentState L K)
    (hlo : 4 ≤ p.val) (hhi : p.val ≤ 5) :
    (phaseInit L K p a).role = a.role ∧
      (phaseInit L K p a).bias = a.bias ∧
      (phaseInit L K p a).phase = a.phase := by
  have hp : p.val = 4 ∨ p.val = 5 := by omega
  rcases hp with hp | hp
  · have he : p = ⟨4, by decide⟩ := Fin.ext hp
    subst p
    simp [phaseInit]
  · refine ⟨?_, phaseInit_five_bias L K a p hp,
      phaseInit_five_phase L K a p hp⟩
    rw [phaseInit_role]
    simp [hp]

private theorem run_window_fields (oldP newP : ℕ)
    (hold : 3 ≤ oldP) (hnew : newP ≤ 5) (a : AgentState L K) :
    (runInitsBetween L K oldP newP a).role = a.role ∧
      (runInitsBetween L K oldP newP a).bias = a.bias ∧
      (runInitsBetween L K oldP newP a).phase = a.phase := by
  unfold runInitsBetween
  have haux : ∀ xs : List ℕ,
      (∀ k ∈ xs, oldP < k ∧ k ≤ newP) → ∀ b : AgentState L K,
      (xs.foldl (fun acc k => if h : k < 11 then
        phaseInit L K ⟨k, h⟩ acc else acc) b).role = b.role ∧
      (xs.foldl (fun acc k => if h : k < 11 then
        phaseInit L K ⟨k, h⟩ acc else acc) b).bias = b.bias ∧
      (xs.foldl (fun acc k => if h : k < 11 then
        phaseInit L K ⟨k, h⟩ acc else acc) b).phase = b.phase := by
    intro xs
    induction xs with
    | nil => intro _ b; exact ⟨rfl, rfl, rfl⟩
    | cons k xs ih =>
      intro hxs b
      have hk := hxs k (by simp)
      have hklo : 4 ≤ k := by omega
      have hkhi : k ≤ 5 := by omega
      have hklt : k < 11 := by omega
      simp only [List.foldl_cons, dif_pos hklt]
      rcases init_window_fields (L := L) (K := K) ⟨k, hklt⟩ b hklo hkhi
        with ⟨hr, hb, hp⟩
      rcases ih (fun j hj => hxs j (by simp [hj]))
          (phaseInit L K ⟨k, hklt⟩ b) with ⟨hr', hb', hp'⟩
      exact ⟨hr'.trans hr, hb'.trans hb, hp'.trans hp⟩
  exact haux _ (fun k hk => by simpa using (List.mem_filter.mp hk).2) a

theorem liftTo_fields (a : AgentState L K) (p : Fin 11)
    (ha : 3 ≤ a.phase.val) (hp : p.val ≤ 5) :
    (liftTo a p).role = a.role ∧ (liftTo a p).bias = a.bias ∧
      (liftTo a p).phase = p := by
  exact run_window_fields a.phase.val p.val ha hp { a with phase := p }

theorem liftTo_self (a : AgentState L K) (p : Fin 11)
    (hp : a.phase = p) : liftTo a p = a := by
  subst p
  simp [liftTo, runInitsBetween_self]

theorem epidemic_eq_lifts (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    phaseEpidemicUpdate L K s t =
      (liftTo s (max s.phase t.phase), liftTo t (max s.phase t.phase)) := by
  have hp : (max s.phase t.phase).val ≤ 5 := by
    change max s.phase.val t.phase.val ≤ 5
    exact max_le hs.2 ht.2
  have hsp := (liftTo_fields s (max s.phase t.phase) hs.1 hp).2.2
  have htp := (liftTo_fields t (max s.phase t.phase) ht.1 hp).2.2
  have hnot : ¬ ((s.phase.val < 10 ∨ t.phase.val < 10) ∧
      ((liftTo s (max s.phase t.phase)).phase.val = 10 ∨
        (liftTo t (max s.phase t.phase)).phase.val = 10)) := by
    rintro ⟨_, h | h⟩
    · rw [hsp] at h; omega
    · rw [htp] at h; omega
  unfold phaseEpidemicUpdate
  unfold liftTo at hnot ⊢
  rw [if_neg hnot]

theorem liftTo_reserve_hour (r : AgentState L K) (hr : Window r)
    (hrole : r.role = .reserve) :
    (liftTo r ⟨5, by decide⟩).hour =
      if r.phase.val = 5 then r.hour else sampleUnset := by
  by_cases hp : r.phase.val = 5
  · rw [if_pos hp, liftTo_self r _ (Fin.ext hp)]
  · rw [if_neg hp]
    have hc : r.phase.val = 3 ∨ r.phase.val = 4 := by
      rcases hr with ⟨hlo, hhi⟩
      omega
    rcases hc with hc | hc
    · have hlist : (List.range 11).filter (fun k => 3 < k ∧ k ≤ 5) = [4, 5] := by decide
      simp only [liftTo, runInitsBetween, hc]
      rw [hlist]
      simp [phaseInit, hrole]
    · have hlist : (List.range 11).filter (fun k => 4 < k ∧ k ≤ 5) = [5] := by decide
      simp only [liftTo, runInitsBetween, hc]
      rw [hlist]
      simp [phaseInit, hrole]

theorem local_reserve_left (r m : AgentState L K) (hr : r.role = .reserve) :
    (Phase5Transition L K r m).1 =
      if m.role = .main ∧ m.bias ≠ .zero ∧ r.hour.val = L then
        { r with hour := exponentOf L m.bias } else r := by
  by_cases hm : m.role = .main <;>
    by_cases hb : m.bias = .zero <;>
      by_cases hh : r.hour.val = L <;>
        simp [Phase5Transition, hr, hm, hb, hh]

theorem local_reserve_right (m r : AgentState L K) (hr : r.role = .reserve) :
    (Phase5Transition L K m r).2 =
      if m.role = .main ∧ m.bias ≠ .zero ∧ r.hour.val = L then
        { r with hour := exponentOf L m.bias } else r := by
  by_cases hm : m.role = .main <;>
    by_cases hb : m.bias = .zero <;>
      by_cases hh : r.hour.val = L <;>
        simp [Phase5Transition, hr, hm, hb, hh]

theorem local_main_left (m r : AgentState L K) (hm : m.role = .main) :
    (Phase5Transition L K m r).1 = m := by
  by_cases hr : r.role = .reserve <;>
    by_cases hb : m.bias = .zero <;>
      by_cases hh : r.hour.val = L <;>
        simp [Phase5Transition, hm, hr, hb, hh]

theorem local_main_right (r m : AgentState L K) (hm : m.role = .main) :
    (Phase5Transition L K r m).2 = m := by
  by_cases hr : r.role = .reserve <;>
    by_cases hb : m.bias = .zero <;>
      by_cases hh : r.hour.val = L <;>
        simp [Phase5Transition, hm, hr, hb, hh]

theorem local_reserve_phase_left (r m : AgentState L K)
    (hr : r.role = .reserve) :
    (Phase5Transition L K r m).1.phase = r.phase := by
  rw [local_reserve_left r m hr]
  split_ifs <;> rfl

theorem local_reserve_phase_right (m r : AgentState L K)
    (hr : r.role = .reserve) :
    (Phase5Transition L K m r).2.phase = r.phase := by
  rw [local_reserve_right m r hr]
  split_ifs <;> rfl

theorem local_reserve_hour_left (r m : AgentState L K)
    (hr : r.role = .reserve) (hh : r.hour.val = L) :
    (Phase5Transition L K r m).1.hour =
      if m.role = .main ∧ m.bias ≠ .zero then exponentOf L m.bias else r.hour := by
  rw [local_reserve_left r m hr]
  by_cases h : m.role = .main ∧ m.bias ≠ .zero <;> simp [h, hh]

theorem local_reserve_hour_right (m r : AgentState L K)
    (hr : r.role = .reserve) (hh : r.hour.val = L) :
    (Phase5Transition L K m r).2.hour =
      if m.role = .main ∧ m.bias ≠ .zero then exponentOf L m.bias else r.hour := by
  rw [local_reserve_right m r hr]
  by_cases h : m.role = .main ∧ m.bias ≠ .zero <;> simp [h, hh]

theorem local_accept_left (r m : AgentState L K)
    (hr : r.role = .reserve) (hh : r.hour.val = L) :
    (Phase5Transition L K r m).1.hour.val < L ↔ Eligible m := by
  rw [local_reserve_hour_left r m hr hh]
  by_cases hm : m.role = .main
  · cases hb : m.bias <;> simp [Eligible, hm, hb, exponentOf, hh]
  · simp [Eligible, hm, hh]

theorem local_accept_right (m r : AgentState L K)
    (hr : r.role = .reserve) (hh : r.hour.val = L) :
    (Phase5Transition L K m r).2.hour.val < L ↔ Eligible m := by
  rw [local_reserve_hour_right m r hr hh]
  by_cases hm : m.role = .main
  · cases hb : m.bias <;> simp [Eligible, hm, hb, exponentOf, hh]
  · simp [Eligible, hm, hh]

theorem local_sentinel_invisible_left (r m : AgentState L K)
    (hr : r.role = .reserve) (hm : m.role = .main)
    (hh : r.hour.val = L) (σ : Sign)
    (hb : m.bias = .dyadic σ (sampleUnset : Fin (L + 1))) :
    (Phase5Transition L K r m).1 = r := by
  have he : (sampleUnset : Fin (L + 1)) = r.hour := Fin.ext hh.symm
  rw [local_reserve_left r m hr]
  simp [hm, hb, hh, exponentOf, he]

theorem local_sentinel_invisible_right (m r : AgentState L K)
    (hr : r.role = .reserve) (hm : m.role = .main)
    (hh : r.hour.val = L) (σ : Sign)
    (hb : m.bias = .dyadic σ (sampleUnset : Fin (L + 1))) :
    (Phase5Transition L K m r).2 = r := by
  have he : (sampleUnset : Fin (L + 1)) = r.hour := Fin.ext hh.symm
  rw [local_reserve_right m r hr]
  simp [hm, hb, hh, exponentOf, he]

theorem split_unset (r m : AgentState L K) (hh : r.hour.val = L) :
    doSplit L K r m = (r, m) := by
  cases hb : m.bias <;> simp [doSplit, hb, hh]

theorem transition_max_five (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hmax : max s.phase.val t.phase.val = 5) :
    Transition L K s t = Phase5Transition L K
      (liftTo s ⟨5, by decide⟩) (liftTo t ⟨5, by decide⟩) := by
  let a := liftTo s (⟨5, by decide⟩ : Fin 11)
  let b := liftTo t (⟨5, by decide⟩ : Fin 11)
  have hp : max s.phase t.phase = ⟨5, by decide⟩ := Fin.ext hmax
  have hepi : phaseEpidemicUpdate L K s t = (a, b) := by
    simpa only [hp] using epidemic_eq_lifts s t hs ht
  have hap : a.phase = ⟨5, by decide⟩ := (liftTo_fields s _ hs.1 (by decide)).2.2
  have hbp : b.phase = ⟨5, by decide⟩ := (liftTo_fields t _ ht.1 (by decide)).2.2
  have hav : a.phase.val = 5 := congrArg Fin.val hap
  have hbv : b.phase.val = 5 := congrArg Fin.val hbp
  obtain ⟨hle, hle'⟩ := ReserveSampling.Phase5Transition_phase_le_six a b hav hbv
  unfold Transition
  rw [hepi]
  simp only [hap]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 L K a _ (by omega),
    finishPhase10Entry_eq_self_of_after_ne_10 L K b _ (by omega)]

private theorem below_freeze (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hmax : ¬ 4 ≤ max s.phase.val t.phase.val) :
    s.phase.val = 3 ∧ t.phase.val = 3 := by
  have hlo := hs.1
  have hlo' := ht.1
  have hsl := le_max_left s.phase.val t.phase.val
  have htl := le_max_right s.phase.val t.phase.val
  omega

theorem transition_freeze_fields (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hmax : 4 ≤ max s.phase.val t.phase.val) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).1.bias = s.bias ∧
      (Transition L K s t).2.role = t.role ∧
      (Transition L K s t).2.bias = t.bias := by
  have hupper : max s.phase.val t.phase.val ≤ 5 := max_le hs.2 ht.2
  have hc : max s.phase.val t.phase.val = 4 ∨
      max s.phase.val t.phase.val = 5 := by omega
  rcases hc with hc | hc
  · let a := liftTo s (⟨4, by decide⟩ : Fin 11)
    let b := liftTo t (⟨4, by decide⟩ : Fin 11)
    have hp : max s.phase t.phase = ⟨4, by decide⟩ := Fin.ext hc
    have hepi : phaseEpidemicUpdate L K s t = (a, b) := by
      simpa only [hp] using epidemic_eq_lifts s t hs ht
    have ha := liftTo_fields s (⟨4, by decide⟩ : Fin 11) hs.1 (by decide)
    have hb := liftTo_fields t (⟨4, by decide⟩ : Fin 11) ht.1 (by decide)
    have hap : a.phase = ⟨4, by decide⟩ := ha.2.2
    have hav : a.phase.val = 4 := congrArg Fin.val ha.2.2
    have hbv : b.phase.val = 4 := congrArg Fin.val hb.2.2
    have hl := Phase5To6FuelProducer.Phase4Transition_role_bias a b hav hbv
    unfold Transition
    rw [hepi]
    simp only [hap, finishPhase10Entry_role, finishPhase10Entry_bias]
    exact ⟨hl.1.trans ha.1, hl.2.1.trans ha.2.1,
      hl.2.2.1.trans hb.1, hl.2.2.2.trans hb.2.1⟩
  · rw [transition_max_five s t hs ht hc]
    let a := liftTo s (⟨5, by decide⟩ : Fin 11)
    let b := liftTo t (⟨5, by decide⟩ : Fin 11)
    have ha := liftTo_fields s (⟨5, by decide⟩ : Fin 11) hs.1 (by decide)
    have hb := liftTo_fields t (⟨5, by decide⟩ : Fin 11) ht.1 (by decide)
    have hav : a.phase.val = 5 := congrArg Fin.val ha.2.2
    have hbv : b.phase.val = 5 := congrArg Fin.val hb.2.2
    exact ⟨(Phase5Convergence.Phase5Transition_fst_role_eq a b hav).trans ha.1,
      (Phase5Convergence.Phase5Transition_fst_bias_eq a b hav).trans ha.2.1,
      (Phase5Convergence.Phase5Transition_snd_role_eq a b hbv).trans hb.1,
      (Phase5Convergence.Phase5Transition_snd_bias_eq a b hbv).trans hb.2.1⟩

theorem transition_roles (s t : AgentState L K)
    (hs : Window s) (ht : Window t) :
    (Transition L K s t).1.role = s.role ∧
      (Transition L K s t).2.role = t.role := by
  by_cases hm : 4 ≤ max s.phase.val t.phase.val
  · have h := transition_freeze_fields s t hs ht hm
    exact ⟨h.1, h.2.2.1⟩
  · obtain ⟨hs', ht'⟩ := below_freeze s t hs ht hm
    have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs' ht'
    have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs'
    have hr := Phase5To6FuelProducer.Phase3Transition_roles s t hs' ht'
    unfold Transition
    rw [hepi]
    simpa only [hsp, finishPhase10Entry_role] using hr

private theorem main_three_left (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) (hm : s.role = .main) :
    (Transition L K s t).1.phase.val = 3 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hl := (Phase3Transition_left_output_eq_rule1 L K s t s (by simp [hm])).2
  unfold Transition
  rw [hepi]
  simp only [hsp, finishPhase10Entry_phase_val]
  exact (congrArg Fin.val hl).trans hs

private theorem main_three_right (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) (hm : t.role = .main) :
    (Transition L K s t).2.phase.val = 3 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hl := (Phase3Transition_right_output_eq_rule1 L K s t t (by simp [hm])).2
  unfold Transition
  rw [hepi]
  simp only [hsp, finishPhase10Entry_phase_val]
  exact (congrArg Fin.val hl).trans ht

private theorem main_freeze_max_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hm : s.role = .main)
    (hf : 4 ≤ (Transition L K s t).1.phase.val) :
    4 ≤ max s.phase.val t.phase.val := by
  by_contra h
  obtain ⟨hs', ht'⟩ := below_freeze s t hs ht h
  have hp := main_three_left s t hs' ht' hm
  omega

private theorem main_freeze_max_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hm : t.role = .main)
    (hf : 4 ≤ (Transition L K s t).2.phase.val) :
    4 ≤ max s.phase.val t.phase.val := by
  by_contra h
  obtain ⟨hs', ht'⟩ := below_freeze s t hs ht h
  have hp := main_three_right s t hs' ht' hm
  omega

theorem transition_main_freeze_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hm : s.role = .main)
    (hf : 4 ≤ (Transition L K s t).1.phase.val) :
    (Transition L K s t).1.bias = s.bias :=
  (transition_freeze_fields s t hs ht (main_freeze_max_left s t hs ht hm hf)).2.1

theorem transition_main_freeze_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hm : t.role = .main)
    (hf : 4 ≤ (Transition L K s t).2.phase.val) :
    (Transition L K s t).2.bias = t.bias :=
  (transition_freeze_fields s t hs ht (main_freeze_max_right s t hs ht hm hf)).2.2.2

private theorem local_eligible_four_left (s t : AgentState L K)
    (hs : s.phase.val = 4) (he : Eligible s) :
    (Phase4Transition L K s t).1.phase.val = 5 := by
  rcases he with ⟨hr, σ, j, hb, hj⟩
  simp [Phase4Transition, hb, hj, advancePhaseWithInit, advancePhase,
    hs, phaseInit, hr]

private theorem local_eligible_four_right (s t : AgentState L K)
    (ht : t.phase.val = 4) (he : Eligible t) :
    (Phase4Transition L K s t).2.phase.val = 5 := by
  rcases he with ⟨hr, σ, j, hb, hj⟩
  simp [Phase4Transition, hb, hj, advancePhaseWithInit, advancePhase,
    ht, phaseInit, hr]

theorem transition_eligible_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hmax : 4 ≤ max s.phase.val t.phase.val) (he : Eligible s) :
    (Transition L K s t).1.phase.val = 5 := by
  have hupper : max s.phase.val t.phase.val ≤ 5 := max_le hs.2 ht.2
  have hc : max s.phase.val t.phase.val = 4 ∨
      max s.phase.val t.phase.val = 5 := by omega
  rcases hc with hc | hc
  · let a := liftTo s (⟨4, by decide⟩ : Fin 11)
    let b := liftTo t (⟨4, by decide⟩ : Fin 11)
    have hp : max s.phase t.phase = ⟨4, by decide⟩ := Fin.ext hc
    have hepi : phaseEpidemicUpdate L K s t = (a, b) := by
      simpa only [hp] using epidemic_eq_lifts s t hs ht
    have ha := liftTo_fields s (⟨4, by decide⟩ : Fin 11) hs.1 (by decide)
    have hap : a.phase = ⟨4, by decide⟩ := ha.2.2
    have hav : a.phase.val = 4 := congrArg Fin.val ha.2.2
    have hea : Eligible a := by
      rcases he with ⟨hr, σ, j, hb, hj⟩
      exact ⟨ha.1.trans hr, σ, j, ha.2.1.trans hb, hj⟩
    have hl := local_eligible_four_left a b hav hea
    unfold Transition
    rw [hepi]
    simpa only [hap, finishPhase10Entry_phase_val] using hl
  · rw [transition_max_five s t hs ht hc]
    have ha := liftTo_fields s (⟨5, by decide⟩ : Fin 11) hs.1 (by decide)
    rw [local_main_left _ _ (ha.1.trans he.1)]
    exact congrArg Fin.val ha.2.2

theorem transition_eligible_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hmax : 4 ≤ max s.phase.val t.phase.val) (he : Eligible t) :
    (Transition L K s t).2.phase.val = 5 := by
  have hupper : max s.phase.val t.phase.val ≤ 5 := max_le hs.2 ht.2
  have hc : max s.phase.val t.phase.val = 4 ∨
      max s.phase.val t.phase.val = 5 := by omega
  rcases hc with hc | hc
  · let a := liftTo s (⟨4, by decide⟩ : Fin 11)
    let b := liftTo t (⟨4, by decide⟩ : Fin 11)
    have hp : max s.phase t.phase = ⟨4, by decide⟩ := Fin.ext hc
    have hepi : phaseEpidemicUpdate L K s t = (a, b) := by
      simpa only [hp] using epidemic_eq_lifts s t hs ht
    have ha := liftTo_fields s (⟨4, by decide⟩ : Fin 11) hs.1 (by decide)
    have hb := liftTo_fields t (⟨4, by decide⟩ : Fin 11) ht.1 (by decide)
    have hap : a.phase = ⟨4, by decide⟩ := ha.2.2
    have hbv : b.phase.val = 4 := congrArg Fin.val hb.2.2
    have heb : Eligible b := by
      rcases he with ⟨hr, σ, j, hbi, hj⟩
      exact ⟨hb.1.trans hr, σ, j, hb.2.1.trans hbi, hj⟩
    have hl := local_eligible_four_right a b hbv heb
    unfold Transition
    rw [hepi]
    simpa only [hap, finishPhase10Entry_phase_val] using hl
  · rw [transition_max_five s t hs ht hc]
    have hb := liftTo_fields t (⟨5, by decide⟩ : Fin 11) ht.1 (by decide)
    rw [local_main_right _ _ (hb.1.trans he.1)]
    exact congrArg Fin.val hb.2.2

theorem transition_frozen_eligible_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (he : Eligible (Transition L K s t).1)
    (hf : 4 ≤ (Transition L K s t).1.phase.val) :
    (Transition L K s t).1.phase.val = 5 := by
  have hr := (transition_roles s t hs ht).1
  have hm : s.role = .main := hr.symm.trans he.1
  have hb := transition_main_freeze_left s t hs ht hm hf
  have hin : Eligible s := by
    rcases he with ⟨_, σ, j, hbi, hj⟩
    exact ⟨hm, σ, j, hb.symm.trans hbi, hj⟩
  exact transition_eligible_left s t hs ht
    (main_freeze_max_left s t hs ht hm hf) hin

theorem transition_frozen_eligible_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (he : Eligible (Transition L K s t).2)
    (hf : 4 ≤ (Transition L K s t).2.phase.val) :
    (Transition L K s t).2.phase.val = 5 := by
  have hr := (transition_roles s t hs ht).2
  have hm : t.role = .main := hr.symm.trans he.1
  have hb := transition_main_freeze_right s t hs ht hm hf
  have hin : Eligible t := by
    rcases he with ⟨_, σ, j, hbi, hj⟩
    exact ⟨hm, σ, j, hb.symm.trans hbi, hj⟩
  exact transition_eligible_right s t hs ht
    (main_freeze_max_right s t hs ht hm hf) hin

theorem transition_class_freeze_left (C : Bias L → Prop) (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hf : 4 ≤ (Transition L K s t).1.phase.val) :
    ((Transition L K s t).1.role = .main ∧ C (Transition L K s t).1.bias) ↔
      (s.role = .main ∧ C s.bias) := by
  have hr := (transition_roles s t hs ht).1
  by_cases hm : s.role = .main
  · have hb := transition_main_freeze_left s t hs ht hm hf
    rw [hr, hb]
  · simp [hr, hm]

theorem transition_class_freeze_right (C : Bias L → Prop) (s t : AgentState L K)
    (hs : Window s) (ht : Window t)
    (hf : 4 ≤ (Transition L K s t).2.phase.val) :
    ((Transition L K s t).2.role = .main ∧ C (Transition L K s t).2.bias) ↔
      (t.role = .main ∧ C t.bias) := by
  have hr := (transition_roles s t hs ht).2
  by_cases hm : t.role = .main
  · have hb := transition_main_freeze_right s t hs ht hm hf
    rw [hr, hb]
  · simp [hr, hm]

theorem transition_locked_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hr : s.role = .reserve)
    (hp : s.phase.val = 5) (hh : s.hour.val ≠ L) :
    (Transition L K s t).1.role = .reserve ∧
      (Transition L K s t).1.phase.val = 5 ∧
      (Transition L K s t).1.hour = s.hour := by
  have hmax : max s.phase.val t.phase.val = 5 := by
    simp only [hp, max_eq_left ht.2]
  rw [transition_max_five s t hs ht hmax, liftTo_self s _ (Fin.ext hp)]
  refine ⟨?_, ?_, ?_⟩
  · exact (Phase5Convergence.Phase5Transition_fst_role_eq _ _ hp).trans hr
  · exact (congrArg Fin.val (local_reserve_phase_left _ _ hr)).trans hp
  · exact Phase5Convergence.Phase5Transition_fst_hour_eq_of_reserve_ne_L _ _ hr hh

theorem transition_locked_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hr : t.role = .reserve)
    (hp : t.phase.val = 5) (hh : t.hour.val ≠ L) :
    (Transition L K s t).2.role = .reserve ∧
      (Transition L K s t).2.phase.val = 5 ∧
      (Transition L K s t).2.hour = t.hour := by
  have hmax : max s.phase.val t.phase.val = 5 := by
    simp only [hp, max_eq_right hs.2]
  rw [transition_max_five s t hs ht hmax, liftTo_self t _ (Fin.ext hp)]
  refine ⟨?_, ?_, ?_⟩
  · exact (Phase5Convergence.Phase5Transition_snd_role_eq _ _ hp).trans hr
  · exact (congrArg Fin.val (local_reserve_phase_right _ _ hr)).trans hp
  · exact Phase5Convergence.Phase5Transition_snd_hour_eq_of_reserve_ne_L _ _ hr hh

/-- A genuine new accepted sample; a pre-5 Reserve is unset regardless of stale raw hour. -/
def Accepted (r r' : AgentState L K) : Prop :=
  r.role = .reserve ∧ (r.phase.val < 5 ∨ r.hour.val = L) ∧
    r'.role = .reserve ∧ r'.phase.val = 5 ∧ r'.hour.val < L

private theorem reserve_three_left (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) (hr : s.role = .reserve) :
    (Transition L K s t).1.phase.val = 3 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hl := (Phase3Transition_left_output_eq_rule1 L K s t s (by simp [hr])).2
  unfold Transition
  rw [hepi]
  simp only [hsp, finishPhase10Entry_phase_val]
  exact (congrArg Fin.val hl).trans hs

private theorem reserve_three_right (s t : AgentState L K)
    (hs : s.phase.val = 3) (ht : t.phase.val = 3) (hr : t.role = .reserve) :
    (Transition L K s t).2.phase.val = 3 := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsp : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hl := (Phase3Transition_right_output_eq_rule1 L K s t t (by simp [hr])).2
  unfold Transition
  rw [hepi]
  simp only [hsp, finishPhase10Entry_phase_val]
  exact (congrArg Fin.val hl).trans ht

private theorem local_four_no_accept_left (s t : AgentState L K)
    (hp : s.phase.val = 4) (hr : s.role = .reserve) :
    ¬ ((Phase4Transition L K s t).1.phase.val = 5 ∧
      (Phase4Transition L K s t).1.hour.val < L) := by
  unfold Phase4Transition
  dsimp
  split_ifs <;>
    simp [advancePhaseWithInit, advancePhase, hp, phaseInit, hr, sampleUnset]

private theorem local_four_no_accept_right (s t : AgentState L K)
    (hp : t.phase.val = 4) (hr : t.role = .reserve) :
    ¬ ((Phase4Transition L K s t).2.phase.val = 5 ∧
      (Phase4Transition L K s t).2.hour.val < L) := by
  unfold Phase4Transition
  dsimp
  split_ifs <;>
    simp [advancePhaseWithInit, advancePhase, hp, phaseInit, hr, sampleUnset]

private theorem actual_four_no_accept_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hc : max s.phase.val t.phase.val = 4)
    (hr : s.role = .reserve) :
    ¬ ((Transition L K s t).1.phase.val = 5 ∧
      (Transition L K s t).1.hour.val < L) := by
  let a := liftTo s (⟨4, by decide⟩ : Fin 11)
  let b := liftTo t (⟨4, by decide⟩ : Fin 11)
  have hp : max s.phase t.phase = ⟨4, by decide⟩ := Fin.ext hc
  have hepi : phaseEpidemicUpdate L K s t = (a, b) := by
    simpa only [hp] using epidemic_eq_lifts s t hs ht
  have ha := liftTo_fields s (⟨4, by decide⟩ : Fin 11) hs.1 (by decide)
  have hap : a.phase = ⟨4, by decide⟩ := ha.2.2
  have hav : a.phase.val = 4 := congrArg Fin.val ha.2.2
  have hl := local_four_no_accept_left a b hav (ha.1.trans hr)
  unfold Transition
  rw [hepi]
  simpa only [hap, finishPhase10Entry_phase_val, finishPhase10Entry_hour] using hl

private theorem actual_four_no_accept_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (hc : max s.phase.val t.phase.val = 4)
    (hr : t.role = .reserve) :
    ¬ ((Transition L K s t).2.phase.val = 5 ∧
      (Transition L K s t).2.hour.val < L) := by
  let a := liftTo s (⟨4, by decide⟩ : Fin 11)
  let b := liftTo t (⟨4, by decide⟩ : Fin 11)
  have hp : max s.phase t.phase = ⟨4, by decide⟩ := Fin.ext hc
  have hepi : phaseEpidemicUpdate L K s t = (a, b) := by
    simpa only [hp] using epidemic_eq_lifts s t hs ht
  have ha := liftTo_fields s (⟨4, by decide⟩ : Fin 11) hs.1 (by decide)
  have hb := liftTo_fields t (⟨4, by decide⟩ : Fin 11) ht.1 (by decide)
  have hap : a.phase = ⟨4, by decide⟩ := ha.2.2
  have hbv : b.phase.val = 4 := congrArg Fin.val hb.2.2
  have hl := local_four_no_accept_right a b hbv (hb.1.trans hr)
  unfold Transition
  rw [hepi]
  simpa only [hap, finishPhase10Entry_phase_val, finishPhase10Entry_hour] using hl

private theorem accepted_max_left (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (ha : Accepted s (Transition L K s t).1) :
    max s.phase.val t.phase.val = 5 := by
  have hlo : 3 ≤ max s.phase.val t.phase.val := hs.1.trans (le_max_left _ _)
  have hhi : max s.phase.val t.phase.val ≤ 5 := max_le hs.2 ht.2
  have hc : max s.phase.val t.phase.val = 3 ∨
      max s.phase.val t.phase.val = 4 ∨ max s.phase.val t.phase.val = 5 := by omega
  rcases hc with hc | hc | hc
  · have hslo := hs.1
    have htlo := ht.1
    have hsl := le_max_left s.phase.val t.phase.val
    have htl := le_max_right s.phase.val t.phase.val
    have hs' : s.phase.val = 3 := by omega
    have ht' : t.phase.val = 3 := by omega
    have hp := reserve_three_left s t hs' ht' ha.1
    have hp' := ha.2.2.2.1
    omega
  · exact False.elim ((actual_four_no_accept_left s t hs ht hc ha.1)
      ⟨ha.2.2.2.1, ha.2.2.2.2⟩)
  · exact hc

private theorem accepted_max_right (s t : AgentState L K)
    (hs : Window s) (ht : Window t) (ha : Accepted t (Transition L K s t).2) :
    max s.phase.val t.phase.val = 5 := by
  have hlo : 3 ≤ max s.phase.val t.phase.val := hs.1.trans (le_max_left _ _)
  have hhi : max s.phase.val t.phase.val ≤ 5 := max_le hs.2 ht.2
  have hc : max s.phase.val t.phase.val = 3 ∨
      max s.phase.val t.phase.val = 4 ∨ max s.phase.val t.phase.val = 5 := by omega
  rcases hc with hc | hc | hc
  · have hslo := hs.1
    have htlo := ht.1
    have hsl := le_max_left s.phase.val t.phase.val
    have htl := le_max_right s.phase.val t.phase.val
    have hs' : s.phase.val = 3 := by omega
    have ht' : t.phase.val = 3 := by omega
    have hp := reserve_three_right s t hs' ht' ha.1
    have hp' := ha.2.2.2.1
    omega
  · exact False.elim ((actual_four_no_accept_right s t hs ht hc ha.1)
      ⟨ha.2.2.2.1, ha.2.2.2.2⟩)
  · exact hc

private theorem fresh_lift_hour (r : AgentState L K) (hr : Window r)
    (hrole : r.role = .reserve) (hf : r.phase.val < 5 ∨ r.hour.val = L) :
    (liftTo r ⟨5, by decide⟩).hour.val = L := by
  rw [liftTo_reserve_hour r hr hrole]
  split_ifs with hp
  · rcases hf with hf | hf
    · omega
    · exact hf
  · rfl

theorem fresh_accept_left (r m : AgentState L K)
    (hr : Window r) (hm : Window m) (hrole : r.role = .reserve)
    (hf : r.phase.val < 5 ∨ r.hour.val = L)
    (hmax : max r.phase.val m.phase.val = 5) :
    Accepted r (Transition L K r m).1 ↔ Eligible m := by
  let a := liftTo r (⟨5, by decide⟩ : Fin 11)
  let b := liftTo m (⟨5, by decide⟩ : Fin 11)
  have ha := liftTo_fields r (⟨5, by decide⟩ : Fin 11) hr.1 (by decide)
  have hb := liftTo_fields m (⟨5, by decide⟩ : Fin 11) hm.1 (by decide)
  have har : a.role = .reserve := ha.1.trans hrole
  have hap : a.phase.val = 5 := congrArg Fin.val ha.2.2
  have hah : a.hour.val = L := fresh_lift_hour r hr hrole hf
  have hequiv : Eligible b ↔ Eligible m := by
    unfold Eligible
    rw [hb.1, hb.2.1]
  rw [transition_max_five r m hr hm hmax]
  constructor
  · intro h
    exact hequiv.mp ((local_accept_left a b har hah).mp h.2.2.2.2)
  · intro h
    exact ⟨hrole, hf,
      (Phase5Convergence.Phase5Transition_fst_role_eq a b hap).trans har,
      (congrArg Fin.val (local_reserve_phase_left a b har)).trans hap,
      (local_accept_left a b har hah).mpr (hequiv.mpr h)⟩

theorem fresh_accept_right (m r : AgentState L K)
    (hm : Window m) (hr : Window r) (hrole : r.role = .reserve)
    (hf : r.phase.val < 5 ∨ r.hour.val = L)
    (hmax : max m.phase.val r.phase.val = 5) :
    Accepted r (Transition L K m r).2 ↔ Eligible m := by
  let a := liftTo m (⟨5, by decide⟩ : Fin 11)
  let b := liftTo r (⟨5, by decide⟩ : Fin 11)
  have ha := liftTo_fields m (⟨5, by decide⟩ : Fin 11) hm.1 (by decide)
  have hb := liftTo_fields r (⟨5, by decide⟩ : Fin 11) hr.1 (by decide)
  have hbr : b.role = .reserve := hb.1.trans hrole
  have hbp : b.phase.val = 5 := congrArg Fin.val hb.2.2
  have hbh : b.hour.val = L := fresh_lift_hour r hr hrole hf
  have hequiv : Eligible a ↔ Eligible m := by
    unfold Eligible
    rw [ha.1, ha.2.1]
  rw [transition_max_five m r hm hr hmax]
  constructor
  · intro h
    exact hequiv.mp ((local_accept_right a b hbr hbh).mp h.2.2.2.2)
  · intro h
    exact ⟨hrole, hf,
      (Phase5Convergence.Phase5Transition_snd_role_eq a b hbp).trans hbr,
      (congrArg Fin.val (local_reserve_phase_right a b hbr)).trans hbp,
      (local_accept_right a b hbr hbh).mpr (hequiv.mpr h)⟩

theorem transition_accept_left (r m : AgentState L K)
    (hr : Window r) (hm : Window m) :
    Accepted r (Transition L K r m).1 ↔
      r.role = .reserve ∧
        ((r.phase.val = 5 ∧ r.hour.val = L ∧ Eligible m) ∨
          (r.phase.val < 5 ∧ m.phase.val = 5 ∧ Eligible m)) := by
  constructor
  · intro h
    have hmax := accepted_max_left r m hr hm h
    have he := (fresh_accept_left r m hr hm h.1 h.2.1 hmax).mp h
    refine ⟨h.1, ?_⟩
    by_cases hp : r.phase.val = 5
    · have hh : r.hour.val = L := by
        rcases h.2.1 with hh | hh
        · omega
        · exact hh
      exact Or.inl ⟨hp, hh, he⟩
    · have hlt : r.phase.val < 5 := by have hu := hr.2; omega
      have hmp : m.phase.val = 5 := by
        by_contra hn
        have hu := hm.2
        have hh : max r.phase.val m.phase.val ≤ 4 := max_le (by omega) (by omega)
        omega
      exact Or.inr ⟨hlt, hmp, he⟩
  · rintro ⟨hrole, h | h⟩
    · have hmax : max r.phase.val m.phase.val = 5 := by
        simp only [h.1, max_eq_left hm.2]
      exact (fresh_accept_left r m hr hm hrole (Or.inr h.2.1) hmax).mpr h.2.2
    · have hmax : max r.phase.val m.phase.val = 5 := by
        simp only [h.2.1, max_eq_right hr.2]
      exact (fresh_accept_left r m hr hm hrole (Or.inl h.1) hmax).mpr h.2.2

theorem transition_accept_right (m r : AgentState L K)
    (hm : Window m) (hr : Window r) :
    Accepted r (Transition L K m r).2 ↔
      r.role = .reserve ∧
        ((r.phase.val = 5 ∧ r.hour.val = L ∧ Eligible m) ∨
          (r.phase.val < 5 ∧ m.phase.val = 5 ∧ Eligible m)) := by
  constructor
  · intro h
    have hmax := accepted_max_right m r hm hr h
    have he := (fresh_accept_right m r hm hr h.1 h.2.1 hmax).mp h
    refine ⟨h.1, ?_⟩
    by_cases hp : r.phase.val = 5
    · have hh : r.hour.val = L := by
        rcases h.2.1 with hh | hh
        · omega
        · exact hh
      exact Or.inl ⟨hp, hh, he⟩
    · have hlt : r.phase.val < 5 := by have hu := hr.2; omega
      have hmp : m.phase.val = 5 := by
        by_contra hn
        have hu := hm.2
        have hh : max m.phase.val r.phase.val ≤ 4 := max_le (by omega) (by omega)
        omega
      exact Or.inr ⟨hlt, hmp, he⟩
  · rintro ⟨hrole, h | h⟩
    · have hmax : max m.phase.val r.phase.val = 5 := by
        simp only [h.1, max_eq_right hm.2]
      exact (fresh_accept_right m r hm hr hrole (Or.inr h.2.1) hmax).mpr h.2.2
    · have hmax : max m.phase.val r.phase.val = 5 := by
        simp only [h.2.1, max_eq_left hr.2]
      exact (fresh_accept_right m r hm hr hrole (Or.inl h.1) hmax).mpr h.2.2

def ReadyReserve (a : AgentState L K) : Prop :=
  a.role = .reserve ∧ a.phase.val = 5 ∧ a.hour.val = L

def DormantReserve (a : AgentState L K) : Prop :=
  a.role = .reserve ∧ a.phase.val < 5

def FrozenEligible (a : AgentState L K) : Prop :=
  Eligible a ∧ 4 ≤ a.phase.val

private theorem rectangles_iff (r m : AgentState L K)
    (hcanonical : Eligible m → 4 ≤ m.phase.val → m.phase.val = 5) :
    (r.role = .reserve ∧
      ((r.phase.val = 5 ∧ r.hour.val = L ∧ Eligible m) ∨
        (r.phase.val < 5 ∧ m.phase.val = 5 ∧ Eligible m))) ↔
      ((ReadyReserve r ∧ Eligible m) ∨
        (DormantReserve r ∧ FrozenEligible m)) := by
  constructor
  · rintro ⟨hr, h | h⟩
    · exact Or.inl ⟨⟨hr, h.1, h.2.1⟩, h.2.2⟩
    · refine Or.inr ⟨⟨hr, h.1⟩, h.2.2, ?_⟩
      rw [h.2.1]
      decide
  · rintro (⟨hr, he⟩ | ⟨hr, he⟩)
    · exact ⟨hr.1, Or.inl ⟨hr.2.1, hr.2.2, he⟩⟩
    · exact ⟨hr.1, Or.inr ⟨hr.2, hcanonical he.1 he.2, he.1⟩⟩

theorem transition_accept_rectangles_left (r m : AgentState L K)
    (hr : Window r) (hm : Window m)
    (hcanonical : Eligible m → 4 ≤ m.phase.val → m.phase.val = 5) :
    Accepted r (Transition L K r m).1 ↔
      ((ReadyReserve r ∧ Eligible m) ∨
        (DormantReserve r ∧ FrozenEligible m)) :=
  (transition_accept_left r m hr hm).trans (rectangles_iff r m hcanonical)

theorem transition_accept_rectangles_right (m r : AgentState L K)
    (hm : Window m) (hr : Window r)
    (hcanonical : Eligible m → 4 ≤ m.phase.val → m.phase.val = 5) :
    Accepted r (Transition L K m r).2 ↔
      ((ReadyReserve r ∧ Eligible m) ∨
        (DormantReserve r ∧ FrozenEligible m)) :=
  (transition_accept_right m r hm hr).trans (rectangles_iff r m hcanonical)

theorem transition_accepted_index_left (r m : AgentState L K)
    (hr : Window r) (hm : Window m)
    (hacc : Accepted r (Transition L K r m).1) :
    (Transition L K r m).1.hour = exponentOf L m.bias := by
  have hmax := accepted_max_left r m hr hm hacc
  have he := (fresh_accept_left r m hr hm hacc.1 hacc.2.1 hmax).mp hacc
  rcases he with ⟨hmr, σ, j, hbi, _⟩
  let a := liftTo r (⟨5, by decide⟩ : Fin 11)
  let b := liftTo m (⟨5, by decide⟩ : Fin 11)
  have ha := liftTo_fields r (⟨5, by decide⟩ : Fin 11) hr.1 (by decide)
  have hb := liftTo_fields m (⟨5, by decide⟩ : Fin 11) hm.1 (by decide)
  have har : a.role = .reserve := ha.1.trans hacc.1
  have hbr : b.role = .main := hb.1.trans hmr
  have hbb : b.bias ≠ .zero := by
    rw [hb.2.1, hbi]
    simp
  have hah : a.hour.val = L := fresh_lift_hour r hr hacc.1 hacc.2.1
  rw [transition_max_five r m hr hm hmax]
  change (Phase5Transition L K a b).1.hour = exponentOf L m.bias
  rw [local_reserve_hour_left a b har hah, if_pos ⟨hbr, hbb⟩, hb.2.1]

theorem transition_accepted_index_right (m r : AgentState L K)
    (hm : Window m) (hr : Window r)
    (hacc : Accepted r (Transition L K m r).2) :
    (Transition L K m r).2.hour = exponentOf L m.bias := by
  have hmax := accepted_max_right m r hm hr hacc
  have he := (fresh_accept_right m r hm hr hacc.1 hacc.2.1 hmax).mp hacc
  rcases he with ⟨hmr, σ, j, hbi, _⟩
  let a := liftTo m (⟨5, by decide⟩ : Fin 11)
  let b := liftTo r (⟨5, by decide⟩ : Fin 11)
  have ha := liftTo_fields m (⟨5, by decide⟩ : Fin 11) hm.1 (by decide)
  have hb := liftTo_fields r (⟨5, by decide⟩ : Fin 11) hr.1 (by decide)
  have har : a.role = .main := ha.1.trans hmr
  have hbr : b.role = .reserve := hb.1.trans hacc.1
  have hab : a.bias ≠ .zero := by
    rw [ha.2.1, hbi]
    simp
  have hbh : b.hour.val = L := fresh_lift_hour r hr hacc.1 hacc.2.1
  rw [transition_max_five m r hm hr hmax]
  change (Phase5Transition L K a b).2.hour = exponentOf L m.bias
  rw [local_reserve_hour_right a b hbr hbh, if_pos ⟨har, hab⟩, ha.2.1]

theorem transition_sentinel_invisible_left (r m : AgentState L K)
    (hr : Window r) (hm : Window m) (σ : Sign)
    (hb : m.bias = .dyadic σ (sampleUnset : Fin (L + 1))) :
    ¬ Accepted r (Transition L K r m).1 := by
  have hnot : ¬ Eligible m := by simp [Eligible, hb, sampleUnset]
  intro h
  obtain ⟨_, hrect⟩ := (transition_accept_left r m hr hm).mp h
  rcases hrect with hrect | hrect <;> exact hnot hrect.2.2

theorem transition_sentinel_invisible_right (m r : AgentState L K)
    (hm : Window m) (hr : Window r) (σ : Sign)
    (hb : m.bias = .dyadic σ (sampleUnset : Fin (L + 1))) :
    ¬ Accepted r (Transition L K m r).2 := by
  have hnot : ¬ Eligible m := by simp [Eligible, hb, sampleUnset]
  intro h
  obtain ⟨_, hrect⟩ := (transition_accept_right m r hm hr).mp h
  rcases hrect with hrect | hrect <;> exact hnot hrect.2.2

end LateF6Acceptance
end Ripple.PopulationProtocol.ExactMajority
