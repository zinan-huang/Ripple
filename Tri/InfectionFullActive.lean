/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionHandoff
import Tri.Rung
import Tri.Ladder

/-!
# Full-time handoff after complete activation

Once no inactive molecule remains, the infection state kernel stays on that
closed face. Its active-`X` coordinate is not merely a one-step projection:
the complete deterministic-time iterate is exactly ordinary Tri.
-/

namespace Tri

open scoped ENNReal

instance InfectionCfg.allActiveDecidable (s : InfectionCfg) :
    Decidable s.AllActive := by
  unfold InfectionCfg.AllActive
  infer_instance

instance infectionXConsensusDecidable {n : ℕ}
    (s : InfectionState n) :
    Decidable (InfectionXConsensus s) := by
  unfold InfectionXConsensus
  infer_instance

/-- Reaching the population upper bound for the active count forces complete
activation. -/
theorem InfectionState.allActive_of_total_le_active
    {n : ℕ} (s : InfectionState n) (h : n ≤ s.1.active) :
    s.1.AllActive := by
  rcases s with ⟨⟨ax, ay, ix, iy⟩, hinv⟩
  simp only [InfectionCfg.Inv, InfectionCfg.total, InfectionCfg.active,
    InfectionCfg.inactive] at hinv h
  unfold InfectionCfg.AllActive
  change ix = 0 ∧ iy = 0
  omega

/-- Every semantic event preserves the completely active face. Impossible
activation events are already sent back to the source state by `nextState`. -/
theorem InfectionEvent.nextState_allActive
    {n : ℕ} (s : InfectionState n) (e : InfectionEvent)
    (hs : s.1.AllActive) :
    (InfectionEvent.nextState s e).1.AllActive := by
  unfold InfectionEvent.nextState
  split_ifs
  · exact hs
  · rcases hs with ⟨hix, hiy⟩
    unfold InfectionCfg.AllActive
    cases e <;> simp [InfectionEvent.next, hix, hiy]

/-- Infection states restricted to the closed fully active face. -/
abbrev ActiveInfectionState (n : ℕ) :=
  {s : InfectionState n // s.1.AllActive}

/-- The infection kernel restricted to the fully active face. -/
noncomputable def activeInfectionStep
    (n : ℕ) (h3 : 3 ≤ n)
    (s : ActiveInfectionState n) :
    PMF (ActiveInfectionState n) :=
  (infectionEventPMF s.1.1 (by
    have hinv := s.1.2
    simp only [InfectionCfg.Inv] at hinv
    omega)).map
      (fun e =>
        ⟨InfectionEvent.nextState s.1 e,
          InfectionEvent.nextState_allActive s.1 e s.2⟩)

/-- Forgetting the face proof recovers the original infection step. -/
theorem activeInfectionStep_map_val
    (n : ℕ) (h3 : 3 ≤ n) (s : ActiveInfectionState n) :
    (activeInfectionStep n h3 s).map Subtype.val =
      infectionStateStep n h3 s.1 := by
  unfold activeInfectionStep infectionStateStep
  rw [PMF.map_comp]
  rfl

/-- On a fully active state, the one-step active-`X` marginal is `triChain`. -/
theorem infectionStateStep_map_ax_eq_triChain
    (n : ℕ) (h3 : 3 ≤ n) (s : InfectionState n)
    (hs : s.1.AllActive) :
    (infectionStateStep n h3 s).map (fun z => z.1.ax) =
      triChain n s.1.ax := by
  rw [infectionStateStep_map_ax_allActive n h3 s hs]
  unfold triChain
  have hinv := s.2
  rcases hs with ⟨hix, hiy⟩
  simp only [InfectionCfg.Inv, InfectionCfg.total, InfectionCfg.active,
    InfectionCfg.inactive] at hinv
  rw [dif_pos ⟨h3, by omega⟩]
  congr 1
  omega

/-- The restricted kernel projects pointwise to ordinary Tri. -/
theorem activeInfectionStep_map_ax
    (n : ℕ) (h3 : 3 ≤ n) (s : ActiveInfectionState n) :
    (activeInfectionStep n h3 s).map (fun z => z.1.1.ax) =
      triChain n s.1.1.ax := by
  calc
    (activeInfectionStep n h3 s).map (fun z => z.1.1.ax) =
        ((activeInfectionStep n h3 s).map Subtype.val).map
          (fun z => z.1.ax) := by
            rw [PMF.map_comp]
            congr 1
    _ = (infectionStateStep n h3 s.1).map
          (fun z => z.1.ax) := by
            rw [activeInfectionStep_map_val]
    _ = triChain n s.1.1.ax :=
      infectionStateStep_map_ax_eq_triChain n h3 s.1 s.2

/-- Every finite iterate of the restricted kernel projects exactly to the
ordinary Tri iterate. -/
theorem iter_activeInfectionStep_map_ax
    (n : ℕ) (h3 : 3 ≤ n) (T : ℕ)
    (s : ActiveInfectionState n) :
    (iter (activeInfectionStep n h3) T s).map
        (fun z => z.1.1.ax) =
      iter (triChain n) T s.1.1.ax :=
  iter_map_of_step_map
    (activeInfectionStep n h3) (triChain n)
    (fun z => z.1.1.ax)
    (activeInfectionStep_map_ax n h3) T s

/-- The unrestricted infection iterate started on the fully active face is the
pushforward of the restricted iterate. -/
theorem iter_activeInfectionStep_map_val
    (n : ℕ) (h3 : 3 ≤ n) (T : ℕ)
    (s : ActiveInfectionState n) :
    (iter (activeInfectionStep n h3) T s).map Subtype.val =
      iter (infectionStateStep n h3) T s.1 :=
  iter_map_of_step_map
    (activeInfectionStep n h3) (infectionStateStep n h3)
    Subtype.val (activeInfectionStep_map_val n h3) T s

/-- Full-time version of the handoff: the original infection chain, when
started fully active, has exactly the ordinary-Tri active-`X` marginal. -/
theorem iter_infectionStateStep_map_ax_allActive
    (n : ℕ) (h3 : 3 ≤ n) (T : ℕ)
    (s : InfectionState n) (hs : s.1.AllActive) :
    (iter (infectionStateStep n h3) T s).map
        (fun z => z.1.ax) =
      iter (triChain n) T s.1.ax := by
  let q : ActiveInfectionState n := ⟨s, hs⟩
  calc
    (iter (infectionStateStep n h3) T s).map (fun z => z.1.ax) =
        ((iter (activeInfectionStep n h3) T q).map Subtype.val).map
          (fun z => z.1.ax) := by
            rw [iter_activeInfectionStep_map_val]
    _ = (iter (activeInfectionStep n h3) T q).map
          (fun z => z.1.1.ax) := by
            rw [PMF.map_comp]
            congr 1
    _ = iter (triChain n) T s.1.ax :=
      iter_activeInfectionStep_map_ax n h3 T q

/-- Masking a pushforward by a predicate is the same as masking the source by
the pulled-back predicate. -/
theorem masked_map_eq
    {α β : Type*} (p : PMF α) (f : α → β)
    (Q : β → Prop) [DecidablePred Q] :
    (∑' a, if Q (f a) then 0 else p a) =
      ∑' b, if Q b then 0 else (p.map f) b := by
  calc
    (∑' a, if Q (f a) then 0 else p a) =
        expect p (fun a => if Q (f a) then 0 else 1) := by
          unfold expect
          apply tsum_congr
          intro a
          by_cases ha : Q (f a) <;> simp [ha]
    _ = expect (p.map f) (fun b => if Q b then 0 else 1) := by
          rw [expect_map]
    _ = ∑' b, if Q b then 0 else (p.map f) b := by
          unfold expect
          apply tsum_congr
          intro b
          by_cases hb : Q b <;> simp [hb]

/-- Every ordinary-Tri finite-horizon reachability theorem transfers unchanged
to the infection chain after complete activation. -/
theorem infectionReaches_of_triReaches
    (n : ℕ) (h3 : 3 ≤ n)
    {T : ℕ} {P Q : ℕ → Prop} [DecidablePred Q]
    {ε : ℝ≥0∞}
    (htri : Reaches (triChain n) T P Q ε) :
    Reaches (infectionStateStep n h3) T
      (fun s : InfectionState n => s.1.AllActive ∧ P s.1.ax)
      (fun s => Q s.1.ax) ε := by
  intro s hs
  rw [masked_map_eq
    (iter (infectionStateStep n h3) T s)
    (fun z => z.1.ax) Q]
  rw [iter_infectionStateStep_map_ax_allActive n h3 T s hs.1]
  exact htri s.1.ax hs.2

/-- Strengthened transfer retaining the fact that every terminal infection
state remains on the fully active face. -/
theorem infectionReaches_fullFace_of_triReaches
    (n : ℕ) (h3 : 3 ≤ n)
    {T : ℕ} {P Q : ℕ → Prop} [DecidablePred Q]
    {ε : ℝ≥0∞}
    (htri : Reaches (triChain n) T P Q ε) :
    Reaches (infectionStateStep n h3) T
      (fun s : InfectionState n => s.1.AllActive ∧ P s.1.ax)
      (fun s => s.1.AllActive ∧ Q s.1.ax) ε := by
  intro s hs
  let q : ActiveInfectionState n := ⟨s, hs.1⟩
  let p := iter (activeInfectionStep n h3) T q
  calc
    (∑' z, if z.1.AllActive ∧ Q z.1.ax then 0
        else iter (infectionStateStep n h3) T s z) =
        ∑' z, if z.1.AllActive ∧ Q z.1.ax then 0
          else (p.map Subtype.val) z := by
            rw [iter_activeInfectionStep_map_val n h3 T q]
    _ = ∑' a, if a.1.1.AllActive ∧ Q a.1.1.ax then 0
          else p a := by
            exact (masked_map_eq p Subtype.val
              (fun z : InfectionState n =>
                z.1.AllActive ∧ Q z.1.ax)).symm
    _ = ∑' a, if Q a.1.1.ax then 0 else p a := by
          apply tsum_congr
          intro a
          simp [a.2]
    _ = ∑' x, if Q x then 0
          else (p.map (fun a => a.1.1.ax)) x :=
            masked_map_eq p (fun a => a.1.1.ax) Q
    _ = ∑' x, if Q x then 0
          else iter (triChain n) T s.1.ax x := by
            rw [iter_activeInfectionStep_map_ax n h3 T q]
    _ ≤ ε := htri s.1.ax hs.2

/-- On the invariant state space, full activation plus `ax ≥ n` is exactly
all-`X` infection consensus. -/
theorem infectionXConsensus_iff_allActive_ax
    {n : ℕ} (s : InfectionState n) :
    InfectionXConsensus s ↔
      s.1.AllActive ∧ n ≤ s.1.ax := by
  constructor
  · intro hs
    rcases hs with ⟨hax, hay, hix, hiy⟩
    exact ⟨⟨hix, hiy⟩, by omega⟩
  · rintro ⟨⟨hix, hiy⟩, hax⟩
    have hinv := s.2
    simp only [InfectionCfg.Inv, InfectionCfg.total, InfectionCfg.active,
      InfectionCfg.inactive] at hinv
    unfold InfectionXConsensus
    omega

/-- Ordinary-Tri convergence to its top state transfers to all-`X` infection
consensus after complete activation. -/
theorem infectionReaches_consensus_of_triReaches
    (n : ℕ) (h3 : 3 ≤ n)
    {T : ℕ} {P : ℕ → Prop} {ε : ℝ≥0∞}
    (htri :
      Reaches (triChain n) T P (fun x => n ≤ x) ε) :
    Reaches (infectionStateStep n h3) T
      (fun s : InfectionState n => s.1.AllActive ∧ P s.1.ax)
      InfectionXConsensus ε := by
  have h :=
    infectionReaches_fullFace_of_triReaches n h3 htri
  exact h.mono_post fun s hs =>
    (infectionXConsensus_iff_allActive_ax s).2 hs

/-- Deterministic composition interface for the Theorem 6 headline. The
remaining reveal analysis must provide exactly the joint activation checkpoint
used by `hactivate`; all later dynamics and error accounting are discharged
here. -/
theorem infectionActivation_then_tri_consensus
    (n : ℕ) (h3 : 3 ≤ n)
    {Tactivate Ttri : ℕ}
    {A : InfectionState n → Prop} {P : ℕ → Prop}
    [DecidablePred A] [DecidablePred P]
    {εactivate εtri : ℝ≥0∞}
    (hactivate :
      Reaches (infectionStateStep n h3) Tactivate A
        (fun s => n ≤ s.1.active ∧ P s.1.ax) εactivate)
    (htri :
      Reaches (triChain n) Ttri P (fun x => n ≤ x) εtri) :
    Reaches (infectionStateStep n h3) (Tactivate + Ttri)
      A InfectionXConsensus (εactivate + εtri) := by
  have hactivate' :
      Reaches (infectionStateStep n h3) Tactivate A
        (fun s => s.1.AllActive ∧ P s.1.ax) εactivate :=
    hactivate.mono_post fun s hs =>
      ⟨InfectionState.allActive_of_total_le_active s hs.1, hs.2⟩
  exact hactivate'.comp
    (infectionReaches_consensus_of_triReaches n h3 htri)

end Tri

#print axioms Tri.InfectionState.allActive_of_total_le_active
#print axioms Tri.InfectionEvent.nextState_allActive
#print axioms Tri.iter_infectionStateStep_map_ax_allActive
#print axioms Tri.infectionReaches_of_triReaches
#print axioms Tri.infectionReaches_fullFace_of_triReaches
#print axioms Tri.infectionActivation_then_tri_consensus
