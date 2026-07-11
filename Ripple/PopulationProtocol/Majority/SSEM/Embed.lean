/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Execution Embedding Lemma

Core infrastructure for the impossibility proof (Theorem 1).

If e : Fin m → Fin n is injective, initial configs agree on e's image,
and schedulers correspond via e, then the execution on m agents matches
the execution on n agents restricted through e.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Execution
import Mathlib.Logic.Function.Basic

namespace SSEM

variable {Q X Y : Type*} {m n : ℕ}

/-! ## Input preservation -/

theorem Config.step_snd (P : Protocol Q X Y) (C : Config Q X n)
    (u v w : Fin n) : (C.step P u v w).2 = (C w).2 := by
  unfold Config.step
  by_cases huv : u = v
  · simp [huv]
  · simp only [if_neg huv]
    split
    · rename_i h; subst h; rfl
    · split
      · rename_i _ h; subst h; rfl
      · rfl

theorem execution_input_preserved (P : Protocol Q X Y) (C₀ : Config Q X n)
    (γ : DetScheduler n) (t : ℕ) (v : Fin n) :
    (execution P C₀ γ t v).2 = (C₀ v).2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [execution]
    rw [Config.step_snd]
    exact ih

theorem Config.agentsWithInput_execution [DecidableEq X]
    (P : Protocol Q X Y) (C₀ : Config Q X n)
    (γ : DetScheduler n) (t : ℕ) (x : X) :
    (execution P C₀ γ t).agentsWithInput x = C₀.agentsWithInput x := by
  ext v
  simp only [Config.agentsWithInput, Finset.mem_filter, Finset.mem_univ, true_and,
    Config.inputOf]
  constructor
  · intro h; rwa [execution_input_preserved] at h
  · intro h; rwa [execution_input_preserved]

/-! ## Step commutes with embedding -/

theorem Config.step_embed (P : Protocol Q X Y) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (C' : Config Q X m) (C : Config Q X n)
    (hAgree : ∀ j, C' j = C (e j))
    (u v : Fin m) (i : Fin m) :
    (C'.step P u v) i = (C.step P (e u) (e v)) (e i) := by
  unfold Config.step
  by_cases huv : u = v
  · subst huv; simp; exact hAgree i
  · have hne_euv : e u ≠ e v := fun h => huv (he h)
    simp only [if_neg huv, if_neg hne_euv]
    by_cases hiu : i = u
    · subst hiu
      simp only [ite_true]
      rw [hAgree i, hAgree v]
    · have hne_eu : e i ≠ e u := fun h => hiu (he h)
      simp only [hiu, ↓reduceIte, hne_eu]
      by_cases hiv : i = v
      · subst hiv
        simp only [ite_true]
        rw [hAgree u, hAgree i]
      · have hne_ev : e i ≠ e v := fun h => hiv (he h)
        simp only [hiv, ↓reduceIte, hne_ev]
        exact hAgree i

/-! ## Execution embedding (matching lemma) -/

theorem execution_embed (P : Protocol Q X Y) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (C' : Config Q X m) (C : Config Q X n)
    (hInit : ∀ i, C' i = C (e i))
    (γ' : DetScheduler m) (γ : DetScheduler n)
    (hSched : ∀ t, γ t = (e (γ' t).1, e (γ' t).2)) :
    ∀ t i, (execution P C' γ' t) i = (execution P C γ t) (e i) := by
  intro t
  induction t with
  | zero => exact hInit
  | succ t ih =>
    intro i
    simp only [execution]
    have hs := hSched t
    conv_rhs => rw [show (γ t).1 = e (γ' t).1 from by rw [hs],
                     show (γ t).2 = e (γ' t).2 from by rw [hs]]
    exact Config.step_embed P e he _ _ ih (γ' t).1 (γ' t).2 i

/-! ## Output corollary -/

theorem execution_embed_output (P : Protocol Q X Y) (e : Fin m → Fin n)
    (he : Function.Injective e)
    (C' : Config Q X m) (C : Config Q X n)
    (hInit : ∀ i, C' i = C (e i))
    (γ' : DetScheduler m) (γ : DetScheduler n)
    (hSched : ∀ t, γ t = (e (γ' t).1, e (γ' t).2))
    (t : ℕ) (i : Fin m) :
    (execution P C' γ' t).outputOf P i =
    (execution P C γ t).outputOf P (e i) := by
  simp only [Config.outputOf]
  rw [execution_embed P e he C' C hInit γ' γ hSched t i]

end SSEM
