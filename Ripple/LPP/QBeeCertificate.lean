/-
  QBee certificate for the gamma system.

  The QBee algorithm (Bychkov-Pogudin) quadratizes the 14-variable gamma GPAC
  into an 18-variable degree-2 system by introducing 4 new monomial variables:
    14: pv    = p * v       (= y 6 * y 4)
    15: en_g  = e_n * g     (= y 11 * y 1)
    16: en_f  = e_n * f     (= y 11 * y 0)
    17: en_pv = e_n * p * v (= y 11 * y 6 * y 4)

  This file verifies the certificate by proving (via `ring`) that the
  quadratized ODEs for the new variables are consistent with the chain rule
  applied to the original gamma field. This replaces `native_decide`.

  Variable index:
    0:f  1:g  2:w  3:u  4:v  5:r  6:p  7:q
    8:e  9:Esym  10:e_1  11:e_n  12:ginv  13:gam
    14:pv  15:en_g  16:en_f  17:en_pv
-/

import Ripple.Core.PIVP
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option linter.unusedSimpArgs false

namespace Ripple.LPP.QBee

/-- The original 14-variable gamma GPAC field. -/
noncomputable def gammaField (y : Fin 14 → ℝ) : Fin 14 → ℝ :=
  ![y 2,                                          -- f' = w
    y 6 * y 7 * y 4,                              -- g' = p*q*v
    -(y 2) + y 3 + y 4,                           -- w' = -w + u + v
    -(y 3) + y 5 * y 4,                            -- u' = -u + r*v
    -(y 4),                                        -- v' = -v
    -(y 5 * y 5),                                  -- r' = -r²
    y 6 * y 4,                                     -- p' = p*v
    y 4 - y 7,                                     -- q' = v - q
    1 - y 8,                                       -- e' = 1 - e
    y 9 * y 8 - y 9 - y 8 + 1,                    -- Esym' = Esym*e - Esym - e + 1
    y 9 * y 10 - y 10 + 1,                         -- e_1' = Esym*e_1 - e_1 + 1
    -(y 10 * y 11) + 1,                            -- e_n' = -e_1*e_n + 1
    -(y 12 * y 11 * y 1) + y 12 * y 11 * y 0
      - y 12 + 1,                                  -- ginv' = ginv*en*(f-g) - ginv + 1
    -(y 13 * y 12) + 1]                            -- gam' = -gam*ginv + 1

/-- The 18-variable QBee-quadratized gamma field (degree ≤ 2). -/
noncomputable def gammaQuadField (y : Fin 18 → ℝ) : Fin 18 → ℝ :=
  ![y 2,                                          -- f' = w
    y 7 * y 14,                                    -- g' = q * pv
    -(y 2) + y 3 + y 4,                            -- w' = -w + u + v
    -(y 3) + y 5 * y 4,                            -- u' = -u + r*v
    -(y 4),                                        -- v' = -v
    -(y 5 * y 5),                                  -- r' = -r²
    y 14,                                          -- p' = pv
    y 4 - y 7,                                     -- q' = v - q
    1 - y 8,                                       -- e' = 1 - e
    y 9 * y 8 - y 9 - y 8 + 1,                    -- Esym' = Esym*e - Esym - e + 1
    y 9 * y 10 - y 10 + 1,                         -- e_1' = Esym*e_1 - e_1 + 1
    -(y 10 * y 11) + 1,                            -- e_n' = -e_1*e_n + 1
    -(y 12 * y 15) + y 12 * y 16 - y 12 + 1,      -- ginv' = -ginv*en_g + ginv*en_f - ginv + 1
    -(y 13 * y 12) + 1,                            -- gam' = -gam*ginv + 1
    y 4 * y 14 - y 14,                             -- pv' = v*pv - pv
    -(y 10 * y 15) + y 1 + y 7 * y 17,            -- en_g' = -e_1*en_g + g + q*en_pv
    -(y 10 * y 16) + y 11 * y 2 + y 0,            -- en_f' = -e_1*en_f + e_n*w + f
    -(y 10 * y 17) + y 4 * y 17 + y 14 - y 17]    -- en_pv' = -e_1*en_pv + v*en_pv + pv - en_pv

/-- The monomial substitution: embeds the 14-variable state into
the 18-variable state by computing the QBee new variables. -/
noncomputable def qbeeEmbed (x : Fin 14 → ℝ) : Fin 18 → ℝ :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7,
    x 8, x 9, x 10, x 11, x 12, x 13,
    x 6 * x 4,           -- pv = p * v
    x 11 * x 1,          -- en_g = e_n * g
    x 11 * x 0,          -- en_f = e_n * f
    x 11 * x 6 * x 4]    -- en_pv = e_n * p * v

set_option maxHeartbeats 800000 in
/-- **QBee correctness certificate (original components).**
The first 14 components of the quadratized field, evaluated on the
monomial manifold, equal the original gamma field. -/
theorem qbee_original_components_correct (x : Fin 14 → ℝ) (i : Fin 14) :
    gammaQuadField (qbeeEmbed x) (Fin.castLE (by omega) i) = gammaField x i := by
  fin_cases i <;> simp [gammaQuadField, gammaField, qbeeEmbed, Fin.castLE,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-- **QBee correctness certificate (new variable: pv = p*v).**
The chain rule derivative d/dt[p*v] using the original field
equals the QBee-assigned pv' evaluated on the monomial manifold. -/
theorem qbee_pv_chain_rule (x : Fin 14 → ℝ) :
    -- d/dt[p*v] = p'*v + p*v' = (p*v)*v + p*(-v) = p*v*(v-1)
    -- QBee says: pv' = v*pv - pv, on manifold = v*(p*v) - (p*v) = p*v*(v-1) ✓
    gammaQuadField (qbeeEmbed x) 14 =
      gammaField x 6 * x 4 + x 6 * gammaField x 4 := by
  simp [gammaQuadField, gammaField, qbeeEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_cons]; ring

/-- **QBee correctness certificate (new variable: en_g = e_n*g).**
Chain rule: d/dt[e_n*g] = e_n'*g + e_n*g' -/
theorem qbee_en_g_chain_rule (x : Fin 14 → ℝ) :
    gammaQuadField (qbeeEmbed x) 15 =
      gammaField x 11 * x 1 + x 11 * gammaField x 1 := by
  simp [gammaQuadField, gammaField, qbeeEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_cons]; ring

/-- **QBee correctness certificate (new variable: en_f = e_n*f).**
Chain rule: d/dt[e_n*f] = e_n'*f + e_n*f' -/
theorem qbee_en_f_chain_rule (x : Fin 14 → ℝ) :
    gammaQuadField (qbeeEmbed x) 16 =
      gammaField x 11 * x 0 + x 11 * gammaField x 0 := by
  simp [gammaQuadField, gammaField, qbeeEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_cons]; ring

/-- **QBee correctness certificate (new variable: en_pv = e_n*p*v).**
Chain rule: d/dt[e_n*p*v] = e_n'*p*v + e_n*p'*v + e_n*p*v' -/
theorem qbee_en_pv_chain_rule (x : Fin 14 → ℝ) :
    gammaQuadField (qbeeEmbed x) 17 =
      gammaField x 11 * (x 6 * x 4) + x 11 * gammaField x 6 * x 4
        + x 11 * x 6 * gammaField x 4 := by
  simp [gammaQuadField, gammaField, qbeeEmbed,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_cons]; ring

/-- If x solves the 14-variable gamma ODE, then qbeeEmbed(x) solves
the 18-variable quadratized ODE. This is the key wiring theorem
that connects QBee output to the pipeline. -/
theorem qbee_solution_lift {x : ℝ → Fin 14 → ℝ}
    (hx : ∀ t : ℝ, 0 ≤ t → HasDerivAt x (gammaField (x t)) t) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => qbeeEmbed (x s)) (gammaQuadField (qbeeEmbed (x t))) t := by
  intro t ht
  have hx_t := hx t ht
  have hcomp : ∀ i : Fin 14, HasDerivAt (fun s => x s i) (gammaField (x t) i) t :=
    fun i => hasDerivAt_pi.mp hx_t i
  -- Step 1: compute the actual derivative via chain/product rules
  set F := gammaField (x t)
  have h14 : HasDerivAt (fun s => x s 6 * x s 4)
      (F 6 * x t 4 + x t 6 * F 4) t :=
    (hcomp 6).mul (hcomp 4)
  have h15 : HasDerivAt (fun s => x s 11 * x s 1)
      (F 11 * x t 1 + x t 11 * F 1) t :=
    (hcomp 11).mul (hcomp 1)
  have h16 : HasDerivAt (fun s => x s 11 * x s 0)
      (F 11 * x t 0 + x t 11 * F 0) t :=
    (hcomp 11).mul (hcomp 0)
  have h17 : HasDerivAt (fun s => x s 11 * (x s 6 * x s 4))
      (F 11 * (x t 6 * x t 4) + x t 11 * (F 6 * x t 4 + x t 6 * F 4)) t :=
    (hcomp 11).mul h14
  -- Step 2: assemble the 18-component derivative
  set deriv : Fin 18 → ℝ :=
    ![F 0, F 1, F 2, F 3, F 4, F 5, F 6, F 7,
      F 8, F 9, F 10, F 11, F 12, F 13,
      F 6 * x t 4 + x t 6 * F 4,
      F 11 * x t 1 + x t 11 * F 1,
      F 11 * x t 0 + x t 11 * F 0,
      F 11 * (x t 6 * x t 4) + x t 11 * (F 6 * x t 4 + x t 6 * F 4)]
  -- Step 3: show HasDerivAt for the embedded trajectory with this derivative
  have hderiv : HasDerivAt (fun s => qbeeEmbed (x s)) deriv t := by
    rw [show (fun s => qbeeEmbed (x s)) = (fun s =>
      ![x s 0, x s 1, x s 2, x s 3, x s 4, x s 5, x s 6, x s 7,
        x s 8, x s 9, x s 10, x s 11, x s 12, x s 13,
        x s 6 * x s 4, x s 11 * x s 1, x s 11 * x s 0,
        x s 11 * (x s 6 * x s 4)]) from by ext s; simp [qbeeEmbed]; ring]
    exact hasDerivAt_pi.mpr (fun i => by
      fin_cases i <;> simp [deriv, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons] <;>
      first
        | exact hcomp _
        | exact h14
        | exact h15
        | exact h16
        | exact h17)
  -- Step 4: show deriv = gammaQuadField (qbeeEmbed (x t)) by the certificates
  convert hderiv using 1
  ext i; fin_cases i <;> simp [deriv, gammaQuadField, gammaField, qbeeEmbed, F,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

end Ripple.LPP.QBee
