/-
Ripple.BoundedUniversality.Verified
---------------
Public theorem interface. Every theorem listed here is machine-checked.
Run `#print axioms <name>` to see the exact assumption footprint.

This file is the COMPLETE public index of the project's deliverables:
the headline positive result, the impossibility (robustness) dichotomy,
and the reusable GPAC components. Importing it forces every listed
result into the live compilation closure, so `#print axioms` covers
them all — no deliverable is an unwired orphan.
-/

import Ripple.BoundedUniversality.Routes
-- Headline positive results
import Ripple.BoundedUniversality.BGP.HeadlineFinalNW
import Ripple.BoundedUniversality.BGP.FaithfulHeadlineWire
-- Impossibility (robustness dichotomy)
import Ripple.BoundedUniversality.GPAC.Impossibility
import Ripple.BoundedUniversality.GPAC.PerturbedOrbit
import Ripple.BoundedUniversality.BGP.AmplificationBarrier
-- Reusable GPAC components
import Ripple.BoundedUniversality.GPAC.RationalClock
import Ripple.BoundedUniversality.GPAC.BoundedRobustStep
import Ripple.BoundedUniversality.GPAC.IncrementerDemo
import Ripple.BoundedUniversality.GPAC.RationalRounding

-- ═══════════════════════════════════════════════════════
-- HEADLINE — Turing-complete rational bounded PIVP simulation
-- ═══════════════════════════════════════════════════════

-- Main result: a single rational PIVP eventually-threshold-simulates
-- an undecidable machine (unconditional, no custom axioms).
#check @Ripple.BoundedUniversality.BGP.bounded_pivp_turing_complete

-- Faithful-tube variant of the headline.
#check @Ripple.BoundedUniversality.BGP.bgp_headline_via_faithful_tube

-- ═══════════════════════════════════════════════════════
-- IMPOSSIBILITY — the robustness dichotomy (Paper 1/2 side)
-- ═══════════════════════════════════════════════════════

-- T1: no uniform robust encoder of an undecidable predicate.
#check @Ripple.BoundedUniversality.GPAC.Impossibility.no_uniform_robust_encoding

-- T2: packing — a compact region admits only finitely many
-- ε-separated robust codewords.
#check @Ripple.BoundedUniversality.GPAC.Impossibility.packing_finite

-- Amplification barrier: an arbitrary (non-algebraic) evaluator cannot
-- snap two overlapping configurations whose step-encodings diverge.
#check @Ripple.BoundedUniversality.BGP.no_poly_snap_if_step_amplifies

-- T3: perturbed-orbit — no robust simulation survives a gridifying
-- perturbation of the trajectory.
#check @Ripple.BoundedUniversality.GPAC.PerturbedOrbit.no_perturbed_robust_simulation

-- ═══════════════════════════════════════════════════════
-- GPAC COMPONENTS — reusable rational-encoding deliverables
-- ═══════════════════════════════════════════════════════

-- A nonconstant rational-coefficient periodic clock PIVP.
#check @Ripple.BoundedUniversality.GPAC.exists_rational_periodic_clock

-- A bounded rational robust step map (config-local, non-robust regime).
#check @Ripple.BoundedUniversality.GPAC.BoundedRobustStep.bounded_rational_robust_step

-- Robust-step incrementer demonstration.
#check @Ripple.BoundedUniversality.GPAC.IncrementerDemo.robust_step_incrementer

-- Finite-symbol rounding (rational rounder on a bounded alphabet).
#check @Ripple.BoundedUniversality.GPAC.RationalRounding.finite_symbol_rounder

-- ═══════════════════════════════════════════════════════
-- FULLY PROVED (no custom axioms)
-- ═══════════════════════════════════════════════════════

-- F4a: T1 rigidity ⇒ selected itineraries are periodic
#check @Ripple.BoundedUniversality.HenonSelector.T1_forces_selected_itineraries_periodic

-- F4b: T1 + nonperiodic requirement ⇒ no selector
#check @Ripple.BoundedUniversality.HenonSelector.T1_no_selector_if_nonperiodic_required

-- F1: ρ ↔ |t| ≤ 1 + √10
#check @Ripple.BoundedUniversality.HenonSelector.ρ_iff_abs_le

-- F1: D is Q-semialgebraic
#check @Ripple.BoundedUniversality.HenonSelector.D_isQSemialgebraicPair

-- ═══════════════════════════════════════════════════════
-- ROUTE 3 (no custom axioms in the public theorem footprint)
-- ═══════════════════════════════════════════════════════

-- Route 3 main theorem
#check @Ripple.BoundedUniversality.route3_statement

-- Route 3 gap theorem
#check @Ripple.BoundedUniversality.route3_gap

-- ═══════════════════════════════════════════════════════
-- AXIOM FOOTPRINT
-- ═══════════════════════════════════════════════════════

#print axioms Ripple.BoundedUniversality.BGP.bounded_pivp_turing_complete
#print axioms Ripple.BoundedUniversality.BGP.bgp_headline_via_faithful_tube
#print axioms Ripple.BoundedUniversality.GPAC.Impossibility.no_uniform_robust_encoding
#print axioms Ripple.BoundedUniversality.GPAC.Impossibility.packing_finite
#print axioms Ripple.BoundedUniversality.BGP.no_poly_snap_if_step_amplifies
#print axioms Ripple.BoundedUniversality.GPAC.PerturbedOrbit.no_perturbed_robust_simulation
#print axioms Ripple.BoundedUniversality.GPAC.exists_rational_periodic_clock
#print axioms Ripple.BoundedUniversality.GPAC.BoundedRobustStep.bounded_rational_robust_step
#print axioms Ripple.BoundedUniversality.GPAC.IncrementerDemo.robust_step_incrementer
#print axioms Ripple.BoundedUniversality.GPAC.RationalRounding.finite_symbol_rounder
#print axioms Ripple.BoundedUniversality.HenonSelector.T1_no_selector_if_nonperiodic_required
#print axioms Ripple.BoundedUniversality.HenonSelector.ρ_iff_abs_le
#print axioms Ripple.BoundedUniversality.route3_statement
#print axioms Ripple.BoundedUniversality.route3_gap
