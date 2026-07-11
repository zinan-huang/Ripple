-- Ripple: A Lean 4 Framework for CRN Computable Numbers
--
-- Formalizes the theory of chemical reaction network computable numbers
-- from the following papers:
--   [RTCRN1] Real-time computability of real numbers by CRNs (Nat. Comput. 2018)
--   [RTCRN2] Real-time equivalence of CRNs and analog computers (DNA 25, 2019)
--   [LPP]    Computing real numbers with large-population protocols (DNA 28, 2022)
--   [BAC]    Bounded analog complexity (DNA 32, 2026)
--
-- The goal: given a target number α, semi-automatically construct a
-- Lean proof that α is CRN-computable at a given time complexity.

import Ripple.Core.PIVP
import Ripple.Core.BoundedTime
import Ripple.Core.Compilation
import Ripple.Core.CRNPipeline
import Ripple.Core.ODEGlobal
import Ripple.Core.ZeroInitPositivity
import Ripple.Core.InitShift
import Ripple.ODE.ScalarBarrier
import Ripple.DualRail.ConstantAnnihilation
import Ripple.DualRail.ConstantAnnihilationGeneral
import Ripple.DualRail.ExpMajorization
import Ripple.DualRail.BTCReduction
import Ripple.DualRail.ScalarCubic
import Ripple.DualRail.ScalarQuintic
import Ripple.DualRail.SubtractionGadget
import Ripple.Number.Apery
import Ripple.Number.AperySequences
import Ripple.Number.PiCertified
import Ripple.Number.Ln2Certified
import Ripple.Number.InvECertified
import Ripple.Number.CatalanCertified
import Ripple.Number.Modular.ModularPolynomialQExpansion
import Ripple.Number.Modular.CosetIndex
import Ripple.Number.Modular.SturmBound
import Ripple.Number.Modular.SturmBoundIndex
import Ripple.Number.Modular.LevelOneSturm
import Ripple.Number.Modular.HigherOrderDecay
import Ripple.Number.Modular.LevelOneSturmGeneric
import Ripple.Number.Modular.Phi41Bridge
import Ripple.Number.Modular.Phi41ModularFormAssembly
import Ripple.Number.Modular.Gamma0_41_SturmBound
import Ripple.LPP
import Ripple.Kurtz.Defs
import Ripple.Kurtz.IntegralGronwall
import Ripple.Kurtz.MeanField
import Ripple.Kurtz.PopulationProtocol
import Ripple.PopulationProtocol.Majority
import Ripple.CTMC.DTMC
import Ripple.CTMC.CTMC
import Ripple.CTMC.CTMCProcess
import Ripple.CTMC.CanonicalLaw
import Ripple.CTMC.DensityDependent
import Ripple.CTMC.RandomIndexDoob
import Ripple.CTMC.TwoState
