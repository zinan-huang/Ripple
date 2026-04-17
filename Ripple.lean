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
import Ripple.Number.Apery
import Ripple.LPP
