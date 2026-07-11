/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ranking expected-time bound (re-export wrapper)

This file imports the monolithic `Time.lean` and re-exports the ranking
subphase expected-time bound so that split files (`RecoveryBound`,
`PhaseProofs`) can use them without tracing the full 10K-line dependency
chain.

Key theorems re-exported:
- `PEM_FreshRankingStart_expected_until_rankingEndpoint_or_heap_exit_le`
- `PEM_FreshRankingStart_expected_until_srank_timer2_or_consensus_or_heap_exit_le`
- `PEM_heapPrefix_expected_until_rankingEndpoint_or_exit_from_level_le`
-/

import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time

/-! The import above brings all ranking-bound theorems into scope.
    No additional declarations needed — downstream files import this
    module to access them. -/
