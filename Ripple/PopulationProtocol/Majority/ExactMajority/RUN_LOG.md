# RUN_LOG — ExactMajority wiring campaign

## Run 2026-06-26 22:15
- doctrine version: this session (DOCTRINE.md rewritten for wiring)
- starting avenue: (a) field-by-field concrete instantiation
- tools: ChatGPT family1/2/3 (6+ rounds), Codex subagents (5 dispatched)
- end: ongoing
- status at 11 commits:
  - cleanup: 61 dead files deleted, barrel fixed, naming consolidated
  - Theorem31.lean: structured proof body with 6 private sorry sub-obligations
  - DrainCalibrationConcrete.lean: calibratedHorizon + qHat_calibrated_hpt (0 sorry)
  - SlotInputsFromRegime.lean: scaffold (20 sorry, per-slot residuals)
  - DISCOVERED: hNoOvershoot blanket-false blocker (Assembly'/FaithfulWorkSeamCore path)
  - DISCOVERED: Slot 4 hPostEq structural gap (Phase4Post advFinished branch)
  - hPostEq verified trivial for 8/10 slots (0,1,2,3,5,6,7,8,9)
  - Slot 4 requires code change to TerminalSeamTieResidual or Phase4Post

### Checkpoint 17 commits
- hPostGe + hPostEqOnReset: PROVED sorry-free (10 slots)
- hPreEq: per-slot cascade residual (only slot 5 trivial, rest need cascade facts from Invariants.lean)
- hEvent: per-seam drained-clock residual (hSeedStep_timed_of_drained exists for {0,1,5,6,7,8} but needs clockCounterSumAt=0)
- overshootResidual: seam_noOvershoot_tail_honest exists in SeamPairAdapter.lean
- Phase0: model mismatch identified (MCR coalescent → paper's Lemma 5.1)
- Phase3: no concrete Phase3ModeDomain constructor found
- DrainCalibrationConcrete: hpt proved for drain slots
- Slot 4 hPostEq: FIXED (hPostEqOnReset + hPostGe split)
