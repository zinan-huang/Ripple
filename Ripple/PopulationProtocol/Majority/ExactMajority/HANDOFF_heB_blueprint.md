# heB discharge blueprint (family2 letter, 2026-06-10 — the corrected design)

KEY CORRECTION: taintedGate n = {card = n ∧ AllClockP3 (erase mc)} — the HOUR-WINDOW gate, NOT a
tainted-count threshold. heB's escape = leaving the hour window (AllClockP3 breach = a clock
crossing past phase 3 = the cap-completion / counter-zero event) or card change (null).
⟹ heB unifies with ClockUnconditional's B-11 analysis (HabsGood ⟹ q = 0): the marked-kernel
analogue of hstep_of_sideGood. The side predicate: HourSideGood = card ∧ AllClockP3 ∧ FrontSync
(+ noPhaseAbove3/allClocksCounterPos/GoodFrontWidth/bulk-below as the closure proof needs).
- Instrument: GatedDrift.kill_escape_le_prefix_union with G = taintedGate n, S = HourSideGood,
  q = one-step escape from G∩S (target 0 via the deterministic skeleton + empty cap−1 feeder as in
  B-11), eB = M·q + ∑_{τ<M} side-prefix failures (supplied by the width/FrontSync prefix family
  pushed through markedK_pow_erase — the side events are ERASED-config events, so the real-kernel
  prefix bounds transfer exactly).
- tainted_marked_tail_explicit IS prefix-flexible (free t; hsmall monotone bridge like
  WidthPrefix.hsmall_mono) but is CIRCULAR for heB itself (its RHS contains the same escape mass);
  use only downstream.
- The taint-band alternative CANNOT close at θn = n^{3/5} (immigration M·(θn/n)² ≈ n^{1/5}·KK
  dominates tt = n^{3/20}) — do not attempt; irrelevant to the actual heB.
- Full compilable heB_params skeleton (eB_hour def + the prefix-union proof) is in the letter text
  below the fold in the campaign archive; key shape:
  heB_params (n hn Tcap mc₀ hcard hP3 S q sideB hstep hside) : ∀ T < Tcap, killK-escape ≤ eB_hour
