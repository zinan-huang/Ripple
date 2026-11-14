-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingHourSchedule.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourInvariant
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCancellationTargets
noncomputable section
namespace Ripple.PopulationProtocol.ExactMajority.AveragingHourSchedule
open TimeTheorem StageEventSpec P3DeterministicAlgebra
open AveragingMixedAlgebra AveragingMixedLedgers AveragingLiveProduct
open AveragingCancellationAlgebra AveragingCancellationTargets
def totalRegime (ell h:ℕ):CancellationRegime :=
 if h+4=ell then .totalFourth
 else if h+3=ell then .totalThird
 else if h+2=ell then .totalSecond
 else if h+1=ell then .totalPrevious
 else if h=ell then .totalTerminal
 else .early
def totalTarget (ell h:ℕ):ℚ :=
 if h+4=ell then 13 / 125
 else if h+3=ell then 13 / 100
 else if h+2=ell then 53 / 250
 else if h+1=ell then 51 / 125
 else if h=ell then 101 / 125
 else 1 / 10
def totalPrevious (ell h:ℕ):ℚ:=totalTarget ell (h - 1)
def minorityRegime (ell h:ℕ):CancellationRegime :=
 if h+4=ell then .minorityFourth
 else if h+3=ell then .minorityThird
 else if h+2=ell then .minoritySecond
 else if h+1=ell then .minorityPrevious
 else .minorityTerminal
def minorityTarget (ell h:ℕ):ℚ :=
 if h+4=ell then 3 / 80
 else if h+3=ell then 267 / 10000
 else if h+2=ell then 29 / 2000
 else if h+1=ell then 7 / 1250
 else if h=ell then 1 / 250
 else 7 / 160
def minorityPrevious (ell h:ℕ):ℚ:=minorityTarget ell (h - 1)
theorem totalRegime_kind (ell h:ℕ) :
  targetKind (totalRegime ell h)=.total:=by
 unfold totalRegime
 split_ifs <;> rfl
theorem minorityRegime_kind (ell h:ℕ) :
  targetKind (minorityRegime ell h)=.minority:=by
 unfold minorityRegime
 split_ifs <;> rfl
theorem totalTarget_cast (ell h:ℕ) :
  (totalTarget ell h:ℝ)=currentTarget (totalRegime ell h):=by
 unfold totalTarget totalRegime
 split_ifs <;> norm_num [currentTarget]
theorem totalPrevious_cast (ell h:ℕ) (hell:5≤ell)
  (hpos:1≤h) (hle:h≤ell) :
  (totalPrevious ell h:ℝ)=previousTarget (totalRegime ell h):=by
 unfold totalPrevious totalTarget totalRegime
 split_ifs <;> norm_num [previousTarget] <;> omega
theorem minorityTarget_cast (ell h:ℕ)
  (hle:h≤ell) (hlast:ell≤h+4) :
  (minorityTarget ell h:ℝ)=currentTarget (minorityRegime ell h):=by
 unfold minorityTarget minorityRegime
 split_ifs <;> norm_num [currentTarget] <;> omega
theorem minorityPrevious_cast (ell h:ℕ) (hell:5≤ell)
  (hpos:1≤h) (hle:h≤ell) (hlast:ell≤h+4) :
  (minorityPrevious ell h:ℝ)=previousTarget (minorityRegime ell h):=by
 unfold minorityPrevious minorityTarget minorityRegime
 split_ifs <;> norm_num [previousTarget] <;> omega
theorem totalTarget_early {ell h:ℕ} (hearly:h+5≤ell) :
  totalTarget ell h=1 / 10:=by
 simp [totalTarget,show h+4≠ell by omega,
  show h+3≠ell by omega,show h+2≠ell by omega,
  show h+1≠ell by omega,show h≠ell by omega]
theorem totalPrevious_early {ell h:ℕ} (hpos:1≤h)
  (hearly:h+4≤ell) :
  totalPrevious ell h=1 / 10 :=
 totalTarget_early (by omega:h - 1+5≤ell)
theorem totalPrevious_le {ell h:ℕ} (hpos:1≤h) (hle:h≤ell) :
  totalPrevious ell h≤51 / 125:=by
 unfold totalPrevious totalTarget
 split_ifs <;> norm_num <;> omega
theorem old_block_previous_early {ell h j:ℕ}
  (hpos:1≤j) (hj:j+6≤h) (hh:h≤ell) :
  totalPrevious ell j=1 / 10 :=
 totalPrevious_early hpos (by omega)
theorem minority_base_target (ell:ℕ) (hell:5≤ell) :
  minorityTarget ell (ell - 5)=7 / 160:=by
 simp [minorityTarget,show ell - 5+4≠ell by omega,
  show ell - 5+3≠ell by omega,show ell - 5+2≠ell by omega,
  show ell - 5+1≠ell by omega,show ell - 5≠ell by omega]
theorem total_gap_bound (ell h M d:ℕ) (hle:h≤ell)
  (hscale:5*2^ell*d < 4*M) :
  (2:ℝ)^h*d≤gapTarget (totalRegime ell h)*M:=by
 have hs:(5:ℝ)*(2:ℝ)^ell*d < 4*M:=by exact_mod_cast hscale
 unfold totalRegime
 split_ifs with hfour hthree htwo hone hzero
 ·
  rw [← hfour,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  rw [← hthree,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  rw [← htwo,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  rw [← hone,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  rw [← hzero] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  have hearly:h+5≤ell:=by omega
  have hp:(2:ℝ)^(h+5)≤(2:ℝ)^ell:=by
   exact_mod_cast Nat.pow_le_pow_right (by decide:0 < (2:ℕ)) hearly
  have hp':=mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg d:(0:ℝ)≤d)
  rw [pow_add] at hp'
  norm_num [gapTarget] at hp' ⊢
  nlinarith only [hs,hp']
theorem minority_gap_bound (ell h M d:ℕ)
  (hle:h≤ell) (hlast:ell≤h+4)
  (hscale:2*M≤5*2^ell*d) :
  gapTarget (minorityRegime ell h)*M≤(2:ℝ)^h*d:=by
 have hs:(2:ℝ)*M≤5*(2:ℝ)^ell*d:=by exact_mod_cast hscale
 unfold minorityRegime
 split_ifs with hfour hthree htwo hone
 ·
  rw [← hfour,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  rw [← hthree,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  rw [← htwo,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  rw [← hone,pow_add] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
 ·
  have he:h=ell:=by omega
  rw [← he] at hs
  norm_num [gapTarget] at hs ⊢
  nlinarith only [hs]
theorem minority_base_gap (ell M d:ℕ) (hell:5≤ell)
  (hscale:2*M≤5*2^ell*d) :
  (1 / 80:ℝ)*M≤(2:ℝ)^(ell - 5)*d:=by
 have hs:(2:ℝ)*M≤5*(2:ℝ)^ell*d:=by exact_mod_cast hscale
 have he:ell=(ell - 5)+5:=by omega
 rw [he,pow_add] at hs
 norm_num at hs
 nlinarith only [hs]
theorem minority_base_of_total {P B M:ℝ}
  (htotal:P+B≤(1 / 10)*M)
  (hgap:(1 / 80)*M≤P - B) :
  B≤(7 / 160)*M:=by
 linarith only [htotal,hgap]
theorem initialGap_abs_cast {L K:ℕ} (init:Cfg L K) :
  |(initialGap init:ℝ)|=(gapMagnitude init:ℝ):=by
 unfold gapMagnitude
 rw [← Int.cast_abs,←Int.natCast_natAbs,Int.cast_natCast]
theorem trace_majority_gap (σ:Sign)
  {n:ℕ} {init:InputCfg n} (hvalid:validInitial init)
  {ω:InputLog n} {S T ρ v:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ)
  (hwinning:winningSign init σ) :
  (sideMass σ (trace init ω v):ℝ) -
   (sideMass (oppositeSign σ) (trace init ω v):ℝ) =
    (gapMagnitude init:ℝ):=by
 have hs:=trace_mixedSigned_eq_initialGap init hvalid ω v
  (fun a ha=>by have:=(H.phase_range v hSv hvρ a ha).2; omega)
 have hd:(sideMass .pos (trace init ω v):ℝ) -
   (sideMass .neg (trace init ω v):ℝ)=(initialGap init:ℝ):=by
  exact_mod_cast ((sideMass_sub (trace init ω v)).trans hs)
 have ha:=initialGap_abs_cast init
 cases σ with
 | pos =>
   change 0 < initialGap init at hwinning
   have hp:(0:ℝ) < (initialGap init:ℝ):=by exact_mod_cast hwinning
   rw [abs_of_pos hp] at ha
   exact hd.trans ha
 | neg =>
   change initialGap init < 0 at hwinning
   have hp:(initialGap init:ℝ) < 0:=by exact_mod_cast hwinning
   rw [abs_of_neg hp] at ha
   change (sideMass .neg (trace init ω v):ℝ) -
    (sideMass .pos (trace init ω v):ℝ)=_
   linarith only [hd,ha]
theorem total_targetGap_of_clockHistory (σ:Sign)
  {n:ℕ} {init:InputCfg n} (hvalid:validInitial init)
  {ω:InputLog n} {S T ρ v ell h:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ)
  (hle:h≤ell) (hlevel:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hscale:5*2^ell*gapMagnitude init <
   4*timeMainCount (trace init ω S)) :
  targetGap (totalRegime ell h) σ ⟨h,by omega⟩
   (timeMainCount (trace init ω S)) (trace init ω v):=by
 have hs:=trace_mixedSigned_eq_initialGap init hvalid ω v
  (fun a ha=>by have:=(H.phase_range v hSv hvρ a ha).2; omega)
 have hsR:(prePhase4MassSum (trace init ω v):ℝ) =
   (initialGap init:ℝ):=by exact_mod_cast hs
 simp only [targetGap,totalRegime_kind]
 rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤2^h by positivity),
  hsR,initialGap_abs_cast]
 exact total_gap_bound ell h _ _ hle hscale
theorem minority_targetGap_of_clockHistory (σ:Sign)
  {n:ℕ} {init:InputCfg n} (hvalid:validInitial init)
  {ω:InputLog n} {S T ρ v ell h:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ)
  (hwinning:winningSign init σ)
  (hle:h≤ell) (hlast:ell≤h+4)
  (hlevel:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hscale:2*timeMainCount (trace init ω S) ≤
   5*2^ell*gapMagnitude init) :
  targetGap (minorityRegime ell h) σ ⟨h,by omega⟩
   (timeMainCount (trace init ω S)) (trace init ω v):=by
 simp only [targetGap,minorityRegime_kind]
 rw [trace_majority_gap σ hvalid H hSv hvρ hwinning]
 exact minority_gap_bound ell h _ _ hle hlast hscale
theorem minority_base_of_total_checkpoint (σ:Sign)
  {n:ℕ} {init:InputCfg n} (hvalid:validInitial init)
  {ω:InputLog n} {S T ρ v ell:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (hSv:S≤v) (hvρ:v < ρ)
  (hwinning:winningSign init σ) (hell:5≤ell)
  (hscale:2*timeMainCount (trace init ω S) ≤
   5*2^ell*gapMagnitude init)
  (htotal:(2:ℚ)^(ell - 5)*mixedAbsoluteMass (trace init ω v) ≤
   (1 / 10:ℚ)*timeMainCount (trace init ω S)) :
  (2:ℚ)^(ell - 5)*sideMass (oppositeSign σ) (trace init ω v) ≤
   minorityTarget ell (ell - 5)*timeMainCount (trace init ω S):=by
 have hsum:sideMass σ (trace init ω v) +
   sideMass (oppositeSign σ) (trace init ω v) =
    mixedAbsoluteMass (trace init ω v):=by
  cases σ <;> simpa only [oppositeSign,add_comm] using sideMass_add (trace init ω v)
 have hsumR:(sideMass σ (trace init ω v):ℝ) +
   (sideMass (oppositeSign σ) (trace init ω v):ℝ) =
    (mixedAbsoluteMass (trace init ω v):ℝ):=by exact_mod_cast hsum
 have htotalR:(2:ℝ)^(ell - 5)*(mixedAbsoluteMass (trace init ω v):ℝ) ≤
   (1 / 10:ℝ)*timeMainCount (trace init ω S):=by
  have h2:=(Rat.cast_le (K:=ℝ)).mpr htotal
  push_cast at h2
  exact h2
 have ht:(2:ℝ)^(ell - 5)*(sideMass σ (trace init ω v):ℝ) +
   (2:ℝ)^(ell - 5)*(sideMass (oppositeSign σ) (trace init ω v):ℝ) ≤
    (1 / 10:ℝ)*timeMainCount (trace init ω S):=by
  rw [← mul_add,hsumR]
  exact htotalR
 have hg:=minority_base_gap ell (timeMainCount (trace init ω S))
  (gapMagnitude init) hell hscale
 rw [← trace_majority_gap σ hvalid H hSv hvρ hwinning,mul_sub] at hg
 have hb:=minority_base_of_total ht hg
 rw [minority_base_target ell hell]
 exact (Rat.cast_le (K:=ℝ)).mp (by push_cast; exact_mod_cast hb)
end Ripple.PopulationProtocol.ExactMajority.AveragingHourSchedule
end
