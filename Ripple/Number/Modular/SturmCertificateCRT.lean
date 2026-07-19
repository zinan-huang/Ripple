import Ripple.Number.Modular.SturmCRTModNat
import Ripple.Number.Modular.SturmCRTPrimeList
import Ripple.Number.Modular.SturmCRTBound
import Ripple.Number.Modular.SturmCRTBatch01
import Ripple.Number.Modular.SturmCRTBatch02
import Ripple.Number.Modular.SturmCRTBatch03
import Ripple.Number.Modular.SturmCRTBatch04
import Ripple.Number.Modular.SturmCRTBatch05
import Ripple.Number.Modular.SturmCRTBatch06
import Ripple.Number.Modular.SturmCRTBatch07
import Ripple.Number.Modular.SturmCRTBatch08
import Ripple.Number.Modular.SturmCRTBatch09
import Ripple.Number.Modular.SturmCRTBatch10
import Ripple.Number.Modular.SturmCRTBatch11
import Ripple.Number.Modular.SturmCRTBatch12
import Ripple.Number.Modular.SturmCRTBatch13
import Ripple.Number.Modular.SturmCRTBatch14
import Ripple.Number.Modular.SturmCRTBatch15
import Ripple.Number.Modular.SturmCRTBatch16
import Ripple.Number.Modular.SturmCRTBatch17
import Ripple.Number.Modular.SturmCRTBatch18
import Ripple.Number.Modular.SturmCRTBatch19
import Ripple.Number.Modular.SturmCRTBatch20
import Ripple.Number.Modular.SturmCRTBatch21
import Ripple.Number.Modular.SturmCRTBatch22
import Ripple.Number.Modular.SturmCRTBatch23
import Ripple.Number.Modular.SturmCRTBatch24
import Ripple.Number.Modular.SturmCRTBatch25
import Ripple.Number.Modular.SturmCRTBatch26
import Ripple.Number.Modular.SturmCRTBatch27
import Ripple.Number.Modular.SturmCRTBatch28
import Ripple.Number.Modular.SturmCRTBatch29
import Ripple.Number.Modular.SturmCRTBatch30
import Ripple.Number.Modular.SturmCRTBatch31
import Ripple.Number.Modular.SturmCRTBatch32

namespace Ripple.Number.Modular

private theorem sturmCRTPrimeList_eq_concat :
    sturmCRTPrimeList =
    [999999929, 999999937, 1000000007, 1000000009, 1000000021, 1000000033, 1000000087, 1000000093]
    ++     [1000000097, 1000000103, 1000000123, 1000000181, 1000000207, 1000000223, 1000000241, 1000000271]
    ++     [1000000289, 1000000297, 1000000321, 1000000349, 1000000363, 1000000403, 1000000409, 1000000411]
    ++     [1000000427, 1000000433, 1000000439, 1000000447, 1000000453, 1000000459, 1000000483, 1000000513]
    ++     [1000000531, 1000000579, 1000000607, 1000000613, 1000000637, 1000000663, 1000000711, 1000000753]
    ++     [1000000787, 1000000801, 1000000829, 1000000861, 1000000871, 1000000891, 1000000901, 1000000919]
    ++     [1000000931, 1000000933, 1000000993, 1000001011, 1000001021, 1000001053, 1000001087, 1000001099]
    ++     [1000001137, 1000001161, 1000001203, 1000001213, 1000001237, 1000001263, 1000001269, 1000001273]
    ++     [1000001279, 1000001311, 1000001329, 1000001333, 1000001351, 1000001371, 1000001393, 1000001413]
    ++     [1000001447, 1000001449, 1000001491, 1000001501, 1000001531, 1000001537, 1000001539, 1000001581]
    ++     [1000001617, 1000001621, 1000001633, 1000001647, 1000001663, 1000001677, 1000001699, 1000001759]
    ++     [1000001773, 1000001789, 1000001791, 1000001801, 1000001803, 1000001819, 1000001857, 1000001887]
    ++     [1000001917, 1000001927, 1000001957, 1000001963, 1000001969, 1000002043, 1000002089, 1000002103]
    ++     [1000002139, 1000002149, 1000002161, 1000002173, 1000002187, 1000002193, 1000002233, 1000002239]
    ++     [1000002277, 1000002307, 1000002359, 1000002361, 1000002431, 1000002449, 1000002457, 1000002499]
    ++     [1000002571, 1000002581, 1000002607, 1000002631, 1000002637, 1000002649, 1000002667, 1000002727]
    ++     [1000002791, 1000002803, 1000002821, 1000002823, 1000002827, 1000002907, 1000002937, 1000002989]
    ++     [1000003009, 1000003013, 1000003051, 1000003057, 1000003097, 1000003111, 1000003133, 1000003153]
    ++     [1000003157, 1000003163, 1000003211, 1000003241, 1000003247, 1000003253, 1000003267, 1000003271]
    ++     [1000003273, 1000003283, 1000003309, 1000003337, 1000003351, 1000003357, 1000003373, 1000003379]
    ++     [1000003397, 1000003469, 1000003471, 1000003513, 1000003519, 1000003559, 1000003577, 1000003579]
    ++     [1000003601, 1000003621, 1000003643, 1000003651, 1000003663, 1000003679, 1000003709, 1000003747]
    ++     [1000003751, 1000003769, 1000003777, 1000003787, 1000003793, 1000003843, 1000003853, 1000003871]
    ++     [1000003889, 1000003891, 1000003909, 1000003919, 1000003931, 1000003951, 1000003957, 1000003967]
    ++     [1000003987, 1000003999, 1000004023, 1000004059, 1000004099, 1000004119, 1000004123, 1000004207]
    ++     [1000004233, 1000004249, 1000004251, 1000004263, 1000004321, 1000004329, 1000004381, 1000004389]
    ++     [1000004437, 1000004449, 1000004459, 1000004497, 1000004507, 1000004519, 1000004539, 1000004567]
    ++     [1000004569, 1000004581, 1000004609, 1000004611, 1000004627, 1000004633, 1000004647]
    ++     [1000004693, 1000004699, 1000004717, 1000004771, 1000004777, 1000004783, 1000004791]
    ++     [1000004807, 1000004839, 1000004843, 1000004849, 1000004857, 1000004867, 1000004869]
    ++     [1000004891, 1000004893, 1000004897, 1000004927, 1000004933, 1000004977, 1000004981]
    ++     [1000005001, 1000005029, 1000005053, 1000005067, 1000005103, 1000005133, 1000005187] := by native_decide

private theorem sturmCRTCheckAllFast_all_primes_bool :
    sturmCRTPrimeList.all (fun p => sturmCRTCheckAllFast p) = true := by
  rw [sturmCRTPrimeList_eq_concat]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sturmCRTCheck_batch01, sturmCRTCheck_batch02⟩, sturmCRTCheck_batch03⟩, sturmCRTCheck_batch04⟩, sturmCRTCheck_batch05⟩, sturmCRTCheck_batch06⟩, sturmCRTCheck_batch07⟩, sturmCRTCheck_batch08⟩, sturmCRTCheck_batch09⟩, sturmCRTCheck_batch10⟩, sturmCRTCheck_batch11⟩, sturmCRTCheck_batch12⟩, sturmCRTCheck_batch13⟩, sturmCRTCheck_batch14⟩, sturmCRTCheck_batch15⟩, sturmCRTCheck_batch16⟩, sturmCRTCheck_batch17⟩, sturmCRTCheck_batch18⟩, sturmCRTCheck_batch19⟩, sturmCRTCheck_batch20⟩, sturmCRTCheck_batch21⟩, sturmCRTCheck_batch22⟩, sturmCRTCheck_batch23⟩, sturmCRTCheck_batch24⟩, sturmCRTCheck_batch25⟩, sturmCRTCheck_batch26⟩, sturmCRTCheck_batch27⟩, sturmCRTCheck_batch28⟩, sturmCRTCheck_batch29⟩, sturmCRTCheck_batch30⟩, sturmCRTCheck_batch31⟩, sturmCRTCheck_batch32⟩

theorem sturmCRTCheckAll_all_primes :
    ∀ p ∈ sturmCRTPrimeList, sturmCRTCheckAll p = true := by
  intro p hp
  rw [← sturmCRTCheckAllFast_eq]
  exact List.all_eq_true.mp sturmCRTCheckAllFast_all_primes_bool p hp

private theorem hderiv_all :
    ∀ j : ℕ, j ≤ 42 →
      E4ZSeries *
          (PowerSeries.X * PowerSeries.derivative ℤ
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =
        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -
          PowerSeries.C (j : ℤ) * E6ZSeries) *
            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j)) := by
  intro j hj
  exact phi41LevelOneDenseRow_derivative_identity_of_base j hj
    (E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity
      E4ZSeries_derivative_identity)
    deltaEulerSeriesZ_derivative_identity

theorem phi41Level41RecurrenceCoeffArrayFirstZero_sturmBound_CRT :
    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true :=
  phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_row_table_bools
    sturmCRTPrimeList_nodup
    sturmCRTPrimeList_prime
    sturmCRTPrimeList_large
    phi41_final_coeff_bound
    sturmCRTPrimeList_bound
    sturmCRTPCompressedMod
    sturmCRTQMod
    (fun p hp => sturmCRTCheckAll_hPcert (sturmCRTCheckAll_all_primes p hp))
    (fun p hp => sturmCRTCheckAll_hQcert (sturmCRTCheckAll_all_primes p hp))
    (fun p hp => sturmCRTCheckAll_hzero (sturmCRTCheckAll_all_primes p hp))
    hderiv_all

end Ripple.Number.Modular
