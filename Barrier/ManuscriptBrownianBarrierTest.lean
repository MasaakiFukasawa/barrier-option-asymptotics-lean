import ManuscriptBrownianWeightedKernelMoment

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def brownianBarrierKernelTest {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (b k : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if pathMaximum (rawPrefixPath W hc t ω) ≤ b then
    psi (b-W t ω) (k-W t ω) (1-(t:ℝ)) else 0

theorem brownian_barrier_test_path_measurable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (b k : ℝ) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (fun ω t => W t ω) inferInstance]
      (brownianBarrierKernelTest W hc b k t) := by
  letI : MeasurableSpace Ω := MeasurableSpace.comap (fun ω t => W t ω) inferInstance
  have hh : Measurable (fun ω t => W t ω) := Measurable.of_comap_le le_rfl
  have hm (s : ℝ≥0) : Measurable (W s) := (measurable_pi_apply s).comp hh
  have hmax := pathMaximum_lipschitz.continuous.measurable.comp (rawPrefixPath_measurable W hm hc t)
  have hphi := phi_contDiff.continuous.measurable
  unfold brownianBarrierKernelTest
  apply Measurable.ite (measurableSet_le hmax measurable_const) _ measurable_const
  unfold psi
  fun_prop

theorem brownian_barrier_test_bound {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (b k : ℝ) (t : ℝ≥0) (ht : t < 1) (ω : Ω) :
    |brownianBarrierKernelTest W hc b k t ω| ≤ 2*normalizer/Real.sqrt (1-(t:ℝ)) := by
  unfold brownianBarrierKernelTest
  split_ifs
  · exact psi_absolute_bound _ _ _ (sub_pos.mpr (show (t:ℝ)<1 from ht))
  · simp only [abs_zero]
    unfold normalizer
    positivity

theorem brownian_barrier_test_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω))
    (s t : ℝ≥0) (hs : 0 < s) (hst : s < t) (ht : t < 1)
    (b k : ℝ) (hb : 0 < b) :
    (∫ ω,W s ω*brownianBarrierKernelTest W hc b k t ω ∂P)=barPsi b k s := by
  rw [← brownian_weighted_kernel_moment P W hW hm hc s t hs hst ht b k hb]
  have hset : MeasurableSet {ω | pathMaximum (rawPrefixPath W hc t ω) ≤ b} := measurableSet_le
    (pathMaximum_lipschitz.continuous.measurable.comp (rawPrefixPath_measurable W hm hc t)) measurable_const
  rw [← integral_indicator hset]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    simp only [brownianBarrierKernelTest,Set.indicator,Set.mem_setOf_eq]
    split_ifs <;> simp

end BarrierManuscript
#print axioms BarrierManuscript.brownian_barrier_test_path_measurable
#print axioms BarrierManuscript.brownian_barrier_test_bound
#print axioms BarrierManuscript.brownian_barrier_test_moment
