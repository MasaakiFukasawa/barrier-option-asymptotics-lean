import ManuscriptBrownianJointCDF
import ManuscriptKilledDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

theorem brownian_terminal_noatom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (k : ℝ) :
    ∀ᵐ ω ∂P, B.W 0 (realTimeClamp 1) ω ≠ k := by
  have hl : HasLaw (B.W 0 (realTimeClamp 1)) (gaussianReal 0 1) P := by
    convert scaled_brownian_gaussian_law P B 1 1 (by norm_num) (by norm_num) using 1 <;> norm_num
    congr 1
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  rw [ae_iff]
  have he := hl.measure_eq (p := fun x => x=k) (measurableSet_singleton k)
  simpa only [not_not,Set.ofPred_eq_eq_singleton,measure_singleton] using he

theorem brownian_endpoint_le_maximum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (ω : Ω) :
    B.W 0 (realTimeClamp 1) ω ≤ brownianMaximum B ω := by
  let f := continuousPath (brownianPrefix B) (brownian_prefix_regular P B).2 ω
  have h := le_csSup (path_range_bddAbove f) (mem_range_self (realTimeClamp (T := (⊤:EReal)) 1))
  simpa only [f,brownianMaximum,pathMaximum,continuousPath,ContinuousMap.coe_mk,brownianPrefix,min_self] using h

theorem brownian_endpoint_maximum_closed_cdf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) :
    P.real {ω | B.W 0 (realTimeClamp 1) ω ≤ k ∧ brownianMaximum B ω ≤ b} =
      normalCDF (min k b)-normalCDF (min k b-2*b) := by
  by_cases hk : k < b
  · have he : {ω | B.W 0 (realTimeClamp 1) ω ≤ k ∧ brownianMaximum B ω ≤ b} =ᵐ[P]
        {ω | B.W 0 (realTimeClamp 1) ω < k ∧ brownianMaximum B ω ≤ b} := by
      filter_upwards [brownian_terminal_noatom P B k] with ω hω
      apply propext
      exact and_congr_left fun _ => ⟨fun h => lt_of_le_of_ne h hω,le_of_lt⟩
    rw [measureReal_congr he,brownian_endpoint_maximum_cdf P B b k hb hk,min_eq_left hk.le]
  · have hbk : b ≤ k := le_of_not_gt hk
    have he : {ω | B.W 0 (realTimeClamp 1) ω ≤ k ∧ brownianMaximum B ω ≤ b} =
        {ω | brownianMaximum B ω ≤ b} := by
      ext ω
      exact ⟨fun h => h.2,fun h => ⟨(brownian_endpoint_le_maximum P B ω).trans (h.trans hbk),h⟩⟩
    have ha : {ω | brownianMaximum B ω ≤ b} =ᵐ[P] {ω | brownianMaximum B ω < b} := by
      filter_upwards [brownian_maximum_noatom P B b hb] with ω hω
      exact propext ⟨fun h => lt_of_le_of_ne h hω,le_of_lt⟩
    rw [he,measureReal_congr ha,brownian_maximum_cdf P B b hb,min_eq_right hbk,
      show b-2*b = -b by ring,normalCDF_neg]
    ring

noncomputable def brownianKilledMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1) (b : ℝ) : Measure ℝ :=
  (P.restrict {ω | brownianMaximum B ω ≤ b}).map (B.W 0 (realTimeClamp 1))

theorem brownianKilledMeasure_Iic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) :
    (brownianKilledMeasure B b).real (Iic k) = normalCDF (min k b)-normalCDF (min k b-2*b) := by
  have hm : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (changed_time_finite 1 (by norm_num))).mono (B.le _) le_rfl
  have he : brownianKilledMeasure B b (Iic k) =
      P {ω | B.W 0 (realTimeClamp 1) ω ≤ k ∧ brownianMaximum B ω ≤ b} := by
    rw [brownianKilledMeasure,Measure.map_apply hm measurableSet_Iic,
      Measure.restrict_apply (hm measurableSet_Iic)]
    rfl
  change (brownianKilledMeasure B b (Iic k)).toReal = _
  rw [he]
  exact brownian_endpoint_maximum_closed_cdf P B b k hb


/-- Full killed endpoint measure, obtained from the derived distribution
function by uniqueness of finite Borel measures. -/
theorem brownian_killed_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (hb : 0 < b) :
    brownianKilledMeasure B b = volume.withDensity (fun x => ENNReal.ofReal (killedDensity b x)) := by
  letI : IsFiniteMeasure (brownianKilledMeasure B b) := by
    unfold brownianKilledMeasure
    infer_instance
  apply Measure.ext_of_Iic
  intro k
  have hμ : brownianKilledMeasure B b (Iic k) =
      ENNReal.ofReal (normalCDF (min k b)-normalCDF (min k b-2*b)) := by
    rw [← brownianKilledMeasure_Iic P B b k hb]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hμ,withDensity_apply _ measurableSet_Iic]
  rw [← ofReal_integral_eq_lintegral_ofReal (killedDensity_integrable b).integrableOn
    (ae_of_all _ fun x => killedDensity_nonneg b hb.le x)]
  rw [integral_Iic_eq_integral_Iio,killedDensity_integral_Iio]


/-- The reflection density integrated against an arbitrary measurable test
function; this includes the Gaussian kernels used in the expansion. -/
theorem brownian_killed_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (hb : 0 < b) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω in {ω | brownianMaximum B ω ≤ b}, f (B.W 0 (realTimeClamp 1) ω) ∂P) =
      ∫ x in Iio b, f x*(phi x-phi (x-2*b)) := by
  classical
  have hm : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (changed_time_finite 1 (by norm_num))).mono (B.le _) le_rfl
  have hd : Measurable (killedDensity b) := by
    exact (phi_contDiff.continuous.measurable.sub
      (phi_contDiff.continuous.measurable.comp (measurable_id.sub_const (2*b)))).ite
        measurableSet_Iio measurable_const
  calc
    _ = ∫ x, f x ∂brownianKilledMeasure B b :=
      (integral_map hm.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ x, killedDensity b x*f x := by
      rw [brownian_killed_density P B b hb,integral_withDensity_eq_integral_toReal_smul
        hd.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (killedDensity_nonneg b hb.le _),smul_eq_mul]
    _ = _ := by
      rw [← integral_indicator measurableSet_Iio]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        simp only [killedDensity,Set.indicator_apply,mem_Iio]
        split_ifs <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.brownian_terminal_noatom
#print axioms BarrierManuscript.brownian_endpoint_le_maximum
#print axioms BarrierManuscript.brownian_endpoint_maximum_closed_cdf
#print axioms BarrierManuscript.brownianKilledMeasure_Iic

#print axioms BarrierManuscript.brownian_killed_density

#print axioms BarrierManuscript.brownian_killed_expectation
