import ManuscriptSmoothPrice
import ManuscriptGaussianBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def phiAverage (d q : ℝ) : ℝ :=
  ∫ t in Icc (-(1/2):ℝ) (1/2), phi (d+q*t)

noncomputable def averageLinear (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ + t • ContinuousLinearMap.snd ℝ ℝ ℝ

noncomputable def phiAverageD (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  ∫ t in Icc (-(1/2):ℝ) (1/2), (-(p.1+p.2*t)*phi (p.1+p.2*t)) • averageLinear t

theorem phi_derivative_bound (x : ℝ) : |-x*phi x| ≤ 3*normalizer := by
  rw [abs_mul,abs_neg,abs_of_nonneg (phi_nonneg x)]
  have h := mul_le_mul_of_nonneg_right (power_le_one_add_square x 1 (by norm_num)) (phi_nonneg x)
  simp only [pow_one] at h
  nlinarith [phi_le x,square_mul_phi_le x]

theorem averageLinear_norm (t : ℝ) : ‖averageLinear t‖ ≤ 1+|t| := by
  unfold averageLinear
  calc
    _ ≤ ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖+‖t • ContinuousLinearMap.snd ℝ ℝ ℝ‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul]; simp

theorem phiAverage_integrandD_bound (p : ℝ × ℝ) (t : ℝ) (ht : t ∈ Icc (-(1/2):ℝ) (1/2)) :
    ‖(-(p.1+p.2*t)*phi (p.1+p.2*t)) • averageLinear t‖ ≤ 5*normalizer := by
  rw [norm_smul,Real.norm_eq_abs]
  have hn := normalizer_nonneg
  have ht' : |t| ≤ 1/2 := abs_le.mpr ht
  have h := mul_le_mul (phi_derivative_bound (p.1+p.2*t)) (averageLinear_norm t)
    (norm_nonneg _) (by positivity : 0 ≤ 3*normalizer)
  have hh := mul_le_mul_of_nonneg_left ht' hn
  nlinarith

theorem phiAverage_hasFDerivAt (p : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => phiAverage p.1 p.2) (phiAverageD p) p := by
  let μ := volume.restrict (Icc (-(1/2):ℝ) (1/2))
  have hc t (z : ℝ × ℝ) : HasFDerivAt (fun p : ℝ × ℝ => p.1+p.2*t) (averageLinear t) z := by
    convert (averageLinear t).hasFDerivAt using 1
    funext q
    change q.1+q.2*t = q.1+t*q.2
    ring
  have hd t (z : ℝ × ℝ) : HasFDerivAt (fun p : ℝ × ℝ => phi (p.1+p.2*t))
      ((-(z.1+z.2*t)*phi (z.1+z.2*t)) • averageLinear t) z := by
    have hh := (phi_derivative (z.1+z.2*t)).hasFDerivAt.comp z (hc t z)
    convert! hh using 1
    apply ContinuousLinearMap.ext
    intro q
    change (-(z.1+z.2*t)*phi (z.1+z.2*t))*(q.1+t*q.2) =
      (q.1+t*q.2)*(-(z.1+z.2*t)*phi (z.1+z.2*t))
    ring
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (s := univ)
    (F := fun p t => phi (p.1+p.2*t))
    (F' := fun p t => (-(p.1+p.2*t)*phi (p.1+p.2*t)) • averageLinear t)
    (bound := fun _ => 5*normalizer) (by simp)
  · exact Eventually.of_forall fun z => (phi_contDiff.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact (phi_contDiff.continuous.comp (by fun_prop)).integrableOn_Icc
  · have hh : Continuous (fun t => (-(p.1+p.2*t)*phi (p.1+p.2*t)) • averageLinear t) := by
      unfold averageLinear
      exact ((by fun_prop : Continuous (fun t : ℝ => -(p.1+p.2*t))).mul
        (phi_contDiff.continuous.comp (by fun_prop))).smul (by fun_prop)
    exact hh.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact fun z _ => phiAverage_integrandD_bound z t ht
  · exact integrable_const _
  · exact ae_of_all _ fun t z _ => hd t z

theorem phiAverageD_continuous : Continuous phiAverageD := by
  unfold phiAverageD
  apply continuous_of_dominated (bound := fun _ => 5*normalizer)
  · intro p
    have hh : Continuous (fun t : ℝ => (-(p.1+p.2*t)*phi (p.1+p.2*t)) • averageLinear t) := by
      unfold averageLinear
      exact ((by fun_prop : Continuous (fun t : ℝ => -(p.1+p.2*t))).mul
        (phi_contDiff.continuous.comp (by fun_prop))).smul (by fun_prop)
    exact hh.aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact phiAverage_integrandD_bound p t ht
  · exact integrable_const _
  · apply ae_of_all
    intro t
    exact ((by fun_prop : Continuous (fun p : ℝ × ℝ => -(p.1+p.2*t))).mul
      (phi_contDiff.continuous.comp (by fun_prop))).smul continuous_const

theorem phiAverage_hasStrictFDerivAt (p : ℝ × ℝ) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => phiAverage p.1 p.2) (phiAverageD p) p :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Eventually.of_forall phiAverage_hasFDerivAt) phiAverageD_continuous.continuousAt

theorem phiAverage_zero (d : ℝ) : phiAverage d 0 = phi d := by
  norm_num [phiAverage,integral_const,Real.volume_Icc]

theorem phiAverageD_zero_apply (d : ℝ) (z : ℝ × ℝ) :
    phiAverageD (d,0) z = (-d*phi d)*z.1 := by
  have hi : Integrable (fun t : ℝ => (-d*phi d) • averageLinear t)
      (volume.restrict (Icc (-(1/2):ℝ) (1/2))) := by
    have hc : Continuous (fun t : ℝ => (-d*phi d) • averageLinear t) := by
      unfold averageLinear
      fun_prop
    exact hc.integrableOn_Icc
  unfold phiAverageD
  simp only [zero_mul,add_zero]
  rw [ContinuousLinearMap.integral_apply hi]
  change (∫ t in Icc (-(1/2):ℝ) (1/2), (-d*phi d)*(z.1+t*z.2)) = _
  rw [integral_const_mul]
  have h0 : (∫ t in Icc (-(1/2):ℝ) (1/2), z.1+t*z.2) = z.1 := by
    have hmul : Integrable (fun t : ℝ => t*z.2) (volume.restrict (Icc (-(1/2):ℝ) (1/2))) :=
      (continuous_id.mul continuous_const).integrableOn_Icc
    rw [integral_add (integrable_const z.1) hmul,
      integral_mul_const]
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2),
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
    norm_num
  rw [h0]

theorem normalCDF_difference_average (d q : ℝ) :
    normalCDF (d+q/2)-normalCDF (d-q/2) = q*phiAverage d q := by
  have hd t : HasDerivAt (fun t => normalCDF (d+q*t)) (q*phi (d+q*t)) t := by
    convert (normalCDF_hasDerivAt _).comp t (((hasDerivAt_id t).const_mul q).const_add d) using 1
    · rfl
    · dsimp only [phi,id_eq]
      ring
  have hi : IntervalIntegrable (fun t : ℝ => q*phi (d+q*t)) volume (-(1/2)) (1/2) :=
    (continuous_const.mul (phi_contDiff.continuous.comp (by fun_prop))).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at he
  unfold phiAverage
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2)]
  convert he.symm using 1 <;> congr 2 <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.phi_derivative_bound
#print axioms BarrierManuscript.averageLinear_norm
#print axioms BarrierManuscript.phiAverage_integrandD_bound
#print axioms BarrierManuscript.phiAverage_hasFDerivAt
#print axioms BarrierManuscript.phiAverageD_continuous
#print axioms BarrierManuscript.phiAverage_hasStrictFDerivAt

#print axioms BarrierManuscript.phiAverage_zero
#print axioms BarrierManuscript.phiAverageD_zero_apply
#print axioms BarrierManuscript.normalCDF_difference_average
