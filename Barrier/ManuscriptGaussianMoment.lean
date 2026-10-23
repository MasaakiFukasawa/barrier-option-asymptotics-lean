import ManuscriptScaledCoefficient
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory ProbabilityTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem phi_atBot : Tendsto phi atBot (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => x^2) atBot atTop := by
    simpa only [Function.comp_def,neg_sq] using
      (tendsto_pow_atTop (α := ℝ) (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_neg_atBot_atTop
  have ht : Tendsto (fun x : ℝ => -(x^2/2)) atBot atBot := tendsto_neg_atTop_atBot.comp (hs.atTop_div_const (by norm_num : (0:ℝ)<2))
  simpa only [Function.comp_def,mul_zero,← phi_eq] using (Real.tendsto_exp_atBot.comp ht).const_mul normalizer

theorem phi_first_moment_integrable : Integrable (fun x : ℝ => x*phi x) volume := by
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/2)).const_mul normalizer
  convert! h using 1
  funext x
  rw [phi_eq]
  rw [show -(x^2/2) = -(1/2)*x^2 by ring]
  ring

theorem phi_first_moment (a : ℝ) : (∫ x in Iio a, x*phi x) = -phi a := by
  have hd x : HasDerivAt (fun x => -phi x) (x*phi x) x := by
    convert! (phi_derivative x).neg using 1
    simp only [neg_mul,neg_neg]
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := a) (fun x _ => hd x)
    phi_first_moment_integrable.integrableOn phi_atBot.neg
  simpa only [integral_Iic_eq_integral_Iio,neg_zero,sub_zero] using h

end BarrierManuscript
#print axioms BarrierManuscript.phi_atBot
#print axioms BarrierManuscript.phi_first_moment_integrable
#print axioms BarrierManuscript.phi_first_moment
