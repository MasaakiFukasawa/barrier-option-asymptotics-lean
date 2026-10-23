import ManuscriptGaussianBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set

namespace BarrierManuscript

theorem inv_sqrt_eq_rpow (u : ℝ) (hu : u ≤ 1) :
    1/Real.sqrt (1-u) = (1-u)^(-(1/2:ℝ)) := by
  rw [Real.rpow_neg (sub_nonneg.mpr hu), ← Real.sqrt_eq_rpow, one_div]

theorem time_bound_integrable :
    IntervalIntegrable (fun u : ℝ => 1/Real.sqrt (1-u)) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1)
    (r := -(1/2:ℝ)) (by norm_num)).comp_sub_left 1
  have hh : IntervalIntegrable (fun u : ℝ => (1-u)^(-(1/2:ℝ))) volume 0 1 := by
    simpa only [sub_zero, sub_self] using h.symm
  apply (intervalIntegrable_congr (f := fun u : ℝ => (1-u)^(-(1/2:ℝ))) ?_).mp hh
  intro u hu
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
  exact (inv_sqrt_eq_rpow u hu.2).symm

theorem time_bound_integral : (∫ u in (0:ℝ)..1, 1/Real.sqrt (1-u)) = 2 := by
  have he : (∫ u in (0:ℝ)..1, 1/Real.sqrt (1-u)) =
      ∫ u in (0:ℝ)..1, (1-u)^(-(1/2:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    exact inv_sqrt_eq_rpow u hu.2
  rw [he, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^(-(1/2:ℝ))) 1]
  norm_num only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2:ℝ)))]
  norm_num

theorem weighted_time_bound_integrable (H : ℝ) (hH : 0 ≤ H) :
    IntervalIntegrable (fun u : ℝ => u^H/Real.sqrt (1-u)) volume 0 1 := by
  simpa only [div_eq_mul_inv, one_mul] using
    time_bound_integrable.continuousOn_mul (Real.continuous_rpow_const hH).continuousOn

end BarrierManuscript

#print axioms BarrierManuscript.time_bound_integrable
#print axioms BarrierManuscript.time_bound_integral
#print axioms BarrierManuscript.weighted_time_bound_integrable
