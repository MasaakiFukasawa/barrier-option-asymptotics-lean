import ManuscriptGammaIntegral
import ManuscriptIncompleteBeta

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem barPhi_uniform_bound (b k u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    |barPhi b k u| ≤ phi k*(4*|b|+3*|k|) := by
  have hN : |normalCDF ((b-u*k)/Real.sqrt (u*(1-u)))| ≤ 1 := by
    rw [abs_of_nonneg (show 0 ≤ normalCDF _ from measureReal_nonneg)]
    exact measureReal_le_one
  have huk : |u*k| ≤ |k| := by
    rw [abs_mul,abs_of_nonneg hu.1]
    exact mul_le_of_le_one_left (abs_nonneg _) hu.2
  have hbk : |b-u*k| ≤ |b|+|k| := (abs_sub _ _).trans (add_le_add_right huk _)
  have hNmul : |2*(b-u*k)*normalCDF ((b-u*k)/Real.sqrt (u*(1-u)))| ≤ 2*(|b|+|k|) := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2*|b-u*k| *1 := mul_le_mul_of_nonneg_left hN (by positivity)
      _ ≤ _ := by nlinarith
  unfold barPhi
  rw [abs_mul,abs_of_nonneg (phi_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (phi_nonneg _)
  have h1 := abs_sub (2*b-u*k) (2*(b-u*k)*normalCDF ((b-u*k)/Real.sqrt (u*(1-u))))
  have h2 := abs_sub (2*b) (u*k)
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h2
  linarith

theorem barPsi_uniform_bound (b k u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    |barPsi b k u| ≤ phi k*(4*|b|+3*|k|)+phi (2*b-k)*(4*|b|+3*|2*b-k|) :=
  (abs_sub _ _).trans (add_le_add (barPhi_uniform_bound b k u hu) (barPhi_uniform_bound b (2*b-k) u hu))

/-- The rough coefficient's one-dimensional integral is well-defined, despite
the singular Volterra weight at the upper endpoint. -/
theorem rough_coefficient_integrable (b k H : ℝ) (hH : -(1/2:ℝ) < H) :
    IntervalIntegrable (fun s : ℝ => (1-s)^(H-1/2)*barPsi b k s) volume 0 1 := by
  let C := phi k*(4*|b|+3*|k|)+phi (2*b-k)*(4*|b|+3*|2*b-k|)
  have hi : IntervalIntegrable (fun s : ℝ => (1-s)^(H-1/2)) volume 0 1 := by
    simpa using (intervalIntegral.intervalIntegrable_rpow'
      (a := (1:ℝ)) (b := 0) (by linarith : -1 < H-1/2)).comp_sub_left 1
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi
  apply (hi'.mul_const C).mono'
  · have hphi : Measurable phi := phi_contDiff.continuous.measurable
    have hN : Measurable normalCDF := normalCDF_contDiff.continuous.measurable
    unfold barPsi barPhi
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
    exact mul_le_mul_of_nonneg_left (barPsi_uniform_bound b k s hs) (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)

end BarrierManuscript
#print axioms BarrierManuscript.barPhi_uniform_bound
#print axioms BarrierManuscript.barPsi_uniform_bound
#print axioms BarrierManuscript.rough_coefficient_integrable
