import ManuscriptGaussianMoment

open MeasureTheory ProbabilityTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem scaled_phi_integrable (m s : ℝ) (hs : s ≠ 0) :
    Integrable (fun x => phi ((x-m)/s)/s) volume := by
  exact (((integrable_gaussianPDFReal 0 1).comp_div hs).comp_sub_right m).div_const s

theorem scaled_phi_moment_integrable (m s : ℝ) (hs : s ≠ 0) :
    Integrable (fun x => x*phi ((x-m)/s)/s) volume := by
  have h1 := (phi_first_moment_integrable.comp_div hs).comp_sub_right m
  have h0 := (scaled_phi_integrable m s hs).const_mul m
  convert! h1.add h0 using 1
  funext x
  dsimp only [Pi.add_apply]
  field_simp
  <;> ring

theorem scaled_phi_truncated_moment (m s a : ℝ) (hs : 0 < s) :
    (∫ x in Iio a, x*phi ((x-m)/s)/s) =
      m*normalCDF ((a-m)/s)-s*phi ((a-m)/s) := by
  have hd x : HasDerivAt (fun y => m*normalCDF ((y-m)/s)-s*phi ((y-m)/s))
      (x*phi ((x-m)/s)/s) x := by
    have ha := ((hasDerivAt_id x).sub_const m).div_const s
    convert! (((normalCDF_hasDerivAt ((x-m)/s)).comp x ha).const_mul m).sub
      (((phi_derivative ((x-m)/s)).comp x ha).const_mul s) using 1
    dsimp only [phi]
    field_simp
    <;> ring
  have ht : Tendsto (fun x : ℝ => (x-m)/s) atBot atBot :=
    (tendsto_atBot_add_const_right atBot (-m) tendsto_id).atBot_div_const hs
  have hlim := ((normalCDF_atBot.comp ht).const_mul m).sub ((phi_atBot.comp ht).const_mul s)
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := a) (fun x _ => hd x)
    (scaled_phi_moment_integrable m s hs.ne').integrableOn hlim
  simpa only [integral_Iic_eq_integral_Iio,mul_zero,sub_zero] using h

end BarrierManuscript
#print axioms BarrierManuscript.scaled_phi_integrable
#print axioms BarrierManuscript.scaled_phi_moment_integrable
#print axioms BarrierManuscript.scaled_phi_truncated_moment
