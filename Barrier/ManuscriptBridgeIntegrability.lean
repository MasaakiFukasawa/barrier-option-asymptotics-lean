import ManuscriptPsiIntegrability
import ManuscriptTranslateKernel

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem bridge_kernel_weight_integrable (b t d : ℝ) (hb : 0 < b) (ht : 0 < t) (hd : 0 < d) :
    Integrable (fun p : ℝ × ℝ => (1+|p.1|)*psi b p.1 t*psi (b-p.1) (p.2-p.1) d)
      ((volume.restrict (Iio b)).prod (volume.restrict (Iio b))) := by
  let F := fun p : ℝ × ℝ => (1+|p.1|)*psi b p.1 t*psi (b-p.1) (p.2-p.1) d
  have hphi := phi_contDiff.continuous.measurable
  have hm : Measurable F := by unfold F psi; fun_prop
  have hdom : Integrable (fun x => (1+|x|)*psi b x t) (volume.restrict (Iio b)) := by
    have h := ((psi_integrable b t ht).norm.add (psi_first_moment_integrable b t ht).norm).integrableOn (s := Iio b)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    simp only [Pi.add_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg (psi_nonneg b x t hb.le hx.le ht)]
    ring
  have hinner x : Integrable (fun y => F (x,y)) (volume.restrict (Iio b)) := by
    exact (((psi_integrable (b-x) d hd).comp_sub_right x).const_mul ((1+|x|)*psi b x t)).integrableOn
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ hinner
  · apply hdom.mono' hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hc : 0 ≤ (1+|x|)*psi b x t := mul_nonneg (by positivity) (psi_nonneg b x t hb.le hx.le ht)
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    have he : (∫ y in Iio b, ‖F (x,y)‖) = ((1+|x|)*psi b x t)*(∫ y in Iio b, psi (b-x) (y-x) d) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
      change ‖((1+|x|)*psi b x t)*psi (b-x) (y-x) d‖ = _
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hc (psi_nonneg (b-x) (y-x) d (sub_nonneg.mpr hx.le) (sub_le_sub_right hy.le x) hd))]
    rw [he]
    have hs : (∫ y in Iio b, psi (b-x) (y-x) d) = ∫ z in Iio (b-x), psi (b-x) z d := by
      rw [← integral_translate_Iio (fun y => psi (b-x) (y-x) d) b x]
      simp only [add_sub_cancel_left]
    rw [hs]
    exact mul_le_of_le_one_right hc (psi_mass_le_one (b-x) d hd)

end BarrierManuscript
#print axioms BarrierManuscript.bridge_kernel_weight_integrable
