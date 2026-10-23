import ManuscriptBridgeIntegrability

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem bridge_test_integrable (b t d : ℝ) (hb : 0 < b) (ht : 0 < t) (hd : 0 < d)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, |f p| ≤ C*(1+|p.1|)) :
    Integrable (fun p : ℝ × ℝ => f p*psi (b-p.1) (p.2-p.1) d*psi b p.1 t)
      ((volume.restrict (Iio b)).prod (volume.restrict (Iio b))) := by
  have hphi := phi_contDiff.continuous.measurable
  have hm : Measurable (fun p : ℝ × ℝ => f p*psi (b-p.1) (p.2-p.1) d*psi b p.1 t) := by
    unfold psi; fun_prop
  apply ((bridge_kernel_weight_integrable b t d hb ht hd).const_mul C).mono' hm.aestronglyMeasurable
  have hdomM : Measurable (fun p : ℝ × ℝ => C*((1+|p.1|)*psi b p.1 t*psi (b-p.1) (p.2-p.1) d)) := by
    unfold psi; fun_prop
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm hdomM)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
  have h1 := psi_nonneg b y t hb.le hy.le ht
  have h2 := psi_nonneg (b-y) (x-y) d (sub_nonneg.mpr hy.le) (sub_le_sub_right hx.le y) hd
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg h1,abs_of_nonneg h2]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound (y,x)) h2) h1
  dsimp only at hh ⊢
  nlinarith only [hh]

end BarrierManuscript
#print axioms BarrierManuscript.bridge_test_integrable
