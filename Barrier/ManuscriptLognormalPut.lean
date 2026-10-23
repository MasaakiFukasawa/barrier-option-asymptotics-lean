import ManuscriptBlackScholesPhysical
import ManuscriptGaussianMoment
import Chapter4GaussianPayoff

open MeasureTheory ProbabilityTheory Set Filter Asakura.Chapter4
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem bsStockPut_external (K s w : ℝ) (hK : 0 < K) (hs : 0 < s) :
    bsStockPut K s w = Asakura.Chapter4.bsPut K 0 0 w s 1 := by
  unfold bsStockPut BarrierManuscript.bsPut Asakura.Chapter4.bsPut bsD
  simp only [zero_sub,sub_zero,zero_mul,Real.exp_zero,one_mul,Real.sqrt_one,mul_one,neg_zero]
  rw [Real.exp_sub,Real.exp_log hK,Real.exp_log hs,Real.log_div hs.ne' hK.ne']
  have h1 : -( (Real.log s-Real.log K-w^2/2)/w) = (Real.log K-Real.log s)/w+w/2 := by
    by_cases hw : w=0
    · simp [hw]
    · field_simp
      <;> ring
  have h2 : -((Real.log s-Real.log K+w^2/2)/w) = (Real.log K-Real.log s)/w-w/2 := by
    by_cases hw : w=0
    · simp [hw]
    · field_simp
      <;> ring
  simp only [zero_add,← sub_eq_add_neg]
  rw [h1,h2]
  field_simp

/-- Gaussian integral form of the undiscounted put, with the exact
normalization used by the barrier manuscript. -/
theorem bsStockPut_gaussian (K s w : ℝ) (hK : 0 < K) (hs : 0 < s) (hw : 0 < w) :
    (∫ z, max (K-s*Real.exp (-w^2/2+w*z)) 0 ∂gaussianReal 0 1) = bsStockPut K s w := by
  rw [bsStockPut_external K s w hK hs]
  simpa only [zero_sub,sub_zero,zero_mul,Real.exp_zero,one_mul,Real.sqrt_one,mul_one,neg_zero,max_comm,neg_div] using
    bs_put_gaussian_payoff s K 0 0 w 1 hs hK hw zero_lt_one

theorem shifted_phi_expectation (m : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x*phi (x-m)) = ∫ z, f (z+m) ∂gaussianReal 0 1 := by
  have hm : (gaussianReal 0 1).map (fun x => x+m) = gaussianReal m 1 := by
    simpa only [zero_add] using (gaussianReal_map_add_const (μ := 0) (v := 1) m)
  rw [← integral_map (by fun_prop : AEMeasurable (fun x : ℝ => x+m) (gaussianReal 0 1)) hf.aestronglyMeasurable,hm]
  rw [gaussianReal_of_var_ne_zero m (by norm_num),integral_withDensity_eq_integral_toReal_smul
    (measurable_gaussianPDF m 1) (ae_of_all _ fun _ => by simp [gaussianPDF])]
  simp only [toReal_gaussianPDF,smul_eq_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp [phi,gaussianPDFReal,mul_comm]

theorem shifted_lognormal_put (K w m : ℝ) (hK : 0 < K) (hw : 0 < w) :
    (∫ x, max (K-Real.exp (w*x)) 0*phi (x-m)) =
      bsStockPut K (Real.exp (w*m+w^2/2)) w := by
  rw [shifted_phi_expectation m _ (by fun_prop),← bsStockPut_gaussian K _ w hK (Real.exp_pos _) hw]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [← Real.exp_add]
  congr 3
  ring

end BarrierManuscript
#print axioms BarrierManuscript.bsStockPut_external
#print axioms BarrierManuscript.bsStockPut_gaussian
#print axioms BarrierManuscript.shifted_phi_expectation
#print axioms BarrierManuscript.shifted_lognormal_put
