import ManuscriptChapmanKolmogorov
import ManuscriptOtherBarrierAlgebra

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem linear_gaussian_integrable (k x w : ℝ) (hw : 0 < w) :
    Integrable (fun y => (y-k)*(phi ((y-x)/w)/w)) volume := by
  have h := (scaled_phi_moment_integrable x w hw.ne').sub ((scaled_phi_integrable x w hw.ne').const_mul k)
  convert! h using 1
  funext y
  dsimp only [Pi.sub_apply]
  ring

theorem linear_gaussian_Iio (k x w a : ℝ) (hw : 0 < w) :
    (∫ y in Iio a, (y-k)*(phi ((y-x)/w)/w)) =
      (x-k)*normalCDF ((a-x)/w)-w*phi ((a-x)/w) := by
  have he y : (y-k)*(phi ((y-x)/w)/w)=y*phi ((y-x)/w)/w-k*(phi ((y-x)/w)/w) := by ring
  simp_rw [he]
  rw [integral_sub (scaled_phi_moment_integrable x w hw.ne').integrableOn
    ((scaled_phi_integrable x w hw.ne').const_mul k).integrableOn,
    integral_const_mul,scaled_phi_truncated_moment x w a hw,scaled_phi_cdf x w a hw]
  ring

theorem call_gaussian_integrable (k x w : ℝ) (hw : 0 < w) :
    Integrable (fun y => max (y-k) 0*(phi ((y-x)/w)/w)) volume := by
  have h := (linear_gaussian_integrable k x w hw).sup (integrable_zero _ _ _)
  convert! h using 1
  funext y
  simp only [Pi.sup_apply,Pi.zero_apply]
  rw [max_mul_of_nonneg _ _ (div_nonneg (phi_nonneg _) hw.le),zero_mul]

theorem truncated_call_integral (b k x w : ℝ) (hk : k ≤ b) (hw : 0 < w) :
    (∫ y in Iio b, max (y-k) 0*(phi ((y-x)/w)/w)) = truncatedCall b k x w := by
  classical
  have he y : max (y-k) 0*(phi ((y-x)/w)/w) =
      (Ioi k).indicator (fun y => (y-k)*(phi ((y-x)/w)/w)) y := by
    by_cases h : k < y
    · simp [h,Set.indicator_of_mem, max_eq_left (sub_nonneg.mpr h.le)]
    · have hy : y-k ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
      simp [h,Set.indicator_of_notMem,max_eq_right hy]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Ioi]
  have hs : Iio b ∩ Ioi k = Ioo k b := by ext y; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo,and_comm]
  rw [hs,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hk,
    ← intervalIntegral.integral_Iio_sub_Iio' (linear_gaussian_integrable k x w hw).integrableOn (linear_gaussian_integrable k x w hw).integrableOn,
    linear_gaussian_Iio k x w b hw,linear_gaussian_Iio k x w k hw]
  unfold truncatedCall
  ring

end BarrierManuscript
#print axioms BarrierManuscript.linear_gaussian_integrable
#print axioms BarrierManuscript.linear_gaussian_Iio
#print axioms BarrierManuscript.call_gaussian_integrable
#print axioms BarrierManuscript.truncated_call_integral
