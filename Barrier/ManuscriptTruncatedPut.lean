import ManuscriptTruncatedCall

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem put_gaussian_integrable (k x w : ℝ) (hw : 0 < w) :
    Integrable (fun y => max (k-y) 0*(phi ((y-x)/w)/w)) volume := by
  have h := (linear_gaussian_integrable k x w hw).neg.sup (integrable_zero _ _ _)
  convert! h using 1
  funext y
  simp only [Pi.sup_apply,Pi.neg_apply,Pi.zero_apply]
  rw [max_mul_of_nonneg _ _ (div_nonneg (phi_nonneg _) hw.le),zero_mul]
  congr 1
  ring

/-- For a strike below the barrier the put payoff already vanishes above
its strike. Thus the truncated Gaussian integral is the vanilla put. -/
theorem truncated_put_integral (b k x w : ℝ) (hk : k ≤ b) (hw : 0 < w) :
    (∫ y in Iio b, max (k-y) 0*(phi ((y-x)/w)/w)) = put k x w := by
  classical
  have he y : max (k-y) 0*(phi ((y-x)/w)/w) =
      (Iio k).indicator (fun y => (k-y)*(phi ((y-x)/w)/w)) y := by
    by_cases h : y < k
    · simp [h,Set.indicator_of_mem, max_eq_left (sub_nonneg.mpr h.le)]
    · have hy : k-y ≤ 0 := sub_nonpos.mpr (le_of_not_gt h)
      simp [h,Set.indicator_of_notMem,max_eq_right hy]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Iio,
    inter_eq_right.mpr (Iio_subset_Iio hk)]
  have hn y : (k-y)*(phi ((y-x)/w)/w) = -((y-k)*(phi ((y-x)/w)/w)) := by ring
  simp_rw [hn]
  rw [integral_neg,linear_gaussian_Iio k x w k hw]
  unfold put
  ring

end BarrierManuscript
#print axioms BarrierManuscript.put_gaussian_integrable
#print axioms BarrierManuscript.truncated_put_integral
