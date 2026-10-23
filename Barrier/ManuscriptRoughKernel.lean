import MVNKernelLp
import ManuscriptRoughCoefficient

open MeasureTheory Set
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def roughKernel (H ν t : ℝ) (s : ℝ) : ℝ :=
  ν*Real.sqrt (2*H)*Asakura.mvnFutureFunction H t s

theorem rough_kernel_memLp (H ν t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    MemLp (roughKernel H ν t) 2 volume :=
  (Asakura.mvn_future_function_memLp H t hH ht).const_mul _

theorem rough_kernel_square_integrable (H ν t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    Integrable (fun s => roughKernel H ν t s^2) volume :=
  (memLp_two_iff_integrable_sq (rough_kernel_memLp H ν t hH ht).aestronglyMeasurable).mp
    (rough_kernel_memLp H ν t hH ht)

theorem rough_kernel_variance (H ν t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    (∫ s in 0..t, roughKernel H ν t s^2)=ν^2*t^(2*H) := by
  have he : (∫ s in 0..t, roughKernel H ν t s^2)=
      (ν*Real.sqrt (2*H))^2*(∫ s in Ioc 0 t,((t-s)^(H-1/2))^2) := by
    rw [intervalIntegral.integral_of_le ht,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only [roughKernel,Asakura.mvnFutureFunction,Set.indicator_of_mem hs,mul_pow]
  rw [he,Asakura.mvn_future_variance H t hH ht,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*H)]
  field_simp

end BarrierManuscript
#print axioms BarrierManuscript.rough_kernel_memLp
#print axioms BarrierManuscript.rough_kernel_square_integrable
#print axioms BarrierManuscript.rough_kernel_variance
