import ManuscriptDeterministicItoDifference
import ManuscriptRoughKernelCut
import ManuscriptSquareMeanConvergence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Truncating the singular Volterra integrand gives a mean-square and
in-probability approximation on the original probability space. Both
integrals are identified by their actual Ito characterizations. -/
theorem rough_integral_cut_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν t : ℝ) (hH : 0 < H) (ht : 0 ≤ t)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hat : ∀ n, a n ≤ t)
    (halim : Tendsto a atTop (𝓝 t))
    (N : HalfClosedTime → Ω → ℝ) (M : ℕ → HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hM : ∀ n, LocalMProcessWitness P B.F (M n))
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N)
    (hMI : ∀ n, ItoCovarianceFormula P B.F (B.W 0) (fun z => roughCutKernel H ν t (a n) z.2) (M n)) :
    (∀ n, MemLp (fun ω => N (realTimeClamp t) ω-M n (realTimeClamp t) ω) 2 P ∧
      (∫ ω,(N (realTimeClamp t) ω-M n (realTimeClamp t) ω)^2 ∂P)=ν^2*(t-a n)^(2*H)) ∧
    TendstoInMeasure P (fun n ω => N (realTimeClamp t) ω-M n (realTimeClamp t) ω)
      atTop (fun _ => 0) := by
  have hg : Measurable (roughKernel H ν t) := by
    unfold roughKernel Asakura.mvnFutureFunction
    exact measurable_const.mul ((measurable_const.sub measurable_id).pow_const _ |>.indicator measurableSet_Ioc)
  have he n := deterministic_ito_difference_energy P B
    (roughKernel H ν t) (roughCutKernel H ν t (a n)) hg (hg.indicator measurableSet_Iic)
    (fun r _ => (rough_kernel_cut_square_integrable H ν t (a n) hH (ha n) (hat n)).intervalIntegrable)
    N (M n) hN (hM n) hNI (hMI n) t ht
  have he' n : (∫ ω,(N (realTimeClamp t) ω-M n (realTimeClamp t) ω)^2 ∂P)=ν^2*(t-a n)^(2*H) :=
    (he n).2.trans (rough_kernel_cut_error H ν t (a n) hH (ha n) (hat n))
  refine ⟨fun n => ⟨(he n).1,he' n⟩,?_⟩
  apply square_mean_zero_inMeasure P _ (fun n => (he n).1)
  simp_rw [he']
  have hl : Tendsto (fun n => t-a n) atTop (𝓝 0) := by
    simpa only [sub_self] using halim.const_sub t
  simpa only [mul_zero] using (hl.rpow_const_nhds_zero (by positivity : 0 < 2*H)).const_mul (ν^2)

end BarrierManuscript
#print axioms BarrierManuscript.rough_integral_cut_approximation
