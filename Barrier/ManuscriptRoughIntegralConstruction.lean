import ManuscriptRoughIntegralLaw
import ManuscriptDeterministicItoConstruction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Existence of the actual singular Volterra integral and its exact law
are supplied by the stochastic-integration construction. -/
theorem rough_integral_exists {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν t : ℝ) (hH : 0 < H) (ht : 0 ≤ t) :
    ∃ N : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N ∧
      HasLaw (N (realTimeClamp t)) (gaussianReal 0 ⟨ν^2*t^(2*H),by positivity⟩) P := by
  have hm : Measurable (roughKernel H ν t) := by
    unfold roughKernel Asakura.mvnFutureFunction
    exact measurable_const.mul ((measurable_const.sub measurable_id).pow_const _ |>.indicator measurableSet_Ioc)
  obtain ⟨N,hN,hNI⟩ := deterministic_ito_exists P B _ hm
    (fun r _ => (rough_kernel_square_integrable H ν t hH ht).intervalIntegrable)
  exact ⟨N,hN,hNI,rough_integral_law P B H ν t hH ht N hN hNI⟩

end BarrierManuscript
#print axioms BarrierManuscript.rough_integral_exists
