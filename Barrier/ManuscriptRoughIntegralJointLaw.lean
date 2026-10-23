import ManuscriptRoughPathApproximation
import ManuscriptFixedPairLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Equality of the joint laws of a Brownian path and its singular
Volterra integral, obtained from the explicit truncated path functionals. -/
theorem rough_integral_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (H ν : ℝ) (hH : 0 < H) (t r : ℝ≥0)
    (a : ℕ → ℝ≥0) (hat : ∀ n, a n < t) (halim : Tendsto (fun n => (a n:ℝ)) atTop (𝓝 (t:ℝ)))
    (N M : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hM : LocalMProcessWitness P C.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N)
    (hMI : ItoCovarianceFormula P C.F (C.W 0) (fun z => roughKernel H ν t z.2) M) :
    IdentDistrib (fun ω => (pathRestriction r (brownianContinuousPath B ω),N (realTimeClamp t) ω))
      (fun ω => (pathRestriction r (brownianContinuousPath C ω),M (realTimeClamp t) ω)) P P := by
  let F := fun n => deterministicIntegralPath (roughKernelExtension H ν t (a n)) (a n)
  have hF n : Measurable (F n) := deterministic_integral_path_measurable _
    (rough_kernel_extension_smooth H ν t (a n) (hat n)) _
  have hres : Measurable (pathRestriction r) := (ContinuousMap.continuous_precomp _).measurable
  have hBp := brownian_continuous_path_measurable B
  have hCp := brownian_continuous_path_measurable C
  have hBn : Measurable (N (realTimeClamp t)) := (hN.adapted P B.F _ (halfTimeClamp_finite t)).mono (B.le _) le_rfl
  have hCn : Measurable (M (realTimeClamp t)) := (hM.adapted P C.F _ (halfTimeClamp_finite t)).mono (C.le _) le_rfl
  have hb := fixed_pair_weak_limit P (fun ω => pathRestriction r (brownianContinuousPath B ω))
    (fun n ω => F n (brownianContinuousPath B ω)) _ (hres.comp hBp)
    (fun n => (hF n).comp hBp) hBn
    (rough_integral_path_approximation P B H ν hH t a hat halim N hN hNI)
  have hc := fixed_pair_weak_limit P (fun ω => pathRestriction r (brownianContinuousPath C ω))
    (fun n ω => F n (brownianContinuousPath C ω)) _ (hres.comp hCp)
    (fun n => (hF n).comp hCp) hCn
    (rough_integral_path_approximation P C H ν hH t a hat halim M hM hMI)
  apply identDistrib_of_weak_limits P P _ _ _ _ _ hb hc
  intro n
  exact (brownian_continuous_path_common_law P B C).comp (hres.prodMk (hF n))

end BarrierManuscript
#print axioms BarrierManuscript.rough_integral_joint_law
