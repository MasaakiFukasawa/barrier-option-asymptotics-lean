import ManuscriptRoughIntegralJointLaw
import ManuscriptRoughCutSequence
import ManuscriptBrownianJointTangent

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The singular integral's common joint law includes an independent
Brownian driver, preserving the information needed by a correlated stock. -/
theorem rough_integral_two_path_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C B₀ C₀ : BrownianSystem P 1)
    (hind : IndepFun (brownianContinuousPath B) (brownianContinuousPath C) P)
    (hind₀ : IndepFun (brownianContinuousPath B₀) (brownianContinuousPath C₀) P)
    (H ν : ℝ) (hH : 0 < H) (N M : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hM : LocalMProcessWitness P B₀.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν 1 z.2) N)
    (hMI : ItoCovarianceFormula P B₀.F (B₀.W 0) (fun z => roughKernel H ν 1 z.2) M) :
    IdentDistrib
      (fun ω => ((pathRestriction 1 (brownianContinuousPath B ω),pathRestriction 1 (brownianContinuousPath C ω)),N (realTimeClamp 1) ω))
      (fun ω => ((pathRestriction 1 (brownianContinuousPath B₀ ω),pathRestriction 1 (brownianContinuousPath C₀ ω)),M (realTimeClamp 1) ω)) P P := by
  let F := fun n => deterministicIntegralPath (roughKernelExtension H ν 1 (roughUnitCut n)) (roughUnitCut n)
  have hF n : Measurable (F n) := deterministic_integral_path_measurable _
    (rough_kernel_extension_smooth H ν 1 (roughUnitCut n) (rough_unit_cut_lt n)) _
  have hres : Measurable (pathRestriction (1:ℝ≥0)) := (ContinuousMap.continuous_precomp _).measurable
  have hBp := brownian_continuous_path_measurable B
  have hCp := brownian_continuous_path_measurable C
  have hB₀p := brownian_continuous_path_measurable B₀
  have hC₀p := brownian_continuous_path_measurable C₀
  have hNm := (hN.adapted P B.F _ (halfTimeClamp_finite 1)).mono (B.le _) le_rfl
  have hMm := (hM.adapted P B₀.F _ (halfTimeClamp_finite 1)).mono (B₀.le _) le_rfl
  have hb := fixed_pair_weak_limit P
    (fun ω => (pathRestriction 1 (brownianContinuousPath B ω),pathRestriction 1 (brownianContinuousPath C ω)))
    (fun n ω => F n (brownianContinuousPath B ω)) _
    ((hres.comp hBp).prodMk (hres.comp hCp)) (fun n => (hF n).comp hBp) hNm
    (rough_integral_path_approximation P B H ν hH 1 roughUnitCut rough_unit_cut_lt rough_unit_cut_limit N hN hNI)
  have hc := fixed_pair_weak_limit P
    (fun ω => (pathRestriction 1 (brownianContinuousPath B₀ ω),pathRestriction 1 (brownianContinuousPath C₀ ω)))
    (fun n ω => F n (brownianContinuousPath B₀ ω)) _
    ((hres.comp hB₀p).prodMk (hres.comp hC₀p)) (fun n => (hF n).comp hB₀p) hMm
    (rough_integral_path_approximation P B₀ H ν hH 1 roughUnitCut rough_unit_cut_lt rough_unit_cut_limit M hM hMI)
  have hbase := independent_pair_identDistrib P P _ _ _ _
    (brownian_continuous_path_common_law P B B₀) (brownian_continuous_path_common_law P C C₀) hind hind₀
  apply identDistrib_of_weak_limits P P _ _ _ _ _ hb hc
  intro n
  exact hbase.comp (((hres.comp measurable_fst).prodMk (hres.comp measurable_snd)).prodMk
    ((hF n).comp measurable_fst))

end BarrierManuscript
#print axioms BarrierManuscript.rough_integral_two_path_law
