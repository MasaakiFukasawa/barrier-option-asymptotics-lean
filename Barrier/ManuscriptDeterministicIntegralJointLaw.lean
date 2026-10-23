import ManuscriptDeterministicIntegralPath

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The Brownian path together with a deterministic C1 Ito integral has
one common joint law. This retains its dependence on the whole path. -/
theorem deterministic_integral_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (R : ℝ≥0)
    (N M : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hM : LocalMProcessWitness P C.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N)
    (hMI : ItoCovarianceFormula P C.F (C.W 0) (fun z => g z.2) M) :
    IdentDistrib (fun ω => (brownianContinuousPath B ω,N (realTimeClamp R) ω))
      (fun ω => (brownianContinuousPath C ω,M (realTimeClamp R) ω)) P P := by
  have hBm := brownian_continuous_path_measurable B
  have hCm := brownian_continuous_path_measurable C
  have hNm := (hN.adapted P B.F _ (halfTimeClamp_finite R)).mono (B.le _) le_rfl
  have hMm := (hM.adapted P C.F _ (halfTimeClamp_finite R)).mono (C.le _) le_rfl
  have hleft : (fun ω => (brownianContinuousPath B ω,N (realTimeClamp R) ω)) =ᵐ[P]
      fun ω => (brownianContinuousPath B ω,deterministicIntegralPath g R (brownianContinuousPath B ω)) := by
    filter_upwards [deterministic_integral_path_encoding P B g hg N hN hNI R] with ω hω
    exact Prod.ext rfl hω
  have hright : (fun ω => (brownianContinuousPath C ω,M (realTimeClamp R) ω)) =ᵐ[P]
      fun ω => (brownianContinuousPath C ω,deterministicIntegralPath g R (brownianContinuousPath C ω)) := by
    filter_upwards [deterministic_integral_path_encoding P C g hg M hM hMI R] with ω hω
    exact Prod.ext rfl hω
  have h := (brownian_continuous_path_common_law P B C).comp
    (measurable_id.prodMk (deterministic_integral_path_measurable g hg R))
  exact (IdentDistrib.of_ae_eq (hBm.prodMk hNm).aemeasurable hleft).trans
    (h.trans (IdentDistrib.of_ae_eq (hCm.prodMk hMm).aemeasurable hright).symm)

end BarrierManuscript
#print axioms BarrierManuscript.deterministic_integral_joint_law
