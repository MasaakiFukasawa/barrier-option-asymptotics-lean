import ManuscriptBrownianCrossLaw
import ManuscriptRawBrownianScaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The local-martingale/covariance Brownian characterization has the
standard finite-dimensional Brownian laws. No Gaussian-law assumption is added. -/
theorem brownian_system_preBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) :
    IsPreBrownianReal (fun t : ℝ≥0 => B.W 0 (realTimeClamp t)) P := by
  obtain ⟨Γ,m,Q,hQ,W,hm,hc,hW,_⟩ := Asakura.brownian_motion_exists
  letI := m
  letI := hQ
  let B0 := naturalBrownianSystem Q W hW.toIsPreBrownianReal hm hc
  have hi := brownian_continuous_path_cross_law P Q B B0
  constructor
  intro I
  have heval : Measurable (fun f : C(ℝ≥0,ℝ) => fun i : I => f i.val) :=
    measurable_pi_iff.mpr (fun i => (continuous_eval_const i.val).measurable)
  have hh := hi.comp heval
  have he : (fun ω => (fun i : I => brownianContinuousPath B0 ω i.val))=
      (fun ω => I.restrict (W · ω)) := by
    funext ω i
    exact naturalBrownianSystem_finite Q W hW.toIsPreBrownianReal hm hc i.val ω
  change IdentDistrib (fun ω => I.restrict (fun t : ℝ≥0 => B.W 0 (realTimeClamp t) ω))
    (fun ω => fun i : I => brownianContinuousPath B0 ω i.val) P Q at hh
  rw [he] at hh
  exact hh.symm.hasLaw (hW.toIsPreBrownianReal.hasLaw I)

end BarrierManuscript
#print axioms BarrierManuscript.brownian_system_preBrownian
