import ManuscriptBrownianScaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def scaleContinuousPath (θ : ℝ) (hp : 0 < θ) (f : C(ℝ≥0,ℝ)) : C(ℝ≥0,ℝ) :=
  ⟨fun t => f (⟨θ,hp.le⟩*t)/Real.sqrt θ,
    (f.continuous.comp (continuous_const.mul continuous_id)).div_const _⟩

theorem scaleContinuousPath_measurable (θ : ℝ) (hp : 0 < θ) :
    Measurable (scaleContinuousPath θ hp) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (show Continuous (fun f : C(ℝ≥0,ℝ) => f (⟨θ,hp.le⟩*t)) from continuous_eval_const _).measurable.div_const _

theorem scaled_brownian_path_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (θ : ℝ) (hp : 0 < θ) :
    brownianContinuousPath (scaledBrownian B θ hp) =
      fun ω => scaleContinuousPath θ hp (brownianContinuousPath B ω) := by
  funext ω
  ext t
  change (scaledBrownian B θ hp).W 0 (realTimeClamp (t:ℝ)) ω =
    B.W 0 (realTimeClamp ((⟨θ,hp.le⟩:ℝ≥0)*t:ℝ)) ω/Real.sqrt θ
  rw [scaledBrownian_W P B θ (t:ℝ) hp t.coe_nonneg]

/-- Independence of entire Brownian paths is preserved by the common
maturity rescaling, not merely by separate marginal convergence. -/
theorem scaled_brownian_paths_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (hind : IndepFun (brownianContinuousPath B) (brownianContinuousPath C) P)
    (θ : ℝ) (hp : 0 < θ) :
    IndepFun (brownianContinuousPath (scaledBrownian B θ hp))
      (brownianContinuousPath (scaledBrownian C θ hp)) P := by
  rw [scaled_brownian_path_encoding P B θ hp,scaled_brownian_path_encoding P C θ hp]
  exact hind.comp (scaleContinuousPath_measurable θ hp) (scaleContinuousPath_measurable θ hp)

end BarrierManuscript
#print axioms BarrierManuscript.scaleContinuousPath_measurable
#print axioms BarrierManuscript.scaled_brownian_path_encoding
#print axioms BarrierManuscript.scaled_brownian_paths_independent
