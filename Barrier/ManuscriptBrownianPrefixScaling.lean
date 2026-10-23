import ManuscriptRoughModelMoment

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem brownian_system_prefix_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (t : ℝ≥0) (ht : 0 < t) (ω : Ω) :
    pathMaximum (rawPrefixPath (fun s ω => B.W 0 (realTimeClamp s) ω)
      (fun ω => (brownianContinuousPath B ω).continuous) t ω)=
      Real.sqrt (t:ℝ)*brownianMaximum (scaledBrownian B t ht) ω := by
  let p := pathRestriction 1 (brownianContinuousPath (scaledBrownian B t ht) ω)
  have he (r : Icc (0:ℝ≥0) 1) :
      B.W 0 (realTimeClamp ((t*r.val:ℝ≥0):ℝ)) ω=Real.sqrt (t:ℝ)*p r := by
    change _=Real.sqrt (t:ℝ)*(scaledBrownian B t ht).W 0 (realTimeClamp (r.val:ℝ)) ω
    rw [scaledBrownian_W P B t r.val ht r.val.coe_nonneg,
      mul_div_cancel₀ _ (Real.sqrt_pos.mpr (show 0 < (t:ℝ) from ht)).ne']
    rfl
  have hpath : rawPrefixPath (fun s ω => B.W 0 (realTimeClamp s) ω)
      (fun ω => (brownianContinuousPath B ω).continuous) t ω=
      (⟨fun r => Real.sqrt (t:ℝ)*p r,p.continuous.const_mul _⟩ : C(Icc (0:ℝ≥0) 1,ℝ)) := by
    ext r
    exact he r
  rw [hpath,pathMaximum_mul_pos p _ (Real.sqrt_pos.mpr (show 0 < (t:ℝ) from ht)),brownian_maximum_encoding P]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_system_prefix_scaling
