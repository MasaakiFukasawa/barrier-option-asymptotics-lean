import ManuscriptRoughIntegralScaling
import ManuscriptRoughTwoPathLaw
import ManuscriptRoughIntegralConstruction

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Joint maturity scaling preserves both Brownian drivers and the actual
singular Volterra integral; no joint distribution is assumed. -/
theorem rough_maturity_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (hind : IndepFun (brownianContinuousPath B) (brownianContinuousPath C) P)
    (H ν : ℝ) (hH : 0 < H) (θ : ℝ≥0) (hθ : 0 < (θ:ℝ))
    (N L : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hL : LocalMProcessWitness P B.F L)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν θ z.2) N)
    (hLI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν 1 z.2) L) :
    IdentDistrib
      (fun ω => ((pathRestriction 1 (brownianContinuousPath (scaledBrownian B θ hθ) ω),
        pathRestriction 1 (brownianContinuousPath (scaledBrownian C θ hθ) ω)),
        N (realTimeClamp θ) ω/(θ:ℝ)^H))
      (fun ω => ((pathRestriction 1 (brownianContinuousPath B ω),
        pathRestriction 1 (brownianContinuousPath C ω)),L (realTimeClamp 1) ω)) P P := by
  obtain ⟨M,hM,hMI,_⟩ := rough_integral_exists P (scaledBrownian B θ hθ) H ν 1 hH (by norm_num)
  have he := rough_integral_scaling P B H ν hH θ hθ roughUnitCut
    rough_unit_cut_lt rough_unit_cut_limit N M hN hM hNI hMI
  have hl := rough_integral_two_path_law P (scaledBrownian B θ hθ) (scaledBrownian C θ hθ) B C
    (scaled_brownian_paths_independent P B C hind θ hθ) hind H ν hH M L hM hL hMI hLI
  have hm := ((hN.adapted P B.F _ (halfTimeClamp_finite θ)).mono (B.le _) le_rfl).div_const ((θ:ℝ)^H)
  have hr : Measurable (pathRestriction (1:ℝ≥0)) := (ContinuousMap.continuous_precomp _).measurable
  have hp := ((hr.comp (brownian_continuous_path_measurable (scaledBrownian B θ hθ))).prodMk
    (hr.comp (brownian_continuous_path_measurable (scaledBrownian C θ hθ)))).prodMk hm
  apply (IdentDistrib.of_ae_eq hp.aemeasurable ?_).trans hl
  filter_upwards [he] with ω hω
  exact congrArg (fun x => ((pathRestriction 1 (brownianContinuousPath (scaledBrownian B θ hθ) ω),
    pathRestriction 1 (brownianContinuousPath (scaledBrownian C θ hθ) ω)),x)) hω

end BarrierManuscript
#print axioms BarrierManuscript.rough_maturity_joint_law
