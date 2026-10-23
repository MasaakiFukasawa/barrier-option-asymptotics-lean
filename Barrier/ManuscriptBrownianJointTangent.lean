import ManuscriptBrownianPathScaling
import ManuscriptMaximumEncoding

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem independent_pair_identDistrib {Ω Γ E F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → E) (Y : Ω → F) (X' : Γ → E) (Y' : Γ → F)
    (hX : IdentDistrib X X' P Q) (hY : IdentDistrib Y Y' P Q)
    (hind : IndepFun X Y P) (hind' : IndepFun X' Y' Q) :
    IdentDistrib (fun ω => (X ω,Y ω)) (fun ω => (X' ω,Y' ω)) P Q := by
  refine ⟨hX.aemeasurable_fst.prodMk hY.aemeasurable_fst,
    hX.aemeasurable_snd.prodMk hY.aemeasurable_snd,?_⟩
  rw [hind.map_prod_eq_prod_map_map hX.aemeasurable_fst hY.aemeasurable_fst,
    hind'.map_prod_eq_prod_map_map hX.aemeasurable_snd hY.aemeasurable_snd,hX.map_eq,hY.map_eq]

/-- Joint Brownian scaling for the stock endpoint, its running maximum,
and the correlated SABR variance tangent. Marginal scaling alone would not
be enough to prove this statement. -/
theorem sabr_brownian_tangent_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (hind : IndepFun (brownianContinuousPath B) (brownianContinuousPath C) P)
    (θ : ℝ) (hp : 0 < θ) (ν ρ : ℝ) :
    IdentDistrib
      (fun ω => ((scaledBrownian B θ hp).W 0 (realTimeClamp 1) ω,
        2*ν*(ρ*(scaledBrownian B θ hp).W 0 (realTimeClamp 1) ω+
          Real.sqrt (1-ρ^2)*(scaledBrownian C θ hp).W 0 (realTimeClamp 1) ω),
        brownianMaximum (scaledBrownian B θ hp) ω))
      (fun ω => (B.W 0 (realTimeClamp 1) ω,
        2*ν*(ρ*B.W 0 (realTimeClamp 1) ω+Real.sqrt (1-ρ^2)*C.W 0 (realTimeClamp 1) ω),
        brownianMaximum B ω)) P P := by
  have hi := independent_pair_identDistrib P P _ _ _ _
    (brownian_continuous_path_common_law P (scaledBrownian B θ hp) B)
    (brownian_continuous_path_common_law P (scaledBrownian C θ hp) C)
    (scaled_brownian_paths_independent P B C hind θ hp) hind
  let f : C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ) → ℝ × ℝ × ℝ := fun p =>
    (p.1 1,2*ν*(ρ*p.1 1+Real.sqrt (1-ρ^2)*p.2 1),pathMaximum (pathRestriction 1 p.1))
  have hM : Continuous (fun g : C(ℝ≥0,ℝ) => pathMaximum (pathRestriction 1 g)) :=
    pathMaximum_lipschitz.continuous.comp (ContinuousMap.continuous_precomp _)
  have h1 : Measurable (fun p : C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ) => p.1 1) :=
    (show Measurable (fun g : C(ℝ≥0,ℝ) => g 1) from (continuous_eval_const 1).measurable).comp measurable_fst
  have h2 : Measurable (fun p : C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ) => p.2 1) :=
    (show Measurable (fun g : C(ℝ≥0,ℝ) => g 1) from (continuous_eval_const 1).measurable).comp measurable_snd
  have hf : Measurable f := h1.prodMk
    ((measurable_const.mul ((measurable_const.mul h1).add (measurable_const.mul h2))).prodMk
      (hM.measurable.comp measurable_fst))
  have h := hi.comp hf
  dsimp only [f,Function.comp_def] at h
  simp_rw [brownian_maximum_encoding P] at h
  simpa only [brownianContinuousPath,ContinuousMap.coe_mk,NNReal.coe_one] using h

end BarrierManuscript
#print axioms BarrierManuscript.independent_pair_identDistrib
#print axioms BarrierManuscript.sabr_brownian_tangent_law
