import ManuscriptBrownianJointTangent

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- Simultaneous scaling of a finite independent family of entire Brownian
paths. This preserves dependence between the tangent and the barrier maximum. -/
theorem finite_brownian_path_scaling {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ι → BrownianSystem P 1)
    (hind : iIndepFun (fun i => brownianContinuousPath (B i)) P)
    (θ : ℝ) (hp : 0 < θ) :
    IdentDistrib (fun ω i => brownianContinuousPath (scaledBrownian (B i) θ hp) ω)
      (fun ω i => brownianContinuousPath (B i) ω) P P := by
  have hm i := (brownian_continuous_path_common_law P (scaledBrownian (B i) θ hp) (B i))
  have hs : iIndepFun (fun i => brownianContinuousPath (scaledBrownian (B i) θ hp)) P := by
    simp_rw [scaled_brownian_path_encoding P]
    exact hind.comp (fun _ => scaleContinuousPath θ hp) (fun _ => scaleContinuousPath_measurable θ hp)
  refine ⟨AEMeasurable.of_eval (fun i => (hm i).aemeasurable_fst),
    AEMeasurable.of_eval (fun i => (hm i).aemeasurable_snd), ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hm i).aemeasurable_fst) hs,
    iIndepFun.map_fun_eq_pi_map (fun i => (hm i).aemeasurable_snd) hind]
  congr 1
  funext i
  exact (hm i).map_eq

theorem finite_brownian_tangent_law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ι → BrownianSystem P 1)
    (hind : iIndepFun (fun i => brownianContinuousPath (B i)) P)
    (i₀ : ι) (a : ι → ℝ) (θ : ℝ) (hp : 0 < θ) :
    IdentDistrib
      (fun ω => ((scaledBrownian (B i₀) θ hp).W 0 (realTimeClamp 1) ω,
        ∑ i, a i*(scaledBrownian (B i) θ hp).W 0 (realTimeClamp 1) ω,
        brownianMaximum (scaledBrownian (B i₀) θ hp) ω))
      (fun ω => ((B i₀).W 0 (realTimeClamp 1) ω,
        ∑ i, a i*(B i).W 0 (realTimeClamp 1) ω,brownianMaximum (B i₀) ω)) P P := by
  let f : (ι → C(ℝ≥0,ℝ)) → ℝ × ℝ × ℝ := fun p =>
    (p i₀ 1, ∑ i, a i*p i 1,pathMaximum (pathRestriction 1 (p i₀)))
  have he i : Measurable (fun p : ι → C(ℝ≥0,ℝ) => p i 1) :=
    (continuous_eval_const 1).measurable.comp (measurable_pi_apply i)
  have hM : Continuous (fun g : C(ℝ≥0,ℝ) => pathMaximum (pathRestriction 1 g)) :=
    pathMaximum_lipschitz.continuous.comp (ContinuousMap.continuous_precomp _)
  have hf : Measurable f := (he i₀).prodMk
    ((Finset.measurable_sum _ (fun i _ => measurable_const.mul (he i))).prodMk
      (hM.measurable.comp (measurable_pi_apply i₀)))
  have h := (finite_brownian_path_scaling P B hind θ hp).comp hf
  dsimp only [f,Function.comp_def] at h
  simp_rw [brownian_maximum_encoding P] at h
  simpa only [brownianContinuousPath,ContinuousMap.coe_mk,NNReal.coe_one] using h

end BarrierManuscript
#print axioms BarrierManuscript.finite_brownian_path_scaling
#print axioms BarrierManuscript.finite_brownian_tangent_law
