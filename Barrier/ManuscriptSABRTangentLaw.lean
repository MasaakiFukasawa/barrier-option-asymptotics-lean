import ManuscriptBrownianJointTangent
import ManuscriptCorollary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem brownian_endpoint_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) :
    HasLaw (B.W 0 (realTimeClamp 1)) (gaussianReal 0 1) P := by
  convert scaled_brownian_gaussian_law P B 1 1 (by norm_num) (by norm_num) using 1 <;> norm_num
  congr 1

theorem sabr_tangent_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (hind : IndepFun (brownianContinuousPath B) (brownianContinuousPath C) P)
    (ν ρ : ℝ) (hρ : ρ^2 ≤ 1) :
    HasLaw (fun ω => 2*ν*(ρ*B.W 0 (realTimeClamp 1) ω+
      Real.sqrt (1-ρ^2)*C.W 0 (realTimeClamp 1) ω)) (gaussianReal 0 ⟨4*ν^2,by positivity⟩) P := by
  have hX := brownian_endpoint_gaussian P B
  have hZ := brownian_endpoint_gaussian P C
  have hpoint : Measurable (fun f : C(ℝ≥0,ℝ) => f 1) := (continuous_eval_const 1).measurable
  have hi : IndepFun (B.W 0 (realTimeClamp 1)) (C.W 0 (realTimeClamp 1)) P := by
    simpa only [Function.comp_def,brownianContinuousPath,ContinuousMap.coe_mk,NNReal.coe_one] using hind.comp hpoint hpoint
  let c := 2*ν*ρ
  let d := 2*ν*Real.sqrt (1-ρ^2)
  have hXY := hi.comp (show Measurable (fun x : ℝ => c*x) by fun_prop)
    (show Measurable (fun x : ℝ => d*x) by fun_prop)
  have hx := gaussianReal_const_mul hX c
  have hz := gaussianReal_const_mul hZ d
  have he : ((NNReal.mk (c^2) (sq_nonneg _))*1+(NNReal.mk (d^2) (sq_nonneg _))*1 : ℝ≥0) = ⟨4*ν^2,by positivity⟩ := by
    apply NNReal.eq
    change c^2*1+d^2*1=4*ν^2
    dsimp only [c,d]
    simp only [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hρ)]
    ring
  have hl : HasLaw (fun ω => c*B.W 0 (realTimeClamp 1) ω+d*C.W 0 (realTimeClamp 1) ω)
      (gaussianReal 0 ⟨4*ν^2,by positivity⟩) P := by
    refine ⟨hx.aemeasurable.add hz.aemeasurable,?_⟩
    have hh : P.map (fun ω => c*B.W 0 (realTimeClamp 1) ω+d*C.W 0 (realTimeClamp 1) ω) =
        gaussianReal (c*0+d*0) ((NNReal.mk (c^2) (sq_nonneg _))*1+(NNReal.mk (d^2) (sq_nonneg _))*1) :=
      gaussianReal_add_gaussianReal_of_indepFun hXY hx hz
    simpa only [Pi.add_apply,mul_zero,zero_add,he] using hh
  convert hl using 1
  funext ω
  dsimp only [c,d]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.brownian_endpoint_gaussian
#print axioms BarrierManuscript.sabr_tangent_gaussian
