import ManuscriptRoughModelData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The rough Bergomi compensator identifies the prescribed curve with
the actual forward variance, including integrability of the variance. -/
theorem rough_model_forward {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : RoughVarianceData D)
    (t : ℝ) (ht : 0 < t) :
    Integrable (D.V (realTimeClamp t)) P ∧
    (∫ ω, D.V (realTimeClamp t) ω ∂P)=R.ξ t := by
  let a : ℝ≥0 := ⟨R.ν^2,by positivity⟩
  let E : ℝ → ℝ := fun x => Real.exp (t^R.H*x-(t^R.H)^2*(a:ℝ)/2)
  have hl := rough_model_tangent_law P D R t ht
  have hi : Integrable (fun ω => E (roughVarianceTangent R t ω)) P :=
    hl.integrable_comp (gaussian_compensated_exponential a (t^R.H)).1
  have hm : (∫ ω, E (roughVarianceTangent R t ω) ∂P)=1 := by
    change (∫ ω, (E ∘ roughVarianceTangent R t) ω ∂P)=1
    rw [hl.integral_comp (show Measurable E by unfold E; fun_prop).aestronglyMeasurable]
    exact (gaussian_compensated_exponential a (t^R.H)).2
  have henc : D.V (realTimeClamp t)=fun ω => R.ξ t*E (roughVarianceTangent R t ω) := by
    funext ω
    have h := rough_model_variance_encoding P D R t ht ω
    have hs := (Real.rpow_pos_of_pos ht R.H).ne'
    have hf := (R.ξpos t ht.le).ne'
    have he : D.V (realTimeClamp t) ω/R.ξ t = E (roughVarianceTangent R t ω) := by
      have hh := (div_left_inj' hs).mp h
      change D.V (realTimeClamp t) ω/R.ξ t-1=E (roughVarianceTangent R t ω)-1 at hh
      linarith
    exact (div_eq_iff hf).mp he |>.trans (mul_comm _ _)
  rw [henc]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul,hm,mul_one]

end BarrierManuscript
#print axioms BarrierManuscript.rough_model_forward
