import ManuscriptSABRModelData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem sabr_model_forward {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : SABRVarianceData D)
    (t : ℝ) (ht : 0 < t) :
    Integrable (D.V (realTimeClamp t)) P ∧
    (∫ ω, D.V (realTimeClamp t) ω ∂P)=sabrForward R t := by
  let a : ℝ≥0 := ⟨4*R.ν^2,by positivity⟩
  let E : ℝ → ℝ := fun x => Real.exp (Real.sqrt t*x-(Real.sqrt t)^2*(a:ℝ)/2)
  have hl := sabr_model_tangent_law P D R t ht
  have hi : Integrable (fun ω => E (sabrVarianceTangent R t ht ω)) P :=
    hl.integrable_comp (gaussian_compensated_exponential a (Real.sqrt t)).1
  have hm : (∫ ω, E (sabrVarianceTangent R t ht ω) ∂P)=1 := by
    change (∫ ω, (E ∘ sabrVarianceTangent R t ht) ω ∂P)=1
    rw [hl.integral_comp (show Measurable E by unfold E; fun_prop).aestronglyMeasurable]
    exact (gaussian_compensated_exponential a (Real.sqrt t)).2
  have henc : D.V (realTimeClamp t)=fun ω => sabrForward R t*E (sabrVarianceTangent R t ht ω) := by
    funext ω
    have h := sabr_model_variance_encoding P D R t ht ω
    have hs := (Real.sqrt_pos.mpr ht).ne'
    have hf : sabrForward R t ≠ 0 := mul_ne_zero D.hv₀.ne' (Real.exp_ne_zero _)
    have he : D.V (realTimeClamp t) ω/sabrForward R t = E (sabrVarianceTangent R t ht ω) := by
      have hh := (div_left_inj' hs).mp h
      change D.V (realTimeClamp t) ω/sabrForward R t-1=E (sabrVarianceTangent R t ht ω)-1 at hh
      linarith
    exact (div_eq_iff hf).mp he |>.trans (mul_comm _ _)
  rw [henc]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul,hm,mul_one]

end BarrierManuscript
#print axioms BarrierManuscript.sabr_model_forward
