import ManuscriptIndependentCoefficient

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Reduction of an integrable linear signal plus independent centered noise
against a bounded measurable endpoint/maximum weight. -/
theorem linear_signal_weight {Γ : Type*} [MeasurableSpace Γ]
    (Q : Measure Γ) [IsProbabilityMeasure Q] (X M R : Γ → ℝ)
    (hX : Measurable X) (hM : Measurable M) (hR : Measurable R)
    (hiX : Integrable X Q) (hiR : Integrable R Q)
    (hind : IndepFun R (fun ω => (X ω,M ω)) Q) (hzero : ∫ ω, R ω ∂Q=0)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (C a : ℝ) (hbound : ∀ q, |f q| ≤ C) :
    (∫ ω, f (X ω,M ω)*(a*X ω+R ω) ∂Q) = a*(∫ ω, f (X ω,M ω)*X ω ∂Q) := by
  have hm := hf.comp (hX.prodMk hM)
  have hi (Y : Γ → ℝ) (hY : Integrable Y Q) : Integrable (fun ω => f (X ω,M ω)*Y ω) Q := by
    apply (hY.norm.const_mul C).mono' (hm.aestronglyMeasurable.mul hY.aestronglyMeasurable)
    exact ae_of_all _ fun ω => by
      simpa only [Pi.mul_apply,Function.comp_def,norm_mul,Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right (hbound (X ω,M ω)) (abs_nonneg (Y ω))
  have he ω : f (X ω,M ω)*(a*X ω+R ω) = a*(f (X ω,M ω)*X ω)+f (X ω,M ω)*R ω := by ring
  simp_rw [he]
  rw [integral_add ((hi X hiX).const_mul a) (hi R hiR),integral_const_mul]
  have hz := independent_residual_zero Q X M R hX hM hR hind hzero f hf
  simp_rw [mul_comm (f (X _,M _))] 
  rw [hz,add_zero]

end BarrierManuscript
#print axioms BarrierManuscript.linear_signal_weight
