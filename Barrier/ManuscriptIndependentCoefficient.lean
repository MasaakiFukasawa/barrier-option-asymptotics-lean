import ManuscriptAlpha
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A centered independent residual contributes zero against any measurable
function of the endpoint and maximum. No density for the residual is used. -/
theorem independent_residual_zero {Γ : Type*} [MeasurableSpace Γ]
    (Q : Measure Γ) [IsProbabilityMeasure Q] (X M R : Γ → ℝ)
    (hX : Measurable X) (hM : Measurable M) (hR : Measurable R)
    (hind : IndepFun R (fun ω => (X ω,M ω)) Q) (hzero : ∫ ω, R ω ∂Q=0)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    (∫ ω, R ω*f (X ω,M ω) ∂Q)=0 := by
  have hi := hind.comp measurable_id hf
  have he := hi.integral_fun_mul_eq_mul_integral hR.aestronglyMeasurable
    (hf.comp (hX.prodMk hM)).aestronglyMeasurable
  simpa only [Function.comp_def,id_eq,hzero,zero_mul] using he

/-- Centering of the normalized variance passes to its weak limit by UI. -/
theorem centered_weak_limit {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Y : ℕ → Ω → ℝ) (η : Γ → ℝ)
    (hlaw : TendstoInDistribution Y atTop η (fun _ => P) Q)
    (hui : UniformIntegrable Y 1 P) (hzero : ∀ n, ∫ ω, Y n ω ∂P=0) :
    Integrable η Q ∧ (∫ ω, η ω ∂Q)=0 := by
  obtain ⟨hi,he⟩ := weak_ui_expectation_limit P Q Y η hlaw hui
  refine ⟨hi,?_⟩
  have hz : Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique he hz

end BarrierManuscript
#print axioms BarrierManuscript.independent_residual_zero
#print axioms BarrierManuscript.centered_weak_limit
