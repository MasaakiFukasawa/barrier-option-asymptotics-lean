import ManuscriptSABRVariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The exact SABR forward variance derived from its Brownian exponential,
with integrability established before computing the expectation. -/
theorem sabr_forward_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (σ ν : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => σ^2*Real.exp (2*ν*W t ω-ν^2*(t:ℝ))) P ∧
    (∫ ω, σ^2*Real.exp (2*ν*W t ω-ν^2*(t:ℝ)) ∂P) = σ^2*Real.exp (ν^2*(t:ℝ)) := by
  have hG := hW.hasLaw_eval t
  have hi : Integrable (fun ω => Real.exp ((2*ν)*W t ω)) P :=
    hG.integrable_comp (integrable_exp_mul_gaussianReal (2*ν))
  have hmean : (∫ ω, Real.exp ((2*ν)*W t ω) ∂P) = Real.exp ((t:ℝ)*(2*ν)^2/2) := by
    simpa only [mgf,zero_mul,zero_add] using mgf_gaussianReal hG (2*ν)
  have he ω : σ^2*Real.exp (2*ν*W t ω-ν^2*(t:ℝ)) =
      σ^2*Real.exp (-(ν^2*(t:ℝ)))*Real.exp ((2*ν)*W t ω) := by
    simp_rw [mul_assoc]
    rw [← Real.exp_add]
    congr 2
    ring
  simp_rw [he]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul,hmean,mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- Dividing by the exact forward curve gives the compensated exponential
used in the uniform-integrability proof. -/
theorem sabr_forward_normalization (σ ν t w : ℝ) (hσ : σ ≠ 0) :
    (σ^2*Real.exp (2*ν*w-ν^2*t))/(σ^2*Real.exp (ν^2*t)) =
      Real.exp (2*ν*w-2*ν^2*t) := by
  rw [mul_div_mul_left _ _ (pow_ne_zero 2 hσ),← Real.exp_sub]
  congr 1
  ring

end BarrierManuscript
#print axioms BarrierManuscript.sabr_forward_variance
#print axioms BarrierManuscript.sabr_forward_normalization
