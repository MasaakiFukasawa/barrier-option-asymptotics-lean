import ManuscriptLognormalFluctuation

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The exponential compensator makes the forward-normalized variance have
mean one, with its integrability proved from the Gaussian moment formula. -/
theorem gaussian_compensated_exponential (a : ℝ≥0) (e : ℝ) :
    Integrable (fun x : ℝ => Real.exp (e*x-e^2*(a:ℝ)/2)) (gaussianReal 0 a) ∧
    (∫ x : ℝ, Real.exp (e*x-e^2*(a:ℝ)/2) ∂gaussianReal 0 a) = 1 := by
  have hid : ∫ x : ℝ, Real.exp (e*x) ∂gaussianReal 0 a =
      Real.exp ((a:ℝ)*e^2/2) := by
    simpa only [mgf, id_eq, zero_mul, zero_add] using
      mgf_gaussianReal (HasLaw.id : HasLaw id (gaussianReal 0 a) (gaussianReal 0 a)) e
  have heq (x : ℝ) : Real.exp (e*x-e^2*(a:ℝ)/2) =
      Real.exp (e*x)*Real.exp (-(e^2*(a:ℝ)/2)) := by rw [← Real.exp_add]; congr 1
  simp_rw [heq]
  refine ⟨(integrable_exp_mul_gaussianReal e).mul_const _, ?_⟩
  rw [integral_mul_const, hid, ← Real.exp_add]
  convert Real.exp_zero using 1 <;> congr 1 <;> ring

/-- Gaussian marginals suffice for uniform integrability of the lognormal
variance family; no independence across maturities is required. -/
theorem lognormal_family_uniformIntegrable {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (a : ℝ≥0) (G : ι → Ω → ℝ)
    (hG : ∀ i, HasLaw (G i) (gaussianReal 0 a) P)
    (e : ι → ℝ) (he : ∀ i, 0 < e i) (he1 : ∀ i, e i ≤ 1) :
    UniformIntegrable (fun i ω =>
      (Real.exp (e i*G i ω-(e i)^2*(a:ℝ)/2)-1)/e i) 1 P := by
  apply uniformIntegrable_transfer (gaussianReal 0 a) P _ _
    (gaussian_lognormal_uniformIntegrable a e he he1)
  intro i
  simpa only [Function.comp_def, id_eq] using
    (HasLaw.id.identDistrib (hG i)).comp (show Measurable (fun x : ℝ =>
      (Real.exp (e i*x-(e i)^2*(a:ℝ)/2)-1)/e i) by fun_prop)

/-- Forward-normalized lognormal variance is centered exactly, at each
maturity, rather than merely centered asymptotically. -/
theorem lognormal_fluctuation_centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ≥0) (G : Ω → ℝ)
    (hG : HasLaw G (gaussianReal 0 a) P) (e : ℝ) :
    Integrable (fun ω => (Real.exp (e*G ω-e^2*(a:ℝ)/2)-1)/e) P ∧
    (∫ ω, (Real.exp (e*G ω-e^2*(a:ℝ)/2)-1)/e ∂P) = 0 := by
  have hi : Integrable (fun ω => Real.exp (e*G ω-e^2*(a:ℝ)/2)) P :=
    hG.integrable_comp (gaussian_compensated_exponential a e).1
  have hm : (∫ ω, Real.exp (e*G ω-e^2*(a:ℝ)/2) ∂P)=1 := by
    rw [show (fun ω => Real.exp (e*G ω-e^2*(a:ℝ)/2)) =
      (fun x : ℝ => Real.exp (e*x-e^2*(a:ℝ)/2)) ∘ G from rfl,
      hG.integral_comp (by fun_prop)]
    exact (gaussian_compensated_exponential a e).2
  refine ⟨(hi.sub (integrable_const 1)).div_const e, ?_⟩
  rw [integral_div, integral_sub hi (integrable_const 1), hm]
  simp

end BarrierManuscript
#print axioms BarrierManuscript.gaussian_compensated_exponential
#print axioms BarrierManuscript.lognormal_family_uniformIntegrable
#print axioms BarrierManuscript.lognormal_fluctuation_centered
