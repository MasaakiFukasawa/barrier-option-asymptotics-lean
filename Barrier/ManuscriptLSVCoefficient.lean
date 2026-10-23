import ManuscriptSmoothStateData
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem square_variance_directional_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : E → ℝ) (x v : E) (hσ : DifferentiableAt ℝ σ x) :
    fderiv ℝ (fun y => (σ y)^2) x v=2*σ x*fderiv ℝ σ x v := by
  have h := hσ.hasFDerivAt.mul hσ.hasFDerivAt
  have he : σ*σ=(fun y => (σ y)^2) := by funext y; simp only [Pi.mul_apply,pow_two]
  rw [he] at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

/-- The coefficient in the manuscript, including the stock factor and
the factor correlations. State coordinates are stock, time, and factors. -/
theorem lsv_gradient_coefficient {κ J : Type*} [Fintype κ] [DecidableEq κ] [Fintype J]
    (σ : (Option (Option κ) → ℝ) → ℝ) (x : Option (Option κ) → ℝ)
    (hσ : DifferentiableAt ℝ σ x) (hp : 0 < σ x)
    (S : ℝ) (ρ : J → ℝ) (c : κ → J → ℝ)
    (g : Option (Option κ) → ℝ)
    (hstock : g none=S*σ x) (htime : g (some none)=0)
    (hfactor : ∀ i,g (some (some i))=∑ j,ρ j*c i j) :
    (∑ i,fderiv ℝ (fun y => (σ y)^2) x (Pi.single i 1)*g i)/(σ x)^2/2 =
      S*fderiv ℝ σ x (Pi.single none 1)+
        ∑ i,∑ j,ρ j*c i j*fderiv ℝ (fun y => Real.log (σ y)) x (Pi.single (some (some i)) 1) := by
  simp_rw [square_variance_directional_derivative σ x _ hσ]
  rw [Fintype.sum_option,Fintype.sum_option,hstock,htime]
  simp only [mul_zero,zero_add]
  simp_rw [hfactor,Finset.mul_sum]
  rw [fderiv.log hσ hp.ne']
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  have he i j : 2*σ x*fderiv ℝ σ x (Pi.single (some (some i)) 1)*(ρ j*c i j)=
      ((σ x)^2*2)*(ρ j*c i j*((σ x)⁻¹*fderiv ℝ σ x (Pi.single (some (some i)) 1))) := by
    field_simp [hp.ne']
    <;> ring
  simp_rw [he,← Finset.mul_sum]
  field_simp [hp.ne']
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.square_variance_directional_derivative
#print axioms BarrierManuscript.lsv_gradient_coefficient
