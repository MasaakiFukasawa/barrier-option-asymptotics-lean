import ManuscriptLognormalLaw
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The normalized Brownian driver in the SABR variance fluctuation has a
Gaussian law independent of maturity. -/
theorem sabr_normalized_driver_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hW : IsPreBrownianReal W P)
    (ν : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    HasLaw (fun ω => (2*ν/Real.sqrt (t:ℝ))*W t ω)
      (gaussianReal 0 ⟨4*ν^2,by positivity⟩) P := by
  have htr : (0:ℝ)<(t:ℝ) := by exact_mod_cast ht
  have hs := Real.sq_sqrt htr.le
  have hs0 := (Real.sqrt_pos.mpr htr).ne'
  have h := gaussianReal_const_mul (hW.hasLaw_eval t) (2*ν/Real.sqrt (t:ℝ))
  have he : (NNReal.mk ((2*ν/Real.sqrt (t:ℝ))^2) (sq_nonneg _))*t = ⟨4*ν^2,by positivity⟩ := by
    apply NNReal.eq
    change (2*ν/Real.sqrt (t:ℝ))^2*(t:ℝ)=4*ν^2
    field_simp
    nlinarith [hs]
  simpa only [mul_zero,he] using h

/-- The actual forward-normalized SABR variance fluctuation is uniformly
integrable over every positive maturity at most one. -/
theorem sabr_variance_uniformIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (ν : ℝ) :
    UniformIntegrable (fun t : Ioc (0:ℝ≥0) 1 => fun ω =>
      (Real.exp (2*ν*W t ω-2*ν^2*(t:ℝ))-1)/Real.sqrt (t:ℝ)) 1 P := by
  let G := fun t : Ioc (0:ℝ≥0) 1 => fun ω => (2*ν/Real.sqrt (t:ℝ))*W t ω
  have hp (t : Ioc (0:ℝ≥0) 1) : (0:ℝ)<(t:ℝ) := by exact_mod_cast t.property.1
  have h := lognormal_family_uniformIntegrable P ⟨4*ν^2,by positivity⟩ G
    (fun t => sabr_normalized_driver_law P W hW ν t t.property.1)
    (fun t => Real.sqrt (t:ℝ)) (fun t => Real.sqrt_pos.mpr (hp t))
    (fun t => Real.sqrt_le_one.mpr (by exact_mod_cast t.property.2))
  convert h using 1
  funext t ω
  dsimp only [G]
  have hs0 := (Real.sqrt_pos.mpr (hp t)).ne'
  have hs := Real.sq_sqrt (hp t).le
  congr 3
  change 2*ν*W t ω-2*ν^2*(t:ℝ) = Real.sqrt (t:ℝ)*(2*ν/Real.sqrt (t:ℝ)*W t ω)-(Real.sqrt (t:ℝ))^2*(4*ν^2)/2
  rw [hs]
  field_simp
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.sabr_normalized_driver_law
#print axioms BarrierManuscript.sabr_variance_uniformIntegrable
