import ManuscriptSABRVariance
import ManuscriptLognormalLinearization

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem sabr_lognormal_encoding (ν w t : ℝ) (ht : 0 < t) :
    (Real.exp (2*ν*w-2*ν^2*t)-1)/Real.sqrt t =
      (Real.exp (Real.sqrt t*((2*ν/Real.sqrt t)*w)-(Real.sqrt t)^2*(4*ν^2)/2)-1)/Real.sqrt t := by
  have hs := Real.sq_sqrt ht.le
  have hs0 := (Real.sqrt_pos.mpr ht).ne'
  congr 3
  rw [hs]
  field_simp
  <;> ring

/-- The manuscript's scalar SABR variance limit, proved for the actual
Brownian exponential along every positive maturity sequence tending to zero. -/
theorem sabr_variance_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (ν : ℝ) (t : ℕ → ℝ≥0)
    (hp : ∀ n, 0 < t n) (hθ : Tendsto (fun n => (t n:ℝ)) atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω =>
      (Real.exp (2*ν*W (t n) ω-2*ν^2*(t n:ℝ))-1)/Real.sqrt (t n:ℝ))
      atTop id (fun _ => P) (gaussianReal 0 ⟨4*ν^2,by positivity⟩) := by
  have hpos (n : ℕ) : (0:ℝ)<(t n:ℝ) := by exact_mod_cast hp n
  have he0 : Tendsto (fun n => Real.sqrt (t n:ℝ)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hθ.sqrt
  have h := lognormal_family_weak_limit P ⟨4*ν^2,by positivity⟩
    (fun n ω => (2*ν/Real.sqrt (t n:ℝ))*W (t n) ω)
    (fun n => sabr_normalized_driver_law P W hW ν (t n) (hp n))
    (fun n => Real.sqrt (t n:ℝ)) (fun n => (Real.sqrt_pos.mpr (hpos n)).ne') he0
  convert h using 1
  funext n ω
  exact sabr_lognormal_encoding ν (W (t n) ω) (t n:ℝ) (hpos n)

end BarrierManuscript
#print axioms BarrierManuscript.sabr_lognormal_encoding
#print axioms BarrierManuscript.sabr_variance_weak_limit
