import ManuscriptSABRModelData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The UI hypothesis of the main theorem is discharged from the SABR
variance formula and independence of the two Brownian drivers. -/
theorem sabr_model_uniformIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : SABRVarianceData D) :
    UniformIntegrable (fun t : Ioc (0:ℝ) 1 => fun ω =>
      (D.V (realTimeClamp t.val) ω/sabrForward R t.val-1)/t.val^(1/2:ℝ)) 1 P := by
  have h := lognormal_family_uniformIntegrable P ⟨4*R.ν^2,by positivity⟩
    (fun t : Ioc (0:ℝ) 1 => sabrVarianceTangent R t.val t.property.1)
    (fun t => sabr_model_tangent_law P D R t.val t.property.1)
    (fun t => Real.sqrt t.val) (fun t => Real.sqrt_pos.mpr t.property.1)
    (fun t => Real.sqrt_le_one.mpr t.property.2)
  convert h using 1
  funext t ω
  rw [← Real.sqrt_eq_rpow]
  exact sabr_model_variance_encoding P D R t.val t.property.1 ω

/-- The variance-coordinate error vanishes in probability, jointly usable
with the independent stock path approximation. -/
theorem sabr_model_variance_remainder {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : SABRVarianceData D)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
      (D.V (realTimeClamp (θ n)) ω/sabrForward R (θ n)-1)/(θ n)^(1/2:ℝ)-sabrVarianceTangent R (θ n) (hp n) ω)
      atTop (fun _ => 0) := by
  have he : Tendsto (fun n => Real.sqrt (θ n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hθ.sqrt
  have h := lognormal_linearization_inMeasure P ⟨4*R.ν^2,by positivity⟩
    (fun n => sabrVarianceTangent R (θ n) (hp n))
    (fun n => sabr_model_tangent_law P D R (θ n) (hp n))
    (fun n => Real.sqrt (θ n)) (fun n => (Real.sqrt_pos.mpr (hp n)).ne') he
  convert h using 1
  funext n ω
  rw [← Real.sqrt_eq_rpow,sabr_model_variance_encoding P D R (θ n) (hp n) ω]
  rfl

end BarrierManuscript
#print axioms BarrierManuscript.sabr_model_uniformIntegrable
#print axioms BarrierManuscript.sabr_model_variance_remainder
