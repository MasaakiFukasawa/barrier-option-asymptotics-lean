import ManuscriptRoughModelData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem rough_model_uniformIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : RoughVarianceData D) :
    UniformIntegrable (fun t : Ioc (0:ℝ) 1 => fun ω =>
      (D.V (realTimeClamp t.val) ω/R.ξ t.val-1)/t.val^R.H) 1 P := by
  have h := lognormal_family_uniformIntegrable P ⟨R.ν^2,by positivity⟩
    (fun t : Ioc (0:ℝ) 1 => roughVarianceTangent R t.val)
    (fun t => rough_model_tangent_law P D R t.val t.property.1)
    (fun t => t.val^R.H) (fun t => Real.rpow_pos_of_pos t.property.1 _)
    (fun t => Real.rpow_le_one t.property.1.le t.property.2 R.hH.le)
  convert h using 1
  funext t ω
  exact rough_model_variance_encoding P D R t.val t.property.1 ω

theorem rough_model_variance_remainder {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : RoughVarianceData D)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
      (D.V (realTimeClamp (θ n)) ω/R.ξ (θ n)-1)/(θ n)^R.H-
        roughVarianceTangent R (θ n) ω) atTop (fun _ => 0) := by
  have h := lognormal_linearization_inMeasure P ⟨R.ν^2,by positivity⟩
    (fun n => roughVarianceTangent R (θ n))
    (fun n => rough_model_tangent_law P D R (θ n) (hp n))
    (fun n => (θ n)^R.H) (fun n => (Real.rpow_pos_of_pos (hp n) _).ne')
    (hθ.rpow_const_nhds_zero R.hH)
  convert h using 1
  funext n ω
  rw [rough_model_variance_encoding P D R (θ n) (hp n) ω]
  rfl

end BarrierManuscript
#print axioms BarrierManuscript.rough_model_uniformIntegrable
#print axioms BarrierManuscript.rough_model_variance_remainder
