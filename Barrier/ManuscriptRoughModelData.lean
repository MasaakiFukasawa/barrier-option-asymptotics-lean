import ManuscriptRoughIntegralLaw
import ManuscriptStockData
import ManuscriptLognormalLinearization

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The variance part of rough Bergomi. Each maturity's singular integral
is specified by the actual Ito characterization. Correlation with the stock
driver is needed separately for the joint limit, not for these marginal results. -/
structure RoughVarianceData {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) where
  W : BrownianSystem P 1
  H : ℝ
  ν : ℝ
  hH : 0 < H
  ξ : ℝ → ℝ
  ξpos : ∀ t, 0 ≤ t → 0 < ξ t
  N : ℝ → HalfClosedTime → Ω → ℝ
  localM : ∀ t, 0 < t → LocalMProcessWitness P W.F (N t)
  integral : ∀ t, 0 < t → ItoCovarianceFormula P W.F (W.W 0)
    (fun z => roughKernel H ν t z.2) (N t)
  variance : ∀ t, 0 < t → ∀ ω,
    D.V (realTimeClamp t) ω=ξ t*Real.exp (N t (realTimeClamp t) ω-ν^2*t^(2*H)/2)

noncomputable def roughVarianceTangent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RoughVarianceData D) (t : ℝ) (ω : Ω) : ℝ := R.N t (realTimeClamp t) ω/t^R.H

theorem rough_model_tangent_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (t : ℝ) (ht : 0 < t) :
    HasLaw (roughVarianceTangent R t) (gaussianReal 0 ⟨R.ν^2,by positivity⟩) P :=
  rough_normalized_integral_law P R.W R.H R.ν t R.hH ht (R.N t) (R.localM t ht) (R.integral t ht)

theorem rough_model_variance_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (t : ℝ) (ht : 0 < t) (ω : Ω) :
    (D.V (realTimeClamp t) ω/R.ξ t-1)/t^R.H =
      (Real.exp (t^R.H*roughVarianceTangent R t ω-(t^R.H)^2*R.ν^2/2)-1)/t^R.H := by
  rw [R.variance t ht ω,mul_div_cancel_left₀ _ (R.ξpos t ht.le).ne']
  have hp : t^(2*R.H)=(t^R.H)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [hp]
  unfold roughVarianceTangent
  have hn := (Real.rpow_pos_of_pos ht R.H).ne'
  congr 3
  field_simp
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.rough_model_tangent_law
#print axioms BarrierManuscript.rough_model_variance_encoding
