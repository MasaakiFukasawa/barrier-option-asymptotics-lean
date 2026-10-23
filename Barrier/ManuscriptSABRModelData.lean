import ManuscriptStockData
import ManuscriptSABRTangentLaw
import ManuscriptSABRVarianceLimit
import ManuscriptSABRForward

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- SABR-specific data added to the original stock SDE. No UI, price
expansion, or weak-limit conclusions are fields of this structure. -/
structure SABRVarianceData {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) where
  C : BrownianSystem P 1
  ν : ℝ
  ρ : ℝ
  correlation_bound : ρ^2 ≤ 1
  independent : IndepFun (brownianContinuousPath D.B) (brownianContinuousPath C) P
  variance : ∀ t : ℝ, 0 ≤ t → ∀ ω,
    D.V (realTimeClamp t) ω = D.v₀*Real.exp (2*ν*(ρ*D.B.W 0 (realTimeClamp t) ω+
      Real.sqrt (1-ρ^2)*C.W 0 (realTimeClamp t) ω)-ν^2*t)

noncomputable def sabrForward {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P} (R : SABRVarianceData D) (t : ℝ) : ℝ :=
  D.v₀*Real.exp (R.ν^2*t)

noncomputable def sabrVarianceTangent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P} (R : SABRVarianceData D)
    (t : ℝ) (ht : 0 < t) (ω : Ω) : ℝ :=
  2*R.ν*(R.ρ*(scaledBrownian D.B t ht).W 0 (realTimeClamp 1) ω+
    Real.sqrt (1-R.ρ^2)*(scaledBrownian R.C t ht).W 0 (realTimeClamp 1) ω)

theorem sabr_model_tangent_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : SABRVarianceData D)
    (t : ℝ) (ht : 0 < t) :
    HasLaw (sabrVarianceTangent R t ht) (gaussianReal 0 ⟨4*R.ν^2,by positivity⟩) P := by
  unfold sabrVarianceTangent
  exact sabr_tangent_gaussian P (scaledBrownian D.B t ht) (scaledBrownian R.C t ht)
    (scaled_brownian_paths_independent P D.B R.C R.independent t ht) R.ν R.ρ R.correlation_bound

theorem sabr_model_variance_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : SABRVarianceData D)
    (t : ℝ) (ht : 0 < t) (ω : Ω) :
    (D.V (realTimeClamp t) ω/sabrForward R t-1)/Real.sqrt t =
      (Real.exp (Real.sqrt t*sabrVarianceTangent R t ht ω-(Real.sqrt t)^2*(4*R.ν^2)/2)-1)/Real.sqrt t := by
  rw [R.variance t ht.le ω]
  unfold sabrForward sabrVarianceTangent
  rw [mul_div_mul_left _ _ D.hv₀.ne',← Real.exp_sub]
  rw [scaledBrownian_W P D.B t 1 ht zero_le_one,scaledBrownian_W P R.C t 1 ht zero_le_one,mul_one]
  have hs0 := (Real.sqrt_pos.mpr ht).ne'
  have hs := Real.sq_sqrt ht.le
  congr 3
  rw [hs]
  field_simp
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.sabr_model_tangent_law
#print axioms BarrierManuscript.sabr_model_variance_encoding
