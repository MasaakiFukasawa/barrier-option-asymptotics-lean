import ManuscriptSABRModelData
import ManuscriptSABRCoefficient

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Independence of the driving paths implies the precise residual
independence needed by the coefficient formula. -/
theorem sabr_residual_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : SABRVarianceData D) :
    IndepFun (R.C.W 0 (realTimeClamp 1))
      (fun ω => (D.B.W 0 (realTimeClamp 1) ω,brownianMaximum D.B ω)) P := by
  have he : Measurable (fun f : C(ℝ≥0,ℝ) => f 1) := (continuous_eval_const 1).measurable
  have hm : Measurable (fun f : C(ℝ≥0,ℝ) => pathMaximum (pathRestriction 1 f)) :=
    (pathMaximum_lipschitz.continuous.comp (ContinuousMap.continuous_precomp _)).measurable
  have h := R.independent.symm.comp he (he.prodMk hm)
  dsimp only [Function.comp_def] at h
  simp_rw [brownian_maximum_encoding P] at h
  simpa only [brownianContinuousPath,ContinuousMap.coe_mk,NNReal.coe_one] using h

theorem sabr_model_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (R : SABRVarianceData D)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    alpha P (D.B.W 0 (realTimeClamp 1))
      (fun ω => 2*R.ν*(R.ρ*D.B.W 0 (realTimeClamp 1) ω+
        Real.sqrt (1-R.ρ^2)*R.C.W 0 (realTimeClamp 1) ω))
      (brownianMaximum D.B) b k (1/2) = R.ν*R.ρ*gamma b k := by
  exact sabr_tangent_coefficient P D.B _
    (((R.C.martingale 0).adapted P R.C.F _ (halfTimeClamp_finite 1)).mono (R.C.le _) le_rfl)
    (brownian_endpoint_gaussian P R.C) (sabr_residual_independent P D R) R.ν R.ρ b k hb hk

end BarrierManuscript
#print axioms BarrierManuscript.sabr_residual_independent
#print axioms BarrierManuscript.sabr_model_coefficient
