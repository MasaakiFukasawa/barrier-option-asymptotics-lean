import ManuscriptRoughStockData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def roughLimit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RoughVarianceData D) (ω : Ω) : ℝ × ℝ × ℝ :=
  (D.B.W 0 (realTimeClamp 1) ω,R.N 1 (realTimeClamp 1) ω,brownianMaximum D.B ω)

theorem rough_stock_scaled_driver {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (C : RoughStockCoupling R) (θ : ℝ) (hθ : 0 < θ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    (scaledBrownian D.B θ hθ).W 0 (realTimeClamp t) ω=
      C.ρ*(scaledBrownian R.W θ hθ).W 0 (realTimeClamp t) ω+
      Real.sqrt (1-C.ρ^2)*(scaledBrownian C.C θ hθ).W 0 (realTimeClamp t) ω := by
  rw [scaledBrownian_W P D.B θ t hθ ht,scaledBrownian_W P R.W θ t hθ ht,
    scaledBrownian_W P C.C θ t hθ ht,C.driver (θ*t) (mul_nonneg hθ.le ht) ω]
  ring

theorem rough_tangent_joint_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (C : RoughStockCoupling R) (θ : ℝ) (hθ : 0 < θ) :
    IdentDistrib
      (fun ω => ((scaledBrownian D.B θ hθ).W 0 (realTimeClamp 1) ω,
        roughVarianceTangent R θ ω,brownianMaximum (scaledBrownian D.B θ hθ) ω))
      (roughLimit R) P P := by
  have hi := rough_maturity_joint_law P R.W C.C C.independent R.H R.ν R.hH
    (NNReal.mk θ hθ.le) hθ (R.N θ) (R.N 1) (R.localM θ hθ) (R.localM 1 zero_lt_one)
    (R.integral θ hθ) (R.integral 1 zero_lt_one)
  have h := hi.comp (rough_triple_map_measurable C.ρ)
  have he : (fun ω => roughTripleMap C.ρ
      ((pathRestriction 1 (brownianContinuousPath (scaledBrownian R.W θ hθ) ω),
        pathRestriction 1 (brownianContinuousPath (scaledBrownian C.C θ hθ) ω)),
        R.N θ (realTimeClamp θ) ω/θ^R.H)) =
      (fun ω => ((scaledBrownian D.B θ hθ).W 0 (realTimeClamp 1) ω,
        roughVarianceTangent R θ ω,brownianMaximum (scaledBrownian D.B θ hθ) ω)) := by
    funext ω
    exact rough_triple_encoding P _ _ _ C.ρ (rough_stock_scaled_driver P D R C θ hθ)
      (roughVarianceTangent R θ) ω
  have hf : (fun ω => roughTripleMap C.ρ
      ((pathRestriction 1 (brownianContinuousPath R.W ω),
        pathRestriction 1 (brownianContinuousPath C.C ω)),R.N 1 (realTimeClamp 1) ω))=roughLimit R := by
    funext ω
    exact rough_triple_encoding P _ _ _ C.ρ C.driver (R.N 1 (realTimeClamp 1)) ω
  change IdentDistrib _ _ P P at h
  rw [← he,← hf]
  exact h

end BarrierManuscript
#print axioms BarrierManuscript.rough_stock_scaled_driver
#print axioms BarrierManuscript.rough_tangent_joint_law
