import ManuscriptRoughModelData
import ManuscriptRoughMaturityLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The rough variance is coupled to the stock by two independent Brownian
paths. This specifies dynamics, not a limiting distribution. -/
structure RoughStockCoupling {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RoughVarianceData D) where
  C : BrownianSystem P 1
  ρ : ℝ
  correlation_bound : ρ^2 ≤ 1
  independent : IndepFun (brownianContinuousPath R.W) (brownianContinuousPath C) P
  driver : ∀ t : ℝ, 0 ≤ t → ∀ ω,
    D.B.W 0 (realTimeClamp t) ω = ρ*R.W.W 0 (realTimeClamp t) ω+
      Real.sqrt (1-ρ^2)*C.W 0 (realTimeClamp t) ω

noncomputable def roughTripleMap (ρ : ℝ)
    (p : (C(Icc (0:ℝ≥0) 1,ℝ) × C(Icc (0:ℝ≥0) 1,ℝ)) × ℝ) : ℝ × ℝ × ℝ :=
  let f := ρ • p.1.1 + Real.sqrt (1-ρ^2) • p.1.2
  (f ⟨1,by simp⟩,p.2,pathMaximum f)

theorem rough_triple_map_measurable (ρ : ℝ) : Measurable (roughTripleMap ρ) := by
  have hc : Continuous (fun p : (C(Icc (0:ℝ≥0) 1,ℝ) × C(Icc (0:ℝ≥0) 1,ℝ)) × ℝ =>
      ρ • p.1.1 + Real.sqrt (1-ρ^2) • p.1.2) :=
    (continuous_fst.fst.const_smul ρ).add (continuous_fst.snd.const_smul (Real.sqrt (1-ρ^2)))
  exact ((continuous_eval_const _).comp hc).measurable.prodMk
    (measurable_snd.prodMk (pathMaximum_lipschitz.continuous.comp hc).measurable)

theorem rough_triple_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B W C : BrownianSystem P 1)
    (ρ : ℝ) (hdriver : ∀ t : ℝ, 0 ≤ t → ∀ ω,
      B.W 0 (realTimeClamp t) ω=ρ*W.W 0 (realTimeClamp t) ω+
        Real.sqrt (1-ρ^2)*C.W 0 (realTimeClamp t) ω)
    (Y : Ω → ℝ) (ω : Ω) :
    roughTripleMap ρ ((pathRestriction 1 (brownianContinuousPath W ω),
      pathRestriction 1 (brownianContinuousPath C ω)),Y ω)=
      (B.W 0 (realTimeClamp 1) ω,Y ω,brownianMaximum B ω) := by
  have he : ρ • pathRestriction 1 (brownianContinuousPath W ω)+
      Real.sqrt (1-ρ^2) • pathRestriction 1 (brownianContinuousPath C ω)=
        pathRestriction 1 (brownianContinuousPath B ω) := by
    ext s
    exact (hdriver s.val s.val.coe_nonneg ω).symm
  unfold roughTripleMap
  rw [he]
  dsimp only
  rw [brownian_maximum_encoding P]
  rfl

end BarrierManuscript
#print axioms BarrierManuscript.rough_triple_map_measurable
#print axioms BarrierManuscript.rough_triple_encoding
