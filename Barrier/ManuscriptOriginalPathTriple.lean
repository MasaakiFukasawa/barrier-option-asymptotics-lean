import ManuscriptStockPathApproximation
import ManuscriptOriginalTriple

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem original_path_triple_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (v : ℝ → ℝ) (H θ : ℝ) (hp : 0 < θ) (ω : Ω) :
    ((normalizedStockStoppedPath D θ hp ω) (realTimeClamp 1),
      (D.V (realTimeClamp θ) ω/v θ-1)/θ^H,
      pathMaximum (normalizedStockStoppedPath D θ hp ω)) = originalTriple D v H θ ω := by
  have h1 : linearClock θ hp (realTimeClamp 1)=realTimeClamp θ := by
    simpa using linear_clock_finite θ hp 1 zero_le_one
  apply Prod.ext
  · simp only [normalizedStockStoppedPath,ContinuousMap.coe_mk,min_self,h1,originalTriple]
  · apply Prod.ext
    · rfl
    · unfold pathMaximum originalTriple
      dsimp only
      congr 1
      ext y
      constructor
      · rintro ⟨r,hr⟩
        refine ⟨linearClock θ hp r,?_⟩
        change (D.S (linearClock θ hp (min (realTimeClamp 1) r)) ω/D.S₀-1)/Real.sqrt (θ*D.v₀)=y at hr
        rw [(linearClock θ hp).monotone.map_min,h1] at hr
        exact hr
      · rintro ⟨r,hr⟩
        refine ⟨(linearClock θ hp).symm r,?_⟩
        change (D.S (linearClock θ hp (min (realTimeClamp 1) ((linearClock θ hp).symm r))) ω/D.S₀-1)/Real.sqrt (θ*D.v₀)=y
        rw [(linearClock θ hp).monotone.map_min,h1,(linearClock θ hp).apply_symm_apply]
        exact hr

theorem brownian_stopped_triple_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (Y : Ω → ℝ) (ω : Ω) :
    ((brownianStoppedPath B 1 zero_le_one ω) (realTimeClamp 1),Y ω,
      pathMaximum (brownianStoppedPath B 1 zero_le_one ω)) =
      (B.W 0 (realTimeClamp 1) ω,Y ω,brownianMaximum B ω) := by
  simp only [brownianStoppedPath,ContinuousMap.coe_mk,min_self,brownianMaximum,continuousPath,brownianPrefix]

end BarrierManuscript
#print axioms BarrierManuscript.original_path_triple_encoding
#print axioms BarrierManuscript.brownian_stopped_triple_encoding
