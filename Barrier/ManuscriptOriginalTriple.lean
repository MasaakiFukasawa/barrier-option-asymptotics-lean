import ManuscriptStockData
import ManuscriptFamilyTimeLimit

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def originalTriple {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P)
    (forward : ℝ → ℝ) (H θ : ℝ) (ω : Ω) : ℝ × ℝ × ℝ :=
  ((D.S (realTimeClamp θ) ω/D.S₀-1)/Real.sqrt (θ*D.v₀),
   (D.V (realTimeClamp θ) ω/forward θ-1)/θ^H,
   sSup (range (fun r : HalfClosedTime =>
     (D.S (min (realTimeClamp θ) r) ω/D.S₀-1)/Real.sqrt (θ*D.v₀))))

theorem original_triple_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (forward : ℝ → ℝ) (H θ b k : ℝ) (hp : 0 < θ) (M : NormalizedBarrierModel P b k)
    (hX : M.X=fun r ω => (D.S (linearClock θ hp (min (realTimeClamp 1) r)) ω/D.S₀-1)/Real.sqrt (θ*D.v₀))
    (hY : M.Y=fun z => (D.V (realTimeClamp (θ*z.2)) z.1/forward (θ*z.2)-1)/θ^H)
    (ω : Ω) : M.triple M.Y 1 ω=originalTriple D forward H θ ω := by
  have h1 : linearClock θ hp (realTimeClamp 1)=realTimeClamp θ := by
    simpa using linear_clock_finite θ hp 1 zero_le_one
  apply Prod.ext
  · simp only [NormalizedBarrierModel.triple,NormalizedBarrierModel.state,hX,min_self,h1,originalTriple]
  · apply Prod.ext
    · simp only [NormalizedBarrierModel.triple,hY,mul_one,originalTriple]
    · change prefixMaximum M.X M.hXc (realTimeClamp 1) ω = _
      unfold prefixMaximum pathMaximum
      congr 1
      ext y
      constructor
      · rintro ⟨r,hr⟩
        refine ⟨linearClock θ hp r,?_⟩
        change M.X (min (realTimeClamp 1) r) ω=y at hr
        rw [hX] at hr
        dsimp only at hr
        rw [← min_assoc,min_self,(linearClock θ hp).monotone.map_min,h1] at hr
        exact hr
      · rintro ⟨r,hr⟩
        refine ⟨(linearClock θ hp).symm r,?_⟩
        change M.X (min (realTimeClamp 1) ((linearClock θ hp).symm r)) ω=y
        rw [hX]
        dsimp only
        rw [← min_assoc,min_self,(linearClock θ hp).monotone.map_min,h1,(linearClock θ hp).apply_symm_apply]
        exact hr

end BarrierManuscript
#print axioms BarrierManuscript.original_triple_encoding
