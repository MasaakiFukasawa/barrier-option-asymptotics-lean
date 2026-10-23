import ManuscriptRoughApplication
import ManuscriptMainTheorem
import ManuscriptRoughModelCoefficient

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The rough Bergomi price expansion with its explicit one-dimensional
coefficient. UI, joint convergence, and the coefficient identity are proved. -/
theorem rough_explicit_price_expansion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (C : RoughStockCoupling R)
    (hm : Measurable R.ξ) (hf : ContinuousAt R.ξ 0) (hf0 : R.ξ 0=D.v₀)
    (hHmax : R.H ≤ 1/2) (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ CoefficientProfile P (roughLimit R) b k R.H ∧
      ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        bsKilledPut (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*b))
          (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*k)) D.S₀
          (Real.sqrt (∫ r in (0:ℝ)..(θ n).val, R.ξ r))-
        roughBergomiCoefficient b k R.H C.ρ R.ν *
          D.S₀*Real.sqrt D.v₀*(θ n).val^(R.H+1/2))/(θ n).val^(R.H+1/2)) atTop (𝓝 0) := by
  simpa only [rough_model_coefficient P D R C b k hb] using
    rough_price_expansion P D R C hm hf hf0 hHmax b k hb hk

end BarrierManuscript
#print axioms BarrierManuscript.rough_explicit_price_expansion
