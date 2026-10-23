import ManuscriptLSVApplication
import ManuscriptSmoothStatePriceDifference

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem regular_lsv_price_difference {Ω ι κ J : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype J]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : LSVModelData (ι := ι) (κ := κ) (J := J) D)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1 ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        physicalBlackScholesPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val-
        lsvCoefficient R/Real.sqrt D.v₀*
          (physicalBlackScholesPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val-
            physicalBachelierPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val))/(θ n).val) atTop (𝓝 0) := by
  have h := smooth_state_price_difference P D R.state b k hb hk
  rwa [regular_lsv_coefficient R] at h

end BarrierManuscript
#print axioms BarrierManuscript.regular_lsv_price_difference
