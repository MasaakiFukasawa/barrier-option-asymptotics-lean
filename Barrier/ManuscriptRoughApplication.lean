import ManuscriptRoughJointLimit
import ManuscriptMainTheorem

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Application to the original rough Bergomi stock. UI and the joint limit
are derived; the coefficient is the main theorem's expectation functional.
Identification with the displayed one-dimensional coefficient is separate. -/
theorem rough_price_expansion {Ω : Type*} [MeasurableSpace Ω]
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
        alpha P (fun ω => (roughLimit R ω).1) (fun ω => (roughLimit R ω).2.1)
          (fun ω => (roughLimit R ω).2.2) b k R.H *
          D.S₀*Real.sqrt D.v₀*(θ n).val^(R.H+1/2))/(θ n).val^(R.H+1/2)) atTop (𝓝 0) := by
  have hB : Measurable (D.B.W 0 (realTimeClamp 1)) :=
    ((D.B.martingale 0).adapted P D.B.F _ (halfTimeClamp_finite 1)).mono (D.B.le _) le_rfl
  have hN : Measurable (R.N 1 (realTimeClamp 1)) :=
    ((R.localM 1 zero_lt_one).adapted P R.W.F _ (halfTimeClamp_finite 1)).mono (R.W.le _) le_rfl
  have hz : Measurable (roughLimit R) := hB.prodMk (hN.prodMk (brownianMaximum_measurable P D.B))
  exact main_theorem P P D R.ξ hm hf hf0 R.H b k 1 R.hH.le hHmax hb hk zero_lt_one
    (roughLimit R) hz
    (fun θ hθ => rough_original_joint_limit P D R C (fun n => (θ n).val)
      (fun n => (θ n).property.1) hθ) (rough_model_uniformIntegrable P D R)

end BarrierManuscript
#print axioms BarrierManuscript.rough_price_expansion
