import ManuscriptSmoothStateJointLimit
import ManuscriptSmoothStateUI
import ManuscriptFiniteBrownianCoefficient
import ManuscriptMainTheorem

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- The price expansion derived from the original state SDE and smooth
variance function. Neither a variance SDE, a joint limit, nor UI is assumed.
The baseline uses the initial variance; the coefficient is explicit. -/
theorem smooth_state_price_expansion {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SmoothStateData (ι := ι) (κ := κ) D) (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1 ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        bsKilledPut (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*b))
          (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*k)) D.S₀
          (Real.sqrt (D.v₀*(θ n).val))-
        (smoothStateInitialDiffusion R R.stock/D.v₀/2)*gamma b k*D.S₀*Real.sqrt D.v₀*(θ n).val)/(θ n).val) atTop (𝓝 0) := by
  classical
  have hm i : Measurable ((R.B i).W 0 (realTimeClamp 1)) :=
    (((R.B i).martingale 0).adapted P (R.B i).F _ (halfTimeClamp_finite 1)).mono ((R.B i).le _) le_rfl
  have hB : Measurable (D.B.W 0 (realTimeClamp 1)) :=
    ((D.B.martingale 0).adapted P D.B.F _ (halfTimeClamp_finite 1)).mono (D.B.le _) le_rfl
  have hz : Measurable (smoothStateLimit R) := hB.prodMk
    ((Finset.measurable_sum _ (fun i _ => measurable_const.mul (hm i))).prodMk
      (brownianMaximum_measurable P D.B))
  obtain ⟨δ,hδ,hδ1,_,h⟩ := main_theorem P P D (fun _ => D.v₀) measurable_const
    continuousAt_const rfl (1/2) b k 1 (by norm_num) le_rfl hb hk zero_lt_one
    (smoothStateLimit R) hz
    (fun θ hθ => smooth_state_original_joint_limit P D R θ hθ) (smooth_state_uniformIntegrable P D R)
  refine ⟨δ,hδ,hδ1,?_⟩
  intro θ hθ
  have ha := finite_brownian_tangent_coefficient P R.B R.independent R.stock
    (fun i => smoothStateInitialDiffusion R i/D.v₀) b k hb hk
  rw [R.stock_driver] at ha
  have hh := h θ hθ
  dsimp only [smoothStateLimit] at hh
  rw [ha] at hh
  simpa only [show (1/2:ℝ)+1/2=1 by norm_num,Real.rpow_one,
    intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm ((θ _).val) D.v₀] using hh

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_price_expansion
