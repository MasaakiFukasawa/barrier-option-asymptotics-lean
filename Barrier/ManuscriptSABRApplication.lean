import ManuscriptSABRJointLimit
import ManuscriptSABRModelCoefficient
import ManuscriptMainTheorem

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The SABR price expansion, with UI, the full joint weak limit, and the
coefficient all derived from the original model data. -/
theorem sabr_price_expansion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SABRVarianceData D) (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        bsKilledPut (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*b))
          (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*k)) D.S₀
          (Real.sqrt (∫ r in (0:ℝ)..(θ n).val, sabrForward R r))-
        R.ν*R.ρ*gamma b k*D.S₀*Real.sqrt D.v₀*(θ n).val)/(θ n).val) atTop (𝓝 0) := by
  have hf : Continuous (sabrForward R) := by unfold sabrForward; fun_prop
  have h0 : sabrForward R 0=D.v₀ := by simp [sabrForward]
  have hB : Measurable (D.B.W 0 (realTimeClamp 1)) :=
    ((D.B.martingale 0).adapted P D.B.F _ (halfTimeClamp_finite 1)).mono (D.B.le _) le_rfl
  have hC : Measurable (R.C.W 0 (realTimeClamp 1)) :=
    ((R.C.martingale 0).adapted P R.C.F _ (halfTimeClamp_finite 1)).mono (R.C.le _) le_rfl
  have hz : Measurable (sabrLimit R) := hB.prodMk
    ((measurable_const.mul ((measurable_const.mul hB).add (measurable_const.mul hC))).prodMk
      (brownianMaximum_measurable P D.B))
  obtain ⟨δ,hδ,hδ1,_,h⟩ := main_theorem P P D (sabrForward R) hf.measurable
    hf.continuousAt h0 (1/2) b k 1 (by norm_num) le_rfl hb hk zero_lt_one
    (sabrLimit R) hz
    (fun θ hθ => sabr_original_joint_limit P D R (fun n => (θ n).val)
      (fun n => (θ n).property.1) hθ) (sabr_model_uniformIntegrable P D R)
  refine ⟨δ,hδ,hδ1,?_⟩
  intro θ hθ
  have ha := sabr_model_coefficient P D R b k hb hk
  have hh := h θ hθ
  dsimp only [sabrLimit] at hh
  rw [ha] at hh
  norm_num at hh
  exact hh

end BarrierManuscript
#print axioms BarrierManuscript.sabr_price_expansion
