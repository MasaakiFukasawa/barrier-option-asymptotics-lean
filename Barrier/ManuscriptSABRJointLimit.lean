import ManuscriptSABRModelUI
import ManuscriptOriginalPathTriple
import ManuscriptJointPathTransfer
import ManuscriptBrownianJointTangent

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def sabrLimit {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : SABRVarianceData D) (ω : Ω) : ℝ × ℝ × ℝ :=
  (D.B.W 0 (realTimeClamp 1) ω,
    2*R.ν*(R.ρ*D.B.W 0 (realTimeClamp 1) ω+
      Real.sqrt (1-R.ρ^2)*R.C.W 0 (realTimeClamp 1) ω),brownianMaximum D.B ω)

/-- The full joint hypothesis follows from the stock SDE and the explicit
SABR variance dynamics, including the running maximum coordinate. -/
theorem sabr_original_joint_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SABRVarianceData D) (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n)
    (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInDistribution (fun n => originalTriple D (sabrForward R) (1/2) (θ n))
      atTop (sabrLimit R) (fun _ => P) P := by
  let X := fun n ω => ((scaledBrownian D.B (θ n) (hp n)).W 0 (realTimeClamp 1) ω,
    sabrVarianceTangent R (θ n) (hp n) ω,brownianMaximum (scaledBrownian D.B (θ n) (hp n)) ω)
  have hi : ∀ n, IdentDistrib (X n) (sabrLimit R) P P := fun n =>
    sabr_brownian_tangent_law P D.B R.C R.independent (θ n) (hp n) R.ν R.ρ
  have hx : TendstoInDistribution X atTop (sabrLimit R) (fun _ => P) P :=
    tendstoInDistribution_of_identDistrib 0 (fun n => (hi 0).trans (hi n).symm) (hi 0)
  have hg := hx.congr (fun n => Filter.Eventually.of_forall (fun ω =>
    (brownian_stopped_triple_encoding P (scaledBrownian D.B (θ n) (hp n))
      (sabrVarianceTangent R (θ n) (hp n)) ω).symm)) (Filter.EventuallyEq.rfl)
  have h := path_triple_weak_transfer P P (realTimeClamp 1)
    (fun n => normalizedStockStoppedPath D (θ n) (hp n))
    (fun n => brownianStoppedPath (scaledBrownian D.B (θ n) (hp n)) 1 zero_le_one)
    (fun n ω => (D.V (realTimeClamp (θ n)) ω/sabrForward R (θ n)-1)/(θ n)^(1/2:ℝ))
    (fun n => sabrVarianceTangent R (θ n) (hp n)) (sabrLimit R) hg
    (stock_path_difference_inMeasure P D θ hp hθ)
    (sabr_model_variance_remainder P D R θ hp hθ)
    (fun n => normalizedStockStoppedPath_measurable P D (θ n) (hp n))
    (fun n => ((((D.hVa _ (halfTimeClamp_finite (θ n))).mono (D.B.le _) le_rfl).div_const _).sub_const 1).div_const _)
  exact h.congr (fun n => Filter.Eventually.of_forall (fun ω =>
    original_path_triple_encoding P D (sabrForward R) (1/2) (θ n) (hp n) ω)) (Filter.EventuallyEq.rfl)

end BarrierManuscript
#print axioms BarrierManuscript.sabr_original_joint_limit
