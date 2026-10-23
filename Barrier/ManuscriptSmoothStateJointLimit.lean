import ManuscriptSmoothStateTangent
import ManuscriptOriginalPathTriple
import ManuscriptJointPathTransfer

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def smoothStateLimit {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : SmoothStateData (ι := ι) (κ := κ) D) (ω : Ω) : ℝ × ℝ × ℝ :=
  (D.B.W 0 (realTimeClamp 1) ω,
    ∑ i,(smoothStateInitialDiffusion R i/D.v₀)*(R.B i).W 0 (realTimeClamp 1) ω,brownianMaximum D.B ω)

/-- The original state SDE and smooth variance function imply the full joint
limit, including the maximum of the stock path. -/
theorem smooth_state_original_joint_limit {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SmoothStateData (ι := ι) (κ := κ) D)
    (τ : ℕ → Ioc (0:ℝ) 1) (hτ : Tendsto (fun n => (τ n).val) atTop (𝓝 0)) :
    TendstoInDistribution (fun n => originalTriple D (fun _ => D.v₀) (1/2) (τ n).val)
      atTop (smoothStateLimit R) (fun _ => P) P := by
  let θ := fun n => (τ n).val
  have hp : ∀ n,0 < θ n := fun n => (τ n).property.1
  have hθ : Tendsto θ atTop (𝓝 0) := hτ
  let X := fun n ω => ((scaledBrownian D.B (θ n) (hp n)).W 0 (realTimeClamp 1) ω,
    smoothVarianceTangent R (θ n) (hp n) ω,brownianMaximum (scaledBrownian D.B (θ n) (hp n)) ω)
  have hi : ∀ n,IdentDistrib (X n) (smoothStateLimit R) P P := by
    intro n
    have h := finite_brownian_tangent_law P R.B R.independent R.stock
      (fun i => smoothStateInitialDiffusion R i/D.v₀) (θ n) (hp n)
    rw [R.stock_driver] at h
    exact h
  have hx : TendstoInDistribution X atTop (smoothStateLimit R) (fun _ => P) P :=
    tendstoInDistribution_of_identDistrib 0 (fun n => (hi 0).trans (hi n).symm) (hi 0)
  have hg := hx.congr (fun n => Filter.Eventually.of_forall (fun ω =>
    (brownian_stopped_triple_encoding P (scaledBrownian D.B (θ n) (hp n))
      (smoothVarianceTangent R (θ n) (hp n)) ω).symm)) Filter.EventuallyEq.rfl
  have h := path_triple_weak_transfer P P (realTimeClamp 1)
    (fun n => normalizedStockStoppedPath D (θ n) (hp n))
    (fun n => brownianStoppedPath (scaledBrownian D.B (θ n) (hp n)) 1 zero_le_one)
    (fun n ω => (D.V (realTimeClamp (θ n)) ω/D.v₀-1)/(θ n)^(1/2:ℝ))
    (fun n => smoothVarianceTangent R (θ n) (hp n)) (smoothStateLimit R) hg
    (stock_path_difference_inMeasure P D θ hp hθ)
    (smooth_state_variance_remainder P D R τ hτ)
    (fun n => normalizedStockStoppedPath_measurable P D (θ n) (hp n))
    (fun n => ((((D.hVa _ (halfTimeClamp_finite (θ n))).mono (D.B.le _) le_rfl).div_const _).sub_const 1).div_const _)
  exact h.congr (fun n => Filter.Eventually.of_forall (fun ω =>
    original_path_triple_encoding P D (fun _ => D.v₀) (1/2) (θ n) (hp n) ω)) Filter.EventuallyEq.rfl

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_original_joint_limit
