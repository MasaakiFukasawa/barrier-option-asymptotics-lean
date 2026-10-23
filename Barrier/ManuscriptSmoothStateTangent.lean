import ManuscriptSmoothStateRemainder

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

noncomputable def smoothVarianceTangent {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : SmoothStateData (ι := ι) (κ := κ) D) (t : ℝ) (ht : 0 < t) (ω : Ω) : ℝ :=
  ∑ i,(smoothStateInitialDiffusion R i/D.v₀)*(scaledBrownian (R.B i) t ht).W 0 (realTimeClamp 1) ω

/-- The variance tangent is derived directly from the original state SDE
and Taylor's theorem, without postulating a variance SDE or a joint limit. -/
theorem smooth_state_variance_remainder {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SmoothStateData (ι := ι) (κ := κ) D)
    (θ : ℕ → Ioc (0:ℝ) 1) (hθ : Tendsto (fun n => (θ n).val) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
      (D.V (realTimeClamp (θ n).val) ω/D.v₀-1)/(θ n).val^(1/2:ℝ)-
        smoothVarianceTangent R (θ n).val (θ n).property.1 ω) atTop (fun _ => 0) := by
  have hcoord j := inMeasure_zero_const_mul P
    (coordinate_tangent (R.coordinate j) (fun n => (θ n).val) (fun n => (θ n).property.1) hθ)
    (smoothStateGradient R j)
  have hsum := inMeasure_zero_finset_sum P Finset.univ _ (fun j _ => hcoord j)
  have h := inMeasure_zero_const_mul P
    (inMeasure_zero_add P hsum (smooth_state_remainder_inMeasure R θ hθ)) D.v₀⁻¹
  apply h.congr (fun n => ?_) Filter.EventuallyEq.rfl
  filter_upwards [R.variance (θ n).val (θ n).property.1.le] with ω hv
  rw [hv,← Real.sqrt_eq_rpow]
  dsimp only [smoothStateRemainder,smoothVarianceTangent,smoothStateInitialDiffusion]
  rw [R.initial_variance]
  have hswap : (∑ j,smoothStateGradient R j*(∑ i,(R.coordinate j).initial i*
      (scaledBrownian (R.B i) (θ n).val (θ n).property.1).W 0 (realTimeClamp 1) ω)) =
      ∑ i,(∑ j,smoothStateGradient R j*(R.coordinate j).initial i)*
      (scaledBrownian (R.B i) (θ n).val (θ n).property.1).W 0 (realTimeClamp 1) ω := by
    simp_rw [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    exact Finset.sum_comm
  simp only [mul_sub,Finset.sum_sub_distrib,← mul_div_assoc,← Finset.sum_div]
  rw [hswap]
  simp only [div_mul_eq_mul_div,← Finset.sum_div]
  change D.v₀⁻¹*(_+((R.f (smoothStatePoint R (θ n).val ω)-D.v₀-_)/_))=_
  have hF : R.f (smoothStatePoint R (θ n).val ω)=R.f (fun j => R.x₀ j+coordinateIncrement (R.coordinate j) (θ n).val ω) := rfl
  rw [hF]
  field_simp [D.hv₀.ne',(Real.sqrt_pos.mpr (θ n).property.1).ne']
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_variance_remainder
