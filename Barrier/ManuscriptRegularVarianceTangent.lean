import ManuscriptRegularVarianceData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

theorem regular_drift_negligible {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RegularVarianceData (ι := ι) D)
    (θ : ℕ → ℝ) (hp : ∀ n,0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => regularDrift R (θ n) ω/Real.sqrt (θ n)) atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => ((regular_drift_measurable R (θ n) (hp n).le).div_const _).aestronglyMeasurable)
  filter_upwards with ω
  apply squeeze_zero_norm' _ (show Tendsto (fun n => R.L*Real.sqrt (θ n)) atTop (𝓝 0) from by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hθ).const_mul R.L)
  filter_upwards [hθ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  exact regular_scaled_drift_bound R (θ n) ⟨hp n,hn.le⟩ ω

noncomputable def regularVarianceTangent {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RegularVarianceData (ι := ι) D) (t : ℝ) (ht : 0 < t) (ω : Ω) : ℝ :=
  ∑ i,(R.initial i/D.v₀)*(scaledBrownian (R.B i) t ht).W 0 (realTimeClamp 1) ω

/-- The actual variance SDE implies its first-order tangent. -/
theorem regular_variance_remainder {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RegularVarianceData (ι := ι) D)
    (θ : ℕ → ℝ) (hp : ∀ n,0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
      (D.V (realTimeClamp (θ n)) ω/D.v₀-1)/(θ n)^(1/2:ℝ)-regularVarianceTangent R (θ n) (hp n) ω)
      atTop (fun _ => 0) := by
  have hN i := ito_endpoint_tangent P (R.B i) (R.G i) (R.N i)
    (R.adapted i) (R.continuous i) (R.localM i) (R.integral i)
    (R.initial i) (R.initial_value i) θ hp hθ
  have hsum := inMeasure_zero_finset_sum P Finset.univ _ (fun i _ => hN i)
  have h := inMeasure_zero_const_mul P
    (inMeasure_zero_add P hsum (regular_drift_negligible P D R θ hp hθ)) D.v₀⁻¹
  apply h.congr (fun n => ?_) Filter.EventuallyEq.rfl
  filter_upwards [R.variance] with ω hω
  rw [hω (θ n) (hp n).le,← Real.sqrt_eq_rpow]
  dsimp only [regularVarianceTangent,regularDrift]
  simp only [Finset.sum_sub_distrib,← Finset.sum_div, mul_sub,mul_add,Finset.mul_sum]
  have hs : ∑ i,D.v₀⁻¹*(R.initial i*(scaledBrownian (R.B i) (θ n) (hp n)).W 0 (realTimeClamp 1) ω)=
      ∑ i,(R.initial i/D.v₀)*(scaledBrownian (R.B i) (θ n) (hp n)).W 0 (realTimeClamp 1) ω := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  field_simp [D.hv₀.ne', (Real.sqrt_pos.mpr (hp n)).ne']
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.regular_drift_negligible
#print axioms BarrierManuscript.regular_variance_remainder
