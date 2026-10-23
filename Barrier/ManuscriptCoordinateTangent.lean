import ManuscriptRegularCoordinate

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ι → BrownianSystem P 1}

theorem coordinate_scaled_drift_bound (R : RegularCoordinate B)
    (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) (ω : Ω) :
    |coordinateDrift R t ω/Real.sqrt t|≤R.L*Real.sqrt t := by
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg t)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr ht.1)).mpr
  calc
    _ ≤ R.L*t := coordinate_drift_bound R t ⟨ht.1.le,ht.2⟩ ω
    _ = _ := by rw [mul_assoc,Real.mul_self_sqrt ht.1.le]

theorem coordinate_uniformIntegrable (R : RegularCoordinate B) :
    UniformIntegrable (fun t : Ioc (0:ℝ) 1 => fun ω => coordinateIncrement R t.val ω/Real.sqrt t.val) 1 P := by
  have hb (t : Ioc (0:ℝ) 1) := coordinate_second_moment R t.val ⟨t.property.1.le,t.property.2⟩
  apply second_moment_uniformIntegrable P
    (fun t : Ioc (0:ℝ) 1 => fun ω => coordinateIncrement R t.val ω/Real.sqrt t.val)
    (fun t => (coordinate_increment_measurable R t.val t.property.1.le).div_const (Real.sqrt t.val))
    (fun t => by simpa only [div_eq_mul_inv,mul_comm] using (hb t).1.const_mul (Real.sqrt t.val)⁻¹)
    (coordinateMomentBound R) (by unfold coordinateMomentBound; positivity)
  intro t
  simp_rw [div_pow]
  rw [integral_div,Real.sq_sqrt t.property.1.le]
  exact (div_le_iff₀ t.property.1).mpr (hb t).2

theorem coordinate_drift_negligible (R : RegularCoordinate B)
    (θ : ℕ → ℝ) (hp : ∀ n,0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => coordinateDrift R (θ n) ω/Real.sqrt (θ n)) atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => ((coordinate_drift_measurable R (θ n) (hp n).le).div_const _).aestronglyMeasurable)
  filter_upwards with ω
  apply squeeze_zero_norm' _ (show Tendsto (fun n => R.L*Real.sqrt (θ n)) atTop (𝓝 0) from by
    simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hθ).const_mul R.L)
  filter_upwards [hθ.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  exact coordinate_scaled_drift_bound R (θ n) ⟨hp n,hn.le⟩ ω

theorem coordinate_tangent (R : RegularCoordinate B)
    (θ : ℕ → ℝ) (hp : ∀ n,0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => coordinateIncrement R (θ n) ω/Real.sqrt (θ n)-
      ∑ i,R.initial i*(scaledBrownian (B i) (θ n) (hp n)).W 0 (realTimeClamp 1) ω)
      atTop (fun _ => 0) := by
  have hN i := ito_endpoint_tangent P (B i) (R.G i) (R.N i)
    (R.adapted i) (R.continuous i) (R.localM i) (R.integral i)
    (R.initial i) (R.initial_value i) θ hp hθ
  have h := inMeasure_zero_add P (inMeasure_zero_finset_sum P Finset.univ _ (fun i _ => hN i))
    (coordinate_drift_negligible R θ hp hθ)
  convert h using 1
  funext n ω
  simp only [coordinateIncrement,add_div,Finset.sum_sub_distrib,Finset.sum_div]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.coordinate_scaled_drift_bound
#print axioms BarrierManuscript.coordinate_uniformIntegrable
#print axioms BarrierManuscript.coordinate_drift_negligible
#print axioms BarrierManuscript.coordinate_tangent
