import ManuscriptSmoothStateData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

noncomputable def smoothStateRemainder {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : SmoothStateData (ι := ι) (κ := κ) D) (t : ℝ) (ω : Ω) : ℝ :=
  (R.f (smoothStatePoint R t ω)-R.f R.x₀-
    ∑ j,smoothStateGradient R j*coordinateIncrement (R.coordinate j) t ω)/Real.sqrt t

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}

theorem smooth_state_remainder_moment (R : SmoothStateData (ι := ι) (κ := κ) D)
    (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
    Integrable (smoothStateRemainder R t) P ∧
      (∫ ω,|smoothStateRemainder R t ω| ∂P) ≤
        (R.derivative_bound:ℝ)*(∑ j,coordinateMomentBound (R.coordinate j))*Real.sqrt t := by
  have hq j := coordinate_second_moment (R.coordinate j) t ⟨ht.1.le,ht.2⟩
  have hqi j := (memLp_two_iff_integrable_sq (hq j).1.aestronglyMeasurable).mp (hq j).1
  let Y : Ω → ℝ := fun ω => (R.derivative_bound:ℝ)*(∑ j,(coordinateIncrement (R.coordinate j) t ω)^2)/Real.sqrt t
  have hiY : Integrable Y P := ((integrable_finset_sum _ (fun j _ => hqi j)).const_mul _).div_const _
  have hm : Measurable (smoothStateRemainder R t) :=
    (((R.differentiable.continuous.measurable.comp (smooth_state_measurable R t ht.1.le)).sub_const _).sub
      (Finset.measurable_sum _ (fun j _ => measurable_const.mul
        (coordinate_increment_measurable (R.coordinate j) t ht.1.le)))).div_const _
  have hb ω : |smoothStateRemainder R t ω|≤Y ω := by
    have h := smooth_finite_quadratic_remainder R.f R.differentiable R.derivative_bound
      R.derivative_lipschitz R.x₀ (smoothStatePoint R t ω)
    rw [smooth_state_linearization R t ω] at h
    simp only [smoothStatePoint,add_sub_cancel_left] at h
    dsimp only [smoothStateRemainder,Y]
    rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg t)]
    exact div_le_div_of_nonneg_right h (Real.sqrt_nonneg t)
  have hi : Integrable (smoothStateRemainder R t) P := hiY.mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => hb ω)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω,Y ω ∂P := integral_mono_ae hi.abs hiY (ae_of_all _ hb)
    _ = (R.derivative_bound:ℝ)*(∑ j,∫ ω,(coordinateIncrement (R.coordinate j) t ω)^2 ∂P)/Real.sqrt t := by
      rw [integral_div,integral_const_mul,integral_finset_sum _ (fun j _ => hqi j)]
    _ ≤ (R.derivative_bound:ℝ)*(∑ j,coordinateMomentBound (R.coordinate j)*t)/Real.sqrt t := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hq j).2)) R.derivative_bound.coe_nonneg)
        (Real.sqrt_nonneg t)
    _ = _ := by
      rw [← Finset.sum_mul]
      have hs := Real.sq_sqrt ht.1.le
      have hp := (Real.sqrt_pos.mpr ht.1).ne'
      field_simp
      rw [hs]

theorem smooth_state_remainder_inMeasure (R : SmoothStateData (ι := ι) (κ := κ) D)
    (θ : ℕ → Ioc (0:ℝ) 1) (hθ : Tendsto (fun n => (θ n).val) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => smoothStateRemainder R (θ n).val) atTop (fun _ => 0) := by
  apply abs_mean_zero_inMeasure P _ (fun n => (smooth_state_remainder_moment R (θ n).val (θ n).property).1)
  apply squeeze_zero (fun n => integral_nonneg (fun ω => abs_nonneg _))
    (fun n => (smooth_state_remainder_moment R (θ n).val (θ n).property).2)
  simpa using (Real.continuous_sqrt.tendsto 0 |>.comp hθ).const_mul
    ((R.derivative_bound:ℝ)*(∑ j,coordinateMomentBound (R.coordinate j)))

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_remainder_moment
#print axioms BarrierManuscript.smooth_state_remainder_inMeasure
