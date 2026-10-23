import ManuscriptSmoothStateData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- The smooth variance function and actual state SDE imply UI. Its
Lipschitz bound is used for the tails; the Taylor remainder alone would not
justify this step. -/
theorem smooth_state_uniformIntegrable {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SmoothStateData (ι := ι) (κ := κ) D) :
    UniformIntegrable (fun t : Ioc (0:ℝ) 1 => fun ω =>
      (D.V (realTimeClamp t.val) ω/D.v₀-1)/t.val^(1/2:ℝ)) 1 P := by
  have habs j : UniformIntegrable (fun t : Ioc (0:ℝ) 1 => fun ω =>
      |coordinateIncrement (R.coordinate j) t.val ω/Real.sqrt t.val|) 1 P := by
    apply uniformIntegrable_of_abs_le P _ _ (coordinate_uniformIntegrable (R.coordinate j))
      (fun t => (continuous_abs.measurable.comp
        ((coordinate_increment_measurable (R.coordinate j) t.val t.property.1.le).div_const _)).aestronglyMeasurable)
    exact fun _ => ae_of_all _ fun _ => by simp
  have hsum := ui_finset_sum P Finset.univ _ (fun j _ => habs j)
  have h := ui_const_mul P hsum ((R.value_bound:ℝ)/D.v₀)
  apply uniformIntegrable_of_abs_le P _ _ h
    (fun t => (((((D.hVa _ (halfTimeClamp_finite t.val)).mono (D.B.le _) le_rfl).div_const _).sub_const 1).div_const _).aestronglyMeasurable)
  intro t
  filter_upwards [R.variance t.val t.property.1.le] with ω hv
  have hl := R.lipschitz.dist_le_mul (smoothStatePoint R t.val ω) R.x₀
  rw [dist_eq_norm,dist_eq_norm,Real.norm_eq_abs] at hl
  have hn : ‖smoothStatePoint R t.val ω-R.x₀‖ ≤
      ∑ j,|coordinateIncrement (R.coordinate j) t.val ω| := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr
    intro j
    simpa only [Pi.sub_apply,smoothStatePoint,add_sub_cancel_left,Real.norm_eq_abs] using
      (Finset.single_le_sum (fun i _ => abs_nonneg (coordinateIncrement (R.coordinate i) t.val ω)) (Finset.mem_univ j))
  have hb := hl.trans (mul_le_mul_of_nonneg_left hn R.value_bound.coe_nonneg)
  have he : (D.V (realTimeClamp t.val) ω/D.v₀-1)/t.val^(1/2:ℝ)=
      (R.f (smoothStatePoint R t.val ω)-R.f R.x₀)/D.v₀/Real.sqrt t.val := by
    rw [← Real.sqrt_eq_rpow,R.initial_variance,hv]
    field_simp [D.hv₀.ne']
    rfl
  rw [he,abs_div,abs_div,abs_of_pos D.hv₀,abs_of_nonneg (Real.sqrt_nonneg t.val)]
  have hh := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hb D.hv₀.le) (Real.sqrt_nonneg t.val)
  convert hh using 1
  rw [abs_of_nonneg (mul_nonneg (div_nonneg R.value_bound.coe_nonneg D.hv₀.le)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))]
  simp only [abs_div,abs_of_nonneg (Real.sqrt_nonneg t.val),← Finset.sum_div]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_uniformIntegrable
