import ManuscriptSquareMeanConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem abs_mean_zero_inMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : ∀ n,Integrable (X n) P)
    (hl : Tendsto (fun n => ∫ ω,|X n ω| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  have he n : eLpNorm (X n) 1 P=ENNReal.ofReal (∫ ω,|X n ω| ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hX n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX n)]
    simp only [Real.norm_eq_abs]
  have hn : Tendsto (fun n => eLpNorm (X n) 1 P) atTop (𝓝 0) := by
    simp_rw [he]
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.tendsto 0 |>.comp hl
  convert hn using 1
  funext n
  congr 1
  funext ω
  simp

end BarrierManuscript
#print axioms BarrierManuscript.abs_mean_zero_inMeasure
