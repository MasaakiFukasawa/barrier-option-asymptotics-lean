import Chapter6SquareMeanToL1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem square_mean_zero_inMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, MemLp (X n) 2 P)
    (hl : Tendsto (fun n => ∫ ω,X n ω^2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  have hL := Asakura.Chapter6.square_mean_zero_implies_L1_zero P X hX hl
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
  have he n : eLpNorm (X n) 1 P=ENNReal.ofReal (∫ ω,|X n ω| ∂P) := by
    have hi := (hX n).integrable (by norm_num)
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    simp only [Real.norm_eq_abs]
  have hn : Tendsto (fun n => eLpNorm (X n) 1 P) atTop (𝓝 0) := by
    simp_rw [he]
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.tendsto 0 |>.comp hL
  convert hn using 1
  funext n
  congr 1
  funext ω
  simp

end BarrierManuscript
#print axioms BarrierManuscript.square_mean_zero_inMeasure
