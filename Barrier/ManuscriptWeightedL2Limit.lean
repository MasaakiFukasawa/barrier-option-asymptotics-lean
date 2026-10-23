import ManuscriptSquareMeanConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Mean-square approximation transfers expectations against a bounded
measurable test on the same probability space. This retains all dependence
between the approximating integral and the barrier test. -/
theorem weighted_L2_expectation_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y Z : Ω → ℝ)
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 P)
    (hZ : Measurable Z) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ ω, |Z ω| ≤ C)
    (he : Tendsto (fun n => ∫ ω,(X n ω-Y ω)^2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, X n ω*Z ω ∂P) atTop (𝓝 (∫ ω, Y ω*Z ω ∂P)) := by
  have hi (U : Ω → ℝ) (hU : MemLp U 2 P) : Integrable (fun ω => U ω*Z ω) P := by
    apply ((hU.integrable (by norm_num)).norm.mul_const C).mono'
      (hU.aestronglyMeasurable.mul hZ.aestronglyMeasurable)
    exact ae_of_all _ fun ω => by
      change ‖U ω*Z ω‖ ≤ ‖U ω‖*C
      rw [Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg _)
  have hl := Asakura.Chapter6.square_mean_zero_implies_L1_zero P
    (fun n ω => X n ω-Y ω) (fun n => (hX n).sub hY) he
  have hz : Tendsto (fun n => C*(∫ ω,|X n ω-Y ω| ∂P)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hl.const_mul C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro n
  rw [← integral_sub (hi (X n) (hX n)) (hi Y hY)]
  calc
    _ ≤ ∫ ω, ‖X n ω*Z ω-Y ω*Z ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, C*|X n ω-Y ω| ∂P := by
      apply integral_mono_ae ((hi (X n) (hX n)).sub (hi Y hY)).norm
        ((((hX n).sub hY).integrable (by norm_num)).norm.const_mul C)
      exact ae_of_all _ fun ω => by
        change ‖X n ω*Z ω-Y ω*Z ω‖ ≤ C*‖X n ω-Y ω‖
        rw [← sub_mul,Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg (X n ω-Y ω))
    _ = _ := integral_const_mul _ _

end BarrierManuscript
#print axioms BarrierManuscript.weighted_L2_expectation_limit
