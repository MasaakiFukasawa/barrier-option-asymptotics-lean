import ManuscriptStockCoefficients

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem bounded_clock_total_limit (a : ℕ → ℝ → ℝ) (ha : ∀ n, Measurable (a n))
    (V : ℝ) (hb : ∀ n u, u ∈ Ioo (0:ℝ) 1 → |a n u| ≤ V)
    (hlim : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => a n u) atTop (𝓝 1)) :
    Tendsto (fun n => Real.sqrt (∫ u in (0:ℝ)..1, a n u)) atTop (𝓝 1) := by
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioo (0:ℝ) 1))
    (fun _ => V) (fun n => (ha n).aestronglyMeasurable) (integrable_const V)
    (fun n => (ae_restrict_mem measurableSet_Ioo).mono fun u hu => by simpa only [Real.norm_eq_abs] using hb n u hu)
    ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => hlim u hu)
  have hi : (∫ u in Ioo (0:ℝ) 1, (1:ℝ)) = 1 := by norm_num
  rw [hi] at h
  simpa only [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo,Real.sqrt_one] using h.sqrt

end BarrierManuscript
#print axioms BarrierManuscript.bounded_clock_total_limit
