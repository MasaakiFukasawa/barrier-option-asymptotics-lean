import ManuscriptFiniteSecondMoment
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A Lipschitz derivative gives the quadratic Taylor bound needed for
the state-to-variance delta method. No stochastic remainder is assumed. -/
theorem smooth_quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : Differentiable ℝ f) (L : ℝ≥0)
    (hL : LipschitzWith L (fderiv ℝ f)) (x y : E) :
    |f y-f x-fderiv ℝ f x (y-x)|≤(L:ℝ)*‖y-x‖^2 := by
  let g := fun z => f z-f x-fderiv ℝ f x (z-x)
  have hd z : HasFDerivAt g (fderiv ℝ f z-fderiv ℝ f x) z := by
    convert ((hf z).hasFDerivAt.sub_const (f x)).sub
      ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)) using 1 <;>
      ext v <;> simp [g]
  have hbound z (hz : z ∈ Metric.closedBall x ‖y-x‖) :
      ‖fderiv ℝ f z-fderiv ℝ f x‖≤(L:ℝ)*‖y-x‖ := by
    have h := hL.dist_le_mul z x
    rw [dist_eq_norm,dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) L.coe_nonneg)
  have h := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le (x := x) (y := y)
    (fun z _ => (hd z).hasFDerivWithinAt) hbound
    (Metric.mem_closedBall_self (norm_nonneg _)) (by simp [Metric.mem_closedBall,dist_eq_norm])
  simpa [g,Real.norm_eq_abs,pow_two,mul_assoc] using h

theorem smooth_finite_quadratic_remainder {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (hf : Differentiable ℝ f) (L : ℝ≥0)
    (hL : LipschitzWith L (fderiv ℝ f)) (x y : ι → ℝ) :
    |f y-f x-fderiv ℝ f x (y-x)|≤(L:ℝ)*∑ i,(y i-x i)^2 := by
  exact (smooth_quadratic_remainder f hf L hL x y).trans
    (mul_le_mul_of_nonneg_left (pi_norm_sq_le_sum_sq (y-x)) L.coe_nonneg)

end BarrierManuscript
#print axioms BarrierManuscript.smooth_quadratic_remainder
#print axioms BarrierManuscript.smooth_finite_quadratic_remainder
