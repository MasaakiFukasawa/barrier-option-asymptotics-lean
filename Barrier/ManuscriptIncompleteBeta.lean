import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def betaPrimitive (a t : ℝ) : ℝ := t^a*(1-t)^(-a)/a

theorem betaPrimitive_derivative (a t : ℝ) (ha : a ≠ 0) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (betaPrimitive a) (t^(a-1)*(1-t)^(-a-1)) t := by
  have h := ((Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.1.ne')).mul
    (((hasDerivAt_id t).const_sub 1).rpow_const
      (p := -a) (Or.inl (sub_pos.mpr ht.2).ne'))).div_const a
  convert h using 1
  · rfl
  · have h1 : t^a = t^(a-1)*t := by
      simpa only [sub_add_cancel] using Real.rpow_add_one ht.1.ne' (a-1)
    have h2 : (1-t)^(-a) = (1-t)^(-a-1)*(1-t) := by
      simpa only [sub_add_cancel] using Real.rpow_add_one (sub_pos.mpr ht.2).ne' (-a-1)
    simp only [id_eq]
    rw [h1,h2]
    field_simp
    <;> ring

/-- The incomplete-beta identity in the rough Bergomi calculation. Both
endpoint continuity and integrability at zero are proved for every a > 0. -/
theorem incomplete_beta_identity (a z : ℝ) (ha : 0 < a) (hz : z ∈ Ioo (0:ℝ) 1) :
    (∫ t in (0:ℝ)..z, t^(a-1)*(1-t)^(-a-1)) = (z/(1-z))^a/a := by
  have hpow (r : ℝ) : ContinuousOn (fun t : ℝ => (1-t)^r) (Icc 0 z) := by
    intro t ht
    exact (((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (sub_pos.mpr (lt_of_le_of_lt ht.2 hz.2)).ne'))).continuousWithinAt
  have hf : ContinuousOn (betaPrimitive a) (Icc 0 z) :=
    ((Real.continuous_rpow_const ha.le).continuousOn.mul (hpow (-a))).div_const a
  have hi : IntervalIntegrable (fun t : ℝ => t^(a-1)*(1-t)^(-a-1)) volume 0 z := by
    apply (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a-1)).mul_continuousOn
    simpa only [uIcc_of_le hz.1.le] using hpow (-a-1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz.1.le hf
    (fun t ht => betaPrimitive_derivative a t ha.ne' ⟨ht.1,ht.2.trans hz.2⟩) hi
  rw [h]
  simp only [betaPrimitive,Real.zero_rpow ha.ne',zero_mul,zero_div,sub_zero]
  rw [Real.div_rpow hz.1.le (sub_pos.mpr hz.2).le, Real.rpow_neg (sub_pos.mpr hz.2).le]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.betaPrimitive_derivative
#print axioms BarrierManuscript.incomplete_beta_identity
