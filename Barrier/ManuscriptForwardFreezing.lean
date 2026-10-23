import ManuscriptATMVariance
import ManuscriptForwardDrift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A linear error in forward variance gives a quadratic error in integrated
variance. Measurability and the bound supply interval integrability. -/
theorem integrated_forward_error (v : ℝ → ℝ) (v₀ C θ : ℝ)
    (hm : Measurable v) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hb : ∀ t ∈ Icc (0:ℝ) θ, |v t-v₀| ≤ C*t) :
    |(∫ t in (0:ℝ)..θ, v t)-v₀*θ| ≤ C*θ^2/2 := by
  have hd : IntervalIntegrable (fun t => v t-v₀) volume 0 θ := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hθ).mpr
    apply (integrable_const (C*θ)).mono' (hm.sub measurable_const).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hb t ht).trans (mul_le_mul_of_nonneg_left ht.2 hC)
  have hi : IntervalIntegrable v volume 0 θ := by
    simpa only [sub_add_cancel] using hd.add (intervalIntegrable_const (b := θ) (a := (0:ℝ)) (c := v₀))
  have heq : (∫ t in (0:ℝ)..θ, v t)-v₀*θ = ∫ t in (0:ℝ)..θ, v t-v₀ := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp [mul_comm]
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le hθ
    (Filter.Eventually.of_forall fun t ht => show ‖v t-v₀‖ ≤ C*t from hb t ⟨ht.1.le,ht.2⟩)
    ((continuous_const.mul continuous_id).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := θ))
  have hiC : (∫ t : ℝ in (0:ℝ)..θ, C*t) = C*θ^2/2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  change |∫ t in (0:ℝ)..θ, v t-v₀| ≤ (∫ t in (0:ℝ)..θ, C*t) at h
  rwa [hiC] at h

/-- The square-root denominator is bounded away from zero by the positive
initial variance, giving the precise O(theta^(3/2)) volatility error. -/
theorem total_volatility_freezing_bound (A v C θ : ℝ)
    (hA : 0 ≤ A) (hv : 0 < v) (hC : 0 ≤ C) (hθ : 0 < θ)
    (herr : |A-v*θ| ≤ C*θ^2/2) :
    |Real.sqrt A-Real.sqrt (v*θ)| ≤ (C/(2*Real.sqrt v))*θ*Real.sqrt θ := by
  have hs : 0 < Real.sqrt (v*θ) := Real.sqrt_pos.mpr (mul_pos hv hθ)
  have hd : 0 < Real.sqrt A+Real.sqrt (v*θ) := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) hs
  have he : Real.sqrt A-Real.sqrt (v*θ) =
      (A-v*θ)/(Real.sqrt A+Real.sqrt (v*θ)) := by
    apply (eq_div_iff hd.ne').mpr
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt (mul_pos hv hθ).le]
  rw [he, abs_div, abs_of_pos hd]
  calc
    _ ≤ (C*θ^2/2)/Real.sqrt (v*θ) :=
      div_le_div₀ (by positivity) herr hs (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.sqrt_mul hv.le]
      field_simp
      nlinarith [Real.sq_sqrt hθ.le]

/-- Freezing the initial variance changes total volatility by o(theta). -/
theorem total_volatility_freezing_limit (A θ : ℕ → ℝ) (v C : ℝ)
    (hv : 0 < v) (hC : 0 ≤ C) (hA : ∀ n, 0 ≤ A n)
    (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (herr : ∀ n, |A n-v*θ n| ≤ C*(θ n)^2/2) :
    Tendsto (fun n => (Real.sqrt (A n)-Real.sqrt (v*θ n))/θ n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => (C/(2*Real.sqrt v))*Real.sqrt (θ n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero] using hθ.sqrt.const_mul (C/(2*Real.sqrt v))
  apply squeeze_zero_norm (fun n => ?_) hlim
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hp n)]
  apply (div_le_iff₀ (hp n)).mpr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using
    total_volatility_freezing_bound (A n) v C (θ n) (hA n) hv hC (hp n) (herr n)

end BarrierManuscript
#print axioms BarrierManuscript.integrated_forward_error
#print axioms BarrierManuscript.total_volatility_freezing_bound
#print axioms BarrierManuscript.total_volatility_freezing_limit
