import ManuscriptExponentialPathLimit
import ManuscriptUniformIntegrability
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A global exponential remainder estimate, including large Gaussian tails. -/
theorem abs_exp_sub_one_le (z : ℝ) :
    |Real.exp z - 1| ≤ |z| * Real.exp |z| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (z : ℂ) 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one] at h
  rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

/-- A maturity-independent Gaussian-exponential envelope for the normalized
lognormal variance fluctuation. -/
theorem lognormal_fluctuation_bound (e x a : ℝ)
    (he : 0 < e) (he1 : e ≤ 1) (ha : 0 ≤ a) :
    |(Real.exp (e*x-e^2*a/2)-1)/e| ≤
      Real.exp a * (Real.exp (2*x) + Real.exp (-2*x)) := by
  let d := |x| + a/2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hz : |e*x-e^2*a/2| ≤ e*d := by
    rw [show e*x-e^2*a/2=e*(x-e*a/2) by ring, abs_mul, abs_of_pos he]
    apply mul_le_mul_of_nonneg_left _ he.le
    calc
      |x-e*a/2| ≤ |x|+|e*a/2| := abs_sub _ _
      _ = |x|+e*a/2 := by rw [abs_of_nonneg (show 0 ≤ e*a/2 by positivity)]
      _ ≤ d := by dsimp [d]; nlinarith
  have hzd : |e*x-e^2*a/2| ≤ d := hz.trans (mul_le_of_le_one_left hd he1)
  have hdd : d ≤ Real.exp d := by linarith [Real.add_one_le_exp d]
  have htail : Real.exp (2*|x|) ≤ Real.exp (2*x)+Real.exp (-2*x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-2*x)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      rw [show 2 * -x = -2*x by ring]
      linarith [Real.exp_pos (2*x)]
  calc
    _ ≤ (|e*x-e^2*a/2| * Real.exp |e*x-e^2*a/2|)/e := by
      rw [abs_div, abs_of_pos he]
      exact div_le_div_of_nonneg_right (abs_exp_sub_one_le _) he.le
    _ ≤ (e*d*Real.exp d)/e := by
      apply div_le_div_of_nonneg_right _ he.le
      exact mul_le_mul hz (Real.exp_le_exp.mpr hzd) (Real.exp_pos _).le (by positivity)
    _ = d*Real.exp d := by field_simp
    _ ≤ Real.exp d * Real.exp d := mul_le_mul_of_nonneg_right hdd (Real.exp_pos _).le
    _ = Real.exp a * Real.exp (2*|x|) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [d]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le

/-- Uniform integrability follows from a single integrable Gaussian envelope,
not from pointwise convergence of the lognormal fluctuations. -/
theorem gaussian_lognormal_uniformIntegrable {ι : Type*}
    (a : ℝ≥0) (e : ι → ℝ) (he : ∀ i, 0 < e i) (he1 : ∀ i, e i ≤ 1) :
    UniformIntegrable (fun i (x : ℝ) =>
      (Real.exp (e i*x-(e i)^2*(a:ℝ)/2)-1)/e i) 1 (gaussianReal 0 a) := by
  let g : ℝ → ℝ := fun x => Real.exp (a:ℝ)*(Real.exp (2*x)+Real.exp (-2*x))
  have hi : Integrable g (gaussianReal 0 a) :=
    ((integrable_exp_mul_gaussianReal (μ := 0) (v := a) 2).add
      (integrable_exp_mul_gaussianReal (μ := 0) (v := a) (-2))).const_mul _
  apply uniformIntegrable_of_abs_le (gaussianReal 0 a) (fun _ : ι => g) _
    (uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hi))
  · intro i
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (Real.exp (e i*x-(e i)^2*(a:ℝ)/2)-1)/e i)).measurable.aestronglyMeasurable
  · intro i
    filter_upwards [] with x
    exact (lognormal_fluctuation_bound _ _ _ (he i) (he1 i) a.coe_nonneg).trans (le_abs_self _)

/-- The scalar lognormal expansion, on a common Gaussian realization. -/
theorem lognormal_fluctuation_limit (e : ℕ → ℝ) (he : ∀ n, e n ≠ 0)
    (he0 : Tendsto e atTop (𝓝 0)) (x a : ℝ) :
    Tendsto (fun n => (Real.exp (e n*x-(e n)^2*a/2)-1)/e n) atTop (𝓝 x) := by
  have h := (expPathExtension_continuous id (fun _ : ℝ => x) (fun _ => a)
    continuous_id continuous_const continuous_const).continuousAt.tendsto.comp he0
  simpa only [Function.comp_def, id_eq, expPathExtension_formula _ _ _ (he _),
    expPathExtension_zero] using h

end BarrierManuscript
#print axioms BarrierManuscript.abs_exp_sub_one_le
#print axioms BarrierManuscript.lognormal_fluctuation_bound
#print axioms BarrierManuscript.gaussian_lognormal_uniformIntegrable
#print axioms BarrierManuscript.lognormal_fluctuation_limit
