import ManuscriptRemainder

open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem regular_scale_ratio_bound (θ v H : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hv : 0 ≤ v) (hH : H ≤ 1/2) :
    |Real.sqrt (v*θ)/θ^H| ≤ Real.sqrt v := by
  have hr : Real.sqrt θ ≤ θ^H := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1 hH
  rw [abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (v*θ)/θ^H)]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hθ H)).mpr
  rw [Real.sqrt_mul hv]
  exact mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg v)

/-- Assemble the two convergent leading coefficients and the three bounded
remainder coefficients. This is asymptotic bookkeeping; the pricing identity
and convergence of the coefficients must come from the preceding stochastic
and Gaussian lemmas. -/
theorem integrated_expansion_assembly (θ price base A B J₀ J₁ J₂ : ℕ → ℝ)
    (v H a b C : ℝ) (hθ : Tendsto θ atTop (𝓝 0)) (hp : ∀ n, 0 < θ n)
    (hθ1 : ∀ n, θ n ≤ 1) (hv : 0 ≤ v) (hH : H ≤ 1/2)
    (hA : Tendsto A atTop (𝓝 a)) (hB : Tendsto B atTop (𝓝 b))
    (h₀ : ∀ n, |J₀ n| ≤ C) (h₁ : ∀ n, |J₁ n| ≤ C) (h₂ : ∀ n, |J₂ n| ≤ C)
    (he : ∀ n, price n = base n - (2*Real.sqrt (v*θ n)*A n+(θ n)^H*B n+
      (Real.sqrt (v*θ n))^2*J₀ n+2*Real.sqrt (v*θ n)*(θ n)^H*J₁ n+
      (Real.sqrt (v*θ n))^2*(θ n)^H*J₂ n)) :
    Tendsto (fun n => (price n-base n+2*Real.sqrt (v*θ n)*a+(θ n)^H*b)/(θ n)^H)
      atTop (𝓝 0) := by
  have ha : Tendsto (fun n => a-A n) atTop (𝓝 0) := by simpa using hA.const_sub a
  have hscale := bounded_multiplier_vanishes (fun n => a-A n)
    (fun n => Real.sqrt (v*θ n)/(θ n)^H) (Real.sqrt v) ha
    (fun n => regular_scale_ratio_bound (θ n) v H (hp n) (hθ1 n) hv hH)
  have hrem := normalized_remainder_vanishes θ J₀ J₁ J₂ v H C hθ hp hv (by linarith) h₀ h₁ h₂
  have hb : Tendsto (fun n => b-B n) atTop (𝓝 0) := by simpa using hB.const_sub b
  have h := ((hscale.const_mul 2).add hb).sub hrem
  simp only [mul_zero,add_zero,sub_zero] at h
  apply h.congr
  intro n
  rw [he n]
  have hn : (θ n)^H ≠ 0 := (Real.rpow_pos_of_pos (hp n) H).ne'
  field_simp
  ring

/-- Comparison with an independently proved baseline expansion cancels its
coefficient, leaving the volatility-fluctuation correction. -/
theorem baseline_expansion_cancellation (price gaussian bs e h : ℕ → ℝ) (a b : ℝ)
    (hh : ∀ n, h n ≠ 0)
    (hp : Tendsto (fun n => (price n-gaussian n+2*e n*a+h n*b)/h n) atTop (𝓝 0))
    (hbs : Tendsto (fun n => (bs n-gaussian n+2*e n*a)/h n) atTop (𝓝 0)) :
    Tendsto (fun n => (price n-bs n+h n*b)/h n) atTop (𝓝 0) := by
  have h := hp.sub hbs
  simp only [sub_zero] at h
  apply h.congr
  intro n
  field_simp
  ring

end BarrierManuscript
#print axioms BarrierManuscript.regular_scale_ratio_bound
#print axioms BarrierManuscript.integrated_expansion_assembly
#print axioms BarrierManuscript.baseline_expansion_cancellation
