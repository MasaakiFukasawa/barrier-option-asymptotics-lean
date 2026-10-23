import ManuscriptDeterministicIntegralPath
import ManuscriptRoughKernelScaling

open MeasureTheory Set
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem deterministic_integral_path_scaling (g h : ℝ → ℝ) (a : ℝ≥0)
    (θ c : ℝ) (hθ : 0 < θ)
    (hv : h (θ*a)=c*g a)
    (hd : ∀ s : ℝ, 0 ≤ s → s ≤ (a:ℝ) → deriv h (θ*s)*θ=c*deriv g s)
    (f : C(ℝ≥0,ℝ)) :
    deterministicIntegralPath h ((NNReal.mk θ hθ.le)*a) f=
      c*Real.sqrt θ*deterministicIntegralPath g a (scaleContinuousPath θ hθ f) := by
  have hs := (Real.sqrt_pos.mpr hθ).ne'
  have he (s : ℝ) (hs0 : 0 ≤ s) :
      (scaleContinuousPath θ hθ f) (Real.toNNReal s)=f (Real.toNNReal (θ*s))/Real.sqrt θ := by
    change f ((NNReal.mk θ hθ.le)*Real.toNNReal s)/Real.sqrt θ=_
    congr 2
    apply NNReal.eq
    simp only [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal s hs0,
      Real.coe_toNNReal (θ*s) (mul_nonneg hθ.le hs0)]
  have hi : (∫ s in (0:ℝ)..(θ*a),deriv h s*f (Real.toNNReal s))=
      c*Real.sqrt θ*(∫ s in (0:ℝ)..(a:ℝ),deriv g s*(scaleContinuousPath θ hθ f) (Real.toNNReal s)) := by
    have hc := intervalIntegral.smul_integral_comp_mul_left
      (fun s : ℝ => deriv h s*f (Real.toNNReal s)) (a := 0) (b := (a:ℝ)) θ
    simp only [smul_eq_mul,mul_zero] at hc
    rw [← hc,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hsa
    have hs' : s ∈ Icc (0:ℝ) a := by simpa only [uIcc_of_le a.coe_nonneg] using hsa
    dsimp only
    rw [he s hs'.1]
    have hd' := hd s hs'.1 hs'.2
    calc
      θ*(deriv h (θ*s)*f (Real.toNNReal (θ*s))) = (deriv h (θ*s)*θ)*f (Real.toNNReal (θ*s)) := by ring
      _ = (c*deriv g s)*f (Real.toNNReal (θ*s)) := by rw [hd']
      _ = _ := by field_simp
  unfold deterministicIntegralPath
  simp only [NNReal.coe_mul,NNReal.coe_mk,hv]
  rw [hi]
  change c*g a*f ((NNReal.mk θ hθ.le)*a)-_=c*Real.sqrt θ*(g a*(f ((NNReal.mk θ hθ.le)*a)/Real.sqrt θ)-_)
  field_simp
  <;> ring

theorem rough_integral_path_scaling (H ν θ : ℝ) (hθ : 0 < θ)
    (a : ℝ≥0) (ha : a < 1) (f : C(ℝ≥0,ℝ)) :
    deterministicIntegralPath (roughKernelExtension H ν θ (θ*a)) ((NNReal.mk θ hθ.le)*a) f=
      θ^H*deterministicIntegralPath (roughKernelExtension H ν 1 a) a (scaleContinuousPath θ hθ f) := by
  have hv := rough_kernel_extension_scaling H ν 1 a a θ ha hθ
  simp only [mul_one] at hv
  have hd (s : ℝ) (_ : 0 ≤ s) (_ : s ≤ (a:ℝ)) := rough_kernel_extension_derivative_scaling H ν 1 a s θ ha hθ
  simp only [mul_one] at hd
  have h := deterministic_integral_path_scaling _ _ a θ (θ^(H-1/2)) hθ hv hd f
  have hc : θ^(H-1/2)*Real.sqrt θ=θ^H := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hθ]
    congr 1
    ring
  simpa only [hc] using h

end BarrierManuscript
#print axioms BarrierManuscript.deterministic_integral_path_scaling
#print axioms BarrierManuscript.rough_integral_path_scaling
