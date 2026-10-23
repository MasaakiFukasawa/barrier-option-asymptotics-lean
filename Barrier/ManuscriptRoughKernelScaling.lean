import ManuscriptRoughKernelExtension

open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem smoothPositive_scaling (θ a x : ℝ) (hθ : 0 < θ) :
    smoothPositive (θ*a) (θ*x)=θ*smoothPositive a x := by
  unfold smoothPositive
  rw [show θ*x-θ*a=θ*(x-a) by ring,mul_div_mul_left _ _ hθ.ne']
  ring

theorem positivePowerExtension_scaling (θ a r x : ℝ) (hθ : 0 < θ) (ha : 0 < a) :
    positivePowerExtension (θ*a) r (θ*x)=θ^r*positivePowerExtension a r x := by
  unfold positivePowerExtension
  rw [smoothPositive_scaling θ a x hθ,Real.mul_rpow hθ.le (smoothPositive_pos ha x).le]

theorem rough_kernel_extension_scaling (H ν t a s θ : ℝ) (hat : a < t) (hθ : 0 < θ) :
    roughKernelExtension H ν (θ*t) (θ*a) (θ*s)=θ^(H-1/2)*roughKernelExtension H ν t a s := by
  unfold roughKernelExtension
  rw [show (θ*t-θ*a)/4=θ*((t-a)/4) by ring,show θ*t-θ*s=θ*(t-s) by ring,
    positivePowerExtension_scaling θ ((t-a)/4) (H-1/2) (t-s) hθ (by linarith)]
  ring

theorem rough_kernel_extension_derivative_scaling (H ν t a s θ : ℝ) (hat : a < t) (hθ : 0 < θ) :
    deriv (roughKernelExtension H ν (θ*t) (θ*a)) (θ*s)*θ=
      θ^(H-1/2)*deriv (roughKernelExtension H ν t a) s := by
  have hbig := (rough_kernel_extension_smooth H ν (θ*t) (θ*a)
    (mul_lt_mul_of_pos_left hat hθ)).differentiable (by norm_num)
  have hsmall := (rough_kernel_extension_smooth H ν t a hat).differentiable (by norm_num)
  have hb := (hbig (θ*s)).hasDerivAt.comp s ((hasDerivAt_id s).const_mul θ)
  have hs := (hsmall s).hasDerivAt.const_mul (θ^(H-1/2))
  have he : (fun x => roughKernelExtension H ν (θ*t) (θ*a) (θ*x))=
      (fun x => θ^(H-1/2)*roughKernelExtension H ν t a x) := by
    funext x
    exact rough_kernel_extension_scaling H ν t a x θ hat hθ
  change HasDerivAt (fun x => roughKernelExtension H ν (θ*t) (θ*a) (θ*x))
    (deriv (roughKernelExtension H ν (θ*t) (θ*a)) (θ*s)*(θ*1)) s at hb
  rw [he,mul_one] at hb
  exact hb.unique hs

end BarrierManuscript
#print axioms BarrierManuscript.smoothPositive_scaling
#print axioms BarrierManuscript.positivePowerExtension_scaling
#print axioms BarrierManuscript.rough_kernel_extension_scaling
#print axioms BarrierManuscript.rough_kernel_extension_derivative_scaling
