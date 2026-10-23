import ManuscriptRoughKernelCut
import Chapter3SmoothPositivePower

open Set
open Asakura.Chapter3Complete
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def roughKernelExtension (H ν t a : ℝ) (s : ℝ) : ℝ :=
  ν*Real.sqrt (2*H)*positivePowerExtension ((t-a)/4) (H-1/2) (t-s)

theorem rough_kernel_extension_smooth (H ν t a : ℝ) (ha : a < t) :
    ContDiff ℝ 1 (roughKernelExtension H ν t a) := by
  exact contDiff_const.mul ((positivePowerExtension_contDiff (by linarith : 0 < (t-a)/4)
    (H-1/2) 1).comp (contDiff_const.sub contDiff_id))

theorem rough_kernel_extension_value (H ν t a s : ℝ) (ha : a < t) (hs : s ≤ a) :
    roughKernelExtension H ν t a s=ν*Real.sqrt (2*H)*(t-s)^(H-1/2) := by
  unfold roughKernelExtension
  rw [(positivePowerExtension_value_deriv (by linarith : 0 < (t-a)/4)
    (by linarith : 2*((t-a)/4)<t-s) (H-1/2)).1]

theorem rough_kernel_cut_extension (H ν t a : ℝ) (ha : 0 ≤ a) (hat : a < t) :
    roughCutKernel H ν t a=(Ioc 0 a).indicator (roughKernelExtension H ν t a) := by
  funext s
  by_cases hs : s ∈ Ioc (0:ℝ) a
  · have hst : s ∈ Ioc (0:ℝ) t := ⟨hs.1,hs.2.trans hat.le⟩
    simp only [roughCutKernel,Set.mem_Iic,Set.indicator_of_mem (show s ∈ Iic a from hs.2),Set.indicator_of_mem hs,
      roughKernel,Asakura.mvnFutureFunction,Set.indicator_of_mem hst,
      rough_kernel_extension_value H ν t a s hat hs.2]
  · by_cases hsa : s ≤ a
    · have hs0 : ¬ 0 < s := fun h => hs ⟨h,hsa⟩
      have hst : s ∉ Ioc (0:ℝ) t := fun h => hs0 h.1
      simp [roughCutKernel,roughKernel,Asakura.mvnFutureFunction,hsa,hs,hst]
    · simp [roughCutKernel,hsa,hs]

end BarrierManuscript
#print axioms BarrierManuscript.rough_kernel_extension_smooth
#print axioms BarrierManuscript.rough_kernel_extension_value
#print axioms BarrierManuscript.rough_kernel_cut_extension
