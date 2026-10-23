import ManuscriptRoughKernelTail

open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def roughCutKernel (H ν t a : ℝ) : ℝ → ℝ :=
  (Iic a).indicator (roughKernel H ν t)

theorem rough_kernel_cut_difference (H ν t a s : ℝ) (ha : 0 ≤ a) :
    roughKernel H ν t s-roughCutKernel H ν t a s =
      (Ioc a t).indicator (roughKernel H ν t) s := by
  by_cases hsa : s ≤ a
  · have hn : s ∉ Ioc a t := fun h => (not_lt_of_ge hsa) h.1
    simp [roughCutKernel,hsa,hn]
  · have has : a < s := lt_of_not_ge hsa
    by_cases hst : s ≤ t
    · simp [roughCutKernel,hsa,show s ∈ Ioc a t from ⟨has,hst⟩]
    · have hn : s ∉ Ioc (0:ℝ) t := fun h => hst h.2
      have hn' : s ∉ Ioc a t := fun h => hst h.2
      simp [roughCutKernel,roughKernel,Asakura.mvnFutureFunction,hsa,hn,hn']

theorem rough_kernel_cut_square (H ν t a : ℝ) (ha : 0 ≤ a) :
    (fun s => (roughKernel H ν t s-roughCutKernel H ν t a s)^2)=
      (Ioc a t).indicator (fun s => roughKernel H ν t s^2) := by
  funext s
  rw [rough_kernel_cut_difference H ν t a s ha]
  by_cases hs : s ∈ Ioc a t <;> simp [hs]

theorem rough_kernel_cut_square_integrable (H ν t a : ℝ) (hH : 0 < H)
    (ha : 0 ≤ a) (hat : a ≤ t) :
    Integrable (fun s => (roughKernel H ν t s-roughCutKernel H ν t a s)^2) volume := by
  rw [rough_kernel_cut_square H ν t a ha]
  exact (rough_kernel_square_integrable H ν t hH (ha.trans hat)).indicator measurableSet_Ioc

theorem rough_kernel_cut_error (H ν t a : ℝ) (hH : 0 < H)
    (ha : 0 ≤ a) (hat : a ≤ t) :
    (∫ s in 0..t,(roughKernel H ν t s-roughCutKernel H ν t a s)^2)=ν^2*(t-a)^(2*H) := by
  rw [rough_kernel_cut_square H ν t a ha,intervalIntegral.integral_of_le (ha.trans hat),
    setIntegral_indicator measurableSet_Ioc]
  have hsub : Ioc a t ⊆ Ioc (0:ℝ) t := Ioc_subset_Ioc_left ha
  rw [Set.inter_eq_right.mpr hsub,← intervalIntegral.integral_of_le hat]
  exact rough_kernel_tail_energy H ν t a hH ha hat

end BarrierManuscript
#print axioms BarrierManuscript.rough_kernel_cut_difference
#print axioms BarrierManuscript.rough_kernel_cut_square
#print axioms BarrierManuscript.rough_kernel_cut_square_integrable
#print axioms BarrierManuscript.rough_kernel_cut_error
