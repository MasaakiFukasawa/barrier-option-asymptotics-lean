import ManuscriptRoughKernel

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The exact energy discarded by truncating the singular Volterra kernel
at a<t. It vanishes at order (t-a)^(2H). -/
theorem rough_kernel_tail_energy (H ν t a : ℝ) (hH : 0 < H)
    (ha : 0 ≤ a) (hat : a ≤ t) :
    (∫ s in a..t,roughKernel H ν t s^2)=ν^2*(t-a)^(2*H) := by
  have he : (∫ s in a..t,roughKernel H ν t s^2)=
      (ν*Real.sqrt (2*H))^2*(∫ s in a..t,(t-s)^(2*H-1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hat
    intro s hs
    have hst : s ∈ Ioc (0:ℝ) t := ⟨ha.trans_lt hs.1,hs.2.le⟩
    simp only [roughKernel,Asakura.mvnFutureFunction,Set.indicator_of_mem hst,mul_pow]
    congr 1
    rw [← Real.rpow_natCast,← Real.rpow_mul (sub_nonneg.mpr hs.2.le)]
    congr 1
    ring
  rw [he,intervalIntegral.integral_comp_sub_left (fun s : ℝ => s^(2*H-1)) t]
  simp only [sub_self]
  rw [integral_rpow (Or.inl (by linarith : -1 < 2*H-1))]
  rw [show 2*H-1+1=2*H by ring,Real.zero_rpow (by positivity : 2*H ≠ 0),sub_zero]
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*H)]
  field_simp

theorem rough_kernel_tail_energy_limit (H ν t : ℝ) (hH : 0 < H)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hat : ∀ n, a n ≤ t)
    (halim : Tendsto a atTop (𝓝 t)) :
    Tendsto (fun n => ∫ s in a n..t,roughKernel H ν t s^2) atTop (𝓝 0) := by
  simp_rw [rough_kernel_tail_energy H ν t _ hH (ha _) (hat _)]
  have h : Tendsto (fun n => t-a n) atTop (𝓝 0) := by
    simpa only [sub_self] using halim.const_sub t
  simpa only [mul_zero] using (h.rpow_const_nhds_zero (by positivity : 0 < 2*H)).const_mul (ν^2)

end BarrierManuscript
#print axioms BarrierManuscript.rough_kernel_tail_energy
#print axioms BarrierManuscript.rough_kernel_tail_energy_limit
