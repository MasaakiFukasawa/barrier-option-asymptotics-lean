import ManuscriptRoughPathApproximation
import ManuscriptRoughIntegralLaw
import ManuscriptWeightedL2Limit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The truncated Brownian path functionals converge in every bounded
weighted expectation to the actual singular integral. -/
theorem rough_weighted_path_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν : ℝ) (hH : 0 < H) (t : ℝ≥0)
    (a : ℕ → ℝ≥0) (hat : ∀ n, a n < t) (halim : Tendsto (fun n => (a n:ℝ)) atTop (𝓝 (t:ℝ)))
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N)
    (Z : Ω → ℝ) (hZ : Measurable Z) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ ω, |Z ω| ≤ C) :
    Tendsto (fun n => ∫ ω,
      deterministicIntegralPath (roughKernelExtension H ν t (a n)) (a n) (brownianContinuousPath B ω)*Z ω ∂P)
      atTop (𝓝 (∫ ω,N (realTimeClamp t) ω*Z ω ∂P)) := by
  have hg : Measurable (roughKernel H ν t) := by
    unfold roughKernel Asakura.mvnFutureFunction
    exact measurable_const.mul ((measurable_const.sub measurable_id).pow_const _ |>.indicator measurableSet_Ioc)
  have hi n : Integrable (fun s => roughCutKernel H ν t (a n) s^2) volume :=
    (memLp_two_iff_integrable_sq ((rough_kernel_memLp H ν t hH t.coe_nonneg).indicator measurableSet_Iic).aestronglyMeasurable).mp
      ((rough_kernel_memLp H ν t hH t.coe_nonneg).indicator measurableSet_Iic)
  choose M hM hMI using fun n => deterministic_ito_exists P B (roughCutKernel H ν t (a n))
    (hg.indicator measurableSet_Iic) (fun r _ => (hi n).intervalIntegrable)
  have he := (rough_integral_cut_approximation P B H ν t hH t.coe_nonneg
    (fun n => (a n:ℝ)) (fun n => (a n).coe_nonneg) (fun n => (hat n).le) halim N M hN hM hNI hMI).1
  have hY : MemLp (N (realTimeClamp t)) 2 P := by
    simpa using (rough_integral_law P B H ν t hH t.coe_nonneg N hN hNI).memLp (memLp_id_gaussianReal 2)
  have hX n : MemLp (M n (realTimeClamp t)) 2 P := by
    convert hY.sub (he n).1 using 1
    funext ω
    simp
  have hl : Tendsto (fun n => ∫ ω,(M n (realTimeClamp t) ω-N (realTimeClamp t) ω)^2 ∂P) atTop (𝓝 0) := by
    have hh n : (∫ ω,(M n (realTimeClamp t) ω-N (realTimeClamp t) ω)^2 ∂P)=ν^2*((t:ℝ)-a n)^(2*H) := by
      rw [show (fun ω => (M n (realTimeClamp t) ω-N (realTimeClamp t) ω)^2)=
        (fun ω => (N (realTimeClamp t) ω-M n (realTimeClamp t) ω)^2) by funext ω; ring]
      exact (he n).2
    simp_rw [hh]
    have hd : Tendsto (fun n => (t:ℝ)-(a n:ℝ)) atTop (𝓝 0) := by
      simpa only [sub_self] using halim.const_sub (t:ℝ)
    simpa only [mul_zero] using (hd.rpow_const_nhds_zero (by positivity : 0 < 2*H)).const_mul (ν^2)
  have hw := weighted_L2_expectation_limit P (fun n => M n (realTimeClamp t))
    (N (realTimeClamp t)) Z hX hY hZ C hC hb hl
  have henc n := rough_cut_path_encoding P B H ν t (a n) (hat n) (M n) (hM n) (hMI n)
  convert hw using 1
  funext n
  apply integral_congr_ae
  filter_upwards [henc n] with ω hω
  rw [hω]

end BarrierManuscript
#print axioms BarrierManuscript.rough_weighted_path_approximation
