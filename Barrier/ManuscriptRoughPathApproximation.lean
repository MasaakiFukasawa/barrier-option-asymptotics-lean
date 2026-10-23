import ManuscriptRoughIntegralApproximation
import ManuscriptRoughKernelExtension
import ManuscriptTruncatedIntegralPath

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem rough_cut_path_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν : ℝ) (t a : ℝ≥0) (hat : a < t)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughCutKernel H ν t a z.2) N) :
    N (realTimeClamp t)=ᵐ[P] fun ω =>
      deterministicIntegralPath (roughKernelExtension H ν t a) a (brownianContinuousPath B ω) := by
  have he := rough_kernel_cut_extension H ν t a a.coe_nonneg (show (a:ℝ)<(t:ℝ) from hat)
  simp_rw [he] at hNI
  exact truncated_integral_path_encoding P B _ (rough_kernel_extension_smooth H ν t a hat)
    a t hat.le N hN hNI

/-- The singular integral is approximated on its original probability
space by explicit measurable functionals of its Brownian path. -/
theorem rough_integral_path_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν : ℝ) (hH : 0 < H) (t : ℝ≥0)
    (a : ℕ → ℝ≥0) (hat : ∀ n, a n < t) (halim : Tendsto (fun n => (a n:ℝ)) atTop (𝓝 (t:ℝ)))
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N) :
    TendstoInMeasure P (fun n ω => N (realTimeClamp t) ω-
      deterministicIntegralPath (roughKernelExtension H ν t (a n)) (a n) (brownianContinuousPath B ω))
      atTop (fun _ => 0) := by
  have hg : Measurable (roughKernel H ν t) := by
    unfold roughKernel Asakura.mvnFutureFunction
    exact measurable_const.mul ((measurable_const.sub measurable_id).pow_const _ |>.indicator measurableSet_Ioc)
  have hi n : Integrable (fun s => roughCutKernel H ν t (a n) s^2) volume :=
    (memLp_two_iff_integrable_sq ((rough_kernel_memLp H ν t hH t.coe_nonneg).indicator measurableSet_Iic).aestronglyMeasurable).mp
      ((rough_kernel_memLp H ν t hH t.coe_nonneg).indicator measurableSet_Iic)
  choose M hM hMI using fun n => deterministic_ito_exists P B (roughCutKernel H ν t (a n))
    (hg.indicator measurableSet_Iic) (fun r _ => (hi n).intervalIntegrable)
  have he := (rough_integral_cut_approximation P B H ν t hH t.coe_nonneg
    (fun n => (a n:ℝ)) (fun n => (a n).coe_nonneg) (fun n => (hat n).le) halim N M hN hM hNI hMI).2
  apply TendstoInMeasure.congr_left _ he
  intro n
  filter_upwards [rough_cut_path_encoding P B H ν t (a n) (hat n) (M n) (hM n) (hMI n)] with ω hω
  rw [hω]

end BarrierManuscript
#print axioms BarrierManuscript.rough_cut_path_encoding
#print axioms BarrierManuscript.rough_integral_path_approximation
