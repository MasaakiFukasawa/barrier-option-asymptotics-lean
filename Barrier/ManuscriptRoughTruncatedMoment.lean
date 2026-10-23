import ManuscriptWeightedPathIntegral
import ManuscriptBarPsiTestIBP
import ManuscriptRoughKernelExtension

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A Brownian weighted-moment identity determines the corresponding
truncated Volterra-integral moment, with the stochastic Fubini and endpoint
terms justified. -/
theorem rough_truncated_barPsi_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν b k κ : ℝ) (hb : 0 < b) (t a : ℝ≥0) (ha : 0 < a) (hat : a < t) (ht : t < 1)
    (Z : Ω → ℝ) (hZ : Measurable Z) (C : ℝ) (hC : 0 ≤ C) (hZb : ∀ ω, |Z ω| ≤ C)
    (hMoment : ∀ s : ℝ, 0 < s → s < (t:ℝ) →
      (∫ ω,B.W 0 (realTimeClamp s) ω*Z ω ∂P)=κ*barPsi b k s) :
    (∫ ω,deterministicIntegralPath (roughKernelExtension H ν t a) a
      (brownianContinuousPath B ω)*Z ω ∂P)=
      κ*(∫ s in (0:ℝ)..(a:ℝ),roughKernel H ν t s*barPsiTimeDerivative b k s) := by
  obtain ⟨D,hD,hD0,hDb⟩ := brownian_integrable_path_bound P B t t.coe_nonneg
  have hFbound : ∀ (ω : Ω) (s : ℝ≥0), s ≤ a → |brownianContinuousPath B ω s| ≤ D ω := by
    intro ω s hs
    exact hDb ω s ⟨s.coe_nonneg,hs.trans hat.le⟩
  have hg := rough_kernel_extension_smooth H ν t a hat
  have hw := weighted_path_integral_expectation P (brownianContinuousPath B)
    (brownian_continuous_path_measurable B) (roughKernelExtension H ν t a) hg a
    D Z hD hD0 hFbound hZ C hC hZb
  have he : (∫ s in (0:ℝ)..(a:ℝ),deriv (roughKernelExtension H ν t a) s*
      (∫ ω,brownianContinuousPath B ω (Real.toNNReal s)*Z ω ∂P))=
      ∫ s in (0:ℝ)..(a:ℝ),deriv (roughKernelExtension H ν t a) s*(κ*barPsi b k s) := by
    apply intervalIntegral.integral_congr_Ioo_of_le a.coe_nonneg
    intro s hs
    have hh : (fun ω => brownianContinuousPath B ω (Real.toNNReal s)*Z ω)=
      (fun ω => B.W 0 (realTimeClamp s) ω*Z ω) := by
      funext ω
      simp only [brownianContinuousPath,ContinuousMap.coe_mk,Real.coe_toNNReal _ hs.1.le]
    dsimp only
    rw [hh,hMoment s hs.1 (hs.2.trans hat)]
  rw [he] at hw
  have hmA : (∫ ω,brownianContinuousPath B ω a*Z ω ∂P)=κ*barPsi b k a :=
    hMoment a ha hat
  rw [hmA] at hw
  have hscale : (∫ s in (0:ℝ)..(a:ℝ),deriv (roughKernelExtension H ν t a) s*(κ*barPsi b k s))=
      κ*(∫ s in (0:ℝ)..(a:ℝ),deriv (roughKernelExtension H ν t a) s*barPsi b k s) := by
    simp_rw [show ∀ s, deriv (roughKernelExtension H ν t a) s*(κ*barPsi b k s)=
      κ*(deriv (roughKernelExtension H ν t a) s*barPsi b k s) by intro s; ring]
    exact intervalIntegral.integral_const_mul _ _
  rw [hscale] at hw
  calc
    _ = κ*(roughKernelExtension H ν t a a*barPsi b k a-
        (∫ s in (0:ℝ)..(a:ℝ),deriv (roughKernelExtension H ν t a) s*barPsi b k s)) := by rw [hw]; ring
    _ = κ*(∫ s in (0:ℝ)..(a:ℝ),roughKernelExtension H ν t a s*barPsiTimeDerivative b k s) := by
      rw [barPsi_test_ibp b k a hb ⟨ha,hat.trans ht⟩ _ hg]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr_Ioo_of_le a.coe_nonneg
      intro s hs
      dsimp only
      rw [rough_kernel_extension_value H ν t a s hat hs.2.le]
      unfold roughKernel Asakura.mvnFutureFunction
      rw [Set.indicator_of_mem (show s ∈ Ioc (0:ℝ) (t:ℝ) from ⟨hs.1,(hs.2.trans hat).le⟩)]

end BarrierManuscript
#print axioms BarrierManuscript.rough_truncated_barPsi_moment
