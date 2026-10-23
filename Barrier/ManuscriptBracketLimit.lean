import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

noncomputable def normalizedBracket (S V : ℝ → ℝ) (S₀ v₀ θ u : ℝ) : ℝ :=
  ∫ s in 0..u, (S (θ*s)/S₀)^2*V (θ*s)/v₀

/-- The bracket expression in the manuscript converges pathwise. This is an
analytic statement about the displayed integral, separate from identifying it
as the quadratic variation of the rescaled stochastic integral. Paths on
nonnegative times can be extended constantly to negative times. -/
theorem normalizedBracket_tendsto (S V : ℝ → ℝ) (S₀ v₀ u : ℝ)
    (hS : Continuous S) (hV : Continuous V)
    (hS₀ : S 0 = S₀) (hv₀ : V 0 = v₀) (hSn : S₀ ≠ 0) (hvn : v₀ ≠ 0) :
    Tendsto (fun θ => normalizedBracket S V S₀ v₀ θ u) (𝓝 0) (𝓝 u) := by
  have hc : Continuous (fun p : ℝ × ℝ => (S (p.1*p.2)/S₀)^2*V (p.1*p.2)/v₀) := by
    fun_prop
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun θ s : ℝ => (S (θ*s)/S₀)^2*V (θ*s)/v₀) hc 0 u
  have h := hi.continuousAt.tendsto (x := (0:ℝ))
  simpa only [normalizedBracket, zero_mul, hS₀, hv₀, div_self hSn, one_pow,
    one_mul, div_self hvn, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_one] using h

/-- Measurable bracket expressions converge in probability, with no extra
moment assumption. Pathwise continuity supplies their convergence. -/
theorem normalizedBracket_inMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (S V : Ω → ℝ → ℝ)
    (S₀ v₀ u : ℝ) (θ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0))
    (hS : ∀ᵐ ω ∂P, Continuous (S ω)) (hV : ∀ᵐ ω ∂P, Continuous (V ω))
    (hS₀ : ∀ᵐ ω ∂P, S ω 0 = S₀) (hv₀ : ∀ᵐ ω ∂P, V ω 0 = v₀)
    (hSn : S₀ ≠ 0) (hvn : v₀ ≠ 0)
    (hm : ∀ n, AEStronglyMeasurable
      (fun ω => normalizedBracket (S ω) (V ω) S₀ v₀ (θ n) u) P) :
    TendstoInMeasure P (fun n ω => normalizedBracket (S ω) (V ω) S₀ v₀ (θ n) u)
      atTop (fun _ => u) := by
  apply tendstoInMeasure_of_tendsto_ae hm
  filter_upwards [hS,hV,hS₀,hv₀] with ω hs hv hs0 hv0
  exact (normalizedBracket_tendsto (S ω) (V ω) S₀ v₀ u hs hv hs0 hv0 hSn hvn).comp hθ

end BarrierManuscript

#print axioms BarrierManuscript.normalizedBracket_tendsto
#print axioms BarrierManuscript.normalizedBracket_inMeasure
