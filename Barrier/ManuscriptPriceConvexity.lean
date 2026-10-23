import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Set
namespace BarrierManuscript

/-- The put payoff satisfies the strike-convexity inequality pointwise. -/
theorem put_payoff_convexity (x k₁ k₂ a c : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : a+c=1) :
    max (a*k₁+c*k₂-x) 0 ≤ a*max (k₁-x) 0+c*max (k₂-x) 0 := by
  apply max_le
  · have h1 := mul_le_mul_of_nonneg_left (le_max_left (k₁-x) 0) ha
    have h2 := mul_le_mul_of_nonneg_left (le_max_left (k₂-x) 0) hc
    nlinarith [congrArg (fun z : ℝ => z*x) hs]
  · positivity

/-- A finite surviving measure is independent of strike, so taking its put
payoff expectation preserves strike convexity. -/
theorem put_expectation_convex {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (X : Ω → ℝ) (hi : Integrable X Q) :
    ConvexOn ℝ univ (fun k : ℝ => ∫ ω, max (k-X ω) 0 ∂Q) := by
  have hpay (k : ℝ) : Integrable (fun ω => max (k-X ω) 0) Q :=
    ((integrable_const k).sub hi).sup (integrable_const 0)
  refine ⟨convex_univ, ?_⟩
  intro k₁ _ k₂ _ a c ha hc hs
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hpay k₁).const_mul a) ((hpay k₂).const_mul c)]
  exact integral_mono (hpay _) (((hpay k₁).const_mul a).add ((hpay k₂).const_mul c))
    (fun ω => put_payoff_convexity (X ω) k₁ k₂ a c ha hc hs)

/-- The interpolation used for regular models is convex in strike whenever
both component prices are convex and the interpolation weight lies in [0,1]. -/
theorem interpolated_price_convex (p q : ℝ → ℝ)
    (hp : ConvexOn ℝ univ p) (hq : ConvexOn ℝ univ q)
    (δ : ℝ) (hδ : δ ∈ Icc (0:ℝ) 1) :
    ConvexOn ℝ univ (fun k => p k+(q k-p k)*δ) := by
  convert (hp.smul (sub_nonneg.mpr hδ.2)).add (hq.smul hδ.1) using 1
  funext k
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Strike convexity implies nonnegative equal-spacing butterfly values. -/
theorem convex_price_butterfly (p : ℝ → ℝ) (hp : ConvexOn ℝ univ p)
    (k h : ℝ) : 0 ≤ p (k-h)-2*p k+p (k+h) := by
  have hh := hp.2 (mem_univ (k-h)) (mem_univ (k+h))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at hh
  rw [show (1/2:ℝ)*(k-h)+1/2*(k+h)=k by ring] at hh
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.put_payoff_convexity
#print axioms BarrierManuscript.put_expectation_convex
#print axioms BarrierManuscript.interpolated_price_convex
#print axioms BarrierManuscript.convex_price_butterfly
