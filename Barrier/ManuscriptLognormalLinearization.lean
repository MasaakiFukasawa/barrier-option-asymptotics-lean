import ManuscriptLognormalLaw
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Gaussian marginals make the lognormal linearization error vanish in
probability on the original probability space. The variables need not share
a common realization or be independent across maturities. -/
theorem lognormal_linearization_inMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ≥0) (G : ℕ → Ω → ℝ)
    (hG : ∀ n, HasLaw (G n) (gaussianReal 0 a) P)
    (e : ℕ → ℝ) (he : ∀ n, e n ≠ 0) (he0 : Tendsto e atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
      (Real.exp (e n*G n ω-(e n)^2*(a:ℝ)/2)-1)/e n-G n ω) atTop (fun _ => 0) := by
  let f := fun n (x : ℝ) => (Real.exp (e n*x-(e n)^2*(a:ℝ)/2)-1)/e n-x
  have hm (n : ℕ) : Measurable (f n) := by dsimp only [f]; fun_prop
  have hc : TendstoInMeasure (gaussianReal 0 a) f atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable)
    apply ae_of_all
    intro x
    simpa only [f,sub_self] using (lognormal_fluctuation_limit e he he0 x a).sub_const x
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have h := tendstoInMeasure_iff_norm.mp hc ε hε
  simp only [sub_zero] at h ⊢
  have heq (n : ℕ) : P {ω | ε ≤ ‖f n (G n ω)‖} =
      (gaussianReal 0 a) {x | ε ≤ ‖f n x‖} := by
    exact ((hG n).identDistrib HasLaw.id).measure_mem_eq
      (measurableSet_le measurable_const (hm n).norm)
  simpa only [f,← heq] using h

/-- Scalar lognormal weak convergence derived from the Gaussian marginal
law and the preceding in-probability remainder estimate. -/
theorem lognormal_family_weak_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : ℝ≥0) (G : ℕ → Ω → ℝ)
    (hG : ∀ n, HasLaw (G n) (gaussianReal 0 a) P)
    (e : ℕ → ℝ) (he : ∀ n, e n ≠ 0) (he0 : Tendsto e atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω =>
      (Real.exp (e n*G n ω-(e n)^2*(a:ℝ)/2)-1)/e n) atTop id (fun _ => P) (gaussianReal 0 a) := by
  have hbase : TendstoInDistribution G atTop id (fun _ => P) (gaussianReal 0 a) :=
    tendstoInDistribution_of_identDistrib 0 (fun n => (hG 0).identDistrib (hG n)) ((hG 0).identDistrib HasLaw.id)
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ id hbase
    (lognormal_linearization_inMeasure P a G hG e he he0)
  intro n
  exact (show Measurable (fun x : ℝ => (Real.exp (e n*x-(e n)^2*(a:ℝ)/2)-1)/e n) by fun_prop).comp_aemeasurable (hG n).aemeasurable

end BarrierManuscript
#print axioms BarrierManuscript.lognormal_linearization_inMeasure
#print axioms BarrierManuscript.lognormal_family_weak_limit
