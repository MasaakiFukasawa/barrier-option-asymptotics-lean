import ManuscriptTruncatedCall
import ManuscriptBrownianKilledMeasure

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The UOC reflection formula as an actual continuously monitored Brownian
payoff expectation. The incompatible terminal/barrier corner does not require
an Ito dominated-convergence argument: use the killed endpoint measure. -/
theorem brownian_killed_call {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    (∫ ω in {ω | brownianMaximum B ω ≤ b}, max (B.W 0 (realTimeClamp 1) ω-k) 0 ∂P) =
      truncatedCall b k 0 1-truncatedCall b k (2*b) 1 := by
  rw [brownian_killed_expectation P B b hb (fun x => max (x-k) 0) (by fun_prop)]
  have h0 : IntegrableOn (fun x => max (x-k) 0*phi x) (Iio b) := by
    simpa only [sub_zero,div_one] using (call_gaussian_integrable k 0 1 zero_lt_one).integrableOn
  have hB : IntegrableOn (fun x => max (x-k) 0*phi (x-2*b)) (Iio b) := by
    simpa only [div_one] using (call_gaussian_integrable k (2*b) 1 zero_lt_one).integrableOn
  simp_rw [mul_sub]
  rw [integral_sub h0 hB]
  have h1 := truncated_call_integral b k 0 1 hk zero_lt_one
  have h2 := truncated_call_integral b k (2*b) 1 hk zero_lt_one
  simp only [sub_zero,div_one] at h1 h2
  rw [h1,h2]

theorem brownian_uoc_put_digital {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    (∫ ω in {ω | brownianMaximum B ω ≤ b}, max (B.W 0 (realTimeClamp 1) ω-k) 0 ∂P) =
      killedPut b k 0 1-b+(b-k)*(2*normalCDF b-1) := by
  rw [brownian_killed_call P B b k hb hk]
  simpa only [add_zero,sub_zero,div_one] using uoc_put_survival_decomposition b k 0 1

end BarrierManuscript
#print axioms BarrierManuscript.brownian_killed_call
#print axioms BarrierManuscript.brownian_uoc_put_digital
