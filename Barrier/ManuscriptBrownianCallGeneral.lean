import ManuscriptRawKilledDensity
import ManuscriptTruncatedCall
import ManuscriptTranslateKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The reflected call formula for an arbitrary starting point and Brownian
clock. The event monitors the entire continuous path up to that clock. -/
theorem brownian_killed_call_general {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ht : 0 < t)
    (b k x : ℝ) (hx : x < b) (hk : k ≤ b) :
    (∫ ω in {ω | pathMaximum (rawPrefixPath W hc t ω) ≤ b-x},
      max (x+W t ω-k) 0 ∂P) =
      truncatedCall b k x (Real.sqrt (t:ℝ))-
        truncatedCall b k (2*b-x) (Real.sqrt (t:ℝ)) := by
  have htr : (0:ℝ)<(t:ℝ) := by exact_mod_cast ht
  have hw := Real.sqrt_pos.mpr htr
  rw [raw_brownian_killed_expectation P W hW hm hc t ht (b-x) (sub_pos.mpr hx)
    (fun y => max (x+y-k) 0) (by fun_prop)]
  have he (y : ℝ) :
      max (x+y-k) 0 * psi (b-x) y (t:ℝ) =
      (fun z => max (z-k) 0 *
        (phi ((z-x)/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ) -
         phi ((z-(2*b-x))/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ))) (x+y) := by
    dsimp only
    unfold psi
    rw [show x+y-x=y by ring, show x+y-(2*b-x)=y-2*(b-x) by ring]
    ring
  simp_rw [he]
  rw [integral_translate_Iio (fun z => max (z-k) 0 *
    (phi ((z-x)/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ) -
     phi ((z-(2*b-x))/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ))) b x]
  simp_rw [mul_sub]
  rw [integral_sub (call_gaussian_integrable k x _ hw).integrableOn
    (call_gaussian_integrable k (2*b-x) _ hw).integrableOn,
    truncated_call_integral b k x _ hk hw,
    truncated_call_integral b k (2*b-x) _ hk hw]

/-- The European-digital/UOP decomposition holds at every positive Brownian
clock, not just at unit time. -/
theorem brownian_uoc_decomposition_general {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ht : 0 < t)
    (b k x : ℝ) (hx : x < b) (hk : k ≤ b) :
    (∫ ω in {ω | pathMaximum (rawPrefixPath W hc t ω) ≤ b-x},
      max (x+W t ω-k) 0 ∂P) =
      killedPut b k x (Real.sqrt (t:ℝ))+x-b+
        (b-k)*(2*normalCDF ((b-x)/Real.sqrt (t:ℝ))-1) := by
  rw [brownian_killed_call_general P W hW hm hc t ht b k x hx hk]
  exact uoc_put_survival_decomposition b k x _

end BarrierManuscript
#print axioms BarrierManuscript.brownian_killed_call_general
#print axioms BarrierManuscript.brownian_uoc_decomposition_general
