import ManuscriptRawKilledDensity
import ManuscriptTruncatedPut
import ManuscriptTranslateKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The reflected put formula for an arbitrary starting point and Brownian
clock. The event monitors the entire continuous path up to that clock. -/
theorem brownian_killed_put_general {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ht : 0 < t)
    (b k x : ℝ) (hx : x < b) (hk : k ≤ b) :
    (∫ ω in {ω | pathMaximum (rawPrefixPath W hc t ω) ≤ b-x},
      max (k-(x+W t ω)) 0 ∂P) =
      killedPut b k x (Real.sqrt (t:ℝ)) := by
  have htr : (0:ℝ)<(t:ℝ) := by exact_mod_cast ht
  have hw := Real.sqrt_pos.mpr htr
  rw [raw_brownian_killed_expectation P W hW hm hc t ht (b-x) (sub_pos.mpr hx)
    (fun y => max (k-(x+y)) 0) (by fun_prop)]
  have he (y : ℝ) :
      max (k-(x+y)) 0 * psi (b-x) y (t:ℝ) =
      (fun z => max (k-z) 0 *
        (phi ((z-x)/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ) -
         phi ((z-(2*b-x))/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ))) (x+y) := by
    dsimp only
    unfold psi
    rw [show x+y-x=y by ring, show x+y-(2*b-x)=y-2*(b-x) by ring]
    ring
  simp_rw [he]
  rw [integral_translate_Iio (fun z => max (k-z) 0 *
    (phi ((z-x)/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ) -
     phi ((z-(2*b-x))/Real.sqrt (t:ℝ))/Real.sqrt (t:ℝ))) b x]
  unfold killedPut
  simp_rw [mul_sub]
  rw [integral_sub (put_gaussian_integrable k x _ hw).integrableOn
    (put_gaussian_integrable k (2*b-x) _ hw).integrableOn,
    truncated_put_integral b k x _ hk hw,
    truncated_put_integral b k (2*b-x) _ hk hw]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_killed_put_general
