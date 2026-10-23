import ManuscriptBrownianStrictSurvival
import ManuscriptTiltedGaussianPut

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Continuous-monitoring Black--Scholes UOP valuation, derived from the
Brownian law and Girsanov. The barrier is strictly above the initial stock. -/
theorem geometric_brownian_barrier_price {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (K barrier w : ℝ) (hK : 0 < K) (hb : 1 < barrier) (hKb : K ≤ barrier) (hw : 0 < w) :
    (∫ ω, if (∀ r ∈ Icc (0:ℝ) 1,
        Real.exp (w*B.W 0 (realTimeClamp r) ω-w^2*r/2) < barrier)
      then max (K-Real.exp (w*B.W 0 (realTimeClamp 1) ω-w^2/2)) 0 else 0 ∂P) =
      bsKilledPut barrier K 1 w := by
  let b := Real.log barrier/w
  have hbp : 0 < b := div_pos (Real.log_pos hb) hw
  have hbe : Real.exp (w*b) = barrier := by
    dsimp only [b]
    rw [mul_div_cancel₀ _ hw.ne',Real.exp_log (zero_lt_one.trans hb)]
  have h := drifted_brownian_killed_density P B (w/2) b hbp
    (fun x => max (K-Real.exp (w*x)) 0) (by fun_prop)
  rw [tilted_killed_lognormal_integral K w b hK hw (by rwa [hbe]),hbe] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [drifted_survival_strict_ae P B (w/2) b hbp] with ω hs
  have he : (∀ r ∈ Icc (0:ℝ) 1, Real.exp (w*B.W 0 (realTimeClamp r) ω-w^2*r/2) < barrier) ↔
      (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-(w/2)*r ≤ b) := by
    rw [← hs]
    apply forall_congr'
    intro r
    apply forall_congr'
    intro _
    rw [← hbe,Real.exp_lt_exp]
    have hp : w*B.W 0 (realTimeClamp r) ω-w^2*r/2 = w*(B.W 0 (realTimeClamp r) ω-(w/2)*r) := by ring
    rw [hp,mul_lt_mul_iff_right₀ hw]
  simp only [he]
  split_ifs
  · congr 3
    ring
  · rfl

end BarrierManuscript
#print axioms BarrierManuscript.geometric_brownian_barrier_price
