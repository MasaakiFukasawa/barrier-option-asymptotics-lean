import ManuscriptStockDriftIntegrable
import ManuscriptMaturityExpectation
import Mathlib.Topology.Order.IsLUB

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Complete stopped pricing expectation identity for a lower-bounded
normalized stock return. Both drift integrability and the path dominator
are derived here. The theorem's stochastic inputs are the local martingale
and its actual density, not an assumed pricing identity. -/
theorem stock_payoff_expectation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X C : HalfClosedTime → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hXm : ∀ t, Measurable[F t] (X t)) (hXc : ∀ ω, Continuous (fun t => X t ω))
    (hC : LocalCovarianceWitness P F X X C)
    (a : ℝ → ℝ) (ham : Measurable a) (hai : IntervalIntegrable a volume 0 1)
    (c U : ℝ) (hc : 0 < c) (hU : 0 ≤ U)
    (ha : ∀ s ∈ Icc (0:ℝ) 1, c^2 ≤ a s ∧ a s ≤ U^2)
    (G Y : Ω × ℝ → ℝ) (hYm : Measurable Y)
    (hGm : ∀ ω, Measurable (fun r => G (ω,r)))
    (hGi : ∀ r, 0 ≤ r → ∀ᵐ ω ∂P, IntervalIntegrable (fun s => G (ω,s)) volume 0 r)
    (hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω = ∫ s in 0..r, G (ω,s))
    (e h L lower b k : ℝ) (hb : 0 < b) (hk : k ≤ b)
    (hYs : ∀ s ∈ Ioo (0:ℝ) 1, Integrable (fun ω => Y (ω,s)) P)
    (hYL : ∀ s ∈ Ioo (0:ℝ) 1, (∫ ω, |Y (ω,s)| ∂P) ≤ L)
    (hG : ∀ᵐ z ∂P.prod (volume.restrict (Ioo (0:ℝ) 1)),
      G z = a z.2*(1+e*X (realTimeClamp z.2) z.1)^2*(1+h*Y z))
    (hlower : ∀ᵐ ω ∂P, ∀ t, lower ≤ X t ω) :
    (∫ ω, if (∃ r : HalfClosedTime, r ≤ realTimeClamp 1 ∧ X r ω = b) then 0
      else max (k-X (realTimeClamp 1) ω) 0 ∂P) =
      killedPut b k 0 (Real.sqrt (∫ s in (0:ℝ)..1, a s)) +
        ∫ s in (0:ℝ)..1, ∫ ω, barrierDrift X G a b k (ω,s) ∂P := by
  have hdi := stock_barrier_drift_integrable P F hF hle X hXm hXc G Y hYm a ham hai
    b k e h c U L hc hU ha hYs hYL hG
  have hinit : ∀ᵐ ω ∂P, X ⊥ ω < b := by
    filter_upwards [hX.initial P F] with ω hω
    simpa only [hω,Pi.zero_apply] using hb
  let D := max |lower| |b|
  have hbound : ∀ᵐ ω ∂P, ∀ t,
      |X (min (realTimeClamp (cappedBarrier X b ω)) t) ω| ≤ D := by
    filter_upwards [hlower,hinit] with ω hω hi
    intro t
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le lower).trans (hω _))
    · exact (cappedBarrier_below_at X hXc b ω hi t).trans ((le_abs_self b).trans (le_max_right _ _))
  obtain ⟨t,_,ht,htlim⟩ := exists_seq_strictMono_tendsto' (by norm_num : (0:ℝ) < 1)
  have he := maturity_price_expectation P F hF hle hnull X C hX hXm hXc hC a ham hai
    (c^2) (sq_pos_of_pos hc) (fun s hs => (ha s hs).1) G hGm hGi hCG b k hk hinit hdi
    (fun _ => D) (integrable_const D) hbound t (fun n => ⟨(ht n).1.le,(ht n).2⟩) htlim
  simpa only [cappedBarrier_terminal_payoff X hXc b k hk] using he

end BarrierManuscript
#print axioms BarrierManuscript.stock_payoff_expectation
