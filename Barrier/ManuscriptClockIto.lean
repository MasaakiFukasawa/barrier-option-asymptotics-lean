import ManuscriptVarianceClock
import ManuscriptKilledIto

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The actual integrated forward-variance clock in the Gaussian Ito identity.
Only measurability and integrability of the deterministic curve are required. -/
theorem clock_killed_ito {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X C : HalfClosedTime → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (a : ℝ → ℝ) (ham : Measurable a) (hai : IntervalIntegrable a volume 0 1)
    (c : ℝ) (hc : 0 < c) (ha : ∀ s ∈ Icc (0:ℝ) 1, c ≤ a s)
    (G : Ω × ℝ → ℝ) (hGm : ∀ ω, Measurable (fun r => G (ω,r)))
    (hGi : ∀ r, 0 ≤ r → ∀ᵐ ω ∂P, IntervalIntegrable (fun s => G (ω,s)) volume 0 r)
    (hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω = ∫ s in 0..r, G (ω,s))
    (b k T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    ∃ N : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P F N ∧
      ∀ r ∈ Icc 0 T,
        (fun ω => killedPut b k (X (realTimeClamp r) ω) (Real.sqrt (varianceClock a (realTimeClamp r)))) =ᵐ[P]
          fun ω => killedPut b k (X ⊥ ω) (Real.sqrt (∫ s in (0:ℝ)..1, a s)) + N (realTimeClamp r) ω -
            (∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω) (varianceClock a (realTimeClamp s))*a s) +
            (∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω) (varianceClock a (realTimeClamp s))*G (ω,s)) := by
  have hδ : 0 < c*(1-T) := mul_pos hc (sub_pos.mpr hT1)
  obtain ⟨N,hN,he⟩ := killed_price_ito P F hF hle hnull X C hX hC (varianceClock a)
    (fun _ _ => (varianceClock_continuous a hai).continuousAt)
    ((varianceClock_antitone a hai (fun s hs => hc.le.trans (ha s hs))).antitoneOn _)
    (varianceClockDrift a) (ham.indicator measurableSet_Icc |>.neg)
    (fun _ _ => (varianceClock_drift_integrable a hai).intervalIntegrable)
    (varianceClock_drift_identity a) G hGm hGi hCG b k (c*(1-T)) T hδ hT
    (fun r hr => (mul_le_mul_of_nonneg_left (sub_le_sub_left hr.2 1) hc.le).trans
      (varianceClock_lower_bound a hai c r ⟨hr.1,hr.2.trans hT1.le⟩ ha))
  refine ⟨N,hN,?_⟩
  intro r hr
  filter_upwards [he r hr] with ω hω
  have hi : (∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω)
      (varianceClock a (realTimeClamp s))*varianceClockDrift a s) =
      -(∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω)
        (varianceClock a (realTimeClamp s))*a s) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    simp only [varianceClockDrift, Set.indicator_of_mem (show s ∈ Icc (0:ℝ) 1 from
      ⟨hs.1,hs.2.trans (hr.2.trans hT1.le)⟩), mul_neg]
  rw [varianceClock_initial,hi] at hω
  simpa only [sub_eq_add_neg] using hω

end BarrierManuscript
#print axioms BarrierManuscript.clock_killed_ito
