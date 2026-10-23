import ManuscriptClockIto
import ManuscriptCappedBarrier

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem varianceGamma_boundary (b k r : ℝ) : varianceGamma b k b r = 0 := by
  unfold varianceGamma
  have : k-2*b+b=k-b := by ring
  rw [this,sub_self,zero_div]

theorem varianceGamma_continuousAt (b k : ℝ) (z : ℝ × ℝ) (hz : 0 < z.2) :
    ContinuousAt (fun z : ℝ × ℝ => varianceGamma b k z.1 z.2) z := by
  have hs : ContinuousAt (fun z : ℝ × ℝ => Real.sqrt z.2) z := continuousAt_snd.sqrt
  have hn : Real.sqrt z.2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hz)
  exact ((phi_contDiff.continuous.continuousAt.comp ((continuousAt_const.sub continuousAt_fst).div hs hn)).sub
    (phi_contDiff.continuous.continuousAt.comp ((continuousAt_const.add continuousAt_fst).div hs hn))).div
      (continuousAt_const.mul hs) (mul_ne_zero (by norm_num) hn)

theorem stopped_density_intervalIntegrable (g : ℝ → ℝ) (τ r : ℝ)
    (hg : IntervalIntegrable g volume 0 r) :
    IntervalIntegrable (fun s => if s ≤ τ then g s else 0) volume 0 r := by
  exact ⟨hg.1.indicator measurableSet_Iic,hg.2.indicator measurableSet_Iic⟩

/-- The forward-variance Ito formula for the actual capped barrier stop.
The drift is supported on times before the hit; at the barrier the Gaussian
second derivative vanishes exactly. -/
theorem stopped_clock_killed_ito {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X C : HalfClosedTime → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hXm : ∀ t, Measurable[F t] (X t)) (hXc : ∀ ω, Continuous (fun t => X t ω))
    (hC : LocalCovarianceWitness P F X X C)
    (a : ℝ → ℝ) (ham : Measurable a) (hai : IntervalIntegrable a volume 0 1)
    (c : ℝ) (hc : 0 < c) (ha : ∀ s ∈ Icc (0:ℝ) 1, c ≤ a s)
    (G : Ω × ℝ → ℝ) (hGm : ∀ ω, Measurable (fun r => G (ω,r)))
    (hGi : ∀ r, 0 ≤ r → ∀ᵐ ω ∂P, IntervalIntegrable (fun s => G (ω,s)) volume 0 r)
    (hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω = ∫ s in 0..r, G (ω,s))
    (b k T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1) :
    let τ := cappedBarrier X b
    let Y := fun t ω => X (min (realTimeClamp (τ ω)) t) ω
    ∃ N : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P F N ∧
      ∀ r ∈ Icc 0 T,
        (fun ω => killedPut b k (Y (realTimeClamp r) ω) (Real.sqrt (varianceClock a (realTimeClamp r)))) =ᵐ[P]
          fun ω => killedPut b k (X ⊥ ω) (Real.sqrt (∫ s in (0:ℝ)..1, a s)) + N (realTimeClamp r) ω +
            ∫ s in 0..r, if s ≤ τ ω then
              varianceGamma b k (X (realTimeClamp s) ω) (varianceClock a (realTimeClamp s)) * (G (ω,s)-a s)
            else 0 := by
  dsimp only
  let τ := cappedBarrier X b
  let Y := fun t ω => X (min (realTimeClamp (τ ω)) t) ω
  let D := fun t ω => C (min (realTimeClamp (τ ω)) t) ω
  let J := fun z : Ω × ℝ => if z.2 ≤ τ z.1 then G z else 0
  have hτ := cappedBarrier_stopping F hF X hXm hXc b
  obtain ⟨hY,hD,hDJ⟩ := stopped_covariance_density P F hF hle X C hX hC G hCG τ
    (fun ω => (cappedBarrier_range X b ω).1) hτ
  have hJm ω : Measurable (fun s => J (ω,s)) := by
    exact (hGm ω).ite (show MeasurableSet {s : ℝ | s ≤ τ ω} from measurableSet_Iic) measurable_const
  have hJi r (hr : 0 ≤ r) : ∀ᵐ ω ∂P, IntervalIntegrable (fun s => J (ω,s)) volume 0 r :=
    (hGi r hr).mono fun ω hω => stopped_density_intervalIntegrable _ (τ ω) r hω
  obtain ⟨N,hN,he⟩ := clock_killed_ito P F hF hle hnull Y D hY hD a ham hai c hc ha
    J hJm hJi hDJ b k T hT hT1
  refine ⟨N,hN,?_⟩
  intro r hr
  filter_upwards [he r hr,hGi r hr.1] with ω hω hGω
  have hγ : ContinuousOn (fun s => varianceGamma b k (Y (realTimeClamp s) ω)
      (varianceClock a (realTimeClamp s))) (Icc 0 r) := by
    intro s hs
    have hp := varianceClock_lower_bound a hai c s ⟨hs.1,hs.2.trans (hr.2.trans hT1.le)⟩ ha
    have hpos : 0 < varianceClock a (realTimeClamp s) :=
      lt_of_lt_of_le (mul_pos hc (sub_pos.mpr (hs.2.trans_lt (hr.2.trans_lt hT1)))) hp
    apply ContinuousAt.continuousWithinAt
    apply (varianceGamma_continuousAt b k _ hpos).comp (f := fun s : ℝ =>
      (Y (realTimeClamp s) ω, varianceClock a (realTimeClamp s)))
    exact (((hXc ω).comp (continuous_const.min continuous_id)).comp real_time_clamp_continuous).continuousAt.prodMk
      ((varianceClock_continuous a hai).comp real_time_clamp_continuous).continuousAt
  have har : IntervalIntegrable a volume 0 r := hai.mono_set (by
    simp only [uIcc_of_le hr.1,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (hr.2.trans hT1.le))
  have hga := har.continuousOn_mul (by simpa only [uIcc_of_le hr.1] using hγ)
  have hgj := (stopped_density_intervalIntegrable _ (τ ω) r hGω).continuousOn_mul
    (by simpa only [uIcc_of_le hr.1] using hγ)
  have hcomb : (∫ s in 0..r, varianceGamma b k (Y (realTimeClamp s) ω)
      (varianceClock a (realTimeClamp s))*J (ω,s)) -
      (∫ s in 0..r, varianceGamma b k (Y (realTimeClamp s) ω)
        (varianceClock a (realTimeClamp s))*a s) =
      ∫ s in 0..r, if s ≤ τ ω then varianceGamma b k (X (realTimeClamp s) ω)
        (varianceClock a (realTimeClamp s))*(G (ω,s)-a s) else 0 := by
    rw [← intervalIntegral.integral_sub hgj hga]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    by_cases hst : s ≤ τ ω
    · have hm : realTimeClamp (T := (⊤:EReal)) s ≤ realTimeClamp (τ ω) := real_time_clamp_mono hst
      simp only [Y,J,hst,ite_true,min_eq_right hm]
      ring
    · have hts : realTimeClamp (T := (⊤:EReal)) (τ ω) ≤ realTimeClamp s := real_time_clamp_mono (le_of_not_ge hst)
      have hhit := cappedBarrier_hit X hXc b ω ((lt_of_not_ge hst).trans_le (hs.2.trans (hr.2.trans hT1.le)))
      change X (realTimeClamp (τ ω)) ω = b at hhit
      simp only [Y,J,hst,ite_false,min_eq_left hts,hhit,varianceGamma_boundary,mul_zero,zero_mul,sub_self]
  have hinit : Y ⊥ ω = X ⊥ ω := by simp [Y]
  rw [hinit] at hω
  change killedPut b k (Y (realTimeClamp r) ω) _ = _
  rw [← hcomb]
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.varianceGamma_boundary
#print axioms BarrierManuscript.varianceGamma_continuousAt
#print axioms BarrierManuscript.stopped_density_intervalIntegrable
#print axioms BarrierManuscript.stopped_clock_killed_ito
