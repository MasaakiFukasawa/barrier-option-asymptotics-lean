import ManuscriptStoppedClockIto
import ManuscriptFiniteExpectation
import ManuscriptTerminalExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

noncomputable def barrierDrift {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (G : Ω × ℝ → ℝ) (a : ℝ → ℝ) (b k : ℝ) (z : Ω × ℝ) : ℝ :=
  if z.2 ≤ cappedBarrier X b z.1 then
    varianceGamma b k (X (realTimeClamp z.2) z.1) (varianceClock a (realTimeClamp z.2))*(G z-a z.2)
  else 0

theorem killedPut_continuousAt (b k : ℝ) (z : ℝ × ℝ) (hz : z.2 ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => killedPut b k z.1 z.2) z := by
  have hp (x : ℝ × ℝ → ℝ) (hx : ContinuousAt x z) :
      ContinuousAt (fun z : ℝ × ℝ => put k (x z) z.2) z := by
    have hd : ContinuousAt (fun z : ℝ × ℝ => (k-x z)/z.2) z :=
      (continuousAt_const.sub hx).div continuousAt_snd hz
    exact ((continuousAt_const.sub hx).mul (normalCDF_contDiff.continuous.continuousAt.comp hd)).add
      (continuousAt_snd.mul (phi_contDiff.continuous.continuousAt.comp hd))
  exact (hp _ continuousAt_fst).sub (hp _ (continuousAt_const.sub continuousAt_fst))

/-- The finite-cutoff barrier pricing expectation identity, with the actual
hitting time, Gaussian kernel, integrated forward variance, and constructed
Ito martingale. Its drift-integrability hypothesis is discharged separately
by the manuscript's Gaussian/UI estimates. -/
theorem stopped_price_expectation {Ω : Type*} [m : MeasurableSpace Ω]
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
    (b k T : ℝ) (hT : 0 ≤ T) (hT1 : T < 1)
    (hdi : Integrable (barrierDrift X G a b k) (P.prod (volume.restrict (Ioo 0 1))))
    (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ᵐ ω ∂P, ∀ t, |X (min (realTimeClamp (cappedBarrier X b ω)) t) ω| ≤ D ω) :
    (∫ ω, killedPut b k (X (min (realTimeClamp (cappedBarrier X b ω)) (realTimeClamp T)) ω)
      (Real.sqrt (varianceClock a (realTimeClamp T))) ∂P) =
      killedPut b k 0 (Real.sqrt (∫ s in (0:ℝ)..1, a s)) +
        ∫ s in 0..T, ∫ ω, barrierDrift X G a b k (ω,s) ∂P := by
  let Y := fun t ω => X (min (realTimeClamp (cappedBarrier X b ω)) t) ω
  let pr := fun r ω => killedPut b k (Y (realTimeClamp r) ω) (Real.sqrt (varianceClock a (realTimeClamp r)))
  obtain ⟨N,hN,he⟩ := stopped_clock_killed_ito P F hF hle hnull X C hX hXm hXc hC a ham hai c hc ha
    G hGm hGi hCG b k T hT hT1
  have hpc ω : ContinuousOn (fun r => pr r ω) (Icc 0 T) := by
    intro r hr
    have hp := varianceClock_lower_bound a hai c r ⟨hr.1,hr.2.trans hT1.le⟩ ha
    have hpos : 0 < varianceClock a (realTimeClamp r) :=
      lt_of_lt_of_le (mul_pos hc (sub_pos.mpr (hr.2.trans_lt hT1))) hp
    apply ContinuousAt.continuousWithinAt
    apply (killedPut_continuousAt b k _ (ne_of_gt (Real.sqrt_pos.mpr hpos))).comp
      (f := fun r : ℝ => (Y (realTimeClamp r) ω,Real.sqrt (varianceClock a (realTimeClamp r))))
    exact (((hXc ω).comp (continuous_const.min continuous_id)).comp real_time_clamp_continuous).continuousAt.prodMk
      (((varianceClock_continuous a hai).comp real_time_clamp_continuous).sqrt.continuousAt)
  have hrep r (hr : r ∈ Icc 0 T) : pr r =ᵐ[P] fun ω =>
      killedPut b k 0 (Real.sqrt (∫ s in (0:ℝ)..1, a s)) + N (realTimeClamp r) ω +
        ∫ s in 0..r, barrierDrift X G a b k (ω,s) := by
    filter_upwards [he r hr,hX.initial P F] with ω hω hzero
    simpa only [pr,Y,barrierDrift,hzero,Pi.zero_apply] using hω
  let W := Real.sqrt (∫ s in (0:ℝ)..1, a s)
  let B := fun ω => 2*|k|+2*|b|+2*D ω+2*W*normalizer
  have hiB : Integrable B P := ((integrable_const _).add (hD.const_mul 2)).add (integrable_const _)
  have hb : ∀ᵐ ω ∂P, ∀ r ∈ Icc 0 T, |pr r ω| ≤ B ω := by
    filter_upwards [hbound] with ω hω
    intro r hr
    have hw : |Real.sqrt (varianceClock a (realTimeClamp r))| ≤ W := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      apply Real.sqrt_le_sqrt
      rw [← varianceClock_initial a]
      exact varianceClock_antitone a hai (fun s hs => hc.le.trans (ha s hs)) bot_le
    have h := killedPut_growth_bound b k (Y (realTimeClamp r) ω) (Real.sqrt (varianceClock a (realTimeClamp r)))
    have hm := mul_le_mul_of_nonneg_right hw normalizer_nonneg
    dsimp only [pr,B]
    linarith [hω (realTimeClamp r)]
  exact (finite_ito_expectation P F hF hle N hN T hT hT1.le pr _ hpc
    (barrierDrift X G a b k) hdi hrep B hiB hb).2

end BarrierManuscript
#print axioms BarrierManuscript.killedPut_continuousAt
#print axioms BarrierManuscript.stopped_price_expectation
