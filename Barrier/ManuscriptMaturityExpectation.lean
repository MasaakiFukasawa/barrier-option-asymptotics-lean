import ManuscriptStoppedExpectation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- Remove the terminal cutoff in the stopped expectation identity. The
payoff is at the actual barrier-stopped endpoint; the no-hit payoff
identification is a separate pathwise result. -/
theorem maturity_price_expectation {Ω : Type*} [m : MeasurableSpace Ω]
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
    (b k : ℝ) (hk : k ≤ b) (hb : ∀ᵐ ω ∂P, X ⊥ ω < b)
    (hdi : Integrable (barrierDrift X G a b k) (P.prod (volume.restrict (Ioo 0 1))))
    (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ᵐ ω ∂P, ∀ t, |X (min (realTimeClamp (cappedBarrier X b ω)) t) ω| ≤ D ω)
    (t : ℕ → ℝ) (ht : ∀ n, t n ∈ Ico (0:ℝ) 1) (htlim : Tendsto t atTop (𝓝 1)) :
    (∫ ω, max (k-X (realTimeClamp (cappedBarrier X b ω)) ω) 0 ∂P) =
      killedPut b k 0 (Real.sqrt (∫ s in (0:ℝ)..1, a s)) +
        ∫ s in (0:ℝ)..1, ∫ ω, barrierDrift X G a b k (ω,s) ∂P := by
  let Y := fun s ω => X (min (realTimeClamp (cappedBarrier X b ω)) s) ω
  let w := fun n => Real.sqrt (varianceClock a (realTimeClamp (t n)))
  let x := fun ω => X (realTimeClamp (cappedBarrier X b ω)) ω
  have hτ := cappedBarrier_stopping F hF X hXm hXc b
  have hY := hX.stopped P F hF hle (fun ω => realTimeClamp (cappedBarrier X b ω)) hτ
  have hY1 ω : Y (realTimeClamp 1) ω = x ω := by
    change X (min _ _) ω = _
    rw [min_eq_left (real_time_clamp_mono (cappedBarrier_range X b ω).2)]
  have hxc ω : Continuous (fun s => Y s ω) := (hXc ω).comp (continuous_const.min continuous_id)
  have hw0 : Tendsto w atTop (𝓝 (0:ℝ)) := by
    have hv : varianceClock a (realTimeClamp 1) = 0 := by
      rw [varianceClock_remaining a hai 1 ⟨by norm_num,le_rfl⟩,intervalIntegral.integral_same]
    simpa only [w,Function.comp_def,hv,Real.sqrt_zero] using
      (((varianceClock_continuous a hai).comp real_time_clamp_continuous).sqrt.tendsto 1).comp htlim
  have hw : Tendsto w atTop (𝓝[>] (0:ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hw0,Filter.Eventually.of_forall (fun n => by
    change 0 < Real.sqrt (varianceClock a (realTimeClamp (t n)))
    apply Real.sqrt_pos.mpr
    exact lt_of_lt_of_le (mul_pos hc (sub_pos.mpr (ht n).2))
      (varianceClock_lower_bound a hai c (t n) ⟨(ht n).1,(ht n).2.le⟩ ha))⟩
  have hW n : |w n| ≤ Real.sqrt (∫ s in (0:ℝ)..1, a s) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    rw [← varianceClock_initial a]
    exact varianceClock_antitone a hai (fun s hs => hc.le.trans (ha s hs)) bot_le
  have hterm := killed_terminal_expectation P (fun n => Y (realTimeClamp (t n))) x w b k _ hk
    (fun n => ((hY.adapted P F _ (changed_time_finite _ (ht n).1)).mono (hle _) le_rfl).aestronglyMeasurable)
    (ae_of_all _ fun ω => by
      simpa only [Function.comp_def,hY1] using ((hxc ω).comp real_time_clamp_continuous).tendsto 1 |>.comp htlim)
    (hb.mono fun ω hω => by
      rw [← hY1 ω]
      exact cappedBarrier_below_at X hXc b ω hω _)
    hw hW D hD (hbound.mono fun ω hω n => hω _)
  have hig : IntervalIntegrable (fun s => ∫ ω, barrierDrift X G a b k (ω,s) ∂P) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr
    exact hdi.integral_prod_right
  have hp : ContinuousOn (fun r => ∫ s in (0:ℝ)..r, ∫ ω, barrierDrift X G a b k (ω,s) ∂P) (Icc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      intervalIntegral.continuousOn_primitive_interval' hig left_mem_uIcc
  have htwithin : Tendsto t atTop (𝓝[Icc (0:ℝ) 1] 1) := tendsto_nhdsWithin_iff.mpr
    ⟨htlim,Filter.Eventually.of_forall fun n => ⟨(ht n).1,(ht n).2.le⟩⟩
  have hi := Filter.Tendsto.comp (hp 1 ⟨by norm_num,le_rfl⟩) htwithin
  have hsum := hi.const_add (killedPut b k 0 (Real.sqrt (∫ s in (0:ℝ)..1, a s)))
  have he n := stopped_price_expectation P F hF hle hnull X C hX hXm hXc hC a ham hai c hc ha
    G hGm hGi hCG b k (t n) (ht n).1 (ht n).2 hdi D hD hbound
  have hsum' : Tendsto (fun n => ∫ ω, killedPut b k (Y (realTimeClamp (t n)) ω) (w n) ∂P) atTop
      (𝓝 (killedPut b k 0 (Real.sqrt (∫ s in (0:ℝ)..1, a s)) +
        ∫ s in (0:ℝ)..1, ∫ ω, barrierDrift X G a b k (ω,s) ∂P)) := by
    convert hsum using 1
    funext n
    exact he n
  exact tendsto_nhds_unique hterm hsum'

end BarrierManuscript
#print axioms BarrierManuscript.maturity_price_expectation
