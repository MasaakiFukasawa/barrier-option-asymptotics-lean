import ManuscriptStoppedBracket
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

noncomputable def varianceClock (a : ℝ → ℝ) (t : HalfClosedTime) : ℝ :=
  (∫ s in (0:ℝ)..1, a s) - ∫ s in 0..(finitePrefixTime 1 (by norm_num) t).val, a s

noncomputable def varianceClockDrift (a : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(Icc (0:ℝ) 1).indicator a s

theorem prefix_real_value (r : ℝ) (hr : 0 ≤ r) :
    (finitePrefixTime 1 (by norm_num) (realTimeClamp (T := (⊤:EReal)) r)).val = min r 1 := by
  change (min (realTimeClamp (T := (⊤:EReal)) r : EReal) (1:EReal)).toReal = min r 1
  rw [real_time_clamp_eq r hr le_top]
  change (min (r : EReal) ((1:ℝ):EReal)).toReal = min r 1
  rcases le_total r 1 with h | h
  · rw [min_eq_left (EReal.coe_le_coe h), min_eq_left h, EReal.toReal_coe]
  · rw [min_eq_right (EReal.coe_le_coe h), min_eq_right h, EReal.toReal_coe]

theorem varianceClock_continuous (a : ℝ → ℝ) (ha : IntervalIntegrable a volume 0 1) :
    Continuous (varianceClock a) := by
  have hp : ContinuousOn (fun r : ℝ => ∫ s in 0..r, a s) (Icc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      intervalIntegral.continuousOn_primitive_interval' ha left_mem_uIcc
  exact continuous_const.sub ((continuousOn_iff_continuous_restrict.mp hp).comp
    (finite_prefix_time_continuous 1 (by norm_num)))

theorem varianceClock_drift_integrable (a : ℝ → ℝ) (ha : IntervalIntegrable a volume 0 1) :
    Integrable (varianceClockDrift a) volume := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp ha
  exact (hi.integrable_indicator measurableSet_Icc).neg

theorem varianceClock_initial (a : ℝ → ℝ) : varianceClock a ⊥ = ∫ s in (0:ℝ)..1, a s := by
  have hz : (finitePrefixTime 1 (by norm_num) (⊥ : HalfClosedTime)).val = 0 := by
    change (min (0:EReal) 1).toReal = 0
    norm_num
  simp only [varianceClock,hz,intervalIntegral.integral_same,sub_zero]

/-- The absolutely continuous drift identity is proved for a merely
integrable variance curve, with no continuity hypothesis on that curve. -/
theorem varianceClock_drift_identity (a : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    varianceClock a (realTimeClamp r) = varianceClock a ⊥ +
      ∫ s in 0..r, varianceClockDrift a s := by
  rw [varianceClock_initial]
  unfold varianceClock
  rw [prefix_real_value r hr]
  have hi : (∫ s in 0..r, varianceClockDrift a s) =
      -(∫ s in 0..min r 1, a s) := by
    unfold varianceClockDrift
    rw [intervalIntegral.integral_neg]
    have hcut : (∫ s in 0..r, (Icc (0:ℝ) 1).indicator a s) =
        ∫ s in 0..r, if s ≤ 1 then a s else 0 := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hr] at hs
      simp only [Set.indicator_apply, mem_Icc, hs.1, true_and]
    change -(∫ s in 0..r, (Icc (0:ℝ) 1).indicator a s) = _
    rw [hcut, stopped_density_integral a 1 r (by norm_num) hr, min_comm r 1]
  rw [hi]
  ring


theorem varianceClock_antitone (a : ℝ → ℝ) (ha : IntervalIntegrable a volume 0 1)
    (hn : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ a s) : Antitone (varianceClock a) := by
  intro t u htu
  let p := (finitePrefixTime 1 (by norm_num) t).val
  let q := (finitePrefixTime 1 (by norm_num) u).val
  have hp : p ∈ Icc (0:ℝ) 1 := (finitePrefixTime 1 (by norm_num) t).property
  have hq : q ∈ Icc (0:ℝ) 1 := (finitePrefixTime 1 (by norm_num) u).property
  have hpq : p ≤ q := finite_prefix_time_mono 1 (by norm_num) htu
  have haq : IntervalIntegrable a volume 0 q := ha.mono_set (by
    simp only [uIcc_of_le hq.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hq.2)
  have hnon : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) q)] a :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun s hs => hn s ⟨hs.1.le,hs.2.trans hq.2⟩))
  have hm := intervalIntegral.integral_mono_interval (le_refl (0:ℝ)) hp.1 hpq hnon haq
  exact sub_le_sub_left hm _

theorem varianceClock_remaining (a : ℝ → ℝ) (ha : IntervalIntegrable a volume 0 1)
    (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    varianceClock a (realTimeClamp r) = ∫ s in r..1, a s := by
  have h0r : IntervalIntegrable a volume 0 r := ha.mono_set (by
    simp only [uIcc_of_le hr.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hr.2)
  have hr1 : IntervalIntegrable a volume r 1 := ha.mono_set (by
    simp only [uIcc_of_le hr.2, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc hr.1 le_rfl)
  unfold varianceClock
  rw [prefix_real_value r hr.1, min_eq_left hr.2]
  linarith [intervalIntegral.integral_add_adjacent_intervals h0r hr1]

theorem varianceClock_lower_bound (a : ℝ → ℝ) (ha : IntervalIntegrable a volume 0 1)
    (c r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) (hc : ∀ s ∈ Icc (0:ℝ) 1, c ≤ a s) :
    c * (1-r) ≤ varianceClock a (realTimeClamp r) := by
  rw [varianceClock_remaining a ha r hr]
  have hr1 : IntervalIntegrable a volume r 1 := ha.mono_set (by
    simp only [uIcc_of_le hr.2, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc hr.1 le_rfl)
  have hm := intervalIntegral.integral_mono_on hr.2 intervalIntegrable_const hr1
    (fun s hs => hc s ⟨hr.1.trans hs.1,hs.2⟩)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hm

end BarrierManuscript
#print axioms BarrierManuscript.prefix_real_value
#print axioms BarrierManuscript.varianceClock_continuous
#print axioms BarrierManuscript.varianceClock_drift_integrable
#print axioms BarrierManuscript.varianceClock_initial
#print axioms BarrierManuscript.varianceClock_drift_identity

#print axioms BarrierManuscript.varianceClock_antitone
#print axioms BarrierManuscript.varianceClock_remaining
#print axioms BarrierManuscript.varianceClock_lower_bound
