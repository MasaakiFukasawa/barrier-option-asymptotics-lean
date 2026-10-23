import ManuscriptDriftIdentification

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem cappedBarrier_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : HalfClosedTime → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (b : ℝ) :
    Measurable (cappedBarrier X b) := by
  have hτ := cappedBarrier_stopping F hF X hm hc b
  apply measurable_of_Iic
  intro r
  by_cases hr : 0 ≤ r
  · have he : (cappedBarrier X b) ⁻¹' Iic r =
        {ω | realTimeClamp (T := (⊤:EReal)) (cappedBarrier X b ω) ≤ realTimeClamp r} := by
      ext ω
      change cappedBarrier X b ω ≤ r ↔ realTimeClamp (cappedBarrier X b ω) ≤ (realTimeClamp (T := (⊤:EReal)) r)
      constructor
      · exact fun h => real_time_clamp_mono (T := (⊤:EReal)) h
      · intro h
        change (realTimeClamp (T := (⊤:EReal)) (cappedBarrier X b ω) : EReal) ≤ (realTimeClamp (T := (⊤:EReal)) r : EReal) at h
        rw [real_time_clamp_eq _ (cappedBarrier_range X b ω).1 le_top,real_time_clamp_eq r hr le_top] at h
        exact EReal.coe_le_coe_iff.mp h
    rw [he]
    exact hle _ _ (hτ _)
  · have he : (cappedBarrier X b) ⁻¹' Iic r = ∅ := by
      ext ω
      simp only [mem_preimage,mem_Iic,mem_empty_iff_false,iff_false]
      exact fun h => hr ((cappedBarrier_range X b ω).1.trans h)
    rw [he]
    exact MeasurableSet.empty

theorem stock_real_joint_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (X : HalfClosedTime → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) :
    Measurable (fun z : Ω × ℝ => X (realTimeClamp z.2) z.1) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (fun ω => (hc ω).comp real_time_clamp_continuous)
    (fun r : ℝ => (hm (realTimeClamp r)).mono (hle _) le_rfl)
  exact h.comp measurable_swap

theorem stoppedThetaKernel_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : HalfClosedTime → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω))
    (a : ℝ → ℝ) (ham : Measurable a) (hai : IntervalIntegrable a volume 0 1) (b k : ℝ) :
    Measurable (stoppedThetaKernel X a b k) := by
  have hx := stock_real_joint_measurable F hle X hm hc
  have ht := cappedBarrier_measurable F hF hle X hm hc b
  have hw : Measurable (fun z : Ω × ℝ => Real.sqrt (varianceClock a (realTimeClamp z.2))) :=
    (((varianceClock_continuous a hai).comp real_time_clamp_continuous).sqrt.measurable).comp measurable_snd
  unfold stoppedThetaKernel thetaKernel
  apply Measurable.ite (measurableSet_le measurable_snd (ht.comp measurable_fst))
  · exact ((ham.comp measurable_snd).div (measurable_const.mul hw)).mul
      ((phi_contDiff.continuous.measurable.comp (((measurable_const.add hx).sub measurable_const).div hw)).sub
        (phi_contDiff.continuous.measurable.comp ((measurable_const.sub hx).div hw)))
  · exact measurable_const

end BarrierManuscript
#print axioms BarrierManuscript.cappedBarrier_measurable
#print axioms BarrierManuscript.stock_real_joint_measurable
#print axioms BarrierManuscript.stoppedThetaKernel_measurable
