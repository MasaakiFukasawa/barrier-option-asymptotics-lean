import ManuscriptBrownianMaximum
import ManuscriptDriftIdentification

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

noncomputable def prefixMaximum {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (t : HalfClosedTime) (ω : Ω) : ℝ :=
  pathMaximum ⟨fun r => X (min t r) ω, (hc ω).comp (continuous_const.min continuous_id)⟩

theorem prefixMaximum_lt_iff {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (t : HalfClosedTime) (ω : Ω)
    (b : ℝ) (h₀ : X ⊥ ω < b) :
    prefixMaximum X hc t ω < b ↔ ¬ ∃ r, r ≤ t ∧ X r ω = b := by
  let f : C(HalfClosedTime,ℝ) := ⟨fun r => X (min t r) ω,
    (hc ω).comp (continuous_const.min continuous_id)⟩
  have hle r : f r ≤ prefixMaximum X hc t ω :=
    le_csSup (path_range_bddAbove f) (mem_range_self r)
  constructor
  · intro h ⟨r,hr,he⟩
    have hh := (hle r).trans_lt h
    simpa only [f,ContinuousMap.coe_mk,min_eq_right hr,he,lt_self_iff_false] using hh
  · intro hn
    obtain ⟨r,hr⟩ := pathMaximum_attained f
    change pathMaximum f < b
    rw [← hr]
    by_contra h
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc (show (⊥ : HalfClosedTime) ≤ min t r from bot_le)
      (hc ω).continuousOn (show b ∈ Icc (X ⊥ ω) (X (min t r) ω) from ⟨h₀.le,le_of_not_gt h⟩)
    exact hn ⟨s,hs.2.trans (min_le_left _ _),he⟩

theorem barrierTime_le_iff_hit {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (t : HalfClosedTime)
    (ht : t < ⊤) (b : ℝ) (ω : Ω) :
    barrierTime X b ω ≤ t ↔ ∃ r, r ≤ t ∧ X r ω = b := by
  constructor
  · intro h
    refine ⟨barrierTime X b ω,h,(barrierTime_hit_iff X hc b ω).mpr ?_⟩
    by_contra hn
    have he : {r | X r ω = b} = ∅ := by ext r; simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]; exact fun hh => hn ⟨r,hh⟩
    have : barrierTime X b ω = ⊤ := by simp [barrierTime,he]
    exact (not_le_of_gt ht) (this ▸ h)
  · rintro ⟨r,hr,he⟩
    exact (show barrierTime X b ω ≤ r from sInf_le he).trans hr

theorem prefixMaximum_lt_iff_before_hit {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (t : HalfClosedTime)
    (ht : t < ⊤) (ω : Ω) (b : ℝ) (h₀ : X ⊥ ω < b) :
    prefixMaximum X hc t ω < b ↔ t < barrierTime X b ω := by
  rw [prefixMaximum_lt_iff X hc t ω b h₀,← barrierTime_le_iff_hit X hc t ht b ω,not_le]

theorem stoppedThetaKernel_survival {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (a : ℝ → ℝ)
    (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) (ω : Ω) (h₀ : X ⊥ ω < b) :
    stoppedThetaKernel X a b k (ω,u) =
      if prefixMaximum X hc (realTimeClamp u) ω < b then
        thetaKernel b k (a u) (Real.sqrt (varianceClock a (realTimeClamp u))) (X (realTimeClamp u) ω)
      else 0 := by
  have hclamp : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s →
      ((realTimeClamp (T := (⊤:EReal)) r) < realTimeClamp s ↔ r < s) := by
    intro r s hr hs
    change ((realTimeClamp r : HalfClosedTime) : EReal) < (realTimeClamp s : EReal) ↔ r < s
    rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq s hs le_top,EReal.coe_lt_coe_iff]
  have he : prefixMaximum X hc (realTimeClamp u) ω < b ↔ u < cappedBarrier X b ω := by
    rw [prefixMaximum_lt_iff_before_hit X hc _ (changed_time_finite u hu.1.le) ω b h₀]
    rw [← hclamp u _ hu.1.le (cappedBarrier_range X b ω).1,cappedBarrier_clamp,lt_min_iff]
    exact ⟨fun h => ⟨(hclamp u 1 hu.1.le (by norm_num)).mpr hu.2,h⟩,fun h => h.2⟩
  unfold stoppedThetaKernel
  dsimp only
  simp only [he]
  by_cases hl : u < cappedBarrier X b ω
  · simp [hl,hl.le]
  · by_cases heq : u = cappedBarrier X b ω
    · have hhit := cappedBarrier_hit X hc b ω (heq ▸ hu.2)
      rw [← heq] at hhit
      simp only [heq.le,ite_true,hl,ite_false,hhit,thetaKernel_varianceGamma,varianceGamma_boundary,mul_zero]
    · have hn : ¬u ≤ cappedBarrier X b ω := fun h => heq (le_antisymm h (le_of_not_gt hl))
      simp [hn,hl]

end BarrierManuscript
#print axioms BarrierManuscript.prefixMaximum_lt_iff
#print axioms BarrierManuscript.barrierTime_le_iff_hit
#print axioms BarrierManuscript.prefixMaximum_lt_iff_before_hit

#print axioms BarrierManuscript.stoppedThetaKernel_survival
