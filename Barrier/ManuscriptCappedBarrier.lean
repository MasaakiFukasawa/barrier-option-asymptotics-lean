import ManuscriptBarrierPath
import ManuscriptVarianceClock

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

noncomputable def cappedBarrier {Ω : Type*} (X : HalfClosedTime → Ω → ℝ) (b : ℝ) (ω : Ω) : ℝ :=
  (finitePrefixTime 1 (by norm_num) (barrierTime X b ω)).val

theorem cappedBarrier_range {Ω : Type*} (X : HalfClosedTime → Ω → ℝ) (b : ℝ) (ω : Ω) :
    cappedBarrier X b ω ∈ Icc (0:ℝ) 1 := (finitePrefixTime 1 (by norm_num) _).property

theorem cappedBarrier_clamp {Ω : Type*} (X : HalfClosedTime → Ω → ℝ) (b : ℝ) (ω : Ω) :
    realTimeClamp (cappedBarrier X b ω) = min (realTimeClamp 1) (barrierTime X b ω) :=
  finite_prefix_time_clamp 1 (by norm_num) le_top _

theorem cappedBarrier_stopping {Ω : Type*}
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F)
    (X : HalfClosedTime → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hc : ∀ ω, Continuous (fun t => X t ω)) (b : ℝ) :
    ∀ t, MeasurableSet[F t] {ω | realTimeClamp (cappedBarrier X b ω) ≤ t} := by
  simp_rw [cappedBarrier_clamp]
  exact (written_stopping_min_max F (fun _ => realTimeClamp 1) (barrierTime X b)
    (fun t => by by_cases ht : realTimeClamp (T := (⊤:EReal)) 1 ≤ t <;> simp [ht])
    (barrierTime_stopping F hF X hm hc b)).1

theorem cappedBarrier_below {Ω : Type*}
    (X : HalfClosedTime → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (b : ℝ) (h₀ : ∀ ω, X ⊥ ω < b) (ω : Ω) (t : HalfClosedTime) :
    X (min (realTimeClamp (cappedBarrier X b ω)) t) ω ≤ b := by
  rw [cappedBarrier_clamp, min_comm (realTimeClamp 1), min_assoc]
  exact stopped_path_below X hc b h₀ ω _


theorem cappedBarrier_below_at {Ω : Type*}
    (X : HalfClosedTime → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (b : ℝ) (ω : Ω) (h₀ : X ⊥ ω < b) (t : HalfClosedTime) :
    X (min (realTimeClamp (cappedBarrier X b ω)) t) ω ≤ b := by
  exact cappedBarrier_below (fun s (_ : Unit) => X s ω) (fun _ => hc ω) b (fun _ => h₀) () t

/-- Before the maturity cap, a stopped path really has hit the barrier. -/
theorem cappedBarrier_hit {Ω : Type*}
    (X : HalfClosedTime → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (b : ℝ) (ω : Ω) (hτ : cappedBarrier X b ω < 1) :
    X (realTimeClamp (cappedBarrier X b ω)) ω = b := by
  have hlt : realTimeClamp (cappedBarrier X b ω) < (realTimeClamp (T := (⊤:EReal)) 1) := by
    change (realTimeClamp (cappedBarrier X b ω) : EReal) < (realTimeClamp 1 : EReal)
    rw [real_time_clamp_eq _ (cappedBarrier_range X b ω).1 le_top,
      real_time_clamp_eq 1 (by norm_num) le_top]
    exact EReal.coe_lt_coe_iff.mpr hτ
  rw [cappedBarrier_clamp] at hlt ⊢
  have hh : barrierTime X b ω < realTimeClamp 1 := (min_lt_iff.mp hlt).resolve_left (lt_irrefl _)
  rw [min_eq_right hh.le]
  apply (barrierTime_hit_iff X hc b ω).mpr
  by_contra hn
  have hempty : {t | X t ω = b} = ∅ := by ext t; simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]; exact fun h => hn ⟨t,h⟩
  have htop : barrierTime X b ω = ⊤ := by simp [barrierTime,hempty]
  rw [htop] at hh
  exact not_lt_of_ge le_top hh


theorem cappedBarrier_hit_iff {Ω : Type*}
    (X : HalfClosedTime → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (b : ℝ) (ω : Ω) :
    X (realTimeClamp (cappedBarrier X b ω)) ω = b ↔
      ∃ r : HalfClosedTime, r ≤ realTimeClamp 1 ∧ X r ω = b := by
  constructor
  · intro h
    exact ⟨_,real_time_clamp_mono (cappedBarrier_range X b ω).2,h⟩
  · rintro ⟨r,hr,hv⟩
    have hbr : barrierTime X b ω ≤ r := sInf_le hv
    rw [cappedBarrier_clamp,min_eq_right (hbr.trans hr)]
    exact (barrierTime_hit_iff X hc b ω).mpr ⟨r,hv⟩

/-- Includes hits exactly at maturity. The strike is at or below the barrier. -/
theorem cappedBarrier_terminal_payoff {Ω : Type*}
    (X : HalfClosedTime → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => X t ω))
    (b k : ℝ) (hk : k ≤ b) (ω : Ω) :
    max (k-X (realTimeClamp (cappedBarrier X b ω)) ω) 0 =
      if (∃ r : HalfClosedTime, r ≤ realTimeClamp 1 ∧ X r ω = b) then 0
      else max (k-X (realTimeClamp 1) ω) 0 := by
  classical
  by_cases hh : ∃ r : HalfClosedTime, r ≤ realTimeClamp 1 ∧ X r ω = b
  · rw [ite_eq_left hh,(cappedBarrier_hit_iff X hc b ω).mpr hh,
      max_eq_right (sub_nonpos.mpr hk)]
  · have he : cappedBarrier X b ω = 1 := by
      apply le_antisymm (cappedBarrier_range X b ω).2
      by_contra hn
      exact hh ((cappedBarrier_hit_iff X hc b ω).mp (cappedBarrier_hit X hc b ω (lt_of_not_ge hn)))
    rw [ite_eq_right hh,he]

end BarrierManuscript
#print axioms BarrierManuscript.cappedBarrier_range
#print axioms BarrierManuscript.cappedBarrier_clamp
#print axioms BarrierManuscript.cappedBarrier_stopping
#print axioms BarrierManuscript.cappedBarrier_below
#print axioms BarrierManuscript.cappedBarrier_hit

#print axioms BarrierManuscript.cappedBarrier_hit_iff
#print axioms BarrierManuscript.cappedBarrier_terminal_payoff

#print axioms BarrierManuscript.cappedBarrier_below_at
