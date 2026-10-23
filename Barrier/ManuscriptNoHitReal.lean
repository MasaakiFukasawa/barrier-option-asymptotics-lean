import ManuscriptStockPathEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem nohit_real_iff {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => X t ω)) (ω : Ω) (b : ℝ) (h0 : X ⊥ ω < b) :
    (¬ ∃ t, t ≤ realTimeClamp 1 ∧ X t ω=b) ↔
      ∀ r ∈ Icc (0:ℝ) 1, X (realTimeClamp r) ω < b := by
  constructor
  · intro hn r hr
    by_contra hh
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (⊥:HalfClosedTime) ≤ realTimeClamp r from bot_le)
      (hc ω).continuousOn (show b ∈ Icc (X ⊥ ω) (X (realTimeClamp r) ω) from ⟨h0.le,le_of_not_gt hh⟩)
    exact hn ⟨t,ht.2.trans (real_time_clamp_mono hr.2),he⟩
  · intro h ⟨t,ht,he⟩
    obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t (ht.trans_lt (halfTimeClamp_finite 1))
    have hr1 : r ≤ 1 := by
      change (realTimeClamp r : EReal) ≤ (realTimeClamp 1 : EReal) at ht
      rw [real_time_clamp_eq r hr le_top,real_time_clamp_eq 1 (by norm_num) le_top,EReal.coe_le_coe_iff] at ht
      exact ht
    exact (ne_of_lt (h r ⟨hr,hr1⟩)) he

end BarrierManuscript
#print axioms BarrierManuscript.nohit_real_iff
