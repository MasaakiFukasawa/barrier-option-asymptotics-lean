import ManuscriptGeometricSDE
import ManuscriptBlackScholesPricing

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem linearClock_one (t : HalfClosedTime) : linearClock 1 zero_lt_one t=t := by
  by_cases ht : t=⊤
  · subst t; exact (linearClock 1 zero_lt_one).map_top
  · obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t (lt_top_iff_ne_top.mpr ht)
    rw [linear_clock_finite 1 zero_lt_one r hr,one_mul]

theorem geometric_normalized_model {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k w : ℝ) (hw : 0 < w) :
    ∃ M : NormalizedBarrierModel P b k,
      M.a=(fun _ => 1) ∧ M.c=1 ∧ M.U=1 ∧ M.L=0 ∧ M.e=w ∧
      M.Y=(fun _ => 0) ∧
      M.X=(fun t ω => (geometricStock B w (min (realTimeClamp 1) t) ω-1)/w) := by
  obtain ⟨hsa,hsc,hM,hI⟩ := geometricStock_sde P B w
  have hSDE : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (geometricStock B w (realTimeClamp z.2) z.1/1)*Real.sqrt (w^2))
      (fun t ω => geometricStock B w t ω/1-1) := by
    simpa only [div_one,Real.sqrt_sq_eq_abs,abs_of_pos hw,mul_comm] using hI
  obtain ⟨M,ha,hc,hU,hL,he,hh,hX,hY⟩ := stock_model_exists P B (geometricStock B w) (fun _ _ => w^2)
    1 (w^2) 1 1 zero_lt_one (sq_pos_of_pos hw) zero_lt_one hsa
    (fun _ _ => measurable_const) hsc (fun _ _ _ => continuousAt_const)
    (fun _ _ _ => by unfold geometricStock geometricFlow; positivity)
    (fun _ _ _ => sq_nonneg w) (by simpa only [div_one] using hM) hSDE
    (fun _ => 1) measurable_const intervalIntegrable_const 1 1 0 b k
    zero_lt_one zero_le_one (fun _ _ => by norm_num)
    (fun _ _ => by simp [hw.ne']) (fun _ _ => by simp [hw.ne'])
  refine ⟨M,ha,hc,hU,hL,?_,?_,?_⟩
  · simpa only [one_mul,Real.sqrt_sq_eq_abs,abs_of_pos hw] using he
  · simpa only [mul_one,Real.one_rpow,div_one,div_self (sq_pos_of_pos hw).ne',sub_self] using hY
  · simpa only [linearClock_one,div_one,one_mul,Real.sqrt_sq_eq_abs,abs_of_pos hw] using hX

end BarrierManuscript
#print axioms BarrierManuscript.linearClock_one
#print axioms BarrierManuscript.geometric_normalized_model
