import ManuscriptGeometricModel
import ManuscriptBrownianScaling

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem linearClock_comp (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (t : HalfClosedTime) :
    linearClock a ha (linearClock c hc t) = linearClock (a*c) (mul_pos ha hc) t := by
  by_cases ht : t=⊤
  · subst t; simp only [OrderIso.map_top]
  · obtain ⟨r,hr,_,rfl⟩ := finite_closed_time_real t (lt_top_iff_ne_top.mpr ht)
    rw [linear_clock_finite c hc r hr,linear_clock_finite a ha (c*r) (mul_nonneg hc.le hr),
      linear_clock_finite (a*c) (mul_pos ha hc) r hr,mul_assoc]

theorem pathMaximum_mul_pos {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : C(K,ℝ)) (c : ℝ) (hc : 0 < c) :
    pathMaximum (⟨fun t => c*f t,f.continuous.const_mul c⟩ : C(K,ℝ)) = c*pathMaximum f := by
  have h := pathMaximum_div f c⁻¹ (inv_pos.mpr hc)
  simpa only [div_inv_eq_mul,mul_comm] using h

theorem prefixMaximum_rescaling {Ω : Type*}
    (X Y : HalfClosedTime → Ω → ℝ)
    (hX : ∀ ω, Continuous (fun t => X t ω)) (hY : ∀ ω, Continuous (fun t => Y t ω))
    (u c : ℝ) (hu : 0 < u) (hc : 0 < c)
    (he : ∀ t ω, X (min (realTimeClamp u) (linearClock u hu t)) ω =
      c*Y (min (realTimeClamp 1) t) ω) (ω : Ω) :
    prefixMaximum X hX (realTimeClamp u) ω = c*prefixMaximum Y hY (realTimeClamp 1) ω := by
  rw [prefixMaximum, prefixMaximum,← pathMaximum_mul_pos _ c hc]
  unfold pathMaximum
  congr 1
  ext y
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨(linearClock u hu).symm t,?_⟩
    have hh := he ((linearClock u hu).symm t) ω
    rw [(linearClock u hu).apply_symm_apply] at hh
    exact hh.symm.trans ht
  · rintro ⟨t,ht⟩
    exact ⟨linearClock u hu t,(he t ω).trans ht⟩

theorem normalized_stock_time_scaling (z θ v u : ℝ) (hθ : 0 < θ) (hv : 0 < v) (hu : 0 < u) :
    z/Real.sqrt (θ*v) = Real.sqrt u*(z/Real.sqrt ((θ*u)*v)) := by
  rw [show (θ*u)*v=u*(θ*v) by ring,Real.sqrt_mul hu.le]
  field_simp

theorem normalized_variance_time_scaling (z θ u H : ℝ) (hθ : 0 < θ) (hu : 0 < u) :
    z/θ^H=u^H*(z/(θ*u)^H) := by
  rw [Real.mul_rpow hθ.le hu.le]
  field_simp [Real.rpow_pos_of_pos hθ H |>.ne',Real.rpow_pos_of_pos hu H |>.ne']

end BarrierManuscript
#print axioms BarrierManuscript.linearClock_comp
#print axioms BarrierManuscript.pathMaximum_mul_pos
#print axioms BarrierManuscript.prefixMaximum_rescaling
#print axioms BarrierManuscript.normalized_stock_time_scaling
#print axioms BarrierManuscript.normalized_variance_time_scaling
