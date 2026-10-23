import ManuscriptMaturityRescaling
import ManuscriptStockCoefficients

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem affine_barrier_equivalence (s S₀ e b : ℝ) (hS₀ : S₀ ≠ 0) (he : e ≠ 0) :
    (s/S₀-1)/e = b ↔ s = S₀*(1+e*b) := by
  constructor <;> intro h <;> field_simp at * <;> nlinarith

theorem stock_barrier_event_scaling {Ω : Type*} (S : HalfClosedTime → Ω → ℝ)
    (S₀ e b θ : ℝ) (hS₀ : S₀ ≠ 0) (he : e ≠ 0) (hθ : 0 < θ) (ω : Ω) :
    (∃ t : HalfClosedTime, t ≤ realTimeClamp 1 ∧
      (S (linearClock θ hθ (min (realTimeClamp 1) t)) ω/S₀-1)/e=b) ↔
    (∃ r : HalfClosedTime, r ≤ realTimeClamp θ ∧ S r ω=S₀*(1+e*b)) := by
  have he1 : linearClock θ hθ (realTimeClamp 1) = realTimeClamp θ := by
    simpa only [mul_one] using linear_clock_finite θ hθ 1 (by norm_num)
  constructor
  · rintro ⟨t,ht,hv⟩
    rw [min_eq_right ht,affine_barrier_equivalence _ S₀ e b hS₀ he] at hv
    refine ⟨linearClock θ hθ t,?_,hv⟩
    rw [← he1]
    exact (linearClock θ hθ).monotone ht
  · rintro ⟨r,hr,hv⟩
    have ht : (linearClock θ hθ).symm r ≤ realTimeClamp 1 := by
      rw [← he1] at hr
      exact (linearClock θ hθ).le_iff_le.mp (by simpa using hr)
    refine ⟨(linearClock θ hθ).symm r,ht,?_⟩
    rw [min_eq_right ht,(linearClock θ hθ).apply_symm_apply,
      affine_barrier_equivalence _ S₀ e b hS₀ he]
    exact hv

theorem stock_payoff_scaling {Ω : Type*} (S : HalfClosedTime → Ω → ℝ)
    (S₀ e b k θ : ℝ) (hS₀ : 0 < S₀) (he : 0 < e) (hθ : 0 < θ) (ω : Ω) :
    (if (∃ r : HalfClosedTime, r ≤ realTimeClamp θ ∧ S r ω=S₀*(1+e*b)) then 0
      else max (S₀*(1+e*k)-S (realTimeClamp θ) ω) 0) =
    S₀*e*(if (∃ t : HalfClosedTime, t ≤ realTimeClamp 1 ∧
      (S (linearClock θ hθ (min (realTimeClamp 1) t)) ω/S₀-1)/e=b) then 0
      else max (k-(S (linearClock θ hθ (min (realTimeClamp 1) (realTimeClamp 1))) ω/S₀-1)/e) 0) := by
  simp only [stock_barrier_event_scaling S S₀ e b θ hS₀.ne' he.ne' hθ ω,min_self,
    linear_clock_finite θ hθ 1 (by norm_num),mul_one]
  split_ifs
  · simp
  · rw [mul_max_of_nonneg _ _ (mul_pos hS₀ he).le,mul_zero]
    congr 1
    field_simp
    ring

theorem stock_price_scaling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : HalfClosedTime → Ω → ℝ)
    (S₀ e b k θ : ℝ) (hS₀ : 0 < S₀) (he : 0 < e) (hθ : 0 < θ)
    (M : NormalizedBarrierModel P b k)
    (hX : M.X = fun t ω => (S (linearClock θ hθ (min (realTimeClamp 1) t)) ω/S₀-1)/e) :
    (∫ ω, if (∃ r : HalfClosedTime, r ≤ realTimeClamp θ ∧ S r ω=S₀*(1+e*b)) then 0
      else max (S₀*(1+e*k)-S (realTimeClamp θ) ω) 0 ∂P) = S₀*e*M.price := by
  simp_rw [stock_payoff_scaling S S₀ e b k θ hS₀ he hθ]
  rw [integral_const_mul]
  simp only [NormalizedBarrierModel.price,hX]

end BarrierManuscript
#print axioms BarrierManuscript.affine_barrier_equivalence
#print axioms BarrierManuscript.stock_barrier_event_scaling
#print axioms BarrierManuscript.stock_payoff_scaling
#print axioms BarrierManuscript.stock_price_scaling
