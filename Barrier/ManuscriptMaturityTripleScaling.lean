import ManuscriptClockComposition
import ManuscriptTimeScaling
import ManuscriptStockCoefficientLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem stock_prefix_time_scaling {Ω : Type*}
    (S : HalfClosedTime → Ω → ℝ) (S₀ θ v u : ℝ)
    (hθ : 0 < θ) (hv : 0 < v) (hu : u ∈ Ioc (0:ℝ) 1)
    (X Y : HalfClosedTime → Ω → ℝ)
    (hX : ∀ ω, Continuous (fun t => X t ω)) (hY : ∀ ω, Continuous (fun t => Y t ω))
    (heX : X=fun t ω => (S (linearClock θ hθ (min (realTimeClamp 1) t)) ω/S₀-1)/Real.sqrt (θ*v))
    (heY : Y=fun t ω => (S (linearClock (θ*u) (mul_pos hθ hu.1) (min (realTimeClamp 1) t)) ω/S₀-1)/Real.sqrt ((θ*u)*v))
    (ω : Ω) :
    X (realTimeClamp u) ω = Real.sqrt u*Y (realTimeClamp 1) ω ∧
    prefixMaximum X hX (realTimeClamp u) ω = Real.sqrt u*prefixMaximum Y hY (realTimeClamp 1) ω := by
  have ht := real_time_clamp_mono (T := (⊤:EReal)) hu.2
  have hscale t ω : X (min (realTimeClamp u) (linearClock u hu.1 t)) ω =
      Real.sqrt u*Y (min (realTimeClamp 1) t) ω := by
    rw [heX,heY]
    dsimp only
    rw [← min_assoc,min_eq_right ht,← min_assoc,min_self]
    have hc1 : linearClock u hu.1 (realTimeClamp 1)=realTimeClamp u := by
      simpa using linear_clock_finite u hu.1 1 zero_le_one
    rw [← hc1,← (linearClock u hu.1).monotone.map_min,linearClock_comp]
    exact normalized_stock_time_scaling _ θ v u hθ hv hu.1
  constructor
  · have h := hscale (realTimeClamp 1) ω
    simpa only [linear_clock_finite u hu.1 1 zero_le_one,mul_one,min_self] using h
  · exact prefixMaximum_rescaling X Y hX hY u (Real.sqrt u) hu.1 (Real.sqrt_pos.mpr hu.1) hscale ω

/-- Exact time-rescaling of all three coordinates in the manuscript's
joint convergence assumption, including the path maximum. -/
theorem stock_triple_time_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S V : HalfClosedTime → Ω → ℝ) (forward : ℝ → ℝ) (S₀ θ v u H b k : ℝ)
    (hθ : 0 < θ) (hv : 0 < v) (hu : u ∈ Ioc (0:ℝ) 1)
    (M N : NormalizedBarrierModel P b k)
    (hX : M.X=fun t ω => (S (linearClock θ hθ (min (realTimeClamp 1) t)) ω/S₀-1)/Real.sqrt (θ*v))
    (hX' : N.X=fun t ω => (S (linearClock (θ*u) (mul_pos hθ hu.1) (min (realTimeClamp 1) t)) ω/S₀-1)/Real.sqrt ((θ*u)*v))
    (hY : M.Y=fun z => (V (realTimeClamp (θ*z.2)) z.1/forward (θ*z.2)-1)/θ^H)
    (hY' : N.Y=fun z => (V (realTimeClamp ((θ*u)*z.2)) z.1/forward ((θ*u)*z.2)-1)/(θ*u)^H)
    (ω : Ω) :
    M.triple M.Y u ω = (Real.sqrt u*(N.triple N.Y 1 ω).1,
      u^H*(N.triple N.Y 1 ω).2.1,Real.sqrt u*(N.triple N.Y 1 ω).2.2) := by
  obtain ⟨hx,hm⟩ := stock_prefix_time_scaling S S₀ θ v u hθ hv hu M.X N.X M.hXc N.hXc hX hX' ω
  unfold NormalizedBarrierModel.triple NormalizedBarrierModel.state
  rw [hx,hm,hY,hY']
  dsimp only
  rw [mul_one,normalized_variance_time_scaling _ θ u H hθ hu.1]

end BarrierManuscript
#print axioms BarrierManuscript.stock_prefix_time_scaling
#print axioms BarrierManuscript.stock_triple_time_scaling
