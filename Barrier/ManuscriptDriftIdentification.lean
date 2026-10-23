import ManuscriptStoppedExpectation
import ManuscriptDriftBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

noncomputable def stoppedThetaKernel {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (a : ℝ → ℝ) (b k : ℝ) (z : Ω × ℝ) : ℝ :=
  if z.2 ≤ cappedBarrier X b z.1 then
    thetaKernel b k (a z.2) (Real.sqrt (varianceClock a (realTimeClamp z.2))) (X (realTimeClamp z.2) z.1)
  else 0

theorem thetaKernel_varianceGamma (b k a r x : ℝ) :
    thetaKernel b k a (Real.sqrt r) x = -a*varianceGamma b k x r := by
  unfold thetaKernel varianceGamma
  rw [show k+x-2*b = k-2*b+x by ring]
  ring

/-- Substitute the actual stock bracket density in the stopped drift. -/
theorem barrier_drift_polynomial {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (G Y : Ω × ℝ → ℝ) (a : ℝ → ℝ) (b k e h : ℝ) (z : Ω × ℝ)
    (hG : G z = a z.2*(1+e*X (realTimeClamp z.2) z.1)^2*(1+h*Y z)) :
    barrierDrift X G a b k z = -stoppedThetaKernel X a b k z *
      ((1+e*X (realTimeClamp z.2) z.1)^2*(1+h*Y z)-1) := by
  unfold barrierDrift stoppedThetaKernel
  split_ifs
  · rw [hG,thetaKernel_varianceGamma]
    ring
  · ring

/-- Algebraic identification from the definitions of normalized return and
variance fluctuation. No bracket identity is assumed in this calculation. -/
theorem normalized_stock_density_algebra (S S₀ V v₀ a e h : ℝ)
    (he : e ≠ 0) (hh : h ≠ 0) (hv : v₀ ≠ 0) (ha : a ≠ 0) :
    (S/S₀)^2*V/v₀ = a*(1+e*((S/S₀-1)/e))^2*(1+h*((V/(v₀*a)-1)/h)) := by
  field_simp
  ring

/-- Integrability of the stopped pricing drift follows from the full
Gaussian polynomial estimate after substituting the stock density. -/
theorem barrier_drift_integrable_of_polynomial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : HalfClosedTime → Ω → ℝ) (G Y : Ω × ℝ → ℝ) (a : ℝ → ℝ)
    (b k e h : ℝ)
    (hG : ∀ᵐ z ∂P.prod (volume.restrict (Ioo (0:ℝ) 1)),
      G z = a z.2*(1+e*X (realTimeClamp z.2) z.1)^2*(1+h*Y z))
    (hi : Integrable (fun z => stoppedThetaKernel X a b k z *
      ((1+e*X (realTimeClamp z.2) z.1)^2*(1+h*Y z)-1))
        (P.prod (volume.restrict (Ioo 0 1)))) :
    Integrable (barrierDrift X G a b k) (P.prod (volume.restrict (Ioo 0 1))) := by
  apply hi.neg.congr
  filter_upwards [hG] with z hz
  rw [barrier_drift_polynomial X G Y a b k e h z hz]
  dsimp only [Pi.neg_apply]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.thetaKernel_varianceGamma
#print axioms BarrierManuscript.barrier_drift_polynomial
#print axioms BarrierManuscript.normalized_stock_density_algebra
#print axioms BarrierManuscript.barrier_drift_integrable_of_polynomial
