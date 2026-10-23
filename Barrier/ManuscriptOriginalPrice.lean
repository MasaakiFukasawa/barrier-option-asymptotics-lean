import ManuscriptStockData
import ManuscriptPayoffScaling
import ManuscriptBlackScholesBaseline
import ManuscriptBlackScholesPhysical

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

noncomputable def originalPrice {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) (b k θ : ℝ) : ℝ :=
  ∫ ω, if (∃ r : HalfClosedTime, r ≤ realTimeClamp θ ∧ D.S r ω=D.S₀*(1+Real.sqrt (D.v₀*θ)*b))
    then 0 else max (D.S₀*(1+Real.sqrt (D.v₀*θ)*k)-D.S (realTimeClamp θ) ω) 0 ∂P

theorem total_volatility_scaling (forward : ℝ → ℝ) (v θ : ℝ) (hv : 0 < v) (hθ : 0 < θ) :
    Real.sqrt (v*θ)*Real.sqrt (∫ u in (0:ℝ)..1, forward (θ*u)/v) = Real.sqrt (∫ r in (0:ℝ)..θ, forward r) := by
  rw [← Real.sqrt_mul (mul_pos hv hθ).le,normalized_variance_clock forward v θ hθ.ne',
    mul_div_cancel₀ _ (mul_pos hv hθ).ne']

theorem original_price_expansion_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (forward : ℝ → ℝ) (b k H a : ℝ) (hb : 0 < b)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (M : ℕ → NormalizedBarrierModel P b k)
    (hX : ∀ n, (M n).X=fun r ω => (D.S (linearClock (θ n) (hp n) (min (realTimeClamp 1) r)) ω/D.S₀-1)/Real.sqrt (θ n*D.v₀))
    (h : Tendsto (fun n => ((M n).price-
      bsKilledPut (1+Real.sqrt (D.v₀*θ n)*b) (1+Real.sqrt (D.v₀*θ n)*k) 1
        (Real.sqrt (D.v₀*θ n)*Real.sqrt (∫ s in (0:ℝ)..1, forward (θ n*s)/D.v₀))/Real.sqrt (D.v₀*θ n)-
      (θ n)^H*a)/(θ n)^H) atTop (𝓝 0)) :
    Tendsto (fun n => (originalPrice D b k (θ n)-
      bsKilledPut (D.S₀*(1+Real.sqrt (D.v₀*θ n)*b)) (D.S₀*(1+Real.sqrt (D.v₀*θ n)*k)) D.S₀
        (Real.sqrt (∫ r in (0:ℝ)..θ n, forward r))-
      a*D.S₀*Real.sqrt D.v₀*(θ n)^(H+1/2))/(θ n)^(H+1/2)) atTop (𝓝 0) := by
  let e := fun n => Real.sqrt (D.v₀*θ n)
  let w := fun n => Real.sqrt (∫ s in (0:ℝ)..1, forward (θ n*s)/D.v₀)
  have hep n : 0 < e n := Real.sqrt_pos.mpr (mul_pos D.hv₀ (hp n))
  have helim : Tendsto e atTop (𝓝 0) := by simpa only [e,mul_zero,Real.sqrt_zero] using (hθ.const_mul D.v₀).sqrt
  have hK : ∀ᶠ n in atTop, 0 < 1+e n*k :=
    (show Tendsto (fun n => 1+e n*k) atTop (𝓝 1) by simpa using (helim.mul_const k).const_add 1).eventually (eventually_gt_nhds zero_lt_one)
  have hphys := physical_expansion_scaling (fun n => (M n).price)
    (fun n => bsKilledPut (1+e n*b) (1+e n*k) 1 (e n*w n)/e n) θ D.S₀ D.v₀ H a D.hv₀ hp h
  apply hphys.congr'
  filter_upwards [hK] with n hkn
  have hprice := stock_price_scaling P D.S D.S₀ (e n) b k (θ n) D.hS₀ (hep n) (hp n) (M n)
    (by simpa only [e,mul_comm] using hX n)
  change originalPrice D b k (θ n)=D.S₀*e n*(M n).price at hprice
  have hbs := bsKilledPut_homogeneous D.S₀ (1+e n*b) (1+e n*k) 1 (e n*w n)
    D.hS₀ (by have hh := mul_pos (hep n) hb; linarith) hkn zero_lt_one
  simp only [mul_one] at hbs
  rw [total_volatility_scaling forward D.v₀ (θ n) D.hv₀ (hp n)] at hbs
  rw [hprice,hbs]
  have heq : e n*w n=Real.sqrt (∫ r in (0:ℝ)..θ n, forward r) :=
    total_volatility_scaling forward D.v₀ (θ n) D.hv₀ (hp n)
  change (D.S₀*e n*(M n).price-D.S₀*e n*(bsKilledPut (1+e n*b) (1+e n*k) 1 (e n*w n)/e n)-a*D.S₀*Real.sqrt D.v₀*θ n^(H+1/2))/θ n^(H+1/2) = _
  rw [heq]
  field_simp [(hep n).ne']
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.total_volatility_scaling
#print axioms BarrierManuscript.original_price_expansion_scaling
