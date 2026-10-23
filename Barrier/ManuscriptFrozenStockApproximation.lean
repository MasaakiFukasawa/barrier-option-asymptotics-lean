import ManuscriptFrozenStockError
import ManuscriptSmallTimeEnergy
import ManuscriptVaryingLenglart

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The stock-return process differs from its frozen Brownian driver by
 o_P(sqrt(theta)), uniformly over the maturity interval. No integrable
maximal bound or joint weak limit is assumed. -/
theorem stock_frozen_brownian_approximation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ⨆ t : HalfClosedTime,
      |frozenStockError D (linearClock (θ n) (hp n) (min (realTimeClamp 1) t)) ω/Real.sqrt (θ n)|})
      atTop (𝓝 0) := by
  obtain ⟨hM,C,hC,hbr⟩ := frozen_stock_error_bracket P D
  let F := fun n t => D.B.F (linearClock (θ n) (hp n) t)
  let X := fun n t ω => frozenStockError D (linearClock (θ n) (hp n) t) ω/Real.sqrt (θ n)
  let A := fun n t ω => C (linearClock (θ n) (hp n) t) ω/θ n
  have hres n := long_time_martingale_rescaling P D.B.F (frozenStockError D) C hM hC (θ n) 1 (hp n) zero_lt_one
  simp only [mul_one] at hres
  have hg : ∀ᵐ ω ∂P, Continuous (fun r : ℝ => frozenStockIntegrand D (realTimeClamp r) ω) := by
    apply ae_of_all
    intro ω
    exact continuous_real_path (frozenStockIntegrand D)
      (fun ω t ht => continuousAt_const.add (((D.hSc ω t ht).div_const _).mul ((D.hVc ω t ht).sqrt))) ω
  have h0 : ∀ᵐ ω ∂P, frozenStockIntegrand D (realTimeClamp 0) ω=0 := frozen_stock_integrand_initial P D
  have hq := rescaled_zero_bracket P D.B.F D.B.mono D.B.le (frozenStockError D) C hM hC
    (fun ω r => frozenStockIntegrand D (realTimeClamp r) ω) hg h0 hbr θ hp hθ
  have htail (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => P {ω | δ ≤ A n (realTimeClamp 1) ω}) atTop (𝓝 0) := by
    have he n ω : A n (realTimeClamp 1) ω=C (realTimeClamp (θ n)) ω/θ n := by
      dsimp only [A]
      rw [linear_clock_finite _ _ 1 zero_le_one,mul_one]
    simp_rw [he]
    have hn := (tendstoInMeasure_iff_norm.mp hq) δ hδ
    simp only [sub_zero,Real.norm_eq_abs] at hn
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn (fun _ => bot_le)
      (fun n => measure_mono ?_)
    intro ω hω
    change δ ≤ C (realTimeClamp (θ n)) ω/θ n at hω
    exact hω.trans (le_abs_self _)
  exact varying_local_martingale_zero P F
    (fun n => D.B.mono.comp (linearClock (θ n) (hp n)).monotone)
    (fun _ _ => D.B.le _) (fun _ _ E hm hz => D.B.null _ E hm hz)
    X A (fun n => (hres n).1) (fun n => (hres n).2) htail ε hε

end BarrierManuscript
#print axioms BarrierManuscript.stock_frozen_brownian_approximation
