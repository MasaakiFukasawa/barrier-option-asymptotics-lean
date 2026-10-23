import ManuscriptVolatilityStability

open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Converts the stated ATM implied-variance asymptotic into the total
volatility asymptotic used by the price-stability theorem. The external
implied-variance theorem is an explicit hypothesis. -/
theorem atm_total_volatility_replacement (σ a θ : ℕ → ℝ) (v : ℝ)
    (hv : 0 < v) (hσ : ∀ n, 0 ≤ σ n) (ha : ∀ n, 0 ≤ a n)
    (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (halim : Tendsto a atTop (𝓝 v))
    (herr : Tendsto (fun n => ((σ n)^2-a n)/Real.sqrt (θ n)) atTop (𝓝 0)) :
    Tendsto (fun n => (σ n*Real.sqrt (θ n)-Real.sqrt (θ n*a n))/θ n) atTop (𝓝 0) := by
  have hsθ : Tendsto (fun n => Real.sqrt (θ n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hθ.sqrt
  have hdiff : Tendsto (fun n => (σ n)^2-a n) atTop (𝓝 0) := by
    simpa only [mul_zero,div_mul_cancel₀ _ (Real.sqrt_pos.mpr (hp _)).ne'] using herr.mul hsθ
  have hsquare : Tendsto (fun n => (σ n)^2) atTop (𝓝 v) := by
    simpa only [sub_add_cancel,zero_add] using hdiff.add halim
  have hsig : Tendsto σ atTop (𝓝 (Real.sqrt v)) := by
    simpa only [Real.sqrt_sq (hσ _)] using hsquare.sqrt
  have hden := hsig.add halim.sqrt
  have hl := herr.div hden (by positivity : Real.sqrt v+Real.sqrt v ≠ 0)
  simp only [zero_div] at hl
  apply hl.congr'
  filter_upwards [halim.eventually (eventually_gt_nhds hv)] with n hn
  have ht := Real.sq_sqrt (hp n).le
  have ht0 := (Real.sqrt_pos.mpr (hp n)).ne'
  have ha2 := Real.sq_sqrt (ha n)
  have hd : σ n+Real.sqrt (a n) ≠ 0 := (add_pos_of_nonneg_of_pos (hσ n) (Real.sqrt_pos.mpr hn)).ne'
  dsimp only [Pi.div_apply]
  rw [Real.sqrt_mul (hp n).le]
  field_simp [ht0,hd,(hp n).ne']
  linear_combination -((σ n)^2-a n)*ht+(Real.sqrt (θ n))^2*ha2

end BarrierManuscript
#print axioms BarrierManuscript.atm_total_volatility_replacement
