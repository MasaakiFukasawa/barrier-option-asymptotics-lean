import ManuscriptClock
import ManuscriptVarianceClock

open MeasureTheory Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Continuity only at the origin gives uniform convergence over the
shrinking maturity interval. Continuity away from zero is not assumed. -/
theorem shrinking_curve_uniform (f : ℝ → ℝ) (hf : ContinuousAt f 0)
    (θ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) 1, |f (θ n*s)-f 0| < ε := by
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hf ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hθ) δ hδ] with n hn
  intro s hs
  apply (show dist (f (θ n*s)) (f 0) < ε → |f (θ n*s)-f 0| < ε from fun h => h)
  apply hd
  simp only [Real.dist_eq,sub_zero] at hn ⊢
  rw [abs_mul,abs_of_nonneg hs.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hs.2).trans_lt hn

theorem normalized_forward_clock_bounds (v : ℝ → ℝ) (v₀ : ℝ)
    (hv : ContinuousAt v 0) (hv₀ : v 0 = v₀) (hn : v₀ ≠ 0)
    (θ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) 1, 1/2 ≤ v (θ n*s)/v₀ ∧ v (θ n*s)/v₀ ≤ 3/2 := by
  have h := shrinking_curve_uniform (fun t => v t/v₀) (hv.div_const _) θ hθ (1/2) (by norm_num)
  filter_upwards [h] with n hn' s hs
  have hh := hn' s hs
  simp only [hv₀,div_self hn] at hh
  exact ⟨by linarith [(abs_lt.mp hh).1],by linarith [(abs_lt.mp hh).2]⟩

theorem normalized_forward_remaining_limit (v : ℝ → ℝ) (v₀ : ℝ)
    (hv : ContinuousAt v 0) (hv₀ : v 0 = v₀) (hn : v₀ ≠ 0)
    (θ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0)) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1)
    (hi : ∀ n, IntervalIntegrable (fun s => v (θ n*s)/v₀) volume u 1) :
    Tendsto (fun n => ∫ s in u..1, v (θ n*s)/v₀) atTop (𝓝 (1-u)) ∧
    Tendsto (fun n => remainingVol (fun s => v (θ n*s)/v₀) u) atTop (𝓝 (Real.sqrt (1-u))) := by
  have hlim : Tendsto (fun n => ∫ s in u..1, v (θ n*s)/v₀) atTop (𝓝 (1-u)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [shrinking_curve_uniform (fun t => v t/v₀) (hv.div_const _) θ hθ (ε/2) (by positivity)] with n hn'
    have he : (∫ s in u..1, v (θ n*s)/v₀)-(1-u) = ∫ s in u..1, v (θ n*s)/v₀-1 := by
      rw [intervalIntegral.integral_sub (hi n) intervalIntegrable_const]
      simp
    have hb : |∫ s in u..1, v (θ n*s)/v₀-1| ≤ (1-u)*(ε/2) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le hu.2
        (Filter.Eventually.of_forall fun s hs => show ‖v (θ n*s)/v₀-1‖ ≤ ε/2 from by
          have hh := hn' s ⟨hu.1.trans hs.1.le,hs.2⟩
          simpa only [hv₀,div_self hn,Real.norm_eq_abs] using hh.le)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ε/2) volume u 1)
      simpa only [Real.norm_eq_abs,intervalIntegral.integral_const,smul_eq_mul] using h
    rw [Real.dist_eq,he]
    exact hb.trans_lt (by nlinarith [mul_nonneg hu.1 hε.le])
  exact ⟨hlim,hlim.sqrt⟩

end BarrierManuscript
#print axioms BarrierManuscript.shrinking_curve_uniform
#print axioms BarrierManuscript.normalized_forward_clock_bounds
#print axioms BarrierManuscript.normalized_forward_remaining_limit
