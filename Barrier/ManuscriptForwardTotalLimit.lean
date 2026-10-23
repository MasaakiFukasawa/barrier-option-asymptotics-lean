import ManuscriptForwardClockLimit
import ManuscriptOriginalPrice

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem forward_total_normalized_limit (v : ℝ → ℝ) (v₀ : ℝ)
    (hm : Measurable v) (hv : ContinuousAt v 0) (hv₀ : v 0=v₀) (hn : v₀ ≠ 0)
    (θ : ℕ → ℝ) (hθ : Tendsto θ atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (∫ s in (0:ℝ)..1, v (θ n*s)/v₀)) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n => ∫ s in (0:ℝ)..1, v (θ n*s)/v₀) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [normalized_forward_clock_bounds v v₀ hv hv₀ hn θ hθ,
      shrinking_curve_uniform (fun t => v t/v₀) (hv.div_const _) θ hθ (ε/2) (by positivity)] with n hb he
    have hi : IntervalIntegrable (fun s => v (θ n*s)/v₀) volume 0 1 := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
      apply (integrable_const (3/2:ℝ)).mono' ((hm.comp (measurable_const.mul measurable_id)).div_const _).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      dsimp only [Function.comp_def,Pi.mul_apply,id_eq]
      rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [(hb s hs).1])]
      exact (hb s hs).2
    have heq : (∫ s in (0:ℝ)..1, v (θ n*s)/v₀)-1 = ∫ s in (0:ℝ)..1, v (θ n*s)/v₀-1 := by
      rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
      simp
    rw [Real.dist_eq,heq]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall fun s hs => show ‖v (θ n*s)/v₀-1‖ ≤ ε/2 from by
        simpa only [Real.norm_eq_abs,hv₀,div_self hn] using (he s ⟨hs.1.le,hs.2⟩).le)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ε/2) volume 0 1)
    have hh : |∫ s in (0:ℝ)..1, v (θ n*s)/v₀-1| ≤ ε/2 := by
      simpa only [Real.norm_eq_abs,intervalIntegral.integral_const,sub_zero,one_smul] using hbound
    linarith
  simpa only [Real.sqrt_one] using hlim.sqrt

noncomputable def physicalBachelierPrice (forward : ℝ → ℝ) (S v b k θ : ℝ) : ℝ :=
  S*Real.sqrt (v*θ)*killedPut b k 0 (Real.sqrt (∫ u in (0:ℝ)..1, forward (θ*u)/v))

theorem forward_bs_expansion (forward : ℝ → ℝ) (S v b k : ℝ)
    (hS : 0 < S) (hv : 0 < v) (hm : Measurable forward)
    (hf : ContinuousAt forward 0) (hf0 : forward 0=v)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    Tendsto (fun n => (bsKilledPut (S*(1+Real.sqrt (v*θ n)*b)) (S*(1+Real.sqrt (v*θ n)*k)) S
      (Real.sqrt (∫ r in (0:ℝ)..θ n, forward r))-physicalBachelierPrice forward S v b k (θ n)-
      S*v*θ n*gamma b k)/θ n) atTop (𝓝 0) := by
  have h := bsKilledPut_physical_expansion S v b k hS hv θ
    (fun n => Real.sqrt (∫ u in (0:ℝ)..1, forward (θ n*u)/v)) hp hθ
    (forward_total_normalized_limit forward v hm hf hf0 hv.ne' θ hθ)
  simpa only [total_volatility_scaling forward v _ hv (hp _),physicalBachelierPrice] using h

end BarrierManuscript
#print axioms BarrierManuscript.forward_total_normalized_limit
#print axioms BarrierManuscript.forward_bs_expansion
