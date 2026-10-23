import ManuscriptVaryingKernel
import ManuscriptSmoothPrice

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Concrete Gaussian kernel convergence with volatility-coordinate UI.
The spatial weights cover all terms used in the main expansion. -/
theorem gaussian_weighted_weak_limit {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : ℕ → Ω → ℝ × ℝ × ℝ) (z : Γ → ℝ × ℝ × ℝ)
    (h : TendstoInDistribution Z atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun n ω => (Z n ω).2.1) 1 P)
    (v w : ℕ → ℝ) (v₀ w₀ : ℝ) (hvlim : Tendsto v atTop (𝓝 v₀))
    (hwlim : Tendsto w atTop (𝓝 w₀)) (hw₀ : 0 < w₀)
    (c V W : ℝ) (hc : 0 < c) (hV : ∀ n, |v n| ≤ V)
    (hcw : ∀ n, c ≤ w n) (hwW : ∀ n, w n ≤ W)
    (b k : ℝ) (j : ℕ) (hj : j ≤ 2)
    (hnoatom : ∀ᵐ ω ∂Q, (z ω).2.2 ≠ b) :
    Integrable (fun ω => barrierWeight (fun x => x^j*thetaKernel b k v₀ w₀ x) b (z ω)) Q ∧
    Tendsto (fun n => ∫ ω, barrierWeight (fun x => x^j*thetaKernel b k (v n) (w n) x) b (Z n ω) ∂P)
      atTop (𝓝 (∫ ω, barrierWeight (fun x => x^j*thetaKernel b k v₀ w₀ x) b (z ω) ∂Q)) := by
  let A := normalizer*(1+2*k^2+4*W^2)+normalizer*(1+2*(2*b-k)^2+4*W^2)
  have hn := normalizer_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0)
  let C := V/(2*c)*A+1
  have hC : 0 < C := by dsimp [C]; positivity
  let f := fun z : (ℝ × ℝ) × ℝ => z.2^j*thetaKernel b k z.1.1 z.1.2 z.2
  have hfm : Measurable f := by
    dsimp only [f,thetaKernel]
    exact (measurable_snd.pow_const j).mul (((measurable_fst.fst).div
      (measurable_const.mul measurable_fst.snd)).mul
        ((phi_contDiff.continuous.measurable.comp (by fun_prop)).sub
          (phi_contDiff.continuous.measurable.comp (by fun_prop))))
  have hfc x : ContinuousAt f ((v₀,w₀),x) := by
    dsimp only [f,thetaKernel]
    have hw' : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => z.1.2) ((v₀,w₀),x) := by fun_prop
    have hx' : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => z.2) ((v₀,w₀),x) := by fun_prop
    have h1 : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => (k+z.2-2*b)/z.1.2) ((v₀,w₀),x) :=
      ((continuousAt_const.add hx').sub continuousAt_const).div hw' hw₀.ne'
    have h2 : ContinuousAt (fun z : (ℝ × ℝ) × ℝ => (k-z.2)/z.1.2) ((v₀,w₀),x) :=
      (continuousAt_const.sub hx').div hw' hw₀.ne'
    exact (hx'.pow j).mul (((continuousAt_fst.fst).div (continuousAt_const.mul hw')
      (mul_ne_zero (by norm_num) hw₀.ne')).mul
        ((phi_contDiff.continuous.continuousAt.comp h1).sub (phi_contDiff.continuous.continuousAt.comp h2)))
  have hfb n x : |f ((v n,w n),x)| ≤ C := by
    have hwpos : 0 < w n := hc.trans_le (hcw n)
    have hbound := thetaKernel_bound b k (v n) (w n) x W hwpos (hwW n) j hj
    have hdiv : |v n|/(2*w n) ≤ V/(2*c) :=
      div_le_div₀ hV0 (hV n) (by positivity) (by linarith [hcw n])
    have hm := mul_le_mul_of_nonneg_right hdiv hA
    dsimp only [f]
    rw [abs_mul,abs_pow]
    exact hbound.trans (hm.trans (by dsimp [C]; linarith))
  exact weak_varying_barrier_expectation P Q Z z h hui (fun n => (v n,w n)) (v₀,w₀)
    (hvlim.prodMk_nhds hwlim) f hfm hfc C hC hfb b hnoatom

end BarrierManuscript
#print axioms BarrierManuscript.gaussian_weighted_weak_limit
