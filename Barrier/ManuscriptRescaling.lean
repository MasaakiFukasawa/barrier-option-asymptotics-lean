import ManuscriptBracketLimit
import ManuscriptPathLimit
import Chapter8LongTimeRescaling
import Chapter3ContinuousIntegralConstruction

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- Exact bracket change of variables, for every positive maturity. -/
theorem bracket_change_of_variables (S V : ℝ → ℝ) (S₀ v₀ θ u : ℝ) (hθ : θ ≠ 0) :
    (∫ r in 0..θ*u, (S r/S₀)^2*V r)/(θ*v₀) =
      normalizedBracket S V S₀ v₀ θ u := by
  unfold normalizedBracket
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_mul_left (fun r => (S r/S₀)^2*V r) hθ]
  simp only [mul_zero, smul_eq_mul]
  ring

/-- Connect the actual covariance witness to the continuous-path bracket
limit after deterministic maturity rescaling. This supplies local
martingality, covariance, and convergence in probability for the varying
filtration CLT; these are conclusions rather than assumptions on the
rescaled processes. -/
theorem rescaled_martingale_bracket_limit
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (M C : HalfClosedTime → Ω → ℝ)
    (hM : LocalMProcessWitness P F M) (hC : LocalCovarianceWitness P F M M C)
    (S V : Ω → ℝ → ℝ) (S₀ v₀ : ℝ) (hS₀n : S₀ ≠ 0) (hv₀ : 0 < v₀)
    (hS : ∀ᵐ ω ∂P, Continuous (S ω)) (hV : ∀ᵐ ω ∂P, Continuous (V ω))
    (hS₀ : ∀ᵐ ω ∂P, S ω 0 = S₀) (hV₀ : ∀ᵐ ω ∂P, V ω 0 = v₀)
    (hbracket : ∀ t : ℝ, 0 ≤ t → C (realTimeClamp t) =ᵐ[P]
      fun ω => ∫ r in 0..t, (S ω r/S₀)^2*V ω r)
    (θ : ℕ → ℝ) (hθ : ∀ n, 0 < θ n) (hθlim : Tendsto θ atTop (𝓝 0)) :
    let G := fun n t => F (linearClock (θ n) (hθ n) t)
    let N := fun n t ω => M (linearClock (θ n) (hθ n) t) ω / Real.sqrt (θ n*v₀)
    let D := fun n t ω => C (linearClock (θ n) (hθ n) t) ω / (θ n*v₀)
    (∀ n, LocalMProcessWitness P (G n) (N n)) ∧
    (∀ n, LocalCovarianceWitness P (G n) (N n) (N n) (D n)) ∧
    (∀ u : ℝ≥0, TendstoInMeasure P (fun n => D n (realTimeClamp u)) atTop (fun _ => (u:ℝ))) := by
  dsimp only
  refine ⟨fun n => (long_time_martingale_rescaling P F M C hM hC (θ n) v₀ (hθ n) hv₀).1,
    fun n => (long_time_martingale_rescaling P F M C hM hC (θ n) v₀ (hθ n) hv₀).2, ?_⟩
  intro u
  have he n : (fun ω => C (linearClock (θ n) (hθ n) (realTimeClamp u)) ω/(θ n*v₀)) =ᵐ[P]
      fun ω => normalizedBracket (S ω) (V ω) S₀ v₀ (θ n) u := by
    rw [linear_clock_finite _ _ _ u.coe_nonneg]
    filter_upwards [hbracket (θ n*u) (mul_nonneg (hθ n).le u.coe_nonneg)] with ω hω
    rw [hω, bracket_change_of_variables _ _ _ _ _ _ (hθ n).ne']
  have hc := covariance_adapted_variation P F hF hle hM hM hC
  have hm n : AEStronglyMeasurable
      (fun ω => normalizedBracket (S ω) (V ω) S₀ v₀ (θ n) u) P := by
    have ht : linearClock (θ n) (hθ n) (realTimeClamp u) < ⊤ := by
      rw [linear_clock_finite _ _ _ u.coe_nonneg]
      change (realTimeClamp (θ n*u) : EReal) < ⊤
      rw [real_time_clamp_eq _ (mul_nonneg (hθ n).le u.coe_nonneg) le_top]
      exact EReal.coe_lt_top _
    exact (((hc.adapted _ ht).mono (hle _) le_rfl).div_const (θ n*v₀)).aestronglyMeasurable.congr (he n)
  exact TendstoInMeasure.congr_left (fun n => (he n).symm)
    (normalizedBracket_inMeasure P S V S₀ v₀ u θ hθlim hS hV hS₀ hV₀ hS₀n hv₀.ne' hm)

end BarrierManuscript
#print axioms BarrierManuscript.bracket_change_of_variables
#print axioms BarrierManuscript.rescaled_martingale_bracket_limit
