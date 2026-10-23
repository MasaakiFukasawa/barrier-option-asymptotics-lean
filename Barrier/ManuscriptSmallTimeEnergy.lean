import ManuscriptRescaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem small_time_energy_zero (g : ℝ → ℝ) (hg : Continuous g) (h0 : g 0=0)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    Tendsto (fun n => (∫ s in (0:ℝ)..θ n, (g s)^2)/θ n) atTop (𝓝 0) := by
  have hc : Continuous (fun p : ℝ × ℝ => (g (p.1*p.2))^2) := by fun_prop
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun a s : ℝ => (g (a*s))^2) hc 0 1
  have he (n : ℕ) : (∫ s in (0:ℝ)..θ n, (g s)^2)/θ n = ∫ s in (0:ℝ)..1, (g (θ n*s))^2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun s => (g s)^2) (hp n).ne']
    simp only [mul_zero,mul_one,smul_eq_mul]
    ring
  simp_rw [he]
  simpa only [Function.comp_def,zero_mul,h0,zero_pow (by norm_num : (2:ℕ)≠0),intervalIntegral.integral_zero] using
    hi.continuousAt.tendsto.comp hθ

/-- A continuous integrand vanishing initially gives a rescaled quadratic
variation tending to zero in probability, without any moment assumption. -/
theorem rescaled_zero_bracket {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t≤m)
    (M C : HalfClosedTime → Ω → ℝ) (hM : LocalMProcessWitness P F M)
    (hC : LocalCovarianceWitness P F M M C) (g : Ω → ℝ → ℝ)
    (hg : ∀ᵐ ω ∂P, Continuous (g ω)) (h0 : ∀ᵐ ω ∂P, g ω 0=0)
    (hbr : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω=∫ s in (0:ℝ)..r, (g ω s)^2)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => C (realTimeClamp (θ n)) ω/θ n) atTop (fun _ => 0) := by
  have hc := covariance_adapted_variation P F hF hle hM hM hC
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    have ht : realTimeClamp (T := (⊤:EReal)) (θ n) < ⊤ := by
      change max (0:EReal) (min ⊤ (θ n:EReal)) < ⊤
      simp
    exact (((hc.adapted _ ht).mono (hle _) le_rfl).div_const (θ n)).aestronglyMeasurable
  · filter_upwards [hg,h0,hbr] with ω hgw h0w hbrw
    simpa only [hbrw _ (hp _).le] using small_time_energy_zero (g ω) hgw h0w θ hp hθ

end BarrierManuscript
#print axioms BarrierManuscript.small_time_energy_zero
#print axioms BarrierManuscript.rescaled_zero_bracket
