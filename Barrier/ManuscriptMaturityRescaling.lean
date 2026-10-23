import ManuscriptStoppedBracket

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Rescale and freeze the original stock martingale at normalized maturity.
This derives the global regularity needed by the pricing construction from
ordinary finite-time local-martingale regularity. -/
theorem maturity_rescaled_martingale {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (M C : HalfClosedTime → Ω → ℝ) (hM : LocalMProcessWitness P F M)
    (hC : LocalCovarianceWitness P F M M C)
    (G : Ω × ℝ → ℝ)
    (hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω = ∫ s in 0..r, G (ω,s))
    (θ v : ℝ) (hθ : 0 < θ) (hv : 0 < v) :
    let Fθ := fun t => F (linearClock θ hθ t)
    let X := fun t ω => M (linearClock θ hθ (min (realTimeClamp 1) t)) ω / Real.sqrt (θ*v)
    let D := fun t ω => C (linearClock θ hθ (min (realTimeClamp 1) t)) ω / (θ*v)
    LocalMProcessWitness P Fθ X ∧ LocalCovarianceWitness P Fθ X X D ∧
      (∀ t, Measurable[Fθ t] (X t)) ∧ (∀ ω, Continuous (fun t => X t ω)) ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → D (realTimeClamp r) ω =
        ∫ s in 0..r, if s ≤ 1 then G (ω,θ*s)/v else 0 := by
  dsimp only
  let Fθ := fun t => F (linearClock θ hθ t)
  let N := fun t ω => M (linearClock θ hθ t) ω / Real.sqrt (θ*v)
  let D := fun t ω => C (linearClock θ hθ t) ω / (θ*v)
  have hFθ : Monotone Fθ := hF.comp (linearClock θ hθ).monotone
  have hleθ : ∀ t, Fθ t ≤ m := fun t => hle _
  obtain ⟨hN,hD⟩ := long_time_martingale_rescaling P F M C hM hC θ v hθ hv
  have hstop : ∀ t, MeasurableSet[Fθ t] {ω : Ω | (realTimeClamp (T := (⊤:EReal)) 1) ≤ t} := by
    intro t
    by_cases h : (realTimeClamp (T := (⊤:EReal)) 1) ≤ t <;> simp [h]
  have hd : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → D (realTimeClamp r) ω =
      ∫ s in 0..r, G (ω,θ*s)/v := by
    filter_upwards [hCG] with ω hω
    intro r hr
    dsimp only [D]
    rw [linear_clock_finite θ hθ r hr,hω (θ*r) (mul_nonneg hθ.le hr)]
    rw [intervalIntegral.integral_div]
    rw [intervalIntegral.integral_comp_mul_left (fun s => G (ω,s)) hθ.ne']
    simp only [mul_zero,smul_eq_mul,intervalIntegral.integral_div]
    field_simp
  have hh := stopped_covariance_density P Fθ hFθ hleθ N D hN hD (fun z => G (z.1,θ*z.2)/v)
    hd (fun _ => 1) (fun _ => by norm_num) hstop
  have hreg := hN.stopped_regular P Fθ hFθ hleθ (fun _ => realTimeClamp 1) hstop
    (fun _ => changed_time_finite 1 (by norm_num))
  exact ⟨hh.1,hh.2.1,hreg.1,hreg.2,hh.2.2⟩

end BarrierManuscript
#print axioms BarrierManuscript.maturity_rescaled_martingale
