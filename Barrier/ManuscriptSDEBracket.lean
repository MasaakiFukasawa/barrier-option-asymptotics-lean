import ManuscriptRescaling
import Chapter4BrownianItoCovariances

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- Quadratic variation of the normalized stock return, derived from the
actual Ito-integral characterization of dS/S = sqrt(V) dW. The covariance
formula for the stock itself is not assumed. -/
theorem stock_return_bracket {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (S V : HalfClosedTime → Ω → ℝ) (S₀ : ℝ)
    (hSa : ∀ t, t < ⊤ → Measurable[B.F t] (S t))
    (hVa : ∀ t, t < ⊤ → Measurable[B.F t] (V t))
    (hSc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => S s ω) t)
    (hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t)
    (hV : ∀ ω r, 0 ≤ r → 0 ≤ V (realTimeClamp r) ω)
    (hM : LocalMProcessWitness P B.F (fun t ω => S t ω/S₀-1))
    (hSDE : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (S (realTimeClamp z.2) z.1/S₀)*Real.sqrt (V (realTimeClamp z.2) z.1))
      (fun t ω => S t ω/S₀-1)) :
    ∃ C : HalfClosedTime → Ω → ℝ,
      LocalCovarianceWitness P B.F (fun t ω => S t ω/S₀-1) (fun t ω => S t ω/S₀-1) C ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω =
        ∫ a in 0..r, (S (realTimeClamp a) ω/S₀)^2*V (realTimeClamp a) ω := by
  let H := fun t ω => (S t ω/S₀)*Real.sqrt (V t ω)
  have hHa t ht : Measurable[B.F t] (H t) :=
    ((hSa t ht).div_const S₀).mul ((hVa t ht).sqrt)
  have hHc ω t ht : ContinuousAt (fun s => H s ω) t :=
    ((hSc ω t ht).div_const S₀).mul ((hVc ω t ht).sqrt)
  obtain ⟨D,C,_,hC,_,he⟩ := brownian_ito_cross_and_self_density P B.F B.mono B.le B.null
    (B.W 0) (fun t ω => S t ω/S₀-1) (B.C 0 0) H
    (B.martingale 0) hM (B.cov 0 0) (B.diagonal_clock 0) hHa hHc hSDE
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with ω hω
  intro r hr
  rw [hω r hr]
  apply intervalIntegral.integral_congr
  intro a ha
  have ha' : 0 ≤ a := (by simpa only [uIcc_of_le hr] using ha : a ∈ Icc 0 r).1
  simp only [H, mul_pow, Real.sq_sqrt (hV ω a ha')]

end BarrierManuscript
#print axioms BarrierManuscript.stock_return_bracket
