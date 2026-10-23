import ManuscriptSDEBracket

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem halfTimeClamp_finite (r : ℝ) : (realTimeClamp (T := (⊤:EReal)) r) < ⊤ := by
  change max (0:EReal) (min ⊤ (r:EReal)) < ⊤
  simp

theorem continuous_real_path {Ω : Type*} (X : HalfClosedTime → Ω → ℝ)
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t) (ω : Ω) :
    Continuous (fun r : ℝ => X (realTimeClamp r) ω) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact (hc ω _ (halfTimeClamp_finite r)).comp real_time_clamp_continuous.continuousAt

/-- Functional endpoint/maximum CLT obtained from the original stock SDE.
The covariance is constructed by Ito calculus and its convergence follows
from continuity at the deterministic initial stock and variance. -/
theorem stock_endpoint_maximum_clt {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (S V : HalfClosedTime → Ω → ℝ) (S₀ v₀ : ℝ) (hS₀n : S₀ ≠ 0) (hv₀ : 0 < v₀)
    (hSa : ∀ t, t < ⊤ → Measurable[B.F t] (S t))
    (hVa : ∀ t, t < ⊤ → Measurable[B.F t] (V t))
    (hSc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => S s ω) t)
    (hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t)
    (hS₀ : ∀ᵐ ω ∂P, S (realTimeClamp 0) ω = S₀)
    (hV₀ : ∀ᵐ ω ∂P, V (realTimeClamp 0) ω = v₀)
    (hV : ∀ ω r, 0 ≤ r → 0 ≤ V (realTimeClamp r) ω)
    (hM : LocalMProcessWitness P B.F (fun t ω => S t ω/S₀-1))
    (hSDE : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (S (realTimeClamp z.2) z.1/S₀)*Real.sqrt (V (realTimeClamp z.2) z.1))
      (fun t ω => S t ω/S₀-1))
    (θ : ℕ → ℝ) (hθ : ∀ n, 0 < θ n) (hθlim : Tendsto θ atTop (𝓝 0)) :
    let F := fun n t => B.F (linearClock (θ n) (hθ n) t)
    let X := fun n t ω => (S (linearClock (θ n) (hθ n) t) ω/S₀-1)/Real.sqrt (θ n*v₀)
    ∃ hX : ∀ n, LocalMProcessWitness P (F n) (X n),
      ∃ B0 : BrownianSystem (P.prod P) 1,
        TendstoInDistribution
          (fun n ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
            (pathRestriction 1 (localContinuousPath (X n) ((hX n).path P (F n)) ω))) atTop
          (fun ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
            (pathRestriction 1 (brownianContinuousPath B0 ω))) (fun _ => P) (P.prod P) := by
  dsimp only
  obtain ⟨C,hC,hCG⟩ := stock_return_bracket P B S V S₀ hSa hVa hSc hVc hV hM hSDE
  have hh := rescaled_martingale_bracket_limit P B.F B.mono B.le
    (fun t ω => S t ω/S₀-1) C hM hC (fun ω r => S (realTimeClamp r) ω)
    (fun ω r => V (realTimeClamp r) ω) S₀ v₀ hS₀n hv₀
    (ae_of_all _ (continuous_real_path S hSc)) (ae_of_all _ (continuous_real_path V hVc))
    hS₀ hV₀ (fun r hr => hCG.mono fun ω hω => hω r hr) θ hθ hθlim
  refine ⟨hh.1,?_⟩
  exact martingale_endpoint_maximum_limit P P
    (fun n t => B.F (linearClock (θ n) (hθ n) t))
    (fun n => B.mono.comp (linearClock (θ n) (hθ n)).monotone) (fun n t => B.le _)
    _ _ hh.1 hh.2.1 hh.2.2 B

end BarrierManuscript
#print axioms BarrierManuscript.halfTimeClamp_finite
#print axioms BarrierManuscript.continuous_real_path
#print axioms BarrierManuscript.stock_endpoint_maximum_clt
