import ManuscriptDeterministicBracketLaw
import Chapter4BrownianSystem

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Deterministic measurable, locally square-integrable Brownian integrands
have their exact Gaussian law. The integral is specified by its actual
Ito covariance characterization, not by a Gaussian-law assumption. -/
theorem measurable_deterministic_ito_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : ∀ r, 0 ≤ r → IntervalIntegrable (fun s => g s^2) volume 0 r)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N)
    (R : ℝ) (hR : 0 ≤ R) :
    HasLaw (N (realTimeClamp R))
      (gaussianReal 0 ⟨∫ s in 0..R,g s^2,
        intervalIntegral.integral_nonneg_of_forall hR (fun _ => sq_nonneg _)⟩) P := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (by simp : (0:EReal)<⊤)
  have hgp n : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => g z.2.val) := by
    exact hg.comp (continuous_adapted_real_progressive B.F B.mono (fun z : Ω × ℝ => z.2)
      (c n) (hc n).le (fun _ _ => measurable_const) (fun _ => continuous_id.continuousOn))
  obtain ⟨C,hC,he⟩ := clock_ito_integral_bracket P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) N (B.martingale 0) (B.cov 0 0) hN
    c hc hcm hcT hct hcut hcc
    (fun n ω r hr => B.diagonal_clock 0 ω r hr.1)
    (fun z => g z.2) hgp (fun n => ae_of_all _ fun _ => hi (c n) (hc n).le) hNI
  exact integrable_deterministic_bracket_law P B.F B.mono B.le B.null N C hN hC
    (fun s => g s^2) hi (fun _ _ => sq_nonneg _) (fun r hr => he r hr (EReal.coe_lt_top r)) R hR

end BarrierManuscript
#print axioms BarrierManuscript.measurable_deterministic_ito_law
