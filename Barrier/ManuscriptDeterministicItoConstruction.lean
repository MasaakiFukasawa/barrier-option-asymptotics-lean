import ManuscriptDeterministicItoLaw
import Chapter2ItoCharacterizedConstruction

open MeasureTheory Set
open scoped ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Construct the deterministic locally square-integrable Ito integral
using the stochastic-integration construction from the Asakura project. -/
theorem deterministic_ito_exists {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : ∀ r, 0 ≤ r → IntervalIntegrable (fun s => g s^2) volume 0 r) :
    ∃ N : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (by simp : (0:EReal)<⊤)
  have hAm n ω : MonotoneOn (fun r => B.C 0 0 (realTimeClamp r) ω) (Icc 0 (c n)) := by
    intro r hr s hs hrs
    simpa only [B.diagonal_clock 0 ω r hr.1,B.diagonal_clock 0 ω s hs.1] using hrs
  have hAc n ω : ContinuousOn (fun r => B.C 0 0 (realTimeClamp r) ω) (Icc 0 (c n)) := by
    apply continuousOn_id.congr
    intro r hr
    exact B.diagonal_clock 0 ω r hr.1
  have hgp n : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => g z.2.val) :=
    hg.comp (continuous_adapted_real_progressive B.F B.mono (fun z : Ω × ℝ => z.2)
      (c n) (hc n).le (fun _ _ => measurable_const) (fun _ => continuous_id.continuousOn))
  have hmeasure n ω : (intervalStieltjes 0 (c n) (hc n).le
      (fun r => B.C 0 0 (realTimeClamp r) ω) (hAm n ω)
      (fun r hr => (hAc n ω r hr).mono inter_subset_left)).measure=volume.restrict (Ioc 0 (c n)) := by
    rw [← clock_stieltjes_measure 0 (c n) (hc n).le]
    congr 1
    apply StieltjesFunction.ext
    intro r
    exact B.diagonal_clock 0 ω _ (intervalClamp_mem _ _ _ _).1
  apply ito_integral_exists_with_covariance_characterization P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0)
    c hc hcm hcT hct hcut hcc hAm hAc (fun z => g z.2) hgp
  intro n
  apply ae_of_all
  intro ω
  rw [hmeasure]
  exact (hi (c n) (hc n).le).1

end BarrierManuscript
#print axioms BarrierManuscript.deterministic_ito_exists
