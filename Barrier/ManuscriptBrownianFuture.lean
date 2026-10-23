import FullAuditStrongMarkovWritten
import ManuscriptBrownianScaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Deterministic-time Markov property for the entire future path, obtained
from the existing strong Markov theorem. This is the stochastic independence
needed to multiply the two killed densities in the appendix. -/
theorem brownian_future_independent_past {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) :
    IsPreBrownianReal (fun s ω => W (t+s) ω-W t ω) P ∧
    Indep (MeasurableSpace.comap (fun ω s => W (t+s) ω-W t ω) inferInstance)
      (pastSigma W t) P := by
  have hτ : ∀ s, MeasurableSet[Asakura.nullAugmentation P (pastSigma W s)] {ω : Ω | t ≤ s} := by
    intro s
    by_cases hs : t ≤ s <;> simp only [hs,Set.ofPred_true,Set.ofPred_false] <;> measurability
  have h := brownian_strong_markov_written P W hW hm hc (fun _ => t) hτ
  refine ⟨h.1,?_⟩
  apply indep_of_indep_of_le_right h.2.2
  intro A hA
  constructor
  · exact (past_sigma_le W hm t) A hA
  · intro s
    by_cases hs : t ≤ s
    · simp only [hs,Set.ofPred_true,Set.inter_univ]
      exact ⟨past_sigma_le W hm t A hA,A,(past_sigma_mono W hs) A hA,EventuallyEq.rfl⟩
    · simp only [hs,Set.ofPred_false,Set.inter_empty,MeasurableSet.empty]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_future_independent_past
