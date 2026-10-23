import ManuscriptDeterministicItoLaw
import Chapter4DeterministicItoEnergy

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Exact mean-square error for deterministic Brownian integral
approximations, derived from their Ito characterizations. -/
theorem deterministic_ito_difference_energy {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (hi : ∀ r, 0 ≤ r → IntervalIntegrable (fun s => (g s-h s)^2) volume 0 r)
    (N M : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N) (hM : LocalMProcessWitness P B.F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N)
    (hMI : ItoCovarianceFormula P B.F (B.W 0) (fun z => h z.2) M)
    (R : ℝ) (hR : 0 ≤ R) :
    MemLp (fun ω => N (realTimeClamp R) ω-M (realTimeClamp R) ω) 2 P ∧
    (∫ ω,(N (realTimeClamp R) ω-M (realTimeClamp R) ω)^2 ∂P)=
      ∫ s in 0..R,(g s-h s)^2 := by
  let E := fun t ω => -M t ω+N t ω
  have hE : LocalMProcessWitness P B.F E := by
    simpa only [E,neg_one_mul] using (hM.smul P B.F (-1)).add P B.F B.mono B.le hN
  have hEI : ItoCovarianceFormula P B.F (B.W 0) (fun z => -h z.2+g z.2) E := by
    simpa only [neg_one_mul] using hMI.add_smul P B.F B.mono B.le
      (B.W 0) M N (fun z => h z.2) (fun z => g z.2) hNI (-1)
  have hl := measurable_deterministic_ito_law P B (fun s => -h s+g s)
    (hh.neg.add hg) (by simpa only [neg_add_eq_sub] using hi) E hE hEI R hR
  have hl' : HasLaw (fun ω => N (realTimeClamp R) ω-M (realTimeClamp R) ω)
      (gaussianReal 0 ⟨∫ s in 0..R,(g s-h s)^2,
        intervalIntegral.integral_nonneg_of_forall hR (fun _ => sq_nonneg _)⟩) P := by
    simpa only [E,neg_add_eq_sub] using hl
  refine ⟨hl'.memLp (memLp_id_gaussianReal 2),?_⟩
  have hm := gaussian_law_square_integral P _ 0 _ hl'
  change (∫ ω,(N (realTimeClamp R) ω-M (realTimeClamp R) ω)^2 ∂P)=0^2+(∫ s in 0..R,(g s-h s)^2) at hm
  simpa using hm

end BarrierManuscript
#print axioms BarrierManuscript.deterministic_ito_difference_energy
