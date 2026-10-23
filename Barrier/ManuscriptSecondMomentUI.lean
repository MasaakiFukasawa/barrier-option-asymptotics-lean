import ManuscriptUniformIntegrability
import Chapter6DensityUniformIntegrability

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
open Asakura.Chapter6
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A uniform second moment proves the probabilistic UI needed in the
main theorem, including its L1 bound. -/
theorem second_moment_uniformIntegrable {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hm : ∀ i,Measurable (X i)) (hLp : ∀ i,MemLp (X i) 2 P)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ i,(∫ ω,(X i ω)^2 ∂P) ≤ C) :
    UniformIntegrable X 1 P := by
  have hi := uniform_integrable_of_nonnegative_tails P (fun i ω => |X i ω|)
    (fun i => (continuous_abs.measurable.comp (hm i))) (fun i => ((hLp i).integrable (by norm_num)).abs)
    (fun i => ae_of_all _ fun ω => abs_nonneg _) ?_
  · exact uniformIntegrable_of_abs_le P (fun i ω => |X i ω|) X hi
      (fun i => (hm i).aestronglyMeasurable) (fun i => ae_of_all _ fun ω => by simp)
  intro ε hε
  let R := C/ε+1
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R,hR,fun i => ?_⟩
  have hsq : Integrable (fun ω => (X i ω)^2) P := (memLp_two_iff_integrable_sq (hm i).aestronglyMeasurable).mp (hLp i)
  calc
    (∫ ω in {ω | R < |X i ω|},|X i ω| ∂P) ≤
        ∫ ω in {ω | R < |X i ω|},(X i ω)^2/R ∂P := by
      apply setIntegral_mono_on ((hLp i).integrable (by norm_num)).abs.integrableOn
        (hsq.div_const R).integrableOn (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hm i)))
      intro ω hω
      change R < |X i ω| at hω
      apply (le_div_iff₀ hR).mpr
      nlinarith [sq_abs (X i ω),abs_nonneg (X i ω)]
    _ ≤ ∫ ω,(X i ω)^2/R ∂P := setIntegral_le_integral
      (hsq.div_const R) (ae_of_all _ fun ω => div_nonneg (sq_nonneg _) hR.le)
    _ ≤ C/R := by rw [integral_div]; exact div_le_div_of_nonneg_right (hb i) hR.le
    _ ≤ ε := by
      apply (div_le_iff₀ hR).mpr
      dsimp only [R]
      have hh : ε*(C/ε)=C := mul_div_cancel₀ C hε.ne'
      nlinarith

end BarrierManuscript
#print axioms BarrierManuscript.second_moment_uniformIntegrable
