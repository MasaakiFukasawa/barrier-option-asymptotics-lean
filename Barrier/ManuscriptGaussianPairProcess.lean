import ManuscriptBrownianFuture
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Independent Gaussian processes are jointly Gaussian as a pair-valued
process. Independence is of entire trajectories, not merely equal-time values. -/
theorem independent_gaussian_pair_process {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : T → Ω → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P)
    (hind : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P) :
    IsGaussianProcess (fun t ω => (X t ω,Y t ω)) P := by
  classical
  constructor
  intro I
  have hm : Measurable (fun f : T → ℝ => fun i : I => f i) := measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)
  have hi := hind.comp hm hm
  have hg := IndepFun.hasGaussianLaw (hX.hasGaussianLaw I) (hY.hasGaussianLaw I) hi
  let L : ((I → ℝ) × (I → ℝ)) →L[ℝ] (I → ℝ × ℝ) :=
    { toFun p i := (p.1 i,p.2 i)
      map_add' p q := by ext i <;> rfl
      map_smul' c p := by ext i <;> rfl }
  exact hg.map L

noncomputable def brownianLinearForm (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Every linear combination of two independent Gaussian paths is a
Gaussian process; this supplies the joint Gaussian regression argument. -/
theorem independent_gaussian_linear_process {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : T → Ω → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P)
    (hind : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P) (a b : ℝ) :
    IsGaussianProcess (fun t ω => a*X t ω+b*Y t ω) P := by
  exact (independent_gaussian_pair_process P X Y hX hY hind).comp_left (fun _ => brownianLinearForm a b)

end BarrierManuscript
#print axioms BarrierManuscript.independent_gaussian_pair_process
#print axioms BarrierManuscript.independent_gaussian_linear_process
