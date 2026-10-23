import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Equality of the approximating joint laws survives weak limits. -/
theorem identDistrib_of_weak_limits {Ω Γ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → E) (Y : ℕ → Γ → E) (L : Ω → E) (M : Γ → E)
    (hi : ∀ n, IdentDistrib (X n) (Y n) P Q)
    (hX : TendstoInDistribution X atTop L (fun _ => P) P)
    (hY : TendstoInDistribution Y atTop M (fun _ => Q) Q) :
    IdentDistrib L M P Q := by
  have hYL : TendstoInDistribution Y atTop L (fun _ => Q) P := by
    refine ⟨hY.forall_aemeasurable,hX.aemeasurable_limit,?_⟩
    apply hX.tendsto.congr
    intro n
    exact Subtype.ext (hi n).map_eq
  exact ⟨hX.aemeasurable_limit,hY.aemeasurable_limit,tendstoInDistribution_unique Y hYL hY⟩

end BarrierManuscript
#print axioms BarrierManuscript.identDistrib_of_weak_limits
