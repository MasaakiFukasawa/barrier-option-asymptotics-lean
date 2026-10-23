import ManuscriptForwardDrift
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The zero-mean condition used in the forward-drift calculation follows
from a true martingale starting at zero. -/
theorem true_martingale_mean_zero {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ m)
    (M : ℝ → Ω → ℝ) (hM : Martingale M F P) (h0 : M 0 =ᵐ[P] 0)
    (t : ℝ) (ht : 0 ≤ t) : (∫ ω, M t ω ∂P)=0 := by
  calc
    _ = ∫ ω, P[M t | F 0] ω ∂P := (integral_condExp (F.le 0)).symm
    _ = ∫ ω, M 0 ω ∂P := integral_congr_ae (hM.condExp_ae_eq ht)
    _ = 0 := by rw [integral_congr_ae h0]; simp

/-- The manuscript's semimartingale forward-variance estimate with the
martingale property as input, rather than a separately assumed zero mean. -/
theorem true_semimartingale_forward_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ m)
    (V : Ω → ℝ) (M : ℝ → Ω → ℝ) (a : Ω × ℝ → ℝ)
    (v₀ C t : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hm : AEStronglyMeasurable a (P.prod (volume.restrict (Ioc 0 t))))
    (hi : ∀ s ∈ Ioc (0:ℝ) t, Integrable (fun ω => a (ω,s)) P)
    (hb : ∀ s ∈ Ioc (0:ℝ) t, (∫ ω, |a (ω,s)| ∂P) ≤ C)
    (hM : Martingale M F P) (h0 : M 0 =ᵐ[P] 0)
    (hV : ∀ᵐ ω ∂P, V ω=v₀+M t ω+∫ s in (0:ℝ)..t, a (ω,s)) :
    |(∫ ω, V ω ∂P)-v₀| ≤ C*t :=
  semimartingale_forward_bound P V (M t) a v₀ C t ht hC hm hi hb
    (hM.integrable t) (true_martingale_mean_zero P F M hM h0 t ht) hV

end BarrierManuscript
#print axioms BarrierManuscript.true_martingale_mean_zero
#print axioms BarrierManuscript.true_semimartingale_forward_bound
