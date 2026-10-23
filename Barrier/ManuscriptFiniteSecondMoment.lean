import ManuscriptSecondMomentUI
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem finite_sum_second_moment {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s,MemLp (X i) 2 P) (C : ι → ℝ)
    (hb : ∀ i ∈ s,(∫ ω,(X i ω)^2 ∂P) ≤ C i) :
    MemLp (fun ω => ∑ i ∈ s,X i ω) 2 P ∧
      (∫ ω,(∑ i ∈ s,X i ω)^2 ∂P) ≤ (s.card:ℝ)*∑ i ∈ s,C i := by
  have hs : MemLp (fun ω => ∑ i ∈ s,X i ω) 2 P := memLp_finset_sum _ hX
  have hi i (h : i ∈ s) := (memLp_two_iff_integrable_sq (hX i h).aestronglyMeasurable).mp (hX i h)
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∫ ω,(s.card:ℝ)*∑ i ∈ s,(X i ω)^2 ∂P := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs)
        ((integrable_finset_sum _ hi).const_mul _)
      exact ae_of_all _ fun ω => sq_sum_le_card_mul_sum_sq
    _ = (s.card:ℝ)*∑ i ∈ s,(∫ ω,(X i ω)^2 ∂P) := by
      rw [integral_const_mul,integral_finset_sum _ hi]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) (Nat.cast_nonneg _)

theorem pi_norm_sq_le_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖x‖^2 ≤ ∑ i,(x i)^2 := by
  have hn : 0 ≤ ∑ i,(x i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h : ‖x‖ ≤ Real.sqrt (∑ i,(x i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs,← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  have hs := Real.sq_sqrt hn
  nlinarith [norm_nonneg x,Real.sqrt_nonneg (∑ i,(x i)^2)]

end BarrierManuscript
#print axioms BarrierManuscript.finite_sum_second_moment
#print axioms BarrierManuscript.pi_norm_sq_le_sum_sq
