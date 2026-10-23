import ManuscriptDeterministicItoLaw
import ManuscriptRoughKernel

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The singular Volterra integral in rough Bergomi has variance nu^2*t^(2H).
The hypothesis identifies the actual Ito integral; its Gaussian law is proved. -/
theorem rough_integral_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν t : ℝ) (hH : 0 < H) (ht : 0 ≤ t)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N) :
    HasLaw (N (realTimeClamp t)) (gaussianReal 0 ⟨ν^2*t^(2*H),by positivity⟩) P := by
  have hm : Measurable (roughKernel H ν t) := by
    unfold roughKernel Asakura.mvnFutureFunction
    exact measurable_const.mul ((measurable_const.sub measurable_id).pow_const _ |>.indicator measurableSet_Ioc)
  have hi r (_ : 0 ≤ r) : IntervalIntegrable (fun s => roughKernel H ν t s^2) volume 0 r :=
    (rough_kernel_square_integrable H ν t hH ht).intervalIntegrable
  have hl := measurable_deterministic_ito_law P B _ hm hi N hN hNI t ht
  convert hl using 1
  congr 1
  apply NNReal.eq
  exact (rough_kernel_variance H ν t hH ht).symm

theorem rough_normalized_integral_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν t : ℝ) (hH : 0 < H) (ht : 0 < t)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N) :
    HasLaw (fun ω => N (realTimeClamp t) ω/t^H) (gaussianReal 0 ⟨ν^2,by positivity⟩) P := by
  have hl := gaussianReal_const_mul (rough_integral_law P B H ν t hH ht.le N hN hNI) (1/t^H)
  have hp : t^(2*H)=(t^H)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ht.le]
    congr 1
    ring
  have he : (NNReal.mk ((1/t^H)^2) (sq_nonneg _))*⟨ν^2*t^(2*H),by positivity⟩=⟨ν^2,by positivity⟩ := by
    apply NNReal.eq
    change (1/t^H)^2*(ν^2*t^(2*H))=ν^2
    rw [hp]
    have hn := (Real.rpow_pos_of_pos ht H).ne'
    field_simp
  rw [he,mul_zero] at hl
  convert hl using 1
  funext ω
  ring

end BarrierManuscript
#print axioms BarrierManuscript.rough_integral_law
#print axioms BarrierManuscript.rough_normalized_integral_law
