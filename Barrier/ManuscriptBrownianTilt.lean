import ManuscriptStockCLT
import Chapter6LinearLikelihoodBrownian
import Chapter3IdentityItoIntegral
import Chapter5BracketCommonTime

open MeasureTheory Set Filter Matrix
open scoped Topology ENNReal BigOperators
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4
open Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Constant-drift change of measure with a simultaneous path identity on
[0,1], obtained from the constructed Girsanov theorem. -/
theorem brownian_constant_tilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (a : ℝ) :
    ∃ (Q : Measure Ω) (hQ : IsProbabilityMeasure Q),
      Q = P.withDensity (fun ω => ENNReal.ofReal (Real.exp (a*B.W 0 (realTimeClamp 1) ω-a^2/2))) ∧
      ∃ BQ : BrownianSystem Q 1,
        ∀ᵐ ω ∂Q, ∀ r ∈ Icc (0:ℝ) 1,
          B.W 0 (realTimeClamp r) ω = BQ.W 0 (realTimeClamp r) ω+a*r := by
  have hi := identity_ito_integral P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W 0) (B.martingale 0)
  obtain ⟨Q,hQ,d,hd,hd2,_,hQd,BQ,_,he⟩ := linear_likelihood_changed_brownian P B
    (fun (_ : Fin 1) (_ : Fin 1) _ _ => (1:ℝ))
    (fun (_ : Fin 1) (_ : Fin 1) => B.W 0)
    (fun _ _ _ => measurable_const) (fun _ _ _ => continuous_const)
    (fun _ _ => B.martingale 0)
    (fun _ j => by have hj : j = 0 := Subsingleton.elim _ _; subst j; exact hi)
    1 (by norm_num) (fun _ _ _ _ => by norm_num) 1 (by norm_num) (fun _ => a)
  letI := hQ
  refine ⟨Q,hQ,?_,BQ,?_⟩
  · convert! hQd using 1
    congr 1
    funext ω
    simp [quadraticLogLikelihood,dotProduct,mulVec,pow_two]
  · letI : Nonempty (Icc (0:ℝ) 1) := ⟨⟨0,by norm_num⟩⟩
    have hc := ae_continuous_common_time_equality Q
      (fun r : Icc (0:ℝ) 1 => B.W 0 (realTimeClamp r.val))
      (fun r : Icc (0:ℝ) 1 => fun ω => BQ.W 0 (realTimeClamp r.val) ω+a*r.val)
      (ae_of_all _ fun ω => (continuous_real_path (B.W 0) ((B.martingale 0).path P B.F) ω).comp continuous_subtype_val)
      (ae_of_all _ fun ω => ((continuous_real_path (BQ.W 0) ((BQ.martingale 0).path Q BQ.F) ω).comp continuous_subtype_val).add
        (continuous_const.mul continuous_subtype_val))
      (fun r => by simpa [mul_comm] using he 0 r.val r.property)
    exact hc.mono fun ω hω r hr => hω ⟨r,hr⟩

end BarrierManuscript
#print axioms BarrierManuscript.brownian_constant_tilt
