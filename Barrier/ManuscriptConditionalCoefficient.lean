import ManuscriptBrownianKilledMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.FactorsThrough

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A conditional mean given a real observable exists as a measurable function
of that observable. The pull-out identity is proved, not postulated. -/
theorem conditional_profile {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℝ) (hX : Measurable X)
    (hY : Integrable Y P) :
    ∃ q : ℝ → ℝ, Measurable q ∧
      P[Y | MeasurableSpace.comap X inferInstance] = q ∘ X ∧
      ∀ f : ℝ → ℝ, Measurable f → Integrable (fun ω => f (X ω)*Y ω) P →
        (∫ ω, f (X ω)*Y ω ∂P) = ∫ ω, f (X ω)*q (X ω) ∂P := by
  let mX := MeasurableSpace.comap X inferInstance
  have hle : mX ≤ m := measurable_iff_comap_le.mp hX
  obtain ⟨q,hq,heq⟩ := (stronglyMeasurable_condExp (μ := P) (m := mX) (f := Y)).exists_eq_measurable_comp
  refine ⟨q,hq.measurable,heq,?_⟩
  intro f hf hfi
  have hmX : Measurable[mX] X := measurable_iff_comap_le.mpr le_rfl
  have hp := condExp_mul_of_stronglyMeasurable_left (μ := P) (m := mX)
    (f := fun ω => f (X ω)) (hf.comp hmX).stronglyMeasurable hfi hY
  have hfun : ((fun ω => f (X ω)) * Y) = (fun ω => f (X ω)*Y ω) := rfl
  rw [hfun] at hp
  calc
    _ = ∫ ω, P[(fun ω => f (X ω)*Y ω) | mX] ω ∂P := (integral_condExp hle).symm
    _ = _ := integral_congr_ae (hp.mono fun ω hω => by simpa only [Pi.mul_apply,heq,Function.comp_apply] using hω)

/-- Conditioning on the endpoint under the surviving subprobability measure
produces the coefficient density appearing in the manuscript. -/
theorem brownian_conditional_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (hb : 0 < b) (Y : Ω → ℝ) (hY : Integrable Y P) :
    ∃ q : ℝ → ℝ, Measurable q ∧
      (P.restrict {ω | brownianMaximum B ω ≤ b})[Y |
        MeasurableSpace.comap (B.W 0 (realTimeClamp 1)) inferInstance] = q ∘ (B.W 0 (realTimeClamp 1)) ∧
      ∀ f : ℝ → ℝ, Measurable f →
        Integrable (fun ω => f (B.W 0 (realTimeClamp 1) ω)*Y ω)
          (P.restrict {ω | brownianMaximum B ω ≤ b}) →
        (∫ ω in {ω | brownianMaximum B ω ≤ b}, f (B.W 0 (realTimeClamp 1) ω)*Y ω ∂P) =
          ∫ x in Iio b, f x*q x*(phi x-phi (x-2*b)) := by
  have hX : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (changed_time_finite 1 (by norm_num))).mono (B.le _) le_rfl
  obtain ⟨q,hq,he,h⟩ := conditional_profile (P.restrict {ω | brownianMaximum B ω ≤ b})
    _ Y hX hY.integrableOn
  refine ⟨q,hq,he,?_⟩
  intro f hf hfi
  rw [h f hf hfi]
  exact brownian_killed_expectation P B b hb (fun x => f x*q x) (hf.mul hq)

end BarrierManuscript
#print axioms BarrierManuscript.conditional_profile
#print axioms BarrierManuscript.brownian_conditional_coefficient
