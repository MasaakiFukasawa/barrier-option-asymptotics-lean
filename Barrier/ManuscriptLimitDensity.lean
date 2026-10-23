import ManuscriptConditionalCoefficient
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem limit_killed_expectation {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b : ℝ) (hb : 0 < b) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω in {ω | M ω ≤ b}, f (X ω) ∂Q) =
      ∫ x in Iio b, f x*(phi x-phi (x-2*b)) := by
  have hB : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (changed_time_finite 1 (by norm_num))).mono (B.le _) le_rfl
  have hid : IdentDistrib (fun ω => (X ω,M ω))
      (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)) Q P :=
    ⟨(hX.prodMk hM).aemeasurable,(hB.prodMk (brownianMaximum_measurable P B)).aemeasurable,hlaw⟩
  let g : ℝ × ℝ → ℝ := fun z => if z.2 ≤ b then f z.1 else 0
  have hg : Measurable g := (hf.comp measurable_fst).ite
    (measurableSet_le measurable_snd measurable_const) measurable_const
  have he := (hid.comp hg).integral_eq
  have hMQ : MeasurableSet {ω | M ω ≤ b} := measurableSet_le hM measurable_const
  have hMP : MeasurableSet {ω | brownianMaximum B ω ≤ b} :=
    measurableSet_le (brownianMaximum_measurable P B) measurable_const
  rw [← integral_indicator hMQ,← brownian_killed_expectation P B b hb f hf,
    ← integral_indicator hMP]
  exact he

/-- The conditional density representation for an arbitrary limiting triple:
only its endpoint/maximum marginal must be Brownian. The volatility coordinate
is not required to be a function of a Brownian path. -/
theorem limit_conditional_coefficient {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M Y : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hY : Integrable Y Q)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b : ℝ) (hb : 0 < b) :
    ∃ q : ℝ → ℝ, Measurable q ∧
      (Q.restrict {ω | M ω ≤ b})[Y | MeasurableSpace.comap X inferInstance] = q ∘ X ∧
      ∀ f : ℝ → ℝ, Measurable f →
        Integrable (fun ω => f (X ω)*Y ω) (Q.restrict {ω | M ω ≤ b}) →
        (∫ ω in {ω | M ω ≤ b}, f (X ω)*Y ω ∂Q) =
          ∫ x in Iio b, f x*q x*(phi x-phi (x-2*b)) := by
  obtain ⟨q,hq,he,h⟩ := conditional_profile (Q.restrict {ω | M ω ≤ b}) X Y hX hY.integrableOn
  refine ⟨q,hq,he,?_⟩
  intro f hf hfi
  rw [h f hf hfi]
  exact limit_killed_expectation P Q B X M hX hM hlaw b hb (fun x => f x*q x) (hf.mul hq)

end BarrierManuscript
#print axioms BarrierManuscript.limit_killed_expectation
#print axioms BarrierManuscript.limit_conditional_coefficient
