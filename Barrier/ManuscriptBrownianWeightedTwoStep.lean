import ManuscriptWeightedKernelComposition
import ManuscriptSegmentSurvival
import ManuscriptRawKilledDensity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem brownian_two_step_weighted_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t d : ℝ≥0) (ht : 0 < t) (hd : 0 < d)
    (b : ℝ) (hb : 0 < b) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ q, |f q| ≤ C*(1+|q.1|)) :
    (∫ ω in {ω | pathMaximum (rawPrefixPath W hc (t+d) ω) ≤ b}, f (W t ω,W (t+d) ω) ∂P) =
      ∫ x in Iio b, (∫ y in Iio (b-x), f (x,x+y)*psi (b-x) y (d:ℝ))*psi b x (t:ℝ) := by
  let Z := fun s ω => W (t+s) ω-W t ω
  have hZm : ∀ s, Measurable (Z s) := fun s => (hm (t+s)).sub (hm t)
  have hZc : ∀ ω, Continuous (fun s => Z s ω) := fun ω =>
    ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hZlaw := (brownian_future_independent_past P W hW hm hc t).1
  let A := fun ω => (W t ω,pathMaximum (rawPrefixPath W hc t ω))
  let B := fun ω => (Z d ω,pathMaximum (rawPrefixPath Z hZc d ω))
  have hA : Measurable A := (hm t).prodMk (pathMaximum_lipschitz.continuous.measurable.comp (rawPrefixPath_measurable W hm hc t))
  have hB : Measurable B := (hZm d).prodMk (pathMaximum_lipschitz.continuous.measurable.comp (rawPrefixPath_measurable Z hZm hZc d))
  have hind : IndepFun A B P := by
    simpa only [A,B,Z,endpointMaximum,rawPrefixPath,ContinuousMap.coe_mk,mul_one] using
      brownian_segment_independence P W hW hm hc t d
  have hk₁ (q : ℝ → ℝ) (hq : Measurable q) :
      (∫ ω, if (A ω).2 ≤ b then q (A ω).1 else 0 ∂P)=∫ x in Iio b, q x*psi b x (t:ℝ) := by
    rw [← raw_brownian_killed_expectation P W hW hm hc t ht b hb q hq,
      ← integral_indicator (measurableSet_le hA.snd measurable_const)]
    rfl
  have hk₂ (c : ℝ) (hcpos : 0 < c) (q : ℝ → ℝ) (hq : Measurable q) :
      (∫ ω, if (B ω).2 ≤ c then q (B ω).1 else 0 ∂P)=∫ x in Iio c, q x*psi c x (d:ℝ) := by
    rw [← raw_brownian_killed_expectation P Z hZlaw hZm hZc d hd c hcpos q hq,
      ← integral_indicator (measurableSet_le hB.snd measurable_const)]
    rfl
  have h := weighted_killed_kernel_composition P A B hA hB hind (hW.integrable_eval t) b (fun x => psi b x (t:ℝ))
    (fun c y => psi c y (d:ℝ)) hk₁ hk₂ f hf C hC hbound
  have hset : MeasurableSet {ω | pathMaximum (rawPrefixPath W hc (t+d) ω) ≤ b} :=
    measurableSet_le (pathMaximum_lipschitz.continuous.measurable.comp (rawPrefixPath_measurable W hm hc (t+d))) measurable_const
  rw [← h,← integral_indicator hset]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    have hs := raw_survival_split W hc t d ht hd b ω
    simp only [Set.indicator,Set.mem_ofPred_eq,A,B,Z,hs,add_sub_cancel]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_two_step_weighted_integral
