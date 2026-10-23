import ManuscriptRawKilledDensity

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem raw_unit_killed_measure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ s, Measurable (W s))
    (hc : ∀ ω, Continuous (fun s => W s ω)) (b : ℝ) (hb : 0 < b) :
    (P.restrict {ω | pathMaximum (rawPrefixPath W hc 1 ω) ≤ b}).map (W 1) =
      volume.withDensity (fun x => ENNReal.ofReal (killedDensity b x)) := by
  let B := scaledBrownian (naturalBrownianSystem P W hW hm hc) 1 zero_lt_one
  have h1 : W 1=B.W 0 (realTimeClamp 1) := by
    funext ω
    have h := congrArg Prod.fst (rawPrefix_brownian_scaling P W hW hm hc 1 zero_lt_one ω)
    simpa only [NNReal.coe_one,Real.sqrt_one,one_mul] using h
  have h2 : ∀ ω, pathMaximum (rawPrefixPath W hc 1 ω)=brownianMaximum B ω := by
    intro ω
    have h := congrArg Prod.snd (rawPrefix_brownian_scaling P W hW hm hc 1 zero_lt_one ω)
    simpa only [NNReal.coe_one,Real.sqrt_one,one_mul] using h
  simp_rw [h1,h2]
  exact brownian_killed_density P B b hb

theorem raw_unit_killed_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ s, Measurable (W s))
    (hc : ∀ ω, Continuous (fun s => W s ω)) (b : ℝ) (hb : 0 < b)
    (q : ℝ → ℝ) (hq : Measurable q) :
    Integrable (fun ω => q (W 1 ω)) (P.restrict {ω | pathMaximum (rawPrefixPath W hc 1 ω) ≤ b}) ↔
      IntegrableOn (fun x => psi b x 1*q x) (Iio b) := by
  classical
  have hd : Measurable (killedDensity b) :=
    (phi_contDiff.continuous.measurable.sub
      (phi_contDiff.continuous.measurable.comp (measurable_id.sub_const (2*b)))).ite measurableSet_Iio measurable_const
  change Integrable (q ∘ W 1) _ ↔ _
  rw [← integrable_map_measure hq.aestronglyMeasurable (hm 1).aemeasurable,
    raw_unit_killed_measure P W hW hm hc b hb,
    integrable_withDensity_iff_integrable_smul' hd.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (killedDensity_nonneg b hb.le _),smul_eq_mul]
  have he : (fun x => killedDensity b x*q x)=(Iio b).indicator (fun x => psi b x 1*q x) := by
    funext x
    simp only [killedDensity,psi,Real.sqrt_one,div_one,Set.indicator,mem_Iio]
    split_ifs <;> ring
  rw [he,integrable_indicator_iff measurableSet_Iio]

end BarrierManuscript
#print axioms BarrierManuscript.raw_unit_killed_measure
#print axioms BarrierManuscript.raw_unit_killed_integrable
