import ManuscriptRawBrownianScaling
import ManuscriptLimitPsiMoment

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem raw_brownian_killed_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ht : 0 < t)
    (b : ℝ) (hb : 0 < b) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω in {ω | pathMaximum (rawPrefixPath W hc t ω) ≤ b}, f (W t ω) ∂P) =
      ∫ x in Iio b, f x*psi b x (t:ℝ) := by
  classical
  have htr : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  let B := scaledBrownian (naturalBrownianSystem P W hW hm hc) (t:ℝ) htr
  have hX : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (halfTimeClamp_finite 1)).mono (B.le _) le_rfl
  have hM := brownianMaximum_measurable P B
  have hw : 0 < Real.sqrt (t:ℝ) := Real.sqrt_pos.mpr htr
  have heW ω := congrArg Prod.fst (rawPrefix_brownian_scaling P W hW hm hc t ht ω)
  have heM ω := congrArg Prod.snd (rawPrefix_brownian_scaling P W hW hm hc t ht ω)
  change ∀ ω, W t ω=Real.sqrt (t:ℝ)*B.W 0 (realTimeClamp 1) ω at heW
  change ∀ ω, pathMaximum (rawPrefixPath W hc t ω)=Real.sqrt (t:ℝ)*brownianMaximum B ω at heM
  have hset : MeasurableSet {ω | pathMaximum (rawPrefixPath W hc t ω) ≤ b} :=
    measurableSet_le (pathMaximum_lipschitz.continuous.measurable.comp (rawPrefixPath_measurable W hm hc t)) measurable_const
  have h := scaled_killed_integral P P B (B.W 0 (realTimeClamp 1)) (brownianMaximum B)
    hX hM rfl b (t:ℝ) hb htr f hf
  rw [← h,← integral_indicator hset]
  apply integral_congr_ae
  filter_upwards [brownian_maximum_noatom P B (b/Real.sqrt (t:ℝ)) (div_pos hb hw)] with ω hn
  have hn' : Real.sqrt (t:ℝ)*brownianMaximum B ω ≠ b := by
    intro he
    exact hn ((eq_div_iff hw.ne').mpr (by simpa only [mul_comm] using he))
  have hi : Real.sqrt (t:ℝ)*brownianMaximum B ω < b ↔ Real.sqrt (t:ℝ)*brownianMaximum B ω ≤ b :=
    lt_iff_le_and_ne.trans (and_iff_left hn')
  simp only [Set.indicator,Set.mem_setOf_eq,barrierWeight,heW,heM,mul_one,hi]

end BarrierManuscript
#print axioms BarrierManuscript.raw_brownian_killed_expectation
