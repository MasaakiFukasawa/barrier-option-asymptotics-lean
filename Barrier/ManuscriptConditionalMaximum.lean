import ManuscriptBridgeProfile

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace BarrierManuscript

/-- The appendix proposition as a conditional-expectation identity under the
surviving measure. `bridgeMean b t x = barPsi b x t / psi b x 1` gives its
specified measurable version for every x < b; conditional expectations are
identified almost everywhere, as required by their mathematical definition. -/
theorem conditional_brownian_maximum {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ s, Measurable (W s))
    (hc : ∀ ω, Continuous (fun s => W s ω)) (t : ℝ≥0) (ht : 0 < t) (ht1 : t < 1)
    (b : ℝ) (hb : 0 < b) :
    let Q := P.restrict {ω | pathMaximum (rawPrefixPath W hc 1 ω) ≤ b}
    Q[W t | MeasurableSpace.comap (W 1) inferInstance] =ᵐ[Q]
      (fun ω => bridgeMean b (t:ℝ) (W 1 ω)) := by
  classical
  dsimp only
  let Q := P.restrict {ω | pathMaximum (rawPrefixPath W hc 1 ω) ≤ b}
  let mX := MeasurableSpace.comap (W 1) inferInstance
  letI : MeasurableSpace Ω := m
  have hle : mX ≤ m := (hm 1).comap_le
  have htr : (t:ℝ) ∈ Ioo (0:ℝ) 1 := by
    constructor
    · exact_mod_cast ht
    · exact_mod_cast ht1
  have hq := bridgeMean_measurable b (t:ℝ)
  have hqi : Integrable (fun ω => bridgeMean b (t:ℝ) (W 1 ω)) Q :=
    (raw_unit_killed_integrable P W hW hm hc b hb _ hq).mpr (bridgeMean_weight_integrable b (t:ℝ) hb htr)
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle (hW.integrable_eval t).integrableOn
    (fun s _ _ => hqi.integrableOn)
  · intro s hs _
    obtain ⟨A,hA,rfl⟩ := hs
    let g : ℝ → ℝ := A.indicator (fun _ => 1)
    have hg : Measurable g := measurable_const.indicator hA
    have hgb x : |g x| ≤ 1 := by
      dsimp only [g,Set.indicator]
      split_ifs <;> norm_num
    have hmoment := brownian_conditional_moment_tests P W hW hm hc t ht ht1 b hb g hg 1 zero_le_one hgb
    have hprice := raw_brownian_killed_expectation P W hW hm hc 1 zero_lt_one b hb
      (fun x => bridgeMean b (t:ℝ) x*g x) (hq.mul hg)
    simp only [NNReal.coe_one] at hprice
    have he (Y : Ω → ℝ) : (∫ ω in (W 1) ⁻¹' A, Y ω ∂Q) = ∫ ω, Y ω*g (W 1 ω) ∂Q := by
      rw [← integral_indicator ((hm 1) hA)]
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by
        by_cases h : W 1 ω ∈ A <;> simp [g,Set.indicator,h]
    rw [he,he,hprice,hmoment]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    calc
      _ = g x*(psi b x 1*bridgeMean b (t:ℝ) x) := by ring
      _ = _ := by rw [bridgeMean_weight b (t:ℝ) x hb hx]
  · have hX : Measurable[mX] (W 1) := Measurable.of_comap_le le_rfl
    exact (hq.comp hX).stronglyMeasurable.aestronglyMeasurable

end BarrierManuscript
#print axioms BarrierManuscript.conditional_brownian_maximum
