import ManuscriptBrownianTilt
import ManuscriptBrownianKilledMeasure
import ManuscriptStockPathEncoding

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem brownian_maximum_le_real_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (ω : Ω) (b : ℝ) :
    brownianMaximum B ω ≤ b ↔ ∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω ≤ b := by
  let f := continuousPath (brownianPrefix B) (brownian_prefix_regular P B).2 ω
  constructor
  · intro h r hr
    have hh := (le_csSup (path_range_bddAbove f) (mem_range_self (realTimeClamp r))).trans h
    simpa only [f,continuousPath,ContinuousMap.coe_mk,brownianPrefix,
      min_eq_right (real_time_clamp_mono hr.2)] using hh
  · intro h
    apply csSup_le (range_nonempty f)
    rintro y ⟨t,rfl⟩
    let r := finitePrefixTime 1 (by norm_num) t
    have hh := h r.val r.property
    rw [finite_prefix_time_clamp 1 (by norm_num) le_top] at hh
    exact hh

theorem integral_inverse_positive_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d f : Ω → ℝ) (hd : Measurable d) (hp : ∀ ω, 0 < d ω) :
    (∫ ω, f ω/d ω ∂P.withDensity (fun ω => ENNReal.ofReal (d ω))) = ∫ ω, f ω ∂P := by
  rw [integral_withDensity_eq_integral_toReal_smul hd.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change (ENNReal.ofReal (d ω)).toReal * (f ω/d ω) = f ω
    rw [ENNReal.toReal_ofReal (hp ω).le]
    field_simp [(hp ω).ne']

/-- Killed endpoint density for Brownian motion with constant drift -a.
The exponential factor is derived by Girsanov, not posited as a survival
correction for a stochastic-volatility process. -/
theorem drifted_brownian_killed_density {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (a b : ℝ) (hb : 0 < b) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω, if (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-a*r ≤ b)
      then f (B.W 0 (realTimeClamp 1) ω-a) else 0 ∂P) =
      ∫ x in Iio b, (f x*Real.exp (-a*x-a^2/2))*(phi x-phi (x-2*b)) := by
  obtain ⟨Q,hQ,hQd,BQ,he⟩ := brownian_constant_tilt P B a
  letI := hQ
  let d := fun ω => Real.exp (a*B.W 0 (realTimeClamp 1) ω-a^2/2)
  have hdm : Measurable d := (((B.martingale 0).adapted P B.F _ (halfTimeClamp_finite 1)).mono (B.le _) le_rfl |>.const_mul a |>.sub_const (a^2/2)).exp
  let g := fun ω => if (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-a*r ≤ b)
    then f (B.W 0 (realTimeClamp 1) ω-a) else 0
  have hchange : (∫ ω, g ω/d ω ∂Q) = ∫ ω, g ω ∂P := by
    rw [hQd]
    exact integral_inverse_positive_density P d g hdm (fun _ => Real.exp_pos _)
  rw [← hchange,← brownian_killed_expectation Q BQ b hb (fun x => f x*Real.exp (-a*x-a^2/2))
    (hf.mul (by fun_prop)),← integral_indicator (measurableSet_le (brownianMaximum_measurable Q BQ) measurable_const)]
  apply integral_congr_ae
  filter_upwards [he] with ω hω
  have h1 := hω 1 (by norm_num)
  have hs : (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-a*r ≤ b) ↔ brownianMaximum BQ ω ≤ b := by
    rw [brownian_maximum_le_real_iff Q BQ ω b]
    constructor <;> intro h r hr
    · have hh := h r hr; rw [hω r hr] at hh; linarith
    · rw [hω r hr]; simpa using h r hr
  dsimp only [g,d]
  rw [show B.W 0 (realTimeClamp 1) ω-a = BQ.W 0 (realTimeClamp 1) ω by simpa using congrArg (fun x => x-a) h1]
  by_cases hm : brownianMaximum BQ ω ≤ b
  · rw [if_pos (hs.mpr hm),Set.indicator_of_mem (show ω ∈ {ω | brownianMaximum BQ ω ≤ b} from hm)]
    rw [div_eq_mul_inv,← Real.exp_neg]
    congr 2
    rw [h1]
    ring
  · rw [if_neg (fun h => hm (hs.mp h)),zero_div,Set.indicator_of_notMem (show ω ∉ {ω | brownianMaximum BQ ω ≤ b} from hm)]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_maximum_le_real_iff
#print axioms BarrierManuscript.integral_inverse_positive_density
#print axioms BarrierManuscript.drifted_brownian_killed_density
