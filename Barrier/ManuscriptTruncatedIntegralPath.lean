import ManuscriptDeterministicIntegralPath
import ManuscriptDeterministicItoConstruction
import Chapter2ItoStoppedInterval

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A truncated C1 integrand retains a common, explicit path functional. -/
theorem truncated_integral_path_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (a t : ℝ≥0) (hat : a ≤ t)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (Ioc (0:ℝ) (a:ℝ)).indicator g z.2) N) :
    N (realTimeClamp t)=ᵐ[P] fun ω => deterministicIntegralPath g a (brownianContinuousPath B ω) := by
  obtain ⟨V,hV,hVI⟩ := deterministic_ito_exists P B g hg.continuous.measurable
    (fun r _ => (hg.continuous.pow 2).intervalIntegrable 0 r)
  have hi := ito_stochastic_interval_identity P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W 0) V N (fun z => g z.2)
    (B.martingale 0) hV hN (fun _ => hg.continuous.measurable)
    (fun _ => 0) (fun _ => (a:ℝ)) (fun _ => le_rfl) (fun _ => a.coe_nonneg) (fun _ => a.coe_nonneg)
    (fun r => by simp) (fun r => by simp) hVI hNI
  have hencode := deterministic_integral_path_encoding P B g hg V hV hVI a
  filter_upwards [hi,hencode,hV.initial P B.F] with ω hi he hz
  have hh := hi (realTimeClamp t) (halfTimeClamp_finite t)
  rw [min_eq_left (real_time_clamp_mono (show (a:ℝ) ≤ (t:ℝ) from hat)),
    min_eq_left (real_time_clamp_mono t.coe_nonneg)] at hh
  have hz0 : realTimeClamp 0=(⊥ : HalfClosedTime) := by apply Subtype.ext; simp [realTimeClamp]
  have hz' : V (realTimeClamp 0) ω=0 := by simpa only [hz0,Pi.zero_apply] using hz
  rw [hz',sub_zero,he] at hh
  exact hh

end BarrierManuscript
#print axioms BarrierManuscript.truncated_integral_path_encoding
