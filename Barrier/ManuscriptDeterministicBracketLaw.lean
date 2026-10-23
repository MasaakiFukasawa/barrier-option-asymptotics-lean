import Chapter4DeterministicItoLaw
import Chapter6CovarianceCommonTime

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace BarrierManuscript
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- A locally integrable deterministic nonnegative bracket density gives the exact Gaussian
terminal law, including the zero-variance case. -/
theorem integrable_deterministic_bracket_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t,F t ≤ (inferInstance : MeasurableSpace Ω))
    (hnull : ∀ t A,MeasurableSet A → P A=0 → MeasurableSet[F t] A)
    (N C : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (hC : LocalCovarianceWitness P F N N C)
    (f : ℝ → ℝ) (hf : ∀ r, 0 ≤ r → IntervalIntegrable f volume 0 r) (hpos : ∀ r≥0,0≤f r)
    (hCe : ∀ r≥0,C (realTimeClamp r)=ᵐ[P] fun _ => ∫ s in 0..r,f s)
    (R : ℝ) (hR : 0≤R) :
    HasLaw (N (realTimeClamp R))
      (gaussianReal 0 ⟨∫ s in 0..R,f s,
        intervalIntegral.integral_nonneg hR (fun s hs => hpos s hs.1)⟩) P := by
  have hcommon := covariance_density_common_time P F N N C hN hN hC
    (fun z : Ω × ℝ => f z.2)
    (fun r hr => ae_of_all _ fun _ => hf r hr) hCe R hR
  let q := fun t : HalfClosedTime => ∫ s in 0..(finitePrefixTime R hR t).val,f s
  have hRt : realTimeClamp R<⊤ := real_time_below R hR (EReal.coe_lt_top _)
  have hqr : q (realTimeClamp R)=∫ s in 0..R,f s := by
    dsimp only [q]
    rw [finite_prefix_time_of_real R R hR ⟨hR,le_rfl⟩ le_top]
  have hq0 : q ⊥=0 := by
    have hz : (finitePrefixTime (T := ⊤) R hR ⊥).val=0 := by
      change (min (0:EReal) (R:EReal)).toReal=0
      rw [min_eq_left (by exact_mod_cast hR),EReal.toReal_zero]
    dsimp only [q]
    rw [hz,intervalIntegral.integral_same]
  have hqm : MonotoneOn q (Iic (realTimeClamp R)) := by
    intro s hs t ht hst
    let a := (finitePrefixTime R hR s).val
    let b := (finitePrefixTime R hR t).val
    have hab : a≤b := finite_prefix_time_mono R hR hst
    have ha : 0≤a := (finitePrefixTime R hR s).property.1
    have hi := intervalIntegral.integral_nonneg (μ := volume) hab (fun r hr => hpos r (ha.trans hr.1))
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf a ha) ((hf a ha).symm.trans (hf b (ha.trans hab)))
    change (∫ s in 0..a,f s)≤∫ s in 0..b,f s
    linarith
  have hq : ∀ᵐ w ∂P,∀ t,t≤realTimeClamp R → C t w=q t := by
    filter_upwards [hcommon] with w hw
    intro t ht
    obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t (ht.trans_lt hRt)
    have hrR : r≤R := by
      change (realTimeClamp r:EReal)≤(realTimeClamp R:EReal) at ht
      rw [real_time_clamp_eq r hr hrT.le,real_time_clamp_eq R hR le_top] at ht
      exact EReal.coe_le_coe_iff.mp ht
    dsimp only [q]
    rw [finite_prefix_time_of_real R r hR ⟨hr,hrR⟩ le_top]
    exact hw r ⟨hr,hrR⟩
  have hl := (deterministic_bracket_gaussian_increment P (by simp) F hF hle hnull N C hN hC
    q (realTimeClamp R) ⊥ hRt bot_le hqm hq).1
  have he : N (realTimeClamp R)=ᵐ[P] fun w => N (realTimeClamp R) w-N ⊥ w := by
    filter_upwards [hN.initial P F] with w hw
    simp only [hw,Pi.zero_apply,sub_zero]
  have hh := hl.congr he
  convert hh using 1
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mk,hqr,hq0,sub_zero]

end BarrierManuscript

#print axioms BarrierManuscript.integrable_deterministic_bracket_law
