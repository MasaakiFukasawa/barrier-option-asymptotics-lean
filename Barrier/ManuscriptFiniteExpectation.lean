import ManuscriptItoExpectation
import ManuscriptDriftFubini
import ManuscriptVarianceClock
import Chapter5BracketCommonTime

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace BarrierManuscript

/-- Assemble common-time equality, removal of localization and Fubini for a
finite-cutoff Ito price. Joint L1 drift and an integrable path bound suffice. -/
theorem finite_ito_expectation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (price : ℝ → Ω → ℝ) (p : ℝ)
    (hpc : ∀ ω, ContinuousOn (fun r => price r ω) (Icc 0 T))
    (g : Ω × ℝ → ℝ) (hgi : Integrable g (P.prod (volume.restrict (Ioo 0 1))))
    (hrep : ∀ r ∈ Icc 0 T, price r =ᵐ[P] fun ω => p+N (realTimeClamp r) ω+∫ s in 0..r, g (ω,s))
    (C : Ω → ℝ) (hC : Integrable C P)
    (hbound : ∀ᵐ ω ∂P, ∀ r ∈ Icc 0 T, |price r ω| ≤ C ω) :
    Integrable (price T) P ∧
      (∫ ω, price T ω ∂P) = p + ∫ s in 0..T, ∫ ω, g (ω,s) ∂P := by
  have hNreal ω : Continuous (fun r : ℝ => N (realTimeClamp r) ω) :=
    continuous_iff_continuousAt.mpr fun r => (hN.path P F ω _
      (lt_of_le_of_lt (real_time_clamp_mono (le_max_right 0 r))
        (changed_time_finite _ (le_max_left _ _)))).comp real_time_clamp_continuous.continuousAt
  have hfull : ∀ᵐ ω ∂P, IntervalIntegrable (fun s => g (ω,s)) volume 0 1 :=
    hgi.prod_right_ae.mono fun ω hω =>
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr hω
  have hsub : uIcc (0:ℝ) T ⊆ uIcc 0 1 := by
    simp only [uIcc_of_le hT,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hT1
  have hcommon := bracket_primitive_common_time P T hT
    (fun r ω => price r ω-p-N (realTimeClamp r) ω) (fun ω s => g (ω,s))
    (fun ω => ((hpc ω).sub continuousOn_const).sub (hNreal ω).continuousOn)
    (hfull.mono fun ω hω => hω.mono_set hsub)
    (fun r hr => (hrep r hr).mono fun ω hω => by dsimp only; linarith)
  let pr := fun (t : HalfClosedTime) (ω : Ω) => price (finitePrefixTime T hT t).val ω
  let dr := fun (t : HalfClosedTime) (ω : Ω) => ∫ s in 0..(finitePrefixTime T hT t).val, g (ω,s)
  let B := fun ω => ∫ s in (0:ℝ)..1, |g (ω,s)|
  have hiB : Integrable B P := by
    simpa only [B,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo,Real.norm_eq_abs] using hgi.integral_norm_prod_left
  have hrep' : ∀ᵐ ω ∂P, ∀ t, t ≤ realTimeClamp T → pr t ω = p+N t ω+dr t ω := by
    filter_upwards [hcommon] with ω hω
    intro t ht
    have he := hω (finitePrefixTime T hT t).val (finitePrefixTime T hT t).property
    rw [finite_prefix_time_clamp T hT le_top,min_eq_right ht] at he
    dsimp only [pr,dr]
    linarith
  have hpr : ∀ᵐ ω ∂P, ∀ t, t ≤ realTimeClamp T → |pr t ω| ≤ C ω :=
    hbound.mono fun ω hω t _ => hω _ (finitePrefixTime T hT t).property
  have hdr : ∀ᵐ ω ∂P, ∀ t, t ≤ realTimeClamp T → |dr t ω| ≤ B ω := by
    filter_upwards [hfull] with ω hω
    intro t ht
    have hp := (finitePrefixTime T hT t).property
    exact (intervalIntegral.abs_integral_le_integral_abs hp.1).trans
      (intervalIntegral.integral_mono_interval le_rfl hp.1 (hp.2.trans hT1)
        (ae_of_all _ fun _ => abs_nonneg _) hω.norm)
  have hself : (finitePrefixTime T hT (realTimeClamp (T := (⊤:EReal)) T)).val = T := by
    change (min (realTimeClamp (T := (⊤:EReal)) T : EReal) (T:EReal)).toReal = T
    rw [real_time_clamp_eq T hT le_top,min_self,EReal.toReal_coe]
  have hprodT : Integrable g (P.prod (volume.restrict (Ioo 0 T))) :=
    hgi.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono (Ioo_subset_Ioo le_rfl hT1) le_rfl))
  have hdrm : AEStronglyMeasurable (dr (realTimeClamp T)) P := by
    simpa only [dr,hself,intervalIntegral.integral_of_le hT,integral_Ioc_eq_integral_Ioo]
      using hprodT.integral_prod_left.aestronglyMeasurable
  obtain ⟨hi,_,he⟩ := local_ito_expectation_of_random_bounds P F hF hle N hN
    (realTimeClamp T) (changed_time_finite T hT) pr dr p C hC hrep' hpr B hiB hdr hdrm
  have hfub : (∫ ω, (∫ s in 0..T, g (ω,s)) ∂P) = ∫ s in 0..T, ∫ ω, g (ω,s) ∂P := by
    simpa only [intervalIntegral.integral_of_le hT,integral_Ioc_eq_integral_Ioo] using
      (integral_integral_swap (f := fun ω s => g (ω,s)) hprodT)
  simpa only [pr,dr,hself,hfub] using And.intro hi he

end BarrierManuscript
#print axioms BarrierManuscript.finite_ito_expectation
