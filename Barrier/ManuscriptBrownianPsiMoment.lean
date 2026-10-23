import ManuscriptGeometricWeakLimit
import ManuscriptBarPsi

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem brownian_prefix_maximum_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (u : ℝ) (hu : 0 < u) (ω : Ω) :
    pathMaximum (brownianStoppedPath B u hu.le ω) =
      Real.sqrt u*brownianMaximum (scaledBrownian B u hu) ω := by
  have h := scaledBrownian_maximum P B u hu ω (fun ω => (brownianStoppedPath B u hu.le ω).continuous)
  change brownianMaximum (scaledBrownian B u hu) ω=pathMaximum (brownianStoppedPath B u hu.le ω)/Real.sqrt u at h
  rw [h,mul_div_cancel₀ _ (Real.sqrt_pos.mpr hu).ne']

theorem brownian_prefix_maximum_noatom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∀ᵐ ω ∂P, pathMaximum (brownianStoppedPath B u hu.le ω) ≠ b := by
  filter_upwards [brownian_maximum_noatom P (scaledBrownian B u hu) (b/Real.sqrt u)
    (div_pos hb (Real.sqrt_pos.mpr hu))] with ω hω
  rw [brownian_prefix_maximum_scaling P B u hu ω]
  intro he
  apply hω
  apply (eq_div_iff (Real.sqrt_pos.mpr hu).ne').mpr
  simpa only [mul_comm] using he

theorem brownian_prefix_psi_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k u : ℝ) (hb : 0 < b) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ ω, barrierWeight (fun x => x*thetaKernel b k 1 (Real.sqrt (1-u)) x) b
      (B.W 0 (realTimeClamp u) ω,(1:ℝ),pathMaximum (brownianStoppedPath B u hu.1.le ω)) ∂P) =
      -(1/2)*barPsi b k u := by
  let Bu := scaledBrownian B u hu.1
  let f := fun x => x*thetaKernel b k 1 (Real.sqrt (1-u)) x
  have hf : Measurable f := by
    unfold f thetaKernel
    exact measurable_id.mul (measurable_const.mul
      ((phi_contDiff.continuous.measurable.comp (by fun_prop)).sub
        (phi_contDiff.continuous.measurable.comp (by fun_prop))))
  have hX ω : B.W 0 (realTimeClamp u) ω = Real.sqrt u*Bu.W 0 (realTimeClamp 1) ω := by
    rw [scaledBrownian_W P B u 1 hu.1 zero_le_one ω,mul_one,mul_div_cancel₀ _ (Real.sqrt_pos.mpr hu.1).ne']
  have he : (∫ ω, barrierWeight f b (B.W 0 (realTimeClamp u) ω,(1:ℝ),pathMaximum (brownianStoppedPath B u hu.1.le ω)) ∂P) =
      ∫ ω in {ω | brownianMaximum Bu ω ≤ b/Real.sqrt u}, f (Real.sqrt u*Bu.W 0 (realTimeClamp 1) ω) ∂P := by
    rw [← integral_indicator (measurableSet_le (brownianMaximum_measurable P Bu) measurable_const)]
    apply integral_congr_ae
    filter_upwards [brownian_maximum_noatom P Bu (b/Real.sqrt u) (div_pos hb (Real.sqrt_pos.mpr hu.1))] with ω hn
    rw [hX ω,brownian_prefix_maximum_scaling P B u hu.1 ω]
    unfold barrierWeight
    dsimp only
    have hiff : Real.sqrt u*brownianMaximum Bu ω < b ↔ brownianMaximum Bu ω ≤ b/Real.sqrt u := by
      rw [mul_comm,← lt_div_iff₀ (Real.sqrt_pos.mpr hu.1)]
      exact lt_iff_le_and_ne.trans (and_iff_left hn)
    simp only [mul_one]
    change (if Real.sqrt u*brownianMaximum Bu ω < b then f (Real.sqrt u*Bu.W 0 (realTimeClamp 1) ω) else 0) = _
    simp only [hiff,Set.indicator,Set.mem_setOf_eq]
  rw [he,brownian_killed_expectation P Bu (b/Real.sqrt u) (div_pos hb (Real.sqrt_pos.mpr hu.1))
    (fun x => f (Real.sqrt u*x)) (hf.comp (measurable_const.mul measurable_id))]
  simp_rw [← psi_at_one]
  have hscale := psi_integral_scaling b u hu.1 f (fun _ => 1)
  simp only [mul_one] at hscale
  rw [hscale]
  have hp x : f x*psi b x u = -(1/2)*(x*psi (b-x) (k-x) (1-u)*psi b x u) := by
    dsimp only [f]
    rw [thetaKernel_psi]
    ring
  simp_rw [hp]
  rw [integral_const_mul,psi_convolution b k u hu]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_prefix_maximum_scaling
#print axioms BarrierManuscript.brownian_prefix_maximum_noatom
#print axioms BarrierManuscript.brownian_prefix_psi_moment
