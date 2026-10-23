import ManuscriptBrownianPrefixScaling
import ManuscriptRoughTangentLaw
import ManuscriptAlpha

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem rough_alpha_slice {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (C : RoughStockCoupling R)
    (b k u : ℝ) (hb : 0 < b) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ ω, barrierWeight (thetaKernel b k 1 (Real.sqrt (1-u))) b
      (Real.sqrt u*(roughLimit R ω).1,u^R.H*(roughLimit R ω).2.1,
        Real.sqrt u*(roughLimit R ω).2.2) ∂P)=
      -(C.ρ/2)*(∫ s in (0:ℝ)..u,roughKernel R.H R.ν u s*barPsiTimeDerivative b k s) := by
  let F : ℝ × ℝ × ℝ → ℝ := fun z =>
    barrierWeight (thetaKernel b k 1 (Real.sqrt (1-u))) b
      (Real.sqrt u*z.1,u^R.H*z.2.1,Real.sqrt u*z.2.2)
  have hm : Measurable F := by
    have hphi := phi_contDiff.continuous.measurable
    unfold F barrierWeight thetaKernel
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) measurable_const
  have hl := (rough_tangent_joint_law P D R C u hu.1).comp hm
  have he : (∫ ω,F ((scaledBrownian D.B u hu.1).W 0 (realTimeClamp 1) ω,
      roughVarianceTangent R u ω,brownianMaximum (scaledBrownian D.B u hu.1) ω) ∂P)=
      -(1/2)*(∫ ω,R.N u (realTimeClamp u) ω*stockKernelTest D.B b k (NNReal.mk u hu.1.le) ω ∂P) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [brownian_maximum_noatom P (scaledBrownian D.B u hu.1)
      (b/Real.sqrt u) (div_pos hb (Real.sqrt_pos.mpr hu.1))] with ω hn
    have hn' : Real.sqrt u*brownianMaximum (scaledBrownian D.B u hu.1) ω ≠ b := by
      intro h
      exact hn ((eq_div_iff (Real.sqrt_pos.mpr hu.1).ne').mpr (by simpa only [mul_comm] using h))
    have hi : Real.sqrt u*brownianMaximum (scaledBrownian D.B u hu.1) ω < b ↔
        Real.sqrt u*brownianMaximum (scaledBrownian D.B u hu.1) ω ≤ b :=
      lt_iff_le_and_ne.trans (and_iff_left hn')
    have hx : Real.sqrt u*(scaledBrownian D.B u hu.1).W 0 (realTimeClamp 1) ω=
        D.B.W 0 (realTimeClamp u) ω := by
      rw [scaledBrownian_W P D.B u 1 hu.1 zero_le_one,mul_one,
        mul_div_cancel₀ _ (Real.sqrt_pos.mpr hu.1).ne']
    have hy : u^R.H*roughVarianceTangent R u ω=R.N u (realTimeClamp u) ω := by
      exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hu.1 R.H).ne'
    dsimp only [F]
    unfold barrierWeight stockKernelTest brownianBarrierKernelTest
    dsimp only
    rw [hx,hy,brownian_system_prefix_scaling P D.B (NNReal.mk u hu.1.le) hu.1 ω]
    simp only [hi, NNReal.coe_mk]
    split_ifs
    · rw [thetaKernel_psi]; ring
    · ring
  change (∫ ω,F (roughLimit R ω) ∂P)=_
  have hle := hl.integral_eq
  dsimp only [Function.comp_def] at hle
  have hh := rough_model_kernel_moment P D R C b k hb (NNReal.mk u hu.1.le) hu.1 hu.2
  dsimp only [NNReal.coe_mk] at hh
  rw [← hle,he,hh]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.rough_alpha_slice
