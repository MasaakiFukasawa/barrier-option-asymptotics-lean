import ManuscriptBrownianPathScaling
import Chapter4DeterministicItoProduct
import Chapter3IdentityItoIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def deterministicIntegralPath (g : ℝ → ℝ) (R : ℝ≥0)
    (f : C(ℝ≥0,ℝ)) : ℝ :=
  g R*f R-∫ s in (0:ℝ)..(R:ℝ),deriv g s*f (Real.toNNReal s)

theorem deterministic_integral_path_measurable (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (R : ℝ≥0) :
    Measurable (deterministicIntegralPath g R) := by
  have hd : Measurable (deriv g) := (hg.continuous_deriv le_rfl).measurable
  have hEval : Measurable (fun p : C(ℝ≥0,ℝ) × ℝ => p.1 (Real.toNNReal p.2)) := by
    exact (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hi := ((hd.comp measurable_snd).mul hEval).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) (R:ℝ)))
  unfold deterministicIntegralPath
  simp_rw [intervalIntegral.integral_of_le R.coe_nonneg]
  exact (measurable_const.mul (continuous_eval_const R).measurable).sub hi.measurable

/-- A deterministic C1 Ito integral is the same measurable functional of
its Brownian path on every probability space. -/
theorem deterministic_integral_path_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N) (R : ℝ≥0) :
    N (realTimeClamp R)=ᵐ[P] fun ω => deterministicIntegralPath g R (brownianContinuousPath B ω) := by
  have hI := identity_ito_integral P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W 0) (B.martingale 0)
  have hAa := (covariance_adapted_variation P B.F B.mono B.le (B.martingale 0) (B.martingale 0) (B.cov 0 0)).adapted
  obtain ⟨V,hV,hVI,hprod⟩ := deterministic_ito_product P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) (B.W 0) (B.martingale 0) (B.martingale 0)
    hAa (fun ω r hr _ => B.diagonal_clock 0 ω r hr) (fun _ => 1) g continuous_const hg hI
  have hVI' : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) V := by
    simpa only [mul_one] using hVI
  have he := hNI.unique P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null
    (B.W 0) N V (fun z => g z.2) (B.martingale 0) hN hV hVI'
  filter_upwards [hprod,he] with ω hp he
  have hh := hp R R.coe_nonneg (EReal.coe_lt_top _)
  rw [← he _ (halfTimeClamp_finite R)] at hh
  unfold deterministicIntegralPath
  have hi : (∫ s in (0:ℝ)..(R:ℝ),deriv g s*(brownianContinuousPath B ω) (Real.toNNReal s))=
      ∫ s in (0:ℝ)..(R:ℝ),deriv g s*B.W 0 (realTimeClamp s) ω := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le R.coe_nonneg] using hs : s ∈ Icc (0:ℝ) R).1
    simp only [brownianContinuousPath,ContinuousMap.coe_mk,Real.coe_toNNReal s hs0]
  rw [hi]
  change N (realTimeClamp R) ω=g R*B.W 0 (realTimeClamp R) ω-_
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.deterministic_integral_path_measurable
#print axioms BarrierManuscript.deterministic_integral_path_encoding
