import ManuscriptDeterministicIntegralPath
import ManuscriptBrownianPathBound
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Fubini for the integration-by-parts path functional against a bounded
test. The integrable path bound is explicit and is supplied by Doob for Brownian paths. -/
theorem weighted_path_integral_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → C(ℝ≥0,ℝ)) (hF : Measurable F)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) (a : ℝ≥0)
    (D Z : Ω → ℝ) (hD : Integrable D P) (hD0 : ∀ ω, 0 ≤ D ω)
    (hbound : ∀ (ω : Ω) (s : ℝ≥0), s ≤ a → |F ω s| ≤ D ω)
    (hZ : Measurable Z) (C : ℝ) (hC : 0 ≤ C) (hZb : ∀ ω, |Z ω| ≤ C) :
    (∫ ω, deterministicIntegralPath g a (F ω)*Z ω ∂P)=
      g a*(∫ ω,F ω a*Z ω ∂P)-
        ∫ s in (0:ℝ)..(a:ℝ),deriv g s*(∫ ω,F ω (Real.toNNReal s)*Z ω ∂P) := by
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0:ℝ) (a:ℝ)) (hg.continuous_deriv le_rfl).continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl,a.coe_nonneg⟩)
  let f : Ω × ℝ → ℝ := fun p => deriv g p.2*F p.1 (Real.toNNReal p.2)*Z p.1
  have heval : Measurable (fun p : Ω × ℝ => F p.1 (Real.toNNReal p.2)) :=
    continuous_eval.measurable.comp ((hF.comp measurable_fst).prodMk
      (continuous_real_toNNReal.measurable.comp measurable_snd))
  have hm : Measurable f := ((hg.continuous_deriv le_rfl).measurable.comp measurable_snd).mul heval |>.mul (hZ.comp measurable_fst)
  have hj : Integrable f (P.prod (volume.restrict (Ioc (0:ℝ) (a:ℝ)))) := by
    apply ((hD.const_mul (K*C)).comp_fst (volume.restrict (Ioc (0:ℝ) (a:ℝ)))).mono' hm.aestronglyMeasurable
    filter_upwards [(Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioc)] with p hp
    change ‖deriv g p.2*F p.1 (Real.toNNReal p.2)*Z p.1‖ ≤ K*C*D p.1
    rw [norm_mul,norm_mul,Real.norm_eq_abs (F _ _),Real.norm_eq_abs (Z _)]
    calc
      _ ≤ K*D p.1*C := mul_le_mul (mul_le_mul (hK p.2 ⟨hp.1.le,hp.2⟩)
        (hbound p.1 (Real.toNNReal p.2) (by change (Real.toNNReal p.2 : ℝ) ≤ (a:ℝ); rw [Real.coe_toNNReal _ hp.1.le]; exact hp.2))
        (abs_nonneg _) hK0) (hZb _) (abs_nonneg _) (mul_nonneg hK0 (hD0 _))
      _ = _ := by ring
  have hterm : Integrable (fun ω => g a*(F ω a*Z ω)) P := by
    apply (hD.mul_const (|g a| * C)).mono'
      ((measurable_const.mul (((continuous_eval_const a).measurable.comp hF).mul hZ)).aestronglyMeasurable)
    filter_upwards [] with ω
    change ‖g a*(F ω a*Z ω)‖ ≤ D ω*(|g a| * C)
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    nlinarith [mul_le_mul (hbound ω a le_rfl) (hZb ω) (abs_nonneg _) (hD0 ω),abs_nonneg (g a)]
  have hi : Integrable (fun ω => ∫ s in (0:ℝ)..(a:ℝ),f (ω,s)) P := by
    simpa only [intervalIntegral.integral_of_le a.coe_nonneg] using hj.integral_prod_left
  have he ω : deterministicIntegralPath g a (F ω)*Z ω=
      g a*(F ω a*Z ω)-(∫ s in (0:ℝ)..(a:ℝ),f (ω,s)) := by
    unfold deterministicIntegralPath
    rw [sub_mul,← intervalIntegral.integral_mul_const]
    simp only [f,mul_assoc]
  simp_rw [he]
  rw [integral_sub hterm hi,integral_const_mul]
  congr 1
  have hs := integral_integral_swap (f := fun ω s => f (ω,s)) hj
  simp only [← intervalIntegral.integral_of_le a.coe_nonneg] at hs
  rw [hs]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [f,mul_assoc,integral_const_mul]

end BarrierManuscript
#print axioms BarrierManuscript.weighted_path_integral_expectation
