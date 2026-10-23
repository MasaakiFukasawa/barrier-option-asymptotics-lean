import ManuscriptBarrierLimit
import ManuscriptGaussianBounds

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Deterministically varying kernels are adjoined as coordinates before
applying Portmanteau and UI. Global uniform convergence of the kernels is
not needed. -/
theorem weak_varying_barrier_expectation {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : ℕ → Ω → ℝ × ℝ × ℝ) (z : Γ → ℝ × ℝ × ℝ)
    (h : TendstoInDistribution Z atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun n ω => (Z n ω).2.1) 1 P)
    (p : ℕ → ℝ × ℝ) (p₀ : ℝ × ℝ) (hp : Tendsto p atTop (𝓝 p₀))
    (w : (ℝ × ℝ) × ℝ → ℝ) (hwm : Measurable w)
    (hw : ∀ x, ContinuousAt w (p₀,x))
    (C : ℝ) (hC : 0 < C) (hbw : ∀ n x, |w (p n,x)| ≤ C)
    (b : ℝ) (hnoatom : ∀ᵐ ω ∂Q, (z ω).2.2 ≠ b) :
    Integrable (fun ω => barrierWeight (fun x => w (p₀,x)) b (z ω)) Q ∧
    Tendsto (fun n => ∫ ω, barrierWeight (fun x => w (p n,x)) b (Z n ω) ∂P) atTop
      (𝓝 (∫ ω, barrierWeight (fun x => w (p₀,x)) b (z ω) ∂Q)) := by
  have hpi : TendstoInMeasure P (fun n (_ : Ω) => p n) atTop (fun _ => p₀) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const) (ae_of_all _ fun _ => hp)
  have hj := h.prodMk_of_tendstoInMeasure_const Z (fun n (_ : Ω) => p n) z hpi
    (fun _ => aemeasurable_const)
  let g := fun a : (ℝ × ℝ × ℝ) × (ℝ × ℝ) =>
    if a.1.2.2 < b then (w (a.2,a.1.1)/C)*a.1.2.1 else 0
  have hg : Measurable g := by
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · exact ((hwm.comp (by fun_prop)).div_const C).mul (by fun_prop)
    · exact measurable_const
  have hgc : ∀ᵐ ω ∂Q, ContinuousAt g (z ω,p₀) := by
    filter_upwards [hnoatom] with ω hω
    have hpair : ContinuousAt
        (fun a : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => (a.2,a.1.1)) (z ω,p₀) := by fun_prop
    have hcomp : ContinuousAt (fun a : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => w (a.2,a.1.1)) (z ω,p₀) :=
      ContinuousAt.comp (f := fun a : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => (a.2,a.1.1)) (hw ((z ω).1)) hpair
    have hv : ContinuousAt (fun a : (ℝ × ℝ × ℝ) × (ℝ × ℝ) =>
        (w (a.2,a.1.1)/C)*a.1.2.1) (z ω,p₀) :=
      (hcomp.div_const C).mul (by fun_prop)
    have hm : Continuous (fun a : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => a.1.2.2) := by fun_prop
    rcases lt_or_gt_of_ne hω with hω | hω
    · apply hv.congr_of_eventuallyEq
      filter_upwards [hm.continuousAt.eventually (gt_mem_nhds hω)] with a ha
      exact ite_eq_left ha
    · apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [hm.continuousAt.eventually (lt_mem_nhds hω)] with a ha
      exact ite_eq_right (not_lt.mpr ha.le)
  have hl := distribution_ae_continuous_mapping P Q _ _ g hj hg hgc
  have huig : UniformIntegrable (fun n ω => g (Z n ω,p n)) 1 P := by
    apply uniformIntegrable_of_abs_le P (fun n ω => (Z n ω).2.1) _ hui
      (fun n => (hg.comp_aemeasurable (hj.forall_aemeasurable n)).aestronglyMeasurable)
    intro n
    apply ae_of_all
    intro ω
    simp only [g, Function.comp_apply]
    split_ifs
    · rw [abs_mul, abs_div, abs_of_pos hC]
      exact mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hC).mpr (hbw n _))
    · simp
  obtain ⟨hi,he⟩ := weak_ui_expectation_limit P Q _ _ hl huig
  have hscale (a : (ℝ × ℝ × ℝ) × (ℝ × ℝ)) :
      C*g a = barrierWeight (fun x => w (a.2,x)) b a.1 := by
    dsimp only [g, barrierWeight]
    split_ifs <;> field_simp <;> ring
  constructor
  · simpa only [Function.comp_apply, hscale] using hi.const_mul C
  · have hc := he.const_mul C
    simpa only [← integral_const_mul, Function.comp_apply, hscale] using hc

end BarrierManuscript
#print axioms BarrierManuscript.weak_varying_barrier_expectation
