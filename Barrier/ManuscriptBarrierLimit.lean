import ManuscriptWeakUI

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Strict survival at finite maturity; the limiting maximum has no atom at the barrier. -/
noncomputable def barrierWeight (w : ℝ → ℝ) (b : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  if z.2.2 < b then w z.1*z.2.1 else 0

theorem barrierWeight_continuousAt (w : ℝ → ℝ) (hw : Continuous w)
    (b : ℝ) (z : ℝ × ℝ × ℝ) (hz : z.2.2 ≠ b) :
    ContinuousAt (barrierWeight w b) z := by
  have hc : Continuous (fun z : ℝ × ℝ × ℝ => w z.1*z.2.1) := by fun_prop
  have hm : Continuous (fun z : ℝ × ℝ × ℝ => z.2.2) := by fun_prop
  rcases lt_or_gt_of_ne hz with hz | hz
  · apply hc.continuousAt.congr_of_eventuallyEq
    filter_upwards [hm.continuousAt.eventually (gt_mem_nhds hz)] with x hx
    exact ite_eq_left hx
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hm.continuousAt.eventually (lt_mem_nhds hz)] with x hx
    exact ite_eq_right (not_lt.mpr hx.le)

/-- The manuscript's barrier-weighted weak-expectation step, on possibly
different probability spaces. UI is required only for the volatility
coordinate; no mixed moment with the stock coordinate is assumed. -/
theorem weak_barrier_weighted_expectation {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : ℕ → Ω → ℝ × ℝ × ℝ) (z : Γ → ℝ × ℝ × ℝ)
    (h : TendstoInDistribution Z atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun n ω => (Z n ω).2.1) 1 P)
    (w : ℝ → ℝ) (hw : Continuous w) (hbw : ∀ x, |w x| ≤ 1)
    (b : ℝ) (hnoatom : ∀ᵐ ω ∂Q, (z ω).2.2 ≠ b) :
    Integrable (fun ω => barrierWeight w b (z ω)) Q ∧
    Tendsto (fun n => ∫ ω, barrierWeight w b (Z n ω) ∂P) atTop
      (𝓝 (∫ ω, barrierWeight w b (z ω) ∂Q)) := by
  have hm : Measurable (barrierWeight w b) := by
    unfold barrierWeight
    exact Measurable.ite (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const)
      ((hw.measurable.comp measurable_fst).mul (measurable_fst.comp measurable_snd)) measurable_const
  have hl := distribution_ae_continuous_mapping P Q Z z (barrierWeight w b) h hm
    (hnoatom.mono fun ω hω => barrierWeight_continuousAt w hw b (z ω) hω)
  apply weak_ui_expectation_limit P Q _ _ hl
  apply uniformIntegrable_of_abs_le P (fun n ω => (Z n ω).2.1) _ hui
    (fun n => (hm.comp_aemeasurable (h.forall_aemeasurable n)).aestronglyMeasurable)
  intro n
  apply ae_of_all
  intro ω
  simp only [barrierWeight, Function.comp_apply]
  split_ifs
  · rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hbw _)
  · simp

/-- The bounded-kernel form, allowing any positive uniform bound. -/
theorem weak_barrier_bounded_expectation {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : ℕ → Ω → ℝ × ℝ × ℝ) (z : Γ → ℝ × ℝ × ℝ)
    (h : TendstoInDistribution Z atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun n ω => (Z n ω).2.1) 1 P)
    (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ) (hC : 0 < C)
    (hbw : ∀ x, |w x| ≤ C)
    (b : ℝ) (hnoatom : ∀ᵐ ω ∂Q, (z ω).2.2 ≠ b) :
    Integrable (fun ω => barrierWeight w b (z ω)) Q ∧
    Tendsto (fun n => ∫ ω, barrierWeight w b (Z n ω) ∂P) atTop
      (𝓝 (∫ ω, barrierWeight w b (z ω) ∂Q)) := by
  obtain ⟨hi,hl⟩ := weak_barrier_weighted_expectation P Q Z z h hui
    (fun x => w x/C) (hw.div_const C) (fun x => by
      rw [abs_div, abs_of_pos hC]
      exact (div_le_one hC).mpr (hbw x)) b hnoatom
  have he (x : ℝ × ℝ × ℝ) :
      C*barrierWeight (fun y => w y/C) b x = barrierWeight w b x := by
    unfold barrierWeight
    split_ifs <;> field_simp <;> ring
  constructor
  · simpa only [he] using hi.const_mul C
  · have hmul := hl.const_mul C
    simpa only [← integral_const_mul, he] using hmul


theorem barrierWeight_eq_closed_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ × ℝ × ℝ) (w : ℝ → ℝ) (b : ℝ)
    (hb : ∀ᵐ ω ∂P, (Z ω).2.2 ≠ b) :
    (fun ω => barrierWeight w b (Z ω)) =ᵐ[P]
      (fun ω => if (Z ω).2.2 ≤ b then w (Z ω).1*(Z ω).2.1 else 0) := by
  filter_upwards [hb] with ω hω
  have he : (Z ω).2.2 < b ↔ (Z ω).2.2 ≤ b := ⟨le_of_lt,fun h => lt_of_le_of_ne h hω⟩
  simp only [barrierWeight,he]

end BarrierManuscript
#print axioms BarrierManuscript.barrierWeight_continuousAt
#print axioms BarrierManuscript.weak_barrier_weighted_expectation

#print axioms BarrierManuscript.weak_barrier_bounded_expectation

#print axioms BarrierManuscript.barrierWeight_eq_closed_ae
