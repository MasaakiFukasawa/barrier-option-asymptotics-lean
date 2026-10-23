import ManuscriptJointPathTransfer

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace BarrierManuscript

theorem inMeasure_zero_add {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure P f atTop (fun _ => 0))
    (hg : TendstoInMeasure P g atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => f n ω + g n ω) atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have h := (tendstoInMeasure_iff_norm.mp hf (ε/2) (by positivity)).add
    (tendstoInMeasure_iff_norm.mp hg (ε/2) (by positivity))
  simp only [sub_zero, add_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro n
  apply le_trans (measure_mono (t := {ω | ε/2 ≤ ‖f n ω‖} ∪ {ω | ε/2 ≤ ‖g n ω‖}) ?_)
    (measure_union_le _ _)
  intro ω hω
  simp only [mem_setOf_eq, sub_zero] at hω
  change ε/2 ≤ ‖f n ω‖ ∨ ε/2 ≤ ‖g n ω‖
  by_contra hn
  push_neg at hn
  have := norm_add_le (f n ω) (g n ω)
  linarith

theorem inMeasure_zero_finset_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (f : ι → ℕ → Ω → ℝ)
    (hf : ∀ i ∈ s, TendstoInMeasure P (f i) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun _ => 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply tendstoInMeasure_iff_norm.mpr
    intro ε hε
    simpa [not_le.mpr hε] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using inMeasure_zero_add P
      (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem inMeasure_zero_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {f : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure P f atTop (fun _ => 0)) (c : ℝ) :
    TendstoInMeasure P (fun n ω => c * f n ω) atTop (fun _ => 0) := by
  by_cases hc : c = 0
  · subst c
    apply tendstoInMeasure_iff_norm.mpr
    intro ε hε
    simpa [not_le.mpr hε] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have h := tendstoInMeasure_iff_norm.mp hf (ε/|c|) (div_pos hε (abs_pos.mpr hc))
  simpa only [sub_zero, Real.norm_eq_abs, abs_mul,
    div_le_iff₀ (abs_pos.mpr hc), mul_comm (|f _ _|) (|c|)] using h

end BarrierManuscript
#print axioms BarrierManuscript.inMeasure_zero_add
#print axioms BarrierManuscript.inMeasure_zero_finset_sum
#print axioms BarrierManuscript.inMeasure_zero_const_mul
