import ManuscriptSquareMeanConvergence

open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem inMeasure_div_positive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (c : ℝ) (hc : 0 < c)
    (h : TendstoInMeasure P X atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => X n ω/c) atTop (fun _ => 0) := by
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have hh := tendstoInMeasure_iff_norm.mp h (ε*c) (mul_pos hε hc)
  simpa only [sub_zero,norm_div,Real.norm_eq_abs,abs_of_pos hc,le_div_iff₀ hc] using hh

theorem inMeasure_of_reverse_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (h : TendstoInMeasure P (fun n ω => Z ω-X n ω) atTop (fun _ => 0)) :
    TendstoInMeasure P X atTop Z := by
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have hh := tendstoInMeasure_iff_norm.mp h ε hε
  simpa only [sub_zero,norm_sub_rev] using hh

end BarrierManuscript
#print axioms BarrierManuscript.inMeasure_div_positive
#print axioms BarrierManuscript.inMeasure_of_reverse_error
