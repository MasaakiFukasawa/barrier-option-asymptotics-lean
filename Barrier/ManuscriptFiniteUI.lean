import ManuscriptSecondMomentUI

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem ui_add {Ω κ : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : κ → Ω → ℝ} (hf : UniformIntegrable f 1 P) (hg : UniformIntegrable g 1 P) :
    UniformIntegrable (fun t ω => f t ω+g t ω) 1 P := by
  refine ⟨hf.1.add hg.1 le_rfl, ?_⟩
  obtain ⟨C,hC⟩ := hf.2
  obtain ⟨D,hD⟩ := hg.2
  refine ⟨C+D,fun t => ?_⟩
  exact (eLpNorm_add_le (f := f t) (g := g t) le_rfl).trans (by simpa using add_le_add (hC t) (hD t))

theorem ui_finset_sum {Ω ι κ : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ι) (f : ι → κ → Ω → ℝ)
    (hf : ∀ i ∈ s,UniformIntegrable (f i) 1 P) :
    UniformIntegrable (fun t ω => ∑ i ∈ s,f i t ω) 1 P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert (uniformIntegrable_const (ι := κ) le_rfl (by norm_num : (1:ℝ≥0∞)≠⊤)
      (MemLp.zero : MemLp (fun _ : Ω => (0:ℝ)) 1 P)) using 1
    funext t ω
    simp
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using ui_add P
      (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem ui_const_mul {Ω κ : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f : κ → Ω → ℝ} (hf : UniformIntegrable f 1 P) (c : ℝ) :
    UniformIntegrable (fun t ω => c*f t ω) 1 P := by
  obtain ⟨n,hn⟩ := exists_nat_gt |c|
  have hu := ui_finset_sum P (Finset.range n) (fun _ => f) (fun _ _ => hf)
  apply uniformIntegrable_of_abs_le P _ _ hu
    (fun t => (hf.aestronglyMeasurable t).const_mul c)
  intro t
  filter_upwards with ω
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  exact mul_le_mul_of_nonneg_right hn.le (abs_nonneg _)

theorem ui_of_uniform_bound {Ω κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : κ → Ω → ℝ)
    (hm : ∀ t,Measurable (f t)) (C : ℝ)
    (hb : ∀ t ω,|f t ω|≤C) : UniformIntegrable f 1 P := by
  apply uniformIntegrable_of_abs_le P (fun _ _ => C) f
    (uniformIntegrable_const le_rfl (by norm_num) (memLp_const C))
    (fun t => (hm t).aestronglyMeasurable)
  exact fun t => ae_of_all _ fun ω => (hb t ω).trans (le_abs_self C)

end BarrierManuscript
#print axioms BarrierManuscript.ui_add
#print axioms BarrierManuscript.ui_finset_sum
#print axioms BarrierManuscript.ui_const_mul
#print axioms BarrierManuscript.ui_of_uniform_bound
