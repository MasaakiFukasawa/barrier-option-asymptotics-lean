import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Domination transfers genuine probabilistic uniform integrability, including
its uniform L1 bound, rather than just integrability of each member. -/
theorem uniformIntegrable_of_abs_le {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y Z : ι → Ω → ℝ) (hY : UniformIntegrable Y 1 P)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, |Z i ω| ≤ |Y i ω|) : UniformIntegrable Z 1 P := by
  have he (i) : ∀ᵐ ω ∂P, ‖Z i ω‖ₑ ≤ ‖Y i ω‖ₑ := by
    filter_upwards [hb i] with ω hω
    simpa only [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hω
  refine ⟨hY.1.ae_mono hZ he, ?_⟩
  obtain ⟨C,hC⟩ := hY.2
  exact ⟨C, fun i => (eLpNorm_mono_enorm_ae (hZ i) (he i)).trans (hC i)⟩

theorem uniformIntegrable_unit_weight {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y W : ι → Ω → ℝ) (hY : UniformIntegrable Y 1 P)
    (hW : ∀ i, AEStronglyMeasurable (W i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, |W i ω| ≤ 1) :
    UniformIntegrable (fun i ω => W i ω*Y i ω) 1 P := by
  apply uniformIntegrable_of_abs_le P Y _ hY
    (fun i => (hW i).mul (hY.aestronglyMeasurable i))
  intro i
  filter_upwards [hb i] with ω hω
  change |W i ω*Y i ω| ≤ |Y i ω|
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hω

/-- Vitali gives convergence of expectations and integrability of the limit;
the latter is derived, not assumed. -/
theorem ui_expectation_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Z : ℕ → Ω → ℝ) (z : Ω → ℝ)
    (hui : UniformIntegrable Z 1 P)
    (hz : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (z ω))) :
    Integrable z P ∧ Tendsto (fun n => ∫ ω, Z n ω ∂P) atTop (𝓝 (∫ ω, z ω ∂P)) := by
  have hl := hui.memLp_of_ae_tendsto hz
  have hconv := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num : (1:ℝ≥0∞) ≠ ∞) hui.aestronglyMeasurable hl hui.1 hz
  refine ⟨memLp_one_iff_integrable.mp hl, ?_⟩
  exact tendsto_integral_of_L1' z
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hui.memLp n))) hconv

theorem barrier_indicator_eventually {m : ℕ → ℝ} {z b : ℝ}
    (hm : Tendsto m atTop (𝓝 z)) (hb : z ≠ b) :
    ∀ᶠ n in atTop, (m n ≤ b ↔ z ≤ b) := by
  rcases lt_or_gt_of_ne hb with h | h
  · filter_upwards [hm.eventually (gt_mem_nhds h)] with n hn
    simp only [hn.le, h.le]
  · filter_upwards [hm.eventually (lt_mem_nhds h)] with n hn
    simp only [not_le.mpr hn, not_le.mpr h]

/-- The barrier-weighted expectation step on a common a.s.-convergent
realization. Convergence in law alone is NOT substituted for the a.s.
hypotheses: constructing/transferring such a realization is separate work. -/
theorem ui_barrier_expectation_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (Y W M : ℕ → Ω → ℝ) (y w m : Ω → ℝ) (b : ℝ)
    (hui : UniformIntegrable Y 1 P)
    (hW : ∀ n, AEStronglyMeasurable (W n) P)
    (hM : ∀ n, Measurable (M n))
    (hb : ∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ 1)
    (hYlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (y ω)))
    (hWlim : ∀ᵐ ω ∂P, Tendsto (fun n => W n ω) atTop (𝓝 (w ω)))
    (hMlim : ∀ᵐ ω ∂P, Tendsto (fun n => M n ω) atTop (𝓝 (m ω)))
    (hnoatom : ∀ᵐ ω ∂P, m ω ≠ b) :
    Integrable (fun ω => if m ω ≤ b then w ω*y ω else 0) P ∧
    Tendsto (fun n => ∫ ω, if M n ω ≤ b then W n ω*Y n ω else 0 ∂P)
      atTop (𝓝 (∫ ω, if m ω ≤ b then w ω*y ω else 0 ∂P)) := by
  let Z := fun n ω => if M n ω ≤ b then W n ω*Y n ω else 0
  have hZmeas (n) : AEStronglyMeasurable (Z n) P := by
    exact ((hW n).mul (hui.aestronglyMeasurable n)).indicator
      (hM n measurableSet_Iic)
  have hZui : UniformIntegrable Z 1 P := by
    apply uniformIntegrable_of_abs_le P (fun n ω => W n ω*Y n ω) Z
      (uniformIntegrable_unit_weight P Y W hui hW hb) hZmeas
    intro n; apply ae_of_all; intro ω
    dsimp [Z]; split_ifs
    · exact le_rfl
    · simpa only [abs_zero] using (abs_nonneg (W n ω*Y n ω))
  apply ui_expectation_limit P Z _ hZui
  filter_upwards [hYlim, hWlim, hMlim, hnoatom] with ω hy hw hm hn
  have he := barrier_indicator_eventually hm hn
  by_cases h : m ω ≤ b
  · rw [ite_eq_left h]
    apply (hw.mul hy).congr'
    filter_upwards [he] with n hne
    simp only [Z, ite_eq_left (hne.mpr h)]
  · rw [ite_eq_right h]
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hne
    simp only [Z, ite_eq_right (fun hh => h (hne.mp hh))]

/-- Arbitrarily bounded weights are allowed: no higher moment of Y is used. -/
theorem ui_bounded_barrier_expectation_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (Y W M : ℕ → Ω → ℝ) (y w m : Ω → ℝ) (b C : ℝ) (hC : 0 < C)
    (hui : UniformIntegrable Y 1 P)
    (hW : ∀ n, AEStronglyMeasurable (W n) P)
    (hM : ∀ n, Measurable (M n))
    (hb : ∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ C)
    (hYlim : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (y ω)))
    (hWlim : ∀ᵐ ω ∂P, Tendsto (fun n => W n ω) atTop (𝓝 (w ω)))
    (hMlim : ∀ᵐ ω ∂P, Tendsto (fun n => M n ω) atTop (𝓝 (m ω)))
    (hnoatom : ∀ᵐ ω ∂P, m ω ≠ b) :
    Integrable (fun ω => if m ω ≤ b then w ω*y ω else 0) P ∧
    Tendsto (fun n => ∫ ω, if M n ω ≤ b then W n ω*Y n ω else 0 ∂P)
      atTop (𝓝 (∫ ω, if m ω ≤ b then w ω*y ω else 0 ∂P)) := by
  have hb' (n) : ∀ᵐ ω ∂P, |W n ω/C| ≤ 1 := by
    filter_upwards [hb n] with ω hω
    rw [abs_div, abs_of_pos hC]
    exact (div_le_one hC).mpr hω
  have hl' : ∀ᵐ ω ∂P, Tendsto (fun n => W n ω/C) atTop (𝓝 (w ω/C)) :=
    hWlim.mono (fun _ h => h.div_const C)
  obtain ⟨hi,hl⟩ := ui_barrier_expectation_limit P Y (fun n ω => W n ω/C) M
    y (fun ω => w ω/C) m b hui (fun n => by simpa only [div_eq_mul_inv] using (hW n).mul_const C⁻¹) hM hb'
    hYlim hl' hMlim hnoatom
  have he (a d z : ℝ) : C*(if z ≤ b then (a/C)*d else 0) =
      (if z ≤ b then a*d else 0) := by
    split_ifs <;> field_simp
    ring
  constructor
  · have h := hi.const_mul C
    simpa only [he] using h
  · have h := hl.const_mul C
    simp_rw [← integral_const_mul, he] at h
    exact h

/-- Uniform integrability transfers to copies on a different probability
space. It is not an extra assumption on a proposed coupling. -/
theorem uniformIntegrable_transfer {Ω Γ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsFiniteMeasure Q]
    (Y : ι → Ω → ℝ) (Z : ι → Γ → ℝ)
    (hui : UniformIntegrable Y 1 P) (hlaw : ∀ i, IdentDistrib (Y i) (Z i) P Q) :
    UniformIntegrable Z 1 Q := by
  apply uniformIntegrable_of (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num : (1:ℝ≥0∞) ≠ ∞)
    (fun i => (hlaw i).aemeasurable_snd.aestronglyMeasurable)
  intro ε hε
  obtain ⟨C,hC⟩ := hui.spec (by norm_num) (by norm_num) hε
  refine ⟨C, fun i => ?_⟩
  let f : ℝ → ℝ := {z | C ≤ ‖z‖₊}.indicator id
  have hm : Measurable f := measurable_id.indicator
    (measurableSet_le measurable_const measurable_nnnorm)
  have he : IdentDistrib ({ω | C ≤ ‖Y i ω‖₊}.indicator (Y i))
      ({ω | C ≤ ‖Z i ω‖₊}.indicator (Z i)) P Q := by
    change IdentDistrib (fun ω => if C ≤ ‖Y i ω‖₊ then Y i ω else 0)
      (fun ω => if C ≤ ‖Z i ω‖₊ then Z i ω else 0) P Q
    simpa only [f, Function.comp_def, Set.indicator, mem_ofPred_eq, id_eq] using (hlaw i).comp hm
  rw [← he.eLpNorm_eq 1]
  exact hC i

end BarrierManuscript

#print axioms BarrierManuscript.uniformIntegrable_of_abs_le
#print axioms BarrierManuscript.uniformIntegrable_unit_weight
#print axioms BarrierManuscript.ui_expectation_limit
#print axioms BarrierManuscript.barrier_indicator_eventually
#print axioms BarrierManuscript.ui_barrier_expectation_limit
#print axioms BarrierManuscript.ui_bounded_barrier_expectation_limit
#print axioms BarrierManuscript.uniformIntegrable_transfer
