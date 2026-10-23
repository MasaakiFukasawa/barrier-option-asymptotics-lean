import ManuscriptBrownianMaximum

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem upper_tail_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hm : Measurable X)
    (b : ℝ) (k : ℕ → ℝ) (hk : ∀ n, b < k n) (hlim : Tendsto k atTop (𝓝 b)) :
    Tendsto (fun n => P.real {ω | X ω < k n}) atTop (𝓝 (P.real {ω | X ω ≤ b})) := by
  let f := fun n ω => if X ω < k n then (1:ℝ) else 0
  let g := fun ω => if X ω ≤ b then (1:ℝ) else 0
  have hf n : AEStronglyMeasurable (f n) P :=
    (measurable_const.ite (measurableSet_lt hm measurable_const) measurable_const).aestronglyMeasurable
  have hbnd n : ∀ᵐ ω ∂P, ‖f n ω‖ ≤ (1:ℝ) := ae_of_all _ fun ω => by simp [f]; split_ifs <;> norm_num
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    apply ae_of_all
    intro ω
    by_cases h : X ω ≤ b
    · have hall n : X ω < k n := h.trans_lt (hk n)
      simp only [f,g,ite_eq_left h,ite_eq_left (hall _)]
      exact tendsto_const_nhds
    · apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually (gt_mem_nhds (lt_of_not_ge h))] with n hn
      simp [f,g,h,not_lt.mpr hn.le]
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ)) hf (integrable_const 1) hbnd hconv
  have hformula (a : ℝ) : (∫ ω, if X ω < a then (1:ℝ) else 0 ∂P) = P.real {ω | X ω < a} := by
    change (∫ ω, {ω | X ω < a}.indicator (fun _ => (1:ℝ)) ω ∂P) = _
    rw [integral_indicator_const _ (measurableSet_lt hm measurable_const)]
    simp
  have hformula' : (∫ ω, g ω ∂P) = P.real {ω | X ω ≤ b} := by
    change (∫ ω, {ω | X ω ≤ b}.indicator (fun _ => (1:ℝ)) ω ∂P) = _
    rw [integral_indicator_const _ (measurableSet_le hm measurable_const)]
    simp
  simpa only [f,hformula,hformula'] using hi

theorem noatom_of_equal_tails {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hm : Measurable X) (b : ℝ)
    (he : P.real {ω | X ω ≤ b} = P.real {ω | X ω < b}) :
    ∀ᵐ ω ∂P, X ω ≠ b := by
  have hset : {ω | X ω = b} = {ω | X ω ≤ b} \ {ω | X ω < b} := by
    ext ω
    simp only [Set.mem_sdiff,mem_ofPred_eq,not_lt]
    exact le_antisymm_iff
  rw [ae_iff]
  simp only [not_not]
  apply (measureReal_eq_zero_iff).mp
  rw [hset,measureReal_sdiff (show {ω | X ω < b} ⊆ {ω | X ω ≤ b} from fun ω (h : X ω < b) => show X ω ≤ b from h.le) (measurableSet_lt hm measurable_const),he,sub_self]

/-- The no-atom property required by the discontinuous barrier indicator in
the main weak-limit argument, derived from the Brownian maximum law. -/
theorem brownian_maximum_noatom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (hb : 0 < b) : ∀ᵐ ω ∂P, brownianMaximum B ω ≠ b := by
  obtain ⟨k,_,hk,hklim⟩ := exists_seq_strictAnti_tendsto b
  have h₁ := upper_tail_limit P _ (brownianMaximum_measurable P B) b k hk hklim
  have h₂ := ((normalCDF_contDiff.continuous.tendsto b |>.comp hklim).const_mul 2).sub_const 1
  have he n := brownian_maximum_cdf P B (k n) (hb.trans (hk n))
  have h₂' : Tendsto (fun n => P.real {ω | brownianMaximum B ω < k n}) atTop
      (𝓝 (2*normalCDF b-1)) := by simpa only [he,Function.comp_def] using h₂
  apply noatom_of_equal_tails P _ (brownianMaximum_measurable P B) b
  rw [tendsto_nhds_unique h₁ h₂',brownian_maximum_cdf P B b hb]

end BarrierManuscript
#print axioms BarrierManuscript.upper_tail_limit
#print axioms BarrierManuscript.noatom_of_equal_tails
#print axioms BarrierManuscript.brownian_maximum_noatom
