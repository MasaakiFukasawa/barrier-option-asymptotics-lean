import ManuscriptSmoothPrice
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem put_strike_derivative (k x w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun a => put a x w) (normalCDF ((k-x)/w)) k := by
  have hd := ((hasDerivAt_id k).sub_const x).div_const w
  have h := (((hasDerivAt_id k).sub_const x).mul ((normalCDF_hasDerivAt _).comp k hd)).add
    (((phi_derivative _).comp k hd).const_mul w)
  convert h using 1
  · rfl
  · dsimp [phi]
    field_simp
    ring

theorem killed_put_strike_derivative (b k x w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun a => killedPut b a x w)
      (normalCDF ((k-x)/w)-normalCDF ((k-(2*b-x))/w)) k :=
  (put_strike_derivative k x w hw).sub (put_strike_derivative k (2*b-x) w hw)

/-- Differentiation of the actual expected put payoff at a non-atom.
The derivative is a probability, with domination justified by the unit
Lipschitz constant of the payoff as a function of strike. -/
theorem expected_put_derivative {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hm : Measurable X) (hi : Integrable X P) (k : ℝ)
    (hk : ∀ᵐ ω ∂P, X ω ≠ k) :
    HasDerivAt (fun a => ∫ ω, max (a-X ω) 0 ∂P) (P.real {ω | X ω < k}) k := by
  let D := fun ω => if X ω < k then (1:ℝ) else 0
  have hmD : Measurable D := measurable_const.ite (measurableSet_lt hm measurable_const) measurable_const
  have hl ω : LipschitzWith 1 (fun a : ℝ => max (a-X ω) 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (a-X ω) (b-X ω) 0
  have hd : ∀ᵐ ω ∂P, HasDerivAt (fun a => max (a-X ω) 0) (D ω) k := by
    filter_upwards [hk] with ω hω
    rcases lt_or_gt_of_ne hω with hω | hω
    · rw [show D ω = 1 from ite_eq_left hω]
      apply ((hasDerivAt_id k).sub_const (X ω)).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds hω] with a ha
      exact max_eq_left (sub_nonneg.mpr ha.le)
    · rw [show D ω = 0 from ite_eq_right (not_lt.mpr hω.le)]
      apply (hasDerivAt_const k (0:ℝ)).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds hω] with a ha
      exact max_eq_right (sub_nonpos.mpr ha.le)
  have h := (hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) (F := fun (a : ℝ) (ω : Ω) => max (a-X ω) 0) (x₀ := k) (F' := D) (bound := fun _ => (1:ℝ))
    (s := univ) (Filter.univ_mem)
    (Filter.Eventually.of_forall fun a => ((measurable_const.sub hm).max measurable_const).aestronglyMeasurable)
    (((integrable_const k).sub hi).pos_part) hmD.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa using hl ω)
    (integrable_const 1) hd).2
  have he : (∫ ω, D ω ∂P) = P.real {ω | X ω < k} := by
    change (∫ ω, {ω | X ω < k}.indicator (fun _ => (1:ℝ)) ω ∂P) = _
    rw [integral_indicator_const _ (measurableSet_lt hm measurable_const)]
    simp
  rwa [he] at h

/-- A killed-put formula determines its sub-barrier distribution function. -/
theorem killed_put_identifies_cdf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hm : Measurable X) (hi : Integrable X P) (b k : ℝ) (hk : k < b)
    (hnoatom : ∀ᵐ ω ∂P, X ω ≠ k)
    (hput : ∀ a ≤ b, (∫ ω, max (a-X ω) 0 ∂P) = killedPut b a 0 1) :
    P.real {ω | X ω < k} = normalCDF k-normalCDF (k-2*b) := by
  have h := expected_put_derivative P X hm hi k hnoatom
  have he : (fun a => ∫ ω, max (a-X ω) 0 ∂P) =ᶠ[𝓝 k] (fun a => killedPut b a 0 1) := by
    filter_upwards [gt_mem_nhds hk] with a ha
    exact hput a ha.le
  have hh := h.congr_of_eventuallyEq he.symm
  have hd := killed_put_strike_derivative b k 0 1 (by norm_num)
  simpa only [sub_zero,div_one] using hh.unique hd

end BarrierManuscript
#print axioms BarrierManuscript.put_strike_derivative
#print axioms BarrierManuscript.killed_put_strike_derivative
#print axioms BarrierManuscript.expected_put_derivative
#print axioms BarrierManuscript.killed_put_identifies_cdf
