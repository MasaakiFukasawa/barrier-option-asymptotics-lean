import ManuscriptUniformIntegrability
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

noncomputable def signedTruncation (R : ℝ) (x : ℝ) : ℝ := max (-R) (min R x)

theorem signedTruncation_bound (R x : ℝ) (hR : 0 ≤ R) :
    |signedTruncation R x| ≤ R := by
  unfold signedTruncation
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem signedTruncation_error (R x : ℝ) (hR : 0 ≤ R) :
    |x-signedTruncation R x| ≤ if R ≤ |x| then |x| else 0 := by
  unfold signedTruncation
  rcases le_total x (-R) with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx, abs_of_nonpos (by linarith)]
    have ha : |x| = -x := abs_of_nonpos (by linarith)
    rw [ha, ite_eq_left (by linarith)]
    linarith
  · rcases le_total x R with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx, sub_self, abs_zero]
      split_ifs <;> positivity
    · rw [min_eq_left hx', max_eq_right (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith : 0 ≤ x), ite_eq_left hx']
      linarith

noncomputable def boundedSignedTruncation (R : ℝ) (hR : 0 ≤ R) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨signedTruncation R, by unfold signedTruncation; fun_prop⟩
    (2*R) (fun x y => by
      change |signedTruncation R x-signedTruncation R y| ≤ 2*R
      have h := abs_sub (signedTruncation R x) (signedTruncation R y)
      linarith [signedTruncation_bound R x hR, signedTruncation_bound R y hR])

theorem integral_abs_le_of_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : Integrable f P) (C : ℝ) (hC : 0 ≤ C)
    (hb : eLpNorm f 1 P ≤ ENNReal.ofReal C) : (∫ ω, |f ω| ∂P) ≤ C := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hf] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hb

/-- UI supplies a common signed truncation radius with uniformly small L1
error. The radius is obtained from the actual tail criterion for UI. -/
theorem ui_signed_truncation {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ι → Ω → ℝ) (hui : UniformIntegrable Y 1 P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ i,
      Integrable (fun ω => Y i ω-signedTruncation R (Y i ω)) P ∧
      (∫ ω, |Y i ω-signedTruncation R (Y i ω)| ∂P) ≤ ε := by
  obtain ⟨R,hR⟩ := hui.spec (by norm_num : (1:ℝ≥0∞) ≠ 0)
    (by norm_num : (1:ℝ≥0∞) ≠ ∞) (ENNReal.ofReal_pos.mpr hε)
  refine ⟨R,R.coe_nonneg, fun i => ?_⟩
  let T := {ω | R ≤ ‖Y i ω‖₊}.indicator (Y i)
  have hm : AEStronglyMeasurable (fun ω => Y i ω-signedTruncation R (Y i ω)) P := by
    apply (hui.aestronglyMeasurable i).sub
    exact (show Continuous (signedTruncation (R:ℝ)) by unfold signedTruncation; fun_prop).comp_aestronglyMeasurable
      (hui.aestronglyMeasurable i)
  have he : ∀ ω, ‖Y i ω-signedTruncation R (Y i ω)‖ ≤ ‖T ω‖ := by
    intro ω
    have hh := signedTruncation_error R (Y i ω) R.coe_nonneg
    have hc : (R ≤ ‖Y i ω‖₊) ↔ ((R:ℝ) ≤ |Y i ω|) := by
      exact_mod_cast (Iff.rfl : (R:ℝ) ≤ ‖Y i ω‖ ↔ (R:ℝ) ≤ |Y i ω|)
    by_cases hω : R ≤ ‖Y i ω‖₊
    · simpa [T, Set.indicator, hω, Real.norm_eq_abs, hc.mp hω] using hh
    · simpa [T, Set.indicator, hω, Real.norm_eq_abs, (not_congr hc).mp hω] using hh
  have hn : eLpNorm (fun ω => Y i ω-signedTruncation R (Y i ω)) 1 P ≤ ENNReal.ofReal ε :=
    (eLpNorm_mono hm he).trans (hR i)
  have hi : Integrable (fun ω => Y i ω-signedTruncation R (Y i ω)) P :=
    memLp_one_iff_integrable.mp (hn.trans_lt ENNReal.ofReal_lt_top)
  exact ⟨hi, integral_abs_le_of_eLpNorm_le P _ hi ε hε.le hn⟩

end BarrierManuscript
#print axioms BarrierManuscript.ui_signed_truncation
