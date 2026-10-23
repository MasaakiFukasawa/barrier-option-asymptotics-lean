import ManuscriptTerminal
import ManuscriptSmoothPrice
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

theorem put_growth_bound (k x w : ℝ) : |put k x w| ≤ |k-x|+|w| *normalizer := by
  have hPhi : |normalCDF ((k-x)/w)| ≤ 1 := by
    rw [abs_of_nonneg (show 0 ≤ normalCDF ((k-x)/w) from measureReal_nonneg)]
    exact measureReal_le_one
  have hp : |phi ((k-x)/w)| ≤ normalizer := by
    rw [abs_of_nonneg (phi_nonneg _)]
    exact phi_le _
  unfold put
  have h := abs_add_le ((k-x)*normalCDF ((k-x)/w)) (w*phi ((k-x)/w))
  rw [abs_mul,abs_mul] at h
  nlinarith [mul_le_mul_of_nonneg_left hPhi (abs_nonneg (k-x)),
    mul_le_mul_of_nonneg_left hp (abs_nonneg w)]

theorem killedPut_growth_bound (b k x w : ℝ) :
    |killedPut b k x w| ≤ 2*|k|+2*|b|+2*|x|+2*|w| *normalizer := by
  have h := abs_sub (put k x w) (put k (2*b-x) w)
  have h1 := put_growth_bound k x w
  have h2 := put_growth_bound k (2*b-x) w
  have h3 := abs_sub k x
  have h4 := abs_sub k (2*b-x)
  have h5 := abs_sub (2*b) x
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] at h5
  change |put k x w-put k (2*b-x) w| ≤ _
  linarith

/-- Passage to maturity in expectation for stopped prices. An integrable
path bound may be deterministic (the positive stock stopped at an upper
barrier) or random (for the Brownian reflection calculation). -/
theorem killed_terminal_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (x : Ω → ℝ) (w : ℕ → ℝ)
    (b k W : ℝ) (hk : k ≤ b)
    (hm : ∀ n, AEStronglyMeasurable (X n) P)
    (hx : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (x ω)))
    (hb : ∀ᵐ ω ∂P, x ω ≤ b) (hw : Tendsto w atTop (𝓝[>] 0))
    (hW : ∀ n, |w n| ≤ W)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ᵐ ω ∂P, ∀ n, |X n ω| ≤ D ω) :
    Tendsto (fun n => ∫ ω, killedPut b k (X n ω) (w n) ∂P) atTop
      (𝓝 (∫ ω, max (k-x ω) 0 ∂P)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun ω => 2*|k|+2*|b|+2*D ω+2*W*normalizer)
  · intro n
    have hp (a : Ω → ℝ) (ha : AEStronglyMeasurable a P) :
        AEStronglyMeasurable (fun ω => put k (a ω) (w n)) P := by
      unfold put
      have hd : AEStronglyMeasurable (fun ω => (k-a ω)/(w n)) P :=
        (aestronglyMeasurable_const.sub ha).mul_const (w n)⁻¹
      exact ((aestronglyMeasurable_const.sub ha).mul
        (normalCDF_contDiff.continuous.comp_aestronglyMeasurable hd)).add
        ((phi_contDiff.continuous.comp_aestronglyMeasurable hd).const_mul _)
    exact (hp _ (hm n)).sub (hp _ (aestronglyMeasurable_const.sub (hm n)))
  · exact ((integrable_const _).add (hD.const_mul 2)).add (integrable_const _)
  · intro n
    filter_upwards [hbound] with ω hω
    have h := killedPut_growth_bound b k (X n ω) (w n)
    have hw' := mul_le_mul_of_nonneg_right (hW n) normalizer_nonneg
    rw [Real.norm_eq_abs]
    linarith [hω n]
  · filter_upwards [hx,hb] with ω hω hbar
    exact killedPut_terminal b k (x ω) hk hbar _ w hω hw

end BarrierManuscript
#print axioms BarrierManuscript.put_growth_bound
#print axioms BarrierManuscript.killedPut_growth_bound
#print axioms BarrierManuscript.killed_terminal_expectation
