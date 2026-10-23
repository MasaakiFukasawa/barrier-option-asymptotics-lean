import ManuscriptBachelier
import Chapter3SmoothPositivePower
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
open Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

theorem phi_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) phi := by
  unfold phi gaussianPDFReal
  fun_prop

theorem normalCDF_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) normalCDF := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (normalCDF_hasDerivAt x).differentiableAt, ?_⟩
  have he : deriv normalCDF = phi := funext fun x => (normalCDF_hasDerivAt x).deriv
  rw [he]
  exact phi_contDiff

/-- A globally smooth price which agrees with the actual killed price when
the remaining variance is at least δ. Only the variance coordinate is
modified; no smoothness of the deterministic variance curve is presumed. -/
noncomputable def smoothKilledPrice (δ b k : ℝ) (z : Fin 2 → ℝ) : ℝ :=
  killedPut b k (z 0) (Real.sqrt (smoothPositive (δ/4) (z 1)))

theorem smoothKilledPrice_contDiffN (δ b k : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ContDiff ℝ n (smoothKilledPrice δ b k) := by
  have hp : ContDiff ℝ n (fun z : Fin 2 → ℝ => smoothPositive (δ/4) (z 1)) :=
    (smoothPositive_contDiff (δ/4) n).comp (by fun_prop)
  have hw : ContDiff ℝ n (fun z : Fin 2 → ℝ => Real.sqrt (smoothPositive (δ/4) (z 1))) :=
    hp.sqrt (fun z => (smoothPositive_pos (by positivity) (z 1)).ne')
  have hwn (z : Fin 2 → ℝ) : Real.sqrt (smoothPositive (δ/4) (z 1)) ≠ 0 :=
    (Real.sqrt_pos.mpr (smoothPositive_pos (by positivity) (z 1))).ne'
  have hput (x : (Fin 2 → ℝ) → ℝ) (hx : ContDiff ℝ n x) :
      ContDiff ℝ n (fun z => put k (x z) (Real.sqrt (smoothPositive (δ/4) (z 1)))) := by
    have hd : ContDiff ℝ n (fun z => (k-x z)/Real.sqrt (smoothPositive (δ/4) (z 1))) :=
      (contDiff_const.sub hx).div hw hwn
    exact (contDiff_const.sub hx).mul ((normalCDF_contDiff.of_le (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).comp hd) |>.add
      (hw.mul ((phi_contDiff.of_le (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞))).comp hd))
  exact (hput (fun z => z 0) (by fun_prop)).sub
    (hput (fun z => 2*b-z 0) (by fun_prop))

theorem smoothKilledPrice_contDiff (δ b k : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ 2 (smoothKilledPrice δ b k) := smoothKilledPrice_contDiffN δ b k hδ 2

theorem smoothKilledPrice_eq (δ b k : ℝ) (hδ : 0 < δ) (z : Fin 2 → ℝ)
    (hz : δ ≤ z 1) : smoothKilledPrice δ b k z = killedPut b k (z 0) (Real.sqrt (z 1)) := by
  unfold smoothKilledPrice
  rw [smoothPositive_eq (by positivity : 0 < δ/4) (by linarith : 2*(δ/4) ≤ z 1)]

/-- Agreement holds on a neighborhood, permitting transfer of first and
second derivatives when applying the global Ito theorem. -/
theorem smoothKilledPrice_eventuallyEq (δ b k : ℝ) (hδ : 0 < δ) (z : Fin 2 → ℝ)
    (hz : δ ≤ z 1) :
    smoothKilledPrice δ b k =ᶠ[𝓝 z] (fun x => killedPut b k (x 0) (Real.sqrt (x 1))) := by
  have hc : Continuous (fun z : Fin 2 → ℝ => z 1) := by fun_prop
  filter_upwards [hc.continuousAt.eventually (lt_mem_nhds (show δ/2 < z 1 by linarith))] with x hx
  unfold smoothKilledPrice
  rw [smoothPositive_eq (by positivity : 0 < δ/4) (by linarith : 2*(δ/4) ≤ x 1)]

end BarrierManuscript
#print axioms BarrierManuscript.phi_contDiff
#print axioms BarrierManuscript.normalCDF_contDiff
#print axioms BarrierManuscript.smoothKilledPrice_contDiff
#print axioms BarrierManuscript.smoothKilledPrice_eq
#print axioms BarrierManuscript.smoothKilledPrice_eventuallyEq
