import ManuscriptGaussianBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def bsPut (l w : ℝ) : ℝ :=
  Real.exp l*normalCDF (l/w+w/2)-normalCDF (l/w-w/2)

theorem phi_exponential_tilt (l w : ℝ) (hw : w ≠ 0) :
    Real.exp l*phi (l/w+w/2) = phi (l/w-w/2) := by
  rw [phi_eq,phi_eq]
  have he : l + -((l/w+w/2)^2/2) = -((l/w-w/2)^2/2) := by field_simp; ring
  calc
    _ = normalizer*Real.exp (l + -((l/w+w/2)^2/2)) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he]

theorem bsPut_log_delta (l w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun l => bsPut l w) (Real.exp l*normalCDF (l/w+w/2)) l := by
  have hp := ((hasDerivAt_id l).div_const w).add_const (w/2)
  have hm := ((hasDerivAt_id l).div_const w).sub_const (w/2)
  have hd := ((Real.hasDerivAt_exp l).mul ((normalCDF_hasDerivAt _).comp l hp)).sub
    ((normalCDF_hasDerivAt _).comp l hm)
  convert hd using 1
  · rfl
  · change Real.exp l*normalCDF (l/w+w/2) =
      Real.exp l*normalCDF (l/w+w/2)+Real.exp l*(phi (l/w+w/2)*(1/w))-phi (l/w-w/2)*(1/w)
    rw [← mul_assoc,phi_exponential_tilt l w hw]
    ring

theorem bsPut_log_gamma (l w : ℝ) :
    HasDerivAt (fun l => Real.exp l*normalCDF (l/w+w/2))
      (Real.exp l*normalCDF (l/w+w/2)+Real.exp l*phi (l/w+w/2)/w) l := by
  convert (Real.hasDerivAt_exp l).mul ((normalCDF_hasDerivAt _).comp l
    (((hasDerivAt_id l).div_const w).add_const (w/2))) using 1
  · rfl
  · dsimp [phi]; ring

theorem bsPut_vega (l w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (bsPut l) (phi (l/w-w/2)) w := by
  have hl := (hasDerivAt_const w l).div (hasDerivAt_id w) hw
  have hp := hl.add ((hasDerivAt_id w).div_const 2)
  have hm := hl.sub ((hasDerivAt_id w).div_const 2)
  have hd := (((normalCDF_hasDerivAt _).comp w hp).const_mul (Real.exp l)).sub
    ((normalCDF_hasDerivAt _).comp w hm)
  convert hd using 1
  · rfl
  · change phi (l/w-w/2) = Real.exp l*(phi (l/w+w/2)*((0*w-l*1)/w^2+1/2))-
      phi (l/w-w/2)*((0*w-l*1)/w^2-1/2)
    rw [← mul_assoc,phi_exponential_tilt l w hw]
    ring

/-- The log-coordinate Black--Scholes heat identity, including its drift term. -/
theorem bsPut_heat (l w : ℝ) (hw : w ≠ 0) :
    deriv (bsPut l) w = w*(deriv (fun y => deriv (fun z => bsPut z w) y) l-
      deriv (fun z => bsPut z w) l) := by
  have he : (fun y => deriv (fun z => bsPut z w) y) =
      (fun y => Real.exp y*normalCDF (y/w+w/2)) := by
    funext y
    exact (bsPut_log_delta y w hw).deriv
  rw [he,(bsPut_vega l w hw).deriv,(bsPut_log_gamma l w).deriv,(bsPut_log_delta l w hw).deriv]
  rw [add_sub_cancel_left,phi_exponential_tilt l w hw]
  field_simp

noncomputable def bsStockPut (K s w : ℝ) : ℝ := s*bsPut (Real.log K-Real.log s) w

noncomputable def bsKilledPut (B K s w : ℝ) : ℝ :=
  bsStockPut K s w - (s/B)*bsStockPut K (B^2/s) w

theorem bsStockPut_delta (K s w : ℝ) (hs : s ≠ 0) (hw : w ≠ 0) :
    HasDerivAt (fun s => bsStockPut K s w)
      (-normalCDF ((Real.log K-Real.log s)/w-w/2)) s := by
  have hl := (Real.hasDerivAt_log hs).const_sub (Real.log K)
  have h := (hasDerivAt_id s).mul ((bsPut_log_delta _ w hw).comp s hl)
  convert h using 1
  · rfl
  · dsimp only [bsPut,Function.comp_def,id_eq]
    field_simp
    ring

theorem bsStockPut_gamma (K s w : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun s => -normalCDF ((Real.log K-Real.log s)/w-w/2))
      (phi ((Real.log K-Real.log s)/w-w/2)/(s*w)) s := by
  have hl := ((Real.hasDerivAt_log hs).const_sub (Real.log K)).div_const w
  convert ((normalCDF_hasDerivAt _).comp s (hl.sub_const (w/2))).neg using 1
  · rfl
  · dsimp only [phi]
    ring

theorem bsStockPut_vega (K s w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (bsStockPut K s) (s*phi ((Real.log K-Real.log s)/w-w/2)) w :=
  (bsPut_vega _ w hw).const_mul s

theorem bsStockPut_heat (K s w : ℝ) (hs : s ≠ 0) (hw : w ≠ 0) :
    deriv (bsStockPut K s) w = w*s^2*deriv (fun y => deriv (fun z => bsStockPut K z w) y) s := by
  have he : (fun y => deriv (fun z => bsStockPut K z w) y) =ᶠ[𝓝 s]
      (fun y => -normalCDF ((Real.log K-Real.log y)/w-w/2)) := by
    filter_upwards [eventually_ne_nhds hs] with y hy
    exact (bsStockPut_delta K y w hy hw).deriv
  rw [(bsStockPut_vega K s w hw).deriv,he.deriv_eq,(bsStockPut_gamma K s w hs).deriv]
  field_simp

theorem bsKilledPut_boundary (B K w : ℝ) (hB : B ≠ 0) : bsKilledPut B K B w = 0 := by
  unfold bsKilledPut
  rw [div_self hB,one_mul,show B^2/B=B by field_simp]
  exact sub_self _

end BarrierManuscript
#print axioms BarrierManuscript.phi_exponential_tilt
#print axioms BarrierManuscript.bsPut_log_delta
#print axioms BarrierManuscript.bsPut_log_gamma
#print axioms BarrierManuscript.bsPut_vega
#print axioms BarrierManuscript.bsPut_heat

#print axioms BarrierManuscript.bsStockPut_delta
#print axioms BarrierManuscript.bsStockPut_gamma
#print axioms BarrierManuscript.bsStockPut_vega
#print axioms BarrierManuscript.bsStockPut_heat
#print axioms BarrierManuscript.bsKilledPut_boundary
