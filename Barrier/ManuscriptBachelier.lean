import Chapter4NormalCDF

open MeasureTheory ProbabilityTheory Filter
open Asakura.Chapter4

namespace BarrierManuscript

noncomputable def phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x
noncomputable def put (k x w : ℝ) : ℝ :=
  (k-x)*normalCDF ((k-x)/w)+w*phi ((k-x)/w)
noncomputable def killedPut (b k x w : ℝ) : ℝ := put k x w-put k (2*b-x) w

theorem phi_derivative (x : ℝ) : HasDerivAt phi (-x*phi x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert h using 1
  · funext y; simp [phi, gaussianPDFReal]
  · simp [phi, gaussianPDFReal]; ring

theorem put_delta (k x w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun x => put k x w) (-normalCDF ((k-x)/w)) x := by
  have hd := ((hasDerivAt_id x).const_sub k).div_const w
  have h := (((hasDerivAt_id x).const_sub k).mul
    ((normalCDF_hasDerivAt _).comp x hd)).add
    (((phi_derivative _).comp x hd).const_mul w)
  convert h using 1
  · rfl
  · simp only [phi, neg_div, Function.comp_apply, id_eq]
    field_simp
    ring

theorem put_gamma (k x w : ℝ) (_hw : w ≠ 0) :
    HasDerivAt (fun x => -normalCDF ((k-x)/w)) (phi ((k-x)/w)/w) x := by
  convert (((normalCDF_hasDerivAt _).comp x
    (((hasDerivAt_id x).const_sub k).div_const w)).neg) using 1
  · funext y; rfl
  · dsimp [phi]; ring

theorem put_vega (k x w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (put k x) (phi ((k-x)/w)) w := by
  have hd := (hasDerivAt_const w (k-x)).div (hasDerivAt_id w) hw
  have h := (((normalCDF_hasDerivAt _).comp w hd).const_mul (k-x)).add
    ((hasDerivAt_id w).mul ((phi_derivative _).comp w hd))
  convert h using 1
  · rfl
  · dsimp [phi]
    field_simp
    ring

theorem killedPut_boundary (b k w : ℝ) : killedPut b k b w = 0 := by
  simp [killedPut, show 2*b-b=b by ring]

theorem killedPut_delta (b k x w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun x => killedPut b k x w)
      (-normalCDF ((k-x)/w)-normalCDF ((k-(2*b-x))/w)) x := by
  convert (put_delta k x w hw).sub
    ((put_delta k (2*b-x) w hw).comp x ((hasDerivAt_id x).const_sub (2*b))) using 1
  · rfl
  · ring

theorem killedPut_gamma (b k x w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun x => -normalCDF ((k-x)/w)-normalCDF ((k-(2*b-x))/w))
      ((phi ((k-x)/w)-phi ((k-(2*b-x))/w))/w) x := by
  have h := (put_gamma k x w hw).add
    ((put_gamma k (2*b-x) w hw).comp x ((hasDerivAt_id x).const_sub (2*b)))
  convert h using 1
  · funext y; dsimp; ring
  · ring

theorem killedPut_vega (b k x w : ℝ) (hw : w ≠ 0) :
    HasDerivAt (killedPut b k x)
      (phi ((k-x)/w)-phi ((k-(2*b-x))/w)) w :=
  (put_vega k x w hw).sub (put_vega k (2*b-x) w hw)

/-- The actual reflected pricing formula satisfies the backward PDE whenever
the remaining total volatility satisfies 2 w w' = -v. -/
theorem killedPut_pde (b k x t v w' : ℝ) (w : ℝ → ℝ)
    (hw : w t ≠ 0) (hd : HasDerivAt w w' t) (hclock : 2*w t*w' = -v) :
    deriv (fun u => killedPut b k x (w u)) t + v/2 *
      deriv (fun y => deriv (fun z => killedPut b k z (w t)) y) x = 0 := by
  have he : (fun y => deriv (fun z => killedPut b k z (w t)) y) =
      (fun y => -normalCDF ((k-y)/w t)-normalCDF ((k-(2*b-y))/w t)) := by
    funext y; exact (killedPut_delta b k y (w t) hw).deriv
  have ht := ((killedPut_vega b k x (w t) hw).comp t hd).deriv
  simp only [Function.comp_def] at ht
  rw [he, (killedPut_gamma b k x (w t) hw).deriv, ht]
  field_simp
  have hz : w t*2*w' + v = 0 := by nlinarith [hclock]
  rw [hz]
  ring

end BarrierManuscript

#print axioms BarrierManuscript.phi_derivative
#print axioms BarrierManuscript.put_delta
#print axioms BarrierManuscript.put_gamma
#print axioms BarrierManuscript.put_vega
#print axioms BarrierManuscript.killedPut_boundary
#print axioms BarrierManuscript.killedPut_delta
#print axioms BarrierManuscript.killedPut_gamma
#print axioms BarrierManuscript.killedPut_vega
#print axioms BarrierManuscript.killedPut_pde
