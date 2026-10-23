import ManuscriptBlackScholes

open MeasureTheory Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The reciprocal reflection used by the Black--Scholes barrier formula. -/
theorem reciprocal_reflection_delta (f f' : ℝ → ℝ) (B s : ℝ)
    (hs : s ≠ 0) (hB : B ≠ 0) (hf : HasDerivAt f (f' (B^2/s)) (B^2/s)) :
    HasDerivAt (fun s => (s/B)*f (B^2/s))
      (f (B^2/s)/B-(B/s)*f' (B^2/s)) s := by
  have hy := (hasDerivAt_const s (B^2)).div (hasDerivAt_id s) hs
  convert ((hasDerivAt_id s).div_const B).mul (hf.comp s hy) using 1
  · rfl
  · dsimp only [Function.comp_def,Pi.div_apply,id_eq]
    field_simp
    ring

theorem reciprocal_reflection_gamma (f f' f'' : ℝ → ℝ) (B s : ℝ)
    (hs : s ≠ 0) (hB : B ≠ 0)
    (hf : HasDerivAt f (f' (B^2/s)) (B^2/s))
    (hf' : HasDerivAt f' (f'' (B^2/s)) (B^2/s)) :
    HasDerivAt (fun s => f (B^2/s)/B-(B/s)*f' (B^2/s))
      (B^3/s^3*f'' (B^2/s)) s := by
  have hy := (hasDerivAt_const s (B^2)).div (hasDerivAt_id s) hs
  have hq := (hasDerivAt_const s B).div (hasDerivAt_id s) hs
  convert ((hf.comp s hy).div_const B).sub (hq.mul (hf'.comp s hy)) using 1
  · rfl
  · dsimp only [Function.comp_def,Pi.div_apply,id_eq]
    field_simp
    ring

theorem bs_reflection_gamma (B K s w : ℝ) (hB : B ≠ 0) (hs : s ≠ 0) (hw : w ≠ 0) :
    deriv (fun y => deriv (fun z => (z/B)*bsStockPut K (B^2/z) w) y) s =
      B^3/s^3*(phi ((Real.log K-Real.log (B^2/s))/w-w/2)/((B^2/s)*w)) := by
  let f := fun x => bsStockPut K x w
  let f' := fun x => -normalCDF ((Real.log K-Real.log x)/w-w/2)
  let f'' := fun x => phi ((Real.log K-Real.log x)/w-w/2)/(x*w)
  have hn : B^2/s ≠ 0 := div_ne_zero (pow_ne_zero _ hB) hs
  have he : (fun y => deriv (fun z => (z/B)*f (B^2/z)) y) =ᶠ[𝓝 s]
      (fun y => f (B^2/y)/B-(B/y)*f' (B^2/y)) := by
    filter_upwards [eventually_ne_nhds hs] with y hy
    exact (reciprocal_reflection_delta f f' B y hy hB
      (bsStockPut_delta K (B^2/y) w (div_ne_zero (pow_ne_zero _ hB) hy) hw)).deriv
  rw [he.deriv_eq]
  exact (reciprocal_reflection_gamma f f' f'' B s hs hB
    (bsStockPut_delta K (B^2/s) w hn hw) (bsStockPut_gamma K (B^2/s) w hn)).deriv

/-- The reflected term satisfies the same stock-coordinate heat identity. -/
theorem bs_reflection_heat (B K s w : ℝ) (hB : B ≠ 0) (hs : s ≠ 0) (hw : w ≠ 0) :
    deriv (fun w => (s/B)*bsStockPut K (B^2/s) w) w =
      w*s^2*deriv (fun y => deriv (fun z => (z/B)*bsStockPut K (B^2/z) w) y) s := by
  rw [((bsStockPut_vega K (B^2/s) w hw).const_mul (s/B)).deriv,
    bs_reflection_gamma B K s w hB hs hw]
  field_simp

theorem bsKilledPut_heat (B K s w : ℝ) (hB : B ≠ 0) (hs : s ≠ 0) (hw : w ≠ 0) :
    deriv (bsKilledPut B K s) w =
      w*s^2*deriv (fun y => deriv (fun z => bsKilledPut B K z w) y) s := by
  let f := fun x => bsStockPut K x w
  let f' := fun x => -normalCDF ((Real.log K-Real.log x)/w-w/2)
  let f'' := fun x => phi ((Real.log K-Real.log x)/w-w/2)/(x*w)
  let g' := fun x => f (B^2/x)/B-(B/x)*f' (B^2/x)
  have hn : B^2/s ≠ 0 := div_ne_zero (pow_ne_zero _ hB) hs
  have hg' := reciprocal_reflection_gamma f f' f'' B s hs hB
    (bsStockPut_delta K (B^2/s) w hn hw) (bsStockPut_gamma K (B^2/s) w hn)
  have he : (fun y => deriv (fun z => bsKilledPut B K z w) y) =ᶠ[𝓝 s]
      (fun y => f' y-g' y) := by
    filter_upwards [eventually_ne_nhds hs] with y hy
    exact ((bsStockPut_delta K y w hy hw).sub (reciprocal_reflection_delta f f' B y hy hB
      (bsStockPut_delta K (B^2/y) w (div_ne_zero (pow_ne_zero _ hB) hy) hw))).deriv
  have hss : deriv (fun y => deriv (fun z => bsKilledPut B K z w) y) s =
      f'' s-B^3/s^3*f'' (B^2/s) := by
    rw [he.deriv_eq]
    exact ((bsStockPut_gamma K s w hs).sub hg').deriv
  have hv := ((bsStockPut_vega K s w hw).sub ((bsStockPut_vega K (B^2/s) w hw).const_mul (s/B))).deriv
  change deriv (bsKilledPut B K s) w = _ at hv
  rw [hv,hss]
  dsimp only [f'']
  field_simp

end BarrierManuscript
#print axioms BarrierManuscript.reciprocal_reflection_delta
#print axioms BarrierManuscript.reciprocal_reflection_gamma
#print axioms BarrierManuscript.bs_reflection_gamma
#print axioms BarrierManuscript.bs_reflection_heat

#print axioms BarrierManuscript.bsKilledPut_heat
