import ManuscriptSmoothPrice
import Chapter3GradientCalculus

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
open Asakura.Chapter3Complete Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- Joint space/volatility differential of the actual Bachelier put. -/
theorem put_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x w : E → ℝ) (dx dw : E →L[ℝ] ℝ) (z : E) (k : ℝ)
    (hx : HasFDerivAt x dx z) (hw : HasFDerivAt w dw z) (hwn : w z ≠ 0) :
    HasFDerivAt (fun y => put k (x y) (w y))
      ((-normalCDF ((k-x z)/w z)) • dx + phi ((k-x z)/w z) • dw) z := by
  have hd₀ := (hx.const_sub k).mul ((hasDerivAt_inv hwn).comp_hasFDerivAt z hw)
  simp only [Pi.mul_apply, Function.comp_apply, ← div_eq_mul_inv] at hd₀
  have hd := hd₀
  have h := ((hx.const_sub k).mul ((normalCDF_hasDerivAt _).comp_hasFDerivAt z hd)).add
    (hw.mul ((phi_derivative _).comp_hasFDerivAt z hd))
  convert h using 1
  · rfl
  · ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul, Pi.mul_apply, Function.comp_apply, phi, ← div_eq_mul_inv]
    field_simp
    ring

/-- Joint differential of the killed formula. -/
theorem killedPut_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x w : E → ℝ) (dx dw : E →L[ℝ] ℝ) (z : E) (b k : ℝ)
    (hx : HasFDerivAt x dx z) (hw : HasFDerivAt w dw z) (hwn : w z ≠ 0) :
    HasFDerivAt (fun y => killedPut b k (x y) (w y))
      ((-normalCDF ((k-x z)/w z)-normalCDF ((k-2*b+x z)/w z)) • dx +
       (phi ((k-x z)/w z)-phi ((k-2*b+x z)/w z)) • dw) z := by
  have h := (put_hasFDerivAt x w dx dw z k hx hw hwn).sub
    (put_hasFDerivAt (fun y => 2*b-x y) w (-dx) dw z k (hx.const_sub (2*b)) hw hwn)
  convert h using 1
  · rfl
  · ext v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
    have he : k-(2*b-x z) = k-2*b+x z := by ring
    rw [he]
    ring

/-- The two partial derivatives used in the remaining-variance version of
Ito's formula. They are derivatives of the smooth extension itself. -/
theorem smoothKilledPrice_first (δ b k : ℝ) (hδ : 0 < δ) (z : Fin 2 → ℝ)
    (hz : δ/2 < z 1) :
    fderiv ℝ (smoothKilledPrice δ b k) z (Pi.single 0 1) =
      -normalCDF ((k-z 0)/Real.sqrt (z 1))-normalCDF ((k-2*b+z 0)/Real.sqrt (z 1)) ∧
    fderiv ℝ (smoothKilledPrice δ b k) z (Pi.single 1 1) =
      (phi ((k-z 0)/Real.sqrt (z 1))-phi ((k-2*b+z 0)/Real.sqrt (z 1)))/(2*Real.sqrt (z 1)) := by
  have hr : 0 < z 1 := by linarith
  have hs : Real.sqrt (z 1) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hw := (Real.hasDerivAt_sqrt hr.ne').comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℝ) 1 z)
  have hf := killedPut_hasFDerivAt (fun x : Fin 2 → ℝ => x 0)
    (fun x : Fin 2 → ℝ => Real.sqrt (x 1)) _ _ z b k
    (hasFDerivAt_apply (𝕜 := ℝ) 0 z) hw hs
  have he : smoothKilledPrice δ b k =ᶠ[𝓝 z]
      (fun x => killedPut b k (x 0) (Real.sqrt (x 1))) := by
    have hc : Continuous (fun z : Fin 2 → ℝ => z 1) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hz)] with x hx
    unfold smoothKilledPrice
    rw [smoothPositive_eq (by positivity : 0 < δ/4) (by linarith : 2*(δ/4) ≤ x 1)]
  have hh := hf.congr_of_eventuallyEq he
  rw [hh.fderiv]
  constructor <;> simp [smul_eq_mul, div_eq_mul_inv]

/-- The second space derivative and the remaining-variance derivative
satisfy the heat equation on the region where the extension agrees with
actual pricing. -/
theorem smoothKilledPrice_heat (δ b k : ℝ) (hδ : 0 < δ) (z : Fin 2 → ℝ)
    (hz : δ/2 < z 1) :
    fderiv ℝ (fderiv ℝ (smoothKilledPrice δ b k)) z (Pi.single 0 1) (Pi.single 0 1) =
      2*fderiv ℝ (smoothKilledPrice δ b k) z (Pi.single 1 1) := by
  have hr : 0 < z 1 := by linarith
  have hs : Real.sqrt (z 1) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  rw [← coordinate_gradient_fderiv _ (smoothKilledPrice_contDiffN δ b k hδ 3) 0]
  let D := fun x : Fin 2 → ℝ =>
    -normalCDF ((k-x 0)/Real.sqrt (x 1))-normalCDF ((k-2*b+x 0)/Real.sqrt (x 1))
  have he : (fun x => fderiv ℝ (smoothKilledPrice δ b k) x (Pi.single 0 1)) =ᶠ[𝓝 z] D := by
    have hc : Continuous (fun z : Fin 2 → ℝ => z 1) := by fun_prop
    filter_upwards [hc.continuousAt.eventually (lt_mem_nhds hz)] with x hx
    exact (smoothKilledPrice_first δ b k hδ x hx).1
  rw [he.fderiv_eq, (smoothKilledPrice_first δ b k hδ z hz).2]
  have hw := ((hasDerivAt_inv hs).comp (z 1) (Real.hasDerivAt_sqrt hr.ne')).comp_hasFDerivAt z
    (hasFDerivAt_apply (𝕜 := ℝ) 1 z)
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) 0 z
  have ha := (h0.const_sub k).mul hw
  have hb := (h0.const_add (k-2*b)).mul hw
  have hd := ((normalCDF_hasDerivAt _).comp_hasFDerivAt z ha).neg.sub
    ((normalCDF_hasDerivAt _).comp_hasFDerivAt z hb)
  change HasFDerivAt D _ z at hd
  rw [hd.fderiv]
  simp [phi, smul_eq_mul, div_eq_mul_inv]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.put_hasFDerivAt
#print axioms BarrierManuscript.killedPut_hasFDerivAt

#print axioms BarrierManuscript.smoothKilledPrice_first
#print axioms BarrierManuscript.smoothKilledPrice_heat
