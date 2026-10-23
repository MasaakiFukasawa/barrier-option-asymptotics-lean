import ManuscriptGaussianBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open Asakura.Chapter4

set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

theorem normalCDF_atBot : Tendsto normalCDF atBot (𝓝 0) := by
  change Tendsto (fun x => normalCDF x) atBot (𝓝 0)
  simp_rw [normalCDF_eq_integral]
  simpa only [id_eq] using
    (tendsto_integral_Iic_zero (f := gaussianPDFReal 0 1) (μ := volume)
      (tendsto_id : Tendsto (fun x : ℝ => x) atBot atBot))

theorem normalCDF_atTop : Tendsto normalCDF atTop (𝓝 1) := by
  have h := (normalCDF_atBot.comp tendsto_neg_atTop_atBot).const_sub 1
  simpa only [Function.comp_def, normalCDF_neg, sub_sub_cancel, sub_zero] using h

/-- Joint terminal limit: the state may move while total volatility vanishes. -/
theorem put_terminal {ι : Type*} {l : Filter ι} (k x : ℝ) (xs ws : ι → ℝ)
    (hx : Tendsto xs l (𝓝 x)) (hw : Tendsto ws l (𝓝[>] 0)) :
    Tendsto (fun n => put k (xs n) (ws n)) l (𝓝 (max (k-x) 0)) := by
  have hw0 := hw.mono_right inf_le_left
  have hwpos : ∀ᶠ n in l, 0 < ws n := hw.eventually self_mem_nhdsWithin
  have hn := hx.const_sub k
  have hnoise : Tendsto (fun n => ws n*phi ((k-xs n)/ws n)) l (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa using hw0.mul_const normalizer)
    · filter_upwards [hwpos] with n hn
      exact mul_nonneg hn.le (phi_nonneg _)
    · filter_upwards [hwpos] with n hn
      exact mul_le_mul_of_nonneg_left (phi_le _) hn.le
  have hmain : Tendsto (fun n => (k-xs n)*normalCDF ((k-xs n)/ws n)) l
      (𝓝 (max (k-x) 0)) := by
    rcases lt_trichotomy x k with hlt | heq | hgt
    · have hz : Tendsto (fun n => (k-xs n)/ws n) l atTop := by
        simpa only [div_eq_mul_inv, Pi.inv_apply] using hn.pos_mul_atTop (sub_pos.mpr hlt)
          hw.inv_tendsto_nhdsGT_zero
      simpa only [Function.comp_apply, mul_one, max_eq_left (sub_nonneg.mpr hlt.le)] using
        hn.mul (normalCDF_atTop.comp hz)
    · have hz : Tendsto (fun n => |k-xs n|) l (𝓝 0) := by
        simpa [heq] using hn.abs
      have hh : Tendsto (fun n => |(k-xs n)*normalCDF ((k-xs n)/ws n)|) l (𝓝 0) := by
        apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_) hz
        rw [abs_mul]
        change |k-xs n| * |(gaussianReal 0 1).real (Iic ((k-xs n)/ws n))| ≤ _
        rw [abs_of_nonneg measureReal_nonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) measureReal_le_one
      have hh' : Tendsto (fun n => ‖(k-xs n)*normalCDF ((k-xs n)/ws n)‖) l (𝓝 0) := by
        simpa only [Real.norm_eq_abs] using hh
      have h := tendsto_zero_iff_norm_tendsto_zero.mpr hh'
      simpa [heq, Real.norm_eq_abs] using h
    · have hz : Tendsto (fun n => (k-xs n)/ws n) l atBot := by
        simpa only [div_eq_mul_inv, Pi.inv_apply] using
          hw.inv_tendsto_nhdsGT_zero.atTop_mul_neg (sub_neg.mpr hgt) hn
            |>.congr (fun _ => mul_comm _ _)
      simpa only [Function.comp_apply, mul_zero, max_eq_right (sub_nonpos.mpr hgt.le)] using
        hn.mul (normalCDF_atBot.comp hz)
  simpa only [put, add_zero] using hmain.add hnoise

theorem killedPut_terminal {ι : Type*} {l : Filter ι} (b k x : ℝ)
    (hk : k ≤ b) (hxbar : x ≤ b) (xs ws : ι → ℝ)
    (hx : Tendsto xs l (𝓝 x)) (hw : Tendsto ws l (𝓝[>] 0)) :
    Tendsto (fun n => killedPut b k (xs n) (ws n)) l (𝓝 (max (k-x) 0)) := by
  have h := (put_terminal k x xs ws hx hw).sub
    (put_terminal k (2*b-x) (fun n => 2*b-xs n) ws (hx.const_sub (2*b)) hw)
  have hz : max (k-(2*b-x)) 0 = 0 := max_eq_right (by linarith)
  simpa only [killedPut, hz, sub_zero] using h

theorem killedPut_volatility_stability (b k x w₁ w₂ : ℝ)
    (h₁ : 0 < w₁) (h₂ : 0 < w₂) :
    |killedPut b k x w₂-killedPut b k x w₁| ≤ 2*normalizer*|w₂-w₁| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Ioi (0:ℝ)) (f := killedPut b k x)
    (f' := fun w => phi ((k-x)/w)-phi ((k-(2*b-x))/w))
    (fun w hw => (killedPut_vega b k x w (ne_of_gt hw)).hasDerivWithinAt)
    (C := 2*normalizer) (fun w _ => ?_) (convex_Ioi 0) h₁ h₂
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (phi_nonneg _), abs_of_nonneg (phi_nonneg _)]
      linarith [phi_le ((k-x)/w), phi_le ((k-(2*b-x))/w)])

end BarrierManuscript

#print axioms BarrierManuscript.normalCDF_atBot
#print axioms BarrierManuscript.normalCDF_atTop
#print axioms BarrierManuscript.put_terminal
#print axioms BarrierManuscript.killedPut_terminal
#print axioms BarrierManuscript.killedPut_volatility_stability
