import ManuscriptBlackScholes
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

noncomputable def logRatio (k e : ℝ) : ℝ := if e=0 then k else Real.log (1+k*e)/e

theorem log_one_add_derivative (k e : ℝ) (he : 1+k*e ≠ 0) :
    HasDerivAt (fun e => Real.log (1+k*e)) (k/(1+k*e)) e := by
  convert (Real.hasDerivAt_log he).comp e (((hasDerivAt_id e).const_mul k).const_add 1) using 1
  · rfl
  · ring

theorem logRatio_derivative_zero (k : ℝ) : HasDerivAt (logRatio k) (-k^2/2) 0 := by
  have hn : ∀ᶠ e : ℝ in 𝓝 0, 1+k*e ≠ 0 := by
    exact ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt
      (x := (0:ℝ))).eventually_ne (by simp)
  have hfd : ∀ᶠ e : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun e => Real.log (1+k*e)-k*e) (k/(1+k*e)-k) e := by
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with e he
    convert (log_one_add_derivative k e he).sub ((hasDerivAt_id e).const_mul k) using 1
    · rfl
    · simp
  have hgd : ∀ᶠ e : ℝ in 𝓝[≠] 0, HasDerivAt (fun e : ℝ => e^2) (2*e) e := by
    apply Eventually.of_forall
    intro e
    convert (hasDerivAt_id e).pow 2 using 1
    · rfl
    · simp
  have hg' : ∀ᶠ e : ℝ in 𝓝[≠] 0, 2*e ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact mul_ne_zero (by norm_num) he
  have hfl : Tendsto (fun e => Real.log (1+k*e)-k*e) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun e : ℝ => Real.log (1+k*e)-k*e) 0 :=
      (log_one_add_derivative k 0 (by simp)).continuousAt.sub (continuous_id.const_mul k).continuousAt
    have hh := hcont.tendsto
    simpa only [Pi.sub_apply,id_eq,mul_zero,add_zero,Real.log_one,sub_zero] using hh.mono_left nhdsWithin_le_nhds
  have hgl : Tendsto (fun e : ℝ => e^2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (tendsto_id.pow 2 : Tendsto (fun e : ℝ => e^2) (𝓝 0) (𝓝 ((0:ℝ)^2))).mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun e : ℝ => (k/(1+k*e)-k)/(2*e)) (𝓝[≠] 0) (𝓝 (-k^2/2)) := by
    have hh : Tendsto (fun e : ℝ => -k^2/(2*(1+k*e))) (𝓝 (0:ℝ)) (𝓝 (-k^2/2)) := by
      have hd : Tendsto (fun e : ℝ => 2*(1+k*e)) (𝓝 0) (𝓝 2) := by
        simpa only [Pi.sub_apply,id_eq,mul_zero,add_zero,mul_one] using
          (tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)) :
            Tendsto (fun e : ℝ => 2*(1+k*e)) (𝓝 0) (𝓝 (2*(1+k*0))))
      exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => -k^2) (𝓝 0) (𝓝 (-k^2))).div hd (by norm_num)

    apply (hh.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin,hn.filter_mono nhdsWithin_le_nhds] with e he hne
    change e ≠ 0 at he
    field_simp
    ring
  have hlim := HasDerivAt.lhopital_zero_nhdsNE hfd hgd hg' hfl hgl hl
  rw [hasDerivAt_iff_tendsto_slope]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  change e ≠ 0 at he
  simp only [slope_def_field,logRatio,ite_true,ite_false,he,sub_zero]
  field_simp

noncomputable def logRatioD (k e : ℝ) : ℝ :=
  if e=0 then -k^2/2 else (k*e/(1+k*e)-Real.log (1+k*e))/e^2

theorem logRatio_derivative (k e : ℝ) (he : 1+k*e ≠ 0) :
    HasDerivAt (logRatio k) (logRatioD k e) e := by
  by_cases hz : e=0
  · subst e
    simpa only [logRatioD,ite_true] using logRatio_derivative_zero k
  · have hh := (log_one_add_derivative k e he).div (hasDerivAt_id e) hz
    have hd : HasDerivAt (fun e => Real.log (1+k*e)/e) (logRatioD k e) e := by
      convert hh using 1
      · rfl
      · simp only [logRatioD,hz,ite_false,id_eq,mul_one]
        ring
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with x hx
    simp only [logRatio,hx,ite_false]

theorem logRatioD_continuousAt_zero (k : ℝ) : ContinuousAt (logRatioD k) 0 := by
  have hn : ∀ᶠ e : ℝ in 𝓝 0, 1+k*e ≠ 0 :=
    ((continuous_const.add (continuous_id.const_mul k)).continuousAt (x := (0:ℝ))).eventually_ne (by simp)
  have hfd : ∀ᶠ e : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun e => k*e/(1+k*e)-Real.log (1+k*e)) (-k^2*e/(1+k*e)^2) e := by
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with e he
    have hh := (((hasDerivAt_id e).const_mul k).div
      (((hasDerivAt_id e).const_mul k).const_add 1) he).sub (log_one_add_derivative k e he)
    convert hh using 1
    · rfl
    · dsimp only [id_eq]
      field_simp
      ring
  have hgd : ∀ᶠ e : ℝ in 𝓝[≠] 0, HasDerivAt (fun e : ℝ => e^2) (2*e) e := by
    apply Eventually.of_forall
    intro e
    convert (hasDerivAt_id e).pow 2 using 1
    · rfl
    · simp
  have hg' : ∀ᶠ e : ℝ in 𝓝[≠] 0, 2*e ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with e he
    exact mul_ne_zero (by norm_num) he
  have hfl : Tendsto (fun e => k*e/(1+k*e)-Real.log (1+k*e)) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have hd : ContinuousAt (fun e : ℝ => k*e/(1+k*e)) 0 := by fun_prop (disch := norm_num)
    have hcont : ContinuousAt (fun e : ℝ => k*e/(1+k*e)-Real.log (1+k*e)) 0 :=
      hd.sub (log_one_add_derivative k 0 (by simp)).continuousAt
    have hh := hcont.tendsto
    simpa only [Pi.sub_apply,id_eq,mul_zero,zero_div,add_zero,Real.log_one,sub_zero] using hh.mono_left nhdsWithin_le_nhds
  have hgl : Tendsto (fun e : ℝ => e^2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (tendsto_id.pow 2 : Tendsto (fun e : ℝ => e^2) (𝓝 0) (𝓝 ((0:ℝ)^2))).mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun e : ℝ => (-k^2*e/(1+k*e)^2)/(2*e)) (𝓝[≠] 0) (𝓝 (-k^2/2)) := by
    have hd : ContinuousAt (fun e : ℝ => -k^2/(2*(1+k*e)^2)) 0 := by fun_prop (disch := norm_num)
    have hh : Tendsto (fun e : ℝ => -k^2/(2*(1+k*e)^2)) (𝓝 0) (𝓝 (-k^2/2)) := by
      simpa only [Pi.sub_apply,id_eq,mul_zero,add_zero,one_pow,mul_one] using hd.tendsto
    apply (hh.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin,hn.filter_mono nhdsWithin_le_nhds] with e he hne
    change e ≠ 0 at he
    field_simp
  have hh := HasDerivAt.lhopital_zero_nhdsNE hfd hgd hg' hfl hgl hl
  rw [continuousAt_iff_punctured_nhds]
  simp only [logRatioD,ite_true]
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  change e ≠ 0 at he
  simp only [logRatioD,he,ite_false]

theorem logRatio_strict_derivative_zero (k : ℝ) : HasStrictDerivAt (logRatio k) (-k^2/2) 0 := by
  have hn : ∀ᶠ e : ℝ in 𝓝 0, 1+k*e ≠ 0 :=
    ((continuous_const.add (continuous_id.const_mul k)).continuousAt (x := (0:ℝ))).eventually_ne (by simp)
  have hh := hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    (hn.mono fun e he => logRatio_derivative k e he) (logRatioD_continuousAt_zero k)
  simpa only [logRatioD,ite_true] using hh

end BarrierManuscript
#print axioms BarrierManuscript.log_one_add_derivative
#print axioms BarrierManuscript.logRatio_derivative_zero

#print axioms BarrierManuscript.logRatio_derivative
#print axioms BarrierManuscript.logRatioD_continuousAt_zero

#print axioms BarrierManuscript.logRatio_strict_derivative_zero
