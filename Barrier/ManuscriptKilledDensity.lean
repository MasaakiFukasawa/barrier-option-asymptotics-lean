import ManuscriptTerminal
import ManuscriptSmoothPrice

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
open Asakura.Chapter4
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

noncomputable def killedDensity (b x : ℝ) : ℝ := if x < b then phi x-phi (x-2*b) else 0

theorem shifted_phi_integrable (d : ℝ) : Integrable (fun x => phi (x-d)) volume := by
  have he : (fun x => phi (x-d)) = gaussianPDFReal d 1 := by
    funext x
    simp [phi,gaussianPDFReal]
  rw [he]
  exact integrable_gaussianPDFReal d 1

theorem shifted_phi_integral (d k : ℝ) : (∫ x in Iio k, phi (x-d)) = normalCDF (k-d) := by
  have hd x : HasDerivAt (fun y => normalCDF (y-d)) (phi (x-d)) x := by
    simpa only [mul_one,Function.comp_def,id_eq,phi] using (normalCDF_hasDerivAt (x-d)).comp x ((hasDerivAt_id x).sub_const d)
  have ht : Tendsto (fun x : ℝ => x-d) atBot atBot := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atBot_add_const_right atBot (-d) tendsto_id
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := k) (fun x _ => hd x)
    (shifted_phi_integrable d).integrableOn (normalCDF_atBot.comp ht)
  simpa only [integral_Iic_eq_integral_Iio,sub_zero] using h

theorem killedDensity_nonneg (b : ℝ) (hb : 0 ≤ b) (x : ℝ) : 0 ≤ killedDensity b x := by
  unfold killedDensity
  split_ifs with hx
  · apply sub_nonneg.mpr
    rw [phi_eq,phi_eq]
    apply mul_le_mul_of_nonneg_left _ normalizer_nonneg
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hx.le)]
  · exact le_rfl

theorem killedDensity_integrable (b : ℝ) : Integrable (killedDensity b) volume := by
  have hphi : Integrable phi volume := by simpa only [sub_zero] using shifted_phi_integrable 0
  exact (hphi.sub (shifted_phi_integrable (2*b))).indicator measurableSet_Iio

theorem killedDensity_integral_Iio (b k : ℝ) :
    (∫ x in Iio k, killedDensity b x) = normalCDF (min k b)-normalCDF (min k b-2*b) := by
  have hphi : Integrable phi volume := by simpa only [sub_zero] using shifted_phi_integrable 0
  change (∫ x in Iio k, (Iio b).indicator (fun x => phi x-phi (x-2*b)) x) = _
  rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio, Iio_inter_Iio]
  rw [integral_sub hphi.integrableOn (shifted_phi_integrable (2*b)).integrableOn]
  have hfirst := shifted_phi_integral 0 (min b k)
  simp only [sub_zero] at hfirst
  rw [hfirst,shifted_phi_integral,min_comm b k]

end BarrierManuscript
#print axioms BarrierManuscript.shifted_phi_integrable
#print axioms BarrierManuscript.shifted_phi_integral
#print axioms BarrierManuscript.killedDensity_nonneg
#print axioms BarrierManuscript.killedDensity_integrable
#print axioms BarrierManuscript.killedDensity_integral_Iio
