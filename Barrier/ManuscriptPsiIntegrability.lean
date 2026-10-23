import ManuscriptChapmanKolmogorov

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem psi_integrable (b t : ℝ) (ht : 0 < t) : Integrable (psi b · t) volume := by
  have hw := (Real.sqrt_pos.mpr ht).ne'
  have h := (scaled_phi_integrable 0 (Real.sqrt t) hw).sub (scaled_phi_integrable (2*b) (Real.sqrt t) hw)
  convert! h using 1
  funext x
  dsimp only [Pi.sub_apply,psi]
  simp only [sub_zero]
  ring

theorem psi_first_moment_integrable (b t : ℝ) (ht : 0 < t) :
    Integrable (fun x => x*psi b x t) volume := by
  have hw := (Real.sqrt_pos.mpr ht).ne'
  have h := (scaled_phi_moment_integrable 0 (Real.sqrt t) hw).sub (scaled_phi_moment_integrable (2*b) (Real.sqrt t) hw)
  convert! h using 1
  funext x
  dsimp only [Pi.sub_apply,psi]
  simp only [sub_zero]
  ring

theorem psi_nonneg (b x t : ℝ) (hb : 0 ≤ b) (hx : x ≤ b) (ht : 0 < t) : 0 ≤ psi b x t := by
  unfold psi
  apply div_nonneg _ (Real.sqrt_nonneg _)
  apply sub_nonneg.mpr
  rw [phi_eq,phi_eq]
  apply mul_le_mul_of_nonneg_left _ normalizer_nonneg
  apply Real.exp_le_exp.mpr
  have hh : x^2 ≤ (x-2*b)^2 := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hx)]
  have hd := div_le_div_of_nonneg_right hh (sq_nonneg (Real.sqrt t))
  simp only [div_pow] at hd ⊢
  linarith

theorem psi_positive (b x t : ℝ) (hb : 0 < b) (hx : x < b) (ht : 0 < t) : 0 < psi b x t := by
  unfold psi
  apply div_pos _ (Real.sqrt_pos.mpr ht)
  apply sub_pos.mpr
  rw [phi_eq,phi_eq]
  have hn : 0 < normalizer := by unfold normalizer; positivity
  apply mul_lt_mul_of_pos_left _ hn
  apply Real.exp_lt_exp.mpr
  have hh : x^2 < (x-2*b)^2 := by nlinarith [mul_pos hb (sub_pos.mpr hx)]
  have hd := div_lt_div_of_pos_right hh (sq_pos_of_pos (Real.sqrt_pos.mpr ht))
  simp only [div_pow] at hd ⊢
  linarith

theorem psi_mass (b t : ℝ) (ht : 0 < t) :
    (∫ x in Iio b, psi b x t)=2*normalCDF (b/Real.sqrt t)-1 := by
  have he x : psi b x t=phi (x/Real.sqrt t)/Real.sqrt t-phi ((x-2*b)/Real.sqrt t)/Real.sqrt t := by
    unfold psi
    exact sub_div _ _ _
  simp_rw [he]
  rw [integral_sub (by simpa only [sub_zero,IntegrableOn] using (scaled_phi_integrable 0 (Real.sqrt t) (Real.sqrt_pos.mpr ht).ne').integrableOn)
    (scaled_phi_integrable (2*b) (Real.sqrt t) (Real.sqrt_pos.mpr ht).ne').integrableOn]
  have h1 := scaled_phi_cdf 0 (Real.sqrt t) b (Real.sqrt_pos.mpr ht)
  have h2 := scaled_phi_cdf (2*b) (Real.sqrt t) b (Real.sqrt_pos.mpr ht)
  simp only [sub_zero] at h1
  rw [h1,h2,show (b-2*b)/Real.sqrt t=-(b/Real.sqrt t) by ring,normalCDF_neg]
  ring

theorem psi_mass_le_one (b t : ℝ) (ht : 0 < t) :
    (∫ x in Iio b, psi b x t) ≤ 1 := by
  rw [psi_mass b t ht]
  have h : normalCDF (b/Real.sqrt t) ≤ 1 := measureReal_le_one
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.psi_integrable
#print axioms BarrierManuscript.psi_first_moment_integrable
#print axioms BarrierManuscript.psi_nonneg
#print axioms BarrierManuscript.psi_positive
#print axioms BarrierManuscript.psi_mass
#print axioms BarrierManuscript.psi_mass_le_one
