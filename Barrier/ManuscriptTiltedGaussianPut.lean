import ManuscriptLognormalPut

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem phi_exponential_shift (x c a : ℝ) :
    Real.exp (-a*x-a^2/2)*phi (x-c) = Real.exp (-a*c)*phi (x-(c-a)) := by
  rw [phi_eq,phi_eq]
  rw [mul_left_comm,← Real.exp_add,mul_left_comm,← Real.exp_add]
  congr 2
  ring

theorem put_weighted_phi_integrable (K w m : ℝ) (hK : 0 ≤ K) :
    Integrable (fun x => max (K-Real.exp (w*x)) 0*phi (x-m)) volume := by
  have hc : Continuous (fun x : ℝ => max (K-Real.exp (w*x)) 0*phi (x-m)) :=
    (by fun_prop : Continuous (fun x : ℝ => max (K-Real.exp (w*x)) 0)).mul
      (phi_contDiff.continuous.comp (continuous_id.sub continuous_const))
  apply ((shifted_phi_integrable m).const_mul K).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (le_max_right _ _),abs_of_nonneg (phi_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (phi_nonneg _)
  exact max_le (by linarith [Real.exp_pos (w*x)]) hK

theorem put_weighted_phi_cutoff (K w m b : ℝ) (hw : 0 < w) (hKb : K ≤ Real.exp (w*b)) :
    (∫ x in Iio b, max (K-Real.exp (w*x)) 0*phi (x-m)) =
      ∫ x, max (K-Real.exp (w*x)) 0*phi (x-m) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hh : b ≤ x := not_lt.mp hx
  have he := hKb.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hh hw.le))
  rw [max_eq_right (sub_nonpos.mpr he),zero_mul]

theorem tilted_killed_lognormal_integral (K w b : ℝ) (hK : 0 < K) (hw : 0 < w)
    (hKb : K ≤ Real.exp (w*b)) :
    (∫ x in Iio b, (max (K-Real.exp (w*x)) 0*Real.exp (-(w/2)*x-(w/2)^2/2)) *
      (phi x-phi (x-2*b))) =
      bsKilledPut (Real.exp (w*b)) K 1 w := by
  have he x : (max (K-Real.exp (w*x)) 0*Real.exp (-(w/2)*x-(w/2)^2/2)) *
      (phi x-phi (x-2*b)) =
      max (K-Real.exp (w*x)) 0*phi (x-(-(w/2))) -
      Real.exp (-w*b)*(max (K-Real.exp (w*x)) 0*phi (x-(2*b-w/2))) := by
    have h1 := phi_exponential_shift x 0 (w/2)
    have h2 := phi_exponential_shift x (2*b) (w/2)
    simp only [sub_zero,mul_zero,Real.exp_zero,one_mul,zero_sub] at h1
    rw [show -(w/2)*(2*b) = -w*b by ring] at h2
    rw [mul_sub,mul_assoc,mul_assoc,h1,h2]
    ring
  simp_rw [he]
  rw [integral_sub (put_weighted_phi_integrable K w _ hK.le).integrableOn
    ((put_weighted_phi_integrable K w _ hK.le).const_mul _).integrableOn,
    integral_const_mul,put_weighted_phi_cutoff K w _ b hw hKb,put_weighted_phi_cutoff K w _ b hw hKb,
    shifted_lognormal_put K w _ hK hw,shifted_lognormal_put K w _ hK hw]
  rw [show w*(-(w/2))+w^2/2=0 by ring,Real.exp_zero,
    show w*(2*b-w/2)+w^2/2=2*(w*b) by ring]
  unfold bsKilledPut
  simp only [div_one,one_div]
  rw [← Real.exp_nat_mul,neg_mul,Real.exp_neg]
  norm_num

end BarrierManuscript
#print axioms BarrierManuscript.phi_exponential_shift
#print axioms BarrierManuscript.put_weighted_phi_integrable
#print axioms BarrierManuscript.put_weighted_phi_cutoff
#print axioms BarrierManuscript.tilted_killed_lognormal_integral
