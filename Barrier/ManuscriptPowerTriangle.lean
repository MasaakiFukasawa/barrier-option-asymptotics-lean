import ManuscriptTimeTriangle

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem power_triangle_integrable (p : ℝ) (hp : -1 < p) :
    Integrable (fun z : ℝ × ℝ => if z.2 ≤ z.1 then (z.1-z.2)^p else 0)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
  let f : ℝ × ℝ → ℝ := fun z => if z.2 ≤ z.1 then (z.1-z.2)^p else 0
  have hm : Measurable f := Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    (by fun_prop) measurable_const
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change Integrable ((Iic u).indicator (fun s : ℝ => (u-s)^p)) _
    rw [integrable_indicator_iff measurableSet_Iic]
    change Integrable _ ((volume.restrict (Ioc (0:ℝ) 1)).restrict (Iic u))
    rw [Measure.restrict_restrict measurableSet_Iic]
    have he : Iic u ∩ Ioc (0:ℝ) 1=Ioc 0 u := by
      ext s
      simp only [mem_inter_iff,mem_Iic,mem_Ioc]
      constructor
      · rintro ⟨h,hs,_⟩; exact ⟨hs,h⟩
      · rintro ⟨hs,h⟩; exact ⟨h,hs,h.trans hu.2⟩
    rw [he]
    have hpow : IntervalIntegrable (fun s : ℝ => s^p) volume 0 u := intervalIntegral.intervalIntegrable_rpow' hp
    have hrev := (hpow.comp_sub_left u).symm
    simp only [sub_self,sub_zero] at hrev
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hu.1.le).mp hrev
  · apply (integrable_const (1/(p+1))).mono' hm.aestronglyMeasurable.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have he : (∫ s in Ioc (0:ℝ) 1,‖f (u,s)‖)=u^(p+1)/(p+1) := by
      have hn s : ‖f (u,s)‖=if s ≤ u then (u-s)^p else 0 := by
        dsimp only [f]
        split_ifs with h
        · exact Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr h) _)
        · exact norm_zero
      simp_rw [hn]
      rw [unit_triangle_row _ u ⟨hu.1.le,hu.2⟩,
        intervalIntegral.integral_comp_sub_left (fun s : ℝ => s^p) u,sub_self,sub_zero,
        integral_rpow (Or.inl hp),Real.zero_rpow (by linarith : p+1 ≠ 0),sub_zero]
    rw [he,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Real.rpow_nonneg hu.1.le _) (by linarith))]
    exact div_le_div_of_nonneg_right (Real.rpow_le_one hu.1.le hu.2 (by linarith)) (by linarith)

theorem weighted_power_triangle (p : ℝ) (hp : -1 < p) (g : ℝ → ℝ)
    (hg : Measurable g) (C : ℝ) (hb : ∀ s, |g s| ≤ C) :
    (∫ u in (0:ℝ)..1,∫ s in (0:ℝ)..u,(u-s)^p*g s)=
      ∫ s in (0:ℝ)..1,g s*(1-s)^(p+1)/(p+1) := by
  have hi := (power_triangle_integrable p hp).mul_bdd (hg.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs,Function.comp_def] using hb z.2)
  have hi' : Integrable (fun z : ℝ × ℝ => if z.2 ≤ z.1 then (z.1-z.2)^p*g z.2 else 0)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    convert hi using 1
    funext z
    split_ifs <;> simp
  rw [unit_triangle_fubini _ hi']
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro s hs
  dsimp only
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_sub_right (fun u : ℝ => u^p) s,sub_self,
    integral_rpow (Or.inl hp),Real.zero_rpow (by linarith : p+1 ≠ 0),sub_zero]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.power_triangle_integrable
#print axioms BarrierManuscript.weighted_power_triangle
