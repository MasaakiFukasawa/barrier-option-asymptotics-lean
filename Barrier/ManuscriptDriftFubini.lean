import ManuscriptIntegratedBounds
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- The Gaussian time bound yields joint integrability, an integrable bound
for every accumulated drift, and Fubini's identity. This is the bound needed
to remove local-martingale localization in the pricing identity. -/
theorem singular_drift_fubini {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω × ℝ → ℝ) (A : ℝ)
    (hm : AEStronglyMeasurable g (P.prod (volume.restrict (Ioo 0 1))))
    (hi : ∀ u ∈ Ioo (0:ℝ) 1, Integrable (fun ω => g (ω,u)) P)
    (hb : ∀ u ∈ Ioo (0:ℝ) 1, (∫ ω, |g (ω,u)| ∂P) ≤ A/Real.sqrt (1-u)) :
    Integrable g (P.prod (volume.restrict (Ioo 0 1))) ∧
    Integrable (fun ω => ∫ u in (0:ℝ)..1, |g (ω,u)|) P ∧
    (∀ᵐ ω ∂P, ∀ t ∈ Icc (0:ℝ) 1,
      |∫ u in (0:ℝ)..t, g (ω,u)| ≤ ∫ u in (0:ℝ)..1, |g (ω,u)|) ∧
    (∫ ω, (∫ u in (0:ℝ)..1, g (ω,u)) ∂P) = ∫ u in (0:ℝ)..1, ∫ ω, g (ω,u) ∂P := by
  have hmi : AEStronglyMeasurable (fun u => ∫ ω, |g (ω,u)| ∂P)
      (volume.restrict (Ioo 0 1)) := by
    simpa only [Real.norm_eq_abs, Function.comp_apply, Prod.swap_prod_mk] using
      hm.norm.prod_swap.integral_prod_right'
  have htime := (integrated_time_bound (fun u => ∫ ω, |g (ω,u)| ∂P) A hmi
    (fun u hu => by
      rw [abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg (g (ω,u))))]
      exact hb u hu)).1
  have hj : Integrable g (P.prod (volume.restrict (Ioo 0 1))) := by
    apply (integrable_prod_iff' hm).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu using hi u hu
    · simpa only [Real.norm_eq_abs, IntegrableOn] using
        (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mp htime
  refine ⟨hj,?_,?_,?_⟩
  · simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, Real.norm_eq_abs] using hj.integral_norm_prod_left
  · filter_upwards [hj.prod_right_ae] with ω hω
    have hfull : IntervalIntegrable (fun u => g (ω,u)) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr hω
    intro t ht
    calc
      _ ≤ ∫ u in (0:ℝ)..t, |g (ω,u)| := intervalIntegral.abs_integral_le_integral_abs ht.1
      _ ≤ ∫ u in (0:ℝ)..1, |g (ω,u)| :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (ae_of_all _ fun u => abs_nonneg _) hfull.norm
  · simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo] using (integral_integral_swap (f := fun ω u => g (ω,u)) hj)

end BarrierManuscript
#print axioms BarrierManuscript.singular_drift_fubini
