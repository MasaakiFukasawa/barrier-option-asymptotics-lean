import ManuscriptTimeIntegral
import ManuscriptRemainder
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- Endpoint singularities are treated on the open integration interval;
no bound at u=1 is imposed. -/
theorem integrated_time_bound (f : ℝ → ℝ) (A : ℝ)
    (hm : AEStronglyMeasurable f (volume.restrict (Ioo 0 1)))
    (hb : ∀ u ∈ Ioo (0:ℝ) 1, |f u| ≤ A / Real.sqrt (1-u)) :
    IntervalIntegrable f volume 0 1 ∧ |∫ u in (0:ℝ)..1, f u| ≤ 2*A := by
  have hi : Integrable (fun u : ℝ => 1/Real.sqrt (1-u))
      (volume.restrict (Ioo 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      time_bound_integrable
  have hdom : ∀ᵐ u ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖f u‖ ≤ A*(1/Real.sqrt (1-u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa only [Real.norm_eq_abs, mul_one_div] using hb u hu
  have hfi := (hi.const_mul A).mono' hm hdom
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr hfi, ?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ u in Ioo (0:ℝ) 1, ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioo (0:ℝ) 1, A*(1/Real.sqrt (1-u)) :=
      integral_mono_ae hfi.norm (hi.const_mul A) hdom
    _ = 2*A := by
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), time_bound_integral]
      ring

/-- Dominated convergence for the actual singular time bound used in the
proof. Pointwise convergence is needed only for 0<u<1. -/
theorem singular_time_dominated_convergence (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (A : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioo 0 1)))
    (hb : ∀ n u, u ∈ Ioo (0:ℝ) 1 → |f n u| ≤ A/Real.sqrt (1-u))
    (hc : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => f n u) atTop (𝓝 (g u))) :
    IntervalIntegrable g volume 0 1 ∧
      Tendsto (fun n => ∫ u in (0:ℝ)..1, f n u) atTop (𝓝 (∫ u in (0:ℝ)..1, g u)) := by
  have hi : Integrable (fun u : ℝ => A*(1/Real.sqrt (1-u)))
      (volume.restrict (Ioo 0 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      time_bound_integrable).const_mul A
  have hdom n : ∀ᵐ u ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖f n u‖ ≤ A*(1/Real.sqrt (1-u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa only [Real.norm_eq_abs, mul_one_div] using hb n u hu
  have hconv : ∀ᵐ u ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun n => f n u) atTop (𝓝 (g u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu using hc u hu
  have hg : Integrable g (volume.restrict (Ioo 0 1)) := by
    apply hi.mono' (aestronglyMeasurable_of_tendsto_ae atTop hm hconv)
    filter_upwards [hconv, ae_all_iff.mpr hdom] with u hu hd
    exact le_of_tendsto hu.norm (Eventually.of_forall hd)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr hg, ?_⟩
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using
    tendsto_integral_of_dominated_convergence _ hm hi hdom hconv

/-- Integrate the spatial Gaussian/L1 estimate. No stock moment assumption
is used; its powers are absorbed by the kernel. -/
theorem integrated_weighted_kernel_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X G Y : ℝ → Ω → ℝ) (j : ℕ) (A C : ℝ)
    (hA : 0 ≤ A)
    (hX : ∀ u ∈ Ioo (0:ℝ) 1, AEStronglyMeasurable (X u) P)
    (hG : ∀ u ∈ Ioo (0:ℝ) 1, AEStronglyMeasurable (G u) P)
    (hY : ∀ u ∈ Ioo (0:ℝ) 1, Integrable (Y u) P)
    (hL : ∀ u ∈ Ioo (0:ℝ) 1, (∫ ω, |Y u ω| ∂P) ≤ C)
    (hb : ∀ u ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂P,
      |X u ω|^j*|G u ω| ≤ A/Real.sqrt (1-u))
    (hm : AEStronglyMeasurable (fun u => ∫ ω, X u ω^j*G u ω*Y u ω ∂P)
      (volume.restrict (Ioo 0 1))) :
    IntervalIntegrable (fun u => ∫ ω, X u ω^j*G u ω*Y u ω ∂P) volume 0 1 ∧
    |∫ u in (0:ℝ)..1, ∫ ω, X u ω^j*G u ω*Y u ω ∂P| ≤ 2*(A*C) := by
  apply integrated_time_bound _ (A*C) hm
  intro u hu
  obtain ⟨_, he⟩ := weighted_kernel_L1 P (X u) (G u) (Y u) j
    (A/Real.sqrt (1-u)) (hX u hu) (hG u hu) (hY u hu) (hb u hu)
  calc
    _ ≤ (A/Real.sqrt (1-u))*(∫ ω, |Y u ω| ∂P) := he
    _ ≤ (A/Real.sqrt (1-u))*C := mul_le_mul_of_nonneg_left (hL u hu)
      (div_nonneg hA (Real.sqrt_nonneg _))
    _ = _ := by ring

end BarrierManuscript

#print axioms BarrierManuscript.integrated_time_bound
#print axioms BarrierManuscript.singular_time_dominated_convergence
#print axioms BarrierManuscript.integrated_weighted_kernel_bound
