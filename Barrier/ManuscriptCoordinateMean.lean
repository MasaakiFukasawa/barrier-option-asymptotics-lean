import ManuscriptRegularCoordinate
import ManuscriptBoundedItoMean

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

theorem coordinate_mean_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ι → BrownianSystem P 1}
    (R : RegularCoordinate B) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    |∫ ω,coordinateIncrement R t ω ∂P|≤R.L*t := by
  have hN i := bounded_ito_second_moment P (B i) (R.G i) (R.N i)
    (R.adapted i) (R.continuous i) (R.localM i) (R.integral i) (R.K i) t
    (R.K_nonneg i) ht.1 (fun ω s hs => R.diffusion_bound i ω s ⟨hs.1,hs.2.trans ht.2⟩)
  have h0 i := bounded_ito_mean_zero P (B i) (R.G i) (R.N i)
    (R.adapted i) (R.continuous i) (R.localM i) (R.integral i) (R.K i) t
    (R.K_nonneg i) ht.1 (fun ω s hs => R.diffusion_bound i ω s ⟨hs.1,hs.2.trans ht.2⟩)
  have hNi i : Integrable (R.N i (realTimeClamp t)) P := (hN i).1.integrable (by norm_num)
  have hA : Integrable (coordinateDrift R t) P := (integrable_const (R.L*t)).mono'
    (coordinate_drift_measurable R t ht.1).aestronglyMeasurable
    (ae_of_all _ fun ω => coordinate_drift_bound R t ht ω)
  unfold coordinateIncrement
  rw [integral_add (integrable_finset_sum _ (fun i _ => hNi i)) hA,
    integral_finset_sum _ (fun i _ => hNi i)]
  simp only [h0,Finset.sum_const_zero,zero_add]
  calc
    _ ≤ ∫ ω,|coordinateDrift R t ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (coordinateDrift R t) (μ := P)
    _ ≤ ∫ _ : Ω,R.L*t ∂P := integral_mono_ae hA.abs (integrable_const _)
      (ae_of_all _ fun ω => coordinate_drift_bound R t ht ω)
    _ = _ := by simp

end BarrierManuscript
#print axioms BarrierManuscript.coordinate_mean_bound
