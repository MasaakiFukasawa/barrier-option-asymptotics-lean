import ManuscriptRegularVarianceData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- Actual regular variance increments are uniformly integrable after the
square-root normalization. This is derived from the Ito equations, bounded
diffusion coefficients and bounded drift, rather than assumed as model data. -/
theorem regular_variance_uniformIntegrable {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RegularVarianceData (ι := ι) D) :
    UniformIntegrable (fun t : Ioc (0:ℝ) 1 => fun ω =>
      (D.V (realTimeClamp t.val) ω/D.v₀-1)/t.val^(1/2:ℝ)) 1 P := by
  have hN i := bounded_ito_uniformIntegrable P (R.B i) (R.G i) (R.N i)
    (R.adapted i) (R.continuous i) (R.localM i) (R.integral i)
    (R.K i) 1 (R.K_nonneg i) (R.diffusion_bound i)
  have hsum := ui_finset_sum P Finset.univ _ (fun i _ => hN i)
  have hA : UniformIntegrable (fun t : Ioc (0:ℝ) 1 => fun ω => regularDrift R t.val ω/Real.sqrt t.val) 1 P := by
    refine ui_of_uniform_bound P (fun t : Ioc (0:ℝ) 1 => fun ω => regularDrift R t.val ω/Real.sqrt t.val)
      (fun t => (regular_drift_measurable R t.val t.property.1.le).div_const (Real.sqrt t.val)) R.L ?_
    intro t ω
    exact (regular_scaled_drift_bound R t.val t.property ω).trans
      (mul_le_of_le_one_right R.L_nonneg (Real.sqrt_le_one.mpr t.property.2))
  have h := ui_const_mul P (ui_add P hsum hA) D.v₀⁻¹
  apply h.ae_eq
  intro t
  filter_upwards [R.variance] with ω hω
  rw [hω t.val t.property.1.le,← Real.sqrt_eq_rpow]
  simp only [← Finset.sum_div]
  dsimp only [regularDrift]
  field_simp [D.hv₀.ne', (Real.sqrt_pos.mpr t.property.1).ne']
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.regular_variance_uniformIntegrable
