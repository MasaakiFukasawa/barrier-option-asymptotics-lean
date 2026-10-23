import ManuscriptGaussianTruncatedMoment

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Completing the square for the two Gaussian kernels in the killed
transition convolution. -/
theorem gaussian_product (a c x u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u)) *
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u) =
    phi (a-c)*phi ((x-(u*a+(1-u)*c))/Real.sqrt (u*(1-u)))/Real.sqrt (u*(1-u)) := by
  have hu0 : 0 ≤ u := hu.1.le
  have hv0 : 0 ≤ 1-u := by linarith [hu.2]
  have hus : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu.1).ne'
  have hvs : Real.sqrt (1-u) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [hu.2])).ne'
  have hsq : ((a-x)/Real.sqrt (1-u))^2+((x-c)/Real.sqrt u)^2 =
      (a-c)^2+((x-(u*a+(1-u)*c))/Real.sqrt (u*(1-u)))^2 := by
    rw [Real.sqrt_mul hu0]
    simp only [div_pow,mul_pow,Real.sq_sqrt hu0,Real.sq_sqrt hv0]
    field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne']
    <;> ring
  simp_rw [phi_eq]
  rw [Real.sqrt_mul hu0]
  have he : -( ((a-x)/Real.sqrt (1-u))^2/2) - (((x-c)/Real.sqrt u)^2/2) =
      -((a-c)^2/2)-(((x-(u*a+(1-u)*c))/(Real.sqrt u*Real.sqrt (1-u)))^2/2) := by
    rw [Real.sqrt_mul hu0] at hsq
    linarith
  calc
    _ = normalizer^2/(Real.sqrt u*Real.sqrt (1-u)) *
        (Real.exp (-(((a-x)/Real.sqrt (1-u))^2/2)) *
         Real.exp (-(((x-c)/Real.sqrt u)^2/2))) := by ring
    _ = normalizer^2/(Real.sqrt u*Real.sqrt (1-u)) *
        (Real.exp (-((a-c)^2/2)) *
         Real.exp (-(((x-(u*a+(1-u)*c))/(Real.sqrt u*Real.sqrt (1-u)))^2/2))) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 2
    _ = _ := by ring

end BarrierManuscript
#print axioms BarrierManuscript.gaussian_product
