import ManuscriptGaussianProduct

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def gaussianMoment (a c b u : ℝ) : ℝ :=
  phi (a-c)*((u*a+(1-u)*c)*normalCDF ((b-(u*a+(1-u)*c))/Real.sqrt (u*(1-u))) -
    Real.sqrt (u*(1-u))*phi ((b-(u*a+(1-u)*c))/Real.sqrt (u*(1-u))))

theorem gaussian_product_moment_integrable (a c u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    Integrable (fun x => x*(phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u))*
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u)) volume := by
  have hs : 0 < Real.sqrt (u*(1-u)) := Real.sqrt_pos.mpr (mul_pos hu.1 (by linarith [hu.2]))
  have h := (scaled_phi_moment_integrable (u*a+(1-u)*c) (Real.sqrt (u*(1-u))) hs.ne').const_mul (phi (a-c))
  convert! h using 1
  funext x
  rw [mul_assoc,gaussian_product a c x u hu]
  ring

theorem gaussian_product_moment (a c b u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ x in Iio b, x*(phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u))*
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u)) = gaussianMoment a c b u := by
  have hs : 0 < Real.sqrt (u*(1-u)) := Real.sqrt_pos.mpr (mul_pos hu.1 (by linarith [hu.2]))
  have he x : x*(phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u))*
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u) =
      phi (a-c)*(x*phi ((x-(u*a+(1-u)*c))/Real.sqrt (u*(1-u)))/Real.sqrt (u*(1-u))) := by
    rw [mul_assoc,gaussian_product a c x u hu]
    ring
  simp_rw [he]
  rw [integral_const_mul,scaled_phi_truncated_moment _ _ _ hs]
  rfl

theorem psi_convolution_four_moments (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ x in Iio b, x*psi (b-x) (k-x) (1-u)*psi b x u) =
      gaussianMoment k 0 b u-gaussianMoment k (2*b) b u-
      gaussianMoment (2*b-k) 0 b u+gaussianMoment (2*b-k) (2*b) b u := by
  let f := fun a c x => x*(phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u))*
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u)
  have hi a c : IntegrableOn (f a c) (Iio b) := (gaussian_product_moment_integrable a c u hu).integrableOn
  have he x : x*psi (b-x) (k-x) (1-u)*psi b x u =
      f k 0 x-f k (2*b) x-f (2*b-k) 0 x+f (2*b-k) (2*b) x := by
    unfold psi f
    rw [show (k-x-2*(b-x))/Real.sqrt (1-u) = -((2*b-k-x)/Real.sqrt (1-u)) by ring,phi_even]
    ring
  simp_rw [he]
  have h12 : IntegrableOn (fun x => f k 0 x-f k (2*b) x) (Iio b) := (hi k 0).sub (hi k (2*b))
  have h123 : IntegrableOn (fun x => f k 0 x-f k (2*b) x-f (2*b-k) 0 x) (Iio b) := h12.sub (hi (2*b-k) 0)
  rw [integral_add h123 (hi (2*b-k) (2*b)),
    integral_sub h12 (hi (2*b-k) 0),integral_sub (hi k 0) (hi k (2*b))]
  simp only [f,gaussian_product_moment _ _ _ _ hu]

end BarrierManuscript
#print axioms BarrierManuscript.gaussian_product_moment_integrable
#print axioms BarrierManuscript.gaussian_product_moment
#print axioms BarrierManuscript.psi_convolution_four_moments
