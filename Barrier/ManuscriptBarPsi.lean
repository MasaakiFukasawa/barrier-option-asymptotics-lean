import ManuscriptGaussianConvolution

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def barPhi (b k u : ℝ) : ℝ :=
  phi k*(2*b-u*k-2*(b-u*k)*normalCDF ((b-u*k)/Real.sqrt (u*(1-u))))
noncomputable def barPsi (b k u : ℝ) : ℝ := barPhi b k u-barPhi b (2*b-k) u

theorem gaussian_moment_pair (b a u : ℝ) :
    gaussianMoment a 0 b u+gaussianMoment (2*b-a) (2*b) b u =
      barPhi b a u-2*Real.sqrt (u*(1-u))*phi a*phi ((b-u*a)/Real.sqrt (u*(1-u))) := by
  unfold gaussianMoment
  simp only [mul_zero,add_zero,sub_zero]
  rw [show 2*b-a-2*b = -a by ring,phi_even]
  rw [show u*(2*b-a)+(1-u)*(2*b)=2*b-u*a by ring]
  rw [show (b-(2*b-u*a))/Real.sqrt (u*(1-u)) = -((b-u*a)/Real.sqrt (u*(1-u))) by ring,
    phi_even,normalCDF_neg]
  unfold barPhi
  ring

theorem gaussian_reflection_boundary (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    phi k*phi ((b-u*k)/Real.sqrt (u*(1-u))) =
      phi (2*b-k)*phi ((b-u*(2*b-k))/Real.sqrt (u*(1-u))) := by
  have h1 := gaussian_product k 0 b u hu
  have h2 := gaussian_product (2*b-k) 0 b u hu
  simp only [mul_zero,add_zero,sub_zero] at h1 h2
  have he : phi ((2*b-k-b)/Real.sqrt (1-u)) = phi ((k-b)/Real.sqrt (1-u)) := by
    rw [show (2*b-k-b)/Real.sqrt (1-u) = -((k-b)/Real.sqrt (1-u)) by ring,phi_even]
  rw [he] at h2
  have h := h1.symm.trans h2
  have hs : Real.sqrt (u*(1-u)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu.1 (sub_pos.mpr hu.2))).ne'
  exact (div_left_inj' hs).mp h

/-- The closed Gaussian convolution identity printed in the main proof. -/
theorem psi_convolution (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ x in Iio b, x*psi (b-x) (k-x) (1-u)*psi b x u) = barPsi b k u := by
  rw [psi_convolution_four_moments b k u hu]
  have h1 := gaussian_moment_pair b k u
  have h2 := gaussian_moment_pair b (2*b-k) u
  rw [show 2*b-(2*b-k)=k by ring] at h2
  have he := congrArg (fun x : ℝ => 2*Real.sqrt (u*(1-u))*x) (gaussian_reflection_boundary b k u hu)
  unfold barPsi
  nlinarith only [h1,h2,he]

end BarrierManuscript
#print axioms BarrierManuscript.gaussian_moment_pair
#print axioms BarrierManuscript.gaussian_reflection_boundary
#print axioms BarrierManuscript.psi_convolution
