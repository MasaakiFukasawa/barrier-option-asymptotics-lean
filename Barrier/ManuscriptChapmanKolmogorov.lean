import ManuscriptBarPsi

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem scaled_phi_cdf (m s a : ℝ) (hs : 0 < s) :
    (∫ x in Iio a, phi ((x-m)/s)/s) = normalCDF ((a-m)/s) := by
  have hd x : HasDerivAt (fun y => normalCDF ((y-m)/s)) (phi ((x-m)/s)/s) x := by
    convert (normalCDF_hasDerivAt ((x-m)/s)).comp x (((hasDerivAt_id x).sub_const m).div_const s) using 1 <;> simp [phi,div_eq_mul_inv,Function.comp_def]
  have ht : Tendsto (fun x : ℝ => (x-m)/s) atBot atBot :=
    (tendsto_atBot_add_const_right atBot (-m) tendsto_id).atBot_div_const hs
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := a) (fun x _ => hd x)
    (scaled_phi_integrable m s hs.ne').integrableOn (normalCDF_atBot.comp ht)
  simpa only [integral_Iic_eq_integral_Iio,sub_zero] using h

noncomputable def gaussianMass (a c b u : ℝ) : ℝ :=
  phi (a-c)*normalCDF ((b-(u*a+(1-u)*c))/Real.sqrt (u*(1-u)))

theorem gaussian_product_integrable (a c u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    Integrable (fun x => (phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u))*
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u)) volume := by
  have hs : 0 < Real.sqrt (u*(1-u)) := Real.sqrt_pos.mpr (mul_pos hu.1 (sub_pos.mpr hu.2))
  have h := (scaled_phi_integrable (u*a+(1-u)*c) (Real.sqrt (u*(1-u))) hs.ne').const_mul (phi (a-c))
  convert! h using 1
  funext x
  rw [gaussian_product a c x u hu]
  ring

theorem gaussian_product_mass (a c b u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ x in Iio b, (phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u))*
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u)) = gaussianMass a c b u := by
  simp_rw [gaussian_product a c _ u hu]
  simp_rw [mul_div_assoc]
  rw [integral_const_mul,scaled_phi_cdf _ _ _ (Real.sqrt_pos.mpr (mul_pos hu.1 (sub_pos.mpr hu.2)))]
  rfl

theorem psi_chapman_kolmogorov (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ x in Iio b, psi (b-x) (k-x) (1-u)*psi b x u) = psi b k 1 := by
  let f := fun a c x => (phi ((a-x)/Real.sqrt (1-u))/Real.sqrt (1-u))*
      (phi ((x-c)/Real.sqrt u)/Real.sqrt u)
  have hi a c : IntegrableOn (f a c) (Iio b) := (gaussian_product_integrable a c u hu).integrableOn
  have he x : psi (b-x) (k-x) (1-u)*psi b x u =
      f k 0 x-f k (2*b) x-f (2*b-k) 0 x+f (2*b-k) (2*b) x := by
    unfold psi f
    rw [show (k-x-2*(b-x))/Real.sqrt (1-u) = -((2*b-k-x)/Real.sqrt (1-u)) by ring,phi_even]
    ring
  simp_rw [he]
  have h12 : IntegrableOn (fun x => f k 0 x-f k (2*b) x) (Iio b) := (hi k 0).sub (hi k (2*b))
  have h123 : IntegrableOn (fun x => f k 0 x-f k (2*b) x-f (2*b-k) 0 x) (Iio b) := h12.sub (hi (2*b-k) 0)
  rw [integral_add h123 (hi (2*b-k) (2*b)),integral_sub h12 (hi (2*b-k) 0),integral_sub (hi k 0) (hi k (2*b))]
  simp only [f,gaussian_product_mass _ _ _ _ hu]
  have pair (a : ℝ) : gaussianMass a 0 b u+gaussianMass (2*b-a) (2*b) b u=phi a := by
    unfold gaussianMass
    simp only [mul_zero,add_zero,sub_zero]
    rw [show 2*b-a-2*b = -a by ring,phi_even]
    rw [show u*(2*b-a)+(1-u)*(2*b)=2*b-u*a by ring]
    rw [show (b-(2*b-u*a))/Real.sqrt (u*(1-u)) = -((b-u*a)/Real.sqrt (u*(1-u))) by ring,normalCDF_neg]
    ring
  have h1 := pair k
  have h2 := pair (2*b-k)
  rw [show 2*b-(2*b-k)=k by ring] at h2
  simp only [psi,Real.sqrt_one,div_one]
  rw [show k-2*b=-(2*b-k) by ring,phi_even]
  linarith only [h1,h2]

/-- Analytic first moment of the normalized killed bridge kernel. Its
identification with a Brownian conditional law is a separate stochastic step. -/
theorem killed_bridge_first_moment (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ x in Iio b, x*(psi (b-x) (k-x) (1-u)*psi b x u/psi b k 1)) =
      barPsi b k u/psi b k 1 := by
  simp_rw [← mul_div_assoc,← mul_assoc]
  rw [integral_div,psi_convolution b k u hu]

end BarrierManuscript
#print axioms BarrierManuscript.scaled_phi_cdf
#print axioms BarrierManuscript.gaussian_product_integrable
#print axioms BarrierManuscript.gaussian_product_mass
#print axioms BarrierManuscript.psi_chapman_kolmogorov
#print axioms BarrierManuscript.killed_bridge_first_moment
