import ManuscriptBachelier

open MeasureTheory ProbabilityTheory

namespace BarrierManuscript

noncomputable def normalizer : ℝ := (Real.sqrt (2*Real.pi))⁻¹

theorem normalizer_nonneg : 0 ≤ normalizer := by unfold normalizer; positivity

theorem phi_eq (z : ℝ) : phi z = normalizer*Real.exp (-(z^2/2)) := by
  simp [phi, gaussianPDFReal, normalizer, neg_div]

theorem phi_nonneg (z : ℝ) : 0 ≤ phi z := gaussianPDFReal_nonneg 0 1 z

theorem phi_even (z : ℝ) : phi (-z) = phi z := by rw [phi_eq, phi_eq]; simp

theorem phi_le (z : ℝ) : phi z ≤ normalizer := by
  rw [phi_eq]
  exact mul_le_of_le_one_right normalizer_nonneg
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z]))

theorem square_mul_phi_le (z : ℝ) : z^2*phi z ≤ 2*normalizer := by
  have he : z^2/2 ≤ Real.exp (z^2/2) := by
    linarith [Real.add_one_le_exp (z^2/2)]
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(z^2/2))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hh
  have hc := mul_le_mul_of_nonneg_left hh normalizer_nonneg
  rw [phi_eq]
  nlinarith [hc]

/-- Uniform control of translated, rescaled Gaussian factors, including the
quadratic spatial weight needed in the manuscript's remainder estimates. -/
theorem shifted_gaussian_bound (a x w W : ℝ) (hw : 0 < w) (hW : w ≤ W) :
    (1+x^2)*phi ((a-x)/w) ≤ normalizer*(1+2*a^2+4*W^2) := by
  let z := (a-x)/w
  have hx : x = a-w*z := by dsimp [z]; field_simp; ring
  have hsq : x^2 ≤ 2*a^2+2*W^2*z^2 := by
    have hww : w^2 ≤ W^2 := sq_le_sq₀ hw.le (hw.le.trans hW) |>.mpr hW
    have hmul := mul_le_mul_of_nonneg_right hww (sq_nonneg z)
    rw [hx]
    nlinarith [sq_nonneg (a+w*z)]
  have hmul := mul_le_mul_of_nonneg_right hsq (phi_nonneg z)
  have h0 := phi_le z
  have h2 := square_mul_phi_le z
  have ha := mul_le_mul_of_nonneg_left h0 (sq_nonneg a)
  have hW2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg W)
  change (1+x^2)*phi z ≤ _
  nlinarith

theorem power_le_one_add_square (x : ℝ) (j : ℕ) (hj : j ≤ 2) :
    |x|^j ≤ 1+x^2 := by
  interval_cases j
  · simp [sq_nonneg]
  · simp only [pow_one]
    nlinarith [sq_nonneg (|x|-1), sq_abs x]
  · rw [sq_abs]; linarith

theorem shifted_gaussian_power_bound (a x w W : ℝ) (hw : 0 < w) (hW : w ≤ W)
    (j : ℕ) (hj : j ≤ 2) :
    |x|^j*phi ((a-x)/w) ≤ normalizer*(1+2*a^2+4*W^2) :=
  (mul_le_mul_of_nonneg_right (power_le_one_add_square x j hj)
    (phi_nonneg _)).trans (shifted_gaussian_bound a x w W hw hW)

noncomputable def thetaKernel (b k v w x : ℝ) : ℝ :=
  v/(2*w)*(phi ((k+x-2*b)/w)-phi ((k-x)/w))

/-- An explicit uniform Gaussian estimate for all three weights j=0,1,2.
It is valid on the whole real line, hence also on x<b. -/
theorem thetaKernel_bound (b k v w x W : ℝ) (hw : 0 < w) (hW : w ≤ W)
    (j : ℕ) (hj : j ≤ 2) :
    |x|^j*|thetaKernel b k v w x| ≤
      |v|/(2*w) * (normalizer*(1+2*k^2+4*W^2) +
        normalizer*(1+2*(2*b-k)^2+4*W^2)) := by
  have he : phi ((k+x-2*b)/w) = phi (((2*b-k)-x)/w) := by
    rw [show (k+x-2*b)/w = -(((2*b-k)-x)/w) by ring, phi_even]
  have ht : |phi ((k+x-2*b)/w)-phi ((k-x)/w)| ≤
      phi (((2*b-k)-x)/w)+phi ((k-x)/w) := by
    rw [he]
    simpa only [abs_of_nonneg (phi_nonneg _)] using
      abs_sub (phi (((2*b-k)-x)/w)) (phi ((k-x)/w))
  have hb := shifted_gaussian_power_bound (2*b-k) x w W hw hW j hj
  have hk := shifted_gaussian_power_bound k x w W hw hW j hj
  have hsum := mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg x) j)
  have hv : 0 ≤ |v|/(2*w) := by positivity
  have hh := mul_le_mul_of_nonneg_left (show
      |x|^j*|phi ((k+x-2*b)/w)-phi ((k-x)/w)| ≤
        normalizer*(1+2*k^2+4*W^2)+normalizer*(1+2*(2*b-k)^2+4*W^2) by
          nlinarith [hsum]) hv
  simpa only [thetaKernel, abs_mul, abs_div, abs_of_pos (by positivity : 0 < 2*w),
    mul_assoc, mul_left_comm] using hh

theorem killedPut_time_derivative (b k x t v w' : ℝ) (w : ℝ → ℝ)
    (hw : w t ≠ 0) (hd : HasDerivAt w w' t) (hclock : 2*w t*w' = -v) :
    HasDerivAt (fun u => killedPut b k x (w u)) (thetaKernel b k v (w t) x) t := by
  have h := (killedPut_vega b k x (w t) hw).comp t hd
  have he : phi ((k+x-2*b)/w t) = phi ((k-(2*b-x))/w t) := by
    congr 1; ring
  convert h using 1
  · rfl
  · unfold thetaKernel
    rw [he]
    have hv : v = -(2*w t*w') := by linarith
    rw [hv]
    field_simp
    ring

/-- The manuscript's (1-u)^(-1/2) estimate, with an explicit constant
independent of x, w, v and u whenever the displayed uniform bounds hold. -/
theorem thetaKernel_time_domination (b k v w x W V c u : ℝ)
    (hu : u < 1) (hc : 0 < c) (hw : c*Real.sqrt (1-u) ≤ w)
    (hW : w ≤ W) (hv : |v| ≤ V) (j : ℕ) (hj : j ≤ 2) :
    |x|^j*|thetaKernel b k v w x| ≤
      (V/(2*c)*(normalizer*(1+2*k^2+4*W^2)+
        normalizer*(1+2*(2*b-k)^2+4*W^2)))/Real.sqrt (1-u) := by
  have hr : 0 < Real.sqrt (1-u) := Real.sqrt_pos.mpr (by linarith)
  have hwp : 0 < w := (mul_pos hc hr).trans_le hw
  have hden : 0 < 2*(c*Real.sqrt (1-u)) := by positivity
  have hvp : 0 ≤ V := (abs_nonneg v).trans hv
  have hvdiv : |v|/(2*w) ≤ V/(2*(c*Real.sqrt (1-u))) :=
    (div_le_div_of_nonneg_right hv (by positivity)).trans
      (div_le_div_of_nonneg_left hvp hden (by linarith))
  have hC : 0 ≤ normalizer*(1+2*k^2+4*W^2)+
      normalizer*(1+2*(2*b-k)^2+4*W^2) := by
    have := normalizer_nonneg; positivity
  apply (thetaKernel_bound b k v w x W hwp hW j hj).trans
  convert mul_le_mul_of_nonneg_right hvdiv hC using 1
  ring

end BarrierManuscript

#print axioms BarrierManuscript.square_mul_phi_le
#print axioms BarrierManuscript.shifted_gaussian_bound
#print axioms BarrierManuscript.shifted_gaussian_power_bound
#print axioms BarrierManuscript.thetaKernel_bound
#print axioms BarrierManuscript.killedPut_time_derivative
#print axioms BarrierManuscript.thetaKernel_time_domination
