import ManuscriptRoughCoefficient

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def bridgeArgument (b k u : ℝ) : ℝ := (b-u*k)/Real.sqrt (u*(1-u))
noncomputable def bridgeArgumentDeriv (b k u : ℝ) : ℝ :=
  (-k*Real.sqrt (u*(1-u))-(b-u*k)*((1-2*u)/(2*Real.sqrt (u*(1-u)))))/(Real.sqrt (u*(1-u)))^2

theorem bridgeArgument_derivative (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (bridgeArgument b k) (bridgeArgumentDeriv b k u) u := by
  have hr : Real.sqrt (u*(1-u)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu.1 (sub_pos.mpr hu.2))).ne'
  have hs : HasDerivAt (fun s : ℝ => s*(1-s)) (1-2*u) u := by
    convert (hasDerivAt_id u).mul ((hasDerivAt_id u).const_sub 1) using 1
    · rfl
    · simp only [id_eq]; ring
  have hd := hs.sqrt (mul_pos hu.1 (sub_pos.mpr hu.2)).ne'
  convert ((((hasDerivAt_id u).mul_const k).const_sub b).div hd hr) using 1
  · rfl
  · simp only [bridgeArgumentDeriv,id_eq]; ring

theorem barPhi_derivative (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (barPhi b k)
      (phi k*(-k+2*k*normalCDF (bridgeArgument b k u))-
        2*phi k*phi (bridgeArgument b k u)*(b-u*k)*bridgeArgumentDeriv b k u) u := by
  have hz := bridgeArgument_derivative b k u hu
  have hN := (normalCDF_hasDerivAt _).comp u hz
  have h := (((((hasDerivAt_id u).mul_const k).const_sub (2*b)).sub
    (((((hasDerivAt_id u).mul_const k).const_sub b).const_mul 2).mul hN)).const_mul (phi k))
  convert h using 1
  · rfl
  · dsimp only [phi,id_eq,Function.comp_def]; ring

/-- The apparent singular derivative terms cancel under reflection. -/
theorem bridge_derivative_cancellation (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (b-u*k)*bridgeArgumentDeriv b k u =
      (b-u*(2*b-k))*bridgeArgumentDeriv b (2*b-k) u := by
  have hs := Real.sq_sqrt (mul_pos hu.1 (sub_pos.mpr hu.2)).le
  have hr : Real.sqrt (u*(1-u)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu.1 (sub_pos.mpr hu.2))).ne'
  unfold bridgeArgumentDeriv
  field_simp
  linear_combination -4*b*(b-k)*(2*u-1)*hs

theorem barPsi_derivative (b k u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (barPsi b k)
      (phi k*k*(2*normalCDF (bridgeArgument b k u)-1)-
        phi (2*b-k)*(2*b-k)*(2*normalCDF (bridgeArgument b (2*b-k) u)-1)) u := by
  have he := gaussian_reflection_boundary b k u hu
  have hc := bridge_derivative_cancellation b k u hu
  have hd := (barPhi_derivative b k u hu).sub (barPhi_derivative b (2*b-k) u hu)
  convert hd using 1
  · rfl
  · change phi k*phi (bridgeArgument b k u) = phi (2*b-k)*phi (bridgeArgument b (2*b-k) u) at he
    calc
      _ = phi k*(-k+2*k*normalCDF (bridgeArgument b k u))-
          phi (2*b-k)*(-(2*b-k)+2*(2*b-k)*normalCDF (bridgeArgument b (2*b-k) u)) := by ring
      _ = _ := by
        rw [show 2*phi k*phi (bridgeArgument b k u)*(b-u*k)*bridgeArgumentDeriv b k u =
          2*(phi k*phi (bridgeArgument b k u))*((b-u*k)*bridgeArgumentDeriv b k u) by ring,
          he,hc]
        ring

end BarrierManuscript
#print axioms BarrierManuscript.bridgeArgument_derivative
#print axioms BarrierManuscript.barPhi_derivative
#print axioms BarrierManuscript.bridge_derivative_cancellation
#print axioms BarrierManuscript.barPsi_derivative
