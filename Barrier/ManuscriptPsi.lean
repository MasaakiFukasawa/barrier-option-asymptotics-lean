import ManuscriptLimitDensity
import ManuscriptGaussianBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The reflected Gaussian transition density psi from the manuscript. -/
noncomputable def psi (b x t : ℝ) : ℝ :=
  (phi (x/Real.sqrt t)-phi ((x-2*b)/Real.sqrt t))/Real.sqrt t

theorem psi_reflected_form (b x t : ℝ) :
    psi b x t = (phi (x/Real.sqrt t)-phi ((2*b-x)/Real.sqrt t))/Real.sqrt t := by
  unfold psi
  rw [show (x-2*b)/Real.sqrt t = -((2*b-x)/Real.sqrt t) by ring,phi_even]

theorem thetaKernel_psi (b k u x : ℝ) :
    thetaKernel b k 1 (Real.sqrt (1-u)) x = -(1/2)*psi (b-x) (k-x) (1-u) := by
  unfold thetaKernel psi
  rw [show k-x-2*(b-x)=k+x-2*b by ring]
  ring

theorem psi_at_one (b x : ℝ) : psi b x 1 = phi x-phi (x-2*b) := by
  simp [psi]

theorem killedDensity_psi (b x : ℝ) (hx : x < b) : killedDensity b x = psi b x 1 := by
  simp [killedDensity,hx,psi]

theorem psi_scaling (b x u : ℝ) (hu : 0 < u) :
    psi b (Real.sqrt u*x) u = psi (b/Real.sqrt u) x 1/Real.sqrt u := by
  have hn := (Real.sqrt_pos.mpr hu).ne'
  unfold psi
  rw [Real.sqrt_one]
  simp only [div_one]
  rw [mul_div_cancel_left₀ x hn,
    show (Real.sqrt u*x-2*b)/Real.sqrt u=x-2*(b/Real.sqrt u) by field_simp]

theorem psi_continuous (b t : ℝ) : Continuous (fun x => psi b x t) := by
  unfold psi
  exact ((phi_contDiff.continuous.comp (continuous_id.div_const _)).sub
    (phi_contDiff.continuous.comp ((continuous_id.sub continuous_const).div_const _))).div_const _

end BarrierManuscript
#print axioms BarrierManuscript.psi_reflected_form
#print axioms BarrierManuscript.thetaKernel_psi
#print axioms BarrierManuscript.psi_at_one
#print axioms BarrierManuscript.killedDensity_psi
#print axioms BarrierManuscript.psi_scaling
#print axioms BarrierManuscript.psi_continuous
