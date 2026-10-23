import ManuscriptBlackScholesNormalized

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def normalLeg (l C B : ℝ → ℝ) (e w : ℝ) : ℝ :=
  C e*normalCDF (l e/w+e*w/2)+B e*w*phiAverage (l e/w) (e*w)

/-- Cancellation of the log-strike derivative in the first correction. -/
theorem normalLeg_derivative_zero (l C B : ℝ → ℝ) (l' C' B' w : ℝ)
    (hw : w ≠ 0) (hl : HasDerivAt l l' 0) (hC : HasDerivAt C C' 0)
    (hB : HasDerivAt B B' 0) (hmatch : C 0 = B 0*l 0) :
    HasDerivAt (fun e => normalLeg l C B e w)
      (C'*normalCDF (l 0/w)+w*(C 0/2+B')*phi (l 0/w)) 0 := by
  have hpair : HasDerivAt (fun e => (l e/w,e*w)) (l'/w,w) 0 := by
    convert (hl.div_const w).prodMk ((hasDerivAt_id (0:ℝ)).mul_const w) using 1
    · rfl
    · simp
  have havg : HasDerivAt (fun e => phiAverage (l e/w) (e*w))
      ((-(l 0/w)*phi (l 0/w))*(l'/w)) 0 := by
    have hh := (phiAverage_hasFDerivAt (l 0/w,(0:ℝ)*w)).comp_hasDerivAt 0 hpair
    convert! hh using 1
    simp only [zero_mul,phiAverageD_zero_apply]
  have harg := (hl.div_const w).add (((hasDerivAt_id (0:ℝ)).mul_const w).div_const 2)
  have hphi : HasDerivAt (fun e => normalCDF (l e/w+e*w/2))
      (phi (l 0/w)*(l'/w+w/2)) 0 := by
    convert! (normalCDF_hasDerivAt (l 0/w+(0:ℝ)*w/2)).comp 0 harg using 1
    simp only [zero_mul,zero_div,add_zero,mul_one,one_mul,phi]
  have hh := (hC.mul hphi).add ((hB.mul_const w).mul havg)
  convert! hh using 1
  simp only [normalLeg,zero_mul,phiAverage_zero]
  rw [hmatch]
  field_simp
  ring

theorem bsBarrierNormalized_derivative_zero (b k : ℝ) :
    HasDerivAt (fun e => bsBarrierNormalized b k e 1) (gamma b k) 0 := by
  have hfirst := normalLeg_derivative_zero (logRatio k) (fun _ => k) (fun _ => 1)
    (-k^2/2) 0 0 1 (by norm_num) (logRatio_derivative_zero k)
    (hasDerivAt_const 0 k) (hasDerivAt_const 0 1) (by simp [logRatio])
  have hl := (logRatio_derivative_zero k).sub ((logRatio_derivative_zero b).const_mul 2)
  have hC : HasDerivAt (fun e : ℝ => (k-2*b-e*b^2)/(1+e*b)) (b*(b-k)) 0 := by
    convert! ((hasDerivAt_const 0 (k-2*b)).sub ((hasDerivAt_id (0:ℝ)).mul_const (b^2))).div
      (((hasDerivAt_id (0:ℝ)).mul_const b).const_add 1) (by simp) using 1
    simp
    ring
  have hB : HasDerivAt (fun e : ℝ => 1+e*b) b 0 := by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const b).const_add 1 using 1
    simp
  have hsecond := normalLeg_derivative_zero (fun e => logRatio k e-2*logRatio b e)
    (fun e => (k-2*b-e*b^2)/(1+e*b)) (fun e => 1+e*b)
    (-k^2/2-2*(-b^2/2)) (b*(b-k)) b 1 (by norm_num) hl hC hB (by simp [logRatio])
  convert! hfirst.sub hsecond using 1
  · funext e
    dsimp only [Pi.sub_apply]
    unfold bsBarrierNormalized normalLeg
    ring
  · simp only [gamma,logRatio,ite_true,zero_mul,mul_zero,add_zero,sub_zero,div_one,one_mul,zero_add]
    ring

end BarrierManuscript
#print axioms BarrierManuscript.normalLeg_derivative_zero
#print axioms BarrierManuscript.bsBarrierNormalized_derivative_zero
