import ManuscriptGaussianPairProcess

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem brownian_linear_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hind : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P)
    (s t : ℝ≥0) (a b c d : ℝ) :
    cov[fun ω => a*X s ω+b*Y s ω,fun ω => c*X t ω+d*Y t ω;P]=
      (a*c+b*d)*min (s:ℝ) (t:ℝ) := by
  have hXs := (hX.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hYs := (hY.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hXt := (hX.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hYt := (hY.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hc1 := (hind.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero hXs hYt
  have hc2 := (hind.symm.comp (measurable_pi_apply s) (measurable_pi_apply t)).covariance_eq_zero hYs hXt
  change cov[X s,Y t;P]=0 at hc1
  change cov[Y s,X t;P]=0 at hc2
  change cov[(fun ω => a*X s ω)+(fun ω => b*Y s ω),
    (fun ω => c*X t ω)+(fun ω => d*Y t ω);P]=_
  rw [covariance_add_left (hXs.const_mul a) (hYs.const_mul b) ((hXt.const_mul c).add (hYt.const_mul d))]
  rw [covariance_add_right (hXs.const_mul a) (hXt.const_mul c) (hYt.const_mul d),
    covariance_add_right (hYs.const_mul b) (hXt.const_mul c) (hYt.const_mul d)]
  simp_rw [covariance_const_mul_left,covariance_const_mul_right]
  rw [hX.covariance_eval,hY.covariance_eval]
  change a*(c*min (s:ℝ) (t:ℝ))+a*(d*cov[X s,Y t;P])+
    (b*(c*cov[Y s,X t;P])+b*(d*min (s:ℝ) (t:ℝ)))=_
  rw [hc1,hc2]
  ring

theorem brownian_linear_preBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hind : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P)
    (a b : ℝ) (hab : a^2+b^2=1) :
    IsPreBrownianReal (fun t ω => a*X t ω+b*Y t ω) P := by
  apply (independent_gaussian_linear_process P X Y hX.isGaussianProcess hY.isGaussianProcess hind a b).isPreBrownianReal_of_covariance
  · intro t
    rw [integral_add ((hX.integrable_eval t).const_mul a) ((hY.integrable_eval t).const_mul b),
      integral_const_mul,integral_const_mul,hX.integral_eval,hY.integral_eval]
    ring
  · intro s t hst
    rw [brownian_linear_covariance P X Y hX hY hind s t a b a b]
    rw [show a*a+b*b=1 by nlinarith [hab],one_mul,min_eq_left (show (s:ℝ)≤(t:ℝ) from hst)]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_linear_covariance
#print axioms BarrierManuscript.brownian_linear_preBrownian
