import ManuscriptBrownianLinearCovariance

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A volatility-driver value minus its stock-driver projection is
independent of the entire stock-driving Brownian path. -/
theorem brownian_regression_independent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hind : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P)
    (ρ c : ℝ) (hc : ρ^2+c^2=1) (s : ℝ≥0) :
    IndepFun (fun ω => (1-ρ^2)*X s ω+(-ρ*c)*Y s ω)
      (fun ω t => ρ*X t ω+c*Y t ω) P := by
  let R : Unit → Ω → ℝ := fun _ ω => (1-ρ^2)*X s ω+(-ρ*c)*Y s ω
  let S : ℝ≥0 → Ω → ℝ := fun t ω => ρ*X t ω+c*Y t ω
  have hp := independent_gaussian_pair_process P X Y hX.isGaussianProcess hY.isGaussianProcess hind
  let τ : Unit ⊕ ℝ≥0 → ℝ≥0 := Sum.elim (fun _ => s) id
  let L : Unit ⊕ ℝ≥0 → (ℝ × ℝ) →L[ℝ] ℝ :=
    Sum.elim (fun _ => brownianLinearForm (1-ρ^2) (-ρ*c)) (fun _ => brownianLinearForm ρ c)
  have hg : IsGaussianProcess (Sum.elim R S) P := by
    convert (hp.comp_right τ).comp_left L using 1
    funext i ω
    cases i <;> rfl
  have hRm (i : Unit) : AEMeasurable (R i) P :=
    ((measurable_const.mul (hmX s)).add (measurable_const.mul (hmY s))).aemeasurable
  have hSm (t : ℝ≥0) : AEMeasurable (S t) P :=
    ((measurable_const.mul (hmX t)).add (measurable_const.mul (hmY t))).aemeasurable
  have hz (i : Unit) (t : ℝ≥0) : cov[R i,S t;P]=0 := by
    change cov[fun ω => (1-ρ^2)*X s ω+(-ρ*c)*Y s ω,fun ω => ρ*X t ω+c*Y t ω;P]=0
    rw [brownian_linear_covariance P X Y hX hY hind s t (1-ρ^2) (-ρ*c) ρ c]
    have he : (1-ρ^2)*ρ+(-ρ*c)*c=0 := by
      calc
        _ = ρ*(1-(ρ^2+c^2)) := by ring
        _ = 0 := by rw [hc]; ring
    rw [he,zero_mul]
  have hh := hg.indepFun_of_covariance_eq_zero hRm hSm hz
  exact hh.comp (measurable_pi_apply ()) measurable_id

end BarrierManuscript
#print axioms BarrierManuscript.brownian_regression_independent
