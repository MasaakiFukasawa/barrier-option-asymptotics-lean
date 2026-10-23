import ManuscriptBrownianRegression

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Bounded measurable tests of the entire stock path see only the
correlated component of the volatility Brownian motion. -/
theorem brownian_regression_test {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (hmX : ∀ t, Measurable (X t)) (hmY : ∀ t, Measurable (Y t))
    (hind : IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P)
    (ρ c : ℝ) (hc : ρ^2+c^2=1) (s : ℝ≥0) (Z : Ω → ℝ)
    (hZ : Measurable[MeasurableSpace.comap (fun ω t => ρ*X t ω+c*Y t ω) inferInstance] Z)
    (C : ℝ) (hb : ∀ ω, |Z ω| ≤ C) :
    (∫ ω,X s ω*Z ω ∂P)=ρ*(∫ ω,(ρ*X s ω+c*Y s ω)*Z ω ∂P) := by
  let S : ℝ≥0 → Ω → ℝ := fun t ω => ρ*X t ω+c*Y t ω
  let R : Ω → ℝ := fun ω => (1-ρ^2)*X s ω+(-ρ*c)*Y s ω
  have hS := brownian_linear_preBrownian P X Y hX hY hind ρ c hc
  have hmS : Measurable (fun ω t => S t ω) :=
    measurable_pi_iff.mpr (fun t => (measurable_const.mul (hmX t)).add (measurable_const.mul (hmY t)))
  have hmR : Measurable R := (measurable_const.mul (hmX s)).add (measurable_const.mul (hmY s))
  have hmZ : Measurable Z := hZ.mono hmS.comap_le le_rfl
  have hreg : IndepFun R (fun ω t => S t ω) P := brownian_regression_independent P X Y hX hY hmX hmY hind ρ c hc s
  have hRZ : IndepFun R Z P := indep_of_indep_of_le_right hreg hZ.comap_le
  have hmean : (∫ ω,R ω ∂P)=0 := by
    unfold R
    rw [integral_add ((hX.integrable_eval s).const_mul _) ((hY.integrable_eval s).const_mul _),
      integral_const_mul,integral_const_mul,hX.integral_eval,hY.integral_eval]
    ring
  have hzero : (∫ ω,R ω*Z ω ∂P)=0 := by
    rw [hRZ.integral_fun_mul_eq_mul_integral hmR.aestronglyMeasurable hmZ.aestronglyMeasurable,hmean,zero_mul]
  have hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C := ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω
  have hiX := (hX.integrable_eval s).mul_bdd hmZ.aestronglyMeasurable hbound
  have hiS := (hS.integrable_eval s).mul_bdd hmZ.aestronglyMeasurable hbound
  have he ω : R ω*Z ω=X s ω*Z ω-ρ*(S s ω*Z ω) := by dsimp only [R,S]; ring
  simp_rw [he] at hzero
  rw [integral_sub hiX (hiS.const_mul ρ),integral_const_mul] at hzero
  change (∫ ω,X s ω*Z ω ∂P)=ρ*(∫ ω,S s ω*Z ω ∂P)
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.brownian_regression_test
