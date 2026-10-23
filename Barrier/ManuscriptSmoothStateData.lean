import ManuscriptCoordinateTangent
import ManuscriptSmoothTaylorBound
import ManuscriptL1InMeasure

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- State dynamics and a smooth variance function. The state coordinates
are actual finite sums of Ito integrals plus time-integrated drifts. Uniform
integrability, the joint limit, and the price correction are not input fields.
The two Lipschitz bounds are explicit sufficient regularity hypotheses. -/
structure SmoothStateData {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) where
  B : ι → BrownianSystem P 1
  stock : ι
  stock_driver : B stock=D.B
  independent : iIndepFun (fun i => brownianContinuousPath (B i)) P
  coordinate : κ → RegularCoordinate B
  x₀ : κ → ℝ
  f : (κ → ℝ) → ℝ
  differentiable : Differentiable ℝ f
  value_bound : ℝ≥0
  derivative_bound : ℝ≥0
  lipschitz : LipschitzWith value_bound f
  derivative_lipschitz : LipschitzWith derivative_bound (fderiv ℝ f)
  initial_variance : f x₀=D.v₀
  variance : ∀ t : ℝ,0 ≤ t → ∀ᵐ ω ∂P,
    D.V (realTimeClamp t) ω=f (fun j => x₀ j+coordinateIncrement (coordinate j) t ω)

noncomputable def smoothStatePoint {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : SmoothStateData (ι := ι) (κ := κ) D) (t : ℝ) (ω : Ω) (j : κ) : ℝ :=
  R.x₀ j+coordinateIncrement (R.coordinate j) t ω

noncomputable def smoothStateGradient {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : SmoothStateData (ι := ι) (κ := κ) D) (j : κ) : ℝ :=
  fderiv ℝ R.f R.x₀ (Pi.single j 1)

noncomputable def smoothStateInitialDiffusion {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : SmoothStateData (ι := ι) (κ := κ) D) (i : ι) : ℝ :=
  ∑ j,smoothStateGradient R j*(R.coordinate j).initial i

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}

theorem smooth_state_measurable (R : SmoothStateData (ι := ι) (κ := κ) D)
    (t : ℝ) (ht : 0 ≤ t) : Measurable (smoothStatePoint R t) :=
  Measurable.of_eval (fun j => measurable_const.add (coordinate_increment_measurable (R.coordinate j) t ht))

theorem smooth_state_linearization [DecidableEq κ] (R : SmoothStateData (ι := ι) (κ := κ) D)
    (t : ℝ) (ω : Ω) :
    fderiv ℝ R.f R.x₀ (smoothStatePoint R t ω-R.x₀)=
      ∑ j,smoothStateGradient R j*coordinateIncrement (R.coordinate j) t ω := by
  have he (j : κ) : (fun i : κ => if j=i then (1:ℝ) else 0)=Pi.single j 1 := by
    funext i
    by_cases h : j=i
    · subst i; simp
    · simp [Pi.single_apply,h,Ne.symm h]
  have h := LinearMap.pi_apply_eq_sum_univ (fderiv ℝ R.f R.x₀).toLinearMap
    (smoothStatePoint R t ω-R.x₀)
  simp_rw [he] at h
  simpa only [ContinuousLinearMap.coe_coe,Pi.sub_apply,smoothStatePoint,add_sub_cancel_left,
    smul_eq_mul,mul_comm,smoothStateGradient,Pi.single_apply] using h

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_measurable
#print axioms BarrierManuscript.smooth_state_linearization
