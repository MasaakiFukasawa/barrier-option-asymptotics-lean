import ManuscriptStockData
import ManuscriptItoEndpointTangent
import ManuscriptBoundedItoUI
import ManuscriptFiniteUI
import ManuscriptFiniteInMeasure
import ManuscriptFiniteBrownianLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A regular variance SDE, in independent Brownian coordinates. The fields
are actual Ito equations and coefficient bounds; no limit, UI, or pricing
conclusion is assumed. The state-to-variance Ito formula is a separate step. -/
structure RegularVarianceData {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) where
  B : ι → BrownianSystem P 1
  stock : ι
  stock_driver : B stock=D.B
  independent : iIndepFun (fun i => brownianContinuousPath (B i)) P
  G : ι → HalfClosedTime → Ω → ℝ
  N : ι → HalfClosedTime → Ω → ℝ
  adapted : ∀ i t,t < ⊤ → Measurable[(B i).F t] (G i t)
  continuous : ∀ i ω t,t < ⊤ → ContinuousAt (fun s => G i s ω) t
  localM : ∀ i,LocalMProcessWitness P (B i).F (N i)
  integral : ∀ i,ItoCovarianceFormula P (B i).F ((B i).W 0)
    (fun z => G i (realTimeClamp z.2) z.1) (N i)
  initial : ι → ℝ
  initial_value : ∀ i,∀ᵐ ω ∂P,G i (realTimeClamp 0) ω=initial i
  K : ι → ℝ
  K_nonneg : ∀ i,0 ≤ K i
  diffusion_bound : ∀ i ω s,s ∈ Icc (0:ℝ) 1 → |G i (realTimeClamp s) ω|≤K i
  drift : Ω × ℝ → ℝ
  drift_measurable : Measurable drift
  L : ℝ
  L_nonneg : 0 ≤ L
  drift_bound : ∀ ω s,s ∈ Icc (0:ℝ) 1 → |drift (ω,s)|≤L
  variance : ∀ᵐ ω ∂P,∀ t : ℝ,0 ≤ t →
    D.V (realTimeClamp t) ω=D.v₀+(∑ i,N i (realTimeClamp t) ω)+∫ s in (0:ℝ)..t,drift (ω,s)

noncomputable def regularDrift {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RegularVarianceData (ι := ι) D) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0:ℝ)..t,R.drift (ω,s)

theorem regular_drift_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RegularVarianceData (ι := ι) D) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (regularDrift R t) := by
  unfold regularDrift
  simp_rw [intervalIntegral.integral_of_le ht]
  exact (R.drift_measurable.stronglyMeasurable.integral_prod_right').measurable

theorem regular_drift_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RegularVarianceData (ι := ι) D) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (ω : Ω) :
    |regularDrift R t ω|≤R.L*t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => R.drift (ω,s)) (C := R.L) (fun s hs => ?_)
  · simpa only [regularDrift,Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] using h
  · rw [uIoc_of_le ht.1] at hs
    exact R.drift_bound ω s ⟨hs.1.le,hs.2.trans ht.2⟩

theorem regular_scaled_drift_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : RegularVarianceData (ι := ι) D) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) (ω : Ω) :
    |regularDrift R t ω/Real.sqrt t|≤R.L*Real.sqrt t := by
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg t)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr ht.1)).mpr
  calc
    _ ≤ R.L*t := regular_drift_bound R t ⟨ht.1.le,ht.2⟩ ω
    _ = _ := by rw [mul_assoc,Real.mul_self_sqrt ht.1.le]

end BarrierManuscript
#print axioms BarrierManuscript.regular_drift_measurable
#print axioms BarrierManuscript.regular_drift_bound
#print axioms BarrierManuscript.regular_scaled_drift_bound
