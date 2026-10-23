import ManuscriptRegularVarianceData
import ManuscriptFiniteSecondMoment

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- One coordinate of a regular state SDE, before any smooth composition. -/
structure RegularCoordinate {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : ι → BrownianSystem P 1) where
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

noncomputable def coordinateDrift {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ι → BrownianSystem P 1}
    (R : RegularCoordinate B) (t : ℝ) (ω : Ω) : ℝ := ∫ s in (0:ℝ)..t,R.drift (ω,s)

noncomputable def coordinateIncrement {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ι → BrownianSystem P 1}
    (R : RegularCoordinate B) (t : ℝ) (ω : Ω) : ℝ :=
  (∑ i,R.N i (realTimeClamp t) ω)+coordinateDrift R t ω

noncomputable def coordinateMomentBound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ι → BrownianSystem P 1}
    (R : RegularCoordinate B) : ℝ := 2*((Fintype.card ι:ℝ)*∑ i,(R.K i)^2)+2*R.L^2

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ι → BrownianSystem P 1}

theorem coordinate_drift_measurable (R : RegularCoordinate B) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (coordinateDrift R t) := by
  unfold coordinateDrift
  simp_rw [intervalIntegral.integral_of_le ht]
  exact R.drift_measurable.stronglyMeasurable.integral_prod_right'.measurable

theorem coordinate_increment_measurable (R : RegularCoordinate B) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (coordinateIncrement R t) :=
  (Finset.measurable_sum _ (fun i _ =>
    ((R.localM i).adapted P (B i).F _ (halfTimeClamp_finite t)).mono ((B i).le _) le_rfl)).add
    (coordinate_drift_measurable R t ht)

theorem coordinate_drift_bound (R : RegularCoordinate B) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (ω : Ω) :
    |coordinateDrift R t ω|≤R.L*t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => R.drift (ω,s)) (C := R.L) (fun s hs => ?_)
  · simpa only [coordinateDrift,Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] using h
  · rw [uIoc_of_le ht.1] at hs
    exact R.drift_bound ω s ⟨hs.1.le,hs.2.trans ht.2⟩

theorem coordinate_second_moment (R : RegularCoordinate B) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    MemLp (coordinateIncrement R t) 2 P ∧
      (∫ ω,(coordinateIncrement R t ω)^2 ∂P) ≤ coordinateMomentBound R*t := by
  have hN i := bounded_ito_second_moment P (B i) (R.G i) (R.N i)
    (R.adapted i) (R.continuous i) (R.localM i) (R.integral i) (R.K i) t
    (R.K_nonneg i) ht.1 (fun ω s hs => R.diffusion_bound i ω s ⟨hs.1,hs.2.trans ht.2⟩)
  have hs := finite_sum_second_moment P Finset.univ (fun i => R.N i (realTimeClamp t))
    (fun i _ => (hN i).1) (fun i => (R.K i)^2*t) (fun i _ => (hN i).2)
  have ha : MemLp (coordinateDrift R t) 2 P := MemLp.of_bound
    (coordinate_drift_measurable R t ht.1).aestronglyMeasurable (R.L*t)
    (ae_of_all _ fun ω => coordinate_drift_bound R t ht ω)
  have hiA := (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mp ha
  have hiN := (memLp_two_iff_integrable_sq hs.1.aestronglyMeasurable).mp hs.1
  have hA : (∫ ω,(coordinateDrift R t ω)^2 ∂P) ≤ R.L^2*t := by
    calc
      _ ≤ ∫ _ : Ω,R.L^2*t ∂P := by
        apply integral_mono_ae hiA (integrable_const _)
        filter_upwards with ω
        have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg R.L_nonneg ht.1)).mpr (coordinate_drift_bound R t ht ω)
        rw [sq_abs,mul_pow] at hh
        exact hh.trans (mul_le_mul_of_nonneg_left (by nlinarith [ht.1,ht.2] : t^2≤t) (sq_nonneg _))
      _ = _ := by simp
  have hLp : MemLp (coordinateIncrement R t) 2 P := hs.1.add ha
  refine ⟨hLp,?_⟩
  calc
    _ ≤ ∫ ω,2*(∑ i,R.N i (realTimeClamp t) ω)^2+2*(coordinateDrift R t ω)^2 ∂P := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).mp hLp)
        ((hiN.const_mul 2).add (hiA.const_mul 2))
      filter_upwards with ω
      dsimp only [coordinateIncrement,Pi.add_apply]
      nlinarith [sq_nonneg ((∑ i,R.N i (realTimeClamp t) ω)-coordinateDrift R t ω)]
    _ = 2*(∫ ω,(∑ i,R.N i (realTimeClamp t) ω)^2 ∂P)+2*(∫ ω,(coordinateDrift R t ω)^2 ∂P) := by
      rw [integral_add (hiN.const_mul 2) (hiA.const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ 2*((Finset.univ.card:ℝ)*∑ i,(R.K i)^2*t)+2*(R.L^2*t) := by linarith [hs.2]
    _ = coordinateMomentBound R*t := by simp only [coordinateMomentBound,Finset.card_univ,← Finset.sum_mul]; ring

end BarrierManuscript
#print axioms BarrierManuscript.coordinate_drift_measurable
#print axioms BarrierManuscript.coordinate_increment_measurable
#print axioms BarrierManuscript.coordinate_drift_bound
#print axioms BarrierManuscript.coordinate_second_moment
