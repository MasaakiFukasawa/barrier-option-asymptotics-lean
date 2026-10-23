import ManuscriptGammaIntegral
import ManuscriptConditionalPsi

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem marginal_maximum_noatom {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b : ℝ) (hb : 0 < b) : ∀ᵐ ω ∂Q, M ω ≠ b := by
  have hm : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (halfTimeClamp_finite 1)).mono (B.le _) le_rfl
  have hid : IdentDistrib (fun ω => (X ω,M ω))
      (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)) Q P :=
    ⟨(hX.prodMk hM).aemeasurable,(hm.prodMk (brownianMaximum_measurable P B)).aemeasurable,hlaw⟩
  exact hid.symm.ae_snd (measurableSet_eq_fun measurable_snd measurable_const).compl
    (brownian_maximum_noatom P B b hb)

theorem scaled_killed_integral {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ ω, barrierWeight f b (Real.sqrt u*X ω,(1:ℝ),Real.sqrt u*M ω) ∂Q) =
      ∫ x in Iio b, f x*psi b x u := by
  have hc := Real.sqrt_pos.mpr hu
  have hset : MeasurableSet {ω | M ω ≤ b/Real.sqrt u} := measurableSet_le hM measurable_const
  have he : (∫ ω, barrierWeight f b (Real.sqrt u*X ω,(1:ℝ),Real.sqrt u*M ω) ∂Q) =
      ∫ ω in {ω | M ω ≤ b/Real.sqrt u}, f (Real.sqrt u*X ω) ∂Q := by
    rw [← integral_indicator hset]
    apply integral_congr_ae
    filter_upwards [marginal_maximum_noatom P Q B X M hX hM hlaw (b/Real.sqrt u) (div_pos hb hc)] with ω hn
    have hi : Real.sqrt u*M ω < b ↔ M ω ≤ b/Real.sqrt u := by
      rw [mul_comm,← lt_div_iff₀ hc]
      exact lt_iff_le_and_ne.trans (and_iff_left hn)
    simp only [barrierWeight,hi,mul_one,Set.indicator,Set.mem_setOf_eq]
  rw [he,limit_killed_expectation P Q B X M hX hM hlaw (b/Real.sqrt u) (div_pos hb hc)
    (fun x => f (Real.sqrt u*x)) (hf.comp (measurable_const.mul measurable_id))]
  simp_rw [← psi_at_one]
  simpa only [mul_one] using psi_integral_scaling b u hu f (fun _ => 1)

theorem limit_psi_first_moment {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b k u : ℝ) (hb : 0 < b) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ ω, barrierWeight (fun x => x*thetaKernel b k 1 (Real.sqrt (1-u)) x) b
      (Real.sqrt u*X ω,(1:ℝ),Real.sqrt u*M ω) ∂Q) = -(1/2)*barPsi b k u := by
  rw [scaled_killed_integral P Q B X M hX hM hlaw b u hb hu.1 _ (by
    unfold thetaKernel
    exact measurable_id.mul (measurable_const.mul
      ((phi_contDiff.continuous.measurable.comp (by fun_prop)).sub (phi_contDiff.continuous.measurable.comp (by fun_prop)))))]
  have he x : (x*thetaKernel b k 1 (Real.sqrt (1-u)) x)*psi b x u =
      -(1/2)*(x*psi (b-x) (k-x) (1-u)*psi b x u) := by rw [thetaKernel_psi]; ring
  simp_rw [he]
  rw [integral_const_mul,psi_convolution b k u hu]

end BarrierManuscript
#print axioms BarrierManuscript.marginal_maximum_noatom
#print axioms BarrierManuscript.scaled_killed_integral
#print axioms BarrierManuscript.limit_psi_first_moment
