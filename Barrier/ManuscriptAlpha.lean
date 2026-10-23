import ManuscriptLimitPsiMoment

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def alpha {Γ : Type*} [MeasurableSpace Γ] (Q : Measure Γ)
    (X Y M : Γ → ℝ) (b k H : ℝ) : ℝ :=
  -(∫ u in (0:ℝ)..1, ∫ ω, barrierWeight (thetaKernel b k 1 (Real.sqrt (1-u))) b
    (Real.sqrt u*X ω,u^H*Y ω,Real.sqrt u*M ω) ∂Q)

theorem conditional_alpha_slice {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M Y : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hY : Integrable Y Q)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b k u H : ℝ) (hb : 0 < b) (hu : u ∈ Ioo (0:ℝ) 1) :
    ∃ q : ℝ → ℝ, Measurable q ∧
      (Q.restrict {ω | M ω ≤ b/Real.sqrt u})[Y | MeasurableSpace.comap X inferInstance] = q ∘ X ∧
      (∫ ω, barrierWeight (thetaKernel b k 1 (Real.sqrt (1-u))) b
        (Real.sqrt u*X ω,u^H*Y ω,Real.sqrt u*M ω) ∂Q) =
      -(u^H/2)*(∫ x in Iio b, q (x/Real.sqrt u)*psi (b-x) (k-x) (1-u)*psi b x u) := by
  obtain ⟨q,hq,he,h⟩ := conditional_psi_coefficient P Q B X M Y hX hM hY hlaw b k u H hb hu
  refine ⟨q,hq,he,?_⟩
  have hset : MeasurableSet {ω | Real.sqrt u*M ω ≤ b} := measurableSet_le (measurable_const.mul hM) measurable_const
  rw [← h,← integral_indicator hset]
  apply integral_congr_ae
  filter_upwards [marginal_maximum_noatom P Q B X M hX hM hlaw (b/Real.sqrt u)
    (div_pos hb (Real.sqrt_pos.mpr hu.1))] with ω hn
  have hn' : Real.sqrt u*M ω ≠ b := by
    intro he
    exact hn ((eq_div_iff (Real.sqrt_pos.mpr hu.1).ne').mpr (by simpa only [mul_comm] using he))
  have hi : Real.sqrt u*M ω < b ↔ Real.sqrt u*M ω ≤ b := lt_iff_le_and_ne.trans (and_iff_left hn')
  simp only [barrierWeight,hi,Set.indicator,Set.mem_setOf_eq]

theorem alpha_representation {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M Y : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hY : Integrable Y Q)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b k H : ℝ) (hb : 0 < b) :
    ∃ q : ℝ → ℝ → ℝ,
      (∀ u ∈ Ioo (0:ℝ) 1, Measurable (q u) ∧
        (Q.restrict {ω | M ω ≤ b/Real.sqrt u})[Y | MeasurableSpace.comap X inferInstance] = q u ∘ X) ∧
      alpha Q X Y M b k H = (1/2)*(∫ u in (0:ℝ)..1, u^H*
        (∫ x in Iio b, q u (x/Real.sqrt u)*psi (b-x) (k-x) (1-u)*psi b x u)) := by
  classical
  choose q hq he hc using fun u : Ioo (0:ℝ) 1 =>
    conditional_alpha_slice P Q B X M Y hX hM hY hlaw b k u.val H hb u.property
  let q' := fun u => if h : u ∈ Ioo (0:ℝ) 1 then q ⟨u,h⟩ else fun _ => 0
  refine ⟨q',fun u hu => ?_,?_⟩
  · simpa only [q',dif_pos hu] using And.intro (hq ⟨u,hu⟩) (he ⟨u,hu⟩)
  · unfold alpha
    rw [← intervalIntegral.integral_neg,← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [hc ⟨u,hu⟩]
    simp only [q',dif_pos hu]
    ring

end BarrierManuscript
#print axioms BarrierManuscript.conditional_alpha_slice
#print axioms BarrierManuscript.alpha_representation
