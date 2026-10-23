import ManuscriptScaledCoefficient
import ManuscriptRemainder

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The coefficient printed in the main theorem. Its weighted integrability
is derived from integrability of eta, without a mixed stock/variance moment. -/
theorem conditional_psi_coefficient {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M Y : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hY : Integrable Y Q)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b k u H : ℝ) (hb : 0 < b) (hu : u ∈ Ioo (0:ℝ) 1) :
    ∃ q : ℝ → ℝ, Measurable q ∧
      (Q.restrict {ω | M ω ≤ b/Real.sqrt u})[Y | MeasurableSpace.comap X inferInstance] = q ∘ X ∧
      (∫ ω in {ω | Real.sqrt u*M ω ≤ b},
        thetaKernel b k 1 (Real.sqrt (1-u)) (Real.sqrt u*X ω)*(u^H*Y ω) ∂Q) =
      -(u^H/2)*(∫ x in Iio b, q (x/Real.sqrt u)*psi (b-x) (k-x) (1-u)*psi b x u) := by
  let f := thetaKernel b k 1 (Real.sqrt (1-u))
  have hf : Measurable f := by
    unfold f thetaKernel
    exact measurable_const.mul ((phi_contDiff.continuous.measurable.comp
      (((measurable_const.add measurable_id).sub measurable_const).div_const _)).sub
      (phi_contDiff.continuous.measurable.comp ((measurable_const.sub measurable_id).div_const _)))
  have hw : 0 < Real.sqrt (1-u) := Real.sqrt_pos.mpr (by linarith [hu.2])
  have hfi : Integrable (fun ω => f (Real.sqrt u*X ω)*Y ω) Q := by
    have h := weighted_kernel_L1 Q (fun ω => Real.sqrt u*X ω)
      (fun ω => f (Real.sqrt u*X ω)) Y 0
      (1/(2*Real.sqrt (1-u))*(normalizer*(1+2*k^2+4*(Real.sqrt (1-u))^2)+
        normalizer*(1+2*(2*b-k)^2+4*(Real.sqrt (1-u))^2)))
      (measurable_const.mul hX).aestronglyMeasurable
      (hf.comp (measurable_const.mul hX)).aestronglyMeasurable hY
      (ae_of_all _ fun ω => by
        simpa only [abs_one] using
          (thetaKernel_bound b k 1 (Real.sqrt (1-u)) (Real.sqrt u*X ω) (Real.sqrt (1-u)) hw le_rfl 0 (by norm_num)))
    simpa only [pow_zero,one_mul] using h.1
  obtain ⟨q,hq,he,h⟩ := scaled_conditional_coefficient P Q B X M Y hX hM hY hlaw b u hb hu.1
  refine ⟨q,hq,he,?_⟩
  have hh := h f hf hfi.integrableOn
  have hp x : f x*q (x/Real.sqrt u)*psi b x u =
      -(1/2)*(q (x/Real.sqrt u)*psi (b-x) (k-x) (1-u)*psi b x u) := by
    dsimp only [f]
    rw [thetaKernel_psi]
    ring
  have hleft ω : f (Real.sqrt u*X ω)*(u^H*Y ω) = u^H*(f (Real.sqrt u*X ω)*Y ω) := by ring
  change (∫ ω in {ω | Real.sqrt u*M ω ≤ b}, f (Real.sqrt u*X ω)*(u^H*Y ω) ∂Q) = _
  simp_rw [hleft]
  rw [integral_const_mul,hh]
  simp_rw [hp]
  rw [integral_const_mul]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.conditional_psi_coefficient
