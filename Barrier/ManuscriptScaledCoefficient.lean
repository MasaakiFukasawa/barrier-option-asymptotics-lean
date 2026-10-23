import ManuscriptPsi

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem integral_comp_mul_left_Iio_real (g : ℝ → ℝ) (a c : ℝ) (hc : 0 < c) :
    (∫ x in Iio a, g (c*x)) = c⁻¹*(∫ x in Iio (c*a), g x) := by
  rw [← integral_indicator measurableSet_Iio,← integral_indicator measurableSet_Iio,
    ← abs_of_pos (inv_pos.mpr hc),← smul_eq_mul,← Measure.integral_comp_mul_left]
  congr
  ext x
  rw [← indicator_comp_right,preimage_const_mul_Iio₀ _ hc,mul_div_cancel_left₀ _ hc.ne',Function.comp_def]

theorem psi_integral_scaling (b u : ℝ) (hu : 0 < u) (f q : ℝ → ℝ) :
    (∫ r in Iio (b/Real.sqrt u), f (Real.sqrt u*r)*q r*psi (b/Real.sqrt u) r 1) =
      ∫ x in Iio b, f x*q (x/Real.sqrt u)*psi b x u := by
  have hc := Real.sqrt_pos.mpr hu
  let g := fun x => f x*q (x/Real.sqrt u)*psi b x u
  have he r : f (Real.sqrt u*r)*q r*psi (b/Real.sqrt u) r 1 = Real.sqrt u*g (Real.sqrt u*r) := by
    dsimp only [g]
    rw [psi_scaling b r u hu,mul_div_cancel_left₀ r hc.ne']
    field_simp
  simp_rw [he]
  rw [integral_const_mul,integral_comp_mul_left_Iio_real g (b/Real.sqrt u) (Real.sqrt u) hc,
    mul_div_cancel₀ b hc.ne',← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]

/-- The manuscript's spatial change of variables in the conditional
coefficient integral, retaining its precise survival conditioning. -/
theorem scaled_conditional_coefficient {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M Y : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hY : Integrable Y Q)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∃ q : ℝ → ℝ, Measurable q ∧
      (Q.restrict {ω | M ω ≤ b/Real.sqrt u})[Y | MeasurableSpace.comap X inferInstance] = q ∘ X ∧
      ∀ f : ℝ → ℝ, Measurable f →
        Integrable (fun ω => f (Real.sqrt u*X ω)*Y ω) (Q.restrict {ω | M ω ≤ b/Real.sqrt u}) →
        (∫ ω in {ω | Real.sqrt u*M ω ≤ b}, f (Real.sqrt u*X ω)*Y ω ∂Q) =
          ∫ x in Iio b, f x*q (x/Real.sqrt u)*psi b x u := by
  have hc := Real.sqrt_pos.mpr hu
  obtain ⟨q,hq,he,h⟩ := limit_conditional_coefficient P Q B X M Y hX hM hY hlaw
    (b/Real.sqrt u) (div_pos hb hc)
  refine ⟨q,hq,he,?_⟩
  intro f hf hfi
  have hs : {ω | Real.sqrt u*M ω ≤ b} = {ω | M ω ≤ b/Real.sqrt u} := by
    ext ω
    change Real.sqrt u*M ω ≤ b ↔ M ω ≤ b/Real.sqrt u
    rw [le_div_iff₀ hc,mul_comm]
  rw [hs,h (fun x => f (Real.sqrt u*x)) (hf.comp (measurable_const.mul measurable_id)) hfi]
  simp_rw [← psi_at_one]
  exact psi_integral_scaling b u hu f q

end BarrierManuscript
#print axioms BarrierManuscript.integral_comp_mul_left_Iio_real
#print axioms BarrierManuscript.psi_integral_scaling
#print axioms BarrierManuscript.scaled_conditional_coefficient
