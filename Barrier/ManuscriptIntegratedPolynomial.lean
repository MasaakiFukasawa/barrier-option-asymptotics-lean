import ManuscriptDriftFubini
import ManuscriptDriftBounds

open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Joint integrability and the time-integrated coefficient bound follow from
Gaussian spatial domination and a first moment of the volatility coordinate. -/
theorem joint_weighted_kernel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X G Y : Ω × ℝ → ℝ)
    (hX : Measurable X) (hG : Measurable G) (hY : Measurable Y)
    (j : ℕ) (A L : ℝ) (hA : 0 ≤ A)
    (hYs : ∀ s ∈ Ioo (0:ℝ) 1, Integrable (fun ω => Y (ω,s)) P)
    (hYL : ∀ s ∈ Ioo (0:ℝ) 1, (∫ ω, |Y (ω,s)| ∂P) ≤ L)
    (hb : ∀ s ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂P, |X (ω,s)|^j*|G (ω,s)| ≤ A/Real.sqrt (1-s)) :
    Integrable (fun z => X z^j*G z*Y z) (P.prod (volume.restrict (Ioo 0 1))) ∧
    |∫ s in (0:ℝ)..1, ∫ ω, X (ω,s)^j*G (ω,s)*Y (ω,s) ∂P| ≤ 2*(A*L) := by
  have hm := ((hX.pow_const j).mul hG).mul hY
  have hs s (hu : s ∈ Ioo (0:ℝ) 1) := weighted_kernel_L1 P
    (fun ω => X (ω,s)) (fun ω => G (ω,s)) (fun ω => Y (ω,s)) j (A/Real.sqrt (1-s))
    ((hX.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    ((hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) (hYs s hu) (hb s hu)
  have hnorm s (hu : s ∈ Ioo (0:ℝ) 1) :
      (∫ ω, |X (ω,s)^j*G (ω,s)*Y (ω,s)| ∂P) ≤ (A*L)/Real.sqrt (1-s) := by
    calc
      _ ≤ ∫ ω, (A/Real.sqrt (1-s))*|Y (ω,s)| ∂P :=
        integral_mono_ae (hs s hu).1.abs ((hYs s hu).abs.const_mul _) (by
          filter_upwards [hb s hu] with ω hω
          simpa only [abs_mul,abs_pow] using mul_le_mul_of_nonneg_right hω (abs_nonneg (Y (ω,s))))
      _ = (A/Real.sqrt (1-s))*(∫ ω, |Y (ω,s)| ∂P) := integral_const_mul _ _
      _ ≤ (A/Real.sqrt (1-s))*L := mul_le_mul_of_nonneg_left (hYL s hu) (by positivity)
      _ = _ := by ring
  refine ⟨(singular_drift_fubini P _ (A*L) hm.aestronglyMeasurable
    (fun s hu => (hs s hu).1) hnorm).1,?_⟩
  exact (integrated_weighted_kernel_bound P (fun s ω => X (ω,s)) (fun s ω => G (ω,s))
    (fun s ω => Y (ω,s)) j A L hA
    (fun s _ => (hX.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (fun s _ => (hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    hYs hYL hb hm.aestronglyMeasurable.prod_swap.integral_prod_right').2

/-- Exact integration of all five polynomial terms. The integrability of each
term is explicit; this lemma never distributes a nonintegrable sum. -/
theorem polynomial_integral_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X G Y : Ω → ℝ) (e h : ℝ)
    (hA : Integrable (fun z => X z*G z) μ)
    (hB : Integrable (fun z => G z*Y z) μ)
    (hJ₀ : Integrable (fun z => X z^2*G z) μ)
    (hJ₁ : Integrable (fun z => X z*G z*Y z) μ)
    (hJ₂ : Integrable (fun z => X z^2*G z*Y z) μ) :
    (∫ z, G z*((1+e*X z)^2*(1+h*Y z)-1) ∂μ) =
      2*e*(∫ z, X z*G z ∂μ)+h*(∫ z, G z*Y z ∂μ)+
      e^2*(∫ z, X z^2*G z ∂μ)+2*e*h*(∫ z, X z*G z*Y z ∂μ)+
      e^2*h*(∫ z, X z^2*G z*Y z ∂μ) := by
  have he z : G z*((1+e*X z)^2*(1+h*Y z)-1) =
      2*e*(X z*G z)+h*(G z*Y z)+e^2*(X z^2*G z)+
      2*e*h*(X z*G z*Y z)+e^2*h*(X z^2*G z*Y z) := by ring
  simp_rw [he]
  have ha : Integrable (fun z => 2*e*(X z*G z)) μ := hA.const_mul _
  have hb : Integrable (fun z => h*(G z*Y z)) μ := hB.const_mul _
  have h0 : Integrable (fun z => e^2*(X z^2*G z)) μ := hJ₀.const_mul _
  have h1 : Integrable (fun z => 2*e*h*(X z*G z*Y z)) μ := hJ₁.const_mul _
  have h2 : Integrable (fun z => e^2*h*(X z^2*G z*Y z)) μ := hJ₂.const_mul _
  have hab : Integrable (fun z => 2*e*(X z*G z)+h*(G z*Y z)) μ := ha.add hb
  have hab0 : Integrable (fun z => 2*e*(X z*G z)+h*(G z*Y z)+e^2*(X z^2*G z)) μ := hab.add h0
  have hab01 : Integrable (fun z => 2*e*(X z*G z)+h*(G z*Y z)+e^2*(X z^2*G z)+2*e*h*(X z*G z*Y z)) μ := hab0.add h1
  rw [integral_add hab01 h2,integral_add hab0 h1,integral_add hab h0,integral_add ha hb]
  simp only [integral_const_mul]

end BarrierManuscript
#print axioms BarrierManuscript.joint_weighted_kernel
#print axioms BarrierManuscript.polynomial_integral_decomposition
