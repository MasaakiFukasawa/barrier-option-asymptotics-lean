import ManuscriptDriftFubini
import ManuscriptRemainder

open MeasureTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem full_drift_point_bound (e h x y g A : ℝ)
    (h₀ : |g| ≤ A) (h₁ : |x| * |g| ≤ A) (h₂ : x^2*|g| ≤ A) :
    |g*((1+e*x)^2*(1+h*y)-1)| ≤
      A*(2+2*|e|+e^2)+A*(1+2*|e|+e^2)*|h| * |y| := by
  have he : |1+e*x| ≤ 1+|e| * |x| := by simpa only [abs_one,abs_mul] using abs_add_le (1:ℝ) (e*x)
  have he2 : |g| * |1+e*x|^2 ≤ A*(1+2*|e|+e^2) := by
    have hs : |1+e*x|^2 ≤ (1+|e| * |x|)^2 := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr he
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg g)
    have h1 := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2*|e| by positivity)
    have h2 := mul_le_mul_of_nonneg_left h₂ (sq_nonneg e)
    have hsq : (1+|e| * |x|)^2 = 1+2*|e| * |x|+e^2*x^2 := by
      rw [add_sq,mul_pow,sq_abs,sq_abs]
      ring
    rw [hsq] at hm
    nlinarith
  have hy : |1+h*y| ≤ 1+|h| * |y| := by simpa only [abs_one,abs_mul] using abs_add_le (1:ℝ) (h*y)
  have hA : 0 ≤ A := (abs_nonneg _).trans h₀
  have hprod := mul_le_mul he2 hy (abs_nonneg _) (by positivity : 0 ≤ A*(1+2*|e|+e^2))
  have hs := mul_le_mul_of_nonneg_left (abs_sub ((1+e*x)^2*(1+h*y)) 1) (abs_nonneg g)
  simp only [abs_mul,abs_pow,abs_one] at hs ⊢
  nlinarith

/-- Integrability of the entire Ito drift, rather than just its remainder.
Gaussian weighted bounds require only the first absolute volatility moment. -/
theorem full_drift_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X G Y : Ω → ℝ) (e h A : ℝ)
    (hX : AEStronglyMeasurable X P) (hG : AEStronglyMeasurable G P) (hY : Integrable Y P)
    (h₀ : ∀ᵐ ω ∂P, |G ω| ≤ A) (h₁ : ∀ᵐ ω ∂P, |X ω| * |G ω| ≤ A)
    (h₂ : ∀ᵐ ω ∂P, (X ω)^2*|G ω| ≤ A) :
    Integrable (fun ω => G ω*((1+e*X ω)^2*(1+h*Y ω)-1)) P ∧
    (∫ ω, |G ω*((1+e*X ω)^2*(1+h*Y ω)-1)| ∂P) ≤
      A*(2+2*|e|+e^2)+A*(1+2*|e|+e^2)*|h| *(∫ ω, |Y ω| ∂P) := by
  let f := fun ω => G ω*((1+e*X ω)^2*(1+h*Y ω)-1)
  let q := fun ω => A*(2+2*|e|+e^2)+A*(1+2*|e|+e^2)*|h| * |Y ω|
  have hiq : Integrable q P := (integrable_const _).add (hY.abs.const_mul _)
  have hm : AEStronglyMeasurable f P := hG.mul
    (((aestronglyMeasurable_const.add (hX.const_mul e)).pow 2).mul
      (aestronglyMeasurable_const.add (hY.aestronglyMeasurable.const_mul h)) |>.sub aestronglyMeasurable_const)
  have hb : ∀ᵐ ω ∂P, ‖f ω‖ ≤ q ω := by
    filter_upwards [h₀,h₁,h₂] with ω h0 h1 h2
    exact full_drift_point_bound e h (X ω) (Y ω) (G ω) A h0 h1 h2
  have hi := hiq.mono' hm hb
  refine ⟨hi,?_⟩
  have he : (∫ ω, q ω ∂P) = A*(2+2*|e|+e^2)+A*(1+2*|e|+e^2)*|h| *(∫ ω, |Y ω| ∂P) := by
    rw [show q = (fun ω => A*(2+2*|e|+e^2)+A*(1+2*|e|+e^2)*|h| * |Y ω|) from rfl,
      integral_add (integrable_const _) (hY.abs.const_mul _),integral_const_mul]
    simp [integral_const_mul]
  rw [← he]
  exact integral_mono_ae hi.abs hiq hb


/-- Joint integrability of the complete drift from the manuscript's Gaussian
bounds and a uniform first absolute volatility moment. -/
theorem full_drift_joint_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X G Y : Ω × ℝ → ℝ)
    (e h A L : ℝ) (hA : 0 ≤ A)
    (hXm : AEStronglyMeasurable X (P.prod (volume.restrict (Ioo 0 1))))
    (hGm : AEStronglyMeasurable G (P.prod (volume.restrict (Ioo 0 1))))
    (hYm : AEStronglyMeasurable Y (P.prod (volume.restrict (Ioo 0 1))))
    (hXs : ∀ s ∈ Ioo (0:ℝ) 1, AEStronglyMeasurable (fun ω => X (ω,s)) P)
    (hGs : ∀ s ∈ Ioo (0:ℝ) 1, AEStronglyMeasurable (fun ω => G (ω,s)) P)
    (hYs : ∀ s ∈ Ioo (0:ℝ) 1, Integrable (fun ω => Y (ω,s)) P)
    (hYL : ∀ s ∈ Ioo (0:ℝ) 1, (∫ ω, |Y (ω,s)| ∂P) ≤ L)
    (hb : ∀ s ∈ Ioo (0:ℝ) 1, ∀ j : ℕ, j ≤ 2 →
      ∀ᵐ ω ∂P, |X (ω,s)|^j*|G (ω,s)| ≤ A/Real.sqrt (1-s)) :
    Integrable (fun z => G z*((1+e*X z)^2*(1+h*Y z)-1))
      (P.prod (volume.restrict (Ioo 0 1))) := by
  let f := fun z => G z*((1+e*X z)^2*(1+h*Y z)-1)
  have hs s (hu : s ∈ Ioo (0:ℝ) 1) := full_drift_L1 P
    (fun ω => X (ω,s)) (fun ω => G (ω,s)) (fun ω => Y (ω,s)) e h (A/Real.sqrt (1-s))
    (hXs s hu) (hGs s hu) (hYs s hu)
    (by simpa only [pow_zero,one_mul] using hb s hu 0 (by norm_num))
    (by simpa only [pow_one] using hb s hu 1 (by norm_num))
    (by simpa only [sq_abs] using hb s hu 2 le_rfl)
  have hm : AEStronglyMeasurable f (P.prod (volume.restrict (Ioo 0 1))) := hGm.mul
    (((aestronglyMeasurable_const.add (hXm.const_mul e)).pow 2).mul
      (aestronglyMeasurable_const.add (hYm.const_mul h)) |>.sub aestronglyMeasurable_const)
  apply (singular_drift_fubini P f
    (A*(2+2*|e|+e^2)+A*(1+2*|e|+e^2)*|h| * L) hm (fun s hu => (hs s hu).1) ?_).1
  intro s hu
  have hpos : 0 < Real.sqrt (1-s) := Real.sqrt_pos.mpr (sub_pos.mpr hu.2)
  have hc : 0 ≤ (A/Real.sqrt (1-s))*(1+2*|e|+e^2)*|h| := by positivity
  have hmL := mul_le_mul_of_nonneg_left (hYL s hu) hc
  calc
    _ ≤ (A/Real.sqrt (1-s))*(2+2*|e|+e^2)+
        (A/Real.sqrt (1-s))*(1+2*|e|+e^2)*|h| *(∫ ω, |Y (ω,s)| ∂P) := (hs s hu).2
    _ ≤ (A/Real.sqrt (1-s))*(2+2*|e|+e^2)+
        (A/Real.sqrt (1-s))*(1+2*|e|+e^2)*|h| * L := add_le_add le_rfl hmL
    _ = _ := by ring

end BarrierManuscript
#print axioms BarrierManuscript.full_drift_point_bound
#print axioms BarrierManuscript.full_drift_L1

#print axioms BarrierManuscript.full_drift_joint_integrable
