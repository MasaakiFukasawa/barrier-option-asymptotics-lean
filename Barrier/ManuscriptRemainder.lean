import ManuscriptGaussianBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- Gaussian spatial weights absorb powers of X. Only an L1 moment of Y
is required, not an Lp moment or a mixed moment of X and Y. -/
theorem weighted_kernel_L1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X G Y : Ω → ℝ) (j : ℕ) (A : ℝ)
    (hX : AEStronglyMeasurable X P) (hG : AEStronglyMeasurable G P)
    (hY : Integrable Y P)
    (hb : ∀ᵐ ω ∂P, |X ω|^j*|G ω| ≤ A) :
    Integrable (fun ω => X ω^j*G ω*Y ω) P ∧
    |∫ ω, X ω^j*G ω*Y ω ∂P| ≤ A*(∫ ω, |Y ω| ∂P) := by
  have hnorm : ∀ᵐ ω ∂P, ‖X ω^j*G ω*Y ω‖ ≤ A*|Y ω| := by
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow] using
      mul_le_mul_of_nonneg_right hω (abs_nonneg (Y ω))
  have hy : Integrable (fun ω => |Y ω|) P := by
    simpa only [Real.norm_eq_abs] using hY.norm
  have hi := (hy.const_mul A).mono' (((hX.pow j).mul hG).mul hY.aestronglyMeasurable) hnorm
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, ‖X ω^j*G ω*Y ω‖ ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => X ω^j*G ω*Y ω) (μ := P)
    _ ≤ ∫ ω, A*|Y ω| ∂P := integral_mono_ae hi.norm (hy.const_mul A) hnorm
    _ = _ := integral_const_mul _ _

noncomputable def expansionRemainder (e h x y : ℝ) : ℝ :=
  (1+e*x)^2*(1+h*y)-1-2*e*x-h*y

theorem expansionRemainder_eq (e h x y : ℝ) :
    expansionRemainder e h x y = e^2*x^2+2*e*h*x*y+e^2*h*x^2*y := by
  unfold expansionRemainder; ring

/-- A quantitative expectation bound for precisely the three discarded terms
in the main theorem. The actual expectation is estimated, not postulated. -/
theorem remainder_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X G Y : Ω → ℝ) (A e h : ℝ)
    (hX : AEStronglyMeasurable X P) (hG : AEStronglyMeasurable G P)
    (hY : Integrable Y P)
    (hb1 : ∀ᵐ ω ∂P, |X ω| *|G ω| ≤ A)
    (hb2 : ∀ᵐ ω ∂P, |X ω|^2*|G ω| ≤ A) :
    Integrable (fun ω => G ω*expansionRemainder e h (X ω) (Y ω)) P ∧
    |∫ ω, G ω*expansionRemainder e h (X ω) (Y ω) ∂P| ≤
      e^2*A+(|2*e*h|+|e^2*h|)*A*(∫ ω, |Y ω| ∂P) := by
  obtain ⟨hi0,h0⟩ := weighted_kernel_L1 P X G (fun _ => 1) 2 A hX hG
    (integrable_const 1) hb2
  obtain ⟨hi1,h1⟩ := weighted_kernel_L1 P X G Y 1 A hX hG hY (by simpa using hb1)
  obtain ⟨hi2,h2⟩ := weighted_kernel_L1 P X G Y 2 A hX hG hY hb2
  have he (ω) : G ω*expansionRemainder e h (X ω) (Y ω) =
      e^2*(X ω^2*G ω*1)+(2*e*h)*(X ω^1*G ω*Y ω)+
        (e^2*h)*(X ω^2*G ω*Y ω) := by rw [expansionRemainder_eq]; ring
  have hi : Integrable (fun ω => e^2*(X ω^2*G ω*1)+(2*e*h)*(X ω^1*G ω*Y ω)+
      (e^2*h)*(X ω^2*G ω*Y ω)) P :=
    ((hi0.const_mul (e^2)).add (hi1.const_mul (2*e*h))).add
    (hi2.const_mul (e^2*h))
  have hs : Integrable (fun ω => e^2*(X ω^2*G ω*1)+(2*e*h)*(X ω^1*G ω*Y ω)) P :=
    (hi0.const_mul (e^2)).add (hi1.const_mul (2*e*h))
  have hi2' : Integrable (fun ω => (e^2*h)*(X ω^2*G ω*Y ω)) P := hi2.const_mul _
  constructor
  · simpa only [Pi.add_apply, ← he] using hi
  · simp_rw [he]
    rw [integral_add hs hi2',
      integral_add (hi0.const_mul _) (hi1.const_mul _)]
    simp_rw [integral_const_mul]
    have ht := (abs_add_le
      (e^2*(∫ ω, X ω^2*G ω*1 ∂P)+(2*e*h)*(∫ ω, X ω^1*G ω*Y ω ∂P))
      ((e^2*h)*(∫ ω, X ω^2*G ω*Y ω ∂P))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    simp only [abs_mul, abs_of_nonneg (sq_nonneg e)] at ht
    simp only [abs_one, integral_const, probReal_univ, smul_eq_mul, mul_one] at h0
    have h0' := mul_le_mul_of_nonneg_left h0 (sq_nonneg e)
    have h1' := mul_le_mul_of_nonneg_left h1 (abs_nonneg (2*e*h))
    have h2' := mul_le_mul_of_nonneg_left h2 (abs_nonneg (e^2*h))
    simp only [abs_mul, abs_of_nonneg (sq_nonneg e), mul_one] at ht h0' h1' h2' ⊢
    nlinarith [ht, h0', h1', h2']

theorem bounded_multiplier_vanishes (a z : ℕ → ℝ) (C : ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hz : ∀ n, |z n| ≤ C) :
    Tendsto (fun n => a n*z n) atTop (𝓝 0) := by
  have h : Tendsto (fun n => |a n*z n|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_)
      (by simpa using ha.abs.mul_const C)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hz n) (abs_nonneg _)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using h)

/-- Little-o bookkeeping for the three integrated remainder coefficients.
Their bounds are the output of the Gaussian/L1 estimates. This proves the
vanishing of the normalized remainder even at H=1/2 (indeed for H<1). -/
theorem normalized_remainder_vanishes (θ J₀ J₁ J₂ : ℕ → ℝ) (v₀ H C : ℝ)
    (hθ : Tendsto θ atTop (𝓝 0)) (hpos : ∀ n, 0 < θ n)
    (hv : 0 ≤ v₀) (hH : H < 1)
    (h₀ : ∀ n, |J₀ n| ≤ C) (h₁ : ∀ n, |J₁ n| ≤ C) (h₂ : ∀ n, |J₂ n| ≤ C) :
    Tendsto (fun n => ((Real.sqrt (v₀*θ n))^2*J₀ n +
      2*Real.sqrt (v₀*θ n)*(θ n)^H*J₁ n +
      (Real.sqrt (v₀*θ n))^2*(θ n)^H*J₂ n)/(θ n)^H) atTop (𝓝 0) := by
  have ha : Tendsto (fun n => v₀*(θ n)^(1-H)) atTop (𝓝 0) := by
    simpa using (hθ.rpow_const_nhds_zero (by linarith : 0 < 1-H)).const_mul v₀
  have hb : Tendsto (fun n => 2*Real.sqrt (v₀*θ n)) atTop (𝓝 0) := by
    simpa using ((hθ.const_mul v₀).sqrt).const_mul 2
  have hc : Tendsto (fun n => v₀*θ n) atTop (𝓝 0) := by
    simpa using hθ.const_mul v₀
  have h := ((bounded_multiplier_vanishes _ J₀ C ha h₀).add
    (bounded_multiplier_vanishes _ J₁ C hb h₁)).add
    (bounded_multiplier_vanishes _ J₂ C hc h₂)
  simp only [add_zero] at h
  apply h.congr
  intro n
  rw [Real.sq_sqrt (mul_nonneg hv (hpos n).le), Real.rpow_sub (hpos n), Real.rpow_one]
  have hn : (θ n)^H ≠ 0 := (Real.rpow_pos_of_pos (hpos n) H).ne'
  field_simp

end BarrierManuscript

#print axioms BarrierManuscript.weighted_kernel_L1
#print axioms BarrierManuscript.expansionRemainder_eq
#print axioms BarrierManuscript.remainder_expectation_bound
#print axioms BarrierManuscript.bounded_multiplier_vanishes
#print axioms BarrierManuscript.normalized_remainder_vanishes
