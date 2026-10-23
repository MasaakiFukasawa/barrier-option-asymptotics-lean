import ManuscriptBlackScholes
import ManuscriptTerminal

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem bsKilledPut_vega (B K S w : ℝ) (hS : S ≠ 0) (hB : B ≠ 0) (hw : w ≠ 0) :
    HasDerivAt (bsKilledPut B K S)
      (S*phi ((Real.log K-Real.log S)/w-w/2)-B*phi ((Real.log K-Real.log (B^2/S))/w-w/2)) w := by
  convert (bsStockPut_vega K S w hw).sub ((bsStockPut_vega K (B^2/S) w hw).const_mul (S/B)) using 1
  · rfl
  · field_simp

theorem bsKilledPut_volatility_stability (B K S w₁ w₂ : ℝ)
    (hS : 0 < S) (hB : 0 < B) (h₁ : 0 < w₁) (h₂ : 0 < w₂) :
    |bsKilledPut B K S w₂-bsKilledPut B K S w₁| ≤ (S+B)*normalizer*|w₂-w₁| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Ioi (0:ℝ)) (f := bsKilledPut B K S)
    (f' := fun w => S*phi ((Real.log K-Real.log S)/w-w/2)-B*phi ((Real.log K-Real.log (B^2/S))/w-w/2))
    (fun w hw => (bsKilledPut_vega B K S w hS.ne' hB.ne' hw.ne').hasDerivWithinAt)
    (C := (S+B)*normalizer) (fun w _ => ?_) (convex_Ioi 0) h₁ h₂
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs]
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (mul_nonneg hS.le (phi_nonneg _)),abs_of_nonneg (mul_nonneg hB.le (phi_nonneg _))]
    nlinarith [mul_le_mul_of_nonneg_left (phi_le ((Real.log K-Real.log S)/w-w/2)) hS.le,
      mul_le_mul_of_nonneg_left (phi_le ((Real.log K-Real.log (B^2/S))/w-w/2)) hB.le]

/-- A volatility error o(theta) changes any uniformly Lipschitz family of
prices by o(theta). This separates the price argument from the cited
ATM-implied-volatility asymptotic. -/
theorem volatility_replacement (price : ℕ → ℝ → ℝ) (w v θ : ℕ → ℝ) (C : ℝ)
    (hp : ∀ n, 0 < θ n)
    (hb : ∀ n, |price n (v n)-price n (w n)| ≤ C*|v n-w n|)
    (hv : Tendsto (fun n => (v n-w n)/θ n) atTop (𝓝 0)) :
    Tendsto (fun n => (price n (v n)-price n (w n))/θ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => ?_) (by simpa only [norm_zero,mul_zero] using hv.norm.const_mul C)
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (hp n)]
  have hh := div_le_div_of_nonneg_right (hb n) (hp n).le
  simpa only [Real.norm_eq_abs,abs_div,abs_of_pos (hp n),mul_div_assoc] using hh

end BarrierManuscript
#print axioms BarrierManuscript.bsKilledPut_vega
#print axioms BarrierManuscript.bsKilledPut_volatility_stability
#print axioms BarrierManuscript.volatility_replacement
