import ManuscriptBlackScholesExpansion
import ManuscriptAsymptoticAssembly

open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem normalized_bs_baseline_expansion (b k v H : ℝ) (hv : 0 < v) (hH : H ≤ 1/2)
    (θ w : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ1 : ∀ n, θ n ≤ 1)
    (hθ : Tendsto θ atTop (𝓝 0)) (hw : Tendsto w atTop (𝓝 1)) :
    Tendsto (fun n =>
      (bsKilledPut (1+Real.sqrt (v*θ n)*b) (1+Real.sqrt (v*θ n)*k) 1 (Real.sqrt (v*θ n)*w n)/Real.sqrt (v*θ n)-
        killedPut b k 0 (w n)-Real.sqrt (v*θ n)*gamma b k)/(θ n)^H) atTop (𝓝 0) := by
  let e := fun n => Real.sqrt (v*θ n)
  have he : Tendsto e atTop (𝓝 0) := by simpa only [e,mul_zero,Real.sqrt_zero] using (hθ.const_mul v).sqrt
  have hen n : e n ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hv (hp n))).ne'
  have h := bounded_multiplier_vanishes _ (fun n => e n/(θ n)^H) (Real.sqrt v)
    (bsKilledPut_expansion b k e w he hw hen)
    (fun n => regular_scale_ratio_bound (θ n) v H (hp n) (hθ1 n) hv.le hH)
  apply h.congr
  intro n
  change _ = (bsKilledPut (1+e n*b) (1+e n*k) 1 (e n*w n)/e n-killedPut b k 0 (w n)-e n*gamma b k)/(θ n)^H
  field_simp [hen n,Real.rpow_pos_of_pos (hp n) H |>.ne']
  <;> ring

/-- Convert the normalized price error to the original monetary scale. -/
theorem physical_expansion_scaling (price bs θ : ℕ → ℝ) (S v H a : ℝ)
    (hv : 0 < v) (hp : ∀ n, 0 < θ n)
    (h : Tendsto (fun n => (price n-bs n-(θ n)^H*a)/(θ n)^H) atTop (𝓝 0)) :
    Tendsto (fun n => (S*Real.sqrt (v*θ n)*price n-S*Real.sqrt (v*θ n)*bs n-
      a*S*Real.sqrt v*(θ n)^(H+1/2))/(θ n)^(H+1/2)) atTop (𝓝 0) := by
  have hh := h.const_mul (S*Real.sqrt v)
  simp only [mul_zero] at hh
  apply hh.congr
  intro n
  simp_rw [Real.sqrt_mul hv.le,Real.sqrt_eq_rpow,Real.rpow_add (hp n)]
  have hn (p : ℝ) : (θ n)^p ≠ 0 := (Real.rpow_pos_of_pos (hp n) p).ne'
  field_simp [hn]
  <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.normalized_bs_baseline_expansion
#print axioms BarrierManuscript.physical_expansion_scaling
