import ManuscriptBlackScholesExpansion

open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem bsStockPut_homogeneous (S K s w : ℝ) (hS : 0 < S) (hK : 0 < K) (hs : 0 < s) :
    bsStockPut (S*K) (S*s) w = S*bsStockPut K s w := by
  unfold bsStockPut
  rw [Real.log_mul hS.ne' hK.ne',Real.log_mul hS.ne' hs.ne']
  rw [show Real.log S+Real.log K-(Real.log S+Real.log s) = Real.log K-Real.log s by ring]
  ring

theorem bsKilledPut_homogeneous (S B K s w : ℝ)
    (hS : 0 < S) (hB : 0 < B) (hK : 0 < K) (hs : 0 < s) :
    bsKilledPut (S*B) (S*K) (S*s) w = S*bsKilledPut B K s w := by
  unfold bsKilledPut
  have hr : (S*B)^2/(S*s) = S*(B^2/s) := by field_simp
  rw [hr,bsStockPut_homogeneous _ _ _ _ hS hK hs,
    bsStockPut_homogeneous _ _ _ _ hS hK (by positivity)]
  field_simp

/-- The manuscript's monetary second-order expansion, with total volatility
sqrt(v0 theta) times any curve tending to one. -/
theorem bsKilledPut_physical_expansion (S v b k : ℝ) (hS : 0 < S) (hv : 0 < v)
    (θ w : ℕ → ℝ) (hp : ∀ n, 0 < θ n)
    (hθ : Tendsto θ atTop (𝓝 0)) (hw : Tendsto w atTop (𝓝 1)) :
    Tendsto (fun n =>
      (bsKilledPut (S*(1+Real.sqrt (v*θ n)*b)) (S*(1+Real.sqrt (v*θ n)*k)) S
        (Real.sqrt (v*θ n)*w n) -
       S*Real.sqrt (v*θ n)*killedPut b k 0 (w n) - S*v*θ n*gamma b k)/θ n)
      atTop (𝓝 0) := by
  let e := fun n => Real.sqrt (v*θ n)
  have he : Tendsto e atTop (𝓝 0) := by simpa [e] using (hθ.const_mul v).sqrt
  have hen n : e n ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hv (hp n))).ne'
  have hb : ∀ᶠ n in atTop, 0 < 1+e n*b :=
    (show Tendsto (fun n => 1+e n*b) atTop (𝓝 1) by simpa using (he.mul_const b).const_add 1).eventually (eventually_gt_nhds zero_lt_one)
  have hk : ∀ᶠ n in atTop, 0 < 1+e n*k :=
    (show Tendsto (fun n => 1+e n*k) atTop (𝓝 1) by simpa using (he.mul_const k).const_add 1).eventually (eventually_gt_nhds zero_lt_one)
  have h := (bsKilledPut_expansion b k e w he hw hen).const_mul (S*v)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hb,hk] with n hbn hkn
  have he2 : (e n)^2 = v*θ n := Real.sq_sqrt (mul_pos hv (hp n)).le
  have hh := bsKilledPut_homogeneous S (1+e n*b) (1+e n*k) 1 (e n*w n) hS hbn hkn zero_lt_one
  simp only [mul_one] at hh
  change _ = (bsKilledPut (S*(1+e n*b)) (S*(1+e n*k)) S (e n*w n)-S*e n*killedPut b k 0 (w n)-S*v*θ n*gamma b k)/θ n
  rw [hh,he2]
  field_simp

end BarrierManuscript
#print axioms BarrierManuscript.bsStockPut_homogeneous
#print axioms BarrierManuscript.bsKilledPut_homogeneous
#print axioms BarrierManuscript.bsKilledPut_physical_expansion
