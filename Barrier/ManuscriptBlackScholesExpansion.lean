import ManuscriptBlackScholesStrict

open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Second-order expansion of the closed barrier formula, allowing an arbitrary
convergent normalized total-volatility curve. -/
theorem bsKilledPut_expansion (b k : ℝ) (e w : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hw : Tendsto w atTop (𝓝 1))
    (hen : ∀ n, e n ≠ 0) :
    Tendsto (fun n =>
      (bsKilledPut (1+e n*b) (1+e n*k) 1 (e n*w n) -
        e n*killedPut b k 0 (w n) - (e n)^2*gamma b k)/(e n)^2)
      atTop (𝓝 0) := by
  have hb : ∀ᶠ n in atTop, 0 < 1+e n*b :=
    (show Tendsto (fun n => 1+e n*b) atTop (𝓝 1) by simpa using (he.mul_const b).const_add 1).eventually (eventually_gt_nhds zero_lt_one)
  have hk : ∀ᶠ n in atTop, 0 < 1+e n*k :=
    (show Tendsto (fun n => 1+e n*k) atTop (𝓝 1) by simpa using (he.mul_const k).const_add 1).eventually (eventually_gt_nhds zero_lt_one)
  apply (bsBarrierNormalized_expansion b k e w he hw).congr'
  filter_upwards [hb,hk] with n hbn hkn
  rw [← bsBarrierNormalized_formula b k (e n) (w n) (hen n) hbn hkn]
  field_simp

end BarrierManuscript
#print axioms BarrierManuscript.bsKilledPut_expansion
