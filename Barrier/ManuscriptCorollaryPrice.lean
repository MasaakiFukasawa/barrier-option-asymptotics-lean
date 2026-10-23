import ManuscriptBlackScholesPhysical
import ManuscriptCorollaryCoefficient

open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The second price representation in Corollary 1 follows from its first
representation and the independently verified Black--Scholes expansion. -/
theorem corollary_price_reformulation (price bs base θ : ℕ → ℝ) (S v a g : ℝ)
    (hv : 0 < v)
    (hp : Tendsto (fun n => (price n-bs n-(a/2)*g*Real.sqrt v*S*θ n)/θ n) atTop (𝓝 0))
    (hb : Tendsto (fun n => (bs n-base n-S*v*θ n*g)/θ n) atTop (𝓝 0)) :
    Tendsto (fun n => (price n-bs n-a/(2*Real.sqrt v)*(bs n-base n))/θ n) atTop (𝓝 0) := by
  have h := hp.sub (hb.const_mul (a/(2*Real.sqrt v)))
  simp only [mul_zero,sub_zero] at h
  apply h.congr
  intro n
  have hs := Real.sq_sqrt hv.le
  have hn := (Real.sqrt_pos.mpr hv).ne'
  field_simp
  congr 1
  linear_combination -(a*g*S*θ n)*hs

end BarrierManuscript
#print axioms BarrierManuscript.corollary_price_reformulation
