import ManuscriptLogRatio
import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Strict differentiability gives a uniform expansion in the first variable,
even if the second variable converges more slowly. This is the two-scale
limit required for an arbitrary continuous forward-variance curve. -/
theorem strict_increment_limit (F : ℝ × ℝ → ℝ) (D : (ℝ × ℝ) →L[ℝ] ℝ)
    (w₀ : ℝ) (hf : HasStrictFDerivAt F D (0,w₀))
    (e w : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hw : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun n => (F (e n,w n)-F (0,w n)-e n*D (1,0))/e n) atTop (𝓝 0) := by
  have hp : Tendsto (fun n => ((e n,w n),((0:ℝ),w n))) atTop (𝓝 ((0,w₀),(0,w₀))) :=
    (he.prodMk_nhds hw).prodMk_nhds (tendsto_const_nhds.prodMk_nhds hw)
  have h := (hf.isLittleO.comp_tendsto (k := fun n => ((e n,w n),(0,w n))) (l' := atTop) hp).norm_right
  have hsub n : ((e n,w n):ℝ × ℝ)-((0,w n):ℝ × ℝ) = (e n,0) := by ext <;> simp
  simp only [Function.comp_def,hsub,Prod.norm_def,norm_zero,
    max_eq_left (norm_nonneg _)] at h
  have hd n : D (e n,0) = e n*D (1,0) := by
    have heq : (e n,0) = e n • ((1,0):ℝ × ℝ) := by simp
    rw [heq,map_smul,smul_eq_mul]
  simp_rw [hd] at h
  exact h.of_norm_right.tendsto_div_nhds_zero

end BarrierManuscript
#print axioms BarrierManuscript.strict_increment_limit
