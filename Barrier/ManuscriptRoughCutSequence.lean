import ManuscriptRoughPathApproximation

open Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def roughUnitCut (n : ℕ) : ℝ≥0 :=
  ⟨1-1/((n:ℝ)+1), by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hh : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith⟩

theorem rough_unit_cut_lt (n : ℕ) : roughUnitCut n < 1 := by
  change 1-1/((n:ℝ)+1)<1
  have hp : 0 < 1/((n:ℝ)+1) := by positivity
  linarith

theorem rough_unit_cut_limit : Tendsto (fun n => (roughUnitCut n:ℝ)) atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1-1/((n:ℝ)+1)) atTop (𝓝 1)
  simpa only [sub_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub 1

end BarrierManuscript
#print axioms BarrierManuscript.rough_unit_cut_lt
#print axioms BarrierManuscript.rough_unit_cut_limit
