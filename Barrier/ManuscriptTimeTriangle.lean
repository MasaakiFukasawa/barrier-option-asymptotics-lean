import ManuscriptWeightedPathIntegral
import ManuscriptRoughKernelTail

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem unit_triangle_row (f : ℝ → ℝ) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    (∫ s in Ioc (0:ℝ) 1, if s ≤ u then f s else 0)=∫ s in (0:ℝ)..u,f s := by
  change (∫ s in Ioc (0:ℝ) 1, (Iic u).indicator f s)=_
  rw [integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have he : Iic u ∩ Ioc (0:ℝ) 1=Ioc 0 u := by
    ext s
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · rintro ⟨h,hs,_⟩; exact ⟨hs,h⟩
    · rintro ⟨hs,h⟩; exact ⟨h,hs,h.trans hu.2⟩
  rw [he,intervalIntegral.integral_of_le hu.1]

theorem unit_triangle_column (f : ℝ → ℝ) (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
    (∫ u in Ioc (0:ℝ) 1, if s ≤ u then f u else 0)=∫ u in s..1,f u := by
  change (∫ u in Ioc (0:ℝ) 1, (Ici s).indicator f u)=_
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have he : Ici s ∩ Ioc (0:ℝ) 1=Icc s 1 := by
    ext u
    simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
    constructor
    · rintro ⟨h,_,hu⟩; exact ⟨h,hu⟩
    · rintro ⟨h,hu⟩; exact ⟨h,hs.1.trans_le h,hu⟩
  rw [he,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hs.2.le]

theorem unit_triangle_fubini (f : ℝ → ℝ → ℝ)
    (hi : Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then f p.1 p.2 else 0)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1)))) :
    (∫ u in (0:ℝ)..1, ∫ s in (0:ℝ)..u,f u s)=
      ∫ s in (0:ℝ)..1,∫ u in s..1,f u s := by
  have hf := integral_integral_swap (f := fun u s => if s ≤ u then f u s else 0) hi
  rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ u in Ioc (0:ℝ) 1,∫ s in Ioc (0:ℝ) 1,if s ≤ u then f u s else 0 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      exact (unit_triangle_row (f u) u ⟨hu.1.le,hu.2⟩).symm
    _ = ∫ s in Ioc (0:ℝ) 1,∫ u in Ioc (0:ℝ) 1,if s ≤ u then f u s else 0 := hf
    _ = _ := by
      rw [integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      exact unit_triangle_column (fun u => f u s) s hs

end BarrierManuscript
#print axioms BarrierManuscript.unit_triangle_fubini
