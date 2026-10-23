import ManuscriptBrownianWeightedTwoStep

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem integral_translate_Iio (g : ℝ → ℝ) (b a : ℝ) :
    (∫ y in Iio (b-a), g (a+y)) = ∫ x in Iio b, g x := by
  classical
  rw [← integral_indicator measurableSet_Iio,← integral_indicator measurableSet_Iio]
  calc
    _ = ∫ y, (Iio b).indicator g (a+y) := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        have h : y < b-a ↔ a+y < b := by constructor <;> intro h <;> linarith
        simp only [Set.indicator,mem_Iio,h]
    _ = _ := integral_add_left_eq_self _ a

theorem shifted_killed_kernel (f : ℝ × ℝ → ℝ) (b x d : ℝ) :
    (∫ y in Iio (b-x), f (x,x+y)*psi (b-x) y d) =
      ∫ y in Iio b, f (x,y)*psi (b-x) (y-x) d := by
  rw [← integral_translate_Iio (fun y => f (x,y)*psi (b-x) (y-x) d) b x]
  simp only [add_sub_cancel_left]

end BarrierManuscript
#print axioms BarrierManuscript.integral_translate_Iio
#print axioms BarrierManuscript.shifted_killed_kernel
