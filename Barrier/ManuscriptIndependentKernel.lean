import ManuscriptBrownianSegments
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Bounded measurable tests of independent random vectors can be evaluated
using two independent copies. This supplies the Fubini step in the killed
transition-kernel calculation. -/
theorem independent_kernel_integral {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (Y : Ω → F)
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (f : E × F → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ q, |f q| ≤ C) :
    (∫ ω, f (X ω,Y ω) ∂P) = ∫ ω, ∫ ω', f (X ω,Y ω') ∂P ∂P := by
  have hi : Integrable f ((P.map X).prod (P.map Y)) := by
    apply (integrable_const C).mono' hf.aestronglyMeasurable
    exact ae_of_all _ fun q => by simpa only [Real.norm_eq_abs] using hb q
  have hm : AEStronglyMeasurable (fun x => ∫ y, f (x,y) ∂P.map Y) (P.map X) :=
    hf.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  rw [← integral_map (hX.prodMk hY).aemeasurable hf.aestronglyMeasurable,
    hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,integral_prod f hi,
    integral_map hX.aemeasurable hm]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => integral_map hY.aemeasurable
    ((hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)

end BarrierManuscript
#print axioms BarrierManuscript.independent_kernel_integral
