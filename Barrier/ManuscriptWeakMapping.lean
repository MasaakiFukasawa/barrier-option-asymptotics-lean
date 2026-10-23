import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- The almost-everywhere continuous mapping theorem, proved directly by
Portmanteau. In particular it permits barrier indicators when the limit
maximum has no atom at the barrier; no Skorokhod realization is assumed. -/
theorem distribution_ae_continuous_mapping
    {E F Ω Γ : Type*} [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → E) (Z : Γ → E) (g : E → F)
    (h : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (hg : Measurable g) (hc : ∀ᵐ ω ∂Q, ContinuousAt g (Z ω)) :
    TendstoInDistribution (fun n ω => g (X n ω)) atTop (fun ω => g (Z ω))
      (fun _ => P) Q := by
  refine ⟨fun n => hg.comp_aemeasurable (h.forall_aemeasurable n),
    hg.comp_aemeasurable h.aemeasurable_limit, ?_⟩
  apply tendsto_of_forall_isOpen_le_liminf'
  intro U hU
  let V := interior (g ⁻¹' U)
  have he : Q (Z ⁻¹' (g ⁻¹' U)) = Q (Z ⁻¹' V) := by
    apply measure_congr
    filter_upwards [hc] with ω hω
    apply propext
    change (g (Z ω) ∈ U ↔ Z ω ∈ interior (g ⁻¹' U))
    constructor
    · intro hzu
      exact mem_interior_iff_mem_nhds.mpr (hω.preimage_mem_nhds (hU.mem_nhds hzu))
    · exact fun hv => (interior_subset (s := g ⁻¹' U)) hv
  have hv := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto
    (isOpen_interior : IsOpen V)
  simp only [ProbabilityMeasure.coe_mk] at hv ⊢
  change (Q.map (g ∘ Z)) U ≤ liminf (fun n => (P.map (g ∘ X n)) U) atTop
  rw [Measure.map_apply_of_aemeasurable
    (hg.comp_aemeasurable h.aemeasurable_limit) hU.measurableSet]
  change Q (Z ⁻¹' (g ⁻¹' U)) ≤ _
  rw [he, ← Measure.map_apply_of_aemeasurable h.aemeasurable_limit isOpen_interior.measurableSet]
  refine hv.trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) isOpen_interior.measurableSet,
    Measure.map_apply_of_aemeasurable (hg.comp_aemeasurable (h.forall_aemeasurable n))
      hU.measurableSet]
  exact measure_mono (preimage_mono interior_subset)

end BarrierManuscript
#print axioms BarrierManuscript.distribution_ae_continuous_mapping
