import ManuscriptMaximumNoAtom

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The maximum used in the functional CLT is exactly the maximum in the
proved Brownian barrier formula, despite the different time-space encodings. -/
theorem brownian_maximum_encoding {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (ω : Ω) :
    pathMaximum (pathRestriction 1 (brownianContinuousPath B ω)) = brownianMaximum B ω := by
  unfold pathMaximum brownianMaximum
  congr 1
  ext y
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨realTimeClamp (r.val : ℝ),?_⟩
    change B.W 0 (min (realTimeClamp 1) (realTimeClamp (r.val : ℝ))) ω = y
    rw [min_eq_right (real_time_clamp_mono (show (r.val : ℝ) ≤ 1 from r.property.2))]
    exact hr
  · rintro ⟨t,ht⟩
    let r := finitePrefixTime 1 (by norm_num) t
    let n : ℝ≥0 := ⟨r.val,r.property.1⟩
    refine ⟨⟨n,⟨bot_le,show n ≤ 1 from r.property.2⟩⟩,?_⟩
    change B.W 0 (realTimeClamp r.val) ω = y
    rw [finite_prefix_time_clamp 1 (by norm_num) le_top]
    exact ht

theorem brownian_clt_maximum_noatom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂P, pathMaximum (pathRestriction 1 (brownianContinuousPath B ω)) ≠ b := by
  simpa only [brownian_maximum_encoding] using brownian_maximum_noatom P B b hb

theorem brownian_scaled_maximum_noatom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∀ᵐ ω ∂P, Real.sqrt u*pathMaximum (pathRestriction 1 (brownianContinuousPath B ω)) ≠ b := by
  filter_upwards [brownian_clt_maximum_noatom P B (b/Real.sqrt u) (div_pos hb (Real.sqrt_pos.mpr hu))] with ω hω
  intro he
  apply hω
  apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr hu))).mpr
  simpa only [mul_comm] using he

end BarrierManuscript
#print axioms BarrierManuscript.brownian_maximum_encoding
#print axioms BarrierManuscript.brownian_clt_maximum_noatom
#print axioms BarrierManuscript.brownian_scaled_maximum_noatom
