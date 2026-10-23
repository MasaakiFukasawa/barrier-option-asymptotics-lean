import ManuscriptBrownianCDF
import ManuscriptPathLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

theorem pathMaximum_attained {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : C(K,ℝ)) : ∃ t, f t = pathMaximum f :=
  (isCompact_range f.continuous).sSup_mem (range_nonempty f)

noncomputable def brownianMaximum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1) (ω : Ω) : ℝ :=
  pathMaximum (continuousPath (brownianPrefix B) (brownian_prefix_regular P B).2 ω)

theorem brownianMaximum_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) :
    Measurable (brownianMaximum B) :=
  pathMaximum_lipschitz.continuous.measurable.comp
    (continuous_path_measurable (brownianPrefix B) (brownian_prefix_regular P B).2
      (fun t => ((brownian_prefix_regular P B).1 t).mono (B.le t) le_rfl))

theorem brownian_maximum_endpoint_event {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (ω : Ω) (h₀ : brownianPrefix B ⊥ ω < b) :
    brownianMaximum B ω < b ↔ brownianBarrierEndpoint B b ω < b := by
  let X := brownianPrefix B
  have hc := (brownian_prefix_regular P B).2
  let f := continuousPath X hc ω
  have hle t : X t ω ≤ brownianMaximum B ω := le_csSup (path_range_bddAbove f) (mem_range_self t)
  constructor
  · intro h
    exact (hle _).trans_lt h
  · intro h
    have hall t : X t ω < b := by
      by_contra hn
      obtain ⟨r,hr⟩ := intermediate_value_univ (⊥ : HalfClosedTime) t (hc ω)
        (show b ∈ Icc (X ⊥ ω) (X t ω) from ⟨h₀.le,le_of_not_gt hn⟩)
      have hhit : ∃ r : HalfClosedTime, r ≤ realTimeClamp 1 ∧ X r ω = b := by
        refine ⟨min (realTimeClamp 1) r,min_le_left _ _,?_⟩
        simpa only [X,brownianPrefix,← min_assoc,min_self] using hr
      have he := (cappedBarrier_hit_iff X hc b ω).mpr hhit
      change brownianBarrierEndpoint B b ω = b at he
      exact (ne_of_lt h) he
    obtain ⟨t,ht⟩ := pathMaximum_attained f
    rw [show brownianMaximum B ω = f t from ht.symm]
    exact hall t

theorem brownian_maximum_cdf {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (hb : 0 < b) :
    P.real {ω | brownianMaximum B ω < b} = 2*normalCDF b-1 := by
  have he : {ω | brownianMaximum B ω < b} =ᵐ[P] {ω | brownianBarrierEndpoint B b ω < b} := by
    filter_upwards [(B.martingale 0).initial P B.F] with ω hω
    apply propext
    exact brownian_maximum_endpoint_event P B b ω (by
      simpa only [brownianPrefix,min_bot_right,hω,Pi.zero_apply] using hb)
  rw [measureReal_congr he,brownian_strict_survival P B b hb]

end BarrierManuscript
#print axioms BarrierManuscript.pathMaximum_attained
#print axioms BarrierManuscript.brownianMaximum_measurable
#print axioms BarrierManuscript.brownian_maximum_endpoint_event
#print axioms BarrierManuscript.brownian_maximum_cdf
