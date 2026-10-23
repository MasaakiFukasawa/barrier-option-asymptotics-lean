import ManuscriptMaximumNoAtom

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem brownian_barrier_endpoint_eq_terminal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b : ℝ) (ω : Ω) (hb : brownianBarrierEndpoint B b ω < b) :
    brownianBarrierEndpoint B b ω = B.W 0 (realTimeClamp 1) ω := by
  have ht : cappedBarrier (brownianPrefix B) b ω = 1 := by
    apply le_antisymm (cappedBarrier_range (brownianPrefix B) b ω).2
    by_contra hn
    have he := cappedBarrier_hit (brownianPrefix B) (brownian_prefix_regular P B).2 b ω (lt_of_not_ge hn)
    exact (ne_of_lt hb) he
  simp only [brownianBarrierEndpoint,ht,brownianPrefix,min_self]

/-- Reflection's sub-barrier joint distribution, derived through the killed
put formula and strike differentiation, with no reflection axiom. -/
theorem brownian_endpoint_maximum_cdf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) (hk : k < b) :
    P.real {ω | B.W 0 (realTimeClamp 1) ω < k ∧ brownianMaximum B ω ≤ b} =
      normalCDF k-normalCDF (k-2*b) := by
  have he : {ω | B.W 0 (realTimeClamp 1) ω < k ∧ brownianMaximum B ω ≤ b} =ᵐ[P]
      {ω | brownianBarrierEndpoint B b ω < k} := by
    filter_upwards [(B.martingale 0).initial P B.F,brownian_maximum_noatom P B b hb] with ω hzero hne
    apply propext
    have hevent := brownian_maximum_endpoint_event P B b ω (by
      simpa only [brownianPrefix,min_bot_right,hzero,Pi.zero_apply] using hb)
    constructor
    · rintro ⟨hW,hM⟩
      have hU := hevent.mp (lt_of_le_of_ne hM hne)
      rwa [brownian_barrier_endpoint_eq_terminal P B b ω hU]
    · intro hU
      have hU' := hU.trans hk
      exact ⟨by simpa only [brownian_barrier_endpoint_eq_terminal P B b ω hU'] using hU,
        (hevent.mpr hU').le⟩
  rw [measureReal_congr he,brownian_barrier_endpoint_cdf P B b k hb hk]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_barrier_endpoint_eq_terminal
#print axioms BarrierManuscript.brownian_endpoint_maximum_cdf
