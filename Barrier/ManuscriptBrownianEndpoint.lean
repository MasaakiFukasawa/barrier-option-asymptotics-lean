import ManuscriptBrownianKilledPut
import Chapter7GridGaussianLimitLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

noncomputable def brownianPrefix {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1) : HalfClosedTime → Ω → ℝ :=
  fun t ω => B.W 0 (min (realTimeClamp 1) t) ω

noncomputable def brownianBarrierEndpoint {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1) (b : ℝ) (ω : Ω) : ℝ :=
  brownianPrefix B (realTimeClamp (cappedBarrier (brownianPrefix B) b ω)) ω

theorem brownian_prefix_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) :
    ∃ D : Ω → ℝ, Integrable D P ∧ ∀ ω t, |brownianPrefix B t ω| ≤ D ω := by
  obtain ⟨hc,hm,hn⟩ := local_energy_maximal_bound P B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) (realTimeClamp 1)
    (changed_time_finite 1 (by norm_num)) (fun _ => 1) (integrable_const 1) 1 (by norm_num)
    (ae_of_all _ fun ω => by rw [B.diagonal_clock 0 ω 1 (by norm_num)]; norm_num)
  let D := fun ω => ‖continuousPath (brownianPrefix B) hc ω‖
  have hi : Integrable D P := by
    have hp : MemLp (continuousPath (brownianPrefix B) hc) 2 P := hn.trans_lt ENNReal.ofReal_lt_top
    exact hp.norm.integrable (by norm_num)
  refine ⟨D,hi,?_⟩
  intro ω t
  simpa only [D,Real.norm_eq_abs,continuousPath,ContinuousMap.coe_mk] using
    (continuousPath (brownianPrefix B) hc ω).norm_coe_le_norm t

theorem brownian_prefix_regular {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) :
    (∀ t, Measurable[B.F t] (brownianPrefix B t)) ∧
      (∀ ω, Continuous (fun t => brownianPrefix B t ω)) := by
  have hs : ∀ t, MeasurableSet[B.F t] {ω : Ω | realTimeClamp (T := (⊤:EReal)) 1 ≤ t} := by
    intro t
    by_cases ht : realTimeClamp (T := (⊤:EReal)) 1 ≤ t <;> simp [ht]
  exact (B.martingale 0).stopped_regular P B.F B.mono B.le (fun _ => realTimeClamp 1) hs
    (fun _ => changed_time_finite 1 (by norm_num))

theorem brownian_barrier_endpoint_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (b : ℝ) :
    Measurable (brownianBarrierEndpoint B b) := by
  obtain ⟨hm,hc⟩ := brownian_prefix_regular P B
  have hτ := cappedBarrier_stopping B.F B.mono (brownianPrefix B) hm hc b
  exact (stopped_value_measurable_right_continuous m (show (0:EReal) ≤ ⊤ from le_top)
    B.F B.mono B.le (fun ω => realTimeClamp (cappedBarrier (brownianPrefix B) b ω)) hτ
    (brownianPrefix B) hm (fun ω _ => (hc ω).continuousAt.continuousWithinAt)).mono
    (show writtenStoppedSpace m B.F _ hτ ≤ m from fun A hA => hA.1) le_rfl

theorem brownian_barrier_endpoint_integrable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (b : ℝ) :
    Integrable (brownianBarrierEndpoint B b) P := by
  obtain ⟨D,hD,hb⟩ := brownian_prefix_bound P B
  exact hD.mono' (brownian_barrier_endpoint_measurable P B b).aestronglyMeasurable
    (ae_of_all _ fun ω => hb ω _)

theorem brownian_barrier_endpoint_noatom {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (b k : ℝ) (hk : k < b) :
    ∀ᵐ ω ∂P, brownianBarrierEndpoint B b ω ≠ k := by
  have hl : HasLaw (B.W 0 (realTimeClamp 1)) (gaussianReal 0 1) P := by
    convert scaled_brownian_gaussian_law P B 1 1 (by norm_num) (by norm_num) using 1 <;> norm_num
    congr 1
  haveI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hn : ∀ᵐ ω ∂P, B.W 0 (realTimeClamp 1) ω ≠ k := by
    rw [ae_iff]
    have he := hl.measure_eq (p := fun x => x=k) (measurableSet_singleton k)
    simpa only [not_not,Set.setOf_eq_eq_singleton,measure_singleton] using he
  obtain ⟨_,hc⟩ := brownian_prefix_regular P B
  filter_upwards [hn] with ω hω
  intro he
  by_cases ht : cappedBarrier (brownianPrefix B) b ω < 1
  · have hh := cappedBarrier_hit (brownianPrefix B) hc b ω ht
    change brownianBarrierEndpoint B b ω = b at hh
    exact (ne_of_lt hk) (he.symm.trans hh)
  · have ht1 := le_antisymm (cappedBarrier_range (brownianPrefix B) b ω).2 (le_of_not_gt ht)
    apply hω
    simpa only [brownianBarrierEndpoint,brownianPrefix,ht1,min_self] using he

end BarrierManuscript
#print axioms BarrierManuscript.brownian_prefix_bound
#print axioms BarrierManuscript.brownian_prefix_regular
#print axioms BarrierManuscript.brownian_barrier_endpoint_measurable
#print axioms BarrierManuscript.brownian_barrier_endpoint_integrable
#print axioms BarrierManuscript.brownian_barrier_endpoint_noatom
