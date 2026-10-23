import ManuscriptBrownianFuture

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def rawPrefixPath {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ω : Ω) : C(Icc (0:ℝ≥0) 1,ℝ) :=
  ⟨fun r => W (t*r.val) ω,(hc ω).comp (continuous_const.mul continuous_subtype_val)⟩

theorem rawPrefixPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (W : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) :
    Measurable (rawPrefixPath W hc t) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro r
  exact hm (t*r.val)

/-- The endpoint and maximum of the past segment are independent of the
endpoint and maximum of the shifted future segment. -/
theorem brownian_segment_independence {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t d : ℝ≥0) :
    let Z := fun s ω => W (t+s) ω-W t ω
    let hZ : ∀ ω, Continuous (fun s => Z s ω) := fun ω => ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    IndepFun
      (fun ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1) (rawPrefixPath W hc t ω))
      (fun ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1) (rawPrefixPath Z hZ d ω)) P := by
  dsimp only
  let Z := fun s ω => W (t+s) ω-W t ω
  let hZ : ∀ ω, Continuous (fun s => Z s ω) := fun ω => ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  let G := MeasurableSpace.comap (fun ω s => Z s ω) inferInstance
  letI : MeasurableSpace Ω := m
  have hPast : Measurable[pastSigma W t] (rawPrefixPath W hc t) := by
    letI : MeasurableSpace Ω := pastSigma W t
    apply ContinuousMap.measurable_iff_eval.mpr
    intro r
    exact (natural_process_adapted W (t*r.val)).mono
      (past_sigma_mono W (mul_le_of_le_one_right (show (0:ℝ≥0) ≤ t from bot_le) r.property.2)) le_rfl
  have hFuture : Measurable[G] (rawPrefixPath Z hZ d) := by
    letI : MeasurableSpace Ω := G
    apply ContinuousMap.measurable_iff_eval.mpr
    intro r
    exact (measurable_pi_apply (d*r.val)).comp (Measurable.of_comap_le (show G ≤ G from le_rfl))
  have hep := (endpointMaximum_continuous (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)).measurable
  have hi := (brownian_future_independent_past P W hW hm hc t).2
  exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left hi (hep.comp hFuture).comap_le)
    (hep.comp hPast).comap_le).symm

end BarrierManuscript
#print axioms BarrierManuscript.rawPrefixPath_measurable
#print axioms BarrierManuscript.brownian_segment_independence
