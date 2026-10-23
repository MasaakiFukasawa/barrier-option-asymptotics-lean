import ManuscriptGeometricModel
import ManuscriptExponentialPathLimit
import ManuscriptStockCoefficientLimit
import ManuscriptBrownianScaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def brownianStoppedPath {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (u : ℝ) (hu : 0 ≤ u) (ω : Ω) : C(HalfClosedTime,ℝ) :=
  ⟨fun t => B.W 0 (min (realTimeClamp u) t) ω,
    open_path_stopped_continuous (B.W 0) ((B.martingale 0).path P B.F) u hu (EReal.coe_lt_top u) ω⟩

noncomputable def prefixTimePath (u : ℝ) (hu : 0 ≤ u) : C(HalfClosedTime,ℝ) :=
  ⟨fun t => (finitePrefixTime u hu t).val,continuous_subtype_val.comp (finite_prefix_time_continuous u hu)⟩

theorem brownianStoppedPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (u : ℝ) (hu : 0 ≤ u) :
    Measurable (brownianStoppedPath B u hu) :=
  continuous_path_measurable _ _ (fun t => ((B.martingale 0).adapted P B.F _
    ((min_le_left _ _).trans_lt (halfTimeClamp_finite u))).mono (B.le _) le_rfl)

theorem normalized_triple_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (b k : ℝ) (M : NormalizedBarrierModel P b k) (u : ℝ) :
    Measurable (M.triple (fun _ => 1) u) := by
  have hm : Measurable (fun ω => prefixMaximum M.X M.hXc (realTimeClamp u) ω) :=
    pathMaximum_lipschitz.continuous.measurable.comp
      (continuous_path_measurable _ (fun ω => (M.hXc ω).comp (continuous_const.min continuous_id))
        (fun t => (M.hXm _).mono (M.hle _) le_rfl))
  change Measurable (fun ω => (M.X (realTimeClamp u) ω,(1:ℝ),prefixMaximum M.X M.hXc (realTimeClamp u) ω))
  exact ((M.hXm _).mono (M.hle _) le_rfl).prodMk (measurable_const.prodMk hm)

theorem geometric_prefix_path {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k w u : ℝ) (hw : 0 < w) (hu : u ∈ Icc (0:ℝ) 1)
    (M : NormalizedBarrierModel P b k)
    (hX : M.X=(fun t ω => (geometricStock B w (min (realTimeClamp 1) t) ω-1)/w)) (ω : Ω) :
    (⟨fun t => M.X (min (realTimeClamp u) t) ω,(M.hXc ω).comp (continuous_const.min continuous_id)⟩ : C(HalfClosedTime,ℝ)) =
      expPathMap (brownianStoppedPath B u hu.1 ω) (prefixTimePath u hu.1) w := by
  ext t
  let r := finitePrefixTime u hu.1 t
  have hr : realTimeClamp r.val=min (realTimeClamp u) t := finite_prefix_time_clamp u hu.1 le_top t
  change M.X (min (realTimeClamp u) t) ω = expPathExtension w _ _
  rw [hX]
  dsimp only
  rw [← min_assoc,min_eq_right (real_time_clamp_mono hu.2),← hr,geometricStock_real P B w r.val r.property.1 ω]
  rw [expPathExtension_formula _ _ _ hw.ne']
  dsimp only [brownianStoppedPath,prefixTimePath,ContinuousMap.coe_mk]
  rw [hr]

theorem geometric_triple_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hlim : Tendsto w atTop (𝓝 0))
    (M : ℕ → NormalizedBarrierModel P b k)
    (hX : ∀ n, (M n).X=(fun t ω => (geometricStock B (w n) (min (realTimeClamp 1) t) ω-1)/w n))
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
    TendstoInDistribution (fun n => (M n).triple (fun _ => 1) u) atTop
      (fun ω => (B.W 0 (realTimeClamp u) ω,(1:ℝ),pathMaximum (brownianStoppedPath B u hu.1 ω))) (fun _ => P) P := by
  have hm : Measurable (fun ω => (B.W 0 (realTimeClamp u) ω,(1:ℝ),pathMaximum (brownianStoppedPath B u hu.1 ω))) :=
    (((B.martingale 0).adapted P B.F _ (halfTimeClamp_finite u)).mono (B.le _) le_rfl).prodMk
      (measurable_const.prodMk (pathMaximum_lipschitz.continuous.measurable.comp (brownianStoppedPath_measurable P B u hu.1)))
  apply tendstoInDistribution_of_ae_tendsto (fun n => (normalized_triple_measurable P b k (M n) u).aemeasurable) hm.aemeasurable
  apply ae_of_all
  intro ω
  have h := exponential_path_limit (brownianStoppedPath B u hu.1 ω) (prefixTimePath u hu.1) w hlim
  have hc : Continuous (fun f : C(HalfClosedTime,ℝ) => (f (realTimeClamp u),(1:ℝ),pathMaximum f)) :=
    (continuous_eval_const (realTimeClamp u)).prodMk (continuous_const.prodMk pathMaximum_lipschitz.continuous)
  have hh := hc.continuousAt.tendsto.comp h
  convert! hh using 1
  · funext n
    dsimp only [Function.comp_def]
    rw [← geometric_prefix_path P B b k (w n) u (hw n) hu (M n) (hX n) ω]
    simp only [Function.comp_def,NormalizedBarrierModel.triple,NormalizedBarrierModel.state,prefixMaximum,ContinuousMap.coe_mk,min_self]
  · simp only [brownianStoppedPath,ContinuousMap.coe_mk,min_self]

end BarrierManuscript
#print axioms BarrierManuscript.brownianStoppedPath_measurable
#print axioms BarrierManuscript.normalized_triple_measurable
#print axioms BarrierManuscript.geometric_prefix_path
#print axioms BarrierManuscript.geometric_triple_limit
