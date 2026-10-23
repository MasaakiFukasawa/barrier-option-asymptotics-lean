import ManuscriptFiniteDeterministicTimeChange

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The arithmetic SDE in the opening section has its Brownian time-change
representation on every finite horizon. The input is the actual Ito SDE;
no Gaussian law, time-change identity, boundedness, or variance-clock
divergence is assumed. Measurable nonnegative locally integrable variance
is sufficient. -/
theorem deterministic_variance_model_time_change {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (v : ℝ → ℝ) (hv : Measurable v) (hpos : ∀ r,0 ≤ r → 0 ≤ v r)
    (hi : ∀ r,0 ≤ r → IntervalIntegrable v volume 0 r)
    (X : HalfClosedTime → Ω → ℝ) (x₀ : ℝ)
    (hX : LocalMProcessWitness P B.F (fun t ω => X t ω-x₀))
    (hSDE : ItoCovarianceFormula P B.F (B.W 0) (fun z => Real.sqrt (v z.2))
      (fun t ω => X t ω-x₀))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ W : BrownianSystem (P.prod P) 1,∀ᵐ z ∂P.prod P,∀ r ∈ Icc (0:ℝ) T,
      X (realTimeClamp r) z.1=x₀+W.W 0 (realTimeClamp (∫ s in (0:ℝ)..r,v s)) z := by
  have hs (r : ℝ) (hr : 0 ≤ r) :
      IntervalIntegrable (fun s => (Real.sqrt (v s))^2) volume 0 r := by
    apply (hi r hr).congr
    intro s hsr
    rw [uIoc_of_le hr] at hsr
    exact (Real.sq_sqrt (hpos s hsr.1.le)).symm
  obtain ⟨W,hw⟩ := finite_deterministic_ito_time_change P B (fun s => Real.sqrt (v s)) hv.sqrt hs
    (fun t ω => X t ω-x₀) hX hSDE T hT
  refine ⟨W,?_⟩
  filter_upwards [hw] with z hz r hr
  have he : (∫ s in (0:ℝ)..r,(Real.sqrt (v s))^2)=∫ s in (0:ℝ)..r,v s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    exact Real.sq_sqrt (hpos s hs.1)
  have h := hz r hr
  rw [he] at h
  linarith

/-- A continuous nondecreasing variance clock covers the whole Brownian
observation interval, so monitoring through physical time loses no barrier
crossings, including when the clock has flat portions. -/
theorem continuous_clock_survival (q f : ℝ → ℝ) (T b : ℝ) (hT : 0 ≤ T)
    (hc : ContinuousOn q (Icc (0:ℝ) T)) (hm : MonotoneOn q (Icc (0:ℝ) T)) (h0 : q 0=0) :
    (∀ r ∈ Icc (0:ℝ) T,f (q r)<b) ↔ (∀ u ∈ Icc (0:ℝ) (q T),f u<b) := by
  constructor
  · intro h u hu
    have hu' : u ∈ Icc (q 0) (q T) := by simpa only [h0] using hu
    obtain ⟨r,hr,he⟩ := intermediate_value_Icc hT hc hu'
    simpa only [he] using h r hr
  · intro h r hr
    apply h (q r)
    exact ⟨by simpa only [h0] using hm ⟨le_rfl,hT⟩ hr hr.1,
      hm hr ⟨hT,le_rfl⟩ hr.2⟩

end BarrierManuscript
#print axioms BarrierManuscript.deterministic_variance_model_time_change
#print axioms BarrierManuscript.continuous_clock_survival
