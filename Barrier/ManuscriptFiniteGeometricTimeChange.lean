import ManuscriptFiniteDeterministicTimeChange

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter6 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Construction of the deterministic-volatility stochastic exponential,
with both actual Ito equations and its finite-horizon geometric Brownian
representation. There is no infinite-horizon variance-divergence assumption. -/
theorem finite_geometric_time_change {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : ∀ r,0 ≤ r → IntervalIntegrable (fun s => g s^2) volume 0 r)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ (N A : HalfClosedTime → Ω → ℝ) (W : BrownianSystem (P.prod P) 1),
      LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N ∧
      LocalCovarianceWitness P B.F N N A ∧
      LocalMProcessWitness P B.F (fun t ω => Real.exp (N t ω-A t ω/2)-1) ∧
      ItoCovarianceFormula P B.F N (fun z => Real.exp (N (realTimeClamp z.2) z.1-A (realTimeClamp z.2) z.1/2))
        (fun t ω => Real.exp (N t ω-A t ω/2)-1) ∧
      ∀ᵐ z ∂P.prod P,∀ r ∈ Icc (0:ℝ) T,
        Real.exp (N (realTimeClamp r) z.1-A (realTimeClamp r) z.1/2)=
          Real.exp (W.W 0 (realTimeClamp (∫ s in (0:ℝ)..r,g s^2)) z-(∫ s in (0:ℝ)..r,g s^2)/2) := by
  obtain ⟨N,hN,hNI⟩ := deterministic_ito_exists P B g hg hi
  obtain ⟨A,hA,he⟩ := deterministic_ito_bracket_common P B g hg hi N hN hNI
  obtain ⟨W,hw⟩ := finite_deterministic_ito_time_change P B g hg hi N hN hNI T hT
  obtain ⟨hS,hSI⟩ := stochastic_exponential_constructed P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null N A hN hA
  have he' : ∀ᵐ z ∂P.prod P,∀ r : ℝ,0 ≤ r → A (realTimeClamp r) z.1=∫ s in (0:ℝ)..r,g s^2 :=
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae he
  refine ⟨N,A,W,hN,hNI,hA,hS,hSI,?_⟩
  filter_upwards [he',hw] with z hz hh r hr
  rw [hz r hr.1,hh r hr]

end BarrierManuscript
#print axioms BarrierManuscript.finite_geometric_time_change
