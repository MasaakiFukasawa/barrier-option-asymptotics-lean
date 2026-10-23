import ManuscriptMainFamily

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

def CoefficientProfile {Γ : Type*} [MeasurableSpace Γ] (Q : Measure Γ)
    (z : Γ → ℝ × ℝ × ℝ) (b k H : ℝ) : Prop :=
  ∃ q : ℝ → ℝ → ℝ,
    (∀ u ∈ Ioo (0:ℝ) 1, Measurable (q u) ∧
      (Q.restrict {ω | (z ω).2.2 ≤ b/Real.sqrt u})[fun ω => (z ω).2.1 |
        MeasurableSpace.comap (fun ω => (z ω).1) inferInstance] = q u ∘ (fun ω => (z ω).1)) ∧
    alpha Q (fun ω => (z ω).1) (fun ω => (z ω).2.1) (fun ω => (z ω).2.2) b k H =
      (1/2)*(∫ u in (0:ℝ)..1, u^H*(∫ x in Iio b,
        q u (x/Real.sqrt u)*psi (b-x) (k-x) (1-u)*psi b x u))

theorem original_coefficient_profile {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (D : StockSDEData P) (b k H : ℝ) (hb : 0 < b)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (M : ℕ → NormalizedBarrierModel P b k)
    (hX : ∀ n, (M n).X=fun r ω => (D.S (linearClock (θ n) (hp n) (min (realTimeClamp 1) r)) ω/D.S₀-1)/Real.sqrt (θ n*D.v₀))
    (z : Γ → ℝ × ℝ × ℝ) (hz : Measurable z)
    (hlaw : TendstoInDistribution (fun n => (M n).triple (M n).Y 1) atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun n ω => (M n).Y (ω,1)) 1 P) :
    CoefficientProfile Q z b k H := by
  obtain ⟨B₀,hmarg⟩ := original_stock_limit_marginal P Q D.B D.S D.V D.S₀ D.v₀ b k
    D.hS₀.ne' D.hv₀ D.hSa D.hVa D.hSc D.hVc D.hSinitial D.hVinitial D.hVpos D.hM D.hSDE
    θ hp hθ M hX z hlaw
  have hη := hlaw.continuous_comp (show Continuous (fun q : ℝ × ℝ × ℝ => q.2.1) from continuous_snd.fst)
  have hi := (weak_ui_expectation_limit P Q _ _ hη hui).1
  exact alpha_representation (P.prod P) Q B₀ (fun ω => (z ω).1) (fun ω => (z ω).2.2)
    (fun ω => (z ω).2.1) hz.fst hz.snd.snd hi hmarg b k H hb

end BarrierManuscript
#print axioms BarrierManuscript.original_coefficient_profile
