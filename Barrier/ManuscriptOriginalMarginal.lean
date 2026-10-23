import ManuscriptStockPathEncoding
import ManuscriptMaximumEncoding
import ManuscriptStockCoefficientLimit
import ManuscriptWeakUI

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem original_stock_limit_marginal {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (S V : HalfClosedTime → Ω → ℝ) (S₀ v₀ b k : ℝ)
    (hS₀n : S₀ ≠ 0) (hv₀ : 0 < v₀)
    (hSa : ∀ t, t < ⊤ → Measurable[B.F t] (S t))
    (hVa : ∀ t, t < ⊤ → Measurable[B.F t] (V t))
    (hSc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => S s ω) t)
    (hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t)
    (hS₀ : ∀ᵐ ω ∂P, S (realTimeClamp 0) ω = S₀)
    (hV₀ : ∀ᵐ ω ∂P, V (realTimeClamp 0) ω = v₀)
    (hV : ∀ ω r, 0 ≤ r → 0 ≤ V (realTimeClamp r) ω)
    (hM : LocalMProcessWitness P B.F (fun t ω => S t ω/S₀-1))
    (hSDE : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (S (realTimeClamp z.2) z.1/S₀)*Real.sqrt (V (realTimeClamp z.2) z.1))
      (fun t ω => S t ω/S₀-1))
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (M : ℕ → NormalizedBarrierModel P b k)
    (hX : ∀ n, (M n).X=fun t ω => (S (linearClock (θ n) (hp n) (min (realTimeClamp 1) t)) ω/S₀-1)/Real.sqrt (θ n*v₀))
    (z : Γ → ℝ × ℝ × ℝ)
    (hlaw : TendstoInDistribution (fun n => (M n).triple (M n).Y 1) atTop z (fun _ => P) Q) :
    ∃ B₀ : BrownianSystem (P.prod P) 1,
      Q.map (fun ω => ((z ω).1,(z ω).2.2)) =
        (P.prod P).map (fun ω => (B₀.W 0 (realTimeClamp 1) ω,brownianMaximum B₀ ω)) := by
  obtain ⟨hN,B₀,hclt⟩ := stock_endpoint_maximum_clt P B S V S₀ v₀ hS₀n hv₀ hSa hVa hSc hVc hS₀ hV₀ hV hM hSDE θ hp hθ
  refine ⟨B₀,?_⟩
  have hpairs n ω := stock_endpoint_maximum_encoding
    (fun t ω => (S (linearClock (θ n) (hp n) t) ω/S₀-1)/Real.sqrt (θ n*v₀)) (M n).X
    ((hN n).path P _) (M n).hXc (fun t ht ω => by rw [hX n]; dsimp only; rw [min_eq_right ht]) ω
  have hbrown : TendstoInDistribution
      (fun n ω => (((M n).triple (M n).Y 1 ω).1,((M n).triple (M n).Y 1 ω).2.2)) atTop
      (fun ω => (B₀.W 0 (realTimeClamp 1) ω,brownianMaximum B₀ ω)) (fun _ => P) (P.prod P) := by
    apply hclt.congr
    · intro n
      exact ae_of_all _ fun ω => hpairs n ω
    · apply ae_of_all
      intro ω
      apply Prod.ext
      · rfl
      · exact brownian_maximum_encoding (P.prod P) B₀ ω
  exact identify_endpoint_maximum_law P Q (P.prod P) _ z _ hlaw hbrown

end BarrierManuscript
#print axioms BarrierManuscript.original_stock_limit_marginal
