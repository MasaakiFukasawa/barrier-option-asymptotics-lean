import ManuscriptStockModelConstruction

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
namespace BarrierManuscript

/-- Original stock SDE assumptions, with no price or limit conclusions.
Finite-time continuity is sufficient; no condition is imposed at infinity. -/
structure StockSDEData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] where
  B : BrownianSystem P 1
  S : HalfClosedTime → Ω → ℝ
  V : HalfClosedTime → Ω → ℝ
  S₀ : ℝ
  v₀ : ℝ
  hS₀ : 0 < S₀
  hv₀ : 0 < v₀
  hSa : ∀ t, t < ⊤ → Measurable[B.F t] (S t)
  hVa : ∀ t, t < ⊤ → Measurable[B.F t] (V t)
  hSc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => S s ω) t
  hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t
  hSinitial : ∀ᵐ ω ∂P, S (realTimeClamp 0) ω=S₀
  hVinitial : ∀ᵐ ω ∂P, V (realTimeClamp 0) ω=v₀
  hSpos : ∀ ω t, t < ⊤ → 0 ≤ S t ω
  hVpos : ∀ ω r, 0 ≤ r → 0 ≤ V (realTimeClamp r) ω
  hM : LocalMProcessWitness P B.F (fun t ω => S t ω/S₀-1)
  hSDE : ItoCovarianceFormula P B.F (B.W 0)
    (fun z => (S (realTimeClamp z.2) z.1/S₀)*Real.sqrt (V (realTimeClamp z.2) z.1))
    (fun t ω => S t ω/S₀-1)

end BarrierManuscript
#print axioms BarrierManuscript.stock_model_exists
