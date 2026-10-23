import ManuscriptStockData
import Chapter3IdentityItoIntegral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def frozenStockError {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) : HalfClosedTime → Ω → ℝ :=
  fun t ω => -Real.sqrt D.v₀*D.B.W 0 t ω+(D.S t ω/D.S₀-1)

noncomputable def frozenStockIntegrand {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) : HalfClosedTime → Ω → ℝ :=
  fun t ω => -Real.sqrt D.v₀+(D.S t ω/D.S₀)*Real.sqrt (D.V t ω)

/-- The error from freezing the diffusion coefficient is an actual local
martingale with quadratic variation equal to the integral of its squared
coefficient error. This is derived from the original stock SDE. -/
theorem frozen_stock_error_bracket {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) :
    LocalMProcessWitness P D.B.F (frozenStockError D) ∧
    ∃ C : HalfClosedTime → Ω → ℝ,
      LocalCovarianceWitness P D.B.F (frozenStockError D) (frozenStockError D) C ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω =
        ∫ s in (0:ℝ)..r, (frozenStockIntegrand D (realTimeClamp s) ω)^2 := by
  have hN : LocalMProcessWitness P D.B.F (frozenStockError D) :=
    ((D.B.martingale 0).smul P D.B.F (-Real.sqrt D.v₀)).add P D.B.F D.B.mono D.B.le D.hM
  have hI := identity_ito_integral P (by simp : (0:EReal)<⊤)
    D.B.F D.B.mono D.B.le D.B.null (D.B.W 0) (D.B.martingale 0)
  have hNI : ItoCovarianceFormula P D.B.F (D.B.W 0)
      (fun z => frozenStockIntegrand D (realTimeClamp z.2) z.1) (frozenStockError D) := by
    unfold frozenStockError
    simpa only [mul_one,frozenStockIntegrand] using
      hI.add_smul P D.B.F D.B.mono D.B.le (D.B.W 0) (D.B.W 0)
        (fun t ω => D.S t ω/D.S₀-1) (fun _ => 1)
        (fun z => (D.S (realTimeClamp z.2) z.1/D.S₀)*Real.sqrt (D.V (realTimeClamp z.2) z.1))
        D.hSDE (-Real.sqrt D.v₀)
  have hHa t ht : Measurable[D.B.F t] (frozenStockIntegrand D t) :=
    measurable_const.add (((D.hSa t ht).div_const D.S₀).mul ((D.hVa t ht).sqrt))
  have hHc ω t ht : ContinuousAt (fun s => frozenStockIntegrand D s ω) t :=
    continuousAt_const.add (((D.hSc ω t ht).div_const D.S₀).mul ((D.hVc ω t ht).sqrt))
  obtain ⟨_,C,_,hC,_,he⟩ := brownian_ito_cross_and_self_density P D.B.F D.B.mono D.B.le D.B.null
    (D.B.W 0) (frozenStockError D) (D.B.C 0 0) (frozenStockIntegrand D)
    (D.B.martingale 0) hN (D.B.cov 0 0) (D.B.diagonal_clock 0) hHa hHc hNI
  exact ⟨hN,C,hC,he⟩

theorem frozen_stock_integrand_initial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) :
    (fun ω => frozenStockIntegrand D (realTimeClamp 0) ω) =ᵐ[P] 0 := by
  filter_upwards [D.hSinitial,D.hVinitial] with ω hS hV
  simp only [frozenStockIntegrand,hS,hV,div_self D.hS₀.ne',one_mul,neg_add_cancel,Pi.zero_apply]

end BarrierManuscript
#print axioms BarrierManuscript.frozen_stock_error_bracket
#print axioms BarrierManuscript.frozen_stock_integrand_initial
