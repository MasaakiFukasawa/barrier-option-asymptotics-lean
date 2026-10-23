import ManuscriptRoughAlphaSlice
import ManuscriptPowerTriangle
import ManuscriptRoughBetaReduction

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The coefficient is derived from the actual jointly constructed Volterra
integral and stock Brownian driver; no conditional moment identity is assumed. -/
theorem rough_model_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (C : RoughStockCoupling R)
    (b k : ℝ) (hb : 0 < b) :
    alpha P (fun ω => (roughLimit R ω).1) (fun ω => (roughLimit R ω).2.1)
      (fun ω => (roughLimit R ω).2.2) b k R.H=
      roughBergomiCoefficient b k R.H C.ρ R.ν := by
  have he : alpha P (fun ω => (roughLimit R ω).1) (fun ω => (roughLimit R ω).2.1)
      (fun ω => (roughLimit R ω).2.2) b k R.H=
      (C.ρ/2)*(∫ u in (0:ℝ)..1,∫ s in (0:ℝ)..u,
        roughKernel R.H R.ν u s*barPsiTimeDerivative b k s) := by
    unfold alpha
    rw [← intervalIntegral.integral_neg,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro u hu
    dsimp only
    rw [rough_alpha_slice P D R C b k u hb hu]
    ring
  have hk : (∫ u in (0:ℝ)..1,∫ s in (0:ℝ)..u,
        roughKernel R.H R.ν u s*barPsiTimeDerivative b k s)=
      R.ν*Real.sqrt (2*R.H)*(∫ u in (0:ℝ)..1,∫ s in (0:ℝ)..u,
        (u-s)^(R.H-1/2)*barPsiTimeDerivative b k s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro u hu
    dsimp only
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hu.1.le
    intro s hs
    dsimp only
    simp only [roughKernel,Asakura.mvnFutureFunction,Set.indicator_of_mem (show s ∈ Ioc (0:ℝ) u from ⟨hs.1,hs.2.le⟩)]
    ring
  rw [he,hk,weighted_power_triangle (R.H-1/2) (by linarith [R.hH])
    (barPsiTimeDerivative b k) (barPsiTimeDerivative_measurable b k)
    (phi k*|k|+phi (2*b-k)*|2*b-k|) (barPsiTimeDerivative_bound b k)]
  rw [show R.H-1/2+1=R.H+1/2 by ring,
    rough_coefficient_ibp b k (R.H+1/2) hb (by linarith [R.hH])]
  simp only [show R.H+1/2-1=R.H-1/2 by ring,roughBergomiCoefficient]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.rough_model_coefficient
