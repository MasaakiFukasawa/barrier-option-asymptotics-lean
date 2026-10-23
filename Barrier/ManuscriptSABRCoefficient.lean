import ManuscriptCorollary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The SABR tangent coefficient. The residual Brownian endpoint is
independent of the stock Brownian endpoint and its running maximum. -/
theorem sabr_tangent_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (Z : Ω → ℝ) (hZ : Measurable Z) (hZlaw : HasLaw Z (gaussianReal 0 1) P)
    (hind : IndepFun Z (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)) P)
    (ν ρ b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    alpha P (B.W 0 (realTimeClamp 1))
      (fun ω => 2*ν*(ρ*B.W 0 (realTimeClamp 1) ω+Real.sqrt (1-ρ^2)*Z ω))
      (brownianMaximum B) b k (1/2) = ν*ρ*gamma b k := by
  have hX : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (halfTimeClamp_finite 1)).mono (B.le _) le_rfl
  have hM := brownianMaximum_measurable P B
  obtain ⟨hiX,_⟩ := brownian_marginal_centered P P B _ _ hX hM rfl
  have hiZ := hZlaw.integrable ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl)
  have hz : (∫ ω, Z ω ∂P)=0 := by rw [hZlaw.integral_eq,integral_id_gaussianReal]
  let c := 2*ν*Real.sqrt (1-ρ^2)
  have hR : Measurable (fun ω => c*Z ω) := measurable_const.mul hZ
  have hRi : Integrable (fun ω => c*Z ω) P := hiZ.const_mul c
  have hRind : IndepFun (fun ω => c*Z ω)
      (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)) P := by
    exact hind.comp (show Measurable (fun z : ℝ => c*z) by fun_prop) measurable_id
  have hRzero : (∫ ω, c*Z ω ∂P)=0 := by rw [integral_const_mul,hz,mul_zero]
  have h := linear_alpha P P B _ _ _ hX hM hR hiX hRi hRind hRzero rfl (2*ν*ρ) b k hb hk
  convert h using 1
  · congr 2
    funext ω
    dsimp only [c]
    ring
  · ring

end BarrierManuscript
#print axioms BarrierManuscript.sabr_tangent_coefficient
