import ManuscriptItoFreezing
import ManuscriptStockPathApproximation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- The endpoint consequence of the uniform freezing theorem, stated in
the joint-convergence-friendly difference-in-probability form. -/
theorem ito_endpoint_tangent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G N : HalfClosedTime → Ω → ℝ)
    (hGa : ∀ t,t < ⊤ → Measurable[B.F t] (G t))
    (hGc : ∀ ω t,t < ⊤ → ContinuousAt (fun s => G s ω) t)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => G (realTimeClamp z.2) z.1) N)
    (a : ℝ) (hG0 : ∀ᵐ ω ∂P,G (realTimeClamp 0) ω=a)
    (θ : ℕ → ℝ) (hp : ∀ n,0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω =>
      N (realTimeClamp (θ n)) ω/Real.sqrt (θ n)-a*(scaledBrownian B (θ n) (hp n)).W 0 (realTimeClamp 1) ω)
      atTop (fun _ => 0) := by
  have hE := (ito_frozen_error_bracket P B G N hGa hGc hN hNI a).1
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have h := ito_frozen_brownian_approximation P B G N hGa hGc hN hNI a hG0 θ hp hθ ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  have hc : Continuous (fun t : HalfClosedTime =>
      itoFrozenError B N a (linearClock (θ n) (hp n) (min (realTimeClamp 1) t)) ω/Real.sqrt (θ n)) := by
    apply Continuous.div_const
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (g := fun r : HalfClosedTime => itoFrozenError B N a r ω)
      (f := fun s : HalfClosedTime => linearClock (θ n) (hp n) (min (realTimeClamp 1) s))
      (hE.path P B.F ω _ (scaled_capped_time_finite (θ n) (hp n) t))
      (((linear_clock_continuous (θ n) (hp n)).comp (continuous_const.min continuous_id)).continuousAt)
  have hb := (isCompact_range hc.abs).bddAbove
  have hs := le_ciSup hb (realTimeClamp (T := (⊤:EReal)) 1)
  change ε ≤ _
  apply le_trans _ hs
  simp only [min_self,linear_clock_finite _ _ 1 zero_le_one,mul_one,itoFrozenError]
  simp only [Set.mem_setOf_eq,sub_zero,Real.norm_eq_abs,
    scaledBrownian_W P B (θ n) 1 (hp n) zero_le_one,mul_one] at hω
  convert hω using 1
  congr 1
  ring

end BarrierManuscript
#print axioms BarrierManuscript.ito_endpoint_tangent
