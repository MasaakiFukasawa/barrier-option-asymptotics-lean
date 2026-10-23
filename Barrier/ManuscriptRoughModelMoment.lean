import ManuscriptRoughCorrelatedMoment
import ManuscriptRoughStockData

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def stockKernelTest {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (t : ℝ≥0) : Ω → ℝ :=
  brownianBarrierKernelTest (fun s ω => B.W 0 (realTimeClamp s) ω)
    (fun ω => (brownianContinuousPath B ω).continuous) b k t

theorem rough_model_kernel_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : RoughVarianceData D) (C : RoughStockCoupling R)
    (b k : ℝ) (hb : 0 < b) (t : ℝ≥0) (ht : 0 < t) (ht1 : t < 1) :
    (∫ ω,R.N t (realTimeClamp t) ω*stockKernelTest D.B b k t ω ∂P)=
      C.ρ*(∫ s in (0:ℝ)..(t:ℝ),roughKernel R.H R.ν t s*barPsiTimeDerivative b k s) := by
  have hc : C.ρ^2+(Real.sqrt (1-C.ρ^2))^2=1 := by
    rw [Real.sq_sqrt (sub_nonneg.mpr C.correlation_bound)]
    ring
  have h := rough_correlated_kernel_moment P R.W C.C C.independent C.ρ (Real.sqrt (1-C.ρ^2)) hc
    R.H R.ν b k R.hH hb t ht ht1 (R.N t) (R.localM t ht) (R.integral t ht)
  have he : (fun s ω => mixedBrownianPath R.W C.C C.ρ (Real.sqrt (1-C.ρ^2)) ω s)=
      (fun s : ℝ≥0 => D.B.W 0 (realTimeClamp s)) := by
    funext s ω
    exact (C.driver s s.coe_nonneg ω).symm
  have htst ω : brownianBarrierKernelTest
      (fun s ω => mixedBrownianPath R.W C.C C.ρ (Real.sqrt (1-C.ρ^2)) ω s)
      (fun ω => (mixedBrownianPath R.W C.C C.ρ (Real.sqrt (1-C.ρ^2)) ω).continuous) b k t ω=
      stockKernelTest D.B b k t ω := by
    have hv (s : ℝ≥0) : mixedBrownianPath R.W C.C C.ρ (Real.sqrt (1-C.ρ^2)) ω s=D.B.W 0 (realTimeClamp s) ω :=
      congrFun (congrFun he s) ω
    have hp : rawPrefixPath
        (fun s ω => mixedBrownianPath R.W C.C C.ρ (Real.sqrt (1-C.ρ^2)) ω s)
        (fun ω => (mixedBrownianPath R.W C.C C.ρ (Real.sqrt (1-C.ρ^2)) ω).continuous) t ω=
        rawPrefixPath (fun s ω => D.B.W 0 (realTimeClamp s) ω)
          (fun ω => (brownianContinuousPath D.B ω).continuous) t ω := by
      ext r
      exact hv (t*r.val)
    unfold stockKernelTest brownianBarrierKernelTest
    rw [hp]
    dsimp only
    rw [hv]
  simpa only [htst] using h

end BarrierManuscript
#print axioms BarrierManuscript.rough_model_kernel_moment
