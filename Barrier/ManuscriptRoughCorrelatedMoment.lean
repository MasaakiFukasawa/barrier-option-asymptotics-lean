import ManuscriptRoughMomentLimit
import ManuscriptBrownianBarrierTest
import ManuscriptBrownianRegressionTest
import ManuscriptBrownianPreLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def mixedBrownianPath {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (ρ c : ℝ) (ω : Ω) : C(ℝ≥0,ℝ) :=
  ρ • brownianContinuousPath B ω+c • brownianContinuousPath C ω

/-- The actual Volterra integral's barrier-weighted moment, including the
stock/volatility correlation. The Brownian conditional moment, regression,
Fubini and singular cutoff limit are all proved, rather than assumed. -/
theorem rough_correlated_kernel_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B C : BrownianSystem P 1)
    (hind : IndepFun (brownianContinuousPath B) (brownianContinuousPath C) P)
    (ρ c : ℝ) (hc : ρ^2+c^2=1) (H ν b k : ℝ) (hH : 0 < H) (hb : 0 < b)
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t < 1)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N) :
    (∫ ω,N (realTimeClamp t) ω*
      brownianBarrierKernelTest (fun s ω => mixedBrownianPath B C ρ c ω s)
        (fun ω => (mixedBrownianPath B C ρ c ω).continuous) b k t ω ∂P)=
      ρ*(∫ s in (0:ℝ)..(t:ℝ),roughKernel H ν t s*barPsiTimeDerivative b k s) := by
  let X := fun s : ℝ≥0 => B.W 0 (realTimeClamp s)
  let Y := fun s : ℝ≥0 => C.W 0 (realTimeClamp s)
  let S := fun s ω => ρ*X s ω+c*Y s ω
  have hX := brownian_system_preBrownian P B
  have hY := brownian_system_preBrownian P C
  have hmX (s : ℝ≥0) : Measurable (X s) :=
    (continuous_eval_const s).measurable.comp (brownian_continuous_path_measurable B)
  have hmY (s : ℝ≥0) : Measurable (Y s) :=
    (continuous_eval_const s).measurable.comp (brownian_continuous_path_measurable C)
  have hev : Measurable (fun f : C(ℝ≥0,ℝ) => fun s => f s) :=
    measurable_pi_iff.mpr (fun s => (continuous_eval_const s).measurable)
  have hi : IndepFun (fun ω s => X s ω) (fun ω s => Y s ω) P := hind.comp hev hev
  have hS : IsPreBrownianReal S P := brownian_linear_preBrownian P X Y hX hY hi ρ c hc
  have hmS (s : ℝ≥0) : Measurable (S s) := (measurable_const.mul (hmX s)).add (measurable_const.mul (hmY s))
  have hSc (ω : Ω) : Continuous (fun s => S s ω) := (mixedBrownianPath B C ρ c ω).continuous
  let Z := brownianBarrierKernelTest S hSc b k t
  have hZpath := brownian_barrier_test_path_measurable S hSc b k t
  have hZ : Measurable Z := hZpath.mono (measurable_pi_iff.mpr hmS).comap_le le_rfl
  let A := 2*normalizer/Real.sqrt (1-(t:ℝ))
  have hA : 0 ≤ A := by unfold A normalizer; positivity
  have hZb ω : |Z ω| ≤ A := brownian_barrier_test_bound S hSc b k t ht1 ω
  change (∫ ω,N (realTimeClamp t) ω*Z ω ∂P)=_
  apply rough_barPsi_moment P B H ν b k ρ hH hb t ht ht1 N hN hNI Z hZ A hA hZb
  intro s hs hst
  let q := Real.toNNReal s
  have hq : (q:ℝ)=s := Real.coe_toNNReal _ hs.le
  have hqp : 0 < q := by change (0:ℝ)<(q:ℝ); rwa [hq]
  have hqt : q < t := by change (q:ℝ)<(t:ℝ); rwa [hq]
  have hreg := brownian_regression_test P X Y hX hY hmX hmY hi ρ c hc q Z hZpath A hZb
  have hmom := brownian_barrier_test_moment P S hS hmS hSc q t hqp hqt ht1 b k hb
  change (∫ ω,X q ω*Z ω ∂P)=ρ*(∫ ω,S q ω*Z ω ∂P) at hreg
  rw [hmom] at hreg
  simpa only [X,hq] using hreg

end BarrierManuscript
#print axioms BarrierManuscript.rough_correlated_kernel_moment
