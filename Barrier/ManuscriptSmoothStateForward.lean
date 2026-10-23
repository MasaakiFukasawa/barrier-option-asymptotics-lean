import ManuscriptSmoothStateRemainder
import ManuscriptCoordinateMean

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- The forward variance differs from the spot variance by O(t), with
an explicit constant derived from the state drift and diffusion bounds. -/
theorem smooth_state_forward_bound {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SmoothStateData (ι := ι) (κ := κ) D) (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) :
    Integrable (D.V (realTimeClamp t)) P ∧
      |(∫ ω,D.V (realTimeClamp t) ω ∂P)-D.v₀| ≤
        ((∑ j,|smoothStateGradient R j| *(R.coordinate j).L)+
          (R.derivative_bound:ℝ)*(∑ j,coordinateMomentBound (R.coordinate j)))*t := by
  let A : Ω → ℝ := fun ω => ∑ j,smoothStateGradient R j*coordinateIncrement (R.coordinate j) t ω
  have hq j : Integrable (coordinateIncrement (R.coordinate j) t) P :=
    (coordinate_second_moment (R.coordinate j) t ⟨ht.1.le,ht.2⟩).1.integrable (by norm_num)
  have hiA : Integrable A P := integrable_finset_sum _ (fun j _ => (hq j).const_mul _)
  have hr := smooth_state_remainder_moment R t ht
  have he ω : R.f (smoothStatePoint R t ω)=D.v₀+A ω+Real.sqrt t*smoothStateRemainder R t ω := by
    dsimp only [A,smoothStateRemainder]
    rw [R.initial_variance]
    field_simp [(Real.sqrt_pos.mpr ht.1).ne']
    <;> ring
  have hv : D.V (realTimeClamp t)=ᵐ[P] fun ω => D.v₀+A ω+Real.sqrt t*smoothStateRemainder R t ω := by
    filter_upwards [R.variance t ht.1.le] with ω hω
    exact hω.trans (he ω)
  have hsum := ((integrable_const D.v₀).add hiA).add (hr.1.const_mul (Real.sqrt t))
  refine ⟨hsum.congr hv.symm,?_⟩
  have hbA : |∫ ω,A ω ∂P|≤(∑ j,|smoothStateGradient R j| *(R.coordinate j).L)*t := by
    rw [integral_finset_sum _ (fun j _ => (hq j).const_mul _)]
    simp_rw [integral_const_mul]
    calc
      _ ≤ ∑ j,|smoothStateGradient R j*(∫ ω,coordinateIncrement (R.coordinate j) t ω ∂P)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j,|smoothStateGradient R j| *((R.coordinate j).L*t) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (coordinate_mean_bound (R.coordinate j) t ⟨ht.1.le,ht.2⟩) (abs_nonneg _)
      _ = _ := by simp only [Finset.sum_mul,mul_assoc]
  have hbR : |Real.sqrt t*(∫ ω,smoothStateRemainder R t ω ∂P)|≤
      ((R.derivative_bound:ℝ)*∑ j,coordinateMomentBound (R.coordinate j))*t := by
    have hn : |∫ ω,smoothStateRemainder R t ω ∂P|≤∫ ω,|smoothStateRemainder R t ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (smoothStateRemainder R t) (μ := P)
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg t)]
    calc
      _ ≤ Real.sqrt t*((R.derivative_bound:ℝ)*(∑ j,coordinateMomentBound (R.coordinate j))*Real.sqrt t) :=
        mul_le_mul_of_nonneg_left (hn.trans hr.2) (Real.sqrt_nonneg t)
      _ = ((R.derivative_bound:ℝ)*∑ j,coordinateMomentBound (R.coordinate j))*(Real.sqrt t*Real.sqrt t) := by ring
      _ = _ := by rw [Real.mul_self_sqrt ht.1.le]
  have hiBase : Integrable (fun ω => D.v₀+A ω) P := (integrable_const D.v₀).add hiA
  rw [integral_congr_ae hv,integral_add hiBase (hr.1.const_mul (Real.sqrt t)),
    integral_add (integrable_const D.v₀) hiA,integral_const_mul]
  have hmass : P.real univ=1 := by simp
  simp only [integral_const,hmass,one_smul]
  have hh := (abs_add_le (∫ ω,A ω ∂P) (Real.sqrt t*(∫ ω,smoothStateRemainder R t ω ∂P))).trans (add_le_add hbA hbR)
  convert hh using 1 <;> congr 1 <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_forward_bound
