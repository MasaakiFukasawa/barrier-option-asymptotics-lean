import ManuscriptLinearCoefficient

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem linear_alpha_slice {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M R : Γ → ℝ)
    (hX : Measurable X) (hM : Measurable M) (hR : Measurable R)
    (hiX : Integrable X Q) (hiR : Integrable R Q)
    (hind : IndepFun R (fun ω => (X ω,M ω)) Q) (hzero : ∫ ω, R ω ∂Q=0)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (a b k u : ℝ) (hb : 0 < b) (hu : u ∈ Ioo (0:ℝ) 1) :
    (∫ ω, barrierWeight (thetaKernel b k 1 (Real.sqrt (1-u))) b
      (Real.sqrt u*X ω,u^(1/2:ℝ)*(a*X ω+R ω),Real.sqrt u*M ω) ∂Q) =
      -(a/2)*barPsi b k u := by
  let w := Real.sqrt (1-u)
  let f : ℝ × ℝ → ℝ := fun q => if Real.sqrt u*q.2 < b then
    thetaKernel b k 1 w (Real.sqrt u*q.1) else 0
  have hw : 0 < w := Real.sqrt_pos.mpr (by linarith [hu.2])
  have ht : Measurable (thetaKernel b k 1 w) := by
    unfold thetaKernel
    exact measurable_const.mul ((phi_contDiff.continuous.measurable.comp (by fun_prop)).sub
      (phi_contDiff.continuous.measurable.comp (by fun_prop)))
  have hf : Measurable f :=
    Measurable.ite (measurableSet_lt (measurable_const.mul measurable_snd) measurable_const)
      (ht.comp (measurable_const.mul measurable_fst)) measurable_const
  let C := 1/(2*w)*(normalizer*(1+2*k^2+4*w^2)+normalizer*(1+2*(2*b-k)^2+4*w^2))
  have hC : 0 ≤ C := by dsimp only [C]; have hn := normalizer_nonneg; positivity
  have hbound q : |f q| ≤ C := by
    dsimp only [f]
    split_ifs
    · simpa only [pow_zero,one_mul,abs_one] using thetaKernel_bound b k 1 w (Real.sqrt u*q.1) w hw le_rfl 0 (by norm_num)
    · simpa only [abs_zero] using hC
  have hs := linear_signal_weight Q X M R hX hM hR hiX hiR hind hzero f hf C a hbound
  have he ω : barrierWeight (thetaKernel b k 1 w) b
      (Real.sqrt u*X ω,u^(1/2:ℝ)*(a*X ω+R ω),Real.sqrt u*M ω) =
      Real.sqrt u*(f (X ω,M ω)*(a*X ω+R ω)) := by
    rw [← Real.sqrt_eq_rpow]
    dsimp only [barrierWeight,f]
    split_ifs <;> ring
  have he' ω : barrierWeight (fun x => x*thetaKernel b k 1 w x) b
      (Real.sqrt u*X ω,(1:ℝ),Real.sqrt u*M ω) = Real.sqrt u*(f (X ω,M ω)*X ω) := by
    dsimp only [barrierWeight,f]
    split_ifs <;> ring
  change (∫ ω, barrierWeight (thetaKernel b k 1 w) b _ ∂Q)=_
  simp_rw [he]
  rw [integral_const_mul,hs]
  have hmom := limit_psi_first_moment P Q B X M hX hM hlaw b k u hb hu
  change (∫ ω, barrierWeight (fun x => x*thetaKernel b k 1 w x) b _ ∂Q)=_ at hmom
  simp_rw [he'] at hmom
  rw [integral_const_mul] at hmom
  calc
    _ = a*(Real.sqrt u*(∫ ω, f (X ω,M ω)*X ω ∂Q)) := by ring
    _ = _ := by rw [hmom]; ring

/-- The coefficient reduction in Corollary 1, expressed through a centered
independent residual. -/
theorem linear_alpha {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M R : Γ → ℝ)
    (hX : Measurable X) (hM : Measurable M) (hR : Measurable R)
    (hiX : Integrable X Q) (hiR : Integrable R Q)
    (hind : IndepFun R (fun ω => (X ω,M ω)) Q) (hzero : ∫ ω, R ω ∂Q=0)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (a b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    alpha Q X (fun ω => a*X ω+R ω) M b k (1/2) = (a/2)*gamma b k := by
  unfold alpha
  have he : (∫ u in (0:ℝ)..1, ∫ ω, barrierWeight (thetaKernel b k 1 (Real.sqrt (1-u))) b
      (Real.sqrt u*X ω,u^(1/2:ℝ)*(a*X ω+R ω),Real.sqrt u*M ω) ∂Q) =
      ∫ u in (0:ℝ)..1, -(a/2)*barPsi b k u := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact linear_alpha_slice P Q B X M R hX hM hR hiX hiR hind hzero hlaw a b k u hb hu
  rw [he,intervalIntegral.integral_const_mul,gamma_integral P B b k hb hk]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.linear_alpha_slice
#print axioms BarrierManuscript.linear_alpha
