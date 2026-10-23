import ManuscriptStockExpectation
import ManuscriptIntegratedPolynomial
import ManuscriptSurvivalKernel

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Data for a normalized, maturity-stopped stock. All fields are model and
regularity assumptions; no pricing or asymptotic conclusion is a field. -/
structure NormalizedBarrierModel {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (b k : ℝ) where
  F : HalfClosedTime → MeasurableSpace Ω
  hF : Monotone F
  hle : ∀ t, F t ≤ m
  hnull : ∀ t E, MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E
  X : HalfClosedTime → Ω → ℝ
  C : HalfClosedTime → Ω → ℝ
  hX : LocalMProcessWitness P F X
  hXm : ∀ t, Measurable[F t] (X t)
  hXc : ∀ ω, Continuous (fun t => X t ω)
  hC : LocalCovarianceWitness P F X X C
  a : ℝ → ℝ
  ham : Measurable a
  hai : IntervalIntegrable a volume 0 1
  c : ℝ
  U : ℝ
  hc : 0 < c
  hU : 0 ≤ U
  ha : ∀ s ∈ Icc (0:ℝ) 1, c^2 ≤ a s ∧ a s ≤ U^2
  G : Ω × ℝ → ℝ
  Y : Ω × ℝ → ℝ
  hYm : Measurable Y
  hGm : ∀ ω, Measurable (fun r => G (ω,r))
  hGi : ∀ r, 0 ≤ r → ∀ᵐ ω ∂P, IntervalIntegrable (fun s => G (ω,s)) volume 0 r
  hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω = ∫ s in 0..r, G (ω,s)
  e : ℝ
  h : ℝ
  L : ℝ
  lower : ℝ
  hYs : ∀ s ∈ Ioo (0:ℝ) 1, Integrable (fun ω => Y (ω,s)) P
  hYL : ∀ s ∈ Ioo (0:ℝ) 1, (∫ ω, |Y (ω,s)| ∂P) ≤ L
  hG : ∀ᵐ z ∂P.prod (volume.restrict (Ioo (0:ℝ) 1)),
    G z = a z.2*(1+e*X (realTimeClamp z.2) z.1)^2*(1+h*Y z)
  hlower : ∀ᵐ ω ∂P, ∀ t, lower ≤ X t ω

namespace NormalizedBarrierModel
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {b k : ℝ} (M : NormalizedBarrierModel P b k)

noncomputable def kernel := stoppedThetaKernel M.X M.a b k
noncomputable def state (z : Ω × ℝ) := M.X (realTimeClamp z.2) z.1
noncomputable def bound := M.U^2/(2*M.c)*(normalizer*(1+2*k^2+4*M.U^2)+normalizer*(1+2*(2*b-k)^2+4*M.U^2))
noncomputable def price := ∫ ω, if (∃ r : HalfClosedTime, r ≤ realTimeClamp 1 ∧ M.X r ω = b)
  then 0 else max (k-M.X (realTimeClamp 1) ω) 0 ∂P
noncomputable def base := killedPut b k 0 (Real.sqrt (∫ s in (0:ℝ)..1, M.a s))
noncomputable def coefficient (j : ℕ) (Y : Ω × ℝ → ℝ) :=
  ∫ z, M.state z^j*M.kernel z*Y z ∂P.prod (volume.restrict (Ioo 0 1))

theorem state_measurable : Measurable M.state := stock_real_joint_measurable M.F M.hle M.X M.hXm M.hXc

theorem kernel_measurable : Measurable M.kernel :=
  stoppedThetaKernel_measurable M.F M.hF M.hle M.X M.hXm M.hXc M.a M.ham M.hai b k

theorem bound_nonneg : 0 ≤ M.bound := by
  have hc := M.hc
  have hn := normalizer_nonneg
  unfold bound
  positivity

theorem kernel_bound (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) (j : ℕ) (hj : j ≤ 2) (ω : Ω) :
    |M.state (ω,s)|^j*|M.kernel (ω,s)| ≤ M.bound/Real.sqrt (1-s) :=
  stoppedThetaKernel_weighted_bound M.X M.a M.hai b k M.c M.U M.hc M.hU M.ha s hs j hj ω

theorem coefficient_integrable (j : ℕ) (hj : j ≤ 2) (Y : Ω × ℝ → ℝ) (hYm : Measurable Y)
    (L : ℝ) (hYs : ∀ s ∈ Ioo (0:ℝ) 1, Integrable (fun ω => Y (ω,s)) P)
    (hYL : ∀ s ∈ Ioo (0:ℝ) 1, (∫ ω, |Y (ω,s)| ∂P) ≤ L) :
    Integrable (fun z => M.state z^j*M.kernel z*Y z) (P.prod (volume.restrict (Ioo 0 1))) :=
  (joint_weighted_kernel P M.state M.kernel Y M.state_measurable M.kernel_measurable hYm
    j M.bound L M.bound_nonneg hYs hYL (fun s hs => ae_of_all _ (M.kernel_bound s hs j hj))).1

theorem coefficient_time (j : ℕ) (Y : Ω × ℝ → ℝ)
    (hi : Integrable (fun z => M.state z^j*M.kernel z*Y z) (P.prod (volume.restrict (Ioo 0 1)))) :
    M.coefficient j Y = ∫ s in (0:ℝ)..1, ∫ ω, M.state (ω,s)^j*M.kernel (ω,s)*Y (ω,s) ∂P := by
  simpa only [coefficient,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] using integral_prod_symm _ hi

theorem coefficient_bound (j : ℕ) (hj : j ≤ 2) (Y : Ω × ℝ → ℝ) (hYm : Measurable Y)
    (L : ℝ) (hYs : ∀ s ∈ Ioo (0:ℝ) 1, Integrable (fun ω => Y (ω,s)) P)
    (hYL : ∀ s ∈ Ioo (0:ℝ) 1, (∫ ω, |Y (ω,s)| ∂P) ≤ L) :
    |M.coefficient j Y| ≤ 2*(M.bound*L) := by
  rw [M.coefficient_time j Y (M.coefficient_integrable j hj Y hYm L hYs hYL)]
  exact (joint_weighted_kernel P M.state M.kernel Y M.state_measurable M.kernel_measurable hYm
    j M.bound L M.bound_nonneg hYs hYL (fun s hs => ae_of_all _ (M.kernel_bound s hs j hj))).2

/-- The five-term pricing identity follows from the stock Ito representation,
with every spatial/time integral justified by the Gaussian bounds. -/
theorem price_expansion (hb : 0 < b) (hk : k ≤ b) :
    M.price = M.base - (2*M.e*M.coefficient 1 (fun _ => 1)+M.h*M.coefficient 0 M.Y+
      M.e^2*M.coefficient 2 (fun _ => 1)+2*M.e*M.h*M.coefficient 1 M.Y+
      M.e^2*M.h*M.coefficient 2 M.Y) := by
  have hc j (hj : j ≤ 2) := M.coefficient_integrable j hj (fun _ => 1) measurable_const 1
    (fun _ _ => integrable_const 1) (fun _ _ => by simp)
  have hy j (hj : j ≤ 2) := M.coefficient_integrable j hj M.Y M.hYm M.L M.hYs M.hYL
  have hA : Integrable (fun z => M.state z*M.kernel z) (P.prod (volume.restrict (Ioo 0 1))) := by
    simpa only [pow_one,mul_one] using hc 1 (by norm_num)
  have hB : Integrable (fun z => M.kernel z*M.Y z) (P.prod (volume.restrict (Ioo 0 1))) := by
    simpa only [pow_zero,one_mul] using hy 0 (by norm_num)
  have h0 : Integrable (fun z => M.state z^2*M.kernel z) (P.prod (volume.restrict (Ioo 0 1))) := by
    simpa only [mul_one] using hc 2 le_rfl
  have h1 : Integrable (fun z => M.state z*M.kernel z*M.Y z) (P.prod (volume.restrict (Ioo 0 1))) := by
    simpa only [pow_one] using hy 1 (by norm_num)
  have h2 := hy 2 le_rfl
  have hdi := stock_barrier_drift_integrable P M.F M.hF M.hle M.X M.hXm M.hXc
    M.G M.Y M.hYm M.a M.ham M.hai b k M.e M.h M.c M.U M.L M.hc M.hU M.ha M.hYs M.hYL M.hG
  have hp := stock_payoff_expectation P M.F M.hF M.hle M.hnull M.X M.C M.hX M.hXm M.hXc M.hC
    M.a M.ham M.hai M.c M.U M.hc M.hU M.ha M.G M.Y M.hYm M.hGm M.hGi M.hCG
    M.e M.h M.L M.lower b k hb hk M.hYs M.hYL M.hG M.hlower
  change M.price = M.base + _ at hp
  have hfub : (∫ s in (0:ℝ)..1, ∫ ω, barrierDrift M.X M.G M.a b k (ω,s) ∂P) =
      ∫ z, barrierDrift M.X M.G M.a b k z ∂P.prod (volume.restrict (Ioo 0 1)) := by
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo] using (integral_prod_symm _ hdi).symm
  have hd : (∫ z, barrierDrift M.X M.G M.a b k z ∂P.prod (volume.restrict (Ioo 0 1))) =
      -(∫ z, M.kernel z*((1+M.e*M.state z)^2*(1+M.h*M.Y z)-1) ∂P.prod (volume.restrict (Ioo 0 1))) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [M.hG] with z hz
    rw [barrier_drift_polynomial M.X M.G M.Y M.a b k M.e M.h z hz]
    change -M.kernel z * _ = -(M.kernel z * _)
    dsimp only [state]
    ring
  rw [hfub,hd,polynomial_integral_decomposition _ M.state M.kernel M.Y M.e M.h hA hB h0 h1 h2] at hp
  simpa only [coefficient,pow_one,pow_zero,one_mul,mul_one,sub_eq_add_neg] using hp

end NormalizedBarrierModel
end BarrierManuscript
#print axioms BarrierManuscript.NormalizedBarrierModel.state_measurable
#print axioms BarrierManuscript.NormalizedBarrierModel.kernel_measurable
#print axioms BarrierManuscript.NormalizedBarrierModel.bound_nonneg
#print axioms BarrierManuscript.NormalizedBarrierModel.kernel_bound
#print axioms BarrierManuscript.NormalizedBarrierModel.coefficient_integrable
#print axioms BarrierManuscript.NormalizedBarrierModel.coefficient_time
#print axioms BarrierManuscript.NormalizedBarrierModel.coefficient_bound

#print axioms BarrierManuscript.NormalizedBarrierModel.price_expansion
