import ManuscriptStockCoefficients
import ManuscriptIntegratedGaussianLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable
namespace NormalizedBarrierModel
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {b k : ℝ} (M : NormalizedBarrierModel P b k)

noncomputable def triple (Y : Ω × ℝ → ℝ) (u : ℝ) (ω : Ω) : ℝ × ℝ × ℝ :=
  (M.state (ω,u),Y (ω,u),prefixMaximum M.X M.hXc (realTimeClamp u) ω)

theorem coefficient_survival_slice (hb : 0 < b) (j : ℕ) (Y : Ω × ℝ → ℝ)
    (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    (fun ω => M.state (ω,u)^j*M.kernel (ω,u)*Y (ω,u)) =ᵐ[P]
      (fun ω => barrierWeight
        (fun x => x^j*thetaKernel b k (M.a u) (remainingVol M.a u) x) b (M.triple Y u ω)) := by
  filter_upwards [M.hX.initial P M.F] with ω hi
  have hinit : M.X ⊥ ω < b := by simpa only [hi,Pi.zero_apply] using hb
  dsimp only [kernel]
  rw [stoppedThetaKernel_survival M.X M.hXc M.a b k u hu ω hinit,
    varianceClock_remaining M.a M.hai u ⟨hu.1.le,hu.2.le⟩]
  simp only [barrierWeight,triple,remainingVol,state]
  split_ifs <;> ring

theorem coefficient_survival_time (hb : 0 < b) (j : ℕ) (Y : Ω × ℝ → ℝ)
    (hi : Integrable (fun z => M.state z^j*M.kernel z*Y z) (P.prod (volume.restrict (Ioo 0 1)))) :
    M.coefficient j Y = ∫ u in (0:ℝ)..1, ∫ ω,
      barrierWeight (fun x => x^j*thetaKernel b k (M.a u) (remainingVol M.a u) x) b
        (M.triple Y u ω) ∂P := by
  rw [M.coefficient_time j Y hi]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact integral_congr_ae (M.coefficient_survival_slice hb j Y u hu)

end NormalizedBarrierModel

/-- The limits of the actual stock coefficients, joining the stopping-time
identity, Gaussian weak/UI limit, and time dominated convergence. -/
theorem stock_coefficient_limit {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (b k : ℝ) (hb : 0 < b) (M : ℕ → NormalizedBarrierModel P b k)
    (Y : ℕ → Ω × ℝ → ℝ) (hYm : ∀ n, Measurable (Y n))
    (z : ℝ → Γ → ℝ × ℝ × ℝ)
    (hlaw : ∀ u ∈ Ioo (0:ℝ) 1, TendstoInDistribution
      (fun n => (M n).triple (Y n) u) atTop (z u) (fun _ => P) Q)
    (hui : ∀ u ∈ Ioo (0:ℝ) 1, UniformIntegrable (fun n ω => Y n (ω,u)) 1 P)
    (ha : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => (M n).a u) atTop (𝓝 1))
    (hw : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => remainingVol (M n).a u) atTop (𝓝 (Real.sqrt (1-u))))
    (c V W L : ℝ) (hc : 0 < c) (hV : 0 ≤ V)
    (hav : ∀ n u, u ∈ Ioo (0:ℝ) 1 → |(M n).a u| ≤ V)
    (hcw : ∀ n u, u ∈ Ioo (0:ℝ) 1 → c*Real.sqrt (1-u) ≤ remainingVol (M n).a u)
    (hwW : ∀ n u, u ∈ Ioo (0:ℝ) 1 → remainingVol (M n).a u ≤ W)
    (hL : ∀ n u, u ∈ Ioo (0:ℝ) 1 → (∫ ω, |Y n (ω,u)| ∂P) ≤ L)
    (hnoatom : ∀ u ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂Q, (z u ω).2.2 ≠ b)
    (j : ℕ) (hj : j ≤ 2) :
    Tendsto (fun n => (M n).coefficient j (Y n)) atTop
      (𝓝 (∫ u in (0:ℝ)..1, ∫ ω,
        barrierWeight (fun x => x^j*thetaKernel b k 1 (Real.sqrt (1-u)) x) b (z u ω) ∂Q)) := by
  have hi n := (M n).coefficient_integrable j hj (Y n) (hYm n) L
    (fun u hu => (hui u hu).memLp n |>.integrable le_rfl) (hL n)
  have hmeas n : AEStronglyMeasurable (fun u => ∫ ω,
      barrierWeight (fun x => x^j*thetaKernel b k ((M n).a u) (remainingVol (M n).a u) x) b
        ((M n).triple (Y n) u ω) ∂P) (volume.restrict (Ioo 0 1)) := by
    have hm := (((M n).state_measurable.pow_const j).mul (M n).kernel_measurable).mul (hYm n)
    have hma : AEStronglyMeasurable (fun q => (M n).state q^j*(M n).kernel q*Y n q)
        (P.prod (volume.restrict (Ioo (0:ℝ) 1))) := hm.aestronglyMeasurable
    apply hma.prod_swap.integral_prod_right'.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact integral_congr_ae ((M n).coefficient_survival_slice hb j (Y n) u hu)
  have hlim := (integrated_gaussian_weak_limit P Q (fun n => (M n).triple (Y n)) z hlaw hui
    (fun n => (M n).a) (fun n => remainingVol (M n).a) (fun _ => 1) (fun u => Real.sqrt (1-u))
    ha hw (fun u hu => Real.sqrt_pos.mpr (sub_pos.mpr hu.2)) c V W L hc hV hav hcw hwW hL
    b k j hj hnoatom hmeas).2
  exact hlim.congr (fun n => ((M n).coefficient_survival_time hb j (Y n) (hi n)).symm)

end BarrierManuscript
#print axioms BarrierManuscript.NormalizedBarrierModel.coefficient_survival_slice
#print axioms BarrierManuscript.NormalizedBarrierModel.coefficient_survival_time
#print axioms BarrierManuscript.stock_coefficient_limit
