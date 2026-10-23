import ManuscriptStockCLT
import ManuscriptMaturityRescaling
import ManuscriptStockCoefficients

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem finite_real_joint_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (F : HalfClosedTime → MeasurableSpace Ω) (hle : ∀ t, F t ≤ m)
    (X : HalfClosedTime → Ω → ℝ) (hm : ∀ t, t < ⊤ → Measurable[F t] (X t))
    (hc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => X s ω) t) :
    Measurable (fun z : Ω × ℝ => X (realTimeClamp z.2) z.1) :=
  (measurable_uncurry_of_continuous_of_measurable (continuous_real_path X hc)
    (fun r => (hm _ (halfTimeClamp_finite r)).mono (hle _) le_rfl)).comp measurable_swap

/-- Construct the normalized pricing model from the original stock SDE at a
fixed positive maturity. The only fluctuation estimate supplied is its first
absolute moment; the covariance and stopped regularity are derived. -/
theorem stock_model_exists {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (S V : HalfClosedTime → Ω → ℝ) (S₀ v₀ θ H : ℝ)
    (hS₀ : 0 < S₀) (hv₀ : 0 < v₀) (hθ : 0 < θ)
    (hSa : ∀ t, t < ⊤ → Measurable[B.F t] (S t))
    (hVa : ∀ t, t < ⊤ → Measurable[B.F t] (V t))
    (hSc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => S s ω) t)
    (hVc : ∀ ω t, t < ⊤ → ContinuousAt (fun s => V s ω) t)
    (hSpos : ∀ ω t, t < ⊤ → 0 ≤ S t ω)
    (hV : ∀ ω r, 0 ≤ r → 0 ≤ V (realTimeClamp r) ω)
    (hM : LocalMProcessWitness P B.F (fun t ω => S t ω/S₀-1))
    (hSDE : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => (S (realTimeClamp z.2) z.1/S₀)*Real.sqrt (V (realTimeClamp z.2) z.1))
      (fun t ω => S t ω/S₀-1))
    (a : ℝ → ℝ) (ham : Measurable a) (hai : IntervalIntegrable a volume 0 1)
    (c U L b k : ℝ) (hc : 0 < c) (hU : 0 ≤ U)
    (ha : ∀ s ∈ Icc (0:ℝ) 1, c^2 ≤ a s ∧ a s ≤ U^2)
    (hYs : ∀ u ∈ Ioo (0:ℝ) 1,
      Integrable (fun ω => (V (realTimeClamp (θ*u)) ω/(v₀*a u)-1)/θ^H) P)
    (hYL : ∀ u ∈ Ioo (0:ℝ) 1,
      (∫ ω, |(V (realTimeClamp (θ*u)) ω/(v₀*a u)-1)/θ^H| ∂P) ≤ L) :
    ∃ M : NormalizedBarrierModel P b k,
      M.a = a ∧ M.c = c ∧ M.U = U ∧ M.L = L ∧
      M.e = Real.sqrt (θ*v₀) ∧ M.h = θ^H ∧
      M.X = (fun t ω => (S (linearClock θ hθ (min (realTimeClamp 1) t)) ω/S₀-1)/Real.sqrt (θ*v₀)) ∧
      M.Y = (fun z => (V (realTimeClamp (θ*z.2)) z.1/(v₀*a z.2)-1)/θ^H) := by
  obtain ⟨C,hC,hCG⟩ := stock_return_bracket P B S V S₀ hSa hVa hSc hVc hV hM hSDE
  let F := fun t => B.F (linearClock θ hθ t)
  let X := fun t ω => (S (linearClock θ hθ (min (realTimeClamp 1) t)) ω/S₀-1)/Real.sqrt (θ*v₀)
  let D := fun t ω => C (linearClock θ hθ (min (realTimeClamp 1) t)) ω/(θ*v₀)
  let G : Ω × ℝ → ℝ := fun z => if z.2 ≤ 1 then
    (S (realTimeClamp (θ*z.2)) z.1/S₀)^2*V (realTimeClamp (θ*z.2)) z.1/v₀ else 0
  let Y : Ω × ℝ → ℝ := fun z => (V (realTimeClamp (θ*z.2)) z.1/(v₀*a z.2)-1)/θ^H
  have hres := maturity_rescaled_martingale P B.F B.mono B.le
    (fun t ω => S t ω/S₀-1) C hM hC
    (fun z => (S (realTimeClamp z.2) z.1/S₀)^2*V (realTimeClamp z.2) z.1) hCG θ v₀ hθ hv₀
  have hYmeas : Measurable Y := by
    have hvm : Measurable (fun z : Ω × ℝ => V (realTimeClamp (θ*z.2)) z.1) := (finite_real_joint_measurable B.F B.le V hVa hVc).comp
      (measurable_fst.prodMk (measurable_const.mul measurable_snd))
    exact ((hvm.div (measurable_const.mul (ham.comp measurable_snd))).sub_const 1).div_const (θ^H)
  have hgcont ω : Continuous (fun u : ℝ => (S (realTimeClamp (θ*u)) ω/S₀)^2*
      V (realTimeClamp (θ*u)) ω/v₀) := by
    exact ((((continuous_real_path S hSc ω).comp (continuous_const.mul continuous_id)).div_const S₀).pow 2 |>.mul
      ((continuous_real_path V hVc ω).comp (continuous_const.mul continuous_id))).div_const v₀
  have hGm ω : Measurable (fun u => G (ω,u)) :=
    (hgcont ω).measurable.ite measurableSet_Iic measurable_const
  have hGi r (hr : 0 ≤ r) : ∀ᵐ ω ∂P, IntervalIntegrable (fun u => G (ω,u)) volume 0 r := by
    apply ae_of_all
    intro ω
    exact intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp ((hgcont ω).intervalIntegrable 0 r)).indicator measurableSet_Iic)
  have hpoly : ∀ᵐ z ∂P.prod (volume.restrict (Ioo (0:ℝ) 1)),
      G z = a z.2*(1+Real.sqrt (θ*v₀)*X (realTimeClamp z.2) z.1)^2*(1+θ^H*Y z) := by
    have ht : ∀ᵐ z ∂P.prod (volume.restrict (Ioo (0:ℝ) 1)), z.2 ∈ Ioo (0:ℝ) 1 :=
      (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).mpr
        (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioo)
    filter_upwards [ht] with z hz
    rcases z with ⟨ω,u⟩
    have hu : u ∈ Ioo (0:ℝ) 1 := hz
    have ha₀ : a u ≠ 0 := ne_of_gt ((sq_pos_of_pos hc).trans_le (ha u ⟨hu.1.le,hu.2.le⟩).1)
    dsimp only [G,X,Y]
    rw [if_pos hu.2.le,min_eq_right (real_time_clamp_mono hu.2.le),linear_clock_finite θ hθ u hu.1.le]
    exact normalized_stock_density_algebra _ S₀ _ v₀ (a u) _ _
      (Real.sqrt_pos.mpr (mul_pos hθ hv₀)).ne' (Real.rpow_pos_of_pos hθ H).ne' hv₀.ne' ha₀
  have hlower : ∀ᵐ ω ∂P, ∀ t, -1/Real.sqrt (θ*v₀) ≤ X t ω := by
    apply ae_of_all
    intro ω t
    apply (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr (mul_pos hθ hv₀))).mpr
    have htime : linearClock θ hθ (min (realTimeClamp 1) t) < ⊤ := by
      rw [← (linearClock θ hθ).map_top]
      exact (linearClock θ hθ).strictMono ((min_le_left _ _).trans_lt (changed_time_finite 1 (by norm_num)))
    linarith [div_nonneg (hSpos ω _ htime) hS₀.le]
  let M : NormalizedBarrierModel P b k := {
    F := F, hF := B.mono.comp (linearClock θ hθ).monotone, hle := fun t => B.le _,
    hnull := fun t E hm hz => B.null _ E hm hz,
    X := X, C := D, hX := hres.1, hXm := hres.2.2.1, hXc := hres.2.2.2.1, hC := hres.2.1,
    a := a, ham := ham, hai := hai, c := c, U := U, hc := hc, hU := hU, ha := ha,
    G := G, Y := Y, hYm := hYmeas, hGm := hGm, hGi := hGi, hCG := hres.2.2.2.2,
    e := Real.sqrt (θ*v₀), h := θ^H, L := L, lower := -1/Real.sqrt (θ*v₀),
    hYs := hYs, hYL := hYL, hG := hpoly, hlower := hlower }
  exact ⟨M,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end BarrierManuscript
#print axioms BarrierManuscript.finite_real_joint_measurable
#print axioms BarrierManuscript.stock_model_exists
