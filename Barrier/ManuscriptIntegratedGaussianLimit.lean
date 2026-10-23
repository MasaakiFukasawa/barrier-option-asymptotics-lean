import ManuscriptGaussianWeakLimit
import ManuscriptIntegratedBounds

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem barrier_weight_L1_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ × ℝ × ℝ) (hZ : AEMeasurable Z P)
    (hY : Integrable (fun ω => (Z ω).2.1) P)
    (w : ℝ → ℝ) (hw : Continuous w) (b A : ℝ) (hA : 0 ≤ A) (hb : ∀ x, |w x| ≤ A) :
    Integrable (fun ω => barrierWeight w b (Z ω)) P ∧
      |∫ ω, barrierWeight w b (Z ω) ∂P| ≤ A*(∫ ω, |(Z ω).2.1| ∂P) := by
  have hm : Measurable (barrierWeight w b) := by
    unfold barrierWeight
    exact Measurable.ite (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_const)
      ((hw.measurable.comp measurable_fst).mul (measurable_fst.comp measurable_snd)) measurable_const
  have hd : ∀ᵐ ω ∂P, ‖barrierWeight w b (Z ω)‖ ≤ A*|(Z ω).2.1| := by
    apply ae_of_all
    intro ω
    simp only [barrierWeight,Real.norm_eq_abs]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)
    · simpa using mul_nonneg hA (abs_nonneg (Z ω).2.1)
  have hi := (hY.abs.const_mul A).mono' (hm.comp_aemeasurable hZ).aestronglyMeasurable hd
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, ‖barrierWeight w b (Z ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, A*|(Z ω).2.1| ∂P := integral_mono_ae hi.norm (hY.abs.const_mul A) hd
    _ = _ := integral_const_mul _ _

/-- The actual Gaussian weak limits can be integrated through the singular
terminal bound. This assembles the spatial/UI and time-DCT steps. -/
theorem integrated_gaussian_weak_limit {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : ℕ → ℝ → Ω → ℝ × ℝ × ℝ) (z : ℝ → Γ → ℝ × ℝ × ℝ)
    (h : ∀ u ∈ Ioo (0:ℝ) 1, TendstoInDistribution (fun n => Z n u) atTop (z u) (fun _ => P) Q)
    (hui : ∀ u ∈ Ioo (0:ℝ) 1, UniformIntegrable (fun n ω => (Z n u ω).2.1) 1 P)
    (v w : ℕ → ℝ → ℝ) (v₀ w₀ : ℝ → ℝ)
    (hvlim : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => v n u) atTop (𝓝 (v₀ u)))
    (hwlim : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => w n u) atTop (𝓝 (w₀ u)))
    (hw₀ : ∀ u ∈ Ioo (0:ℝ) 1, 0 < w₀ u)
    (c V W L : ℝ) (hc : 0 < c) (hV₀ : 0 ≤ V)
    (hV : ∀ n u, u ∈ Ioo (0:ℝ) 1 → |v n u| ≤ V)
    (hcw : ∀ n u, u ∈ Ioo (0:ℝ) 1 → c*Real.sqrt (1-u) ≤ w n u)
    (hwW : ∀ n u, u ∈ Ioo (0:ℝ) 1 → w n u ≤ W)
    (hL : ∀ n u, u ∈ Ioo (0:ℝ) 1 → (∫ ω, |(Z n u ω).2.1| ∂P) ≤ L)
    (b k : ℝ) (j : ℕ) (hj : j ≤ 2)
    (hnoatom : ∀ u ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂Q, (z u ω).2.2 ≠ b)
    (hm : ∀ n, AEStronglyMeasurable (fun u => ∫ ω,
      barrierWeight (fun x => x^j*thetaKernel b k (v n u) (w n u) x) b (Z n u ω) ∂P)
        (volume.restrict (Ioo 0 1))) :
    let f := fun n u => ∫ ω, barrierWeight (fun x => x^j*thetaKernel b k (v n u) (w n u) x) b (Z n u ω) ∂P
    let g := fun u => ∫ ω, barrierWeight (fun x => x^j*thetaKernel b k (v₀ u) (w₀ u) x) b (z u ω) ∂Q
    IntervalIntegrable g volume 0 1 ∧ Tendsto (fun n => ∫ u in (0:ℝ)..1, f n u) atTop
      (𝓝 (∫ u in (0:ℝ)..1, g u)) := by
  dsimp only
  let A := V/(2*c)*(normalizer*(1+2*k^2+4*W^2)+normalizer*(1+2*(2*b-k)^2+4*W^2))
  have hn := normalizer_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply singular_time_dominated_convergence _ _ (A*L) hm
  · intro n u hu
    have hwp : 0 < w n u := (mul_pos hc (Real.sqrt_pos.mpr (sub_pos.mpr hu.2))).trans_le (hcw n u hu)
    have hweight : Continuous (fun x => x^j*thetaKernel b k (v n u) (w n u) x) := by
      unfold thetaKernel
      exact (continuous_id.pow j).mul (continuous_const.mul
        ((phi_contDiff.continuous.comp (by fun_prop)).sub (phi_contDiff.continuous.comp (by fun_prop))))
    have hb x : |x^j*thetaKernel b k (v n u) (w n u) x| ≤ A/Real.sqrt (1-u) := by
      rw [abs_mul,abs_pow]
      exact thetaKernel_time_domination b k (v n u) (w n u) x W V c u hu.2 hc (hcw n u hu)
        (hwW n u hu) (hV n u hu) j hj
    have he := (barrier_weight_L1_bound P (Z n u) ((h u hu).forall_aemeasurable n)
      ((hui u hu).memLp n |>.integrable le_rfl) _ hweight b (A/Real.sqrt (1-u))
      (div_nonneg hA (Real.sqrt_nonneg _)) hb).2
    calc
      _ ≤ (A/Real.sqrt (1-u))*(∫ ω, |(Z n u ω).2.1| ∂P) := he
      _ ≤ (A/Real.sqrt (1-u))*L := mul_le_mul_of_nonneg_left (hL n u hu) (by positivity)
      _ = _ := by ring
  · intro u hu
    exact (gaussian_weighted_weak_limit P Q (fun n => Z n u) (z u) (h u hu) (hui u hu)
      (fun n => v n u) (fun n => w n u) (v₀ u) (w₀ u) (hvlim u hu) (hwlim u hu) (hw₀ u hu)
      (c*Real.sqrt (1-u)) V W (mul_pos hc (Real.sqrt_pos.mpr (sub_pos.mpr hu.2)))
      (fun n => hV n u hu) (fun n => hcw n u hu) (fun n => hwW n u hu) b k j hj (hnoatom u hu)).2

end BarrierManuscript
#print axioms BarrierManuscript.barrier_weight_L1_bound
#print axioms BarrierManuscript.integrated_gaussian_weak_limit
