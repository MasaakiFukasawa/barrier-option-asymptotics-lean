import ManuscriptWeakMapping
import ManuscriptUniformIntegrability

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

noncomputable def boundedPositiveTruncation (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (N : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => min (f x) (N:ℝ), hf.min continuous_const⟩ N
    (fun x y => by
      change |min (f x) (N:ℝ) - min (f y) (N:ℝ)| ≤ N
      have hx := le_min (hn x) (Nat.cast_nonneg N)
      have hy := le_min (hn y) (Nat.cast_nonneg N)
      exact abs_le.mpr ⟨by linarith [min_le_right (f y) (N:ℝ)],
        by linarith [min_le_right (f x) (N:ℝ)]⟩)

/-- A nonnegative continuous moment bound passes to a weak limit. The
integrability of the limit is proved by truncation and Fatou. -/
theorem weak_nonnegative_moment_bound {Ω Γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Z : Γ → ℝ)
    (h : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) (C : ℝ)
    (hXi : ∀ n, Integrable (fun ω => f (X n ω)) P)
    (hC : ∀ n, (∫ ω, f (X n ω) ∂P) ≤ C) :
    Integrable (fun ω => f (Z ω)) Q ∧ (∫ ω, f (Z ω) ∂Q) ≤ C := by
  let b (N : ℕ) := boundedPositiveTruncation f hf hn N
  have hb (N : ℕ) : Tendsto (fun n => ∫ ω, b N (X n ω) ∂P) atTop
      (𝓝 (∫ ω, b N (Z ω) ∂Q)) :=
    (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      h.forall_aemeasurable h.aemeasurable_limit).mp h (b N)
  have hbm (N : ℕ) : AEStronglyMeasurable (fun ω => b N (Z ω)) Q :=
    ((b N).continuous.measurable.comp_aemeasurable h.aemeasurable_limit).aestronglyMeasurable
  have hbi (N : ℕ) : Integrable (fun ω => b N (Z ω)) Q := by
    apply (integrable_const (μ := Q) (N:ℝ)).mono' (hbm N)
    apply ae_of_all
    intro ω
    change |min (f (Z ω)) (N:ℝ)| ≤ N
    rw [abs_of_nonneg (le_min (hn _) (Nat.cast_nonneg N))]
    exact min_le_right _ _
  have hbe (N : ℕ) : (∫ ω, b N (Z ω) ∂Q) ≤ C := by
    apply le_of_tendsto (hb N)
    apply Eventually.of_forall
    intro n
    have hni : Integrable (fun ω => b N (X n ω)) P := by
      apply (integrable_const (μ := P) (N:ℝ)).mono'
        (((b N).continuous.measurable.comp_aemeasurable (h.forall_aemeasurable n)).aestronglyMeasurable)
      apply ae_of_all
      intro ω
      change |min (f (X n ω)) (N:ℝ)| ≤ N
      rw [abs_of_nonneg (le_min (hn _) (Nat.cast_nonneg N))]
      exact min_le_right _ _
    exact (integral_mono hni (hXi n) (fun ω => min_le_left _ _)).trans (hC n)
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun N => b N (Z ω)) atTop (𝓝 (f (Z ω))) := by
    apply ae_of_all
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (f (Z ω)))] with N hN
    exact (min_eq_left hN).symm
  have hfm : AEStronglyMeasurable (fun ω => f (Z ω)) Q :=
    (hf.measurable.comp_aemeasurable h.aemeasurable_limit).aestronglyMeasurable
  have hnorm (N : ℕ) : eLpNorm (fun ω => b N (Z ω)) 1 Q ≤ ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm (hbm N),
      ← ofReal_integral_norm_eq_lintegral_enorm (hbi N)]
    apply ENNReal.ofReal_le_ofReal
    have he : (fun ω => ‖b N (Z ω)‖) = (fun ω => b N (Z ω)) := by
      funext ω
      exact abs_of_nonneg (le_min (hn _) (Nat.cast_nonneg N))
    rw [he]
    exact hbe N
  have hl := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hnorm) hbm hfm hlim
  have hi : Integrable (fun ω => f (Z ω)) Q :=
    memLp_one_iff_integrable.mp (show MemLp (fun ω => f (Z ω)) 1 Q from
      hl.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  have hCn : 0 ≤ C := (integral_nonneg (fun ω => hn (X 0 ω))).trans (hC 0)
  rw [eLpNorm_one_eq_lintegral_enorm hfm, ← ofReal_integral_norm_eq_lintegral_enorm hi] at hl
  have he : (fun ω => ‖f (Z ω)‖) = (fun ω => f (Z ω)) := by
    funext ω; exact abs_of_nonneg (hn _)
  rw [he] at hl
  exact (ENNReal.ofReal_le_ofReal_iff hCn).mp hl

end BarrierManuscript
#print axioms BarrierManuscript.weak_nonnegative_moment_bound
