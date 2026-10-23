import ManuscriptWeakExpectation
import ManuscriptTruncation

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

private theorem truncation_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Y : Ω → ℝ) (hm : AEMeasurable Y P)
    (R : ℝ) (hR : 0 ≤ R) : Integrable (fun ω => signedTruncation R (Y ω)) P := by
  apply (integrable_const (μ := P) R).mono'
    (((boundedSignedTruncation R hR).continuous.measurable.comp_aemeasurable hm).aestronglyMeasurable)
  exact ae_of_all _ fun ω => signedTruncation_bound R (Y ω) hR

/-- Uniform truncation error passes to the weak limit by the nonnegative
continuous moment lemma. -/
theorem weak_ui_truncation {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Z : Γ → ℝ)
    (h : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (hui : UniformIntegrable X 1 P) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ n, (∫ ω, |X n ω-signedTruncation R (X n ω)| ∂P) ≤ ε) ∧
      Integrable (fun ω => Z ω-signedTruncation R (Z ω)) Q ∧
      (∫ ω, |Z ω-signedTruncation R (Z ω)| ∂Q) ≤ ε := by
  obtain ⟨R,hR,he⟩ := ui_signed_truncation P X hui ε hε
  have hf : Continuous (fun x : ℝ => |x-signedTruncation R x|) := by
    unfold signedTruncation; fun_prop
  obtain ⟨hi,hb⟩ := weak_nonnegative_moment_bound P Q X Z h _ hf
    (fun _ => abs_nonneg _) ε (fun n => by simpa only [Real.norm_eq_abs] using (he n).1.norm)
    (fun n => (he n).2)
  have hm : AEStronglyMeasurable (fun ω => Z ω-signedTruncation R (Z ω)) Q := by
    exact ((show Continuous (fun x => x-signedTruncation R x) by
      unfold signedTruncation; fun_prop).measurable.comp_aemeasurable h.aemeasurable_limit).aestronglyMeasurable
  exact ⟨R,hR,fun n => (he n).2, (integrable_norm_iff hm).mp hi,hb⟩

/-- Weak convergence plus probabilistic uniform integrability implies
convergence of expectations. The limit's integrability is a conclusion,
and the random variables may live on different probability spaces. -/
theorem weak_ui_expectation_limit {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : ℕ → Ω → ℝ) (Z : Γ → ℝ)
    (h : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (hui : UniformIntegrable X 1 P) :
    Integrable Z Q ∧ Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 (∫ ω, Z ω ∂Q)) := by
  obtain ⟨R₀,hR₀,_,hi₀,_⟩ := weak_ui_truncation P Q X Z h hui 1 (by norm_num)
  have hZi : Integrable Z Q := by
    convert hi₀.add (truncation_integrable Q Z h.aemeasurable_limit R₀ hR₀) using 1
    funext ω; simp
  refine ⟨hZi, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨R,hR,hXerr,hZerr,hZbound⟩ :=
    weak_ui_truncation P Q X Z h hui (ε/3) (by positivity)
  have hc := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).mp h (boundedSignedTruncation R hR)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hc (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hiX := memLp_one_iff_integrable.mp (hui.memLp n)
  have hiTX := truncation_integrable P (X n) (h.forall_aemeasurable n) R hR
  have hiTZ := truncation_integrable Q Z h.aemeasurable_limit R hR
  have heX : |(∫ ω, X n ω ∂P)-(∫ ω, signedTruncation R (X n ω) ∂P)| ≤ ε/3 := by
    rw [← integral_sub hiX hiTX]
    calc
      _ ≤ ∫ ω, |X n ω-signedTruncation R (X n ω)| ∂P := by
        simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun ω => X n ω-signedTruncation R (X n ω)) (μ := P))
      _ ≤ ε/3 := hXerr n
  have heZ : |(∫ ω, Z ω ∂Q)-(∫ ω, signedTruncation R (Z ω) ∂Q)| ≤ ε/3 := by
    rw [← integral_sub hZi hiTZ]
    calc
      _ ≤ ∫ ω, |Z ω-signedTruncation R (Z ω)| ∂Q := by
        simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun ω => Z ω-signedTruncation R (Z ω)) (μ := Q))
      _ ≤ ε/3 := hZbound
  have hmid := hN n hn
  change |(∫ ω, signedTruncation R (X n ω) ∂P)-
    (∫ ω, signedTruncation R (Z ω) ∂Q)| < ε/3 at hmid
  rw [Real.dist_eq]
  have ht := abs_sub_le (∫ ω, X n ω ∂P)
    (∫ ω, signedTruncation R (X n ω) ∂P) (∫ ω, Z ω ∂Q)
  have ht' := abs_sub_le (∫ ω, signedTruncation R (X n ω) ∂P)
    (∫ ω, signedTruncation R (Z ω) ∂Q) (∫ ω, Z ω ∂Q)
  rw [abs_sub_comm (∫ ω, signedTruncation R (Z ω) ∂Q) (∫ ω, Z ω ∂Q)] at ht'
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.weak_ui_truncation
#print axioms BarrierManuscript.weak_ui_expectation_limit
