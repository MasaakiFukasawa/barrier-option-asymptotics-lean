import Chapter8MartingaleCLTVarying
import Chapter7FiniteTimeCLT

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

noncomputable def pathMaximum {K : Type*} [TopologicalSpace K]
    (f : C(K,ℝ)) : ℝ := sSup (range f)

theorem path_range_bddAbove {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f : C(K,ℝ)) : BddAbove (range f) := by
  refine ⟨‖f‖, ?_⟩
  rintro y ⟨t,rfl⟩
  exact (le_abs_self _).trans (f.norm_coe_le_norm t)

theorem pathMaximum_sub_le {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f g : C(K,ℝ)) : pathMaximum f-pathMaximum g ≤ ‖f-g‖ := by
  apply sub_le_iff_le_add.mpr
  apply csSup_le (range_nonempty f)
  rintro y ⟨t,rfl⟩
  have hd : f t-g t ≤ ‖f-g‖ :=
    (le_abs_self _).trans ((f-g).norm_coe_le_norm t)
  have hg : g t ≤ pathMaximum g := le_csSup (path_range_bddAbove g) (mem_range_self t)
  linarith

/-- Maximum is 1-Lipschitz in the uniform path norm; this is the missing
continuous-mapping step for the manuscript's running maximum. -/
theorem pathMaximum_lipschitz {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K] :
    LipschitzWith 1 (pathMaximum (K := K)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply abs_le.mpr
  constructor
  · have h := pathMaximum_sub_le g f
    rw [norm_sub_rev] at h
    linarith
  · exact pathMaximum_sub_le f g

noncomputable def endpointMaximum {K : Type*} [TopologicalSpace K]
    (t : K) (f : C(K,ℝ)) : ℝ × ℝ := (f t,pathMaximum f)

theorem endpointMaximum_continuous {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (t : K) : Continuous (endpointMaximum t) :=
  (continuous_eval_const t).prodMk pathMaximum_lipschitz.continuous

/-- Actual functional martingale CLT followed by the endpoint/maximum map.
Filtrations are allowed to depend on n, as they do after maturity rescaling. -/
theorem martingale_endpoint_maximum_limit
    {Ω Γ : Type*} [m : MeasurableSpace Ω] [q : MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : ℕ → HalfClosedTime → MeasurableSpace Ω) (hF : ∀ n, Monotone (F n))
    (hle : ∀ n t, F n t ≤ m)
    (M C : ℕ → HalfClosedTime → Ω → ℝ)
    (hM : ∀ n, LocalMProcessWitness P (F n) (M n))
    (hC : ∀ n, LocalCovarianceWitness P (F n) (M n) (M n) (C n))
    (hp : ∀ t : ℝ≥0, TendstoInMeasure P (fun n => C n (realTimeClamp t))
      atTop (fun _ => (t:ℝ)))
    (B : BrownianSystem Q 1) :
    ∃ B0 : BrownianSystem (P.prod Q) 1,
      TendstoInDistribution
        (fun n ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
          (pathRestriction 1 (localContinuousPath (M n) ((hM n).path P (F n)) ω))) atTop
        (fun ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
          (pathRestriction 1 (brownianContinuousPath B0 ω))) (fun _ => P) (P.prod Q) := by
  obtain ⟨B0,hlim⟩ := martingale_clt_varying_filtration_with_driver
    P Q F hF hle M C hM hC hp B
  refine ⟨B0, ?_⟩
  have hr : Continuous (pathRestriction (1:ℝ≥0)) := ContinuousMap.continuous_precomp _
  exact hlim.continuous_comp
    ((endpointMaximum_continuous (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)).comp hr)

/-- Uniqueness identifies the endpoint/maximum marginal of the assumed
three-dimensional limit once the functional Brownian limit is established. -/
theorem identify_endpoint_maximum_law
    {Ω Γ Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Γ) (R : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (X : ℕ → Ω → ℝ × ℝ × ℝ) (Z : Γ → ℝ × ℝ × ℝ) (B : Λ → ℝ × ℝ)
    (hjoint : TendstoInDistribution X atTop Z (fun _ => P) Q)
    (hBrownian : TendstoInDistribution (fun n ω => ((X n ω).1,(X n ω).2.2))
      atTop B (fun _ => P) R) :
    Q.map (fun ω => ((Z ω).1,(Z ω).2.2)) = R.map B := by
  have hc : Continuous (fun z : ℝ × ℝ × ℝ => (z.1,z.2.2)) := by fun_prop
  exact tendstoInDistribution_unique _ (hjoint.continuous_comp hc) hBrownian

end BarrierManuscript

#print axioms BarrierManuscript.pathMaximum_lipschitz
#print axioms BarrierManuscript.endpointMaximum_continuous
#print axioms BarrierManuscript.martingale_endpoint_maximum_limit
#print axioms BarrierManuscript.identify_endpoint_maximum_law
