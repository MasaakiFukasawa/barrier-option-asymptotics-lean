import ManuscriptMaximumEncoding
import ManuscriptGaussianWeakLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Transfer the derived Brownian no-atom property to the maximum coordinate
of the manuscript's assumed triple limit, using the identified marginal law. -/
theorem limit_maximum_noatom {Γ Λ : Type*} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (Q : Measure Γ) (R : Measure Λ) [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (Z : Γ → ℝ × ℝ × ℝ) (hZ : AEMeasurable Z Q) (B : BrownianSystem R 1)
    (hlaw : Q.map (fun ω => ((Z ω).1,(Z ω).2.2)) =
      R.map (fun ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
        (pathRestriction 1 (brownianContinuousPath B ω))))
    (b : ℝ) (hb : 0 < b) : ∀ᵐ ω ∂Q, (Z ω).2.2 ≠ b := by
  let A : Set (ℝ × ℝ) := {z | z.2=b}
  have hA : MeasurableSet A := measurableSet_eq_fun measurable_snd measurable_const
  have hZm : AEMeasurable (fun ω => ((Z ω).1,(Z ω).2.2)) Q :=
    hZ.fst.prodMk hZ.snd.snd
  have hBm : Measurable (fun ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
      (pathRestriction 1 (brownianContinuousPath B ω))) :=
    ((endpointMaximum_continuous _).comp (ContinuousMap.continuous_precomp _)).measurable.comp
      (brownian_continuous_path_measurable B)
  have hz : R {ω | pathMaximum (pathRestriction 1 (brownianContinuousPath B ω)) = b} = 0 := by
    simpa only [ae_iff,not_not] using brownian_clt_maximum_noatom R B b hb
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ A) hlaw
  rw [Measure.map_apply_of_aemeasurable hZm hA,Measure.map_apply hBm hA] at he
  rw [ae_iff]
  simpa only [A,endpointMaximum,Set.preimage_setOf_eq,not_not,hz] using he

theorem limit_scaled_maximum_noatom {Γ Λ : Type*} [MeasurableSpace Γ] [MeasurableSpace Λ]
    (Q : Measure Γ) (R : Measure Λ) [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (Z : Γ → ℝ × ℝ × ℝ) (hZ : AEMeasurable Z Q) (B : BrownianSystem R 1)
    (hlaw : Q.map (fun ω => ((Z ω).1,(Z ω).2.2)) =
      R.map (fun ω => endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
        (pathRestriction 1 (brownianContinuousPath B ω))))
    (b u : ℝ) (hb : 0 < b) (hu : 0 < u) :
    ∀ᵐ ω ∂Q, Real.sqrt u*(Z ω).2.2 ≠ b := by
  filter_upwards [limit_maximum_noatom Q R Z hZ B hlaw (b/Real.sqrt u)
    (div_pos hb (Real.sqrt_pos.mpr hu))] with ω hω
  intro he
  exact hω ((eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr hu))).mpr (by simpa only [mul_comm] using he))

end BarrierManuscript
#print axioms BarrierManuscript.limit_maximum_noatom
#print axioms BarrierManuscript.limit_scaled_maximum_noatom
