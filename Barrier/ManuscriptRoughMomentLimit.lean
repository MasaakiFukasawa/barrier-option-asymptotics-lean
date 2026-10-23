import ManuscriptRoughTruncatedMoment
import ManuscriptRoughWeightedApproximation
import ManuscriptRoughCutSequence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Removal of the Volterra cutoff in a bounded weighted moment. All
singular-kernel integrability and convergence are derived from H>0. -/
theorem rough_barPsi_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν b k κ : ℝ) (hH : 0 < H) (hb : 0 < b) (t : ℝ≥0) (ht : 0 < t) (ht1 : t < 1)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν t z.2) N)
    (Z : Ω → ℝ) (hZ : Measurable Z) (C : ℝ) (hC : 0 ≤ C) (hZb : ∀ ω, |Z ω| ≤ C)
    (hMoment : ∀ s : ℝ, 0 < s → s < (t:ℝ) →
      (∫ ω,B.W 0 (realTimeClamp s) ω*Z ω ∂P)=κ*barPsi b k s) :
    (∫ ω,N (realTimeClamp t) ω*Z ω ∂P)=
      κ*(∫ s in (0:ℝ)..(t:ℝ),roughKernel H ν t s*barPsiTimeDerivative b k s) := by
  let a := fun n => t*roughUnitCut (n+1)
  have hau n : 0 < roughUnitCut (n+1) := by
    change 0 < 1-1/(((n+1:ℕ):ℝ)+1)
    have hden : 1 < ((n+1:ℕ):ℝ)+1 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hh : 1/(((n+1:ℕ):ℝ)+1) < 1 := (div_lt_one (by positivity)).mpr hden
    linarith
  have ha n : 0 < a n := mul_pos ht (hau n)
  have hat n : a n < t := by simpa only [a,mul_one] using mul_lt_mul_of_pos_left (rough_unit_cut_lt (n+1)) ht
  have halim : Tendsto (fun n => (a n:ℝ)) atTop (𝓝 (t:ℝ)) := by
    simpa only [a,NNReal.coe_mul,mul_one,Function.comp_def] using (rough_unit_cut_limit.comp (tendsto_add_atTop_nat 1)).const_mul (t:ℝ)
  have hw := rough_weighted_path_approximation P B H ν hH t a hat halim N hN hNI Z hZ C hC hZb
  have he n := rough_truncated_barPsi_moment P B H ν b k κ hb t (a n) (ha n) (hat n) ht1 Z hZ C hC hZb hMoment
  have hkernel : IntegrableOn (roughKernel H ν t) (Icc (0:ℝ) (t:ℝ)) :=
    ((rough_kernel_memLp H ν t hH t.coe_nonneg).restrict (Icc (0:ℝ) (t:ℝ))).integrable (by norm_num)
  have hf : IntegrableOn (fun s => roughKernel H ν t s*barPsiTimeDerivative b k s) (Icc (0:ℝ) (t:ℝ)) :=
    hkernel.mul_bdd (barPsiTimeDerivative_measurable b k).aestronglyMeasurable
      (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using barPsiTimeDerivative_bound b k s)
  have hc : ContinuousOn (fun x => ∫ s in (0:ℝ)..x,roughKernel H ν t s*barPsiTimeDerivative b k s)
      (Icc (0:ℝ) (t:ℝ)) := by
    simpa only [uIcc_of_le t.coe_nonneg] using intervalIntegral.continuousOn_primitive_interval
      (a := (0:ℝ)) (b := (t:ℝ)) (by simpa only [uIcc_of_le t.coe_nonneg] using hf)
  have haWithin : Tendsto (fun n => (a n:ℝ)) atTop (𝓝[Icc (0:ℝ) (t:ℝ)] (t:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨halim,Filter.Eventually.of_forall fun n => ⟨(a n).coe_nonneg,(hat n).le⟩⟩
  have hl := (hc t ⟨t.coe_nonneg,le_rfl⟩).tendsto.comp haWithin
  simp_rw [he] at hw
  exact tendsto_nhds_unique hw (hl.const_mul κ)

end BarrierManuscript
#print axioms BarrierManuscript.rough_barPsi_moment
