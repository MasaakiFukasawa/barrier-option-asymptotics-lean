import ManuscriptPsiSemigroup
import ManuscriptBrownianWeightedTwoStep

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem psi_absolute_bound (b x t : ℝ) (ht : 0 < t) :
    |psi b x t| ≤ 2*normalizer/Real.sqrt t := by
  unfold psi
  rw [abs_div,abs_of_pos (Real.sqrt_pos.mpr ht)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg t)
  have h := abs_sub (phi (x/Real.sqrt t)) (phi ((x-2*b)/Real.sqrt t))
  rw [abs_of_nonneg (phi_nonneg _),abs_of_nonneg (phi_nonneg _)] at h
  linarith [phi_le (x/Real.sqrt t),phi_le ((x-2*b)/Real.sqrt t)]

/-- Inserting a killed transition density after time u turns the earlier
Brownian moment into the appendix's barPsi, at the original observation time s. -/
theorem brownian_weighted_kernel_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω))
    (s u : ℝ≥0) (hs : 0 < s) (hsu : s < u) (hu : u < 1)
    (b k : ℝ) (hb : 0 < b) :
    (∫ ω in {ω | pathMaximum (rawPrefixPath W hc u ω) ≤ b},
      W s ω*psi (b-W u ω) (k-W u ω) (1-(u:ℝ)) ∂P)=barPsi b k s := by
  have hsr : 0 < (s:ℝ) := hs
  have hus : 0 < ((u-s:ℝ≥0):ℝ) := by exact_mod_cast tsub_pos_iff_lt.mpr hsu
  have hur : (u:ℝ) < 1 := hu
  have hnext : 0 < 1-(u:ℝ) := sub_pos.mpr hur
  let f : ℝ × ℝ → ℝ := fun p => p.1*psi (b-p.2) (k-p.2) (1-(u:ℝ))
  have hphi := phi_contDiff.continuous.measurable
  have hf : Measurable f := by unfold f psi; fun_prop
  let C := 2*normalizer/Real.sqrt (1-(u:ℝ))
  have hC : 0 ≤ C := by unfold C normalizer; positivity
  have hbound (p : ℝ × ℝ) : |f p| ≤ C*(1+|p.1|) := by
    dsimp only [f]
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left (psi_absolute_bound (b-p.2) (k-p.2) (1-(u:ℝ)) hnext) (abs_nonneg p.1)
    change |p.1| *|psi (b-p.2) (k-p.2) (1-(u:ℝ))| ≤ _
    nlinarith
  have h := brownian_two_step_weighted_integral P W hW hm hc s (u-s) hs
    (tsub_pos_iff_lt.mpr hsu) b hb f hf C hC hbound
  simp only [add_tsub_cancel_of_le hsu.le] at h
  change (∫ ω in {ω | pathMaximum (rawPrefixPath W hc u ω) ≤ b},f (W s ω,W u ω) ∂P)=_
  rw [h]
  have he x : (∫ y in Iio (b-x),f (x,x+y)*psi (b-x) y ((u-s:ℝ≥0):ℝ))=
      x*psi (b-x) (k-x) (1-(s:ℝ)) := by
    have heq y : f (x,x+y)*psi (b-x) y ((u-s:ℝ≥0):ℝ)=
      x*(psi ((b-x)-y) ((k-x)-y) (1-(u:ℝ))*psi (b-x) y ((u-s:ℝ≥0):ℝ)) := by
      dsimp only [f]
      rw [show b-(x+y)=b-x-y by ring,show k-(x+y)=k-x-y by ring]
      ring
    simp_rw [heq]
    rw [integral_const_mul,psi_semigroup (b-x) (k-x) ((u-s:ℝ≥0):ℝ) (1-(u:ℝ)) hus hnext]
    rw [NNReal.coe_sub hsu.le]
    congr 2
    ring
  simp_rw [he]
  exact psi_convolution b k (s:ℝ) ⟨hsr,(show (s:ℝ)<1 from hsu.trans hu)⟩

end BarrierManuscript
#print axioms BarrierManuscript.psi_absolute_bound
#print axioms BarrierManuscript.brownian_weighted_kernel_moment
