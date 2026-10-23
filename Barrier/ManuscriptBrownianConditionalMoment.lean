import ManuscriptBridgeTestIntegrability

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace BarrierManuscript

theorem brownian_conditional_moment_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ s, Measurable (W s))
    (hc : ∀ ω, Continuous (fun s => W s ω)) (t : ℝ≥0) (ht : 0 < t) (ht1 : t < 1)
    (b : ℝ) (hb : 0 < b) (g : ℝ → ℝ) (hg : Measurable g)
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ x, |g x| ≤ C) :
    (∫ ω in {ω | pathMaximum (rawPrefixPath W hc 1 ω) ≤ b}, W t ω*g (W 1 ω) ∂P) =
      ∫ x in Iio b, g x*barPsi b x (t:ℝ) := by
  have htr : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  have htr1 : (t:ℝ) < 1 := by exact_mod_cast ht1
  have hd : (0:ℝ≥0) < 1-t := tsub_pos_iff_lt.mpr ht1
  have htd : t+(1-t)=1 := add_tsub_cancel_of_le ht1.le
  let f := fun p : ℝ × ℝ => p.1*g p.2
  have hf : Measurable f := measurable_fst.mul (hg.comp measurable_snd)
  have hbound p : |f p| ≤ C*(1+|p.1|) := by
    dsimp only [f]
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left (hgb p.2) (abs_nonneg p.1)
    nlinarith only [h,hC]
  have hraw := brownian_two_step_weighted_integral P W hW hm hc t (1-t) ht hd b hb f hf C hC hbound
  simp only [htd,NNReal.coe_sub ht1.le,NNReal.coe_one] at hraw
  simp_rw [shifted_killed_kernel] at hraw
  have hi := bridge_test_integrable b (t:ℝ) (1-(t:ℝ)) hb htr (sub_pos.mpr htr1) f hf C hC hbound
  have hs := integral_integral_swap (f := fun y x => f (y,x)*psi (b-y) (x-y) (1-(t:ℝ))*psi b y (t:ℝ)) hi
  have hrewrite : (∫ x in Iio b, (∫ y in Iio b, f (x,y)*psi (b-x) (y-x) (1-(t:ℝ)))*psi b x (t:ℝ)) =
      ∫ x in Iio b, g x*barPsi b x (t:ℝ) := by
    simp_rw [← integral_mul_const]
    rw [hs]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      have he y : f (y,x)*psi (b-y) (x-y) (1-(t:ℝ))*psi b y (t:ℝ) =
          g x*(y*psi (b-y) (x-y) (1-(t:ℝ))*psi b y (t:ℝ)) := by dsimp only [f]; ring
      simp_rw [he]
      rw [integral_const_mul,psi_convolution b x (t:ℝ) ⟨htr,htr1⟩]
  exact hraw.trans hrewrite

end BarrierManuscript
#print axioms BarrierManuscript.brownian_conditional_moment_tests
