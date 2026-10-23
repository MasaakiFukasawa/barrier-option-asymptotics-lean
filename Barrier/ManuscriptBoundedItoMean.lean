import ManuscriptItoFreezing
import ManuscriptSecondMomentUI
import Chapter2StoppedM2Equivalence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Bounded diffusion coefficients turn the stopped local martingale into
a true martingale, hence the actual Ito integral has zero mean. -/
theorem bounded_ito_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G N : HalfClosedTime → Ω → ℝ)
    (hGa : ∀ t,t < ⊤ → Measurable[B.F t] (G t))
    (hGc : ∀ ω t,t < ⊤ → ContinuousAt (fun s => G s ω) t)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => G (realTimeClamp z.2) z.1) N)
    (K t : ℝ) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hb : ∀ ω s,s ∈ Icc (0:ℝ) t → |G (realTimeClamp s) ω| ≤ K) :
    (∫ ω,N (realTimeClamp t) ω ∂P)=0 := by
  obtain ⟨_,C,_,hC,_,he⟩ := brownian_ito_cross_and_self_density P B.F B.mono B.le B.null
    (B.W 0) N (B.C 0 0) G (B.martingale 0) hN (B.cov 0 0) (B.diagonal_clock 0) hGa hGc hNI
  have hbound : ∀ᵐ ω ∂P,0 ≤ C (realTimeClamp t) ω ∧ C (realTimeClamp t) ω ≤ K^2*t := by
    filter_upwards [he] with ω hω
    rw [hω t ht]
    constructor
    · exact intervalIntegral.integral_nonneg_of_forall ht (fun _ => sq_nonneg _)
    · have h := intervalIntegral.integral_mono_on (μ := volume) ht
        (((continuous_real_path G hGc ω).pow 2).intervalIntegrable 0 t) intervalIntegrable_const
        (fun s hs => by
          have hh := (sq_le_sq₀ (abs_nonneg (G (realTimeClamp s) ω)) hK).mpr (hb ω s hs)
          simpa only [sq_abs,Pi.pow_apply] using hh)
      simpa only [sq_abs,Pi.pow_apply,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using h
  have hiC : Integrable (C (realTimeClamp t)) P := by
    apply (integrable_const (K^2*t)).mono'
      (((hC.adapted P B.F hN hN _ (halfTimeClamp_finite t)).mono (B.le _) le_rfl).aestronglyMeasurable)
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs,abs_of_nonneg hω.1] using hω.2
  have hstop : ∀ s,MeasurableSet[B.F s] {ω : Ω | realTimeClamp (T := (⊤:EReal)) t ≤ s} := by
    intro s
    by_cases h : realTimeClamp (T := (⊤:EReal)) t ≤ s <;> simp [h]
  have heq := stopped_local_M2_equivalences P B.F B.mono B.le B.null N C hN hC
    (fun _ => realTimeClamp t) hstop (fun _ => halfTimeClamp_finite t)
  have hM := heq.2.mp (heq.1.mp hiC)
  have hm := integral_congr_ae ((hM.martingale ⊥ ⊤ bot_le).trans hM.initial)
  rw [integral_condExp (B.le ⊥)] at hm
  simpa only [min_top_right,Pi.zero_apply,integral_zero] using hm

end BarrierManuscript
#print axioms BarrierManuscript.bounded_ito_mean_zero
