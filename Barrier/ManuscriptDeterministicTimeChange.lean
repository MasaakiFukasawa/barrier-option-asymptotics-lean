import ManuscriptDeterministicItoConstruction
import ManuscriptStockCLT
import Chapter7DDSWritten
import Chapter6ExponentialLocal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter6 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The actual deterministic Ito integral has the integrated-variance
clock simultaneously at every finite time. -/
theorem deterministic_ito_bracket_common {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : ∀ r,0 ≤ r → IntervalIntegrable (fun s => g s^2) volume 0 r)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N) :
    ∃ A : HalfClosedTime → Ω → ℝ,LocalCovarianceWitness P B.F N N A ∧
      ∀ᵐ ω ∂P,∀ r : ℝ,0 ≤ r → A (realTimeClamp r) ω=∫ s in (0:ℝ)..r,g s^2 := by
  obtain ⟨c,hc,hcm,hcT,hct,hcut,hcc⟩ := positive_real_time_exhaustion (by simp : (0:EReal)<⊤)
  have hgp n : @Measurable _ _ (progressiveSpace (fun t : Icc (0:ℝ) (c n) => B.F (realTimeClamp t.val))) inferInstance
      (fun z : Ω × Icc (0:ℝ) (c n) => g z.2.val) := by
    exact hg.comp (continuous_adapted_real_progressive B.F B.mono (fun z : Ω × ℝ => z.2)
      (c n) (hc n).le (fun _ _ => measurable_const) (fun _ => continuous_id.continuousOn))
  obtain ⟨A,hA,he⟩ := clock_ito_integral_bracket P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null (B.W 0) (B.C 0 0) N (B.martingale 0) (B.cov 0 0) hN
    c hc hcm hcT hct hcut hcc
    (fun n ω r hr => B.diagonal_clock 0 ω r hr.1)
    (fun z => g z.2) hgp (fun n => ae_of_all _ fun _ => hi (c n) (hc n).le) hNI
  have hp (n : ℕ) := covariance_density_common_time P B.F N N A hN hN hA
    (fun z : Ω × ℝ => g z.2^2) (fun r hr => ae_of_all _ fun _ => hi r hr)
    (fun r hr => he r hr (EReal.coe_lt_top r)) n (Nat.cast_nonneg n)
  refine ⟨A,hA,?_⟩
  filter_upwards [ae_all_iff.mpr hp] with ω hω r hr
  obtain ⟨n,hn⟩ := exists_nat_ge r
  exact hω n r ⟨hr,hn⟩

/-- DDS identifies the entire deterministic-volatility noise, allowing
zero volatility and flat portions of the clock. Divergence is only a
half-line condition; a finite-horizon coefficient can be extended afterwards. -/
theorem deterministic_ito_time_change {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : ∀ r,0 ≤ r → IntervalIntegrable (fun s => g s^2) volume 0 r)
    (hdiv : ∀ q : ℝ,∃ r : ℝ,0 ≤ r ∧ q < ∫ s in (0:ℝ)..r,g s^2)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N) :
    ∃ W : BrownianSystem P 1,∀ᵐ ω ∂P,∀ r : ℝ,0 ≤ r →
      N (realTimeClamp r) ω=W.W 0 (realTimeClamp (∫ s in (0:ℝ)..r,g s^2)) ω := by
  obtain ⟨A,hA,he⟩ := deterministic_ito_bracket_common P B g hg hi N hN hNI
  have hd : ∀ᵐ ω ∂P,∀ q : ℝ,∃ t : HalfClosedTime,t < ⊤ ∧ q < A t ω := by
    filter_upwards [he] with ω hω q
    obtain ⟨r,hr,hh⟩ := hdiv q
    exact ⟨realTimeClamp r,halfTimeClamp_finite r,by rw [hω r hr]; exact hh⟩
  obtain ⟨W,_,hw,_⟩ := dds_written P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null N A hN hA hd
  refine ⟨W,?_⟩
  filter_upwards [he,hw] with ω hω hh r hr
  rw [hh _ (halfTimeClamp_finite r),hω r hr]

/-- In particular the stochastic exponential has the full geometric
Brownian time-change representation, including its drift correction. -/
theorem deterministic_exponential_time_change {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : ∀ r,0 ≤ r → IntervalIntegrable (fun s => g s^2) volume 0 r)
    (hdiv : ∀ q : ℝ,∃ r : ℝ,0 ≤ r ∧ q < ∫ s in (0:ℝ)..r,g s^2) :
    ∃ (N A : HalfClosedTime → Ω → ℝ) (W : BrownianSystem P 1),
      LocalMProcessWitness P B.F N ∧
      ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N ∧
      LocalMProcessWitness P B.F (fun t ω => Real.exp (N t ω-A t ω/2)-1) ∧
      ItoCovarianceFormula P B.F N (fun z => Real.exp (N (realTimeClamp z.2) z.1-A (realTimeClamp z.2) z.1/2))
        (fun t ω => Real.exp (N t ω-A t ω/2)-1) ∧
      ∀ᵐ ω ∂P,∀ r : ℝ,0 ≤ r →
        Real.exp (N (realTimeClamp r) ω-A (realTimeClamp r) ω/2)=
          Real.exp (W.W 0 (realTimeClamp (∫ s in (0:ℝ)..r,g s^2)) ω-(∫ s in (0:ℝ)..r,g s^2)/2) := by
  obtain ⟨N,hN,hNI⟩ := deterministic_ito_exists P B g hg hi
  obtain ⟨A,hA,he⟩ := deterministic_ito_bracket_common P B g hg hi N hN hNI
  obtain ⟨W,hw⟩ := deterministic_ito_time_change P B g hg hi hdiv N hN hNI
  obtain ⟨hS,hSI⟩ := stochastic_exponential_constructed P (by simp : (0:EReal)<⊤)
    B.F B.mono B.le B.null N A hN hA
  refine ⟨N,A,W,hN,hNI,hS,hSI,?_⟩
  filter_upwards [he,hw] with ω hω hh r hr
  rw [hω r hr,hh r hr]

end BarrierManuscript
#print axioms BarrierManuscript.deterministic_ito_bracket_common
#print axioms BarrierManuscript.deterministic_ito_time_change
#print axioms BarrierManuscript.deterministic_exponential_time_change
