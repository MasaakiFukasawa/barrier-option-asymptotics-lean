import ManuscriptStockModelConstruction
import Chapter4GeometricGlobal
import Chapter2StochasticFubiniPrinted

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def geometricStock {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (w : ℝ) (t : HalfClosedTime) (ω : Ω) : ℝ :=
  geometricFlow 1 0 w ![B.C 0 0 t ω,B.W 0 t ω]

theorem geometricStock_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (w r : ℝ) (hr : 0 ≤ r) (ω : Ω) :
    geometricStock B w (realTimeClamp r) ω = Real.exp (w*B.W 0 (realTimeClamp r) ω-w^2*r/2) := by
  simp only [geometricStock,geometricFlow,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    one_mul,zero_sub,B.diagonal_clock 0 ω r hr]
  congr 1
  ring

theorem geometricStock_sde {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (w : ℝ) :
    (∀ t, t < ⊤ → Measurable[B.F t] (geometricStock B w t)) ∧
    (∀ ω t, t < ⊤ → ContinuousAt (fun s => geometricStock B w s ω) t) ∧
    LocalMProcessWitness P B.F (fun t ω => geometricStock B w t ω-1) ∧
    ItoCovarianceFormula P B.F (B.W 0) (fun z => w*geometricStock B w (realTimeClamp z.2) z.1)
      (fun t ω => geometricStock B w t ω-1) := by
  have hclock : ∀ ω (r : ℝ), 0 ≤ r → (r:EReal)<⊤ → B.C 0 0 (realTimeClamp r) ω=r :=
    fun ω r hr _ => B.diagonal_clock 0 ω r hr
  have hCc := (clock_regular_from_identity (B.C 0 0) hclock).2
  have hCv := covariance_adapted_variation P B.F B.mono B.le (B.martingale 0) (B.martingale 0) (B.cov 0 0)
  have hsa t (ht : t<⊤) : Measurable[B.F t] (geometricStock B w t) := by
    letI : MeasurableSpace Ω := B.F t
    unfold geometricStock
    apply (geometricFlow_smooth 1 0 w).continuous.measurable.comp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · exact hCv.adapted t ht
    · exact (B.martingale 0).adapted P B.F t ht
  have hsc ω t (ht : t<⊤) : ContinuousAt (fun s => geometricStock B w s ω) t := by
    apply (geometricFlow_smooth 1 0 w).continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro j
    fin_cases j
    · exact hCc ω t ht
    · exact (B.martingale 0).path P B.F ω t ht
  obtain ⟨N,hN,hNI,he⟩ := geometric_sde_global P (show (0:EReal)<⊤ by simp) B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) hclock 1 0 w
  have hn : ∀ᵐ ω ∂P, ∀ t, t<⊤ → N t ω=geometricStock B w t ω-1 := by
    filter_upwards [he] with ω hω t ht
    obtain ⟨r,hr,hrT,rfl⟩ := finite_closed_time_real t ht
    have hh := hω r hr hrT
    simp only [zero_mul,add_zero] at hh
    unfold geometricStock
    rw [hclock ω r hr hrT]
    linarith
  have hM := LocalMProcessWitness.congr_ae_open P B.F B.mono hN
    (fun t ht => (hsa t ht).sub_const 1) (fun ω t ht => (hsc ω t ht).sub_const 1) hn
  refine ⟨hsa,hsc,hM,?_⟩
  exact ItoCovarianceFormula.congr_integral P B.F B.mono B.le (B.W 0) N _ _ hN hM hn hNI

end BarrierManuscript
#print axioms BarrierManuscript.geometricStock_real
#print axioms BarrierManuscript.geometricStock_sde
