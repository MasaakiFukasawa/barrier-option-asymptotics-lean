import ManuscriptDeterministicTimeChange
import Chapter7BrownianTail

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete
open Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter6 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Finite-horizon time change for the original deterministic Ito integral.
No divergence, strict positivity, or inverse differentiability is needed.
An independent Brownian tail is added only after the observation horizon. -/
theorem finite_deterministic_ito_time_change {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hi : ∀ r,0 ≤ r → IntervalIntegrable (fun s => g s^2) volume 0 r)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => g z.2) N)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ W : BrownianSystem (P.prod P) 1,∀ᵐ z ∂P.prod P,∀ r ∈ Icc (0:ℝ) T,
      N (realTimeClamp r) z.1=W.W 0 (realTimeClamp (∫ s in (0:ℝ)..r,g s^2)) z := by
  obtain ⟨A,hA,he⟩ := deterministic_ito_bracket_common P B g hg hi N hN hNI
  let G := independentProductFiltration P P B.F B.F
  let Z := fun t (z : Ω × Ω) => N (min (realTimeClamp T) t) z.1+
    (B.W 0 t z.2-B.W 0 (min (realTimeClamp T) t) z.2)
  let C := fun t (z : Ω × Ω) => A (min (realTimeClamp T) t) z.1+
    (B.C 0 0 t z.2-B.C 0 0 (min (realTimeClamp T) t) z.2)
  have hh := independent_brownian_tail P P B.F B.mono B.le N A hN hA B T hT
  have hG : Monotone G := hh.1
  have hGl : ∀ t,G t ≤ productSigma m m := hh.2.1
  have hGn : ∀ t E,MeasurableSet[productSigma m m] E → (P.prod P) E=0 → MeasurableSet[G t] E := hh.2.2.1
  have hZ : LocalMProcessWitness (P.prod P) G Z := hh.2.2.2.1
  have hC : LocalCovarianceWitness (P.prod P) G Z Z C := hh.2.2.2.2.1
  have hd : ∀ᵐ z ∂P.prod P,∀ q : ℝ,∃ t,t < ⊤ ∧ q < C t z := ae_of_all _ hh.2.2.2.2.2.2.2
  obtain ⟨W,_,hw,_⟩ := dds_written (P.prod P) (by simp : (0:EReal)<⊤) G hG hGl hGn Z C hZ hC hd
  have he' : ∀ᵐ z ∂P.prod P,∀ r : ℝ,0 ≤ r → A (realTimeClamp r) z.1=∫ s in (0:ℝ)..r,g s^2 :=
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae he
  refine ⟨W,?_⟩
  filter_upwards [hw,he'] with z hz hez r hr
  have hrec := hz (realTimeClamp r) (halfTimeClamp_finite r)
  have hfirst : Z (realTimeClamp r) z=N (realTimeClamp r) z.1 := hh.2.2.2.2.2.2.1 r hr z
  have hclock : C (realTimeClamp r) z=∫ s in (0:ℝ)..r,g s^2 := by
    change A (min (realTimeClamp T) (realTimeClamp r)) z.1+
      (B.C 0 0 (realTimeClamp r) z.2-B.C 0 0 (min (realTimeClamp T) (realTimeClamp r)) z.2)=_
    rw [min_eq_right (real_time_clamp_mono hr.2),sub_self,add_zero,hez r hr.1]
  rwa [hfirst,hclock] at hrec

end BarrierManuscript
#print axioms BarrierManuscript.finite_deterministic_ito_time_change
