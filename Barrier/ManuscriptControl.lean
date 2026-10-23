import FullAuditContinuousOptional
import FullAuditClosedHitting
import Mathlib.Topology.Order.IntermediateValue

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written

set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

attribute [local instance] Classical.propDecidable

noncomputable def barrierTime {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (S : ClosedTime T → Ω → ℝ) (B : ℝ) (ω : Ω) : ClosedTime T :=
  sInf {t | S t ω = B}

theorem barrierTime_stopping {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F)
    (S : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (S t))
    (hc : ∀ ω, Continuous (fun t => S t ω)) (B : ℝ) :
    ∀ t, MeasurableSet[F t] {ω | barrierTime S B ω ≤ t} := by
  simpa only [barrierTime, mem_singleton_iff] using
    continuous_hitting_stopping_written F hF S hm hc {B} isClosed_singleton

theorem barrierTime_hit_iff {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (S : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => S t ω))
    (B : ℝ) (ω : Ω) : S (barrierTime S B ω) ω = B ↔ ∃ t, S t ω = B := by
  constructor
  · exact fun h => ⟨_, h⟩
  · intro h
    exact IsClosed.sInf_mem h (isClosed_eq (hc ω) continuous_const)

/-- No optional-sampling identity is assumed: it follows from the actual
continuous martingale and stopping-time hypotheses. -/
theorem stopped_mean {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (S : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (S t))
    (hi : ∀ t, Integrable (S t) P) (hc : ∀ ω, Continuous (fun t => S t ω))
    (hM : ∀ s t, s ≤ t → P[S t | F s] =ᵐ[P] S s)
    (S₀ : ℝ) (h₀ : ∀ ω, S ⊥ ω = S₀)
    (τ : Ω → ClosedTime T) (hτ : ∀ t, MeasurableSet[F t] {ω | τ ω ≤ t}) :
    Integrable (fun ω => S (τ ω) ω) P ∧ (∫ ω, S (τ ω) ω ∂P) = S₀ := by
  have hs := continuous_closed_optional_written P (Fact.out : 0 ≤ T) F hF hle
    τ hτ S hm (fun ω t => (hc ω).continuousAt.continuousWithinAt)
    ((hm ⊤).mono (hle ⊤) le_rfl) (hi ⊤) (fun t => (hM t ⊤ le_top).symm)
  refine ⟨integrable_condExp.congr hs.symm, ?_⟩
  rw [integral_congr_ae hs,
    integral_condExp (show writtenStoppedSpace m F τ hτ ≤ m from fun A hA => hA.1)]
  have h := integral_congr_ae (hM ⊥ ⊤ bot_le)
  rw [integral_condExp (hle ⊥)] at h
  simpa [h₀] using h

/-- The manuscript's K ≥ B identity, for an actual continuous martingale.
The hitting time and event are constructed, including hits exactly at maturity. -/
theorem uop_above_barrier {Ω : Type*} {m : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {T : EReal} [Fact (0 ≤ T)]
    (F : ClosedTime T → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (S : ClosedTime T → Ω → ℝ) (hm : ∀ t, Measurable[F t] (S t))
    (hi : ∀ t, Integrable (S t) P) (hc : ∀ ω, Continuous (fun t => S t ω))
    (hM : ∀ s t, s ≤ t → P[S t | F s] =ᵐ[P] S s)
    (S₀ B K : ℝ) (h₀ : ∀ ω, S ⊥ ω = S₀) (hB : S₀ < B) (hK : B ≤ K) :
    (∫ ω, if (∃ t, S t ω = B) then 0 else max (K-S ⊤ ω) 0 ∂P) =
      K-S₀+(B-K)*P.real {ω | ∃ t, S t ω = B} := by
  classical
  let τ := barrierTime S B
  let A : Set Ω := {ω | ∃ t, S t ω = B}
  have hτ := barrierTime_stopping F hF S hm hc B
  have hmτ := (stopped_value_measurable_right_continuous m (Fact.out : 0 ≤ T)
    F hF hle τ hτ S hm (fun ω t => (hc ω).continuousAt.continuousWithinAt)).mono
    (show writtenStoppedSpace m F τ hτ ≤ m from fun A hA => hA.1) le_rfl
  have hA : MeasurableSet A := by
    have he : A = (fun ω => S (τ ω) ω) ⁻¹' {B} := by
      ext ω; exact (barrierTime_hit_iff S hc B ω).symm
    rw [he]; exact hmτ (measurableSet_singleton B)
  obtain ⟨hI, hmean⟩ := stopped_mean P F hF hle S hm hi hc hM S₀ h₀ τ hτ
  have hpath (ω : Ω) :
      (if (∃ t, S t ω = B) then 0 else max (K-S ⊤ ω) 0) =
        K-S (τ ω) ω+(B-K)*A.indicator (fun _ => (1:ℝ)) ω := by
    by_cases hh : ∃ t, S t ω = B
    · have hv := (barrierTime_hit_iff S hc B ω).mpr hh
      have ha : ω ∈ A := hh
      rw [ite_eq_left hh, Set.indicator_of_mem ha]
      change 0 = K-S (barrierTime S B ω) ω+(B-K)*1
      rw [hv]; ring
    · have ht : τ ω = ⊤ := by
        have he : {t | S t ω = B} = ∅ := by
          ext t; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h => hh ⟨t,h⟩
        simp [τ, barrierTime, he]
      have hbelow : S ⊤ ω < B := by
        by_contra hn
        have hmem := intermediate_value_univ (⊥ : ClosedTime T) ⊤ (hc ω)
          (show B ∈ Icc (S ⊥ ω) (S ⊤ ω) from ⟨by rw [h₀]; exact hB.le, le_of_not_gt hn⟩)
        exact hh hmem
      have ha : ω ∉ A := hh
      rw [ite_eq_right hh, Set.indicator_of_notMem ha, ht,
        max_eq_left (sub_nonneg.mpr (hbelow.le.trans hK))]
      ring
  simp_rw [hpath]
  have hsub : Integrable (fun ω => K-S (τ ω) ω) P := (integrable_const K).sub hI
  have hind : Integrable (fun ω => (B-K)*A.indicator (fun _ => (1:ℝ)) ω) P :=
    ((integrable_const (1:ℝ)).indicator hA).const_mul (B-K)
  rw [integral_add hsub hind,
    integral_sub (integrable_const K) hI, hmean, integral_const_mul,
    integral_indicator_const (1:ℝ) hA]
  simp [A]

end BarrierManuscript

#print axioms BarrierManuscript.barrierTime_stopping
#print axioms BarrierManuscript.barrierTime_hit_iff
#print axioms BarrierManuscript.stopped_mean
#print axioms BarrierManuscript.uop_above_barrier
