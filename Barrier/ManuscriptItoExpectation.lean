import ManuscriptRescaling
import Chapter2StoppedRegularity
import Chapter5DominatedLocalMean

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript

/-- Remove local martingale localization from a bounded pricing identity.
An integrable bound on the accumulated absolute drift suffices; boundedness
of the payoff alone is not used to claim a zero stochastic-integral mean. -/
theorem local_ito_expectation_of_drift_bound {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (T : HalfClosedTime) (hT : T < ⊤)
    (price drift : HalfClosedTime → Ω → ℝ) (p C : ℝ)
    (hrep : ∀ᵐ ω ∂P, ∀ t, t ≤ T → price t ω = p+N t ω+drift t ω)
    (hprice : ∀ᵐ ω ∂P, ∀ t, t ≤ T → |price t ω| ≤ C)
    (B : Ω → ℝ) (hB : Integrable B P)
    (hD : ∀ᵐ ω ∂P, ∀ t, t ≤ T → |drift t ω| ≤ B ω)
    (hDm : AEStronglyMeasurable (drift T) P) :
    Integrable (price T) P ∧ Integrable (drift T) P ∧
      (∫ ω, price T ω ∂P) = p+(∫ ω, drift T ω ∂P) := by
  have hτ : ∀ t, MeasurableSet[F t] {ω : Ω | T ≤ t} := by
    intro t
    by_cases ht : T ≤ t <;> simp [ht]
  have hiB : Integrable (fun ω => C+|p|+B ω) P := (integrable_const _).add hB
  have hb : ∀ᵐ ω ∂P, ∀ t, ‖N (min T t) ω‖ ≤ C+|p|+B ω := by
    filter_upwards [hrep,hprice,hD] with ω hr hp hd
    intro t
    have hr' := hr (min T t) (min_le_left _ _)
    have hp' := hp (min T t) (min_le_left _ _)
    have hd' := hd (min T t) (min_le_left _ _)
    have he : N (min T t) ω = price (min T t) ω-p-drift (min T t) ω := by linarith
    rw [Real.norm_eq_abs,he]
    have ha := abs_sub (price (min T t) ω-p) (drift (min T t) ω)
    have ha' := abs_sub (price (min T t) ω) p
    linarith
  have hs := hN.stopped P F hF hle (fun _ => T) hτ
  obtain ⟨_,hc⟩ := hN.stopped_regular P F hF hle (fun _ => T) hτ (fun _ => hT)
  have hmean := dominated_local_terminal_mean P F hle (fun t ω => N (min T t) ω)
    hs hc _ hiB hb
  simp only [min_top_right] at hmean
  have hiN : Integrable (N T) P := by
    apply hiB.mono' (((hN.adapted P F T hT).mono (hle T) le_rfl).aestronglyMeasurable)
    filter_upwards [hb] with ω hω
    simpa only [min_self] using hω T
  have hiD : Integrable (drift T) P := hB.mono' hDm (hD.mono fun ω hω => hω T le_rfl)
  have hi : Integrable (fun ω => p+N T ω+drift T ω) P :=
    ((integrable_const p).add hiN).add hiD
  have he : price T =ᵐ[P] (fun ω => p+N T ω+drift T ω) := hrep.mono fun ω hω => hω T le_rfl
  refine ⟨hi.congr he.symm,hiD,?_⟩
  have hiSum : Integrable (fun ω => p+N T ω) P := (integrable_const p).add hiN
  rw [integral_congr_ae he,integral_add hiSum hiD,
    integral_add (integrable_const p) hiN,hmean]
  simp

theorem local_ito_expectation_of_random_bounds {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (N : HalfClosedTime → Ω → ℝ) (hN : LocalMProcessWitness P F N)
    (T : HalfClosedTime) (hT : T < ⊤)
    (price drift : HalfClosedTime → Ω → ℝ) (p : ℝ) (C : Ω → ℝ) (hC : Integrable C P)
    (hrep : ∀ᵐ ω ∂P, ∀ t, t ≤ T → price t ω = p+N t ω+drift t ω)
    (hprice : ∀ᵐ ω ∂P, ∀ t, t ≤ T → |price t ω| ≤ C ω)
    (B : Ω → ℝ) (hB : Integrable B P)
    (hD : ∀ᵐ ω ∂P, ∀ t, t ≤ T → |drift t ω| ≤ B ω)
    (hDm : AEStronglyMeasurable (drift T) P) :
    Integrable (price T) P ∧ Integrable (drift T) P ∧
      (∫ ω, price T ω ∂P) = p+(∫ ω, drift T ω ∂P) := by
  have hτ : ∀ t, MeasurableSet[F t] {ω : Ω | T ≤ t} := by
    intro t
    by_cases ht : T ≤ t <;> simp [ht]
  have hiB : Integrable (fun ω => C ω+|p|+B ω) P := (hC.add (integrable_const _)).add hB
  have hb : ∀ᵐ ω ∂P, ∀ t, ‖N (min T t) ω‖ ≤ C ω+|p|+B ω := by
    filter_upwards [hrep,hprice,hD] with ω hr hp hd
    intro t
    have hr' := hr (min T t) (min_le_left _ _)
    have hp' := hp (min T t) (min_le_left _ _)
    have hd' := hd (min T t) (min_le_left _ _)
    have he : N (min T t) ω = price (min T t) ω-p-drift (min T t) ω := by linarith
    rw [Real.norm_eq_abs,he]
    have ha := abs_sub (price (min T t) ω-p) (drift (min T t) ω)
    have ha' := abs_sub (price (min T t) ω) p
    linarith
  have hs := hN.stopped P F hF hle (fun _ => T) hτ
  obtain ⟨_,hc⟩ := hN.stopped_regular P F hF hle (fun _ => T) hτ (fun _ => hT)
  have hmean := dominated_local_terminal_mean P F hle (fun t ω => N (min T t) ω)
    hs hc _ hiB hb
  simp only [min_top_right] at hmean
  have hiN : Integrable (N T) P := by
    apply hiB.mono' (((hN.adapted P F T hT).mono (hle T) le_rfl).aestronglyMeasurable)
    filter_upwards [hb] with ω hω
    simpa only [min_self] using hω T
  have hiD : Integrable (drift T) P := hB.mono' hDm (hD.mono fun ω hω => hω T le_rfl)
  have hi : Integrable (fun ω => p+N T ω+drift T ω) P :=
    ((integrable_const p).add hiN).add hiD
  have he : price T =ᵐ[P] (fun ω => p+N T ω+drift T ω) := hrep.mono fun ω hω => hω T le_rfl
  refine ⟨hi.congr he.symm,hiD,?_⟩
  have hiSum : Integrable (fun ω => p+N T ω) P := (integrable_const p).add hiN
  rw [integral_congr_ae he,integral_add hiSum hiD,
    integral_add (integrable_const p) hiN,hmean]
  simp

end BarrierManuscript
#print axioms BarrierManuscript.local_ito_expectation_of_drift_bound

#print axioms BarrierManuscript.local_ito_expectation_of_random_bounds
