import ManuscriptSDEBracket
import Chapter2StoppedRegularity

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false

namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem stopped_density_integral (g : ℝ → ℝ) (τ t : ℝ) (hτ : 0 ≤ τ) (ht : 0 ≤ t) :
    (∫ s in 0..t, if s ≤ τ then g s else 0) = ∫ s in 0..min τ t, g s := by
  change (∫ s in 0..t, {s | s ≤ τ}.indicator g s) = _
  rcases le_total τ t with h | h
  · rw [min_eq_left h]
    exact intervalIntegral.integral_indicator ⟨hτ,h⟩
  · rw [min_eq_right h]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact Set.indicator_of_mem (show s ∈ {s | s ≤ τ} from hs.2.trans h) g

/-- The covariance density after a finite real-valued stopping time is the
original density times its time-survival indicator. This is an exact stopped
quadratic-variation identity, unrelated to any Monte Carlo survival factor. -/
theorem stopped_covariance_density {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X C : HalfClosedTime → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (G : Ω × ℝ → ℝ)
    (hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω = ∫ s in 0..r, G (ω,s))
    (τ : Ω → ℝ) (hτpos : ∀ ω, 0 ≤ τ ω)
    (hτ : ∀ t, MeasurableSet[F t] {ω | realTimeClamp (τ ω) ≤ t}) :
    let Y := fun t ω => X (min (realTimeClamp (τ ω)) t) ω
    let D := fun t ω => C (min (realTimeClamp (τ ω)) t) ω
    LocalMProcessWitness P F Y ∧ LocalCovarianceWitness P F Y Y D ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → D (realTimeClamp r) ω =
        ∫ s in 0..r, if s ≤ τ ω then G (ω,s) else 0 := by
  dsimp only
  refine ⟨hX.stopped P F hF hle (fun ω => realTimeClamp (τ ω)) hτ,
    hC.stopped P F hF hle (fun ω => realTimeClamp (τ ω)) hτ,?_⟩
  filter_upwards [hCG] with ω hω
  intro r hr
  rw [← real_time_clamp_mono.map_min, hω (min (τ ω) r) (le_min (hτpos ω) hr),
    stopped_density_integral _ _ _ (hτpos ω) hr]

end BarrierManuscript
#print axioms BarrierManuscript.stopped_density_integral
#print axioms BarrierManuscript.stopped_covariance_density
