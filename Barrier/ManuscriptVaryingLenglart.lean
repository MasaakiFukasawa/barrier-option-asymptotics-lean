import ManuscriptStockCLT
import Chapter2LenglartConvergence

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Lenglart's argument for the varying filtrations created by maturity
rescaling. Vanishing brackets imply vanishing pathwise maxima in probability. -/
theorem varying_local_martingale_zero {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → HalfClosedTime → MeasurableSpace Ω) (hF : ∀ n, Monotone (F n))
    (hle : ∀ n t, F n t ≤ m)
    (hnull : ∀ n t A, MeasurableSet[m] A → P A=0 → MeasurableSet[F n t] A)
    (X C : ℕ → HalfClosedTime → Ω → ℝ)
    (hX : ∀ n, LocalMProcessWitness P (F n) (X n))
    (hC : ∀ n, LocalCovarianceWitness P (F n) (X n) (X n) (C n))
    (hprob : ∀ δ > 0, Tendsto (fun n => P {ω | δ ≤ C n (realTimeClamp 1) ω}) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ⨆ t, |X n (min (realTimeClamp 1) t) ω|}) atTop (𝓝 0) := by
  apply probability_limit_of_arbitrary_remainder P _
    (fun δ n => {ω | δ ≤ C n (realTimeClamp 1) ω}) hprob
  intro η hη
  refine ⟨η*ε^2,mul_pos hη (sq_pos_of_pos hε),?_⟩
  intro n
  have hstop : ∀ t, MeasurableSet[F n t] {ω : Ω | realTimeClamp (T := (⊤:EReal)) 1 ≤ t} := by
    intro t
    by_cases h : realTimeClamp (T := (⊤:EReal)) 1 ≤ t <;> simp [h]
  have h := (local_lenglart P (F n) (hF n) (hle n) (hnull n) (X n) (C n) (hX n) (hC n)
    (fun _ => realTimeClamp 1) hstop (fun _ => halfTimeClamp_finite 1)
    ε (η*ε^2) hε (mul_pos hη (sq_pos_of_pos hε))).1
  rw [mul_div_cancel_right₀ η (ne_of_gt (sq_pos_of_pos hε))] at h
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.varying_local_martingale_zero
