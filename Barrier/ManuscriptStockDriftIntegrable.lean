import ManuscriptDriftMeasurable
import ManuscriptClock

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The integrability hypothesis in the maturity expectation theorem is
proved for the manuscript's actual normalized stock density. -/
theorem stock_barrier_drift_integrable {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (X : HalfClosedTime → Ω → ℝ) (hm : ∀ t, Measurable[F t] (X t))
    (hcont : ∀ ω, Continuous (fun t => X t ω))
    (G Y : Ω × ℝ → ℝ) (hYm : Measurable Y)
    (a : ℝ → ℝ) (ham : Measurable a) (hai : IntervalIntegrable a volume 0 1)
    (b k e h c C L : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (ha : ∀ s ∈ Icc (0:ℝ) 1, c^2 ≤ a s ∧ a s ≤ C^2)
    (hYs : ∀ s ∈ Ioo (0:ℝ) 1, Integrable (fun ω => Y (ω,s)) P)
    (hYL : ∀ s ∈ Ioo (0:ℝ) 1, (∫ ω, |Y (ω,s)| ∂P) ≤ L)
    (hG : ∀ᵐ z ∂P.prod (volume.restrict (Ioo (0:ℝ) 1)),
      G z = a z.2*(1+e*X (realTimeClamp z.2) z.1)^2*(1+h*Y z)) :
    Integrable (barrierDrift X G a b k) (P.prod (volume.restrict (Ioo 0 1))) := by
  let A := C^2/(2*c)*(normalizer*(1+2*k^2+4*C^2)+normalizer*(1+2*(2*b-k)^2+4*C^2))
  have hn := normalizer_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hXm := stock_real_joint_measurable F hle X hm hcont
  have hKm := stoppedThetaKernel_measurable F hF hle X hm hcont a ham hai b k
  apply barrier_drift_integrable_of_polynomial P X G Y a b k e h hG
  apply full_drift_joint_integrable P (fun z => X (realTimeClamp z.2) z.1)
    (stoppedThetaKernel X a b k) Y e h A L hA hXm.aestronglyMeasurable
    hKm.aestronglyMeasurable hYm.aestronglyMeasurable
    (fun s _ => by
      change AEStronglyMeasurable (X (realTimeClamp s)) P
      exact ((hm _).mono (hle _) le_rfl).aestronglyMeasurable)
    (fun s _ => (hKm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    hYs hYL
  intro s hs j hj
  have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
  have his : IntervalIntegrable a volume s 1 := hai.mono_set (by
    simp only [uIcc_of_le hs.2.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc hs.1.le le_rfl)
  have hw := remainingVol_bounds a s c C hs.2.le hc.le hC his
    (fun r hr => (ha r ⟨hs.1.le.trans hr.1,hr.2⟩).1)
    (fun r hr => (ha r ⟨hs.1.le.trans hr.1,hr.2⟩).2)
  have hroot : Real.sqrt (1-s) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1-s ≤ 1 by linarith [hs.1])
  have hW := hw.2.trans (mul_le_of_le_one_right hC hroot)
  have hv : |a s| ≤ C^2 := by
    rw [abs_of_nonneg ((sq_nonneg c).trans (ha s hs').1)]
    exact (ha s hs').2
  apply ae_of_all
  intro ω
  unfold stoppedThetaKernel
  split_ifs
  · rw [varianceClock_remaining a hai s hs']
    exact thetaKernel_time_domination b k (a s) (remainingVol a s) (X (realTimeClamp s) ω)
      C (C^2) c s hs.2 hc hw.1 hW hv j hj
  · simp only [abs_zero,mul_zero]
    exact div_nonneg hA (Real.sqrt_nonneg _)

/-- Uniform Gaussian bounds for every stock power needed in the expansion. -/
theorem stoppedThetaKernel_weighted_bound {Ω : Type*}
    (X : HalfClosedTime → Ω → ℝ) (a : ℝ → ℝ)
    (hai : IntervalIntegrable a volume 0 1)
    (b k c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (ha : ∀ s ∈ Icc (0:ℝ) 1, c^2 ≤ a s ∧ a s ≤ C^2)
    (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) (j : ℕ) (hj : j ≤ 2) (ω : Ω) :
    |X (realTimeClamp s) ω|^j*|stoppedThetaKernel X a b k (ω,s)| ≤
      (C^2/(2*c)*(normalizer*(1+2*k^2+4*C^2)+normalizer*(1+2*(2*b-k)^2+4*C^2)))/Real.sqrt (1-s) := by
  let A := C^2/(2*c)*(normalizer*(1+2*k^2+4*C^2)+normalizer*(1+2*(2*b-k)^2+4*C^2))
  have hn := normalizer_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
  have his : IntervalIntegrable a volume s 1 := hai.mono_set (by
    simp only [uIcc_of_le hs.2.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Icc_subset_Icc hs.1.le le_rfl)
  have hw := remainingVol_bounds a s c C hs.2.le hc.le hC his
    (fun r hr => (ha r ⟨hs.1.le.trans hr.1,hr.2⟩).1)
    (fun r hr => (ha r ⟨hs.1.le.trans hr.1,hr.2⟩).2)
  have hroot : Real.sqrt (1-s) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1-s ≤ 1 by linarith [hs.1])
  have hW := hw.2.trans (mul_le_of_le_one_right hC hroot)
  have hv : |a s| ≤ C^2 := by
    rw [abs_of_nonneg ((sq_nonneg c).trans (ha s hs').1)]
    exact (ha s hs').2
  unfold stoppedThetaKernel
  split_ifs
  · rw [varianceClock_remaining a hai s hs']
    exact thetaKernel_time_domination b k (a s) (remainingVol a s) (X (realTimeClamp s) ω)
      C (C^2) c s hs.2 hc hw.1 hW hv j hj
  · simp only [abs_zero,mul_zero]
    exact div_nonneg hA (Real.sqrt_nonneg _)


end BarrierManuscript
#print axioms BarrierManuscript.stock_barrier_drift_integrable

#print axioms BarrierManuscript.stoppedThetaKernel_weighted_bound
