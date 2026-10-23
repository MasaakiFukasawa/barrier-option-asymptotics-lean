import ManuscriptForwardClockLimit
import ManuscriptStockCoefficients

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem local_forward_bounds (v : ℝ → ℝ) (v₀ : ℝ) (hv : ContinuousAt v 0)
    (h0 : v 0=v₀) (hv₀ : 0 < v₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : Ioc (0:ℝ) δ, ∀ r ∈ Icc (0:ℝ) 1,
      (1/2:ℝ)^2 ≤ v (t.val*r)/v₀ ∧ v (t.val*r)/v₀ ≤ (2:ℝ)^2 := by
  obtain ⟨d,hd,hb⟩ := Metric.continuousAt_iff.mp (hv.div_const v₀) (1/2) (by norm_num)
  refine ⟨min (d/2) 1,lt_min (by positivity) zero_lt_one,min_le_right _ _,?_⟩
  intro t r hr
  have ht : |t.val*r| < d := by
    rw [abs_of_nonneg (mul_nonneg t.property.1.le hr.1)]
    have hh := (mul_le_of_le_one_right t.property.1.le hr.2).trans (t.property.2.trans (min_le_left _ _))
    linarith
  have h := hb (show dist (t.val*r) 0 < d by simpa only [Real.dist_eq,sub_zero] using ht)
  simp only [Real.dist_eq,h0,div_self hv₀.ne'] at h
  have hh := abs_lt.mp h
  constructor <;> nlinarith

theorem normalized_model_clock_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (b k : ℝ) (M : NormalizedBarrierModel P b k)
    (hc : M.c=1/2) (hU : M.U=2) (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
    |M.a u| ≤ 4 ∧ (1/2)*Real.sqrt (1-u) ≤ remainingVol M.a u ∧ remainingVol M.a u ≤ 2 := by
  have hi : IntervalIntegrable M.a volume u 1 := M.hai.mono_set (by
    rw [uIcc_of_le hu.2.le,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hu.1.le le_rfl)
  have hb := remainingVol_bounds M.a u (1/2) 2 hu.2.le (by norm_num) (by norm_num) hi
    (fun r hr => by simpa only [hc] using (M.ha r ⟨hu.1.le.trans hr.1,hr.2⟩).1)
    (fun r hr => by simpa only [hU] using (M.ha r ⟨hu.1.le.trans hr.1,hr.2⟩).2)
  have ha := M.ha u ⟨hu.1.le,hu.2.le⟩
  rw [hc,hU] at ha
  refine ⟨?_,hb.1,?_⟩
  · rw [abs_of_nonneg (by nlinarith [ha.1])]
    nlinarith [ha.2]
  · exact hb.2.trans (by nlinarith [Real.sqrt_le_one.mpr (by linarith [hu.1] : 1-u ≤ 1)])

end BarrierManuscript
#print axioms BarrierManuscript.local_forward_bounds
#print axioms BarrierManuscript.normalized_model_clock_bounds
