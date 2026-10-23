import ManuscriptDriftFubini
import ManuscriptClock

open MeasureTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Bounded first moments of the drift imply its joint integrability and the
linear bound on the expectation of its accumulated integral. -/
theorem bounded_drift_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : Ω × ℝ → ℝ) (C t : ℝ)
    (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hm : AEStronglyMeasurable a (P.prod (volume.restrict (Ioc 0 t))))
    (hi : ∀ s ∈ Ioc (0:ℝ) t, Integrable (fun ω => a (ω,s)) P)
    (hb : ∀ s ∈ Ioc (0:ℝ) t, (∫ ω, |a (ω,s)| ∂P) ≤ C) :
    Integrable (fun ω => ∫ s in (0:ℝ)..t, a (ω,s)) P ∧
      |∫ ω, (∫ s in (0:ℝ)..t, a (ω,s)) ∂P| ≤ C*t := by
  have hmi : AEStronglyMeasurable (fun s => ∫ ω, |a (ω,s)| ∂P)
      (volume.restrict (Ioc 0 t)) := by
    simpa only [Real.norm_eq_abs,Function.comp_apply,Prod.swap_prod_mk] using
      hm.norm.prod_swap.integral_prod_right'
  have htime : Integrable (fun s => ∫ ω, |a (ω,s)| ∂P) (volume.restrict (Ioc 0 t)) := by
    apply (integrable_const C).mono' hmi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
    exact hb s hs
  have hj : Integrable a (P.prod (volume.restrict (Ioc 0 t))) := by
    apply (integrable_prod_iff' hm).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using hi s hs
    · simpa only [Real.norm_eq_abs] using htime
  constructor
  · simpa only [intervalIntegral.integral_of_le ht] using hj.integral_prod_left
  · simp_rw [intervalIntegral.integral_of_le ht]
    rw [integral_integral_swap (f := fun ω s => a (ω,s)) hj]
    calc
      _ ≤ ∫ s in Ioc 0 t, |∫ ω, a (ω,s) ∂P| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun s => ∫ ω, a (ω,s) ∂P) (μ := volume.restrict (Ioc 0 t))
      _ ≤ ∫ s in Ioc 0 t, C := by
        apply integral_mono_ae hj.integral_prod_right.norm (integrable_const C)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hn : |∫ ω, a (ω,s) ∂P| ≤ ∫ ω, |a (ω,s)| ∂P := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => a (ω,s)) (μ := P)
        exact hn.trans (hb s hs)
      _ = C*t := by simp [Real.volume_Ioc,ht,mul_comm]

/-- The semimartingale expectation calculation. The martingale component has
zero mean; the drift hypotheses are precisely first-moment and measurability
conditions needed for Fubini. -/
theorem semimartingale_forward_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V M : Ω → ℝ) (a : Ω × ℝ → ℝ)
    (v₀ C t : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hm : AEStronglyMeasurable a (P.prod (volume.restrict (Ioc 0 t))))
    (hi : ∀ s ∈ Ioc (0:ℝ) t, Integrable (fun ω => a (ω,s)) P)
    (hb : ∀ s ∈ Ioc (0:ℝ) t, (∫ ω, |a (ω,s)| ∂P) ≤ C)
    (hM : Integrable M P) (hMzero : ∫ ω, M ω ∂P=0)
    (hV : ∀ᵐ ω ∂P, V ω=v₀+M ω+∫ s in (0:ℝ)..t, a (ω,s)) :
    |(∫ ω, V ω ∂P)-v₀| ≤ C*t := by
  obtain ⟨hA,hbound⟩ := bounded_drift_mean P a C t ht hC hm hi hb
  have hsum : Integrable (fun ω => v₀+M ω) P := (integrable_const v₀).add hM
  rw [integral_congr_ae hV,integral_add hsum hA,
    integral_add (integrable_const v₀) hM,hMzero]
  simpa using hbound

end BarrierManuscript
#print axioms BarrierManuscript.bounded_drift_mean
#print axioms BarrierManuscript.semimartingale_forward_bound
