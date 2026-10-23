import ManuscriptBrownianKilledPut

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- An integrable bound for the whole Brownian path on a finite interval,
derived from its actual quadratic variation and Doob's inequality. -/
theorem brownian_integrable_path_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ D : Ω → ℝ, Integrable D P ∧ (∀ ω, 0 ≤ D ω) ∧
      ∀ ω s, s ∈ Icc (0:ℝ) T → |B.W 0 (realTimeClamp s) ω| ≤ D ω := by
  obtain ⟨hc,hm,hn⟩ := local_energy_maximal_bound P B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) (realTimeClamp T)
    (changed_time_finite T hT) (fun _ => T) (integrable_const T) 1 zero_le_one
    (ae_of_all _ fun ω => by rw [B.diagonal_clock 0 ω T hT]; simpa using hT)
  let X := continuousPath (fun t ω => B.W 0 (min (realTimeClamp T) t) ω) hc
  have hp : MemLp X 2 P := hn.trans_lt ENNReal.ofReal_lt_top
  refine ⟨fun ω => ‖X ω‖,hp.norm.integrable (by norm_num),fun _ => norm_nonneg _,?_⟩
  intro ω s hs
  have hh := (X ω).norm_coe_le_norm (realTimeClamp s)
  have hst : realTimeClamp s ≤ (realTimeClamp T : HalfClosedTime) := real_time_clamp_mono hs.2
  simpa only [X,continuousPath,ContinuousMap.coe_mk,min_eq_right hst,Real.norm_eq_abs] using hh

end BarrierManuscript
#print axioms BarrierManuscript.brownian_integrable_path_bound
