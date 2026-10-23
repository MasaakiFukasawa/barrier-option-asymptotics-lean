import ManuscriptTruncation
import ManuscriptUniformIntegrability
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem uniformIntegrable_reindex {Ω ι κ : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ι → Ω → ℝ) (hui : UniformIntegrable Y 1 P) (r : κ → ι) :
    UniformIntegrable (fun i => Y (r i)) 1 P := by
  refine ⟨hui.1.comp r,?_⟩
  obtain ⟨C,hC⟩ := hui.2
  exact ⟨C,fun i => hC (r i)⟩

/-- The self-similar time rescaling of the volatility fluctuations preserves
UI and gives the common u^H moment bound used in time integration. -/
theorem volatility_time_scaling {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (hui : UniformIntegrable Y 1 P)
    (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ), u ∈ Ioc (0:ℝ) 1 → ∀ (r : ℕ → ι),
      UniformIntegrable (fun n ω => u^H*Y (r n) ω) 1 P ∧
        ∀ n, (∫ ω, |u^H*Y (r n) ω| ∂P) ≤ C*u^H := by
  obtain ⟨C,hC⟩ := hui.2
  refine ⟨C,C.property,?_⟩
  intro u hu r
  have hp : 0 ≤ u^H := Real.rpow_nonneg hu.1.le H
  have hup : u^H ≤ 1 := Real.rpow_le_one hu.1.le hu.2 hH
  constructor
  · apply uniformIntegrable_unit_weight P (fun n => Y (r n)) (fun _ _ => u^H)
      (uniformIntegrable_reindex P Y hui r) (fun _ => aestronglyMeasurable_const)
    exact fun _ => ae_of_all _ fun _ => by rw [abs_of_nonneg hp]; exact hup
  · intro n
    have hi := hui.memLp (r n) |>.integrable le_rfl
    have hb := integral_abs_le_of_eLpNorm_le P (Y (r n)) hi C C.property (by simpa using hC (r n))
    simp_rw [abs_mul,abs_of_nonneg hp]
    rw [integral_const_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hp

/-- The concrete continuous map in equation (conv2). -/
theorem triple_time_scaling_law {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Z : ℕ → Ω → ℝ × ℝ × ℝ) (z : Γ → ℝ × ℝ × ℝ)
    (h : TendstoInDistribution Z atTop z (fun _ => P) Q) (u H : ℝ) :
    TendstoInDistribution (fun n ω => (Real.sqrt u*(Z n ω).1,u^H*(Z n ω).2.1,Real.sqrt u*(Z n ω).2.2))
      atTop (fun ω => (Real.sqrt u*(z ω).1,u^H*(z ω).2.1,Real.sqrt u*(z ω).2.2)) (fun _ => P) Q :=
by
  have hc : Continuous (fun a : ℝ × ℝ × ℝ => (Real.sqrt u*a.1,u^H*a.2.1,Real.sqrt u*a.2.2)) := by fun_prop
  exact h.continuous_comp hc

end BarrierManuscript
#print axioms BarrierManuscript.uniformIntegrable_reindex
#print axioms BarrierManuscript.volatility_time_scaling
#print axioms BarrierManuscript.triple_time_scaling_law
