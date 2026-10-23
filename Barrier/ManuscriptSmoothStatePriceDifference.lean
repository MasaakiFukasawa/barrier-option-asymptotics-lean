import ManuscriptSmoothStateApplication
import ManuscriptMainCorollaryDifference

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The original smooth state model also has the second price representation. -/
theorem smooth_state_price_difference {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SmoothStateData (ι := ι) (κ := κ) D) (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        physicalBlackScholesPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val-
        (smoothStateInitialDiffusion R R.stock/D.v₀/2)/Real.sqrt D.v₀*
          (physicalBlackScholesPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val-
            physicalBachelierPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val))/(θ n).val) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hδ1,h⟩ := smooth_state_price_expansion P D R b k hb hk
  refine ⟨δ,hδ,hδ1,?_⟩
  intro θ hθ
  have hf : Continuous (fun _ : ℝ => D.v₀) := continuous_const
  have h0 : (fun _ : ℝ => D.v₀) 0=D.v₀ := rfl
  have hh := corollary_price_reformulation
    (fun n => originalPrice D b k (θ n).val)
    (fun n => physicalBlackScholesPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val)
    (fun n => physicalBachelierPrice (fun _ => D.v₀) D.S₀ D.v₀ b k (θ n).val)
    (fun n => (θ n).val) D.S₀ D.v₀ (smoothStateInitialDiffusion R R.stock/D.v₀) (gamma b k) D.hv₀
    (by
      have hp := h θ hθ
      simpa only [physicalBlackScholesPrice,intervalIntegral.integral_const,sub_zero,smul_eq_mul,
        mul_comm ((θ _).val) D.v₀,mul_assoc,mul_comm,mul_left_comm] using hp)
    (forward_bs_expansion (fun _ => D.v₀) D.S₀ D.v₀ b k D.hS₀ D.hv₀ hf.measurable
      hf.continuousAt h0 (fun n => (θ n).val) (fun n => (θ n).property.1) hθ)
  convert hh using 1 <;> congr 1 <;> funext n <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.smooth_state_price_difference
