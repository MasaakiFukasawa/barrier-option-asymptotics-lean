import ManuscriptSABRApplication
import ManuscriptMainCorollaryDifference

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The SABR correction also equals nu*rho/sqrt(v0) times the
Black--Scholes minus Bachelier price to first order. -/
theorem sabr_price_difference {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : SABRVarianceData D) (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        physicalBlackScholesPrice (sabrForward R) D.S₀ D.v₀ b k (θ n).val-
        R.ν*R.ρ/Real.sqrt D.v₀*
          (physicalBlackScholesPrice (sabrForward R) D.S₀ D.v₀ b k (θ n).val-
            physicalBachelierPrice (sabrForward R) D.S₀ D.v₀ b k (θ n).val))/(θ n).val) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hδ1,h⟩ := sabr_price_expansion P D R b k hb hk
  refine ⟨δ,hδ,hδ1,?_⟩
  intro θ hθ
  have hf : Continuous (sabrForward R) := by unfold sabrForward; fun_prop
  have h0 : sabrForward R 0=D.v₀ := by simp [sabrForward]
  have hh := corollary_price_reformulation
    (fun n => originalPrice D b k (θ n).val)
    (fun n => physicalBlackScholesPrice (sabrForward R) D.S₀ D.v₀ b k (θ n).val)
    (fun n => physicalBachelierPrice (sabrForward R) D.S₀ D.v₀ b k (θ n).val)
    (fun n => (θ n).val) D.S₀ D.v₀ (2*R.ν*R.ρ) (gamma b k) D.hv₀
    (by convert h θ hθ using 1 <;> unfold physicalBlackScholesPrice <;> congr 1 <;> funext n <;> ring)
    (forward_bs_expansion (sabrForward R) D.S₀ D.v₀ b k D.hS₀ D.hv₀ hf.measurable
      hf.continuousAt h0 (fun n => (θ n).val) (fun n => (θ n).property.1) hθ)
  convert hh using 1 <;> congr 1 <;> funext n <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.sabr_price_difference
