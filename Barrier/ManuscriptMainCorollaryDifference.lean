import ManuscriptMainCorollary
import ManuscriptForwardTotalLimit
import ManuscriptCorollaryPrice

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace BarrierManuscript

noncomputable def physicalBlackScholesPrice (forward : ℝ → ℝ) (S v b k θ : ℝ) : ℝ :=
  bsKilledPut (S*(1+Real.sqrt (v*θ)*b)) (S*(1+Real.sqrt (v*θ)*k)) S
    (Real.sqrt (∫ r in (0:ℝ)..θ, forward r))

theorem main_corollary_price_difference {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (D : StockSDEData P) (forward : ℝ → ℝ) (hm : Measurable forward)
    (hf : ContinuousAt forward 0) (hf0 : forward 0=D.v₀)
    (b k δ₀ : ℝ) (hb : 0 < b) (hk : k ≤ b) (hδ₀ : 0 < δ₀)
    (z : Γ → ℝ × ℝ × ℝ) (hz : Measurable z)
    (hlaw : ∀ θ : ℕ → Ioc (0:ℝ) δ₀,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      TendstoInDistribution (fun n => originalTriple D forward (1/2) (θ n).val) atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun t : Ioc (0:ℝ) δ₀ => fun ω =>
      (D.V (realTimeClamp t.val) ω/forward t.val-1)/t.val^(1/2:ℝ)) 1 P)
    (hforward : ∀ t : Ioc (0:ℝ) δ₀, ∫ ω, D.V (realTimeClamp t.val) ω ∂P=forward t.val)
    (hind : IndepFun (fun ω => (z ω).2.1-(∫ ω, (z ω).2.1*(z ω).1 ∂Q)*(z ω).1)
      (fun ω => ((z ω).1,(z ω).2.2)) Q) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        physicalBlackScholesPrice forward D.S₀ D.v₀ b k (θ n).val-
        (∫ ω, (z ω).2.1*(z ω).1 ∂Q)/(2*Real.sqrt D.v₀)*
          (physicalBlackScholesPrice forward D.S₀ D.v₀ b k (θ n).val-
            physicalBachelierPrice forward D.S₀ D.v₀ b k (θ n).val))/(θ n).val) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hδ0,hprice⟩ := main_corollary P Q D forward hm hf hf0 b k δ₀ hb hk hδ₀
    z hz hlaw hui hforward hind
  refine ⟨δ,hδ,hδ0,?_⟩
  intro θ hθ
  apply corollary_price_reformulation (fun n => originalPrice D b k (θ n).val)
    (fun n => physicalBlackScholesPrice forward D.S₀ D.v₀ b k (θ n).val)
    (fun n => physicalBachelierPrice forward D.S₀ D.v₀ b k (θ n).val)
    (fun n => (θ n).val) D.S₀ D.v₀ (∫ ω, (z ω).2.1*(z ω).1 ∂Q) (gamma b k) D.hv₀
  · simpa only [physicalBlackScholesPrice,mul_assoc,mul_comm,mul_left_comm] using hprice θ hθ
  · exact forward_bs_expansion forward D.S₀ D.v₀ b k D.hS₀ D.hv₀ hm hf hf0
      (fun n => (θ n).val) (fun n => (θ n).property.1) hθ

end BarrierManuscript
#print axioms BarrierManuscript.main_corollary_price_difference
