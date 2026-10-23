import ManuscriptOriginalCentering

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace BarrierManuscript

/-- The original-model regular-volatility corollary. The centeredness and
Brownian marginal used to reduce alpha are derived, not additional hypotheses. -/
theorem main_corollary {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
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
        bsKilledPut (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*b))
          (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*k)) D.S₀
          (Real.sqrt (∫ r in (0:ℝ)..(θ n).val, forward r))-
        ((∫ ω, (z ω).2.1*(z ω).1 ∂Q)/2)*gamma b k*D.S₀*Real.sqrt D.v₀*(θ n).val)/
        (θ n).val) atTop (𝓝 0) := by
  obtain ⟨B₀,hmarg,hi,hzero⟩ := original_centered_limit P Q D forward hm hf hf0 (1/2) δ₀
    (by norm_num) hδ₀ z hlaw hui hforward
  have hα := corollary_coefficient (P.prod P) Q B₀ (fun ω => (z ω).1)
    (fun ω => (z ω).2.2) (fun ω => (z ω).2.1) hz.fst hz.snd.snd hz.snd.fst
    hi hzero hmarg hind b k hb hk
  obtain ⟨δ,hδ,hδ0,hprofile,hprice⟩ := main_theorem P Q D forward hm hf hf0 (1/2) b k δ₀
    (by norm_num) le_rfl hb hk hδ₀ z hz hlaw hui
  refine ⟨δ,hδ,hδ0,fun θ hθ => ?_⟩
  simpa only [hα,show (1/2:ℝ)+1/2=1 by norm_num,Real.rpow_one] using hprice θ hθ

end BarrierManuscript
#print axioms BarrierManuscript.main_corollary
