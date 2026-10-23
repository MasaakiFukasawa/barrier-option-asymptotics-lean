import ManuscriptMainTheorem
import ManuscriptCorollary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace BarrierManuscript

/-- The limiting Brownian marginal and centered volatility coordinate, derived
from the original assumptions, including the defining forward expectation. -/
theorem original_centered_limit {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (D : StockSDEData P) (forward : ℝ → ℝ) (hm : Measurable forward)
    (hf : ContinuousAt forward 0) (hf0 : forward 0=D.v₀)
    (H δ₀ : ℝ) (hH : 0 ≤ H) (hδ₀ : 0 < δ₀)
    (z : Γ → ℝ × ℝ × ℝ)
    (hlaw : ∀ θ : ℕ → Ioc (0:ℝ) δ₀,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      TendstoInDistribution (fun n => originalTriple D forward H (θ n).val) atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun t : Ioc (0:ℝ) δ₀ => fun ω =>
      (D.V (realTimeClamp t.val) ω/forward t.val-1)/t.val^H) 1 P)
    (hforward : ∀ t : Ioc (0:ℝ) δ₀, ∫ ω, D.V (realTimeClamp t.val) ω ∂P=forward t.val) :
    ∃ B₀ : BrownianSystem (P.prod P) 1,
      Q.map (fun ω => ((z ω).1,(z ω).2.2)) =
        (P.prod P).map (fun ω => (B₀.W 0 (realTimeClamp 1) ω,brownianMaximum B₀ ω)) ∧
      Integrable (fun ω => (z ω).2.1) Q ∧ (∫ ω, (z ω).2.1 ∂Q)=0 := by
  let b : ℝ := 1
  let k : ℝ := 0
  obtain ⟨δ₁,hδ₁,hδ₁one,hbounds⟩ := local_forward_bounds forward D.v₀ hf hf0 D.hv₀
  let δ := min δ₁ δ₀
  have hδ : 0 < δ := lt_min hδ₁ hδ₀
  have hδ0 : δ ≤ δ₀ := min_le_right _ _
  have hδ1 : δ ≤ δ₁ := min_le_left _ _
  let inc : Ioc (0:ℝ) δ → Ioc (0:ℝ) δ₀ := fun t => ⟨t.val,t.property.1,t.property.2.trans hδ0⟩
  have hui' : UniformIntegrable (fun t : Ioc (0:ℝ) δ => fun ω =>
      (D.V (realTimeClamp t.val) ω/forward t.val-1)/t.val^H) 1 P :=
    uniformIntegrable_reindex P _ hui inc
  have hb' : ∀ t : Ioc (0:ℝ) δ, ∀ r ∈ Icc (0:ℝ) 1,
      (1/2:ℝ)^2 ≤ forward (t.val*r)/D.v₀ ∧ forward (t.val*r)/D.v₀ ≤ (2:ℝ)^2 := by
    intro t r hr
    exact hbounds ⟨t.val,t.property.1,t.property.2.trans hδ1⟩ r hr
  obtain ⟨L,hL,F,hF⟩ := original_normalized_family P D forward hm H δ (1/2) 2 b k hH
    (by norm_num) (by norm_num) hb' hui'
  have ha t := (hF t).1
  have hc t := (hF t).2.1
  have hU t := (hF t).2.2.1
  have he t := (hF t).2.2.2.2.1
  have hh t := (hF t).2.2.2.2.2.1
  have hX t := (hF t).2.2.2.2.2.2.1
  have hY t := (hF t).2.2.2.2.2.2.2
  have hencode (t : Ioc (0:ℝ) δ) (ω : Ω) := original_triple_encoding P D forward H t.val b k t.property.1 (F t) (hX t) (hY t) ω
  have hlaw' : ∀ t : ℕ → Ioc (0:ℝ) δ, Tendsto (fun n => (t n).val) atTop (𝓝 0) →
      TendstoInDistribution (fun n => (F (t n)).triple (F (t n)).Y 1) atTop z (fun _ => P) Q := by
    intro t ht
    exact (hlaw (fun n => inc (t n)) ht).congr
      (fun n => ae_of_all _ fun ω => (hencode (t n) ω).symm) (ae_of_all _ fun _ => rfl)
  have huiF : UniformIntegrable (fun t ω => (F t).Y (ω,1)) 1 P := by
    simpa only [hY,mul_one,inc] using hui'
  let seq : ℕ → Ioc (0:ℝ) δ := fun n => ⟨δ/((n:ℝ)+1),
    div_pos hδ (by positivity), div_le_self hδ.le (by have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)⟩
  have hs : Tendsto (fun n => (seq n).val) atTop (𝓝 0) := by
    simpa only [seq,mul_zero,div_eq_mul_inv,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  obtain ⟨B₀,hmarg⟩ := original_stock_limit_marginal P Q D.B D.S D.V D.S₀ D.v₀ b k
    D.hS₀.ne' D.hv₀ D.hSa D.hVa D.hSc D.hVc D.hSinitial D.hVinitial D.hVpos D.hM D.hSDE
    (fun n => (seq n).val) (fun n => (seq n).property.1) hs
    (fun n => F (seq n)) (fun n => hX (seq n)) z (hlaw' seq hs)
  have hη := (hlaw' seq hs).continuous_comp
    (show Continuous (fun q : ℝ × ℝ × ℝ => q.2.1) from continuous_snd.fst)
  have huiSeq := uniformIntegrable_reindex P _ huiF seq
  have hzero n : ∫ ω, (F (seq n)).Y (ω,1) ∂P=0 := by
    have hv : forward (seq n).val ≠ 0 := by
      have hp : 0 < forward (seq n).val/D.v₀ := by
        have h := (hb' (seq n) 1 ⟨zero_le_one,le_rfl⟩).1
        simp only [mul_one] at h
        linarith
      exact ((div_pos_iff_of_pos_right D.hv₀).mp hp).ne'
    have hmean := hforward (inc (seq n))
    have hiV : Integrable (D.V (realTimeClamp (seq n).val)) P :=
      Integrable.of_integral_ne_zero (by rw [hmean]; exact hv)
    simpa only [hY,mul_one] using normalized_variance_centered P _ hiV
      (forward (seq n).val) ((seq n).val^H) hv hmean
  have hcenter := centered_weak_limit P Q _ _ hη huiSeq hzero
  exact ⟨B₀,hmarg,hcenter⟩

end BarrierManuscript
#print axioms BarrierManuscript.original_centered_limit
