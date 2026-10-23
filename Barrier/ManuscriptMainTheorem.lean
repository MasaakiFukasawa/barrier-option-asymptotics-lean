import ManuscriptMainFamily
import ManuscriptOriginalTriple
import ManuscriptOriginalPrice
import ManuscriptOriginalProfile

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace BarrierManuscript

/-- The original-model short-maturity price expansion. All stochastic and
regularity assumptions are data or hypotheses, not assumed price identities.
The conclusion is stated sequentially on a sufficiently small maturity interval. -/
theorem main_theorem {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (D : StockSDEData P) (forward : ℝ → ℝ) (hm : Measurable forward)
    (hf : ContinuousAt forward 0) (hf0 : forward 0=D.v₀)
    (H b k δ₀ : ℝ) (hH : 0 ≤ H) (hHmax : H ≤ 1/2)
    (hb : 0 < b) (hk : k ≤ b) (hδ₀ : 0 < δ₀)
    (z : Γ → ℝ × ℝ × ℝ) (hz : Measurable z)
    (hlaw : ∀ θ : ℕ → Ioc (0:ℝ) δ₀,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      TendstoInDistribution (fun n => originalTriple D forward H (θ n).val)
        atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun t : Ioc (0:ℝ) δ₀ => fun ω =>
      (D.V (realTimeClamp t.val) ω/forward t.val-1)/t.val^H) 1 P) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ CoefficientProfile Q z b k H ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        bsKilledPut (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*b))
          (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*k)) D.S₀
          (Real.sqrt (∫ r in (0:ℝ)..(θ n).val, forward r))-
        alpha Q (fun ω => (z ω).1) (fun ω => (z ω).2.1) (fun ω => (z ω).2.2) b k H *
          D.S₀*Real.sqrt D.v₀*(θ n).val^(H+1/2))/(θ n).val^(H+1/2)) atTop (𝓝 0) := by
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
  have hprofile := original_coefficient_profile P Q D b k H hb
    (fun n => (seq n).val) (fun n => (seq n).property.1) hs
    (fun n => F (seq n)) (fun n => hX (seq n)) z hz (hlaw' seq hs)
    (uniformIntegrable_reindex P _ huiF seq)
  refine ⟨δ,hδ,hδ0,hprofile,?_⟩
  intro θ hθ
  have hn := main_family_expansion P Q D forward hf hf0 H b k δ hH hHmax hb hk
    (hδ1.trans hδ₁one) F ha hc hU he hh hX hY z hz hlaw' huiF θ hθ
  exact original_price_expansion_scaling P D forward b k H
    (alpha Q (fun ω => (z ω).1) (fun ω => (z ω).2.1) (fun ω => (z ω).2.2) b k H)
    hb (fun n => (θ n).val) (fun n => (θ n).property.1) hθ
    (fun n => F (θ n)) (fun n => hX (θ n)) hn

end BarrierManuscript
#print axioms BarrierManuscript.main_theorem
