import ManuscriptMainModel
import ManuscriptFamilyConstruction
import ManuscriptLocalForwardBounds
import ManuscriptOriginalMarginal

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem main_family_expansion {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (D : StockSDEData P) (forward : ℝ → ℝ) (hf : ContinuousAt forward 0) (hf0 : forward 0=D.v₀)
    (H b k δ : ℝ) (hH : 0 ≤ H) (hHmax : H ≤ 1/2) (hb : 0 < b) (hk : k ≤ b) (hδ : δ ≤ 1)
    (F : Ioc (0:ℝ) δ → NormalizedBarrierModel P b k)
    (ha : ∀ t, (F t).a=fun u => forward (t.val*u)/D.v₀)
    (hc : ∀ t, (F t).c=1/2) (hU : ∀ t, (F t).U=2)
    (he : ∀ t, (F t).e=Real.sqrt (t.val*D.v₀)) (hh : ∀ t, (F t).h=t.val^H)
    (hX : ∀ t, (F t).X=fun r ω => (D.S (linearClock t.val t.property.1 (min (realTimeClamp 1) r)) ω/D.S₀-1)/Real.sqrt (t.val*D.v₀))
    (hY : ∀ t, (F t).Y=fun z => (D.V (realTimeClamp (t.val*z.2)) z.1/forward (t.val*z.2)-1)/t.val^H)
    (z : Γ → ℝ × ℝ × ℝ) (hz : Measurable z)
    (hlaw : ∀ t : ℕ → Ioc (0:ℝ) δ, Tendsto (fun n => (t n).val) atTop (𝓝 0) →
      TendstoInDistribution (fun n => (F (t n)).triple (F (t n)).Y 1) atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun t ω => (F t).Y (ω,1)) 1 P)
    (θ : ℕ → Ioc (0:ℝ) δ) (hθ : Tendsto (fun n => (θ n).val) atTop (𝓝 0)) :
    let w := fun n => Real.sqrt (∫ s in (0:ℝ)..1, forward ((θ n).val*s)/D.v₀)
    let e := fun n => Real.sqrt (D.v₀*(θ n).val)
    Tendsto (fun n => ((F (θ n)).price-bsKilledPut (1+e n*b) (1+e n*k) 1 (e n*w n)/e n-
      (θ n).val^H*alpha Q (fun ω => (z ω).1) (fun ω => (z ω).2.1) (fun ω => (z ω).2.2) b k H)/(θ n).val^H)
      atTop (𝓝 0) := by
  obtain ⟨B₀,hmarg⟩ := original_stock_limit_marginal P Q D.B D.S D.V D.S₀ D.v₀ b k
    D.hS₀.ne' D.hv₀ D.hSa D.hVa D.hSc D.hVc D.hSinitial D.hVinitial D.hVpos D.hM D.hSDE
    (fun n => (θ n).val) (fun n => (θ n).property.1) hθ (fun n => F (θ n)) (fun n => hX (θ n)) z (hlaw θ hθ)
  obtain ⟨L,hL,htime⟩ := maturity_family_time_limits P Q D.S D.V forward D.S₀ D.v₀ H b k δ
    D.hv₀ hH F hX hY z hlaw hui θ hθ
  have halim u (hu : u ∈ Ioo (0:ℝ) 1) : Tendsto (fun n => (F (θ n)).a u) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => (θ n).val*u) atTop (𝓝 0) := by
      simpa only [zero_mul] using hθ.mul_const u
    have h := (hf.div_const D.v₀).tendsto.comp ht
    simpa only [ha,hf0,mul_zero,zero_mul,div_self D.hv₀.ne',Function.comp_def] using h
  have hwlim u (hu : u ∈ Ioo (0:ℝ) 1) : Tendsto (fun n => remainingVol (F (θ n)).a u) atTop (𝓝 (Real.sqrt (1-u))) := by
    have hi n : IntervalIntegrable (fun s => forward ((θ n).val*s)/D.v₀) volume u 1 := by
      rw [← ha (θ n)]
      exact (F (θ n)).hai.mono_set (by rw [uIcc_of_le hu.2.le,uIcc_of_le zero_le_one]; exact Icc_subset_Icc hu.1.le le_rfl)
    simpa only [ha] using (normalized_forward_remaining_limit forward D.v₀ hf hf0 D.hv₀.ne'
      (fun n => (θ n).val) hθ u ⟨hu.1.le,hu.2.le⟩ hi).2
  let C : ℝ := (2:ℝ)^2/(2*(1/2))*(normalizer*(1+2*k^2+4*(2:ℝ)^2)+normalizer*(1+2*(2*b-k)^2+4*(2:ℝ)^2))
  have hC : 0 ≤ C := by have hn := normalizer_nonneg; dsimp only [C]; positivity
  have hbound n : (F (θ n)).bound ≤ C := by
    unfold NormalizedBarrierModel.bound
    rw [hc (θ n),hU (θ n)]
  have h := main_model_expansion P Q (P.prod P) B₀ (fun ω => (z ω).1) (fun ω => (z ω).2.1) (fun ω => (z ω).2.2)
    hz.fst hz.snd.snd hmarg b k hb hk (fun n => F (θ n)) (fun n => (θ n).val) D.v₀ H hθ
    (fun n => (θ n).property.1) (fun n => (θ n).property.2.trans hδ) D.hv₀ hHmax
    (fun n => by simpa only [mul_comm] using he (θ n)) (fun n => hh (θ n))
    (fun u hu => (htime u hu).1) (fun u hu => (htime u hu).2.1) halim hwlim
    (1/2) 4 2 L C (by norm_num) (by norm_num) hL hC
    (fun n u hu => (normalized_model_clock_bounds P b k (F (θ n)) (hc (θ n)) (hU (θ n)) u hu).1)
    (fun n u hu => (normalized_model_clock_bounds P b k (F (θ n)) (hc (θ n)) (hU (θ n)) u hu).2.1)
    (fun n u hu => (normalized_model_clock_bounds P b k (F (θ n)) (hc (θ n)) (hU (θ n)) u hu).2.2)
    (fun n u hu => (htime u hu).2.2 n) hbound
  simpa only [ha] using h

end BarrierManuscript
#print axioms BarrierManuscript.main_family_expansion
