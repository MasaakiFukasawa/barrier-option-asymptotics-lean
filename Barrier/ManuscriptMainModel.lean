import ManuscriptStockExpansionLimit
import ManuscriptAlpha
import ManuscriptBlackScholesBaseline
import ManuscriptClockTotalLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Main stochastic-volatility expansion for the constructed normalized
stock models. The Brownian marginal identifies the regular coefficient;
the BS baseline and volatility correction are derived rather than assumed.
Original-model construction and maturity rescaling are separate theorems. -/
theorem main_model_expansion {Ω Γ Λ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace Λ]
    (P : Measure Ω) (Q : Measure Γ) (R : Measure Λ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (B₀ : BrownianSystem R 1) (ξ η ζ : Γ → ℝ) (hξ : Measurable ξ) (hζ : Measurable ζ)
    (hmarginal : Q.map (fun ω => (ξ ω,ζ ω)) =
      R.map (fun ω => (B₀.W 0 (realTimeClamp 1) ω,brownianMaximum B₀ ω)))
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) (M : ℕ → NormalizedBarrierModel P b k)
    (θ : ℕ → ℝ) (v H : ℝ) (hθ : Tendsto θ atTop (𝓝 0)) (hp : ∀ n, 0 < θ n)
    (hθ1 : ∀ n, θ n ≤ 1) (hv : 0 < v) (hH : H ≤ 1/2)
    (he : ∀ n, (M n).e = Real.sqrt (v*θ n)) (hh : ∀ n, (M n).h = (θ n)^H)
    (hlaw : ∀ u ∈ Ioo (0:ℝ) 1, TendstoInDistribution
      (fun n => (M n).triple (M n).Y u) atTop
      (fun ω => (Real.sqrt u*ξ ω,u^H*η ω,Real.sqrt u*ζ ω)) (fun _ => P) Q)
    (hui : ∀ u ∈ Ioo (0:ℝ) 1, UniformIntegrable (fun n ω => (M n).Y (ω,u)) 1 P)
    (ha : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => (M n).a u) atTop (𝓝 1))
    (hw : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => remainingVol (M n).a u) atTop (𝓝 (Real.sqrt (1-u))))
    (c V W L D : ℝ) (hc : 0 < c) (hV : 0 ≤ V) (hL₀ : 0 ≤ L) (hD : 0 ≤ D)
    (hav : ∀ n u, u ∈ Ioo (0:ℝ) 1 → |(M n).a u| ≤ V)
    (hcw : ∀ n u, u ∈ Ioo (0:ℝ) 1 → c*Real.sqrt (1-u) ≤ remainingVol (M n).a u)
    (hwW : ∀ n u, u ∈ Ioo (0:ℝ) 1 → remainingVol (M n).a u ≤ W)
    (hL : ∀ n u, u ∈ Ioo (0:ℝ) 1 → (∫ ω, |(M n).Y (ω,u)| ∂P) ≤ L)
    (hbound : ∀ n, (M n).bound ≤ D) :
    let w := fun n => Real.sqrt (∫ s in (0:ℝ)..1, (M n).a s)
    let e := fun n => Real.sqrt (v*θ n)
    Tendsto (fun n => ((M n).price-
      bsKilledPut (1+e n*b) (1+e n*k) 1 (e n*w n)/e n-
      (θ n)^H*alpha Q ξ η ζ b k H)/(θ n)^H) atTop (𝓝 0) := by
  let z := fun u ω => (Real.sqrt u*ξ ω,u^H*η ω,Real.sqrt u*ζ ω)
  have hn u (hu : u ∈ Ioo (0:ℝ) 1) : ∀ᵐ ω ∂Q, (z u ω).2.2 ≠ b := by
    filter_upwards [marginal_maximum_noatom R Q B₀ ξ ζ hξ hζ hmarginal
      (b/Real.sqrt u) (div_pos hb (Real.sqrt_pos.mpr hu.1))] with ω hω
    intro heq
    apply hω
    apply (eq_div_iff (Real.sqrt_pos.mpr hu.1).ne').mpr
    simpa only [z,mul_comm] using heq
  have hs := stock_expansion_limit P Q b k hb hk M θ v H hθ hp hθ1 hv.le hH he hh
    z hlaw hui ha hw c V W L D hc hV hL₀ hD hav hcw hwW hL hbound hn
  dsimp only at hs ⊢
  have hA : (∫ u in (0:ℝ)..1, ∫ ω,
      barrierWeight (fun x => x*thetaKernel b k 1 (Real.sqrt (1-u)) x) b
        ((z u ω).1,(1:ℝ),(z u ω).2.2) ∂Q) = -(1/2)*gamma b k := by
    rw [← gamma_integral R B₀ b k hb hk,← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact limit_psi_first_moment R Q B₀ ξ ζ hξ hζ hmarginal b k u hb hu
  rw [hA] at hs
  have hw0 := bounded_clock_total_limit (fun n => (M n).a) (fun n => (M n).ham) V hav ha
  have hbs := normalized_bs_baseline_expansion b k v H hv hH θ
    (fun n => Real.sqrt (∫ s in (0:ℝ)..1, (M n).a s)) hp hθ1 hθ hw0
  have h := hs.sub hbs
  simp only [sub_zero] at h
  apply h.congr
  intro n
  unfold NormalizedBarrierModel.base alpha
  dsimp only [z]
  ring

end BarrierManuscript
#print axioms BarrierManuscript.main_model_expansion
