import ManuscriptStockCoefficientLimit
import ManuscriptAsymptoticAssembly

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A normalized stock expansion with the coefficients obtained from the
joint weak limit. No expansion or convergence of price is a hypothesis. -/
theorem stock_expansion_limit {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) (M : ℕ → NormalizedBarrierModel P b k)
    (θ : ℕ → ℝ) (v H : ℝ) (hθ : Tendsto θ atTop (𝓝 0)) (hp : ∀ n, 0 < θ n)
    (hθ1 : ∀ n, θ n ≤ 1) (hv : 0 ≤ v) (hH : H ≤ 1/2)
    (he : ∀ n, (M n).e = Real.sqrt (v*θ n)) (hh : ∀ n, (M n).h = (θ n)^H)
    (z : ℝ → Γ → ℝ × ℝ × ℝ)
    (hlaw : ∀ u ∈ Ioo (0:ℝ) 1, TendstoInDistribution
      (fun n => (M n).triple (M n).Y u) atTop (z u) (fun _ => P) Q)
    (hui : ∀ u ∈ Ioo (0:ℝ) 1, UniformIntegrable (fun n ω => (M n).Y (ω,u)) 1 P)
    (ha : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => (M n).a u) atTop (𝓝 1))
    (hw : ∀ u ∈ Ioo (0:ℝ) 1, Tendsto (fun n => remainingVol (M n).a u) atTop (𝓝 (Real.sqrt (1-u))))
    (c V W L D : ℝ) (hc : 0 < c) (hV : 0 ≤ V) (hL₀ : 0 ≤ L) (hD : 0 ≤ D)
    (hav : ∀ n u, u ∈ Ioo (0:ℝ) 1 → |(M n).a u| ≤ V)
    (hcw : ∀ n u, u ∈ Ioo (0:ℝ) 1 → c*Real.sqrt (1-u) ≤ remainingVol (M n).a u)
    (hwW : ∀ n u, u ∈ Ioo (0:ℝ) 1 → remainingVol (M n).a u ≤ W)
    (hL : ∀ n u, u ∈ Ioo (0:ℝ) 1 → (∫ ω, |(M n).Y (ω,u)| ∂P) ≤ L)
    (hbound : ∀ n, (M n).bound ≤ D)
    (hnoatom : ∀ u ∈ Ioo (0:ℝ) 1, ∀ᵐ ω ∂Q, (z u ω).2.2 ≠ b) :
    let A := ∫ u in (0:ℝ)..1, ∫ ω,
      barrierWeight (fun x => x*thetaKernel b k 1 (Real.sqrt (1-u)) x) b
        ((z u ω).1,1,(z u ω).2.2) ∂Q
    let B := ∫ u in (0:ℝ)..1, ∫ ω,
      barrierWeight (thetaKernel b k 1 (Real.sqrt (1-u))) b (z u ω) ∂Q
    Tendsto (fun n => ((M n).price-(M n).base+2*Real.sqrt (v*θ n)*A+(θ n)^H*B)/(θ n)^H)
      atTop (𝓝 0) := by
  dsimp only
  have hA := stock_coefficient_limit P Q b k hb M (fun _ _ => 1) (fun _ => measurable_const)
    (fun u ω => ((z u ω).1,1,(z u ω).2.2))
    (fun u hu => (hlaw u hu).continuous_comp
      (show Continuous (fun q : ℝ × ℝ × ℝ => (q.1,(1:ℝ),q.2.2)) by fun_prop))
    (fun _ _ => uniformIntegrable_const (by norm_num) (by norm_num) (memLp_const (1:ℝ)))
    ha hw c V W 1 hc hV hav hcw hwW (fun _ _ _ => by simp) hnoatom 1 (by norm_num)
  have hB := stock_coefficient_limit P Q b k hb M (fun n => (M n).Y) (fun n => (M n).hYm)
    z hlaw hui ha hw c V W L hc hV hav hcw hwW hL hnoatom 0 (by norm_num)
  simp only [pow_one] at hA
  simp only [pow_zero,one_mul] at hB
  have hJ₀ n : |(M n).coefficient 2 (fun _ => 1)| ≤ 2*D*(1+L) := by
    have h := (M n).coefficient_bound 2 le_rfl (fun _ => 1) measurable_const 1
      (fun _ _ => integrable_const 1) (fun _ _ => by simp)
    nlinarith [hbound n]
  have hJ n j (hj : j ≤ 2) : |(M n).coefficient j (M n).Y| ≤ 2*D*(1+L) := by
    have h := (M n).coefficient_bound j hj (M n).Y (M n).hYm L (M n).hYs (hL n)
    have hmul := mul_le_mul_of_nonneg_right (hbound n) hL₀
    nlinarith
  apply integrated_expansion_assembly θ (fun n => (M n).price) (fun n => (M n).base)
    (fun n => (M n).coefficient 1 (fun _ => 1)) (fun n => (M n).coefficient 0 (M n).Y)
    (fun n => (M n).coefficient 2 (fun _ => 1)) (fun n => (M n).coefficient 1 (M n).Y)
    (fun n => (M n).coefficient 2 (M n).Y) v H _ _ (2*D*(1+L))
    hθ hp hθ1 hv hH hA hB hJ₀ (fun n => hJ n 1 (by norm_num)) (fun n => hJ n 2 le_rfl)
  intro n
  simpa only [he n,hh n] using (M n).price_expansion hb hk

end BarrierManuscript
#print axioms BarrierManuscript.stock_expansion_limit
