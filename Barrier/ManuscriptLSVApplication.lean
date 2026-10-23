import ManuscriptSmoothStateApplication
import ManuscriptLSVCoefficient

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- LSV in independent Brownian coordinates. The stock column of the
factor diffusion matrix is rho dot c, as obtained when expressing the
correlated drivers in independent coordinates. Bounds in `state` are explicit
sufficient regularity and moment hypotheses, not consequences of smoothness
alone. Stock and time coordinates refer to the actual model processes. -/
structure LSVModelData {Ω ι κ J : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P) where
  state : SmoothStateData (ι := ι) (κ := Option (Option κ)) D
  σ : (Option (Option κ) → ℝ) → ℝ
  differentiable : DifferentiableAt ℝ σ state.x₀
  positive : 0 < σ state.x₀
  variance_function : state.f=(fun x => (σ x)^2)
  stock_coordinate : ∀ t : ℝ,0 ≤ t → ∀ᵐ ω ∂P,smoothStatePoint state t ω none=D.S (realTimeClamp t) ω
  time_coordinate : ∀ t : ℝ,0 ≤ t → ∀ᵐ ω ∂P,smoothStatePoint state t ω (some none)=t
  ρ : J → ℝ
  c₀ : κ → J → ℝ
  correlation_bound : ∑ j,|ρ j|≤1
  stock_diffusion : (state.coordinate none).initial state.stock=D.S₀*σ state.x₀
  time_diffusion : (state.coordinate (some none)).initial state.stock=0
  factor_diffusion : ∀ i,(state.coordinate (some (some i))).initial state.stock=∑ j,ρ j*c₀ i j

noncomputable def lsvCoefficient {Ω ι κ J : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : LSVModelData (ι := ι) (κ := κ) (J := J) D) : ℝ :=
  D.S₀*fderiv ℝ R.σ R.state.x₀ (Pi.single none 1)+
    ∑ i,∑ j,R.ρ j*R.c₀ i j*fderiv ℝ (fun x => Real.log (R.σ x)) R.state.x₀ (Pi.single (some (some i)) 1)

theorem regular_lsv_coefficient {Ω ι κ J : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : StockSDEData P}
    (R : LSVModelData (ι := ι) (κ := κ) (J := J) D) :
    smoothStateInitialDiffusion R.state R.state.stock/D.v₀/2=lsvCoefficient R := by
  have hv : D.v₀=(R.σ R.state.x₀)^2 := by
    rw [← R.state.initial_variance,R.variance_function]
  rw [hv]
  unfold smoothStateInitialDiffusion smoothStateGradient
  rw [R.variance_function]
  exact lsv_gradient_coefficient R.σ R.state.x₀ R.differentiable R.positive D.S₀ R.ρ R.c₀
    (fun i => (R.state.coordinate i).initial R.state.stock)
    R.stock_diffusion R.time_diffusion R.factor_diffusion

/-- The manuscript's regular LSV price formula, derived from the original
state equations under the explicit sufficient bounds in `LSVModelData`.
No variance decomposition, UI, joint-limit or price conclusion is a field. -/
theorem regular_lsv_price_expansion {Ω ι κ J : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype J]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (R : LSVModelData (ι := ι) (κ := κ) (J := J) D)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1 ∧ ∀ θ : ℕ → Ioc (0:ℝ) δ,
      Tendsto (fun n => (θ n).val) atTop (𝓝 0) →
      Tendsto (fun n => (originalPrice D b k (θ n).val-
        bsKilledPut (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*b))
          (D.S₀*(1+Real.sqrt (D.v₀*(θ n).val)*k)) D.S₀
          (Real.sqrt (D.v₀*(θ n).val))-
        lsvCoefficient R*gamma b k*D.S₀*Real.sqrt D.v₀*(θ n).val)/(θ n).val) atTop (𝓝 0) := by
  have h := smooth_state_price_expansion P D R.state b k hb hk
  rwa [regular_lsv_coefficient R] at h

end BarrierManuscript
#print axioms BarrierManuscript.regular_lsv_coefficient
#print axioms BarrierManuscript.regular_lsv_price_expansion
