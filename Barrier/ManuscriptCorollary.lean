import ManuscriptCorollaryCoefficient

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem brownian_marginal_centered {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M : Γ → ℝ) (hX : Measurable X) (hM : Measurable M)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω))) :
    Integrable X Q ∧ (∫ ω, X ω ∂Q)=0 := by
  have hm : Measurable (B.W 0 (realTimeClamp 1)) :=
    ((B.martingale 0).adapted P B.F _ (halfTimeClamp_finite 1)).mono (B.le _) le_rfl
  have hid : IdentDistrib (fun ω => (X ω,M ω))
      (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)) Q P :=
    ⟨(hX.prodMk hM).aemeasurable,(hm.prodMk (brownianMaximum_measurable P B)).aemeasurable,hlaw⟩
  have hx : IdentDistrib X (B.W 0 (realTimeClamp 1)) Q P := hid.comp measurable_fst
  have hg : HasLaw (B.W 0 (realTimeClamp 1)) (gaussianReal 0 1) P := by
    convert scaled_brownian_gaussian_law P B 1 1 (by norm_num) (by norm_num) using 1 <;> norm_num
    congr 1
  refine ⟨hx.integrable_iff.mpr (hg.integrable ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl)),?_⟩
  rw [hx.integral_eq,hg.integral_eq,integral_id_gaussianReal]

/-- Corollary 1's coefficient, with eta's zero mean supplied by the
forward-variance normalization and weak/UI convergence. -/
theorem corollary_coefficient {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (X M Y : Γ → ℝ)
    (hX : Measurable X) (hM : Measurable M) (hY : Measurable Y) (hiY : Integrable Y Q)
    (hzero : ∫ ω, Y ω ∂Q=0)
    (hlaw : Q.map (fun ω => (X ω,M ω)) =
      P.map (fun ω => (B.W 0 (realTimeClamp 1) ω,brownianMaximum B ω)))
    (hind : IndepFun (fun ω => Y ω-(∫ ω, Y ω*X ω ∂Q)*X ω) (fun ω => (X ω,M ω)) Q)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    alpha Q X Y M b k (1/2) = ((∫ ω, Y ω*X ω ∂Q)/2)*gamma b k := by
  obtain ⟨hiX,hXZ⟩ := brownian_marginal_centered P Q B X M hX hM hlaw
  let a := ∫ ω, Y ω*X ω ∂Q
  let R := fun ω => Y ω-a*X ω
  have hR : Measurable R := hY.sub (measurable_const.mul hX)
  have hiR : Integrable R Q := hiY.sub (hiX.const_mul a)
  have hz : ∫ ω, R ω ∂Q=0 := by
    dsimp only [R]
    rw [integral_sub hiY (hiX.const_mul a),integral_const_mul,hzero,hXZ]
    ring
  have hh := linear_alpha P Q B X M R hX hM hR hiX hiR hind hz hlaw a b k hb hk
  have he : (fun ω => a*X ω+R ω)=Y := by funext ω; dsimp only [R]; ring
  rw [he] at hh
  exact hh

/-- The forward curve makes the normalized variance fluctuation centered. -/
theorem normalized_variance_centered {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (V : Ω → ℝ) (hi : Integrable V P)
    (v h : ℝ) (hv : v ≠ 0) (he : ∫ ω, V ω ∂P=v) :
    (∫ ω, (V ω/v-1)/h ∂P)=0 := by
  rw [integral_div,integral_sub (hi.div_const v) (integrable_const 1),integral_div,he]
  simp [hv]

end BarrierManuscript
#print axioms BarrierManuscript.brownian_marginal_centered
#print axioms BarrierManuscript.corollary_coefficient
#print axioms BarrierManuscript.normalized_variance_centered
