import ManuscriptGeometricCoefficientLimit
import ManuscriptGeometricModelPrice
import ManuscriptBlackScholesExpansion

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The gamma identity is obtained by comparing the constructed geometric
stock's Ito expansion with its independently evaluated Black--Scholes price. -/
theorem gamma_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    (∫ u in (0:ℝ)..1, barPsi b k u) = gamma b k := by
  obtain ⟨w,_,hw,hlim⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  choose M ha hc hU hL he hY hX using fun n => geometric_normalized_model P B b k (w n) (hw n)
  have hA := geometric_coefficient_limit P B b k hb w hw hlim M ha hX
  let D := normalizer*(1+2*k^2+4)+normalizer*(1+2*(2*b-k)^2+4)
  have hJ n : |(M n).coefficient 2 (fun _ => 1)| ≤ D := by
    have h := (M n).coefficient_bound 2 le_rfl (fun _ => 1) measurable_const 1
      (fun _ _ => integrable_const 1) (fun _ _ => by simp)
    simp only [NormalizedBarrierModel.bound,hU n,hc n,one_pow,mul_one] at h
    dsimp only [D]
    linarith
  have hrem := bounded_multiplier_vanishes w (fun n => (M n).coefficient 2 (fun _ => 1)) D hlim hJ
  have hprice n : (M n).price=killedPut b k 0 1-
      (2*w n*(M n).coefficient 1 (fun _ => 1)+(w n)^2*(M n).coefficient 2 (fun _ => 1)) := by
    have h := (M n).price_expansion hb hk
    simpa [NormalizedBarrierModel.base,ha n,he n,hY n,NormalizedBarrierModel.coefficient] using h
  have hK : ∀ᶠ n in atTop, 0 < 1+w n*k :=
    (show Tendsto (fun n => 1+w n*k) atTop (𝓝 1) by simpa using (hlim.mul_const k).const_add 1).eventually (eventually_gt_nhds zero_lt_one)
  have hIto : Tendsto (fun n => (bsKilledPut (1+w n*b) (1+w n*k) 1 (w n)-
      w n*killedPut b k 0 1)/(w n)^2) atTop (𝓝 (∫ u in (0:ℝ)..1, barPsi b k u)) := by
    have h := (hA.const_mul (-2)).sub hrem
    have hc : (-2)*(-(1/2)*(∫ u in (0:ℝ)..1, barPsi b k u))-0 = ∫ u in (0:ℝ)..1, barPsi b k u := by ring
    rw [hc] at h
    apply h.congr'
    filter_upwards [hK] with n hkn
    rw [← geometric_model_price P B b k (w n) hb hk (hw n) hkn (M n) (hX n),hprice n]
    field_simp [(hw n).ne']
    <;> ring
  have hBS := bsKilledPut_expansion b k w (fun _ => 1) hlim tendsto_const_nhds (fun n => (hw n).ne')
  have hBS' : Tendsto (fun n => (bsKilledPut (1+w n*b) (1+w n*k) 1 (w n)-
      w n*killedPut b k 0 1)/(w n)^2) atTop (𝓝 (gamma b k)) := by
    have h := hBS.add_const (gamma b k)
    simp only [zero_add,mul_one] at h
    apply h.congr
    intro n
    field_simp [(hw n).ne']
    <;> ring
  exact tendsto_nhds_unique hIto hBS'

end BarrierManuscript
#print axioms BarrierManuscript.gamma_integral
