import ManuscriptGeometricModel
import ManuscriptNoHitReal

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem geometric_model_price {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k w : ℝ) (hb : 0 < b) (hk : k ≤ b) (hw : 0 < w) (hK : 0 < 1+w*k)
    (M : NormalizedBarrierModel P b k)
    (hX : M.X=(fun t ω => (geometricStock B w (min (realTimeClamp 1) t) ω-1)/w)) :
    w*M.price = bsKilledPut (1+w*b) (1+w*k) 1 w := by
  rw [← geometric_brownian_barrier_price P B (1+w*k) (1+w*b) w hK
    (by nlinarith) (by nlinarith) hw]
  unfold NormalizedBarrierModel.price
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [M.hX.initial P M.F] with ω h0
  have h0b : M.X ⊥ ω < b := by simpa only [h0,Pi.zero_apply] using hb
  have hs := nohit_real_iff M.X M.hXc ω b h0b
  have hx r (hr : r ∈ Icc (0:ℝ) 1) : M.X (realTimeClamp r) ω =
      (Real.exp (w*B.W 0 (realTimeClamp r) ω-w^2*r/2)-1)/w := by
    rw [hX]
    dsimp only
    rw [min_eq_right (real_time_clamp_mono hr.2),geometricStock_real P B w r hr.1 ω]
  have he : (¬ ∃ t, t ≤ realTimeClamp 1 ∧ M.X t ω=b) ↔
      (∀ r ∈ Icc (0:ℝ) 1, Real.exp (w*B.W 0 (realTimeClamp r) ω-w^2*r/2) < 1+w*b) := by
    rw [hs]
    apply forall_congr'
    intro r
    apply forall_congr'
    intro hr
    rw [hx r hr,div_lt_iff₀ hw]
    constructor <;> intro h <;> nlinarith
  have ht : M.X (realTimeClamp 1) ω = (Real.exp (w*B.W 0 (realTimeClamp 1) ω-w^2/2)-1)/w := by
    simpa only [mul_one] using hx 1 (by norm_num)
  by_cases hh : ∃ t, t ≤ realTimeClamp 1 ∧ M.X t ω=b
  · rw [if_pos hh,if_neg (fun h => (he.mpr h) hh),mul_zero]
  · rw [if_neg hh,if_pos (he.mp hh),ht,mul_max_of_nonneg _ _ hw.le,mul_zero]
    congr 1
    field_simp
    <;> ring

end BarrierManuscript
#print axioms BarrierManuscript.geometric_model_price
