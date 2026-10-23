import ManuscriptBlackScholesReflection
import ManuscriptPhiAverage
import ManuscriptLogRatio

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def bsBarrierNormalized (b k e w : ℝ) : ℝ :=
  k*normalCDF (logRatio k e/w+e*w/2)+w*phiAverage (logRatio k e/w) (e*w)-
  ((k-2*b-e*b^2)/(1+e*b))*normalCDF ((logRatio k e-2*logRatio b e)/w+e*w/2)-
  (1+e*b)*w*phiAverage ((logRatio k e-2*logRatio b e)/w) (e*w)

noncomputable def gamma (b k : ℝ) : ℝ :=
  k/2*(phi k-phi (k-2*b))-b*(b-k)*normalCDF (k-2*b)

theorem bsBarrierNormalized_zero (b k w : ℝ) :
    bsBarrierNormalized b k 0 w = killedPut b k 0 w := by
  simp only [bsBarrierNormalized,logRatio,ite_true,zero_mul,mul_zero,add_zero,sub_zero,
    div_one,one_mul,phiAverage_zero,killedPut,put]
  ring

theorem bsKilledPut_unit (B K w : ℝ) (hB : 0 < B) (hK : 0 < K) :
    bsKilledPut B K 1 w =
      K*normalCDF (Real.log K/w+w/2)-normalCDF (Real.log K/w-w/2)-
      (K/B*normalCDF ((Real.log K-2*Real.log B)/w+w/2)-
        B*normalCDF ((Real.log K-2*Real.log B)/w-w/2)) := by
  unfold bsKilledPut bsStockPut bsPut
  simp only [Real.log_one,sub_zero,one_mul,div_one]
  rw [Real.exp_log hK,Real.exp_sub,Real.exp_log (sq_pos_of_pos hB),Real.exp_log hK,Real.log_pow]
  field_simp
  ring

theorem bsBarrierNormalized_formula (b k e w : ℝ) (he : e ≠ 0)
    (hb : 0 < 1+e*b) (hk : 0 < 1+e*k) :
    e*bsBarrierNormalized b k e w = bsKilledPut (1+e*b) (1+e*k) 1 (e*w) := by
  have hl k : logRatio k e = Real.log (1+e*k)/e := by simp [logRatio,he,mul_comm]
  have hd k : logRatio k e/w = Real.log (1+e*k)/(e*w) := by rw [hl]; ring
  have hr : (logRatio k e-2*logRatio b e)/w =
      (Real.log (1+e*k)-2*Real.log (1+e*b))/(e*w) := by rw [hl,hl]; ring
  have h1 := normalCDF_difference_average (logRatio k e/w) (e*w)
  have h2 := normalCDF_difference_average ((logRatio k e-2*logRatio b e)/w) (e*w)
  rw [bsKilledPut_unit _ _ _ hb hk]
  unfold bsBarrierNormalized
  rw [← hd,← hr]
  have hc : e*((k-2*b-e*b^2)/(1+e*b)) = (1+e*k)/(1+e*b)-(1+e*b) := by
    field_simp
    ring
  calc
    _ = e*k*normalCDF (logRatio k e/w+e*w/2)+(e*w)*phiAverage (logRatio k e/w) (e*w)-
        e*((k-2*b-e*b^2)/(1+e*b))*normalCDF ((logRatio k e-2*logRatio b e)/w+e*w/2)-
        (1+e*b)*((e*w)*phiAverage ((logRatio k e-2*logRatio b e)/w) (e*w)) := by ring
    _ = _ := by rw [← h1,← h2,hc]; ring

end BarrierManuscript
#print axioms BarrierManuscript.bsBarrierNormalized_zero
#print axioms BarrierManuscript.bsKilledPut_unit
#print axioms BarrierManuscript.bsBarrierNormalized_formula
