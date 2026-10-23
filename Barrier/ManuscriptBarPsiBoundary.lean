import ManuscriptRoughCoefficient

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The Gaussian bridge argument diverges at the initial endpoint when the
barrier is strictly positive. -/
theorem bridge_argument_initial (b k : ℝ) (hb : 0 < b) :
    Tendsto (fun u : ℝ => (b-u*k)/Real.sqrt (u*(1-u))) (𝓝[>] 0) atTop := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hn : Tendsto (fun u : ℝ => b-u*k) (𝓝[>] 0) (𝓝 b) := by
    simpa using (hu.mul_const k).const_sub b
  have hd : Tendsto (fun u : ℝ => Real.sqrt (u*(1-u))) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (hu.mul (hu.const_sub 1)).sqrt
    · filter_upwards [self_mem_nhdsWithin, hu.eventually (eventually_lt_nhds zero_lt_one)] with u hpos hlt
      exact Real.sqrt_pos.mpr (mul_pos hpos (sub_pos.mpr hlt))
  simpa only [div_eq_mul_inv,Pi.inv_apply] using hn.pos_mul_atTop hb hd.inv_tendsto_nhdsGT_zero

theorem barPhi_initial_limit (b k : ℝ) (hb : 0 < b) :
    Tendsto (barPhi b k) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hN := normalCDF_atTop.comp (bridge_argument_initial b k hb)
  have hk := hu.mul_const k
  have h := ((hk.const_sub (2*b)).sub (((hk.const_sub b).const_mul 2).mul hN)).const_mul (phi k)
  change Tendsto (fun u => barPhi b k u) _ _
  simpa only [barPhi, Function.comp_def,zero_mul,sub_zero,mul_one,sub_self,mul_zero] using h

/-- The first boundary term in the rough-coefficient integration by parts
vanishes; the value of the closed formula at u=0 is not used. -/
theorem barPsi_initial_limit (b k : ℝ) (hb : 0 < b) :
    Tendsto (barPsi b k) (𝓝[>] 0) (𝓝 0) := by
  change Tendsto (fun u => barPsi b k u) _ _
  simpa only [barPsi,sub_zero] using (barPhi_initial_limit b k hb).sub (barPhi_initial_limit b (2*b-k) hb)

/-- The positive power kills the terminal boundary term, using a uniform
bound on barPsi. No unjustified endpoint differentiability is needed. -/
theorem barPsi_weighted_terminal (b k a : ℝ) (ha : 0 < a) :
    Tendsto (fun u : ℝ => (1-u)^a*barPsi b k u) (𝓝[<] 1) (𝓝 0) := by
  let C := phi k*(4*|b|+3*|k|)+phi (2*b-k)*(4*|b|+3*|2*b-k|)
  have hu : Tendsto (fun u : ℝ => u) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hw : Tendsto (fun u : ℝ => (1-u)^a) (𝓝[<] 1) (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,Real.zero_rpow ha.ne'] using
      (Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp (hu.const_sub 1)
  apply squeeze_zero_norm' _ (by simpa only [zero_mul] using hw.mul_const C)
  filter_upwards [self_mem_nhdsWithin, hu.eventually (eventually_gt_nhds zero_lt_one)] with u hlt hpos
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)]
  exact mul_le_mul_of_nonneg_left (barPsi_uniform_bound b k u ⟨hpos.le,hlt.le⟩)
    (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)

end BarrierManuscript
#print axioms BarrierManuscript.bridge_argument_initial
#print axioms BarrierManuscript.barPhi_initial_limit
#print axioms BarrierManuscript.barPsi_initial_limit
#print axioms BarrierManuscript.barPsi_weighted_terminal
