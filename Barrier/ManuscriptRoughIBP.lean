import ManuscriptBarPsiDerivative
import ManuscriptBarPsiBoundary

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def barPsiTimeDerivative (b k u : ℝ) : ℝ :=
  phi k*k*(2*normalCDF (bridgeArgument b k u)-1)-
    phi (2*b-k)*(2*b-k)*(2*normalCDF (bridgeArgument b (2*b-k) u)-1)

theorem barPsiTimeDerivative_measurable (b k : ℝ) : Measurable (barPsiTimeDerivative b k) := by
  have hN := normalCDF_contDiff.continuous.measurable
  unfold barPsiTimeDerivative bridgeArgument
  fun_prop

theorem barPsiTimeDerivative_bound (b k u : ℝ) :
    |barPsiTimeDerivative b k u| ≤ phi k*|k|+phi (2*b-k)*|2*b-k| := by
  have hN (x : ℝ) : |2*normalCDF x-1| ≤ 1 := by
    have hn : 0 ≤ normalCDF x := measureReal_nonneg
    have h1 : normalCDF x ≤ 1 := measureReal_le_one
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  unfold barPsiTimeDerivative
  apply (abs_sub _ _).trans
  apply add_le_add
  all_goals
    rw [abs_mul,abs_mul,abs_of_nonneg (phi_nonneg _)]
    exact mul_le_of_le_one_right (mul_nonneg (phi_nonneg _) (abs_nonneg _)) (hN _)

theorem weighted_barPsi_derivative_integrable (b k a : ℝ) (ha : 0 ≤ a) :
    IntervalIntegrable (fun s : ℝ => barPsiTimeDerivative b k s*(1-s)^a/a) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
  apply ((integrable_const (phi k*|k|+phi (2*b-k)*|2*b-k|)).mono' ?_ ?_).div_const a
  · exact ((barPsiTimeDerivative_measurable b k).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (Real.rpow_le_one (sub_nonneg.mpr hs.2) (by linarith [hs.1]) ha)).trans
      (barPsiTimeDerivative_bound b k s)

/-- The rough-coefficient integration by parts with both boundary terms and
all required integrability established for the actual barPsi formula. -/
theorem rough_coefficient_ibp (b k a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    (∫ s in (0:ℝ)..1, barPsiTimeDerivative b k s*(1-s)^a/a) =
      ∫ s in (0:ℝ)..1, (1-s)^(a-1)*barPsi b k s := by
  let F : ℝ → ℝ := fun s => (1-s)^a*barPsi b k s/a
  have hD (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
      HasDerivAt F (barPsiTimeDerivative b k s*(1-s)^a/a-(1-s)^(a-1)*barPsi b k s) s := by
    have hw := ((hasDerivAt_id s).const_sub 1).rpow_const (p := a) (Or.inl (sub_pos.mpr hs.2).ne')
    have hψ := barPsi_derivative b k s hs
    convert (hw.mul hψ).div_const a using 1
    · rfl
    · dsimp only [id_eq,barPsiTimeDerivative]
      field_simp
      <;> ring
  have hi := weighted_barPsi_derivative_integrable b k a ha.le
  have hj : IntervalIntegrable (fun s : ℝ => (1-s)^(a-1)*barPsi b k s) volume 0 1 := by
    convert rough_coefficient_integrable b k (a-1/2) (by linarith) using 1
    congr 1
    funext s
    rw [show a-1/2-1/2=a-1 by ring]
  have hleft : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have hu : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have hw := (Real.continuous_rpow_const ha.le).continuousAt.tendsto.comp (hu.const_sub 1)
    simpa only [F,Function.comp_def,sub_zero,Real.one_rpow,one_mul,zero_div] using
      (hw.mul (barPsi_initial_limit b k hb)).div_const a
  have hright : Tendsto F (𝓝[<] 1) (𝓝 0) := by
    simpa only [F,zero_div] using (barPsi_weighted_terminal b k a ha).div_const a
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hD (hi.sub hj) hleft hright
  rw [intervalIntegral.integral_sub hi hj] at h
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.barPsiTimeDerivative_measurable
#print axioms BarrierManuscript.barPsiTimeDerivative_bound
#print axioms BarrierManuscript.weighted_barPsi_derivative_integrable
#print axioms BarrierManuscript.rough_coefficient_ibp
