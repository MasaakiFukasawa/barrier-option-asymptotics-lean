import ManuscriptRoughIBP

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem barPsi_derivative_intervalIntegrable (b k a : ℝ) (ha : 0 ≤ a) :
    IntervalIntegrable (barPsiTimeDerivative b k) volume 0 a := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ha).mpr
  exact (integrable_const (phi k*|k|+phi (2*b-k)*|2*b-k|)).mono'
    (barPsiTimeDerivative_measurable b k).aestronglyMeasurable
    (ae_of_all _ fun s => by simpa only [Real.norm_eq_abs] using barPsiTimeDerivative_bound b k s)

/-- Weighted integration by parts uses the right limit zero of barPsi at
zero, rather than its irrelevant totalized formula value at that endpoint. -/
theorem barPsi_test_ibp (b k a : ℝ) (hb : 0 < b) (ha : a ∈ Ioo (0:ℝ) 1)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g) :
    g a*barPsi b k a-(∫ s in (0:ℝ)..a,deriv g s*barPsi b k s)=
      ∫ s in (0:ℝ)..a,g s*barPsiTimeDerivative b k s := by
  have hpsi : IntervalIntegrable (barPsi b k) volume 0 1 := by
    simpa only [sub_self,Real.rpow_zero,one_mul] using
      rough_coefficient_integrable b k (1/2) (by norm_num)
  have hpsia : IntervalIntegrable (barPsi b k) volume 0 a := hpsi.mono_set (by
    rw [uIcc_of_le ha.1.le,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ha.2.le)
  have hi := hpsia.continuousOn_mul (hg.continuous_deriv le_rfl).continuousOn
  have hj := (barPsi_derivative_intervalIntegrable b k a ha.1.le).continuousOn_mul hg.continuous.continuousOn
  have hD (s : ℝ) (hs : s ∈ Ioo (0:ℝ) a) :
      HasDerivAt (fun r => g r*barPsi b k r)
        (deriv g s*barPsi b k s+g s*barPsiTimeDerivative b k s) s := by
    have h := ((hg.differentiable (by norm_num)).differentiableAt.hasDerivAt).mul
      (barPsi_derivative b k s ⟨hs.1,hs.2.trans ha.2⟩)
    convert h using 1 <;> rfl
  have hleft : Tendsto (fun s => g s*barPsi b k s) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using (hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (barPsi_initial_limit b k hb)
  have hright : Tendsto (fun s => g s*barPsi b k s) (𝓝[<] a) (𝓝 (g a*barPsi b k a)) :=
    (hg.continuous.continuousAt.mul (barPsi_derivative b k a ha).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ha.1 hD (hi.add hj) hleft hright
  rw [intervalIntegral.integral_add hi hj,sub_zero] at h
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.barPsi_derivative_intervalIntegrable
#print axioms BarrierManuscript.barPsi_test_ibp
