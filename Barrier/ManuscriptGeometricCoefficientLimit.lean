import ManuscriptBrownianPsiMoment

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem geometric_coefficient_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hlim : Tendsto w atTop (𝓝 0))
    (M : ℕ → NormalizedBarrierModel P b k) (ha : ∀ n, (M n).a=fun _ => 1)
    (hX : ∀ n, (M n).X=(fun t ω => (geometricStock B (w n) (min (realTimeClamp 1) t) ω-1)/w n)) :
    Tendsto (fun n => (M n).coefficient 1 (fun _ => 1)) atTop
      (𝓝 (-(1/2)*(∫ u in (0:ℝ)..1, barPsi b k u))) := by
  classical
  let z := fun u ω => if h : 0 ≤ u then
    (B.W 0 (realTimeClamp u) ω,(1:ℝ),pathMaximum (brownianStoppedPath B u h ω)) else (0,1,0)
  have hlaw u (hu : u ∈ Ioo (0:ℝ) 1) : TendstoInDistribution (fun n => (M n).triple (fun _ => 1) u)
      atTop (z u) (fun _ => P) P := by
    simpa only [z,dif_pos hu.1.le] using geometric_triple_limit P B b k w hw hlim M hX u ⟨hu.1.le,hu.2.le⟩
  have hr n u : remainingVol (M n).a u=Real.sqrt (1-u) := by simp [remainingVol,ha n]
  have h := stock_coefficient_limit P P b k hb M (fun _ _ => 1) (fun _ => measurable_const) z hlaw
    (fun _ _ => uniformIntegrable_const (by norm_num) (by norm_num) (memLp_const (1:ℝ)))
    (fun _ _ => by simpa only [ha] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
    (fun u _ => by simpa only [hr] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.sqrt (1-u)) atTop (𝓝 (Real.sqrt (1-u)))))
    1 1 1 1 zero_lt_one zero_le_one (fun n _ _ => by simp [ha n])
    (fun n u _ => by simp [hr]) (fun n u hu => by rw [hr]; exact Real.sqrt_le_one.mpr (by linarith [hu.1]))
    (fun _ _ _ => by simp)
    (fun u hu => by simpa only [z,dif_pos hu.1.le] using brownian_prefix_maximum_noatom P B b u hb hu.1)
    1 (by norm_num)
  simp only [pow_one] at h
  have he : (∫ u in (0:ℝ)..1, ∫ ω, barrierWeight (fun x => x*thetaKernel b k 1 (Real.sqrt (1-u)) x) b (z u ω) ∂P) =
      -(1/2)*(∫ u in (0:ℝ)..1, barPsi b k u) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simpa only [z,dif_pos hu.1.le] using brownian_prefix_psi_moment P B b k u hb hu
  rwa [he] at h

end BarrierManuscript
#print axioms BarrierManuscript.geometric_coefficient_limit
