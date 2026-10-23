import ManuscriptStockData
import ManuscriptFamilyTimeLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem original_normalized_family {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (forward : ℝ → ℝ) (hm : Measurable forward) (H δ c U b k : ℝ)
    (hH : 0 ≤ H) (hc : 0 < c) (hU : 0 ≤ U)
    (hb : ∀ t : Ioc (0:ℝ) δ, ∀ r ∈ Icc (0:ℝ) 1,
      c^2 ≤ forward (t.val*r)/D.v₀ ∧ forward (t.val*r)/D.v₀ ≤ U^2)
    (hui : UniformIntegrable (fun t : Ioc (0:ℝ) δ => fun ω =>
      (D.V (realTimeClamp t.val) ω/forward t.val-1)/t.val^H) 1 P) :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ F : Ioc (0:ℝ) δ → NormalizedBarrierModel P b k,
      ∀ t, (F t).a=(fun r => forward (t.val*r)/D.v₀) ∧
        (F t).c=c ∧ (F t).U=U ∧ (F t).L=L ∧
        (F t).e=Real.sqrt (t.val*D.v₀) ∧ (F t).h=t.val^H ∧
        (F t).X=(fun r ω => (D.S (linearClock t.val t.property.1 (min (realTimeClamp 1) r)) ω/D.S₀-1)/Real.sqrt (t.val*D.v₀)) ∧
        (F t).Y=(fun z => (D.V (realTimeClamp (t.val*z.2)) z.1/forward (t.val*z.2)-1)/t.val^H) := by
  obtain ⟨L,hL,hui'⟩ := volatility_time_scaling P
    (fun t : Ioc (0:ℝ) δ => fun ω => (D.V (realTimeClamp t.val) ω/forward t.val-1)/t.val^H) hui H hH
  have hex (t : Ioc (0:ℝ) δ) : ∃ M : NormalizedBarrierModel P b k,
      M.a=(fun r => forward (t.val*r)/D.v₀) ∧ M.c=c ∧ M.U=U ∧ M.L=L ∧
      M.e=Real.sqrt (t.val*D.v₀) ∧ M.h=t.val^H ∧
      M.X=(fun r ω => (D.S (linearClock t.val t.property.1 (min (realTimeClamp 1) r)) ω/D.S₀-1)/Real.sqrt (t.val*D.v₀)) ∧
      M.Y=(fun z => (D.V (realTimeClamp (t.val*z.2)) z.1/forward (t.val*z.2)-1)/t.val^H) := by
    let a := fun r => forward (t.val*r)/D.v₀
    have ham : Measurable a := (hm.comp (measurable_const.mul measurable_id)).div_const _
    have hai : IntervalIntegrable a volume 0 1 := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
      apply (integrable_const (U^2)).mono' ham.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      rw [Real.norm_eq_abs,abs_of_nonneg ((sq_nonneg c).trans (hb t r hr).1)]
      exact (hb t r hr).2
    have hvol (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) :
        Integrable (fun ω => (D.V (realTimeClamp (t.val*u)) ω/(D.v₀*a u)-1)/t.val^H) P ∧
        (∫ ω, |(D.V (realTimeClamp (t.val*u)) ω/(D.v₀*a u)-1)/t.val^H| ∂P) ≤ L := by
      let τ : Ioc (0:ℝ) δ := ⟨t.val*u,mul_pos t.property.1 hu.1,
        (mul_le_of_le_one_right t.property.1.le hu.2.le).trans t.property.2⟩
      have hi := hui' u ⟨hu.1,hu.2.le⟩ (fun _ => τ)
      have he ω : (D.V (realTimeClamp (t.val*u)) ω/(D.v₀*a u)-1)/t.val^H =
          u^H*((D.V (realTimeClamp τ.val) ω/forward τ.val-1)/τ.val^H) := by
        dsimp only [a,τ]
        rw [mul_div_cancel₀ _ D.hv₀.ne']
        exact normalized_variance_time_scaling _ t.val u H t.property.1 hu.1
      constructor
      · simpa only [← he] using (hi.1.memLp 0).integrable le_rfl
      · have h := hi.2 0
        simp only [← he] at h
        exact h.trans (mul_le_of_le_one_right hL (Real.rpow_le_one hu.1.le hu.2.le hH))
    obtain ⟨M,ha,hmc,hmU,hmL,he,hh,hX,hY⟩ := stock_model_exists P D.B D.S D.V D.S₀ D.v₀ t.val H
      D.hS₀ D.hv₀ t.property.1 D.hSa D.hVa D.hSc D.hVc D.hSpos D.hVpos D.hM D.hSDE
      a ham hai c U L b k hc hU (hb t) (fun u hu => (hvol u hu).1) (fun u hu => (hvol u hu).2)
    have hY' : M.Y=(fun z => (D.V (realTimeClamp (t.val*z.2)) z.1/forward (t.val*z.2)-1)/t.val^H) := by
      rw [hY]
      funext z
      dsimp only [a]
      rw [mul_div_cancel₀ _ D.hv₀.ne']
    exact ⟨M,ha,hmc,hmU,hmL,he,hh,hX,hY'⟩
  choose F hF using hex
  exact ⟨L,hL,F,hF⟩

end BarrierManuscript
#print axioms BarrierManuscript.original_normalized_family
