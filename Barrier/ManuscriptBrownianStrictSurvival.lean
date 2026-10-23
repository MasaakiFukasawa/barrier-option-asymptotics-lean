import ManuscriptBrownianDriftedDensity

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem drifted_survival_strict_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (a b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂P, (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-a*r < b) ↔
      (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-a*r ≤ b) := by
  obtain ⟨Q,hQ,hQd,BQ,he⟩ := brownian_constant_tilt P B a
  letI := hQ
  have hq : ∀ᵐ ω ∂Q, (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-a*r < b) ↔
      (∀ r ∈ Icc (0:ℝ) 1, B.W 0 (realTimeClamp r) ω-a*r ≤ b) := by
    filter_upwards [he,brownian_maximum_noatom Q BQ b hb] with ω hω hn
    constructor
    · exact fun h r hr => (h r hr).le
    · intro h r hr
      have hm : brownianMaximum BQ ω ≤ b := (brownian_maximum_le_real_iff Q BQ ω b).mpr (fun s hs => by
        have hh := h s hs; rw [hω s hs] at hh; linarith)
      have hw : BQ.W 0 (realTimeClamp r) ω ≤ brownianMaximum BQ ω :=
        (brownian_maximum_le_real_iff Q BQ ω _).mp le_rfl r hr
      rw [hω r hr]
      linarith [lt_of_le_of_ne hm hn]
  rw [hQd] at hq
  have hd : Measurable (fun ω => ENNReal.ofReal (Real.exp (a*B.W 0 (realTimeClamp 1) ω-a^2/2))) :=
    ((((B.martingale 0).adapted P B.F _ (halfTimeClamp_finite 1)).mono (B.le _) le_rfl).const_mul a |>.sub_const (a^2/2)).exp.ennreal_ofReal
  exact ((ae_withDensity_iff hd).mp hq).mono fun ω hω => hω (by positivity)

end BarrierManuscript
#print axioms BarrierManuscript.drifted_survival_strict_ae
