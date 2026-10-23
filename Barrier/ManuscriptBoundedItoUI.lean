import ManuscriptBoundedItoMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Bounded regular diffusion coefficients give UI of the actual scaled
Ito fluctuations for the whole continuum of small maturities. -/
theorem bounded_ito_uniformIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G N : HalfClosedTime → Ω → ℝ)
    (hGa : ∀ t,t < ⊤ → Measurable[B.F t] (G t))
    (hGc : ∀ ω t,t < ⊤ → ContinuousAt (fun s => G s ω) t)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => G (realTimeClamp z.2) z.1) N)
    (K δ : ℝ) (hK : 0 ≤ K)
    (hb : ∀ ω s,s ∈ Icc (0:ℝ) δ → |G (realTimeClamp s) ω| ≤ K) :
    UniformIntegrable (fun t : Ioc (0:ℝ) δ => fun ω => N (realTimeClamp t.val) ω/Real.sqrt t.val) 1 P := by
  have hm (t : Ioc (0:ℝ) δ) : Measurable (N (realTimeClamp t.val)) :=
    ((hN.adapted P B.F _ (halfTimeClamp_finite t.val)).mono (B.le _) le_rfl)
  have hbound (t : Ioc (0:ℝ) δ) := bounded_ito_second_moment P B G N hGa hGc hN hNI K t.val hK
    t.property.1.le (fun ω s hs => hb ω s ⟨hs.1,hs.2.trans t.property.2⟩)
  apply second_moment_uniformIntegrable P _ (fun t => (hm t).div_const _)
    (fun t => by simpa only [div_eq_mul_inv,mul_comm] using (hbound t).1.const_mul (Real.sqrt t.val)⁻¹)
    (K^2) (sq_nonneg K)
  intro t
  simp_rw [div_pow]
  rw [integral_div,Real.sq_sqrt t.property.1.le]
  exact (div_le_iff₀ t.property.1).mpr (hbound t).2

end BarrierManuscript
#print axioms BarrierManuscript.bounded_ito_uniformIntegrable
