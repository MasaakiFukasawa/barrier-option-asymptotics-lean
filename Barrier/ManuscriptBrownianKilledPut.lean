import ManuscriptMaturityExpectation
import Chapter3LocalEnergyMaximal
import Mathlib.Topology.Order.IsLUB

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Derive the killed Brownian put price from Ito's formula and the actual
Brownian bracket. The path bound follows from Doob, rather than being added
to the Brownian assumptions. This supplies a route to the killed law without
assuming a reflection principle. -/
theorem brownian_killed_put {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    let X := fun t ω => B.W 0 (min (realTimeClamp 1) t) ω
    (∫ ω, max (k-X (realTimeClamp (cappedBarrier X b ω)) ω) 0 ∂P) = killedPut b k 0 1 := by
  dsimp only
  let X := fun t ω => B.W 0 (min (realTimeClamp 1) t) ω
  let C := fun t ω => B.C 0 0 (min (realTimeClamp 1) t) ω
  have ht1 : realTimeClamp (T := (⊤:EReal)) 1 < ⊤ := changed_time_finite 1 (by norm_num)
  have hs : ∀ t, MeasurableSet[B.F t] {ω : Ω | realTimeClamp (T := (⊤:EReal)) 1 ≤ t} := by
    intro t
    by_cases ht : realTimeClamp (T := (⊤:EReal)) 1 ≤ t <;> simp [ht]
  have hX := (B.martingale 0).stopped P B.F B.mono B.le (fun _ => realTimeClamp 1) hs
  obtain ⟨hXm,hXc⟩ := (B.martingale 0).stopped_regular P B.F B.mono B.le
    (fun _ => realTimeClamp 1) hs (fun _ => ht1)
  have hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → B.C 0 0 (realTimeClamp r) ω = ∫ s in 0..r, (1:ℝ) := by
    exact ae_of_all _ fun ω r hr => by simp [B.diagonal_clock 0 ω r hr]
  obtain ⟨_,hC,hCG'⟩ := stopped_covariance_density P B.F B.mono B.le (B.W 0) (B.C 0 0)
    (B.martingale 0) (B.cov 0 0) (fun _ => 1) hCG (fun _ => 1) (fun _ => by norm_num) hs
  obtain ⟨hpath,hpathm,hpathnorm⟩ := local_energy_maximal_bound P B.F B.mono B.le B.null
    (B.W 0) (B.C 0 0) (B.martingale 0) (B.cov 0 0) (realTimeClamp 1) ht1
    (fun _ => 1) (integrable_const 1) 1 (by norm_num)
    (ae_of_all _ fun ω => by rw [B.diagonal_clock 0 ω 1 (by norm_num)]; norm_num)
  let D := fun ω => ‖continuousPath X hpath ω‖
  have hD : Integrable D P := by
    have hp : MemLp (continuousPath X hpath) 2 P :=
      hpathnorm.trans_lt ENNReal.ofReal_lt_top
    exact hp.norm.integrable (by norm_num)
  have hbound : ∀ᵐ ω ∂P, ∀ t, |X (min (realTimeClamp (cappedBarrier X b ω)) t) ω| ≤ D ω := by
    exact ae_of_all _ fun ω t => by
      simpa only [D,Real.norm_eq_abs,continuousPath,ContinuousMap.coe_mk] using
        (continuousPath X hpath ω).norm_coe_le_norm (min (realTimeClamp (cappedBarrier X b ω)) t)
  let G := fun z : Ω × ℝ => if z.2 ≤ 1 then (1:ℝ) else 0
  have hgzero s (hs : s ∈ Ioo (0:ℝ) 1) ω : barrierDrift X G (fun _ => 1) b k (ω,s) = 0 := by
    simp [barrierDrift,G,hs.2.le]
  have hmem : ∀ᵐ z ∂P.prod (volume.restrict (Ioo (0:ℝ) 1)), z.2 ∈ Ioo (0:ℝ) 1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_snd)).mpr
      (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Ioo)
  have hdi : Integrable (barrierDrift X G (fun _ => 1) b k) (P.prod (volume.restrict (Ioo 0 1))) :=
    (integrable_zero _ _ _).congr (hmem.mono fun z hz => (hgzero z.2 hz z.1).symm)
  obtain ⟨t,_,ht,htlim⟩ := exists_seq_strictMono_tendsto' (by norm_num : (0:ℝ) < 1)
  have he := maturity_price_expectation P B.F B.mono B.le B.null X C hX hXm hXc hC
    (fun _ => 1) measurable_const intervalIntegrable_const 1 (by norm_num) (fun _ _ => le_rfl)
    G (fun _ => measurable_const.ite measurableSet_Iic measurable_const)
    (fun r hr => ae_of_all _ fun _ => stopped_density_intervalIntegrable (fun _ => 1) 1 r intervalIntegrable_const)
    hCG' b k hk ((hX.initial P B.F).mono fun ω hω => by
      change X ⊥ ω = 0 at hω
      rw [hω]
      exact hb)
    hdi D hD hbound t (fun n => ⟨(ht n).1.le,(ht n).2⟩) htlim
  have hint : (∫ s in (0:ℝ)..1, ∫ ω, barrierDrift X G (fun _ => 1) b k (ω,s) ∂P) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    simp only [hgzero s hs,integral_zero]
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,Real.sqrt_one,hint,add_zero] using he

end BarrierManuscript
#print axioms BarrierManuscript.brownian_killed_put
