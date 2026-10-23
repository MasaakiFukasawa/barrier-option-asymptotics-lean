import Chapter7BrownianPathLaw
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators
namespace BarrierManuscript
open Asakura.Chapter7
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written Asakura.Chapter2Complete Asakura.Chapter4
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Any finite list of samples on one common grid has the same law for
two constructed Brownian systems. The assertion is deduced from Levy's
joint increment characteristic function and the initial value zero. -/
theorem brownian_grid_samples_cross_law
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ι : Type*} [Fintype ι]
    (B : BrownianSystem P 1) (B0 : BrownianSystem Q 1) (h : ℝ) (hh : 0 ≤ h) (k : ι → ℕ) :
    IdentDistrib (fun w i => B.W 0 (realTimeClamp ((k i:ℝ)*h)) w)
      (fun w i => B0.W 0 (realTimeClamp ((k i:ℝ)*h)) w) P Q := by
  classical
  let N := Finset.univ.sup k
  have hk i : k i ≤ N := Finset.le_sup (f := k) (Finset.mem_univ i)
  let f := fun z : Fin N → Fin 1 → ℝ => fun i => ∑ j : Fin (k i),z ⟨j.val,j.isLt.trans_le (hk i)⟩ 0
  have hfm : Measurable f := by
    apply measurable_pi_iff.mpr
    intro i
    exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply 0).comp (measurable_pi_apply _))
  obtain ⟨hm,hcl,_⟩ := B.grid_law h hh N
  obtain ⟨hm0,hcl0,_⟩ := B0.grid_law h hh N
  have hl : IdentDistrib (finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h N)
      (finiteNoiseGrid (fun j r => B0.W j (realTimeClamp r)) h N) P Q :=
    ⟨hm.aemeasurable,hm0.aemeasurable,Measure.ext_of_charFunDual (hcl.trans hcl0.symm)⟩
  have hf := hl.comp hfm
  have heB :
      (fun w => f (finiteNoiseGrid (fun j r => B.W j (realTimeClamp r)) h N w)) =ᵐ[P]
        (fun w i => B.W 0 (realTimeClamp ((k i:ℝ)*h)) w) := by
    filter_upwards [(B.martingale 0).initial P B.F] with w hw
    funext i
    dsimp only [f,finiteNoiseGrid]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => B.W 0 (realTimeClamp (((j:ℝ)+1)*h)) w-B.W 0 (realTimeClamp ((j:ℝ)*h)) w)]
    have heq : (∑ j ∈ Finset.range (k i),
        (B.W 0 (realTimeClamp (((j:ℝ)+1)*h)) w-B.W 0 (realTimeClamp ((j:ℝ)*h)) w)) =
        B.W 0 (realTimeClamp ((k i:ℝ)*h)) w-B.W 0 (realTimeClamp ((0:ℝ)*h)) w := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero] using
        Finset.sum_range_sub (fun j : ℕ => B.W 0 (realTimeClamp ((j:ℝ)*h)) w) (k i)
    rw [heq]
    have hz : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl le_top
    simp only [zero_mul,hz,hw,Pi.zero_apply,sub_zero]
  have heC :
      (fun w => f (finiteNoiseGrid (fun j r => B0.W j (realTimeClamp r)) h N w)) =ᵐ[Q]
        (fun w i => B0.W 0 (realTimeClamp ((k i:ℝ)*h)) w) := by
    filter_upwards [(B0.martingale 0).initial Q B0.F] with w hw
    funext i
    dsimp only [f,finiteNoiseGrid]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => B0.W 0 (realTimeClamp (((j:ℝ)+1)*h)) w-B0.W 0 (realTimeClamp ((j:ℝ)*h)) w)]
    have heq : (∑ j ∈ Finset.range (k i),
        (B0.W 0 (realTimeClamp (((j:ℝ)+1)*h)) w-B0.W 0 (realTimeClamp ((j:ℝ)*h)) w)) =
        B0.W 0 (realTimeClamp ((k i:ℝ)*h)) w-B0.W 0 (realTimeClamp ((0:ℝ)*h)) w := by
      simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero] using
        Finset.sum_range_sub (fun j : ℕ => B0.W 0 (realTimeClamp ((j:ℝ)*h)) w) (k i)
    rw [heq]
    have hz : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ := by
      apply Subtype.ext
      exact real_time_clamp_eq 0 le_rfl le_top
    simp only [zero_mul,hz,hw,Pi.zero_apply,sub_zero]
  exact (IdentDistrib.of_ae_eq hf.aemeasurable_fst heB).symm.trans
    (hf.trans (IdentDistrib.of_ae_eq hf.aemeasurable_snd heC))

theorem brownian_continuous_path_cross_law
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : BrownianSystem P 1) (B0 : BrownianSystem Q 1) :
    IdentDistrib (brownianContinuousPath B) (brownianContinuousPath B0) P Q := by
  have hm := brownian_continuous_path_measurable B
  have hm0 := brownian_continuous_path_measurable B0
  have he : IdentDistrib (fun w => pathGridValues (brownianContinuousPath B w))
      (fun w => pathGridValues (brownianContinuousPath B0 w)) P Q := by
    have hX := (path_grid_values_embedding.measurable.comp hm).aemeasurable (μ := P)
    have hY := (path_grid_values_embedding.measurable.comp hm0).aemeasurable (μ := Q)
    have hfin : ∀ I : Finset (ℕ × ℕ),
        IdentDistrib (fun ω => I.restrict (pathGridValues (brownianContinuousPath B ω)))
          (fun ω => I.restrict (pathGridValues (brownianContinuousPath B0 ω))) P Q := by
      intro I
      obtain ⟨D,hD,k,hk⟩ := finite_clock_grid_common_denominator (fun i : I => i.val)
      have hl := brownian_grid_samples_cross_law P Q B B0 (1/(D:ℝ)) (by positivity) k
      convert hl using 1 <;> funext w i <;>
        simp only [Function.comp_def,Finset.restrict, pathGridValues,brownianContinuousPath,ContinuousMap.coe_mk,hk i,div_eq_mul_inv,one_div,one_mul]
    have hmaps I := (hfin I).map_eq
    have hproj : IsProjectiveLimit
        (P.map (fun ω => pathGridValues (brownianContinuousPath B ω)))
        (fun I => Q.map (fun ω => I.restrict (pathGridValues (brownianContinuousPath B0 ω)))) := by
      intro I
      dsimp only
      rw [← hmaps I]
      exact (isProjectiveLimit_map hX) I
    exact ⟨hX,hY,hproj.unique (isProjectiveLimit_map hY)⟩
  refine ⟨hm.aemeasurable,hm0.aemeasurable,?_⟩
  apply path_grid_values_embedding.map_injective
  rw [Measure.map_map path_grid_values_embedding.measurable hm,
    Measure.map_map path_grid_values_embedding.measurable hm0]
  exact he.map_eq


end BarrierManuscript
#print axioms BarrierManuscript.brownian_grid_samples_cross_law
#print axioms BarrierManuscript.brownian_continuous_path_cross_law
