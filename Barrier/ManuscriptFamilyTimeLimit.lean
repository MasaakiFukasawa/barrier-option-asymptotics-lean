import ManuscriptMaturityTripleScaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem maturity_family_time_limits {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (S V : HalfClosedTime → Ω → ℝ) (forward : ℝ → ℝ) (S₀ v H b k δ : ℝ)
    (hv : 0 < v) (hH : 0 ≤ H) (F : Ioc (0:ℝ) δ → NormalizedBarrierModel P b k)
    (hX : ∀ t, (F t).X=fun r ω => (S (linearClock t.val t.property.1 (min (realTimeClamp 1) r)) ω/S₀-1)/Real.sqrt (t.val*v))
    (hY : ∀ t, (F t).Y=fun z => (V (realTimeClamp (t.val*z.2)) z.1/forward (t.val*z.2)-1)/t.val^H)
    (z : Γ → ℝ × ℝ × ℝ)
    (hlaw : ∀ t : ℕ → Ioc (0:ℝ) δ, Tendsto (fun n => (t n).val) atTop (𝓝 0) →
      TendstoInDistribution (fun n => (F (t n)).triple (F (t n)).Y 1) atTop z (fun _ => P) Q)
    (hui : UniformIntegrable (fun t ω => (F t).Y (ω,1)) 1 P)
    (θ : ℕ → Ioc (0:ℝ) δ) (hθ : Tendsto (fun n => (θ n).val) atTop (𝓝 0)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u ∈ Ioo (0:ℝ) 1,
      TendstoInDistribution (fun n => (F (θ n)).triple (F (θ n)).Y u) atTop
        (fun ω => (Real.sqrt u*(z ω).1,u^H*(z ω).2.1,Real.sqrt u*(z ω).2.2)) (fun _ => P) Q ∧
      UniformIntegrable (fun n ω => (F (θ n)).Y (ω,u)) 1 P ∧
      ∀ n, (∫ ω, |(F (θ n)).Y (ω,u)| ∂P) ≤ L := by
  obtain ⟨L,hL,hui'⟩ := volatility_time_scaling P (fun t ω => (F t).Y (ω,1)) hui H hH
  refine ⟨L,hL,?_⟩
  intro u hu
  let τ : ℕ → Ioc (0:ℝ) δ := fun n => ⟨(θ n).val*u,
    mul_pos (θ n).property.1 hu.1,(mul_le_of_le_one_right (θ n).property.1.le hu.2.le).trans (θ n).property.2⟩
  have ht : Tendsto (fun n => (τ n).val) atTop (𝓝 0) := by simpa only [τ,zero_mul] using hθ.mul_const u
  have he n ω := stock_triple_time_scaling P S V forward S₀ (θ n).val v u H b k
    (θ n).property.1 hv ⟨hu.1,hu.2.le⟩ (F (θ n)) (F (τ n)) (hX (θ n)) (hX (τ n)) (hY (θ n)) (hY (τ n)) ω
  have hvol n ω : (F (θ n)).Y (ω,u)=u^H*(F (τ n)).Y (ω,1) := congrArg (fun q : ℝ × ℝ × ℝ => q.2.1) (he n ω)
  refine ⟨?_,?_,?_⟩
  · exact (triple_time_scaling_law P Q _ z (hlaw τ ht) u H).congr
      (fun n => ae_of_all _ fun ω => (he n ω).symm) (ae_of_all _ fun _ => rfl)
  · have h := (hui' u ⟨hu.1,hu.2.le⟩ τ).1
    simpa only [← hvol] using h
  · intro n
    have h := (hui' u ⟨hu.1,hu.2.le⟩ τ).2 n
    simp only [← hvol] at h
    exact h.trans (mul_le_of_le_one_right hL (Real.rpow_le_one hu.1.le hu.2.le hH))

end BarrierManuscript
#print axioms BarrierManuscript.maturity_family_time_limits
