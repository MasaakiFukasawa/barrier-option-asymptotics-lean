import ManuscriptPathLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def expRatio (x : ℝ) : ℝ := if x=0 then 1 else (Real.exp x-1)/x

theorem expRatio_continuous : Continuous expRatio := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have h := (Real.hasDerivAt_exp 0).continuousAt_div
    convert! h using 1
    funext y
    by_cases hy : y=0 <;> simp [expRatio,hy,Function.update]
  · have hc : ContinuousAt (fun y : ℝ => (Real.exp y-1)/y) x :=
      ((Real.continuous_exp.continuousAt).sub continuousAt_const).div continuousAt_id hx
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [expRatio,hy]

theorem expRatio_identity (x : ℝ) : x*expRatio x = Real.exp x-1 := by
  by_cases hx : x=0
  · simp [hx,expRatio]
  · simp only [expRatio,if_neg hx]
    field_simp

noncomputable def expPathExtension (e x t : ℝ) : ℝ :=
  (x-e*t/2)*expRatio (e*(x-e*t/2))

theorem expPathExtension_formula (e x t : ℝ) (he : e ≠ 0) :
    expPathExtension e x t = (Real.exp (e*x-e^2*t/2)-1)/e := by
  apply (eq_div_iff he).mpr
  unfold expPathExtension
  calc
    _ = (e*(x-e*t/2))*expRatio (e*(x-e*t/2)) := by ring
    _ = _ := by rw [expRatio_identity]; congr 2; ring

theorem expPathExtension_zero (x t : ℝ) : expPathExtension 0 x t=x := by
  simp [expPathExtension,expRatio]

theorem expPathExtension_continuous {A : Type*} [TopologicalSpace A]
    (E X T : A → ℝ) (he : Continuous E) (hx : Continuous X) (ht : Continuous T) :
    Continuous (fun r => expPathExtension (E r) (X r) (T r)) :=
  (hx.sub ((he.mul ht).div_const 2)).mul
    (expRatio_continuous.comp (he.mul (hx.sub ((he.mul ht).div_const 2))))

noncomputable def expPathMap {K : Type*} [TopologicalSpace K]
    (X T : C(K,ℝ)) (e : ℝ) : C(K,ℝ) :=
  ⟨fun r => expPathExtension e (X r) (T r),
    expPathExtension_continuous _ _ _ continuous_const X.continuous T.continuous⟩

/-- Uniform convergence of normalized exponential paths on a compact domain. -/
theorem exponential_path_limit {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (X T : C(K,ℝ)) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => expPathMap X T (e n)) atTop (𝓝 X) := by
  have hc : Continuous (expPathMap X T) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact expPathExtension_continuous _ _ _ continuous_fst
      (X.continuous.comp continuous_snd) (T.continuous.comp continuous_snd)
  have hz : expPathMap X T 0=X := by ext r; exact expPathExtension_zero _ _
  simpa only [hz,Function.comp_def] using hc.continuousAt.tendsto.comp he

end BarrierManuscript
#print axioms BarrierManuscript.expRatio_continuous
#print axioms BarrierManuscript.expRatio_identity
#print axioms BarrierManuscript.expPathExtension_formula
#print axioms BarrierManuscript.expPathExtension_zero
#print axioms BarrierManuscript.exponential_path_limit
