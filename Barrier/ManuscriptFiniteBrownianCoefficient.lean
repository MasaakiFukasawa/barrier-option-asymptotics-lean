import ManuscriptFiniteBrownianLaw
import ManuscriptCorollary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace BarrierManuscript

/-- For finitely many independent Brownian drivers, only the coefficient
of the stock driver contributes to the first barrier correction. Independence
here concerns the entire stock path, not just its terminal value. -/
theorem finite_brownian_tangent_coefficient {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ι → BrownianSystem P 1)
    (hind : iIndepFun (fun i => brownianContinuousPath (B i)) P)
    (i₀ : ι) (a : ι → ℝ) (b k : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    alpha P ((B i₀).W 0 (realTimeClamp 1))
      (fun ω => ∑ i,a i*(B i).W 0 (realTimeClamp 1) ω)
      (brownianMaximum (B i₀)) b k (1/2) = (a i₀/2)*gamma b k := by
  let s := Finset.univ.erase i₀
  let R : Ω → ℝ := fun ω => ∑ i ∈ s,a i*(B i).W 0 (realTimeClamp 1) ω
  have hm i : Measurable ((B i).W 0 (realTimeClamp 1)) :=
    (((B i).martingale 0).adapted P (B i).F _ (halfTimeClamp_finite 1)).mono ((B i).le _) le_rfl
  have hcenter i := brownian_marginal_centered P P (B i) _ _ (hm i)
    (brownianMaximum_measurable P (B i)) rfl
  have hR : Measurable R := Finset.measurable_sum _ (fun i _ => measurable_const.mul (hm i))
  have hiR : Integrable R P := integrable_finset_sum _ (fun i _ => (hcenter i).1.const_mul (a i))
  have hR0 : (∫ ω,R ω ∂P)=0 := by
    rw [integral_finset_sum _ (fun i _ => (hcenter i).1.const_mul (a i))]
    simp only [integral_const_mul,fun i => (hcenter i).2,mul_zero,Finset.sum_const_zero]
  let g : ι → C(ℝ≥0,ℝ) → C(ℝ≥0,ℝ) := fun i p => if i=i₀ then p else a i • p
  have hg : ∀ i,Measurable (g i) := by
    intro i
    dsimp only [g]
    split_ifs <;> fun_prop
  have hi := (hind.comp g hg).indepFun_finsetSum_of_notMem
    (fun i => (hg i).comp (brownian_continuous_path_measurable (B i)))
    (s := s) (i := i₀) (Finset.notMem_erase _ _)
  let h : C(ℝ≥0,ℝ) → ℝ × ℝ := fun p => (p 1,pathMaximum (pathRestriction 1 p))
  have hh : Measurable h := (continuous_eval_const 1).measurable.prodMk
    (pathMaximum_lipschitz.continuous.comp (ContinuousMap.continuous_precomp _)).measurable
  have hir := hi.comp (continuous_eval_const (1:ℝ≥0)).measurable hh
  have he ω : ((∑ i ∈ s,(g i ∘ brownianContinuousPath (B i))) ω) 1=R ω := by
    simp only [Finset.sum_apply,ContinuousMap.sum_apply,Function.comp_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hn : i≠i₀ := (Finset.mem_erase.mp hi).1
    simp [g,hn,brownianContinuousPath]
  have he' ω : h ((g i₀ ∘ brownianContinuousPath (B i₀)) ω) =
      ((B i₀).W 0 (realTimeClamp 1) ω,brownianMaximum (B i₀) ω) := by
    simp only [Function.comp_apply,g,ite_true,h,brownian_maximum_encoding P]
    rfl
  have hri : IndepFun R (fun ω => ((B i₀).W 0 (realTimeClamp 1) ω,brownianMaximum (B i₀) ω)) P := by
    change IndepFun (fun ω => ((∑ i ∈ s,(g i ∘ brownianContinuousPath (B i))) ω) 1)
      (fun ω => h ((g i₀ ∘ brownianContinuousPath (B i₀)) ω)) P at hir
    simpa only [he,he'] using hir
  have hc := linear_alpha P P (B i₀) _ _ R (hm i₀)
    (brownianMaximum_measurable P (B i₀)) hR (hcenter i₀).1 hiR hri hR0 rfl (a i₀) b k hb hk
  convert hc using 1
  congr 2
  funext ω
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm

end BarrierManuscript
#print axioms BarrierManuscript.finite_brownian_tangent_coefficient
