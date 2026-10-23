import ManuscriptJointLawLimit

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem fixed_pair_weak_limit {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → E) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hF : Measurable F) (hY : ∀ n, Measurable (Y n)) (hZ : Measurable Z)
    (herror : TendstoInMeasure P (fun n ω => Z ω-Y n ω) atTop (fun _ => 0)) :
    TendstoInDistribution (fun n ω => (F ω,Y n ω)) atTop (fun ω => (F ω,Z ω)) (fun _ => P) P := by
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _
    (tendstoInDistribution_const (hF.prodMk hZ).aemeasurable)
  · apply tendstoInMeasure_iff_norm.mpr
    intro ε hε
    have h := tendstoInMeasure_iff_norm.mp herror ε hε
    simpa only [Pi.sub_apply,Pi.zero_apply,Prod.fst_zero,Prod.snd_zero,Prod.fst_sub,Prod.snd_sub,sub_zero,Prod.norm_def,
      sub_self,norm_zero,max_eq_right (norm_nonneg _),norm_sub_rev] using h
  · intro n
    exact (hF.prodMk (hY n)).aemeasurable

end BarrierManuscript
#print axioms BarrierManuscript.fixed_pair_weak_limit
