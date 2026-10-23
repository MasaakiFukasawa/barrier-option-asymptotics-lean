import ManuscriptPathLimit

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem path_triple_difference_bound {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] (t : K) (f g : C(K,ℝ)) (y z : ℝ) :
    ‖(f t,y,pathMaximum f)-(g t,z,pathMaximum g)‖ ≤ max ‖f-g‖ ‖y-z‖ := by
  have he : ‖f t-g t‖ ≤ ‖f-g‖ := (f-g).norm_coe_le_norm t
  have hm : ‖pathMaximum f-pathMaximum g‖ ≤ ‖f-g‖ := by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using pathMaximum_lipschitz.dist_le_mul f g
  simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub]
  exact max_le (he.trans (le_max_left _ _)) (max_le (le_max_right _ _) (hm.trans (le_max_left _ _)))

/-- Uniform path approximation and approximation of the variance coordinate
jointly transfer the endpoint/variance/maximum weak limit. -/
theorem path_triple_weak_transfer {Ω Γ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (P : Measure Ω) (Q : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (t : K) (F G : ℕ → Ω → C(K,ℝ)) (Y Z : ℕ → Ω → ℝ)
    (L : Γ → ℝ × ℝ × ℝ)
    (hweak : TendstoInDistribution (fun n ω => (G n ω t,Z n ω,pathMaximum (G n ω))) atTop L (fun _ => P) Q)
    (hpath : TendstoInMeasure P (fun n ω => F n ω-G n ω) atTop (fun _ => 0))
    (hvar : TendstoInMeasure P (fun n ω => Y n ω-Z n ω) atTop (fun _ => 0))
    (hF : ∀ n, Measurable (F n)) (hY : ∀ n, Measurable (Y n)) :
    TendstoInDistribution (fun n ω => (F n ω t,Y n ω,pathMaximum (F n ω))) atTop L (fun _ => P) Q := by
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ L hweak
  · apply tendstoInMeasure_iff_norm.mpr
    intro ε hε
    have hp := tendstoInMeasure_iff_norm.mp hpath ε hε
    have hv := tendstoInMeasure_iff_norm.mp hvar ε hε
    simp only [sub_zero] at hp hv
    have hu := hp.add hv
    simp only [add_zero] at hu
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => bot_le)
    intro n
    calc
      _ ≤ P ({ω | ε ≤ ‖F n ω-G n ω‖} ∪ {ω | ε ≤ ‖Y n ω-Z n ω‖}) := by
        apply measure_mono
        intro ω hω
        have h : ε ≤ ‖(F n ω t,Y n ω,pathMaximum (F n ω))-(G n ω t,Z n ω,pathMaximum (G n ω))‖ := by
          simpa only [Set.mem_setOf_eq,Pi.sub_apply,Pi.zero_apply,sub_zero] using hω
        exact le_max_iff.mp (h.trans (path_triple_difference_bound t (F n ω) (G n ω) (Y n ω) (Z n ω)))
      _ ≤ _ := measure_union_le _ _
  · intro n
    exact (((continuous_eval_const t).measurable.comp (hF n)).prodMk
      ((hY n).prodMk (pathMaximum_lipschitz.continuous.measurable.comp (hF n)))).aemeasurable

end BarrierManuscript
#print axioms BarrierManuscript.path_triple_difference_bound
#print axioms BarrierManuscript.path_triple_weak_transfer
