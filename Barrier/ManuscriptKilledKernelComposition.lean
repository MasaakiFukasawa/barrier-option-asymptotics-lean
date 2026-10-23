import ManuscriptIndependentKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

/-- Composition of two killed endpoint kernels follows from independence of
the endpoint/maximum pairs. Only the marginal killed kernels are inputs. -/
theorem killed_kernel_composition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → ℝ × ℝ)
    (hA : Measurable A) (hB : Measurable B) (hind : IndepFun A B P)
    (b : ℝ) (k₁ : ℝ → ℝ) (k₂ : ℝ → ℝ → ℝ)
    (hk₁ : ∀ q : ℝ → ℝ, Measurable q →
      (∫ ω, if (A ω).2 ≤ b then q (A ω).1 else 0 ∂P)=∫ x in Iio b, q x*k₁ x)
    (hk₂ : ∀ c : ℝ, 0 < c → ∀ q : ℝ → ℝ, Measurable q →
      (∫ ω, if (B ω).2 ≤ c then q (B ω).1 else 0 ∂P)=∫ x in Iio c, q x*k₂ c x)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ q, |f q| ≤ C) :
    (∫ ω, if (A ω).2 ≤ b ∧ (B ω).2 ≤ b-(A ω).1
      then f ((A ω).1,(A ω).1+(B ω).1) else 0 ∂P) =
      ∫ x in Iio b, (∫ y in Iio (b-x), f (x,x+y)*k₂ (b-x) y)*k₁ x := by
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun q =>
    if q.1.2 ≤ b then if q.2.2 ≤ b-q.1.1 then f (q.1.1,q.1.1+q.2.1) else 0 else 0
  have hG : Measurable G := by
    apply Measurable.ite (measurableSet_le measurable_fst.snd measurable_const)
    · exact Measurable.ite (measurableSet_le measurable_snd.snd (measurable_const.sub measurable_fst.fst))
        (hf.comp (measurable_fst.fst.prodMk (measurable_fst.fst.add measurable_snd.fst))) measurable_const
    · exact measurable_const
  have hC : 0 ≤ C := (abs_nonneg (f (0,0))).trans (hb (0,0))
  have hGb q : |G q| ≤ C := by dsimp only [G]; split_ifs <;> simp_all only [abs_zero]
  let g : ℝ × Ω → ℝ := fun p => if (B p.2).2 ≤ b-p.1 then f (p.1,p.1+(B p.2).1) else 0
  have hg : Measurable g :=
    Measurable.ite (measurableSet_le (hB.snd.comp measurable_snd) (measurable_const.sub measurable_fst))
      (hf.comp (measurable_fst.prodMk (measurable_fst.add (hB.fst.comp measurable_snd)))) measurable_const
  let q := fun x => ∫ ω, g (x,ω) ∂P
  have hq : Measurable q := hg.stronglyMeasurable.integral_prod_right'.measurable
  have hi := independent_kernel_integral P A B hA hB hind G hG C hGb
  have hleft ω : G (A ω,B ω) =
      if (A ω).2 ≤ b ∧ (B ω).2 ≤ b-(A ω).1 then f ((A ω).1,(A ω).1+(B ω).1) else 0 := by
    dsimp only [G]
    split_ifs <;> simp_all
  have hright ω : (∫ ω', G (A ω,B ω') ∂P)=if (A ω).2 ≤ b then q (A ω).1 else 0 := by
    by_cases h : (A ω).2 ≤ b <;> simp only [G,h,ite_true,ite_false,q,g,integral_zero]
  simp_rw [hleft,hright] at hi
  rw [hi,hk₁ q hq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
  congr 1
  exact hk₂ (b-x) (sub_pos.mpr hx) (fun y => f (x,x+y))
    (hf.comp (measurable_const.prodMk (measurable_const.add measurable_id)))

end BarrierManuscript
#print axioms BarrierManuscript.killed_kernel_composition
