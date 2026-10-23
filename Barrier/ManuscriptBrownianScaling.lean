import ManuscriptStockPathEncoding
import ManuscriptScaledCoefficient

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def scaledBrownian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (u : ℝ) (hu : 0 < u) : BrownianSystem P 1 := by
  have h := long_time_martingale_rescaling P B.F (B.W 0) (B.C 0 0)
    (B.martingale 0) (B.cov 0 0) u 1 hu zero_lt_one
  simp only [mul_one] at h
  exact {
    F := fun t => B.F (linearClock u hu t)
    mono := B.mono.comp (linearClock u hu).monotone
    le := fun _ => B.le _
    null := fun _ E hm hz => B.null _ E hm hz
    W := fun _ t ω => B.W 0 (linearClock u hu t) ω/Real.sqrt u
    C := fun _ _ t ω => B.C 0 0 (linearClock u hu t) ω/u
    martingale := fun _ => h.1
    cov := fun _ _ => h.2
    clock := by
      intro j k ω r hr
      have hj : j=k := Subsingleton.elim _ _
      simp only [hj,ite_true,linear_clock_finite u hu r hr,B.diagonal_clock 0 ω (u*r) (mul_nonneg hu.le hr)]
      field_simp }

theorem scaledBrownian_W {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (u r : ℝ) (hu : 0 < u) (hr : 0 ≤ r) (ω : Ω) :
    (scaledBrownian B u hu).W 0 (realTimeClamp r) ω = B.W 0 (realTimeClamp (u*r)) ω/Real.sqrt u := by
  change B.W 0 (linearClock u hu (realTimeClamp r)) ω/Real.sqrt u = _
  rw [linear_clock_finite u hu r hr]

theorem pathMaximum_div {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : C(K,ℝ)) (c : ℝ) (hc : 0 < c) :
    pathMaximum (⟨fun t => f t/c,f.continuous.div_const c⟩ : C(K,ℝ)) = pathMaximum f/c := by
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    rintro y ⟨t,rfl⟩
    exact div_le_div_of_nonneg_right (le_csSup (path_range_bddAbove f) (mem_range_self t)) hc.le
  · obtain ⟨t,ht⟩ := pathMaximum_attained f
    rw [← ht]
    exact le_csSup (path_range_bddAbove _) (mem_range_self t)

theorem scaledBrownian_maximum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (u : ℝ) (hu : 0 < u) (ω : Ω)
    (hc : ∀ ω, Continuous (fun t => B.W 0 (min (realTimeClamp u) t) ω)) :
    brownianMaximum (scaledBrownian B u hu) ω =
      pathMaximum (⟨fun t => B.W 0 (min (realTimeClamp u) t) ω,hc ω⟩ : C(HalfClosedTime,ℝ))/Real.sqrt u := by
  rw [← pathMaximum_div _ _ (Real.sqrt_pos.mpr hu)]
  unfold brownianMaximum pathMaximum
  congr 1
  ext y
  have h1 : linearClock u hu (realTimeClamp 1)=realTimeClamp u := by
    simpa using linear_clock_finite u hu 1 zero_le_one
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨linearClock u hu t,?_⟩
    change B.W 0 (linearClock u hu (min (realTimeClamp 1) t)) ω/Real.sqrt u=y at ht
    rw [(linearClock u hu).monotone.map_min,h1] at ht
    exact ht
  · rintro ⟨t,ht⟩
    refine ⟨(linearClock u hu).symm t,?_⟩
    change B.W 0 (linearClock u hu (min (realTimeClamp 1) ((linearClock u hu).symm t))) ω/Real.sqrt u=y
    rw [(linearClock u hu).monotone.map_min,h1,(linearClock u hu).apply_symm_apply]
    exact ht

end BarrierManuscript
#print axioms BarrierManuscript.scaledBrownian
#print axioms BarrierManuscript.scaledBrownian_W
#print axioms BarrierManuscript.pathMaximum_div
#print axioms BarrierManuscript.scaledBrownian_maximum
