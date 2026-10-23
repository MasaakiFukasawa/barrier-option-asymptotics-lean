import ManuscriptBrownianSegments
import ManuscriptMaximumEncoding
import ManuscriptClockComposition
import Chapter7NaturalBrownianSystem

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem naturalBrownianSystem_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ω : Ω) :
    (naturalBrownianSystem P W hW hm hc).W 0 (realTimeClamp (t:ℝ)) ω=W t ω := by
  change W (halfTimeReal (realTimeClamp (t:ℝ))) ω=W t ω
  congr 1
  apply NNReal.eq
  exact changed_time_real (t:ℝ) t.property

theorem rawPrefix_brownian_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ht : 0 < t) (ω : Ω) :
    let B := scaledBrownian (naturalBrownianSystem P W hW hm hc) (t:ℝ) (by exact_mod_cast ht)
    (W t ω,pathMaximum (rawPrefixPath W hc t ω)) =
      (Real.sqrt (t:ℝ)*B.W 0 (realTimeClamp 1) ω,Real.sqrt (t:ℝ)*brownianMaximum B ω) := by
  dsimp only
  have htr : (0:ℝ) < (t:ℝ) := by exact_mod_cast ht
  let B := scaledBrownian (naturalBrownianSystem P W hW hm hc) (t:ℝ) (by exact_mod_cast ht)
  let p := pathRestriction 1 (brownianContinuousPath B ω)
  have he (r : Icc (0:ℝ≥0) 1) : W (t*r.val) ω=Real.sqrt (t:ℝ)*p r := by
    change W (t*r.val) ω=Real.sqrt (t:ℝ)*B.W 0 (realTimeClamp (r.val:ℝ)) ω
    rw [scaledBrownian_W P (naturalBrownianSystem P W hW hm hc) (t:ℝ) (r.val:ℝ) htr r.val.property ω,
      mul_div_cancel₀ _ (Real.sqrt_pos.mpr htr).ne']
    exact (naturalBrownianSystem_finite P W hW hm hc (t*r.val) ω).symm
  apply Prod.ext
  · have h1 := he ⟨1,by simp⟩
    change W (t*1) ω=Real.sqrt (t:ℝ)*B.W 0 (realTimeClamp 1) ω at h1
    simpa only [mul_one] using h1
  · change pathMaximum (rawPrefixPath W hc t ω)=Real.sqrt (t:ℝ)*brownianMaximum B ω
    have hpath : rawPrefixPath W hc t ω = (⟨fun r => Real.sqrt (t:ℝ)*p r,p.continuous.const_mul _⟩ : C(Icc (0:ℝ≥0) 1,ℝ)) := by
      ext r
      exact he r
    rw [hpath,pathMaximum_mul_pos p _ (Real.sqrt_pos.mpr htr)]
    rw [show pathMaximum p=brownianMaximum B ω from brownian_maximum_encoding P B ω]

end BarrierManuscript
#print axioms BarrierManuscript.naturalBrownianSystem_finite
#print axioms BarrierManuscript.rawPrefix_brownian_scaling
