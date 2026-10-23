import ManuscriptStockCLT
import ManuscriptSurvivalKernel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The pricing maximum equals the functional-CLT maximum whenever the two
process versions agree through maturity. Values after maturity are irrelevant. -/
theorem stock_maximum_encoding {Ω : Type*}
    (N X : HalfClosedTime → Ω → ℝ)
    (hN : ∀ ω t, t < ⊤ → ContinuousAt (fun s => N s ω) t)
    (hX : ∀ ω, Continuous (fun s => X s ω))
    (hagree : ∀ t, t ≤ realTimeClamp 1 → ∀ ω, X t ω = N t ω) (ω : Ω) :
    pathMaximum (pathRestriction 1 (localContinuousPath N hN ω)) =
      prefixMaximum X hX (realTimeClamp 1) ω := by
  unfold pathMaximum prefixMaximum
  congr 1
  ext y
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨realTimeClamp (r.val : ℝ),?_⟩
    change X (min (realTimeClamp 1) (realTimeClamp (r.val : ℝ))) ω = y
    have ht := real_time_clamp_mono (T := (⊤:EReal)) (show (r.val : ℝ) ≤ 1 from r.property.2)
    rw [min_eq_right ht,hagree _ ht]
    exact hr
  · rintro ⟨t,ht⟩
    let r := finitePrefixTime 1 (by norm_num) t
    let n : ℝ≥0 := ⟨r.val,r.property.1⟩
    refine ⟨⟨n,⟨bot_le,show n ≤ 1 from r.property.2⟩⟩,?_⟩
    change N (realTimeClamp r.val) ω = y
    rw [finite_prefix_time_clamp 1 (by norm_num) le_top,← hagree _ (min_le_left _ _)]
    exact ht

theorem stock_endpoint_maximum_encoding {Ω : Type*}
    (N X : HalfClosedTime → Ω → ℝ)
    (hN : ∀ ω t, t < ⊤ → ContinuousAt (fun s => N s ω) t)
    (hX : ∀ ω, Continuous (fun s => X s ω))
    (hagree : ∀ t, t ≤ realTimeClamp 1 → ∀ ω, X t ω = N t ω) (ω : Ω) :
    endpointMaximum (⟨1,by simp⟩ : Icc (0:ℝ≥0) 1)
      (pathRestriction 1 (localContinuousPath N hN ω)) =
      (X (realTimeClamp 1) ω,prefixMaximum X hX (realTimeClamp 1) ω) := by
  apply Prod.ext
  · exact (hagree _ le_rfl ω).symm
  · exact stock_maximum_encoding N X hN hX hagree ω

end BarrierManuscript
#print axioms BarrierManuscript.stock_maximum_encoding
#print axioms BarrierManuscript.stock_endpoint_maximum_encoding
