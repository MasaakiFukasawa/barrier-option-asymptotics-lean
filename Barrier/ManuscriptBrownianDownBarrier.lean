import ManuscriptBrownianPutGeneral

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A lower-barrier call is the upper-barrier put of the reflected Brownian
stock. This is an equality for continuously monitored payoff expectations. -/
theorem brownian_down_out_call {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hm : ∀ t, Measurable (W t))
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ht : 0 < t)
    (b k x : ℝ) (hx : b < x) (hk : b ≤ k) :
    (∫ ω in {ω | ∀ s : ℝ≥0, s ≤ t → b ≤ x+W s ω},
      max (x+W t ω-k) 0 ∂P) =
      call k x (Real.sqrt (t:ℝ))-call k (2*b-x) (Real.sqrt (t:ℝ)) := by
  let Z : ℝ≥0 → Ω → ℝ := -W
  have hZm : ∀ s, Measurable (Z s) := fun s => (hm s).neg
  have hZc : ∀ ω, Continuous (fun s => Z s ω) := fun ω => (hc ω).neg
  have h := brownian_killed_put_general P Z hW.neg hZm hZc t ht (-b) (-k) (-x)
    (neg_lt_neg hx) (neg_le_neg hk)
  have hset : {ω | pathMaximum (rawPrefixPath Z hZc t ω) ≤ -b- -x} =
      {ω | ∀ s : ℝ≥0, s ≤ t → b ≤ x+W s ω} := by
    ext ω
    rw [mem_setOf_eq, rawPrefix_max_le_iff Z hZc t ht]
    change (∀ s : ℝ≥0, s ≤ t → -W s ω ≤ -b- -x) ↔ _
    constructor <;> intro h s hs <;> have hh := h s hs <;> linarith
  rw [hset] at h
  rw [doc_uop_reflection]
  convert h using 1
  congr 1
  funext ω
  dsimp only [Z, Pi.neg_apply]
  congr 1
  ring

end BarrierManuscript
#print axioms BarrierManuscript.brownian_down_out_call
