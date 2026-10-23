import ManuscriptControl

open MeasureTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- A continuous path starting below the barrier stays below it after stopping
at its first hit. This does not require a probabilistic regularity assumption. -/
theorem stopped_path_below {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (S : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => S t ω))
    (B : ℝ) (h₀ : ∀ ω, S ⊥ ω < B) (ω : Ω) (t : ClosedTime T) :
    S (min (barrierTime S B ω) t) ω ≤ B := by
  by_contra hn
  have hgt := lt_of_not_ge hn
  let q := min (barrierTime S B ω) t
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc (show (⊥ : ClosedTime T) ≤ q from bot_le)
    (hc ω).continuousOn (show B ∈ Icc (S ⊥ ω) (S q ω) from ⟨(h₀ ω).le,hgt.le⟩)
  have hτ : barrierTime S B ω ≤ r := sInf_le he
  have hrq : r < q := lt_of_le_of_ne hr.2 (by
    intro heq
    have : S q ω = B := by simpa only [heq] using he
    exact (ne_of_gt hgt) this)
  exact (not_lt_of_ge (min_le_left _ _)) (lt_of_le_of_lt hτ hrq)

theorem stopped_path_abs_bound {Ω : Type*} {T : EReal} [Fact (0 ≤ T)]
    (S : ClosedTime T → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => S t ω))
    (B L : ℝ) (h₀ : ∀ ω, S ⊥ ω < B) (hL : ∀ t ω, L ≤ S t ω)
    (ω : Ω) (t : ClosedTime T) :
    |S (min (barrierTime S B ω) t) ω| ≤ max |L| |B| := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le L).trans (hL _ _))
  · exact (stopped_path_below S hc B h₀ ω t).trans ((le_abs_self B).trans (le_max_right _ _))

end BarrierManuscript
#print axioms BarrierManuscript.stopped_path_below
#print axioms BarrierManuscript.stopped_path_abs_bound
