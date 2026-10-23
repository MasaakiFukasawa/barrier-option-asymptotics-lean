import ManuscriptBrownianSegments

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace BarrierManuscript

theorem rawPrefix_max_le_iff {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t : ℝ≥0) (ht : 0 < t) (b : ℝ) (ω : Ω) :
    pathMaximum (rawPrefixPath W hc t ω) ≤ b ↔ ∀ s : ℝ≥0, s ≤ t → W s ω ≤ b := by
  constructor
  · intro h s hs
    let r : Icc (0:ℝ≥0) 1 := ⟨s/t,by positivity,(div_le_one ht).mpr hs⟩
    have hr : (rawPrefixPath W hc t ω) r ≤ pathMaximum (rawPrefixPath W hc t ω) :=
      le_csSup (path_range_bddAbove _) (mem_range_self r)
    have he : t*r.val=s := by dsimp only [r]; field_simp
    change W (t*r.val) ω ≤ _ at hr
    rw [he] at hr
    exact hr.trans h
  · intro h
    apply csSup_le (range_nonempty _)
    rintro y ⟨r,rfl⟩
    exact h (t*r.val) (mul_le_of_le_one_right (show (0:ℝ≥0) ≤ t from bot_le) r.property.2)

/-- Exact decomposition of survival into past and shifted-future survival. -/
theorem raw_survival_split {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => W t ω)) (t d : ℝ≥0) (ht : 0 < t) (hd : 0 < d)
    (b : ℝ) (ω : Ω) :
    let Z := fun s ω => W (t+s) ω-W t ω
    let hZ := fun ω => ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    pathMaximum (rawPrefixPath W hc (t+d) ω) ≤ b ↔
      pathMaximum (rawPrefixPath W hc t ω) ≤ b ∧
        pathMaximum (rawPrefixPath Z hZ d ω) ≤ b-W t ω := by
  dsimp only
  rw [rawPrefix_max_le_iff W hc (t+d) (add_pos ht hd),rawPrefix_max_le_iff W hc t ht,
    rawPrefix_max_le_iff _ _ d hd]
  constructor
  · intro h
    constructor
    · intro s hs
      exact h s (hs.trans (le_add_of_nonneg_right (show (0:ℝ≥0) ≤ d from bot_le)))
    · intro s hs
      have hh := h (t+s) (by simpa only [add_comm] using add_le_add_left hs t)
      linarith
  · rintro ⟨h1,h2⟩ s hs
    by_cases hst : s ≤ t
    · exact h1 s hst
    · have hts : t ≤ s := le_of_not_ge hst
      have hh := h2 (s-t) (tsub_le_iff_right.mpr (by simpa only [add_comm] using hs))
      rw [add_tsub_cancel_of_le hts] at hh
      linarith

end BarrierManuscript
#print axioms BarrierManuscript.rawPrefix_max_le_iff
#print axioms BarrierManuscript.raw_survival_split
