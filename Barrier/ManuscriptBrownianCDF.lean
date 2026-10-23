import ManuscriptBrownianEndpoint
import ManuscriptPutTransform

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
open Asakura.FullAudit Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript
attribute [local instance] Classical.propDecidable

theorem brownian_barrier_endpoint_cdf {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k : ℝ) (hb : 0 < b) (hk : k < b) :
    P.real {ω | brownianBarrierEndpoint B b ω < k} = normalCDF k-normalCDF (k-2*b) :=
  killed_put_identifies_cdf P (brownianBarrierEndpoint B b)
    (brownian_barrier_endpoint_measurable P B b) (brownian_barrier_endpoint_integrable P B b)
    b k hk (brownian_barrier_endpoint_noatom P B b k hk)
    (fun a ha => brownian_killed_put P B b a hb ha)

theorem lower_tail_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hm : Measurable X)
    (b : ℝ) (k : ℕ → ℝ) (hk : ∀ n, k n < b) (hlim : Tendsto k atTop (𝓝 b)) :
    Tendsto (fun n => P.real {ω | X ω < k n}) atTop (𝓝 (P.real {ω | X ω < b})) := by
  let f := fun n ω => if X ω < k n then (1:ℝ) else 0
  let g := fun ω => if X ω < b then (1:ℝ) else 0
  have hf n : AEStronglyMeasurable (f n) P :=
    (measurable_const.ite (measurableSet_lt hm measurable_const) measurable_const).aestronglyMeasurable
  have hbnd n : ∀ᵐ ω ∂P, ‖f n ω‖ ≤ (1:ℝ) := ae_of_all _ fun ω => by simp [f]; split_ifs <;> norm_num
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    apply ae_of_all
    intro ω
    by_cases h : X ω < b
    · apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually (lt_mem_nhds h)] with n hn
      simp [f,g,h,hn]
    · have hall n : ¬X ω < k n := not_lt.mpr ((hk n).le.trans (le_of_not_gt h))
      simp only [f,g,ite_eq_right h,ite_eq_right (hall _)]
      exact tendsto_const_nhds
  have hi := tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ)) hf (integrable_const 1) hbnd hconv
  have hformula (a : ℝ) : (∫ ω, if X ω < a then (1:ℝ) else 0 ∂P) = P.real {ω | X ω < a} := by
    change (∫ ω, {ω | X ω < a}.indicator (fun _ => (1:ℝ)) ω ∂P) = _
    rw [integral_indicator_const _ (measurableSet_lt hm measurable_const)]
    simp
  simpa only [f,g,hformula] using hi

/-- The probability of the stopped Brownian endpoint being strictly below
the barrier, obtained by taking strikes up to the barrier in the put law. -/
theorem brownian_strict_survival {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1) (b : ℝ) (hb : 0 < b) :
    P.real {ω | brownianBarrierEndpoint B b ω < b} = 2*normalCDF b-1 := by
  obtain ⟨k,_,hk,hklim⟩ := exists_seq_strictMono_tendsto b
  have h₁ := lower_tail_limit P _ (brownian_barrier_endpoint_measurable P B b) b k hk hklim
  have h₂ := (normalCDF_contDiff.continuous.tendsto b |>.comp hklim).sub
    (normalCDF_contDiff.continuous.tendsto (b-2*b) |>.comp (hklim.sub_const (2*b)))
  have he n := brownian_barrier_endpoint_cdf P B b (k n) hb (hk n)
  have h₂' : Tendsto (fun n => P.real {ω | brownianBarrierEndpoint B b ω < k n}) atTop
      (𝓝 (normalCDF b-normalCDF (b-2*b))) := by simpa only [he,Function.comp_def] using h₂
  have hh := tendsto_nhds_unique h₁ h₂'
  rw [show b-2*b = -b by ring,normalCDF_neg] at hh
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.brownian_barrier_endpoint_cdf
#print axioms BarrierManuscript.lower_tail_limit
#print axioms BarrierManuscript.brownian_strict_survival
