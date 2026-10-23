import ManuscriptFrozenStockApproximation
import ManuscriptGeometricWeakLimit
import ManuscriptBrownianScaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace BarrierManuscript

theorem scaled_capped_time_finite (θ : ℝ) (hp : 0 < θ) (t : HalfClosedTime) :
    linearClock θ hp (min (realTimeClamp 1) t) < ⊤ := by
  have h1 : linearClock θ hp (realTimeClamp 1)=realTimeClamp θ := by
    simpa using linear_clock_finite θ hp 1 zero_le_one
  exact ((linearClock θ hp).monotone (min_le_left _ _)).trans_lt (h1 ▸ halfTimeClamp_finite θ)

noncomputable def normalizedStockStoppedPath {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : StockSDEData P)
    (θ : ℝ) (hp : 0 < θ) (ω : Ω) : C(HalfClosedTime,ℝ) :=
  ⟨fun t => (D.S (linearClock θ hp (min (realTimeClamp 1) t)) ω/D.S₀-1)/Real.sqrt (θ*D.v₀),by
    have ht : Continuous (fun t : HalfClosedTime => linearClock θ hp (min (realTimeClamp 1) t)) :=
      (linear_clock_continuous θ hp).comp (continuous_const.min continuous_id)
    have hstock : Continuous (fun t : HalfClosedTime => D.S (linearClock θ hp (min (realTimeClamp 1) t)) ω) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact ContinuousAt.comp (g := fun r : HalfClosedTime => D.S r ω)
        (f := fun s : HalfClosedTime => linearClock θ hp (min (realTimeClamp 1) s))
        (D.hSc ω _ (scaled_capped_time_finite θ hp t)) ht.continuousAt
    exact ((hstock.div_const D.S₀).sub continuous_const).div_const _⟩

theorem normalizedStockStoppedPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P) (θ : ℝ) (hp : 0 < θ) :
    Measurable (normalizedStockStoppedPath D θ hp) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((((D.hSa _ (scaled_capped_time_finite θ hp t)).mono (D.B.le _) le_rfl).div_const D.S₀).sub_const 1).div_const _

/-- The frozen approximation in the uniform path norm, ready for joint
continuous-mapping arguments involving the endpoint and running maximum. -/
theorem stock_path_difference_inMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : StockSDEData P)
    (θ : ℕ → ℝ) (hp : ∀ n, 0 < θ n) (hθ : Tendsto θ atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => normalizedStockStoppedPath D (θ n) (hp n) ω-
      brownianStoppedPath (scaledBrownian D.B (θ n) (hp n)) 1 zero_le_one ω)
      atTop (fun _ => 0) := by
  let f := fun n ω => normalizedStockStoppedPath D (θ n) (hp n) ω-
    brownianStoppedPath (scaledBrownian D.B (θ n) (hp n)) 1 zero_le_one ω
  have hv : 0 < Real.sqrt D.v₀ := Real.sqrt_pos.mpr D.hv₀
  have he (n : ℕ) (ω : Ω) : (⨆ t : HalfClosedTime,
      |frozenStockError D (linearClock (θ n) (hp n) (min (realTimeClamp 1) t)) ω/Real.sqrt (θ n)|) =
      Real.sqrt D.v₀*‖f n ω‖ := by
    have hg : (Real.sqrt D.v₀) • f n ω =
        (⟨fun t => frozenStockError D (linearClock (θ n) (hp n) (min (realTimeClamp 1) t)) ω/Real.sqrt (θ n),
          by
            have hh : (fun t => frozenStockError D (linearClock (θ n) (hp n) (min (realTimeClamp 1) t)) ω/Real.sqrt (θ n)) =
                fun t => Real.sqrt D.v₀*(f n ω) t := by
              funext t
              dsimp only [f,normalizedStockStoppedPath,brownianStoppedPath,ContinuousMap.coe_mk,ContinuousMap.sub_apply,
                scaledBrownian,frozenStockError]
              rw [Real.sqrt_mul (hp n).le]
              field_simp
              <;> ring
            rw [hh]
            exact continuous_const.mul (f n ω).continuous⟩ : C(HalfClosedTime,ℝ)) := by
      ext t
      dsimp only [f,normalizedStockStoppedPath,brownianStoppedPath,ContinuousMap.coe_mk,ContinuousMap.sub_apply,
        ContinuousMap.smul_apply,smul_eq_mul,scaledBrownian,frozenStockError]
      rw [Real.sqrt_mul (hp n).le]
      field_simp
      <;> ring
    have hh := congrArg norm hg
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hv] at hh
    conv_rhs at hh => rw [ContinuousMap.norm_eq_iSup_norm]
    simpa only [ContinuousMap.coe_mk,Real.norm_eq_abs] using hh.symm
  apply tendstoInMeasure_iff_norm.mpr
  intro ε hε
  have h := stock_frozen_brownian_approximation P D θ hp hθ (Real.sqrt D.v₀*ε) (mul_pos hv hε)
  simp_rw [he] at h
  simpa only [sub_zero,mul_le_mul_iff_right₀ hv] using h

end BarrierManuscript
#print axioms BarrierManuscript.scaled_capped_time_finite
#print axioms BarrierManuscript.normalizedStockStoppedPath_measurable
#print axioms BarrierManuscript.stock_path_difference_inMeasure
