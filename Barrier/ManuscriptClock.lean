import ManuscriptGaussianBounds

open MeasureTheory Set Filter
open scoped Topology

namespace BarrierManuscript

noncomputable def remainingVol (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (∫ s in u..1, v s)

/-- The normalized variance over [0,1] includes a factor 1/θ after the
change of variables r=θu. -/
theorem normalized_variance_clock (v : ℝ → ℝ) (v₀ θ : ℝ) (hθ : θ ≠ 0) :
    (∫ u in (0:ℝ)..1, v (θ*u)/v₀) =
      (∫ r in (0:ℝ)..θ, v r)/(v₀*θ) := by
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_mul_left v hθ]
  simp only [mul_zero, mul_one, smul_eq_mul]
  ring

theorem remainingVol_bounds (v : ℝ → ℝ) (u c C : ℝ)
    (hu : u ≤ 1) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hi : IntervalIntegrable v volume u 1)
    (hlo : ∀ s ∈ Icc u 1, c^2 ≤ v s)
    (hup : ∀ s ∈ Icc u 1, v s ≤ C^2) :
    c*Real.sqrt (1-u) ≤ remainingVol v u ∧
      remainingVol v u ≤ C*Real.sqrt (1-u) := by
  have hl := intervalIntegral.integral_mono_on hu
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c^2) volume u 1) hi hlo
  have hh := intervalIntegral.integral_mono_on hu hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C^2) volume u 1) hup
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hl hh
  constructor
  · have h := Real.sqrt_le_sqrt hl
    rw [Real.sqrt_mul (sub_nonneg.mpr hu), Real.sqrt_sq hc] at h
    simpa only [remainingVol, mul_comm] using h
  · have h := Real.sqrt_le_sqrt hh
    rw [Real.sqrt_mul (sub_nonneg.mpr hu), Real.sqrt_sq hC] at h
    simpa only [remainingVol, mul_comm] using h

/-- A derivative of the actual variance clock, not an assumed Greek identity.
Continuity is only required at the time where this classical derivative is used. -/
theorem remainingVol_derivative (v : ℝ → ℝ) (u : ℝ)
    (hi : IntervalIntegrable v volume u 1)
    (hm : StronglyMeasurableAtFilter v (𝓝 u)) (hc : ContinuousAt v u)
    (hp : 0 < ∫ s in u..1, v s) :
    HasDerivAt (remainingVol v) (-v u/(2*remainingVol v u)) u := by
  have h := (Real.hasDerivAt_sqrt hp.ne').comp u
    (intervalIntegral.integral_hasDerivAt_left hi hm hc)
  convert h using 1
  · rfl
  · dsimp [remainingVol]; ring

theorem remainingVol_pde (v : ℝ → ℝ) (b k x u : ℝ)
    (hi : IntervalIntegrable v volume u 1)
    (hm : StronglyMeasurableAtFilter v (𝓝 u)) (hc : ContinuousAt v u)
    (hp : 0 < ∫ s in u..1, v s) :
    deriv (fun t => killedPut b k x (remainingVol v t)) u + v u/2 *
      deriv (fun y => deriv (fun z => killedPut b k z (remainingVol v u)) y) x = 0 := by
  have hw : remainingVol v u ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  apply killedPut_pde b k x u (v u) _ (remainingVol v) hw
    (remainingVol_derivative v u hi hm hc hp)
  field_simp

/-- Quantitative form of the forward-variance integral estimate in the
regular-model discussion. It allows an O(t) error in the variance curve. -/
theorem integrated_variance_error (v : ℝ → ℝ) (v₀ C θ : ℝ)
    (hθ : 0 ≤ θ) (hC : 0 ≤ C) (hi : IntervalIntegrable v volume 0 θ)
    (hb : ∀ s ∈ Icc 0 θ, |v s-v₀| ≤ C*s) :
    |(∫ s in 0..θ, v s)-v₀*θ| ≤ C*θ^2 := by
  have he : (∫ s in 0..θ, v s)-v₀*θ = ∫ s in 0..θ, v s-v₀ := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp [mul_comm]
  rw [he]
  have h := intervalIntegral.norm_integral_le_of_norm_le hθ
    (Filter.Eventually.of_forall (fun s hs => show ‖v s-v₀‖ ≤ C*θ from by
      rw [Real.norm_eq_abs]
      exact (hb s ⟨hs.1.le,hs.2⟩).trans (mul_le_mul_of_nonneg_left hs.2 hC)))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C*θ) volume 0 θ)
  simpa [Real.norm_eq_abs, pow_two, mul_assoc, mul_comm, mul_left_comm] using h

theorem sqrt_difference_bound (a b E : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (he : |a-b| ≤ E) : |Real.sqrt a-Real.sqrt b| ≤ E/Real.sqrt b := by
  have hbp : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hid : |Real.sqrt a-Real.sqrt b| *(Real.sqrt a+Real.sqrt b) = |a-b| := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le]
  apply (le_div_iff₀ hbp).mpr
  calc
    _ ≤ |Real.sqrt a-Real.sqrt b| *(Real.sqrt a+Real.sqrt b) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg a]) (abs_nonneg _)
    _ = |a-b| := hid
    _ ≤ E := he

/-- Explicit total-volatility error underlying the spot-variance replacement.
The right hand side is a constant times θ^(3/2) when v₀ is fixed. -/
theorem volatility_freezing_bound (v : ℝ → ℝ) (v₀ C θ : ℝ)
    (hθ : 0 < θ) (hv : 0 < v₀) (hC : 0 ≤ C)
    (hi : IntervalIntegrable v volume 0 θ)
    (hpos : 0 ≤ ∫ s in 0..θ, v s)
    (hb : ∀ s ∈ Icc 0 θ, |v s-v₀| ≤ C*s) :
    |Real.sqrt (∫ s in 0..θ, v s)-Real.sqrt (v₀*θ)| ≤
      C*θ^2/Real.sqrt (v₀*θ) :=
  sqrt_difference_bound _ _ _ hpos (mul_pos hv hθ)
    (integrated_variance_error v v₀ C θ hθ.le hC hi hb)

end BarrierManuscript

#print axioms BarrierManuscript.remainingVol_bounds
#print axioms BarrierManuscript.normalized_variance_clock
#print axioms BarrierManuscript.remainingVol_derivative
#print axioms BarrierManuscript.remainingVol_pde
#print axioms BarrierManuscript.integrated_variance_error
#print axioms BarrierManuscript.sqrt_difference_bound
#print axioms BarrierManuscript.volatility_freezing_bound
