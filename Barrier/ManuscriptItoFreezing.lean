import ManuscriptFrozenStockApproximation

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter7 Asakura.Chapter8
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def itoFrozenError {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (N : HalfClosedTime → Ω → ℝ) (a : ℝ) : HalfClosedTime → Ω → ℝ :=
  fun t ω => -a*B.W 0 t ω+N t ω

noncomputable def itoFrozenIntegrand {Ω : Type*}
    (G : HalfClosedTime → Ω → ℝ) (a : ℝ) : HalfClosedTime → Ω → ℝ :=
  fun t ω => -a+G t ω

theorem ito_frozen_error_bracket {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G N : HalfClosedTime → Ω → ℝ)
    (hGa : ∀ t,t < ⊤ → Measurable[B.F t] (G t))
    (hGc : ∀ ω t,t < ⊤ → ContinuousAt (fun s => G s ω) t)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => G (realTimeClamp z.2) z.1) N)
    (a : ℝ) :
    LocalMProcessWitness P B.F (itoFrozenError B N a) ∧
    ∃ C : HalfClosedTime → Ω → ℝ,
      LocalCovarianceWitness P B.F (itoFrozenError B N a) (itoFrozenError B N a) C ∧
      ∀ᵐ ω ∂P,∀ r : ℝ,0 ≤ r → C (realTimeClamp r) ω=
        ∫ s in (0:ℝ)..r,(itoFrozenIntegrand G a (realTimeClamp s) ω)^2 := by
  have hM : LocalMProcessWitness P B.F (itoFrozenError B N a) :=
    ((B.martingale 0).smul P B.F (-a)).add P B.F B.mono B.le hN
  have hId := identity_ito_integral P (by simp : (0:EReal)<⊤) B.F B.mono B.le B.null (B.W 0) (B.martingale 0)
  have hI : ItoCovarianceFormula P B.F (B.W 0)
      (fun z => itoFrozenIntegrand G a (realTimeClamp z.2) z.1) (itoFrozenError B N a) := by
    unfold itoFrozenError
    simpa only [mul_one,itoFrozenIntegrand] using
      hId.add_smul P B.F B.mono B.le (B.W 0) (B.W 0) N (fun _ => 1)
        (fun z => G (realTimeClamp z.2) z.1) hNI (-a)
  obtain ⟨_,C,_,hC,_,he⟩ := brownian_ito_cross_and_self_density P B.F B.mono B.le B.null
    (B.W 0) (itoFrozenError B N a) (B.C 0 0) (itoFrozenIntegrand G a)
    (B.martingale 0) hM (B.cov 0 0) (B.diagonal_clock 0)
    (fun t ht => measurable_const.add (hGa t ht))
    (fun ω t ht => continuousAt_const.add (hGc ω t ht)) hI
  exact ⟨hM,C,hC,he⟩

/-- Freezing any continuous adapted Brownian integrand at its deterministic
initial value gives o_P(sqrt(t)), uniformly over the small time interval.
No bound on conditional densities or extra independence is imposed. -/
theorem ito_frozen_brownian_approximation {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (G N : HalfClosedTime → Ω → ℝ)
    (hGa : ∀ t,t < ⊤ → Measurable[B.F t] (G t))
    (hGc : ∀ ω t,t < ⊤ → ContinuousAt (fun s => G s ω) t)
    (hN : LocalMProcessWitness P B.F N)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => G (realTimeClamp z.2) z.1) N)
    (a : ℝ) (hG0 : ∀ᵐ ω ∂P,G (realTimeClamp 0) ω=a)
    (θ : ℕ → ℝ) (hp : ∀ n,0 < θ n) (hθ : Tendsto θ atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ε ≤ ⨆ t : HalfClosedTime,
      |itoFrozenError B N a (linearClock (θ n) (hp n) (min (realTimeClamp 1) t)) ω/Real.sqrt (θ n)|})
      atTop (𝓝 0) := by
  obtain ⟨hM,C,hC,hbr⟩ := ito_frozen_error_bracket P B G N hGa hGc hN hNI a
  let F := fun n t => B.F (linearClock (θ n) (hp n) t)
  let X := fun n t ω => itoFrozenError B N a (linearClock (θ n) (hp n) t) ω/Real.sqrt (θ n)
  let A := fun n t ω => C (linearClock (θ n) (hp n) t) ω/θ n
  have hres n := long_time_martingale_rescaling P B.F (itoFrozenError B N a) C hM hC (θ n) 1 (hp n) zero_lt_one
  simp only [mul_one] at hres
  have hg : ∀ᵐ ω ∂P, Continuous (fun r : ℝ => itoFrozenIntegrand G a (realTimeClamp r) ω) :=
    ae_of_all _ fun ω => continuous_const.add (continuous_real_path G hGc ω)
  have h0 : ∀ᵐ ω ∂P, itoFrozenIntegrand G a (realTimeClamp 0) ω=0 := by
    filter_upwards [hG0] with ω hω
    simp only [itoFrozenIntegrand,hω,neg_add_cancel]
  have hq := rescaled_zero_bracket P B.F B.mono B.le (itoFrozenError B N a) C hM hC
    (fun ω r => itoFrozenIntegrand G a (realTimeClamp r) ω) hg h0 hbr θ hp hθ
  have htail (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun n => P {ω | δ ≤ A n (realTimeClamp 1) ω}) atTop (𝓝 0) := by
    have he n ω : A n (realTimeClamp 1) ω=C (realTimeClamp (θ n)) ω/θ n := by
      dsimp only [A]
      rw [linear_clock_finite _ _ 1 zero_le_one,mul_one]
    simp_rw [he]
    have hn := (tendstoInMeasure_iff_norm.mp hq) δ hδ
    simp only [sub_zero,Real.norm_eq_abs] at hn
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn (fun _ => bot_le)
      (fun n => measure_mono ?_)
    intro ω hω
    change δ ≤ C (realTimeClamp (θ n)) ω/θ n at hω
    exact hω.trans (le_abs_self _)
  exact varying_local_martingale_zero P F
    (fun n => B.mono.comp (linearClock (θ n) (hp n)).monotone)
    (fun _ _ => B.le _) (fun _ _ E hm hz => B.null _ E hm hz)
    X A (fun n => (hres n).1) (fun n => (hres n).2) htail ε hε

end BarrierManuscript
#print axioms BarrierManuscript.ito_frozen_error_bracket
#print axioms BarrierManuscript.ito_frozen_brownian_approximation
