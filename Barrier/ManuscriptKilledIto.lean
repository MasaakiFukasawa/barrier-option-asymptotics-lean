import ManuscriptVarianceIto
import ManuscriptPriceDifferential

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace BarrierManuscript

noncomputable def varianceGamma (b k x r : ℝ) : ℝ :=
  (phi ((k-x)/Real.sqrt r)-phi ((k-2*b+x)/Real.sqrt r))/(2*Real.sqrt r)

/-- Ito's formula for the actual killed Bachelier price before zero
remaining variance. The local martingale is constructed, and the two
finite-variation terms use the explicit Gaussian formula. -/
theorem killed_price_ito {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : HalfClosedTime → MeasurableSpace Ω) (hF : Monotone F) (hle : ∀ t, F t ≤ m)
    (hnull : ∀ t E, MeasurableSet[m] E → P E=0 → MeasurableSet[F t] E)
    (X C : HalfClosedTime → Ω → ℝ) (hX : LocalMProcessWitness P F X)
    (hC : LocalCovarianceWitness P F X X C)
    (R : HalfClosedTime → ℝ) (hRc : ∀ t, t < ⊤ → ContinuousAt R t)
    (hRm : AntitoneOn R (Iio ⊤))
    (q : ℝ → ℝ) (hqm : Measurable q)
    (hqi : ∀ r, 0 ≤ r → IntervalIntegrable q volume 0 r)
    (hR : ∀ r : ℝ, 0 ≤ r → R (realTimeClamp r) = R ⊥ + ∫ s in 0..r, q s)
    (G : Ω × ℝ → ℝ) (hGm : ∀ ω, Measurable (fun r => G (ω,r)))
    (hGi : ∀ r, 0 ≤ r → ∀ᵐ ω ∂P, IntervalIntegrable (fun s => G (ω,s)) volume 0 r)
    (hCG : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → C (realTimeClamp r) ω = ∫ s in 0..r, G (ω,s))
    (b k δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hpos : ∀ r ∈ Icc 0 T, δ ≤ R (realTimeClamp r)) :
    ∃ N : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P F N ∧
      ∀ r ∈ Icc 0 T,
        (fun ω => killedPut b k (X (realTimeClamp r) ω) (Real.sqrt (R (realTimeClamp r)))) =ᵐ[P]
          fun ω => killedPut b k (X ⊥ ω) (Real.sqrt (R ⊥)) + N (realTimeClamp r) ω +
            (∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω) (R (realTimeClamp s))*q s) +
            (∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω) (R (realTimeClamp s))*G (ω,s)) := by
  obtain ⟨N,hN,he⟩ := variance_coordinate_ito P F hF hle hnull X C hX hC R hRc hRm
    q hqm hqi hR G hGm hGi hCG (smoothKilledPrice δ b k) (smoothKilledPrice_contDiff δ b k hδ)
  refine ⟨N,hN,?_⟩
  have hz : realTimeClamp (T := (⊤:EReal)) 0 = ⊥ := by
    apply Subtype.ext
    exact real_time_clamp_eq 0 le_rfl le_top
  have hp0 : δ ≤ R ⊥ := by simpa only [hz] using hpos 0 ⟨le_rfl,hT⟩
  intro r hr
  filter_upwards [he r hr.1] with ω hω
  have hvalue s (hs : s ∈ Icc 0 T) :
      smoothKilledPrice δ b k ![X (realTimeClamp s) ω,R (realTimeClamp s)] =
        killedPut b k (X (realTimeClamp s) ω) (Real.sqrt (R (realTimeClamp s))) :=
    smoothKilledPrice_eq δ b k hδ _ (hpos s hs)
  have hzero : smoothKilledPrice δ b k ![X ⊥ ω,R ⊥] =
      killedPut b k (X ⊥ ω) (Real.sqrt (R ⊥)) := smoothKilledPrice_eq δ b k hδ _ hp0
  have hfirst s (hs : s ∈ Icc 0 T) :
      fderiv ℝ (smoothKilledPrice δ b k) ![X (realTimeClamp s) ω,R (realTimeClamp s)] (Pi.single 1 1) =
        varianceGamma b k (X (realTimeClamp s) ω) (R (realTimeClamp s)) :=
    (smoothKilledPrice_first δ b k hδ _ (by
      change δ/2 < R (realTimeClamp s); linarith [hpos s hs])).2
  have hsecond s (hs : s ∈ Icc 0 T) :
      fderiv ℝ (fderiv ℝ (smoothKilledPrice δ b k)) ![X (realTimeClamp s) ω,R (realTimeClamp s)]
          (Pi.single 0 1) (Pi.single 0 1) =
        2*varianceGamma b k (X (realTimeClamp s) ω) (R (realTimeClamp s)) := by
    rw [smoothKilledPrice_heat δ b k hδ _ (by
      change δ/2 < R (realTimeClamp s); linarith [hpos s hs]), hfirst s hs]
  have hi1 : (∫ s in 0..r, fderiv ℝ (smoothKilledPrice δ b k)
      ![X (realTimeClamp s) ω,R (realTimeClamp s)] (Pi.single 1 1)*q s) =
      ∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω) (R (realTimeClamp s))*q s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    dsimp only
    rw [hfirst s ⟨hs.1,hs.2.trans hr.2⟩]
  have hi2 : (∫ s in 0..r, fderiv ℝ (fderiv ℝ (smoothKilledPrice δ b k))
      ![X (realTimeClamp s) ω,R (realTimeClamp s)] (Pi.single 0 1) (Pi.single 0 1)*G (ω,s)) =
      2*(∫ s in 0..r, varianceGamma b k (X (realTimeClamp s) ω) (R (realTimeClamp s))*G (ω,s)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    dsimp only
    rw [hsecond s ⟨hs.1,hs.2.trans hr.2⟩]
    ring
  rw [hvalue r hr,hzero,hi1,hi2] at hω
  linarith

end BarrierManuscript
#print axioms BarrierManuscript.killed_price_ito
