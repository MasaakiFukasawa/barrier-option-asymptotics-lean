import ManuscriptSmoothPrice
import ManuscriptRescaling
import Chapter5MultivariateDensityIto
import Chapter3SemimartingaleFiniteSums

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
open Asakura.FullAudit Asakura.Chapter1Written Asakura.Chapter2Written
open Asakura.Chapter2Complete Asakura.Chapter3Complete Asakura.Chapter4 Asakura.Chapter5 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace BarrierManuscript

/-- Construct Ito's identity in space and remaining variance. The clock is
only an absolutely continuous antitone function; no second time derivative
of the forward variance curve is required. All stochastic integrals are
constructed by the imported multivariate Ito theorem. -/
theorem variance_coordinate_ito {Ω : Type*} [m : MeasurableSpace Ω]
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
    (f : (Fin 2 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ N : HalfClosedTime → Ω → ℝ, LocalMProcessWitness P F N ∧
      ∀ r : ℝ, 0 ≤ r →
        (fun ω => f ![X (realTimeClamp r) ω,R (realTimeClamp r)]) =ᵐ[P]
          fun ω => f ![X ⊥ ω,R ⊥] + N (realTimeClamp r) ω +
            (∫ s in 0..r, fderiv ℝ f ![X (realTimeClamp s) ω,R (realTimeClamp s)] (Pi.single 1 1)*q s) +
            (∫ s in 0..r, fderiv ℝ (fderiv ℝ f) ![X (realTimeClamp s) ω,R (realTimeClamp s)]
              (Pi.single 0 1) (Pi.single 0 1)*G (ω,s))/2 := by
  classical
  have hT : (0:EReal) < ⊤ := by simp
  have hzv : AdaptedLocalVariationWitness F (fun _ (_ : Ω) => (0:ℝ)) :=
    continuous_increasing_adapted_variation hT F hF _
      (fun _ _ => measurable_const) (fun _ => monotoneOn_const) (fun _ _ _ => continuousAt_const)
  have hrn : AdaptedLocalVariationWitness F (fun t (_ : Ω) => -R t) :=
    continuous_increasing_adapted_variation hT F hF _ (fun _ _ => measurable_const)
      (fun _ s hs t ht hst => neg_le_neg (hRm hs ht hst)) (fun _ t ht => (hRc t ht).neg)
  have hrv : AdaptedLocalVariationWitness F (fun t (_ : Ω) => R t) := by
    simpa only [neg_one_mul, neg_neg] using hrn.smul (-1)
  let XX : Fin 2 → HalfClosedTime → Ω → ℝ := ![X,fun t _ => R t]
  let AA : Fin 2 → HalfClosedTime → Ω → ℝ := ![fun _ _ => 0,fun t _ => R t]
  let MM : Fin 2 → HalfClosedTime → Ω → ℝ := ![X,fun _ _ => 0]
  let CC := fun (i j : Fin 2) => if i=0 ∧ j=0 then C else (fun _ _ => 0)
  let BB : Fin 2 → Ω × ℝ → ℝ := ![fun _ => 0,fun z => q z.2]
  let GG := fun (i j : Fin 2) => if i=0 ∧ j=0 then G else (fun _ => 0)
  have hXX i : SemimartingaleDecomposition P F (XX i) (AA i) (MM i) := by
    fin_cases i
    · exact ⟨hzv,hX,hX.path P F,fun _ _ _ => by simp [XX,AA,MM]⟩
    · exact ⟨hrv,zero_local_process P hT F,fun _ t ht => hRc t ht,
        fun _ _ _ => by simp [XX,AA,MM]⟩
  have hzero (M : HalfClosedTime → Ω → ℝ) :
      LocalCovarianceWitness P F (fun _ _ => 0) M (fun _ _ => 0) := by
    refine ⟨?_,hzv.toPathwise⟩
    simpa only [zero_mul,sub_zero] using zero_local_process P hT F
  have hCC i j : LocalCovarianceWitness P F (MM i) (MM j) (CC i j) := by
    fin_cases i <;> fin_cases j
    · exact hC
    · exact (hzero X).symm P F
    · exact hzero X
    · exact hzero _
  obtain ⟨c,hcp,hcm,hct,_,_,hcc⟩ := positive_real_time_exhaustion hT
  have hc n : 0 ≤ c n := (hcp n).le
  have hBm i ω : Measurable (fun r => BB i (ω,r)) := by
    fin_cases i
    · exact measurable_const
    · exact hqm
  have hBi i n : ∀ᵐ ω ∂P, IntervalIntegrable (fun r => BB i (ω,r)) volume 0 (c n) := by
    apply ae_of_all
    intro ω
    fin_cases i
    · exact intervalIntegrable_const
    · exact hqi _ (hc n)
  have hAB i n : ∀ᵐ ω ∂P, ∀ r ∈ Icc 0 (c n),
      AA i (realTimeClamp r) ω = AA i ⊥ ω + ∫ s in 0..r, BB i (ω,s) := by
    apply ae_of_all
    intro ω r hr
    fin_cases i
    · simp [AA,BB]
    · exact hR r hr.1
  have hGGm i j ω : Measurable (fun r => GG i j (ω,r)) := by
    dsimp only [GG]; split_ifs
    · exact hGm ω
    · exact measurable_const
  have hGGi i j n : ∀ᵐ ω ∂P, IntervalIntegrable (fun r => GG i j (ω,r)) volume 0 (c n) := by
    dsimp only [GG]; split_ifs
    · exact hGi _ (hc n)
    · exact ae_of_all _ fun _ => intervalIntegrable_const
  have hCCG i j n : ∀ᵐ ω ∂P, ∀ r ∈ Icc 0 (c n),
      CC i j (realTimeClamp r) ω = ∫ s in 0..r, GG i j (ω,s) := by
    filter_upwards [hCG] with ω hω
    intro r hr
    dsimp only [CC,GG]; split_ifs
    · exact hω r hr.1
    · simp
  obtain ⟨N,hN,_,he⟩ := multivariate_density_ito P hT F hF hle hnull XX AA MM CC hXX hCC
    f hf c hc hcm.monotone (fun n => by exact EReal.coe_lt_top _) hcc BB GG hBm hBi hAB hGGm hGGi hCCG
  refine ⟨fun t ω => N 0 t ω+N 1 t ω,(hN 0).add P F hF hle (hN 1),?_⟩
  intro r hr
  have hh := he r hr (EReal.coe_lt_top _)
  have hvec t ω : (fun i => XX i t ω) = ![X t ω,R t] := by ext i; fin_cases i <;> rfl
  simpa only [hvec, Fin.sum_univ_two, BB, GG, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ite_true, ite_false, and_self, Fin.zero_eta, Fin.isValue,
    zero_ne_one, one_ne_zero, false_and, and_false, mul_zero,
    intervalIntegral.integral_zero, add_zero, zero_add] using hh

end BarrierManuscript
#print axioms BarrierManuscript.variance_coordinate_ito
