import ManuscriptIntegralPathScaling
import ManuscriptRoughPathApproximation
import ManuscriptProbabilityRescaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter4 Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- Brownian scaling of the singular integral, proved on the original
probability space using its actual Ito characterization. -/
theorem rough_integral_scaling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (H ν : ℝ) (hH : 0 < H) (θ : ℝ≥0) (hθ : 0 < (θ:ℝ))
    (a : ℕ → ℝ≥0) (ha : ∀ n, a n < 1) (halim : Tendsto (fun n => (a n:ℝ)) atTop (𝓝 1))
    (N M : HalfClosedTime → Ω → ℝ)
    (hN : LocalMProcessWitness P B.F N)
    (hM : LocalMProcessWitness P (scaledBrownian B θ hθ).F M)
    (hNI : ItoCovarianceFormula P B.F (B.W 0) (fun z => roughKernel H ν θ z.2) N)
    (hMI : ItoCovarianceFormula P (scaledBrownian B θ hθ).F
      ((scaledBrownian B θ hθ).W 0) (fun z => roughKernel H ν 1 z.2) M) :
    (fun ω => N (realTimeClamp θ) ω/(θ:ℝ)^H)=ᵐ[P] M (realTimeClamp 1) := by
  have hcut n : θ*a n < θ := by
    have hθ' : 0 < θ := hθ
    simpa only [mul_one] using mul_lt_mul_of_pos_left (ha n) hθ'
  have hlim : Tendsto (fun n => ((θ*a n:ℝ≥0):ℝ)) atTop (𝓝 (θ:ℝ)) := by
    simpa only [NNReal.coe_mul,mul_one] using halim.const_mul (θ:ℝ)
  have hbig := rough_integral_path_approximation P B H ν hH θ (fun n => θ*a n)
    hcut hlim N hN hNI
  have hsmall := rough_integral_path_approximation P (scaledBrownian B θ hθ) H ν hH 1 a ha halim M hM hMI
  have hn := (Real.rpow_pos_of_pos hθ H).ne'
  have hb := inMeasure_div_positive P _ ((θ:ℝ)^H) (Real.rpow_pos_of_pos hθ H) hbig
  let F := fun n ω => deterministicIntegralPath (roughKernelExtension H ν 1 (a n)) (a n)
    (brownianContinuousPath (scaledBrownian B θ hθ) ω)
  have he n ω :
      (N (realTimeClamp θ) ω-deterministicIntegralPath (roughKernelExtension H ν θ (θ*a n))
        (θ*a n) (brownianContinuousPath B ω))/(θ:ℝ)^H=
      N (realTimeClamp θ) ω/(θ:ℝ)^H-F n ω := by
    have hh := rough_integral_path_scaling H ν θ hθ (a n) (ha n) (brownianContinuousPath B ω)
    have ht : (NNReal.mk (θ:ℝ) hθ.le)=θ := by apply NNReal.eq; rfl
    rw [ht] at hh
    rw [hh]
    dsimp only [F]
    rw [scaled_brownian_path_encoding P B θ hθ]
    field_simp
  have hb' : TendstoInMeasure P (fun n ω => N (realTimeClamp θ) ω/(θ:ℝ)^H-F n ω) atTop (fun _ => 0) := by
    convert hb using 1
    funext n ω
    simpa only [NNReal.coe_mul] using (he n ω).symm
  exact tendstoInMeasure_ae_unique
    (inMeasure_of_reverse_error P F _ hb') (inMeasure_of_reverse_error P F _ hsmall)

end BarrierManuscript
#print axioms BarrierManuscript.rough_integral_scaling
