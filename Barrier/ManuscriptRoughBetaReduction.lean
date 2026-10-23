import ManuscriptRoughIBP

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
open Asakura.FullAudit Asakura.Chapter2Complete Asakura.Chapter7
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

/-- The exact beta-weighted expression displayed in the rough Bergomi
subsection reduces to the single weighted barPsi integral. -/
theorem rough_beta_reduction (b k H : ℝ) (hb : 0 < b) (hH : -(1/2:ℝ) < H) :
    (∫ s in (0:ℝ)..1, deriv (barPsi b k) s * s^(H+1/2) *
      (∫ t in (0:ℝ)..(1-s), t^(H-1/2)*(1-t)^(-H-3/2))) =
      ∫ s in (0:ℝ)..1, (1-s)^(H-1/2)*barPsi b k s := by
  have ha : 0 < H+1/2 := by linarith
  have he : (∫ s in (0:ℝ)..1, deriv (barPsi b k) s*s^(H+1/2)*
      (∫ t in (0:ℝ)..(1-s), t^(H-1/2)*(1-t)^(-H-3/2))) =
      ∫ s in (0:ℝ)..1, barPsiTimeDerivative b k s*(1-s)^(H+1/2)/(H+1/2) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro s hs
    have hz : 1-s ∈ Ioo (0:ℝ) 1 := ⟨sub_pos.mpr hs.2,by linarith [hs.1]⟩
    have hbeta := incomplete_beta_identity (H+1/2) (1-s) ha hz
    simp only [show H+1/2-1=H-1/2 by ring,
      show -(H+1/2)-1= -H-3/2 by ring,show 1-(1-s)=s by ring] at hbeta
    dsimp only
    rw [hbeta,(barPsi_derivative b k s hs).deriv]
    change barPsiTimeDerivative b k s*s^(H+1/2)*(((1-s)/s)^(H+1/2)/(H+1/2)) = _
    rw [Real.div_rpow (sub_pos.mpr hs.2).le hs.1.le]
    calc
      _ = (barPsiTimeDerivative b k s*(1-s)^(H+1/2)/(H+1/2)) *
          (s^(H+1/2)/s^(H+1/2)) := by ring
      _ = _ := by rw [div_self (Real.rpow_pos_of_pos hs.1 (H+1/2)).ne',mul_one]
  rw [he]
  simpa only [show H+1/2-1=H-1/2 by ring] using rough_coefficient_ibp b k (H+1/2) hb ha

noncomputable def roughBergomiCoefficient (b k H ρ ν : ℝ) : ℝ :=
  ρ*ν*Real.sqrt (2*H)/2*(∫ s in (0:ℝ)..1, (1-s)^(H-1/2)*barPsi b k s)

/-- At H=1/2 the displayed rough coefficient agrees with the regular-model
corollary's gamma coefficient. -/
theorem rough_coefficient_half {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSystem P 1)
    (b k ρ ν : ℝ) (hb : 0 < b) (hk : k ≤ b) :
    roughBergomiCoefficient b k (1/2) ρ ν = ρ*ν/2*gamma b k := by
  unfold roughBergomiCoefficient
  norm_num only [show (2:ℝ)*(1/2)=1 by norm_num,Real.sqrt_one,mul_one,sub_self,Real.rpow_zero,one_mul]
  rw [gamma_integral P B b k hb hk]

end BarrierManuscript
#print axioms BarrierManuscript.rough_beta_reduction
#print axioms BarrierManuscript.rough_coefficient_half
