import ManuscriptChapmanKolmogorov
import ManuscriptScaledCoefficient

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem psi_space_time_scaling (c b x t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    psi (c*b) (c*x) (c^2*t)=psi b x t/c := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  unfold psi
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc.le]
  have h1 : c*x/(c*Real.sqrt t)=x/Real.sqrt t := by field_simp
  have h2 : (c*x-2*(c*b))/(c*Real.sqrt t)=(x-2*b)/Real.sqrt t := by field_simp <;> ring
  rw [h1,h2]
  ring

/-- The killed Brownian transition kernel's composition law at arbitrary
positive durations, obtained from the normalized Gaussian identity. -/
theorem psi_semigroup (b k s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    (∫ x in Iio b,psi (b-x) (k-x) t*psi b x s)=psi b k (s+t) := by
  let c := Real.sqrt (s+t)
  let u := s/(s+t)
  have hT : 0 < s+t := add_pos hs ht
  have hc : 0 < c := Real.sqrt_pos.mpr hT
  have hc2 : c^2=s+t := Real.sq_sqrt hT.le
  have hu : u ∈ Ioo (0:ℝ) 1 := ⟨div_pos hs hT,(div_lt_one hT).mpr (by linarith)⟩
  have hs' : c^2*u=s := by dsimp only [u]; rw [hc2]; field_simp
  have ht' : c^2*(1-u)=t := by dsimp only [u]; rw [hc2]; field_simp <;> ring
  have hps (B X : ℝ) : psi B X s=psi (B/c) (X/c) u/c := by
    have h := psi_space_time_scaling c (B/c) (X/c) u hc hu.1
    simpa only [hs',mul_div_cancel₀ _ hc.ne'] using h
  have hpt (B X : ℝ) : psi B X t=psi (B/c) (X/c) (1-u)/c := by
    have h := psi_space_time_scaling c (B/c) (X/c) (1-u) hc (sub_pos.mpr hu.2)
    simpa only [ht',mul_div_cancel₀ _ hc.ne'] using h
  let f := fun x => psi (b-x) (k-x) t*psi b x s
  have he (x : ℝ) : f (c*x)=(psi (b/c-x) (k/c-x) (1-u)*psi (b/c) x u)/c^2 := by
    dsimp only [f]
    rw [hpt,hps]
    simp only [sub_div,mul_div_cancel_left₀ _ hc.ne']
    ring
  have hi := integral_comp_mul_left_Iio_real f (b/c) c hc
  rw [mul_div_cancel₀ _ hc.ne'] at hi
  simp_rw [he] at hi
  rw [integral_div,psi_chapman_kolmogorov (b/c) (k/c) u hu] at hi
  have hbase : psi b k (s+t)=psi (b/c) (k/c) 1/c := by
    have h := psi_space_time_scaling c (b/c) (k/c) 1 hc zero_lt_one
    simpa only [mul_one,hc2,mul_div_cancel₀ _ hc.ne'] using h
  rw [hbase]
  change (∫ x in Iio b,f x)=_
  have hh := hi
  field_simp at hh ⊢
  nlinarith

end BarrierManuscript
#print axioms BarrierManuscript.psi_space_time_scaling
#print axioms BarrierManuscript.psi_semigroup
