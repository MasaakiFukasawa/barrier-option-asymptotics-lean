import ManuscriptBrownianConditionalMoment
import ManuscriptRawUnitMeasure

open MeasureTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

noncomputable def bridgeMean (b t x : ℝ) : ℝ := barPsi b x t/psi b x 1

theorem bridgeMean_measurable (b t : ℝ) : Measurable (bridgeMean b t) := by
  have hp := phi_contDiff.continuous.measurable
  have hP := normalCDF_contDiff.continuous.measurable
  unfold bridgeMean barPsi barPhi psi
  fun_prop

theorem barPsi_integrable (b t : ℝ) (hb : 0 < b) (ht : t ∈ Ioo (0:ℝ) 1) :
    IntegrableOn (barPsi b · t) (Iio b) := by
  have hi := bridge_test_integrable b t (1-t) hb ht.1 (sub_pos.mpr ht.2)
    (fun p => p.1) measurable_fst 1 zero_le_one (fun p => by simp only [one_mul]; linarith [abs_nonneg p.1])
  simpa only [IntegrableOn,psi_convolution b _ t ht] using hi.integral_prod_right

theorem bridgeMean_weight (b t x : ℝ) (hb : 0 < b) (hx : x < b) :
    psi b x 1*bridgeMean b t x=barPsi b x t := by
  unfold bridgeMean
  exact mul_div_cancel₀ _ (psi_positive b x 1 hb hx zero_lt_one).ne'

theorem bridgeMean_weight_integrable (b t : ℝ) (hb : 0 < b) (ht : t ∈ Ioo (0:ℝ) 1) :
    IntegrableOn (fun x => psi b x 1*bridgeMean b t x) (Iio b) := by
  apply (barPsi_integrable b t hb ht).congr
  filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
  exact (bridgeMean_weight b t x hb hx).symm

end BarrierManuscript
#print axioms BarrierManuscript.bridgeMean_measurable
#print axioms BarrierManuscript.barPsi_integrable
#print axioms BarrierManuscript.bridgeMean_weight
#print axioms BarrierManuscript.bridgeMean_weight_integrable
