import ManuscriptBlackScholesGamma
import ManuscriptStrictExpansion

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace BarrierManuscript

theorem normalCDF_strict_derivative (x : ℝ) : HasStrictDerivAt normalCDF (phi x) x :=
  hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    (Eventually.of_forall (fun y => normalCDF_hasDerivAt y)) phi_contDiff.continuous.continuousAt

theorem normalLeg_strict (l C B : ℝ → ℝ) (l' C' B' w : ℝ)
    (hw : w ≠ 0) (hl : HasStrictDerivAt l l' 0)
    (hC : HasStrictDerivAt C C' 0) (hB : HasStrictDerivAt B B' 0) :
    ∃ D : (ℝ × ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun p : ℝ × ℝ => normalLeg l C B p.1 p.2) D (0,w) := by
  have he := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasStrictFDerivAt (x := ((0,w):ℝ × ℝ))
  have hv := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasStrictFDerivAt (x := ((0,w):ℝ × ℝ))
  have hlog := hl.hasStrictFDerivAt.comp ((0,w):ℝ × ℝ) he
  have hc := hC.hasStrictFDerivAt.comp ((0,w):ℝ × ℝ) he
  have hb := hB.hasStrictFDerivAt.comp ((0,w):ℝ × ℝ) he
  have hwinv := (hasStrictDerivAt_inv hw).hasStrictFDerivAt.comp ((0,w):ℝ × ℝ) hv
  have hd := hlog.mul hwinv
  have hq := he.mul hv
  have harg := hd.add (hq.mul_const ((2:ℝ)⁻¹))
  have hcdf := (normalCDF_strict_derivative (l 0/w+(0:ℝ)*w/2)).hasStrictFDerivAt.comp
    ((0,w):ℝ × ℝ) harg
  have havg := (phiAverage_hasStrictFDerivAt (l 0/w,(0:ℝ)*w)).comp ((0,w):ℝ × ℝ) (hd.prodMk hq)
  have hh := (hc.mul hcdf).add ((hb.mul hv).mul havg)
  change HasStrictFDerivAt (fun p : ℝ × ℝ => normalLeg l C B p.1 p.2) _ (0,w) at hh
  exact ⟨_,hh⟩

theorem bsBarrierNormalized_strict (b k : ℝ) :
    ∃ D : (ℝ × ℝ) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun p : ℝ × ℝ => bsBarrierNormalized b k p.1 p.2) D (0,1) := by
  obtain ⟨D1,h1⟩ := normalLeg_strict (logRatio k) (fun _ => k) (fun _ => 1)
    (-k^2/2) 0 0 1 (by norm_num) (logRatio_strict_derivative_zero k)
    (hasStrictDerivAt_const 0 k) (hasStrictDerivAt_const 0 1)
  have hl := (logRatio_strict_derivative_zero k).sub ((logRatio_strict_derivative_zero b).const_mul 2)
  have hC : HasStrictDerivAt (fun e : ℝ => (k-2*b-e*b^2)/(1+e*b)) (b*(b-k)) 0 := by
    convert! ((hasStrictDerivAt_const 0 (k-2*b)).sub ((hasStrictDerivAt_id (0:ℝ)).mul_const (b^2))).div
      (((hasStrictDerivAt_id (0:ℝ)).mul_const b).const_add 1) (by simp) using 1
    simp
    ring
  have hB : HasStrictDerivAt (fun e : ℝ => 1+e*b) b 0 := by
    convert! ((hasStrictDerivAt_id (0:ℝ)).mul_const b).const_add 1 using 1
    simp
  obtain ⟨D2,h2⟩ := normalLeg_strict (fun e => logRatio k e-2*logRatio b e)
    (fun e => (k-2*b-e*b^2)/(1+e*b)) (fun e => 1+e*b)
    (-k^2/2-2*(-b^2/2)) (b*(b-k)) b 1 (by norm_num) hl hC hB
  refine ⟨D1-D2,?_⟩
  convert! h1.sub h2 using 1
  funext p
  dsimp only [Pi.sub_apply]
  unfold bsBarrierNormalized normalLeg
  ring

theorem bsBarrierNormalized_expansion (b k : ℝ) (e w : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hw : Tendsto w atTop (𝓝 1)) :
    Tendsto (fun n => (bsBarrierNormalized b k (e n) (w n)-killedPut b k 0 (w n)-e n*gamma b k)/e n)
      atTop (𝓝 0) := by
  obtain ⟨D,hD⟩ := bsBarrierNormalized_strict b k
  have hd : D (1,0) = gamma b k := by
    have hp : HasDerivAt (fun e : ℝ => (e,1)) ((1,0):ℝ × ℝ) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 1)
    have hh := hD.hasFDerivAt.comp_hasDerivAt 0 hp
    exact hh.unique (bsBarrierNormalized_derivative_zero b k)
  have hh := strict_increment_limit (fun p => bsBarrierNormalized b k p.1 p.2) D 1 hD e w he hw
  simpa only [bsBarrierNormalized_zero,hd] using hh

end BarrierManuscript
#print axioms BarrierManuscript.normalCDF_strict_derivative
#print axioms BarrierManuscript.normalLeg_strict
#print axioms BarrierManuscript.bsBarrierNormalized_strict
#print axioms BarrierManuscript.bsBarrierNormalized_expansion
