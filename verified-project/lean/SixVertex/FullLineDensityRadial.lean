import SixVertex.RadialConvolution
import SixVertex.FiniteIntervalSymmetry

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter Topology

/-- A positive hyperbolic-denominator profile decreases with distance
from the origin. -/
theorem phase_fraction_radiallyAntitone (theta A : ℝ) (hs : Real.sin theta ≠ 0) (hA : 0 ≤ A) :
    RadiallyAntitone (fun u => A/(Real.pi*(Real.cosh (2*u)-Real.cos (2*theta)))) := by
  intro u v huv
  have hc : Real.cosh (2*u) ≤ Real.cosh (2*v) := Real.cosh_le_cosh.mpr (by
    simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using mul_le_mul_of_nonneg_left huv (by norm_num : (0 : ℝ) ≤ 2))
  apply div_le_div_of_nonneg_left hA (mul_pos Real.pi_pos (phase_denominator_pos theta u hs))
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hc _) Real.pi_pos.le

theorem kernelS_radiallyAntitone (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    RadiallyAntitone (kernelS lam) := by
  have hs : Real.sin (lam/2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hh := phase_fraction_radiallyAntitone (lam/2) (Real.sin lam) hs (Real.sin_pos_of_pos_of_lt_pi h0 hpi).le
  intro u v huv
  rw [kernelS_eq_phaseDensity,kernelS_eq_phaseDensity]
  simpa only [phaseDensity,show 2*(lam/2)=lam by ring] using hh u v huv

theorem negative_kernelK_radiallyAntitone (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    RadiallyAntitone (fun u => -kernelK lam u) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  have hc : Real.cos lam ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith)
  have hA : 0 ≤ -Real.sin (2*lam) := by
    rw [Real.sin_two_mul]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hs.le) hc)
  simpa only [kernelK,phaseDensity,neg_div] using phase_fraction_radiallyAntitone lam (-Real.sin (2*lam)) hs.ne' hA

theorem negative_physicalFullOperator_radial (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (f : BoundedRealFunction)
    (hf : RadiallyAntitone (fun u => f u)) :
    RadiallyAntitone (fun u => (-(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))) f u) := by
  have he : (fun u => (-(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))) f u)=
      (fun u => boundedConvolution (fun t => -kernelK lam t) (kernelK_integrable lam h0 hpi).neg f u) := by
    funext u
    change -(∫ t : ℝ, kernelK lam t*f (u-t))=∫ t : ℝ, (-kernelK lam t)*f (u-t)
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by ring)
  rw [he]
  exact boundedConvolution_radiallyAntitone _ (kernelK_integrable lam h0 hpi).neg
    (negative_kernelK_radiallyAntitone lam hhalf hpi) f hf

/-- The actual inverse-defined full-line density is radially decreasing.
No Fourier formula is assumed. -/
theorem fullLineDensityFunction_radiallyAntitone (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    RadiallyAntitone (fun u => fullLineDensityFunction lam h0 hpi u) := by
  let A := -(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))
  have hA : ‖A‖ < 1 := (norm_neg (boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))).trans_lt
    ((boundedConvolutionOperator_norm_bound (kernelK lam) (kernelK_integrable lam h0 hpi)).trans_lt (kernelK_L1_mass_lt_one lam h0 hpi))
  change RadiallyAntitone (fun u => (∑' m : ℕ, A^m) (physicalSourceFunction lam h0 hpi) u)
  apply radial_operator_neumann A hA (negative_physicalFullOperator_radial lam h0 hhalf hpi)
  intro u v huv
  change physicalSourceFunction lam h0 hpi v ≤ physicalSourceFunction lam h0 hpi u
  rw [physicalSourceFunction_apply,physicalSourceFunction_apply]
  exact kernelS_radiallyAntitone lam h0 hpi u v huv

end
end SixVertex
