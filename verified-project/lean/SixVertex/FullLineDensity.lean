import SixVertex.FiniteIntervalDensity
import SixVertex.ConvolutionLimits

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem fullLineDensityFunction_equation (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    fullLineDensityFunction lam h0 hpi+
      boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
        (fullLineDensityFunction lam h0 hpi)=physicalSourceFunction lam h0 hpi :=
  boundedConvolutionInverse_solves (kernelK lam) (kernelK_integrable lam h0 hpi)
    (kernelK_L1_mass_lt_one lam h0 hpi) _

theorem fullLineDensityFunction_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Integrable (fun u => fullLineDensityFunction lam h0 hpi u) := by
  apply physicalInverse_preserves_integrable lam h0 hpi (physicalSourceFunction lam h0 hpi)
  simp_rw [physicalSourceFunction_apply]
  exact kernelS_integrable lam h0 hpi

/-- The mass of the actual inverse-defined homogeneous density. No
hyperbolic closed-form or Fourier transform identity is assumed. -/
theorem integral_fullLineDensityFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (∫ u : ℝ, fullLineDensityFunction lam h0 hpi u)=1/2 := by
  have hr := fullLineDensityFunction_integrable lam h0 hpi
  have hk := kernelK_integrable lam h0 hpi
  have hconv : Integrable (boundedConvolutionValue (kernelK lam) (fullLineDensityFunction lam h0 hpi)) :=
    hk.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hr
  have he := congrArg (fun f : BoundedRealFunction => ∫ u : ℝ, f u)
    (fullLineDensityFunction_equation lam h0 hpi)
  change (∫ u : ℝ, fullLineDensityFunction lam h0 hpi u+
    boundedConvolutionValue (kernelK lam) (fullLineDensityFunction lam h0 hpi) u)=_ at he
  rw [integral_add hr hconv] at he
  simp_rw [physicalSourceFunction_apply] at he
  rw [integral_kernelS lam h0 hpi] at he
  have hc : (∫ u : ℝ, boundedConvolutionValue (kernelK lam) (fullLineDensityFunction lam h0 hpi) u)=
      (∫ u : ℝ, kernelK lam u)*(∫ u : ℝ, fullLineDensityFunction lam h0 hpi u) :=
    integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hk hr
  rw [hc,integral_kernelK lam h0 hpi] at he
  have hp : 0 < 1-lam/Real.pi := sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi)
  rw [show 2*lam/Real.pi=2*(lam/Real.pi) by ring] at he
  have hz : (1-lam/Real.pi)*(2*(∫ u : ℝ, fullLineDensityFunction lam h0 hpi u)-1)=0 := by
    nlinarith only [he]
  have hmass := (mul_eq_zero.mp hz).resolve_left hp.ne'
  linarith

end
end SixVertex
