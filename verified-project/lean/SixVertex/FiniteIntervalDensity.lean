import SixVertex.WindowConvolution
import SixVertex.CountingDensity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- The homogeneous source s, as an actual bounded continuous function. -/
def physicalSourceFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  physicalKernelFunction (lam/2) (by linarith) (by linarith [Real.pi_pos])

theorem physicalSourceFunction_apply (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u : ℝ) :
    physicalSourceFunction lam h0 hpi u=kernelS lam u := (kernelS_eq_phaseDensity lam u).symm

def physicalWindowOperator (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) : BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  windowConvolutionOperator (physicalKernelFunction lam h0 hpi) (kernelK_integrable lam h0 hpi) Q

def physicalWindowInverse (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) : BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  windowConvolutionInverse (physicalKernelFunction lam h0 hpi) (kernelK_integrable lam h0 hpi) Q

/-- This is the manuscript's r_Q=(I+K_Q)^(-1)s, with its bounded
whole-line extension fixed by the same actual integral equation. -/
def finiteIntervalDensity (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) : BoundedRealFunction :=
  physicalWindowInverse lam h0 hpi Q (physicalSourceFunction lam h0 hpi)

/-- This is the manuscript's H_Q=(I+K_Q)^(-1)1. -/
def finiteIntervalOne (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) : BoundedRealFunction :=
  physicalWindowInverse lam h0 hpi Q (BoundedContinuousFunction.const ℝ (1 : ℝ))

theorem physicalWindowOperator_apply (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (f : BoundedRealFunction) (u : ℝ) :
    physicalWindowOperator lam h0 hpi Q f u=∫ v in Icc (-Q) Q, kernelK lam (u-v)*f v :=
  windowConvolutionOperator_apply _ _ Q f u

theorem physicalWindowInverse_solves (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (f : BoundedRealFunction) :
    physicalWindowInverse lam h0 hpi Q f+
      physicalWindowOperator lam h0 hpi Q (physicalWindowInverse lam h0 hpi Q f)=f :=
  windowConvolutionInverse_solves (physicalKernelFunction lam h0 hpi)
    (kernelK_integrable lam h0 hpi) (kernelK_L1_mass_lt_one lam h0 hpi) Q f

theorem physicalWindowInverse_solution_unique (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (f g : BoundedRealFunction)
    (hsol : g+physicalWindowOperator lam h0 hpi Q g=f) :
    physicalWindowInverse lam h0 hpi Q f=g := by
  have hi := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T g)
    (windowConvolutionInverse_left (physicalKernelFunction lam h0 hpi) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi) Q)
  change physicalWindowInverse lam h0 hpi Q (g+physicalWindowOperator lam h0 hpi Q g)=g at hi
  rw [hsol] at hi
  exact hi

theorem finiteIntervalDensity_equation (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) :
    finiteIntervalDensity lam h0 hpi Q u+
      (∫ v in Icc (-Q) Q, kernelK lam (u-v)*finiteIntervalDensity lam h0 hpi Q v)=kernelS lam u := by
  have h := congrArg (fun f : BoundedRealFunction => f u)
    (physicalWindowInverse_solves lam h0 hpi Q (physicalSourceFunction lam h0 hpi))
  change finiteIntervalDensity lam h0 hpi Q u+physicalWindowOperator lam h0 hpi Q
    (finiteIntervalDensity lam h0 hpi Q) u=physicalSourceFunction lam h0 hpi u at h
  rwa [physicalWindowOperator_apply,physicalSourceFunction_apply] at h

theorem finiteIntervalOne_equation (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) :
    finiteIntervalOne lam h0 hpi Q u+
      (∫ v in Icc (-Q) Q, kernelK lam (u-v)*finiteIntervalOne lam h0 hpi Q v)=1 := by
  have h := congrArg (fun f : BoundedRealFunction => f u)
    (physicalWindowInverse_solves lam h0 hpi Q (BoundedContinuousFunction.const ℝ (1 : ℝ)))
  change finiteIntervalOne lam h0 hpi Q u+physicalWindowOperator lam h0 hpi Q
    (finiteIntervalOne lam h0 hpi Q) u=1 at h
  rwa [physicalWindowOperator_apply] at h

theorem physicalWindowInverse_norm_bound (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) : ‖physicalWindowInverse lam h0 hpi Q‖ ≤ (1-|1-2*lam/Real.pi|)⁻¹ := by
  have h := windowConvolutionInverse_norm_bound (physicalKernelFunction lam h0 hpi)
    (kernelK_integrable lam h0 hpi) (kernelK_L1_mass_lt_one lam h0 hpi) Q
  change _ ≤ (1-(∫ t : ℝ, |kernelK lam t|))⁻¹ at h
  rw [integral_abs_kernelK lam h0 hpi] at h
  exact h

theorem finiteIntervalOne_norm_bound (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) : ‖finiteIntervalOne lam h0 hpi Q‖ ≤ (1-|1-2*lam/Real.pi|)⁻¹ := by
  have h := ContinuousLinearMap.le_opNorm (physicalWindowInverse lam h0 hpi Q)
    (BoundedContinuousFunction.const ℝ (1 : ℝ))
  change ‖finiteIntervalOne lam h0 hpi Q‖ ≤ _ at h
  simpa only [BoundedContinuousFunction.norm_const_eq,norm_one,mul_one] using
    h.trans (mul_le_mul_of_nonneg_right (physicalWindowInverse_norm_bound lam h0 hpi Q) (norm_nonneg _))

end
end SixVertex
