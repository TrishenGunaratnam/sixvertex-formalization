import SixVertex.FullLineDensity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def finiteIntervalMass (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) : ℝ :=
  ∫ u in Icc (-Q) Q, finiteIntervalDensity lam h0 hpi Q u

theorem physicalWindowOperator_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (f : BoundedRealFunction) :
    Integrable (fun u => physicalWindowOperator lam h0 hpi Q f u) := by
  have he : (fun u => physicalWindowOperator lam h0 hpi Q f u)=
      boundedConvolutionValue (windowedFunction Q f) (physicalKernelFunction lam h0 hpi) := by
    funext u
    change (∫ v : ℝ, kernelK lam (u-v)*windowedFunction Q f v)=
      ∫ v : ℝ, windowedFunction Q f v*kernelK lam (u-v)
    simp only [mul_comm]
  rw [he]
  exact (windowedFunction_integrable Q f).integrable_convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) (kernelK_integrable lam h0 hpi)

/-- The bounded whole-line extension of r_Q is genuinely integrable. -/
theorem finiteIntervalDensity_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) :
    Integrable (fun u => finiteIntervalDensity lam h0 hpi Q u) := by
  have he : (fun u => finiteIntervalDensity lam h0 hpi Q u)=
      fun u => kernelS lam u-physicalWindowOperator lam h0 hpi Q (finiteIntervalDensity lam h0 hpi Q) u := by
    funext u
    rw [physicalWindowOperator_apply]
    linarith [finiteIntervalDensity_equation lam h0 hpi Q u]
  rw [he]
  exact (kernelS_integrable lam h0 hpi).sub (physicalWindowOperator_integrable lam h0 hpi Q _)

/-- Fubini identifies the ordinary full-line integral of the actual
finite-window operator with its signed kernel mass. -/
theorem integral_physicalWindowOperator (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (f : BoundedRealFunction) :
    (∫ u : ℝ, physicalWindowOperator lam h0 hpi Q f u)=
      (∫ t : ℝ, kernelK lam t)*(∫ u in Icc (-Q) Q, f u) := by
  have he : (fun u => physicalWindowOperator lam h0 hpi Q f u)=
      boundedConvolutionValue (windowedFunction Q f) (physicalKernelFunction lam h0 hpi) := by
    funext u
    change (∫ v : ℝ, kernelK lam (u-v)*windowedFunction Q f v)=
      ∫ v : ℝ, windowedFunction Q f v*kernelK lam (u-v)
    simp only [mul_comm]
  rw [he]
  have hc := integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (windowedFunction_integrable Q f) (kernelK_integrable lam h0 hpi)
  change (∫ u : ℝ, boundedConvolutionValue (windowedFunction Q f) (physicalKernelFunction lam h0 hpi) u)=
    (∫ u : ℝ, windowedFunction Q f u)*(∫ t : ℝ, kernelK lam t) at hc
  rw [hc,windowedFunction,integral_indicator measurableSet_Icc,mul_comm]

theorem finiteIntervalDensity_total_mass_equation (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) :
    (∫ u : ℝ, finiteIntervalDensity lam h0 hpi Q u)+
      (1-2*lam/Real.pi)*finiteIntervalMass lam h0 hpi Q=1-lam/Real.pi := by
  have he := congrArg (fun f : BoundedRealFunction => ∫ u : ℝ, f u)
    (physicalWindowInverse_solves lam h0 hpi Q (physicalSourceFunction lam h0 hpi))
  change (∫ u : ℝ, finiteIntervalDensity lam h0 hpi Q u+
    physicalWindowOperator lam h0 hpi Q (finiteIntervalDensity lam h0 hpi Q) u)=_ at he
  rw [integral_add (finiteIntervalDensity_integrable lam h0 hpi Q)
    (physicalWindowOperator_integrable lam h0 hpi Q _),integral_physicalWindowOperator,
    integral_kernelK lam h0 hpi] at he
  simp_rw [physicalSourceFunction_apply] at he
  rw [integral_kernelS lam h0 hpi] at he
  exact he

end
end SixVertex
