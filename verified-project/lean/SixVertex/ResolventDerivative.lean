import SixVertex.ResolventKernel

namespace SixVertex
noncomputable section
open MeasureTheory

def physicalKernelPrimeFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  exponentialDecayBoundedFunction (kernelKPrime lam)
    (continuous_phaseDensityPrime lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne')
    ((2/(Real.sin lam)^2)*(2/(Real.pi*(Real.sin lam)^2))) (by positivity)
    (fun x => kernelKPrime_exponential_bound lam x h0 hpi)

/-- The resolvent derivative is a concrete bounded continuous function. -/
def physicalResolventPrimeFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  physicalKernelPrimeFunction lam h0 hpi-
    boundedConvolution (fun x => physicalResolventKernel lam h0 hpi x)
      (physicalResolventKernel_decay lam h0 hpi).1 (physicalKernelPrimeFunction lam h0 hpi)

theorem physicalResolventPrimeFunction_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Integrable (fun x => physicalResolventPrimeFunction lam h0 hpi x) := by
  have hi : Integrable (boundedConvolutionValue (fun x => physicalResolventKernel lam h0 hpi x)
      (physicalKernelPrimeFunction lam h0 hpi)) :=
    (physicalResolventKernel_decay lam h0 hpi).1.integrable_convolution
      (L := ContinuousLinearMap.mul ℝ ℝ) (kernelKPrime_integrable lam h0 hpi)
  exact (kernelKPrime_integrable lam h0 hpi).sub hi

theorem hasDerivAt_physicalResolventKernel (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (x : ℝ) :
    HasDerivAt (fun u => physicalResolventKernel lam h0 hpi u)
      (physicalResolventPrimeFunction lam h0 hpi x) x := by
  have he : (fun u => physicalResolventKernel lam h0 hpi u)=
      fun u => kernelK lam u-boundedConvolutionValue (fun v => physicalResolventKernel lam h0 hpi v)
        (physicalKernelFunction lam h0 hpi) u := by
    funext u
    have h := physicalResolventKernel_equation lam h0 hpi u
    rw [scalar_convolution_comm] at h
    exact eq_sub_of_add_eq h
  have hx := (hasDerivAt_kernelK lam x h0 hpi).sub
    (boundedConvolutionValue_hasDerivAt (fun v => physicalResolventKernel lam h0 hpi v)
      (physicalResolventKernel_decay lam h0 hpi).1 (physicalKernelFunction lam h0 hpi)
      (physicalKernelPrimeFunction lam h0 hpi) (fun u => hasDerivAt_kernelK lam u h0 hpi) x)
  convert hx using 1
  rfl

theorem physicalResolventKernel_tendsto_atTop (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Filter.Tendsto (fun x => physicalResolventKernel lam h0 hpi x) Filter.atTop (nhds 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => hasDerivAt_physicalResolventKernel lam h0 hpi x)
    (physicalResolventPrimeFunction_integrable lam h0 hpi).integrableOn
    (physicalResolventKernel_decay lam h0 hpi).1.integrableOn

theorem physicalResolventKernel_tendsto_atBot (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Filter.Tendsto (fun x => physicalResolventKernel lam h0 hpi x) Filter.atBot (nhds 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun x _ => hasDerivAt_physicalResolventKernel lam h0 hpi x)
    (physicalResolventPrimeFunction_integrable lam h0 hpi).integrableOn
    (physicalResolventKernel_decay lam h0 hpi).1.integrableOn

end
end SixVertex
