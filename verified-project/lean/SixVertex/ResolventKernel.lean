import SixVertex.WeightedResolvent
import SixVertex.ConvolutionDerivative

namespace SixVertex
noncomputable section
open MeasureTheory

def physicalKernelFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  exponentialDecayBoundedFunction (kernelK lam)
    (continuous_phaseDensity lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne')
    (2/(Real.pi*(Real.sin lam)^2)) (by positivity)
    (fun x => kernelK_exponential_bound lam x h0 hpi)

/-- The full-line physical resolvent is the actual Neumann inverse
applied to K, rather than an additional assumed analytic object. -/
def physicalResolventKernel (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) (physicalKernelFunction lam h0 hpi)

theorem physicalResolventKernel_equation (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (x : ℝ) :
    physicalResolventKernel lam h0 hpi x+
      (∫ t : ℝ, kernelK lam t*physicalResolventKernel lam h0 hpi (x-t))=kernelK lam x := by
  exact congrArg (fun f : BoundedRealFunction => f x)
    (boundedConvolutionInverse_solves (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi) (physicalKernelFunction lam h0 hpi))

theorem physicalResolventKernel_unique (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (R : BoundedRealFunction)
    (heq : ∀ x, R x+(∫ t : ℝ, kernelK lam t*R (x-t))=kernelK lam x) :
    physicalResolventKernel lam h0 hpi=R := by
  have hs : R+boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi) R=
      physicalKernelFunction lam h0 hpi := by
    ext x
    exact heq x
  have hh := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T R)
    (boundedConvolutionInverse_left (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
  change boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
    (R+boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi) R)=R at hh
  rw [hs] at hh
  exact hh

/-- The constructed Neumann resolvent itself has a two-sided exponential
bound and is integrable; this is stronger than merely a bounded inverse. -/
theorem physicalResolventKernel_decay (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Integrable (fun x => physicalResolventKernel lam h0 hpi x) ∧
      ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
        ∀ x, |physicalResolventKernel lam h0 hpi x| ≤ C*Real.exp (-a*|x|) := by
  obtain ⟨a,C,ha,hC,R,hcont,hint,hbound,heq⟩ :=
    exists_exponentially_decaying_kernel_resolvent lam h0 hpi
  let Rb : BoundedRealFunction := BoundedContinuousFunction.ofNormedAddCommGroup R hcont C
    (fun x => (hbound x).trans (mul_le_of_le_one_right hC
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (abs_nonneg x)))))
  have he : physicalResolventKernel lam h0 hpi=Rb := physicalResolventKernel_unique lam h0 hpi Rb heq
  rw [he]
  exact ⟨hint,a,C,ha,hC,hbound⟩

/-- The first derivative is an actual HasDerivAt derivative and has
finite L1 norm. No distributional or formal derivative is substituted. -/
theorem physicalResolventKernel_integrable_derivative (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ R' : ℝ → ℝ, Integrable R' ∧
      ∀ x, HasDerivAt (fun u => physicalResolventKernel lam h0 hpi u) (R' x) x :=
  physical_resolvent_integrable_derivative lam h0 hpi _
    (physicalResolventKernel_decay lam h0 hpi).1 (physicalResolventKernel_equation lam h0 hpi)

end
end SixVertex
