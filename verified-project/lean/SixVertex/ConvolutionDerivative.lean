import SixVertex.BoundedConvolution
import SixVertex.WeightedKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Differentiation under convolution with an integrable left factor
and a genuinely bounded continuous derivative on the right. -/
theorem boundedConvolutionValue_hasDerivAt (k : ℝ → ℝ) (hk : Integrable k)
    (f f' : BoundedRealFunction) (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x) (x : ℝ) :
    HasDerivAt (boundedConvolutionValue k f) (boundedConvolutionValue k f' x) x := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t : ℝ => k t*f (x-t)) (F' := fun x t : ℝ => k t*f' (x-t))
    (bound := fun t : ℝ => |k t| *‖f'‖) (s := univ) (x₀ := x) (by simp)
    (Eventually.of_forall (fun y => (boundedConvolution_integrand_integrable k hk f y).aestronglyMeasurable))
    (boundedConvolution_integrand_integrable k hk f x)
    (boundedConvolution_integrand_integrable k hk f' x).aestronglyMeasurable
    (Eventually.of_forall (fun t y _ => by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (f'.norm_coe_le_norm (y-t)) (abs_nonneg _)))
    (hk.abs.mul_const ‖f'‖)
    (Eventually.of_forall (fun t y _ => by
      simpa only [Function.comp_def,id_eq,one_mul,mul_one] using!
        ((hd (y-t)).comp y ((hasDerivAt_id y).sub_const t)).const_mul (k t)))
  exact h.2

theorem scalar_convolution_comm (f g : ℝ → ℝ) (x : ℝ) :
    (∫ t : ℝ, f t*g (x-t))=(∫ t : ℝ, g t*f (x-t)) := by
  rw [← integral_sub_left_eq_self (fun t : ℝ => f t*g (x-t)) volume x]
  simp only [sub_sub_self,mul_comm]

def exponentialDecayBoundedFunction (k : ℝ → ℝ) (hk : Continuous k) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x, |k x| ≤ C*Real.exp (-2*|x|)) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup k hk C (fun x => (hdecay x).trans
    (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x]))))

/-- Any actual integrable continuous resolvent kernel of the physical
kernel has a genuine integrable first derivative. -/
theorem physical_resolvent_integrable_derivative (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (R : ℝ → ℝ) (hR : Integrable R)
    (heq : ∀ x, R x+(∫ t : ℝ, kernelK lam t*R (x-t))=kernelK lam x) :
    ∃ R' : ℝ → ℝ, Integrable R' ∧ ∀ x, HasDerivAt R (R' x) x := by
  have hk : Continuous (kernelK lam) := continuous_phaseDensity lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hkp : Continuous (kernelKPrime lam) := continuous_phaseDensityPrime lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  let f := exponentialDecayBoundedFunction (kernelK lam) hk (2/(Real.pi*(Real.sin lam)^2)) (by positivity)
    (fun x => kernelK_exponential_bound lam x h0 hpi)
  let f' := exponentialDecayBoundedFunction (kernelKPrime lam) hkp
    ((2/(Real.sin lam)^2)*(2/(Real.pi*(Real.sin lam)^2))) (by positivity)
    (fun x => kernelKPrime_exponential_bound lam x h0 hpi)
  have hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x := fun x => hasDerivAt_kernelK lam x h0 hpi
  have hi : Integrable (boundedConvolutionValue R f') :=
    hR.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (kernelKPrime_integrable lam h0 hpi)
  refine ⟨fun x => kernelKPrime lam x-boundedConvolutionValue R f' x,
    (kernelKPrime_integrable lam h0 hpi).sub hi,?_⟩
  have he : R=(fun x => kernelK lam x-boundedConvolutionValue R f x) := by
    funext x
    have hx := heq x
    rw [scalar_convolution_comm] at hx
    exact eq_sub_of_add_eq hx
  intro x
  have hx := (hasDerivAt_kernelK lam x h0 hpi).sub (boundedConvolutionValue_hasDerivAt R hR f f' hd x)
  convert hx using 1

end
end SixVertex
