import SixVertex.ConvolutionResolvent
import SixVertex.CountingMass

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology

/-- Convolution with an actual L1 kernel preserves a finite left-end
limit, multiplied by the signed kernel mass. -/
theorem boundedConvolution_tendsto_atBot (k : ℝ → ℝ) (hk : Integrable k)
    (f : BoundedRealFunction) (c : ℝ) (hf : Tendsto (fun x => f x) atBot (𝓝 c)) :
    Tendsto (boundedConvolutionValue k f) atBot (𝓝 ((∫ t : ℝ, k t)*c)) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun x t : ℝ => k t*f (x-t)) (f := fun t : ℝ => k t*c)
    (fun t : ℝ => |k t| *‖f‖)
    (Eventually.of_forall (fun x => (boundedConvolution_integrand_integrable k hk f x).aestronglyMeasurable))
    (Eventually.of_forall (fun x => Eventually.of_forall (fun t => by
      change ‖k t*f (x-t)‖ ≤ |k t| *‖f‖
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x-t)) (abs_nonneg _))))
    (hk.abs.mul_const ‖f‖)
    (Eventually.of_forall (fun t => tendsto_const_nhds.mul (hf.comp (real_shift_tendsto_atBot t))))
  change Tendsto (fun x : ℝ => ∫ t : ℝ, k t*f (x-t)) _ _
  simpa only [integral_mul_const] using ht

theorem boundedConvolution_tendsto_atTop (k : ℝ → ℝ) (hk : Integrable k)
    (f : BoundedRealFunction) (c : ℝ) (hf : Tendsto (fun x => f x) atTop (𝓝 c)) :
    Tendsto (boundedConvolutionValue k f) atTop (𝓝 ((∫ t : ℝ, k t)*c)) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun x t : ℝ => k t*f (x-t)) (f := fun t : ℝ => k t*c)
    (fun t : ℝ => |k t| *‖f‖)
    (Eventually.of_forall (fun x => (boundedConvolution_integrand_integrable k hk f x).aestronglyMeasurable))
    (Eventually.of_forall (fun x => Eventually.of_forall (fun t => by
      change ‖k t*f (x-t)‖ ≤ |k t| *‖f‖
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x-t)) (abs_nonneg _))))
    (hk.abs.mul_const ‖f‖)
    (Eventually.of_forall (fun t => tendsto_const_nhds.mul (hf.comp (real_shift_tendsto_atTop t))))
  change Tendsto (fun x : ℝ => ∫ t : ℝ, k t*f (x-t)) _ _
  simpa only [integral_mul_const] using ht

/-- Inverse dressing of a bounded continuous L1 source remains L1.
This is deduced from the constructed kernel representation. -/
theorem physicalInverse_preserves_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (f : BoundedRealFunction) (hf : Integrable (fun x => f x)) :
    Integrable (fun x => boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) f x) := by
  rw [physicalInverse_resolvent_representation lam h0 hpi f]
  exact hf.sub ((physicalResolventKernel_decay lam h0 hpi).1.integrable_convolution
    (L := ContinuousLinearMap.mul ℝ ℝ) hf)

end
end SixVertex
