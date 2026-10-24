import SixVertex.BoundedMeasurableAssociativity
import SixVertex.ExteriorConvolution

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

/-- The resolvent identity remains valid for an actual bounded measurable
right factor, so exterior indicators are covered by justified Fubini. -/
theorem physicalResolventKernel_measurable_identity (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (F : ℝ → ℝ) (hF : AEStronglyMeasurable F)
    (C : ℝ) (hb : ∀ x,‖F x‖ ≤ C) (u : ℝ) :
    (∫ t : ℝ,physicalResolventKernel lam h0 hpi t*F (u-t))+
      (∫ s : ℝ,kernelK lam s*(∫ t : ℝ,physicalResolventKernel lam h0 hpi t*F ((u-s)-t)))=
      ∫ t : ℝ,kernelK lam t*F (u-t) := by
  let R : ℝ → ℝ := fun x => physicalResolventKernel lam h0 hpi x
  have hr : Integrable R := (physicalResolventKernel_decay lam h0 hpi).1
  have hk := kernelK_integrable lam h0 hpi
  have hkr : Integrable (fun t : ℝ => ∫ s : ℝ,kernelK lam s*R (t-s)) :=
    hk.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hr
  have hshift : AEStronglyMeasurable (fun t : ℝ => F (u-t)) :=
    hF.comp_measurePreserving (Measure.measurePreserving_sub_left volume u)
  have hi : Integrable (fun t : ℝ => R t*F (u-t)) :=
    hr.mul_bdd hshift (Eventually.of_forall (fun t => hb (u-t)))
  have hci : Integrable (fun t : ℝ => (∫ s : ℝ,kernelK lam s*R (t-s))*F (u-t)) :=
    hkr.mul_bdd hshift (Eventually.of_forall (fun t => hb (u-t)))
  change (∫ t : ℝ,R t*F (u-t))+(∫ s : ℝ,kernelK lam s*(∫ t : ℝ,R t*F ((u-s)-t)))=_
  rw [← bounded_measurable_convolution_associativity (kernelK lam) R F hk hr hF C hb u,
    ← integral_add hi hci]
  apply integral_congr_ae
  filter_upwards with t
  rw [← add_mul]
  exact congrArg (fun x : ℝ => x*F (u-t)) (physicalResolventKernel_equation lam h0 hpi t)

/-- The exterior operator in the kernel-first convolution convention. -/
theorem exteriorConvolutionOperator_own_integral (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (Q : ℝ) (f : BoundedRealFunction) (u : ℝ) :
    exteriorConvolutionOperator k hk Q f u=
      ∫ t : ℝ,k t*((Icc (-Q) Q)ᶜ.indicator (fun v => f v) (u-t)) := by
  rw [exteriorConvolutionOperator_apply,← integral_indicator measurableSet_Icc.compl]
  have he := integral_sub_left_eq_self
    ((Icc (-Q) Q)ᶜ.indicator (fun v : ℝ => k (u-v)*f v)) volume u
  rw [← he]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : u-t ∈ (Icc (-Q) Q)ᶜ <;> simp [ht]

/-- Multiplication by I+K sends the actual exterior resolvent operator
to the corresponding exterior bare-kernel operator. -/
theorem exterior_physicalResolvent_operator_identity (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (f : BoundedRealFunction) :
    exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
        (physicalResolventKernel_decay lam h0 hpi).1 Q f+
      boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
        (exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
          (physicalResolventKernel_decay lam h0 hpi).1 Q f)=
      exteriorConvolutionOperator (physicalKernelFunction lam h0 hpi)
        (kernelK_integrable lam h0 hpi) Q f := by
  let F : ℝ → ℝ := (Icc (-Q) Q)ᶜ.indicator (fun v => f v)
  have hF : AEStronglyMeasurable F := f.continuous.aestronglyMeasurable.indicator measurableSet_Icc.compl
  have hb (v : ℝ) : ‖F v‖ ≤ ‖f‖ := by
    by_cases hv : v ∈ (Icc (-Q) Q)ᶜ
    · simpa only [F,indicator_of_mem hv] using f.norm_coe_le_norm v
    · simp only [F,indicator_of_notMem hv,norm_zero]
      exact norm_nonneg f
  ext u
  rw [BoundedContinuousFunction.add_apply,
    exteriorConvolutionOperator_own_integral (physicalResolventKernel lam h0 hpi)
      (physicalResolventKernel_decay lam h0 hpi).1 Q f u,
    boundedConvolutionOperator_apply]
  simp_rw [exteriorConvolutionOperator_own_integral (physicalResolventKernel lam h0 hpi)
    (physicalResolventKernel_decay lam h0 hpi).1 Q f]
  exact (physicalResolventKernel_measurable_identity lam h0 hpi F hF ‖f‖ hb u).trans
    (exteriorConvolutionOperator_own_integral (physicalKernelFunction lam h0 hpi)
      (kernelK_integrable lam h0 hpi) Q f u).symm

end
end SixVertex
