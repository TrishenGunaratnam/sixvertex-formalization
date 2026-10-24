import SixVertex.ConvolutionResolvent
import SixVertex.CountingDiscrepancyKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter

/-- Associativity for actual L1 kernels and a bounded measurable factor,
including a window indicator; the Fubini majorant is explicit. -/
theorem bounded_measurable_convolution_associativity (k r F : ℝ → ℝ)
    (hk : Integrable k) (hr : Integrable r) (hF : AEStronglyMeasurable F)
    (C : ℝ) (hb : ∀ x,‖F x‖ ≤ C) (u : ℝ) :
    (∫ t : ℝ,(∫ s : ℝ,k s*r (t-s))*F (u-t))=
      ∫ s : ℝ,k s*(∫ t : ℝ,r t*F ((u-s)-t)) := by
  have hi0 : Integrable (fun p : ℝ×ℝ => k p.2*r (p.1-p.2)) (volume.prod volume) :=
    hk.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hr
  have hFc : AEStronglyMeasurable (fun p : ℝ×ℝ => F (u-p.1)) (volume.prod volume) := by
    exact ((hF.comp_measurePreserving (Measure.measurePreserving_sub_left volume u)).comp_fst)
  have hi : Integrable (fun p : ℝ×ℝ => k p.2*(r (p.1-p.2)*F (u-p.1))) (volume.prod volume) := by
    have hbd := hi0.mul_bdd hFc (Eventually.of_forall (fun p : ℝ×ℝ => hb (u-p.1)))
    convert hbd using 1
    funext p
    ring
  have hrF (x : ℝ) : Integrable (fun t : ℝ => r t*F (x-t)) :=
    hr.mul_bdd (hF.comp_measurePreserving (Measure.measurePreserving_sub_left volume x))
      (Eventually.of_forall (fun t => hb (x-t)))
  exact convolution_assoc' (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ) (fun x y z => mul_assoc x y z)
    (hk.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hr)
    (Eventually.of_forall hrF) hi

end
end SixVertex
