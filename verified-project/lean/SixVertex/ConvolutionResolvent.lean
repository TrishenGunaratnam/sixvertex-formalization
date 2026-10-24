import SixVertex.ResolventKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology

/-- Associativity for two genuinely integrable kernels and a bounded
continuous right factor. The Fubini majorant is built from the two L1
kernels and the actual sup norm of the right factor. -/
theorem boundedConvolution_associativity (k r : ℝ → ℝ) (hk : Integrable k) (hr : Integrable r)
    (f : BoundedRealFunction) (u : ℝ) :
    (∫ t : ℝ, (∫ s : ℝ, k s*r (t-s))*f (u-t))=
      ∫ s : ℝ, k s*(∫ t : ℝ, r t*f ((u-s)-t)) := by
  have hi0 : Integrable (fun p : ℝ×ℝ => k p.2*r (p.1-p.2)) (volume.prod volume) :=
    hk.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hr
  have hi : Integrable (fun p : ℝ×ℝ => k p.2*(r (p.1-p.2)*f (u-p.1))) (volume.prod volume) := by
    have hb := hi0.mul_bdd ((f.continuous.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable)
      (Eventually.of_forall (fun p : ℝ×ℝ => f.norm_coe_le_norm (u-p.1)))
    convert hb using 1
    funext p
    change k p.2*(r (p.1-p.2)*f (u-p.1))=(k p.2*r (p.1-p.2))*f (u-p.1)
    ring
  exact convolution_assoc' (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ) (fun x y z => mul_assoc x y z)
    (hk.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hr)
    (Eventually.of_forall (fun x => boundedConvolution_integrand_integrable r hr f x)) hi

theorem physicalResolventKernel_operator_identity (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (f : BoundedRealFunction) :
    boundedConvolution (fun x => physicalResolventKernel lam h0 hpi x)
        (physicalResolventKernel_decay lam h0 hpi).1 f+
      boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
        (boundedConvolution (fun x => physicalResolventKernel lam h0 hpi x)
          (physicalResolventKernel_decay lam h0 hpi).1 f)=
      boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi) f := by
  let R : ℝ → ℝ := fun x => physicalResolventKernel lam h0 hpi x
  have hR : Integrable R := (physicalResolventKernel_decay lam h0 hpi).1
  have hK := kernelK_integrable lam h0 hpi
  have hKR : Integrable (fun t : ℝ => ∫ s : ℝ, kernelK lam s*R (t-s)) :=
    hK.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hR
  ext u
  change (∫ t : ℝ, R t*f (u-t))+
    (∫ s : ℝ, kernelK lam s*(∫ t : ℝ, R t*f ((u-s)-t)))=(∫ t : ℝ, kernelK lam t*f (u-t))
  rw [← boundedConvolution_associativity (kernelK lam) R hK hR f u,
    ← integral_add (boundedConvolution_integrand_integrable R hR f u)
      (boundedConvolution_integrand_integrable _ hKR f u)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change R t*f (u-t)+(∫ s : ℝ, kernelK lam s*R (t-s))*f (u-t)=kernelK lam t*f (u-t)
    rw [← add_mul]
    exact congrArg (fun v : ℝ => v*f (u-t)) (physicalResolventKernel_equation lam h0 hpi t))

/-- The inverse on bounded continuous functions is exactly convolution
by identity minus the constructed resolvent kernel. -/
theorem physicalInverse_resolvent_representation (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (f : BoundedRealFunction) :
    boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) f=
      f-boundedConvolution (fun x => physicalResolventKernel lam h0 hpi x)
        (physicalResolventKernel_decay lam h0 hpi).1 f := by
  let A := boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
  let T := boundedConvolution (fun x => physicalResolventKernel lam h0 hpi x)
    (physicalResolventKernel_decay lam h0 hpi).1 f
  have he : T+A T=A f := physicalResolventKernel_operator_identity lam h0 hpi f
  have hs : (f-T)+A (f-T)=f := by
    rw [map_sub]
    rw [← he]
    abel
  have hi := congrArg (fun S : BoundedRealFunction →L[ℝ] BoundedRealFunction => S (f-T))
    (boundedConvolutionInverse_left (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
  change boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) ((f-T)+A (f-T))=f-T at hi
  rw [hs] at hi
  exact hi

end
end SixVertex
