import SixVertex.MeasurableResolventIdentity
import SixVertex.FullLineDensity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

/-- The actual finite-window inverse satisfies the exterior-resolvent
fixed-point equation, for every physical parameter. -/
theorem physicalWindowInverse_exterior_equation (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (s : BoundedRealFunction) :
    physicalWindowInverse lam h0 hpi Q s=
      boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) s+
      exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
        (physicalResolventKernel_decay lam h0 hpi).1 Q (physicalWindowInverse lam h0 hpi Q s) := by
  let g := physicalWindowInverse lam h0 hpi Q s
  let B := boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
  let P := physicalWindowOperator lam h0 hpi Q
  let A := exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
    (physicalResolventKernel_decay lam h0 hpi).1 Q
  have hs : g+P g=s := physicalWindowInverse_solves lam h0 hpi Q s
  have ha : A g+B (A g)=B g-P g := exterior_physicalResolvent_operator_identity lam h0 hpi Q g
  have he : (g-A g)+B (g-A g)=s := by
    rw [map_sub]
    linear_combination hs-ha
  have hi := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T (g-A g))
    (boundedConvolutionInverse_left (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
  change boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
    ((g-A g)+B (g-A g))=g-A g at hi
  rw [he] at hi
  change g=_+A g
  rw [hi]
  abel

/-- The whole-line inverse of the constant source is the actual constant
one over the signed zero-frequency multiplier. -/
theorem physicalInverse_one_constant (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
      (BoundedContinuousFunction.const ℝ (1 : ℝ))=
      BoundedContinuousFunction.const ℝ (1/(2*(1-lam/Real.pi))) := by
  let c : ℝ := 1/(2*(1-lam/Real.pi))
  let g : BoundedRealFunction := BoundedContinuousFunction.const ℝ c
  have hd : 0 < 1-lam/Real.pi := sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi)
  have he : g+boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi) g=
      BoundedContinuousFunction.const ℝ (1 : ℝ) := by
    ext u
    change c+(∫ t : ℝ,kernelK lam t*c)=1
    rw [integral_mul_const,integral_kernelK lam h0 hpi]
    have hm : 1-2*lam/Real.pi=2*(1-lam/Real.pi)-1 := by ring
    rw [hm]
    dsimp [c]
    field_simp [hd.ne']
    <;> ring
  have hi := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T g)
    (boundedConvolutionInverse_left (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
  change boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
    (g+boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi) g)=g at hi
  rw [he] at hi
  exact hi

/-- The density used in the paper is already the exterior-resolvent
extension; no additional assumed density is introduced. -/
theorem finiteIntervalDensity_exterior_equation (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) :
    finiteIntervalDensity lam h0 hpi Q=fullLineDensityFunction lam h0 hpi+
      exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
        (physicalResolventKernel_decay lam h0 hpi).1 Q (finiteIntervalDensity lam h0 hpi Q) :=
  physicalWindowInverse_exterior_equation lam h0 hpi Q (physicalSourceFunction lam h0 hpi)

/-- The second actual finite-window solution has the matching exterior
fixed-point equation with its proved whole-line constant source. -/
theorem finiteIntervalOne_exterior_equation (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) :
    finiteIntervalOne lam h0 hpi Q=BoundedContinuousFunction.const ℝ (1/(2*(1-lam/Real.pi)))+
      exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
        (physicalResolventKernel_decay lam h0 hpi).1 Q (finiteIntervalOne lam h0 hpi Q) := by
  have he := physicalWindowInverse_exterior_equation lam h0 hpi Q (BoundedContinuousFunction.const ℝ (1 : ℝ))
  rw [physicalInverse_one_constant lam h0 hpi] at he
  exact he

end
end SixVertex
