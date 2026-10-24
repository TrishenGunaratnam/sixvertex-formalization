import SixVertex.FiniteIntervalSymmetry
import SixVertex.CountingPrimitive

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def physicalCountingPhaseFunction (lam : ℝ) : BoundedRealFunction :=
  phasePrimitiveFunction lam-BoundedContinuousFunction.const ℝ (phaseEnd lam)

theorem physicalCountingPhaseFunction_apply (lam u : ℝ) :
    physicalCountingPhaseFunction lam u=countingTheta lam u := by
  change (barePhase lam u+phaseEnd lam)-phaseEnd lam=countingTheta lam u
  rw [add_sub_cancel_right]
  rfl

theorem physicalCountingPhaseFunction_hasDerivAt (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u : ℝ) :
    HasDerivAt (fun v => physicalCountingPhaseFunction lam v) (physicalKernelFunction lam h0 hpi u) u := by
  simp_rw [physicalCountingPhaseFunction_apply]
  exact hasDerivAt_countingTheta lam u h0 hpi

def finiteIntervalPhaseIntegral (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) : BoundedRealFunction :=
  boundedConvolution (windowedFunction Q (finiteIntervalDensity lam h0 hpi Q))
    (windowedFunction_integrable Q _) (physicalCountingPhaseFunction lam)

theorem finiteIntervalPhaseIntegral_apply (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    finiteIntervalPhaseIntegral lam h0 hpi Q u=
      ∫ v in Icc (-Q) Q, countingTheta lam (u-v)*finiteIntervalDensity lam h0 hpi Q v := by
  change (∫ v : ℝ, windowedFunction Q (finiteIntervalDensity lam h0 hpi Q) v*physicalCountingPhaseFunction lam (u-v))=_
  simp_rw [physicalCountingPhaseFunction_apply]
  have he : (fun v => windowedFunction Q (finiteIntervalDensity lam h0 hpi Q) v*countingTheta lam (u-v))=
      (Icc (-Q) Q).indicator (fun v => countingTheta lam (u-v)*finiteIntervalDensity lam h0 hpi Q v) := by
    funext v
    by_cases hv : v ∈ Icc (-Q) Q <;> simp [windowedFunction,hv,mul_comm]
  rw [he,integral_indicator measurableSet_Icc]

theorem finiteIntervalPhaseIntegral_hasDerivAt (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    HasDerivAt (fun v => finiteIntervalPhaseIntegral lam h0 hpi Q v)
      (physicalWindowOperator lam h0 hpi Q (finiteIntervalDensity lam h0 hpi Q) u) u := by
  have h := boundedConvolutionValue_hasDerivAt (windowedFunction Q (finiteIntervalDensity lam h0 hpi Q))
    (windowedFunction_integrable Q _) (physicalCountingPhaseFunction lam) (physicalKernelFunction lam h0 hpi)
    (physicalCountingPhaseFunction_hasDerivAt lam h0 hpi) u
  have he : boundedConvolutionValue (windowedFunction Q (finiteIntervalDensity lam h0 hpi Q))
      (physicalKernelFunction lam h0 hpi) u=
      physicalWindowOperator lam h0 hpi Q (finiteIntervalDensity lam h0 hpi Q) u := by
    change (∫ v : ℝ, windowedFunction Q (finiteIntervalDensity lam h0 hpi Q) v*kernelK lam (u-v))=
      ∫ v : ℝ, kernelK lam (u-v)*windowedFunction Q (finiteIntervalDensity lam h0 hpi Q) v
    simp only [mul_comm]
  rw [he] at h
  exact h

def finiteIntervalMeanfield (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q u : ℝ) : ℝ :=
  countingS lam u-finiteIntervalPhaseIntegral lam h0 hpi Q u

theorem finiteIntervalMeanfield_hasDerivAt (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    HasDerivAt (finiteIntervalMeanfield lam h0 hpi Q) (finiteIntervalDensity lam h0 hpi Q u) u := by
  have h := (hasDerivAt_countingS lam u h0 hpi).sub (finiteIntervalPhaseIntegral_hasDerivAt lam h0 hpi Q u)
  have he := finiteIntervalDensity_equation lam h0 hpi Q u
  rw [← physicalWindowOperator_apply lam h0 hpi Q (finiteIntervalDensity lam h0 hpi Q) u] at he
  have heval : kernelS lam u-physicalWindowOperator lam h0 hpi Q (finiteIntervalDensity lam h0 hpi Q) u=
      finiteIntervalDensity lam h0 hpi Q u := by linarith
  rw [heval] at h
  exact h

theorem finiteIntervalPhaseIntegral_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (hQ : 0 ≤ Q) : finiteIntervalPhaseIntegral lam h0 hpi Q 0=0 := by
  rw [finiteIntervalPhaseIntegral_apply]
  simp only [zero_sub]
  let g : ℝ → ℝ := fun v => countingTheta lam (-v)*finiteIntervalDensity lam h0 hpi Q v
  have hg (v : ℝ) : g (-v)= -g v := by
    dsimp [g]
    rw [neg_neg,finiteIntervalDensity_neg lam h0 hpi Q hQ v]
    simp only [countingTheta,barePhase_neg]
    ring
  have hs := symmetric_Icc_integral_neg g Q hQ
  simp_rw [hg] at hs
  rw [integral_neg] at hs
  change (∫ v in Icc (-Q) Q, g v)=0
  linarith

/-- Exact reference meanfield identity, including its additive constant.
It uses the actual integral equation and evenness, not a supplied density
formula or an assumed phase normalization. -/
theorem finiteIntervalMeanfield_eq_cumulative (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (hQ : 0 ≤ Q) (u : ℝ) :
    finiteIntervalMeanfield lam h0 hpi Q u=
      finiteIntervalCumulative lam h0 hpi Q u-finiteIntervalMass lam h0 hpi Q/2 := by
  have hd (v : ℝ) : HasDerivAt
      (fun x => finiteIntervalMeanfield lam h0 hpi Q x-finiteIntervalCumulative lam h0 hpi Q x) 0 v := by
    convert (finiteIntervalMeanfield_hasDerivAt lam h0 hpi Q v).sub
      (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q v) using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun v => (hd v).differentiableAt) (fun v => (hd v).deriv) u 0
  change finiteIntervalMeanfield lam h0 hpi Q u-finiteIntervalCumulative lam h0 hpi Q u=
    finiteIntervalMeanfield lam h0 hpi Q 0-finiteIntervalCumulative lam h0 hpi Q 0 at hc
  rw [finiteIntervalCumulative_zero lam h0 hpi Q hQ] at hc
  have hzero : finiteIntervalMeanfield lam h0 hpi Q 0=0 := by
    unfold finiteIntervalMeanfield
    rw [finiteIntervalPhaseIntegral_zero lam h0 hpi Q hQ]
    simp [countingS]
  rw [hzero] at hc
  linarith

end
end SixVertex
