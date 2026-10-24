import SixVertex.FiniteIntervalPositivity
import SixVertex.FullLineDensityPositivity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem physicalWindowOperator_antitone_Q (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (Q T : ℝ) (hQT : Q ≤ T) (f : BoundedRealFunction) (hf : ∀ x, 0 ≤ f x) (u : ℝ) :
    physicalWindowOperator lam h0 hpi T f u ≤ physicalWindowOperator lam h0 hpi Q f u := by
  have hi (P : ℝ) : Integrable (fun v : ℝ => kernelK lam (u-v)*windowedFunction P f v) :=
    bounded_measurable_convolution_integrable (kernelK lam) _ (kernelK_integrable lam h0 hpi)
      (windowedFunction_integrable P f).aestronglyMeasurable ‖f‖ (windowedFunction_norm_bound P f) u
  change (∫ v : ℝ, kernelK lam (u-v)*windowedFunction T f v) ≤
    ∫ v : ℝ, kernelK lam (u-v)*windowedFunction Q f v
  apply integral_mono (hi T) (hi Q)
  intro v
  by_cases hvQ : v ∈ Icc (-Q) Q
  · have hvT : v ∈ Icc (-T) T := ⟨by linarith [hvQ.1],by linarith [hvQ.2]⟩
    simp only [windowedFunction,Set.indicator_of_mem hvQ,Set.indicator_of_mem hvT]
    exact le_rfl
  · by_cases hvT : v ∈ Icc (-T) T
    · simp only [windowedFunction,Set.indicator_of_notMem hvQ,Set.indicator_of_mem hvT,mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam _ hhalf hpi) (hf v)
    · simp only [windowedFunction,Set.indicator_of_notMem hvQ,Set.indicator_of_notMem hvT]
      exact le_rfl

theorem physicalWindowOperator_full_comparison (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ)
    (f : BoundedRealFunction) (hf : ∀ x, 0 ≤ f x) (u : ℝ) :
    boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi) f u ≤
      physicalWindowOperator lam h0 hpi Q f u := by
  have he : boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi) f u=
      ∫ v : ℝ, kernelK lam (u-v)*f v := by
    change (∫ v : ℝ, kernelK lam v*f (u-v))=_
    rw [scalar_convolution_comm (kernelK lam) (fun x => f x) u]
    simp only [mul_comm]
  rw [he]
  have hi := bounded_measurable_convolution_integrable (kernelK lam) (fun v => f v)
    (kernelK_integrable lam h0 hpi) f.continuous.aestronglyMeasurable ‖f‖ f.norm_coe_le_norm u
  have hQ := bounded_measurable_convolution_integrable (kernelK lam) _ (kernelK_integrable lam h0 hpi)
    (windowedFunction_integrable Q f).aestronglyMeasurable ‖f‖ (windowedFunction_norm_bound Q f) u
  change (∫ v : ℝ, kernelK lam (u-v)*f v) ≤ ∫ v : ℝ, kernelK lam (u-v)*windowedFunction Q f v
  apply integral_mono hi hQ
  intro v
  by_cases hv : v ∈ Icc (-Q) Q
  · simp only [windowedFunction,Set.indicator_of_mem hv]
    exact le_rfl
  · simp only [windowedFunction,Set.indicator_of_notMem hv,mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam _ hhalf hpi) (hf v)

/-- Enlarging the interval increases the actual inverse-defined r_Q
in the negative-kernel regime, on its entire bounded extension. -/
theorem finiteIntervalDensity_monotone_Q (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (Q T : ℝ) (hQT : Q ≤ T) (u : ℝ) :
    finiteIntervalDensity lam h0 hpi Q u ≤ finiteIntervalDensity lam h0 hpi T u := by
  apply physicalWindowInverse_le_supersolution lam h0 hhalf hpi Q
    (physicalSourceFunction lam h0 hpi) (finiteIntervalDensity lam h0 hpi T) _ u
  intro x
  have he := congrArg (fun f : BoundedRealFunction => f x)
    (physicalWindowInverse_solves lam h0 hpi T (physicalSourceFunction lam h0 hpi))
  change finiteIntervalDensity lam h0 hpi T x+
    physicalWindowOperator lam h0 hpi T (finiteIntervalDensity lam h0 hpi T) x=
      physicalSourceFunction lam h0 hpi x at he
  have ho := physicalWindowOperator_antitone_Q lam h0 hhalf hpi Q T hQT
    (finiteIntervalDensity lam h0 hpi T) (fun v => (finiteIntervalDensity_pos lam h0 hhalf hpi T v).le) x
  linarith

/-- The full-line density is an actual supersolution of every finite
window equation. This proves r_Q <= r without a closed-form formula. -/
theorem finiteIntervalDensity_le_fullLineDensity (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    finiteIntervalDensity lam h0 hpi Q u ≤ fullLineDensityFunction lam h0 hpi u := by
  apply physicalWindowInverse_le_supersolution lam h0 hhalf hpi Q
    (physicalSourceFunction lam h0 hpi) (fullLineDensityFunction lam h0 hpi) _ u
  intro x
  have he := congrArg (fun f : BoundedRealFunction => f x) (fullLineDensityFunction_equation lam h0 hpi)
  change fullLineDensityFunction lam h0 hpi x+
    boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
      (fullLineDensityFunction lam h0 hpi) x=physicalSourceFunction lam h0 hpi x at he
  have ho := physicalWindowOperator_full_comparison lam h0 hhalf hpi Q
    (fullLineDensityFunction lam h0 hpi) (fun v => (fullLineDensityFunction_pos lam h0 hhalf hpi v).le) x
  linarith

end
end SixVertex
