import SixVertex.FullLineDensity
import SixVertex.PositiveNeumann

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem negative_physicalFullOperator_nonnegative (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (f : BoundedRealFunction) (hf : ∀ x, 0 ≤ f x) (u : ℝ) :
    0 ≤ (-(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))) f u := by
  change 0 ≤ -(∫ t : ℝ, kernelK lam t*f (u-t))
  apply neg_nonneg.mpr
  exact integral_nonpos (fun t => mul_nonpos_of_nonpos_of_nonneg
    (kernelK_nonpos lam t hhalf hpi) (hf (u-t)))

theorem physicalFullInverse_nonnegative (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (f : BoundedRealFunction) (hf : ∀ x, 0 ≤ f x) (u : ℝ) :
    0 ≤ boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) f u := by
  have hn : ‖-(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))‖ < 1 := by
    exact (norm_neg (boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))).trans_lt
      ((boundedConvolutionOperator_norm_bound (kernelK lam) (kernelK_integrable lam h0 hpi)).trans_lt
        (kernelK_L1_mass_lt_one lam h0 hpi))
  exact positive_operator_neumann_nonnegative _ hn
    (negative_physicalFullOperator_nonnegative lam h0 hhalf hpi) f hf u

theorem fullLineDensityFunction_ge_source (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    kernelS lam u ≤ fullLineDensityFunction lam h0 hpi u := by
  have hr : ∀ v, 0 ≤ fullLineDensityFunction lam h0 hpi v :=
    physicalFullInverse_nonnegative lam h0 hhalf hpi (physicalSourceFunction lam h0 hpi)
      (fun v => by rw [physicalSourceFunction_apply]; exact (kernelS_pos lam v h0 hpi).le)
  have he := congrArg (fun f : BoundedRealFunction => f u) (fullLineDensityFunction_equation lam h0 hpi)
  change fullLineDensityFunction lam h0 hpi u+
    (∫ t : ℝ, kernelK lam t*fullLineDensityFunction lam h0 hpi (u-t))=physicalSourceFunction lam h0 hpi u at he
  rw [physicalSourceFunction_apply] at he
  have hk : (∫ t : ℝ, kernelK lam t*fullLineDensityFunction lam h0 hpi (u-t)) ≤ 0 :=
    integral_nonpos (fun t => mul_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam t hhalf hpi) (hr (u-t)))
  linarith

theorem fullLineDensityFunction_pos (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    0 < fullLineDensityFunction lam h0 hpi u :=
  (kernelS_pos lam u h0 hpi).trans_le (fullLineDensityFunction_ge_source lam h0 hhalf hpi u)

end
end SixVertex
