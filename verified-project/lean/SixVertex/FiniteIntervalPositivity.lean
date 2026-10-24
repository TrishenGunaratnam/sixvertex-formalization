import SixVertex.FiniteIntervalDensity
import SixVertex.PositiveNeumann

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- The negative of the actual physical window operator preserves
pointwise nonnegativity when K is nonpositive. -/
theorem negative_physicalWindowOperator_nonnegative (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ)
    (f : BoundedRealFunction) (hf : ∀ x, 0 ≤ f x) (u : ℝ) :
    0 ≤ (-(physicalWindowOperator lam h0 hpi Q)) f u := by
  change 0 ≤ -(physicalWindowOperator lam h0 hpi Q f u)
  rw [physicalWindowOperator_apply]
  apply neg_nonneg.mpr
  exact integral_nonpos (fun v => mul_nonpos_of_nonpos_of_nonneg
    (kernelK_nonpos lam _ hhalf hpi) (hf v))

theorem physicalWindowInverse_nonnegative (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ)
    (f : BoundedRealFunction) (hf : ∀ x, 0 ≤ f x) (u : ℝ) :
    0 ≤ physicalWindowInverse lam h0 hpi Q f u := by
  have hn : ‖-(physicalWindowOperator lam h0 hpi Q)‖ < 1 := by
    exact (norm_neg (physicalWindowOperator lam h0 hpi Q)).trans_lt
      ((windowConvolutionOperator_norm_bound (physicalKernelFunction lam h0 hpi)
        (kernelK_integrable lam h0 hpi) Q).trans_lt (kernelK_L1_mass_lt_one lam h0 hpi))
  exact positive_operator_neumann_nonnegative _ hn
    (negative_physicalWindowOperator_nonnegative lam h0 hhalf hpi Q) f hf u

theorem physicalWindowInverse_monotone (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ)
    (f g : BoundedRealFunction) (hfg : ∀ x, f x ≤ g x) (u : ℝ) :
    physicalWindowInverse lam h0 hpi Q f u ≤ physicalWindowInverse lam h0 hpi Q g u := by
  have h := physicalWindowInverse_nonnegative lam h0 hhalf hpi Q (g-f)
    (fun x => sub_nonneg.mpr (hfg x)) u
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- A supersolution comparison for the actual finite-interval equation. -/
theorem physicalWindowInverse_le_supersolution (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ)
    (f g : BoundedRealFunction)
    (hfg : ∀ x, f x ≤ g x+physicalWindowOperator lam h0 hpi Q g x) (u : ℝ) :
    physicalWindowInverse lam h0 hpi Q f u ≤ g u := by
  have h := physicalWindowInverse_monotone lam h0 hhalf hpi Q f
    (g+physicalWindowOperator lam h0 hpi Q g) hfg u
  rw [physicalWindowInverse_solution_unique lam h0 hpi Q _ g rfl] at h
  exact h

/-- Positivity of r_Q follows from the positive Neumann series, rather
than from an unjustified alternating-series estimate. -/
theorem finiteIntervalDensity_ge_source (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    kernelS lam u ≤ finiteIntervalDensity lam h0 hpi Q u := by
  have hr : ∀ v, 0 ≤ finiteIntervalDensity lam h0 hpi Q v :=
    physicalWindowInverse_nonnegative lam h0 hhalf hpi Q (physicalSourceFunction lam h0 hpi)
      (fun v => by rw [physicalSourceFunction_apply]; exact (kernelS_pos lam v h0 hpi).le)
  have hk : (∫ v in Icc (-Q) Q, kernelK lam (u-v)*finiteIntervalDensity lam h0 hpi Q v) ≤ 0 :=
    integral_nonpos (fun v => mul_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam _ hhalf hpi) (hr v))
  linarith [finiteIntervalDensity_equation lam h0 hpi Q u]

theorem finiteIntervalDensity_pos (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    0 < finiteIntervalDensity lam h0 hpi Q u :=
  (kernelS_pos lam u h0 hpi).trans_le (finiteIntervalDensity_ge_source lam h0 hhalf hpi Q u)

/-- The stated H_Q comparison holds uniformly in Q in the negative
kernel regime; all constants are explicit and independent of the interval. -/
theorem finiteIntervalOne_bounds (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    1 ≤ finiteIntervalOne lam h0 hpi Q u ∧
      finiteIntervalOne lam h0 hpi Q u ≤ (1-|1-2*lam/Real.pi|)⁻¹ := by
  have hh : ∀ v, 0 ≤ finiteIntervalOne lam h0 hpi Q v :=
    physicalWindowInverse_nonnegative lam h0 hhalf hpi Q (BoundedContinuousFunction.const ℝ (1 : ℝ))
      (fun _ => by norm_num)
  constructor
  · have hk : (∫ v in Icc (-Q) Q, kernelK lam (u-v)*finiteIntervalOne lam h0 hpi Q v) ≤ 0 :=
      integral_nonpos (fun v => mul_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam _ hhalf hpi) (hh v))
    linarith [finiteIntervalOne_equation lam h0 hpi Q u]
  · calc
      _ ≤ |finiteIntervalOne lam h0 hpi Q u| := le_abs_self _
      _ ≤ ‖finiteIntervalOne lam h0 hpi Q‖ := by
        simpa only [Real.norm_eq_abs] using (finiteIntervalOne lam h0 hpi Q).norm_coe_le_norm u
      _ ≤ _ := finiteIntervalOne_norm_bound lam h0 hpi Q

end
end SixVertex
