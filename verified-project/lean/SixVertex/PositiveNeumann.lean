import SixVertex.BoundedConvolution
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Pointwise positivity of an actual norm-convergent Neumann inverse.
The premise is positivity of the operator, not of its formal multiplier. -/
theorem positive_operator_neumann_nonnegative (A : BoundedRealFunction →L[ℝ] BoundedRealFunction)
    (hA : ‖A‖ < 1)
    (hpos : ∀ f : BoundedRealFunction, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ A f x)
    (f : BoundedRealFunction) (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ (∑' m : ℕ, A^m) f x := by
  have hs : Summable (fun m : ℕ => A^m) := summable_geometric_of_norm_lt_one (x := A) hA
  have hp (m : ℕ) : ∀ x, 0 ≤ (A^m) f x := by
    induction m with
    | zero => simpa only [pow_zero,one_apply_eq_self] using hf
    | succ m ih =>
      rw [pow_succ']
      exact hpos _ ih
  have he : (∑' m : ℕ, (A^m) f) x=∑' m : ℕ, (A^m) f x :=
    (BoundedContinuousFunction.evalCLM ℝ x).map_tsum (summable_apply hs f)
  rw [tsum_apply hs f,he]
  exact tsum_nonneg (fun m => hp m x)

/-- The same inverse is monotone between bounded continuous sources. -/
theorem positive_operator_neumann_monotone (A : BoundedRealFunction →L[ℝ] BoundedRealFunction)
    (hA : ‖A‖ < 1)
    (hpos : ∀ f : BoundedRealFunction, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ A f x)
    (f g : BoundedRealFunction) (hfg : ∀ x, f x ≤ g x) (x : ℝ) :
    (∑' m : ℕ, A^m) f x ≤ (∑' m : ℕ, A^m) g x := by
  have h := positive_operator_neumann_nonnegative A hA hpos (g-f) (fun x => sub_nonneg.mpr (hfg x)) x
  change 0 ≤ ((∑' m : ℕ, A^m) (g-f)) x at h
  rw [map_sub] at h
  exact sub_nonneg.mp h

end
end SixVertex
