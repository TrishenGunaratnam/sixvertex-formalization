import SixVertex.PositiveNeumann

namespace SixVertex
noncomputable section

/-- An actual bounded solution of g=f+A*g equals the convergent Neumann
solution when the operator is a strict contraction. -/
theorem positive_operator_fixed_point_representation
    (A : BoundedRealFunction →L[ℝ] BoundedRealFunction) (hA : ‖A‖ < 1)
    (f g : BoundedRealFunction) (heq : g=f+A g) :
    g=(∑' m : ℕ,A^m) f := by
  have he := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T g)
    (geom_series_mul_neg A hA)
  change (∑' m : ℕ,A^m) (g-A g)=g at he
  have hs : g-A g=f := sub_eq_iff_eq_add.mpr heq
  rw [hs] at he
  exact he.symm

/-- Positivity of the solution is deduced from the actual positive
operator, not from an alternating inverse. -/
theorem positive_operator_fixed_point_nonnegative
    (A : BoundedRealFunction →L[ℝ] BoundedRealFunction) (hA : ‖A‖ < 1)
    (hpos : ∀ f : BoundedRealFunction,(∀ x,0 ≤ f x) → ∀ x,0 ≤ A f x)
    (f g : BoundedRealFunction) (hf : ∀ x,0 ≤ f x) (heq : g=f+A g) (u : ℝ) :
    0 ≤ g u := by
  rw [positive_operator_fixed_point_representation A hA f g heq]
  exact positive_operator_neumann_nonnegative A hA hpos f hf u

/-- A pointwise supersolution bounds the actual fixed point uniformly. -/
theorem positive_operator_fixed_point_le_supersolution
    (A : BoundedRealFunction →L[ℝ] BoundedRealFunction) (hA : ‖A‖ < 1)
    (hpos : ∀ f : BoundedRealFunction,(∀ x,0 ≤ f x) → ∀ x,0 ≤ A f x)
    (f g v : BoundedRealFunction) (heq : g=f+A g)
    (hsuper : ∀ x,f x ≤ v x-A v x) (u : ℝ) : g u ≤ v u := by
  rw [positive_operator_fixed_point_representation A hA f g heq]
  have hm := positive_operator_neumann_monotone A hA hpos f (v-A v) hsuper u
  have he := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T v)
    (geom_series_mul_neg A hA)
  change (∑' m : ℕ,A^m) (v-A v)=v at he
  rw [he] at hm
  exact hm

end
end SixVertex
