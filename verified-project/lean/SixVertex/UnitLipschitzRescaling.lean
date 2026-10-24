import SixVertex.ArrayQuadrature

namespace SixVertex
noncomputable section
open MeasureTheory Set
open scoped NNReal

/-- Every bounded Lipschitz real test is a positive scalar multiple of
a unit bounded-Lipschitz test, with the same zero set. -/
theorem exists_unit_lipschitz_rescaling (psi : BoundedRealFunction) (K : ℝ≥0)
    (hLip : LipschitzWith K (fun x => psi x)) :
    ∃ (D : ℝ) (phi : BoundedRealFunction), 0 < D ∧ LipschitzWith 1 (fun x => phi x) ∧
      ‖phi‖ ≤ 1 ∧ (∀ x, psi x=D*phi x) ∧ (∀ x, psi x=0 → phi x=0) := by
  let D : ℝ := 1+‖psi‖+(K : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hNorm : ‖psi‖ ≤ D := by dsimp [D]; linarith [K.coe_nonneg]
  have hK : (K : ℝ) ≤ D := by dsimp [D]; linarith [norm_nonneg psi]
  let phi : BoundedRealFunction := D⁻¹ • psi
  have happ (x : ℝ) : phi x=psi x/D := by change D⁻¹*psi x=psi x/D; ring
  refine ⟨D,phi,hD,?_,?_,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change |phi x-phi y| ≤ ((1 : ℝ≥0) : ℝ)*|x-y|
    rw [happ,happ,← sub_div,abs_div,abs_of_pos hD]
    have hp : |psi x-psi y| ≤ (K : ℝ)*|x-y| := by simpa only [Real.dist_eq] using hLip.dist_le_mul x y
    calc
      _ ≤ ((K : ℝ)*|x-y|)/D := div_le_div_of_nonneg_right hp hD.le
      _ ≤ 1*|x-y| := by
        apply (div_le_iff₀ hD).mpr
        nlinarith [mul_le_mul_of_nonneg_right hK (abs_nonneg (x-y))]
  · apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro x
    rw [Real.norm_eq_abs,happ,abs_div,abs_of_pos hD]
    apply (div_le_one hD).mpr
    have hb : |psi x| ≤ ‖psi‖ := by simpa only [Real.norm_eq_abs] using psi.norm_coe_le_norm x
    exact hb.trans hNorm
  · intro x
    rw [happ]
    field_simp
  · intro x hx
    rw [happ,hx,zero_div]

end
end SixVertex
