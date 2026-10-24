import SixVertex.FiniteBetheData
import Mathlib.LinearAlgebra.Matrix.Block

namespace SixVertex

noncomputable def replaceColumns {I : Type*} [Fintype I] [DecidableEq I]
    (G M : Matrix I I ℂ) (H : Finset I) : Matrix I I ℂ :=
  Matrix.of (fun i j => if j ∈ H then M i j else G i j)

/-- Expanding unchanged unit columns leaves the selected principal minor.
Using the same subtype order for rows and columns fixes the sign. -/
theorem det_replace_identity {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (H : Finset I) :
    (replaceColumns 1 M H).det = (M.submatrix (fun i : H => i.val) (fun j : H => j.val)).det := by
  classical
  rw [Matrix.twoBlockTriangular_det' _ (fun i => i ∈ H)]
  · have he : Matrix.toSquareBlockProp (replaceColumns 1 M H) (fun i => i ∈ H) =
        M.submatrix (fun i : H => i.val) (fun j : H => j.val) := by
      ext i j
      simp [Matrix.toSquareBlockProp, replaceColumns, j.property]
    rw [he]
    have hc : Matrix.toSquareBlockProp (replaceColumns 1 M H) (fun i => ¬ i ∈ H) = 1 := by
      ext i j
      simp [Matrix.toSquareBlockProp, replaceColumns, j.property, Matrix.one_apply, Subtype.ext_iff]
    rw [hc, Matrix.det_one, mul_one]
    exact congrArg (fun inst : Fintype H => @Matrix.det H _ inst ℂ _
      (M.submatrix (fun i : H => i.val) (fun j : H => j.val))) (Subsingleton.elim _ _)
  · intro i hi j hj
    simp [replaceColumns, hj, Matrix.one_apply, show i ≠ j from fun h => hj (h ▸ hi)]

/-- The deleted-column determinant identity, with no spectral assumptions. -/
theorem det_replace_columns {I : Type*} [Fintype I] [DecidableEq I]
    (G M : Matrix I I ℂ) (hG : G.det ≠ 0) (H : Finset I) :
    (replaceColumns G M H).det / G.det =
      ((G⁻¹*M).submatrix (fun i : H => i.val) (fun j : H => j.val)).det := by
  classical
  have hfactor : replaceColumns G M H = G * replaceColumns 1 (G⁻¹*M) H := by
    ext i j
    by_cases hj : j ∈ H
    · simp only [replaceColumns, Matrix.of_apply, hj, if_true, Matrix.mul_apply]
      have he := congrFun (congrFun (show G*(G⁻¹*M) = M by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG), one_mul]) i) j
      exact he.symm
    · simp [replaceColumns, Matrix.mul_apply, hj, Matrix.one_apply]
  rw [hfactor, Matrix.det_mul, mul_div_cancel_left₀ _ hG, det_replace_identity]

/-- Row weighting in an arbitrary selected minor. -/
theorem det_weighted_minor {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (ell : I → ℂ) (H : Finset I) :
    ((Matrix.diagonal ell * M).submatrix (fun i : H => i.val) (fun j : H => j.val)).det =
      (∏ i : H, ell i.val) * (M.submatrix (fun i : H => i.val) (fun j : H => j.val)).det := by
  have he : (Matrix.diagonal ell * M).submatrix (fun i : H => i.val) (fun j : H => j.val) =
      Matrix.of (fun i j : H => ell i.val * M i.val j.val) := by
    ext i j
    simp
  rw [he]
  exact Matrix.det_mul_column (fun i : H => ell i.val)
    (M.submatrix (fun i : H => i.val) (fun j : H => j.val))

end SixVertex
