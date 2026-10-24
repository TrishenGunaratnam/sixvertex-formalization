import SixVertex.PositiveGroundState
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace SixVertex
noncomputable section

/-- The exact real quadratic energy of a finite matrix. -/
def realMatrixEnergy {V : Type*} [Fintype V] (A : Matrix V V ℝ) (v : V → ℝ) : ℝ :=
  ∑ i : V,∑ j : V,A i j*v i*v j

/-- Taking coordinatewise absolute values cannot increase energy when
every off-diagonal matrix entry is nonpositive. -/
theorem realMatrixEnergy_abs_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : ∀ i j,i≠j → A i j≤0) (v : V → ℝ) :
    realMatrixEnergy A (fun i => |v i|)≤realMatrixEnergy A v := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i=j
  · subst j
    apply le_of_eq
    calc
      A i i*|v i| *|v i|=A i i*(|v i|^2) := by ring
      _ = A i i*(v i)^2 := by rw [sq_abs]
      _ = _ := by ring
  · have hp : v i*v j≤|v i| *|v j| := by rw [← abs_mul];exact le_abs_self _
    simpa only [mul_assoc] using mul_le_mul_of_nonpos_left hp (hA i j hij)

/-- Coordinatewise absolute values in the actual Euclidean space. -/
def realAbsVector {V : Type*} (x : EuclideanSpace ℝ V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun i => |x i|)

/-- Absolute values preserve the Euclidean norm exactly. -/
theorem realAbsVector_norm {V : Type*} [Fintype V] (x : EuclideanSpace ℝ V) :
    ‖realAbsVector x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,realAbsVector,PiLp.toLp_apply,sq_abs]

/-- The finite quadratic energy is the inner-product energy of the
actual matrix operator on Euclidean space. -/
theorem realMatrixEnergy_eq_inner {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (x : EuclideanSpace ℝ V) :
    realMatrixEnergy A (fun i => x i)=inner ℝ (A.toEuclideanLin x) x := by
  simp only [realMatrixEnergy,PiLp.inner_apply,Real.inner_apply,Matrix.toEuclideanLin,
    Matrix.toLpLin_apply,PiLp.toLp_apply,Matrix.mulVec,dotProduct,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end SixVertex
