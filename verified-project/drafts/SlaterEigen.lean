import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

namespace SixVertex
noncomputable section
open scoped BigOperators

/-- Summing all one-row weighted updates counts each orbital energy once. -/
theorem sum_det_updateRow_column_weights {I R : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] (A : Matrix I I R) (e : I → R) :
    (∑ i, (A.updateRow i (fun j => e j*A i j)).det)=(∑ j,e j)*A.det := by
  classical
  have hp (s : Equiv.Perm I) (i : I) :
      (∏ j,(A.updateRow i (fun k => e k*A i k)) (s j) j)=
        e (s.symm i)*(∏ j,A (s j) j) := by
    have he (j : I) : (A.updateRow i (fun k => e k*A i k)) (s j) j=
        (if j=s.symm i then e j else 1)*A (s j) j := by
      by_cases hj : j=s.symm i
      · subst j
        simp
      · have hs : s j≠i := by intro h;exact hj ((s.eq_symm_apply).mpr h)
        simp [Matrix.updateRow_ne hs,hj]
    simp_rw [he]
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [Matrix.det_apply',hp]
  rw [Finset.sum_comm]
  calc
    _ = ∑ s : Equiv.Perm I, ((s.sign : ℤ) : R)*(∏ j,A (s j) j)*(∑ i,e (s.symm i)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ j,e j)*(∑ s : Equiv.Perm I, ((s.sign : ℤ) : R)*(∏ j,A (s j) j)) := by
      have hs (s : Equiv.Perm I) : (∑ i,e (s.symm i))=∑ i,e i := Equiv.sum_comp s.symm e
      simp_rw [hs]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- A finite Slater wave in labeled particle coordinates. -/
def slaterWave {I X R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (phi : I → X → R) (x : I → X) : R := Matrix.det (fun (i j : I) => phi j (x i))

/-- The sum of the one-particle operator acting in each coordinate. -/
def coordinateHamiltonian {I X R : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    [CommRing R] (A : Matrix X X R) (psi : (I → X) → R) (x : I → X) : R :=
  ∑ i,∑ y,A (x i) y*psi (Function.update x i y)

/-- Colliding particle coordinates vanish exactly by antisymmetry. -/
theorem slaterWave_collision_zero {I X R : Type*} [Fintype I] [DecidableEq I]
    [CommRing R] (phi : I → X → R) (x : I → X) (i j : I) (hij : i≠j) (hx : x i=x j) :
    slaterWave phi x=0 := by
  apply Matrix.det_zero_of_row_eq hij
  exact funext (fun k => congrArg (phi k) hx)

/-- The determinant of one-particle eigenfunctions is an exact eigenfunction
of the coordinate Hamiltonian,with the sum of their energies. -/
theorem slaterWave_coordinate_eigen {I X R : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [CommRing R] (A : Matrix X X R) (phi : I → X → R) (e : I → R)
    (hphi : ∀ j x,∑ y,A x y*phi j y=e j*phi j x) (x : I → X) :
    coordinateHamiltonian A (slaterWave phi) x=(∑ j,e j)*slaterWave phi x := by
  classical
  let M : Matrix I I R := fun i j => phi j (x i)
  have hu (i : I) (y : X) : slaterWave phi (Function.update x i y)=
      (M.updateRow i (fun j => phi j y)).det := by
    unfold slaterWave
    apply congrArg Matrix.det
    ext k j
    by_cases hk : k=i
    · subst k;simp [M,Matrix.updateRow]
    · simp [M,Matrix.updateRow,Function.update,hk]
  unfold coordinateHamiltonian
  simp_rw [hu]
  calc
    _ = ∑ i,(M.updateRow i (∑ y,A (x i) y • (fun j => phi j y))).det := by
      apply Finset.sum_congr rfl
      intro i _
      have hh := Matrix.detRowAlternating.map_update_sum (R:=R) Finset.univ i
        (fun y => A (x i) y • (fun j => phi j y)) M
      change _=(Matrix.detRowAlternating (Function.update M i _))
      rw [hh]
      apply Finset.sum_congr rfl
      intro y _
      exact (Matrix.det_updateRow_smul M i (A (x i) y) (fun j => phi j y)).symm
    _ = ∑ i,(M.updateRow i (fun j => e j*M i j)).det := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      funext j
      simpa [M] using hphi j (x i)
    _ = _ := sum_det_updateRow_column_weights M e

end
end SixVertex
