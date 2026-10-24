import SixVertex.FreeSlaterPositive
import Mathlib.GroupTheory.Perm.Fin

namespace SixVertex
noncomputable section

/-- Exact antisymmetry under a permutation of labeled particle coordinates. -/
theorem freeSlaterWave_permute_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (x : I → ℤ) (e : Equiv.Perm I) :
    freeSlaterWave p (fun i => x (e i))=((e.sign : ℤ) : ℂ)*freeSlaterWave p x := by
  exact Matrix.det_permute e (fun i j => freePlaneWave (p j) (x i))

/-- Taking one particle once around the covering line produces exactly
the fermionic sign dictated by the actual consecutive roots. -/
theorem freeSlaterWave_coordinate_period {particles : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (x : Fin particles → ℤ) (i : Fin particles) :
    freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j))
      (Function.update x i (x i+(L : ℤ)))=
      (-1 : ℂ)^(particles-1)*freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) x := by
  classical
  let M : Matrix (Fin particles) (Fin particles) ℂ :=
    fun k j => freePlaneWave (physicalRootMomentum (Real.pi/2) (Y j)) (x k)
  have hu : freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j))
      (Function.update x i (x i+(L : ℤ)))=
      (M.updateRow i (((-1 : ℂ)^(particles-1)) • M i)).det := by
    unfold freeSlaterWave slaterWave
    apply congrArg Matrix.det
    ext k j
    by_cases hk : k=i
    · subst k
      simpa [Matrix.updateRow,Function.update,M] using freePlaneWave_consecutive_periodicity L hL Y hY j (x i)
    · simp [Matrix.updateRow,Function.update,hk,M]
  rw [hu,Matrix.det_updateRow_smul,Matrix.updateRow_eq_self]
  rfl

/-- Passing the first particle around the circle and putting it last
has no sign: the physical circle phase cancels the cyclic determinant sign. -/
theorem freeSlaterWave_cyclic_wrap (n : ℕ) (L : ℕ) (hL : 0<L)
    (Y : Fin (n+1) → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (x : Fin (n+1) → ℤ) :
    freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j))
      (Fin.snoc (fun i => x i.succ) (x 0+(L : ℤ)))=
      freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) x := by
  let g := Function.update x 0 (x 0+(L : ℤ))
  have hg : Fin.cons (x 0+(L : ℤ)) (fun i => x i.succ)=g := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [g]
    · simp [g,Fin.succ_ne_zero]
  have hr : Fin.snoc (fun i => x i.succ) (x 0+(L : ℤ))=
      fun i => g (finRotate (n+1) i) := by
    rw [Fin.snoc_eq_cons_rotate,hg]
  have hs : (((finRotate (n+1)).sign : ℤ) : ℂ)=(-1 : ℂ)^n := by
    rw [sign_finRotate]
    simp
  rw [hr,freeSlaterWave_permute_coordinates,hs]
  change (-1 : ℂ)^n*freeSlaterWave _ (Function.update x 0 (x 0+(L : ℤ)))=_
  rw [freeSlaterWave_coordinate_period L hL Y hY x 0]
  simp only [Nat.add_sub_cancel]
  have hp : (-1 : ℂ)^n*(-1)^n=1 := by
    rw [← pow_add,← two_mul,pow_mul]
    norm_num
  rw [← mul_assoc,hp,one_mul]

end
end SixVertex
