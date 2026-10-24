import SixVertex.SlaterEigen
import SixVertex.FreeFermionMomentum

namespace SixVertex
noncomputable section

/-- One physical plane wave on the integer covering of the periodic chain. -/
def freePlaneWave (p : ℝ) (x : ℤ) : ℂ := Complex.exp (Complex.I*(p : ℂ)*(x : ℂ))

theorem freePlaneWave_add (p : ℝ) (x a : ℤ) :
    freePlaneWave p (x+a)=freePlaneWave p x*freePlaneWave p a := by
  simp only [freePlaneWave,Int.cast_add,mul_add,Complex.exp_add]

/-- Exact dispersion of the nearest-neighbor hopping operator. -/
theorem freePlaneWave_energy (p : ℝ) (x : ℤ) :
    -(1/2 : ℂ)*(freePlaneWave p (x+1)+freePlaneWave p (x-1))=
      -(Real.cos p : ℂ)*freePlaneWave p x := by
  rw [show x-1=x+(-1) by ring,freePlaneWave_add,freePlaneWave_add]
  have he : freePlaneWave p 1+freePlaneWave p (-1)=2*(Real.cos p : ℂ) := by
    simp only [freePlaneWave,Int.cast_one,Int.cast_neg,mul_one,mul_neg]
    rw [mul_comm Complex.I (p : ℂ)]
    simpa only [neg_mul,Complex.ofReal_cos] using (Complex.two_cos (p : ℂ)).symm
  calc
    _ = -(1/2 : ℂ)*freePlaneWave p x*(freePlaneWave p 1+freePlaneWave p (-1)) := by ring
    _ = _ := by rw [he];ring

/-- The actual consecutive-root grid gives exactly the fermionic circle sign
for every integer position,including negative positions on the cover. -/
theorem freePlaneWave_consecutive_periodicity {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (j : Fin n) (x : ℤ) :
    freePlaneWave (physicalRootMomentum (Real.pi/2) (Y j)) (x+(L : ℤ))=
      (-1 : ℂ)^(n-1)*freePlaneWave (physicalRootMomentum (Real.pi/2) (Y j)) x := by
  rw [freePlaneWave_add]
  have hp := consecutiveRoots_freeFermion_circle_sign L hL Y hY j
  have he : freePlaneWave (physicalRootMomentum (Real.pi/2) (Y j)) (L : ℤ)=
      (-1 : ℂ)^(n-1) := by
    convert hp using 1
    simp only [freePlaneWave,Int.cast_natCast,Complex.ofReal_mul,Complex.ofReal_natCast]
    congr 1
    ring
  rw [he,mul_comm]

/-- The free hopping Hamiltonian on labeled integer particle coordinates.
Collision and periodic boundary identifications are separate restrictions. -/
def freeCoordinateHamiltonian {I : Type*} [Fintype I] [DecidableEq I]
    (psi : (I → ℤ) → ℂ) (x : I → ℤ) : ℂ :=
  -(1/2 : ℂ)*(∑ i,(psi (Function.update x i (x i+1))+psi (Function.update x i (x i-1))))

def freeSlaterWave {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ) : (I → ℤ) → ℂ :=
  slaterWave (fun j => freePlaneWave (p j))

/-- Antisymmetrized physical plane waves solve the exact free coordinate
Hamiltonian with the sum of the one-particle energies. This theorem does
not yet identify the coordinate operator with the spin-sector restriction. -/
theorem freeSlaterWave_energy {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (x : I → ℤ) :
    freeCoordinateHamiltonian (freeSlaterWave p) x=
      (∑ j,-(Real.cos (p j) : ℂ))*freeSlaterWave p x := by
  classical
  let M : Matrix I I ℂ := fun i j => freePlaneWave (p j) (x i)
  have hu (i : I) (y : ℤ) : freeSlaterWave p (Function.update x i y)=
      (M.updateRow i (fun j => freePlaneWave (p j) y)).det := by
    unfold freeSlaterWave slaterWave
    congr 1
    ext k j
    by_cases hk : k=i
    · subst k;simp [M,Matrix.updateRow]
    · simp [M,Matrix.updateRow,Function.update,hk]
  unfold freeCoordinateHamiltonian
  rw [Finset.mul_sum]
  simp_rw [hu]
  calc
    _ = ∑ i,(M.updateRow i (-(1/2 : ℂ) •
        ((fun j => freePlaneWave (p j) (x i+1))+(fun j => freePlaneWave (p j) (x i-1))))).det := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.det_updateRow_smul,Matrix.det_updateRow_add]
    _ = ∑ i,(M.updateRow i (fun j => -(Real.cos (p j) : ℂ)*M i j)).det := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      funext j
      exact freePlaneWave_energy (p j) (x i)
    _ = _ := sum_det_updateRow_column_weights M (fun j => -(Real.cos (p j) : ℂ))

end
end SixVertex
