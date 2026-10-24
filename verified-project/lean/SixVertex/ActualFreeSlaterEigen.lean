import SixVertex.SlaterBlockedHops
import SixVertex.SpinSlaterHops
import SixVertex.SpinHoppingParticleSum

namespace SixVertex
noncomputable section

/-- The allowed right move and the blocked zero are a single exact
covering-coordinate Slater amplitude. -/
theorem spinFreeSlater_right_term {particles : ℕ} (length : ℕ) (hlen : 0<length)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) particles) (j : Fin particles) :
    (if rowSpinAt (length+1) q.val (finRotate (length+1) (occupiedIndex q j))=0 then
      spinFreeSlaterVector (length+1) Y (swapSpinSites q (occupiedIndex q j) (finRotate (length+1) (occupiedIndex q j))) else 0)=
      freeSlaterWave (fun k => physicalRootMomentum (Real.pi/2) (Y k))
        (Function.update (occupiedCoordinates q) j (occupiedCoordinates q j+1))/freeSlaterPhase particles := by
  by_cases hh : rowSpinAt (length+1) q.val (finRotate (length+1) (occupiedIndex q j))=0
  · rw [if_pos hh]
    exact spinFreeSlaterVector_right_hop length Y hY q j hh
  · have ho : rowSpinAt (length+1) q.val (finRotate (length+1) (occupiedIndex q j))=1 := by
      generalize rowSpinAt (length+1) q.val (finRotate (length+1) (occupiedIndex q j))=a at *
      fin_cases a <;> simp_all
    rw [if_neg hh,freeSlaterWave_blocked_right_zero length hlen Y hY q j ho,zero_div]

/-- The corresponding exact left-move identity,including all collisions. -/
theorem spinFreeSlater_left_term {particles : ℕ} (length : ℕ) (hlen : 0<length)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) particles) (j : Fin particles) :
    (if rowSpinAt (length+1) q.val ((finRotate (length+1)).symm (occupiedIndex q j))=0 then
      spinFreeSlaterVector (length+1) Y (swapSpinSites q (occupiedIndex q j) ((finRotate (length+1)).symm (occupiedIndex q j))) else 0)=
      freeSlaterWave (fun k => physicalRootMomentum (Real.pi/2) (Y k))
        (Function.update (occupiedCoordinates q) j (occupiedCoordinates q j-1))/freeSlaterPhase particles := by
  by_cases hh : rowSpinAt (length+1) q.val ((finRotate (length+1)).symm (occupiedIndex q j))=0
  · rw [if_pos hh]
    exact spinFreeSlaterVector_left_hop length Y hY q j hh
  · have ho : rowSpinAt (length+1) q.val ((finRotate (length+1)).symm (occupiedIndex q j))=1 := by
      generalize rowSpinAt (length+1) q.val ((finRotate (length+1)).symm (occupiedIndex q j))=a at *
      fin_cases a <;> simp_all
    rw [if_neg hh,freeSlaterWave_blocked_left_zero length hlen Y hY q j ho,zero_div]

/-- The actual spin-sector Hamiltonian acts on the constructed Slater state
by the proved free coordinate Hamiltonian. Every boundary and blocked case
has been proved;this is no longer an assumed correspondence. -/
theorem actual_free_slater_coordinate_action {particles : ℕ} (n : ℕ)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0)
    (q : ParticleConfigurations (n+2) particles) :
    (complexSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec (spinFreeSlaterVector (n+2) Y) q=
      freeCoordinateHamiltonian (freeSlaterWave (fun k => physicalRootMomentum (Real.pi/2) (Y k)))
        (occupiedCoordinates q)/freeSlaterPhase particles := by
  rw [complexSectorHamiltonian_freeFermion_particle_mulVec]
  have hr (j : Fin particles) := spinFreeSlater_right_term (n+1) (by omega) Y hY q j
  have hl (j : Fin particles) := spinFreeSlater_left_term (n+1) (by omega) Y hY q j
  simp only [finRotate_apply,finRotate_symm_apply] at hr hl
  simp_rw [hr,hl]
  unfold freeCoordinateHamiltonian
  simp_rw [← add_div]
  rw [← Finset.sum_div]
  ring

/-- The constructed positive spin-sector Slater vector satisfies the
ACTUAL free Hamiltonian eigenvalue equation with its exact physical energy. -/
theorem actual_free_slater_eigenvector {particles : ℕ} (n : ℕ)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (n+2) Y 0) :
    (complexSectorHamiltonian (Real.pi/2) (1/2) n particles).mulVec (spinFreeSlaterVector (n+2) Y)=
      (∑ k : Fin particles,-(Real.cos (physicalRootMomentum (Real.pi/2) (Y k)) : ℂ)) •
        spinFreeSlaterVector (n+2) Y := by
  funext q
  rw [actual_free_slater_coordinate_action n Y hY q,freeSlaterWave_energy]
  simp only [Pi.smul_apply,smul_eq_mul,spinFreeSlaterVector]
  ring

end
end SixVertex
