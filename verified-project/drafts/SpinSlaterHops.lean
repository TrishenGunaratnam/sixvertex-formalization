import SixVertex.SpinPeriodicAmplitudes
import Mathlib.Logic.Equiv.Fin.Rotate

namespace SixVertex
noncomputable section

theorem occupiedIndex_zero_index (length m : ℕ)
    (q : ParticleConfigurations (length+1) (m+1)) (j : Fin (m+1))
    (h : occupiedIndex q j=0) : j=0 := by
  by_contra hn
  have hjv : j.val≠0 := by intro h;exact hn (Fin.ext h)
  have hj : (0 : Fin (m+1))<j := by
    change (0 : Fin (m+1)).val<j.val
    simp only [Fin.val_zero]
    omega
  have hm := (occupiedIndex q).strictMono hj
  rw [h] at hm
  change (occupiedIndex q 0).val<0 at hm
  omega

theorem occupiedIndex_last_index (length m : ℕ)
    (q : ParticleConfigurations (length+1) (m+1)) (j : Fin (m+1))
    (h : occupiedIndex q j=Fin.last length) : j=Fin.last m := by
  by_contra hn
  have hj : j<Fin.last m := Fin.lt_last_iff_ne_last.mpr hn
  have hm := (occupiedIndex q).strictMono hj
  rw [h] at hm
  have htop := (occupiedIndex q (Fin.last m)).isLt
  change length<(occupiedIndex q (Fin.last m)).val at hm
  omega

/-- Uniform exact right-hop amplitude,including the periodic boundary. -/
theorem spinFreeSlaterVector_right_hop {particles : ℕ} (length : ℕ)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) particles) (j : Fin particles)
    (hhole : rowSpinAt (length+1) q.val (finRotate (length+1) (occupiedIndex q j))=0) :
    spinFreeSlaterVector (length+1) Y (swapSpinSites q (occupiedIndex q j) (finRotate (length+1) (occupiedIndex q j)))=
      freeSlaterWave (fun k => physicalRootMomentum (Real.pi/2) (Y k))
        (Function.update (occupiedCoordinates q) j (occupiedCoordinates q j+1))/freeSlaterPhase particles := by
  cases particles with
  | zero => exact Fin.elim0 j
  | succ m =>
    by_cases ha : occupiedIndex q j=Fin.last length
    · have hj := occupiedIndex_last_index length m q j ha
      subst j
      have hh : rowSpinAt (length+1) q.val 0=0 := by simpa only [ha,finRotate_last] using hhole
      simpa only [ha,finRotate_last] using spinFreeSlaterVector_wrap_right length m Y hY q ha hh
    · unfold spinFreeSlaterVector
      rw [occupiedCoordinates_swap_right q j _ hhole (coe_finRotate_of_ne_last ha)]

/-- Uniform exact left-hop amplitude,including the periodic boundary. -/
theorem spinFreeSlaterVector_left_hop {particles : ℕ} (length : ℕ)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) particles) (j : Fin particles)
    (hhole : rowSpinAt (length+1) q.val ((finRotate (length+1)).symm (occupiedIndex q j))=0) :
    spinFreeSlaterVector (length+1) Y (swapSpinSites q (occupiedIndex q j) ((finRotate (length+1)).symm (occupiedIndex q j)))=
      freeSlaterWave (fun k => physicalRootMomentum (Real.pi/2) (Y k))
        (Function.update (occupiedCoordinates q) j (occupiedCoordinates q j-1))/freeSlaterPhase particles := by
  cases particles with
  | zero => exact Fin.elim0 j
  | succ m =>
    by_cases ha : occupiedIndex q j=0
    · have hj := occupiedIndex_zero_index length m q j ha
      subst j
      have hr : (finRotate (length+1)).symm 0=Fin.last length := by
        apply (finRotate (length+1)).injective
        simp
      have hh : rowSpinAt (length+1) q.val (Fin.last length)=0 := by simpa only [ha,hr] using hhole
      simpa only [ha,hr] using spinFreeSlaterVector_wrap_left length m Y hY q ha hh
    · have hs : (occupiedIndex q j).val=((finRotate (length+1)).symm (occupiedIndex q j)).val+1 := by
        rw [coe_finRotate_symm_of_ne_zero ha]
        have hn : (occupiedIndex q j).val≠0 := by intro h;exact ha (Fin.ext h)
        omega
      unfold spinFreeSlaterVector
      rw [occupiedCoordinates_swap_left q j _ hhole hs]

end
end SixVertex
