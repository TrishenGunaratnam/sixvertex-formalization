import SixVertex.SpinPeriodicAmplitudes

namespace SixVertex
noncomputable section

theorem occupiedIndex_exists_of_occupied {L particles : ℕ} (q : ParticleConfigurations L particles)
    (a : Fin L) (ha : rowSpinAt L q.val a=1) : ∃ k,occupiedIndex q k=a := by
  let e := (occupiedSites L q.val).orderIsoOfFin ((occupiedSites_card L q.val).trans q.property)
  have hmem : a ∈ occupiedSites L q.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
  refine ⟨e.symm ⟨a,hmem⟩,?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨a,hmem⟩)

theorem freeSlaterWave_update_collision_zero {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (x : I → ℤ) (i k : I) (hik : i≠k) :
    freeSlaterWave p (Function.update x i (x k))=0 := by
  exact slaterWave_collision_zero (fun j => freePlaneWave (p j))
    (Function.update x i (x k)) i k hik (by simp [hik.symm])

theorem freeSlaterWave_update_period_plus_zero {particles : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (x : Fin particles → ℤ) (i k : Fin particles) (hik : i≠k) :
    freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j))
      (Function.update x i (x k+(L : ℤ)))=0 := by
  have h := freeSlaterWave_coordinate_period L hL Y hY (Function.update x i (x k)) i
  simp only [Function.update_self,Function.update_idem] at h
  rw [freeSlaterWave_update_collision_zero _ _ i k hik,mul_zero] at h
  exact h

theorem freeSlaterWave_update_period_minus_zero {particles : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (x : Fin particles → ℤ) (i k : Fin particles) (hik : i≠k) :
    freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j))
      (Function.update x i (x k-(L : ℤ)))=0 := by
  have h := freeSlaterWave_coordinate_period L hL Y hY (Function.update x i (x k-(L : ℤ))) i
  simp only [Function.update_self,Function.update_idem,sub_add_cancel] at h
  rw [freeSlaterWave_update_collision_zero _ _ i k hik] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by norm_num))

theorem finRotate_ne_self_of_length (length : ℕ) (hlen : 0<length) (a : Fin (length+1)) :
    finRotate (length+1) a≠a := by
  by_cases ha : a=Fin.last length
  · rw [ha,finRotate_last]
    intro h
    have hv : (0 : ℕ)=length := by simpa using congrArg Fin.val h
    omega
  · intro h
    have hv := congrArg Fin.val h
    rw [coe_finRotate_of_ne_last ha] at hv
    omega

/-- A blocked right hop gives a collision determinant,also across the seam. -/
theorem freeSlaterWave_blocked_right_zero {particles : ℕ} (length : ℕ) (hlen : 0<length)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) particles) (j : Fin particles)
    (hocc : rowSpinAt (length+1) q.val (finRotate (length+1) (occupiedIndex q j))=1) :
    freeSlaterWave (fun k => physicalRootMomentum (Real.pi/2) (Y k))
      (Function.update (occupiedCoordinates q) j (occupiedCoordinates q j+1))=0 := by
  obtain ⟨k,hk⟩ := occupiedIndex_exists_of_occupied q _ hocc
  have hjk : j≠k := by
    intro h
    subst k
    exact finRotate_ne_self_of_length length hlen _ hk.symm
  by_cases ha : occupiedIndex q j=Fin.last length
  · have hz : occupiedCoordinates q j+1=occupiedCoordinates q k+((length+1 : ℕ) : ℤ) := by
      rw [occupiedCoordinates_eq_index,occupiedCoordinates_eq_index,hk,ha,finRotate_last]
      simp
    rw [hz]
    exact freeSlaterWave_update_period_plus_zero (length+1) (by omega) Y hY _ j k hjk
  · have hz : occupiedCoordinates q j+1=occupiedCoordinates q k := by
      rw [occupiedCoordinates_eq_index,occupiedCoordinates_eq_index,hk]
      exact_mod_cast (coe_finRotate_of_ne_last ha).symm
    rw [hz]
    exact freeSlaterWave_update_collision_zero _ _ j k hjk

/-- A blocked left hop has the same exact vanishing,including at site zero. -/
theorem freeSlaterWave_blocked_left_zero {particles : ℕ} (length : ℕ) (hlen : 0<length)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) particles) (j : Fin particles)
    (hocc : rowSpinAt (length+1) q.val ((finRotate (length+1)).symm (occupiedIndex q j))=1) :
    freeSlaterWave (fun k => physicalRootMomentum (Real.pi/2) (Y k))
      (Function.update (occupiedCoordinates q) j (occupiedCoordinates q j-1))=0 := by
  obtain ⟨k,hk⟩ := occupiedIndex_exists_of_occupied q _ hocc
  have hjk : j≠k := by
    intro h
    subst k
    have he := congrArg (finRotate (length+1)) hk
    exact finRotate_ne_self_of_length length hlen _ (by simpa only [Equiv.apply_symm_apply] using he)
  by_cases ha : occupiedIndex q j=0
  · have hr : (finRotate (length+1)).symm 0=Fin.last length := by
      apply (finRotate (length+1)).injective
      simp
    have hz : occupiedCoordinates q j-1=occupiedCoordinates q k-((length+1 : ℕ) : ℤ) := by
      rw [occupiedCoordinates_eq_index,occupiedCoordinates_eq_index,hk,ha,hr]
      simp
    rw [hz]
    exact freeSlaterWave_update_period_minus_zero (length+1) (by omega) Y hY _ j k hjk
  · have hs := coe_finRotate_symm_of_ne_zero ha
    have hn : (occupiedIndex q j).val≠0 := by intro h;exact ha (Fin.ext h)
    have hnat : (occupiedIndex q j).val=((finRotate (length+1)).symm (occupiedIndex q j)).val+1 := by
      rw [hs]
      omega
    have hz : occupiedCoordinates q j-1=occupiedCoordinates q k := by
      rw [occupiedCoordinates_eq_index,occupiedCoordinates_eq_index,hk]
      have hc : ((occupiedIndex q j).val : ℤ)=
          (((finRotate (length+1)).symm (occupiedIndex q j)).val : ℤ)+1 := by exact_mod_cast hnat
      omega
    rw [hz]
    exact freeSlaterWave_update_collision_zero _ _ j k hjk

end
end SixVertex
