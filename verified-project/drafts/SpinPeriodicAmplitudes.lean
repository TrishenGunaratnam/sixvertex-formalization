import SixVertex.SpinBoundaryCoordinates
import SixVertex.FreeSlaterPeriodicity

namespace SixVertex
noncomputable section

/-- A right hop from the final site to the empty zero site prepends zero
and removes the final occupied coordinate. -/
theorem occupiedIndex_wrap_right (length m : ℕ)
    (q : ParticleConfigurations (length+1) (m+1))
    (ha : occupiedIndex q (Fin.last m)=Fin.last length)
    (hb : rowSpinAt (length+1) q.val 0=0) :
    (fun i => occupiedIndex (swapSpinSites q (Fin.last length) 0) i)=
      @Fin.cons m (fun _ => Fin (length+1)) 0 (fun j => occupiedIndex q j.castSucc) := by
  let r := swapSpinSites q (Fin.last length) 0
  let g := @Fin.cons m (fun _ => Fin (length+1)) 0 (fun j => occupiedIndex q j.castSucc)
  have hm : StrictMono g := by
    apply Fin.strictMono_cons.mpr
    constructor
    · intro i
      have hn := occupiedIndex_ne_hole q 0 hb i.castSucc
      have hnval : (occupiedIndex q i.castSucc).val≠0 := by intro h;exact hn (Fin.ext h)
      change 0<(occupiedIndex q i.castSucc).val
      omega
    · intro i j hij
      apply (occupiedIndex q).strictMono
      simpa using hij
  have hmem (i : Fin (m+1)) : g i ∈ occupiedSites (length+1) r.val := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · dsimp only [g,r]
      rw [Fin.cons_zero,rowSpinAt_swapSpinSites,Equiv.swap_apply_right,← ha]
      exact occupiedIndex_occupied q (Fin.last m)
    · dsimp only [g,r]
      rw [Fin.cons_succ]
      have hlast : occupiedIndex q j.castSucc≠Fin.last length := by
        rw [← ha]
        exact fun h => (Fin.castSucc_ne_last j) ((occupiedIndex q).injective h)
      rw [rowSpinAt_swapSpinSites,Equiv.swap_apply_of_ne_of_ne hlast (occupiedIndex_ne_hole q 0 hb j.castSucc)]
      exact occupiedIndex_occupied q j.castSucc
  exact (Finset.orderEmbOfFin_unique ((occupiedSites_card (length+1) r.val).trans r.property) hmem hm).symm

theorem occupiedCoordinates_wrap_right (length m : ℕ)
    (q : ParticleConfigurations (length+1) (m+1))
    (ha : occupiedIndex q (Fin.last m)=Fin.last length)
    (hb : rowSpinAt (length+1) q.val 0=0) :
    occupiedCoordinates (swapSpinSites q (Fin.last length) 0)=
      @Fin.cons m (fun _ => ℤ) 0 (fun j => occupiedCoordinates q j.castSucc) := by
  funext i
  rw [occupiedCoordinates_eq_index,congrFun (occupiedIndex_wrap_right length m q ha hb) i]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cons_succ,occupiedCoordinates_eq_index]

/-- The physical left boundary exchange has precisely the covering-line
Slater amplitude,with no unproved fermionic sign. -/
theorem spinFreeSlaterVector_wrap_left (length m : ℕ) (Y : Fin (m+1) → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) (m+1)) (ha : occupiedIndex q 0=0)
    (hb : rowSpinAt (length+1) q.val (Fin.last length)=0) :
    spinFreeSlaterVector (length+1) Y (swapSpinSites q 0 (Fin.last length))=
      freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j))
        (Function.update (occupiedCoordinates q) 0 (occupiedCoordinates q 0-1))/freeSlaterPhase (m+1) := by
  let x := Function.update (occupiedCoordinates q) 0 (occupiedCoordinates q 0-1)
  have hc : occupiedCoordinates q 0=0 := by rw [occupiedCoordinates_eq_index,ha];rfl
  have hw := freeSlaterWave_cyclic_wrap m (length+1) (by omega) Y hY x
  have ht : @Fin.snoc m (fun _ => ℤ) (fun i => x i.succ) (x 0+((length+1 : ℕ) : ℤ))=
      @Fin.snoc m (fun _ => ℤ) (fun i => occupiedCoordinates q i.succ) (length : ℤ) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [x,hc]
    · simp [x,Fin.succ_ne_zero]
  rw [ht] at hw
  unfold spinFreeSlaterVector
  rw [occupiedCoordinates_wrap_left length m q ha hb]
  exact congrArg (fun z : ℂ => z/freeSlaterPhase (m+1)) hw

/-- The same exact signless Slater amplitude for the right boundary exchange. -/
theorem spinFreeSlaterVector_wrap_right (length m : ℕ) (Y : Fin (m+1) → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) (length+1) Y 0)
    (q : ParticleConfigurations (length+1) (m+1))
    (ha : occupiedIndex q (Fin.last m)=Fin.last length)
    (hb : rowSpinAt (length+1) q.val 0=0) :
    spinFreeSlaterVector (length+1) Y (swapSpinSites q (Fin.last length) 0)=
      freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j))
        (Function.update (occupiedCoordinates q) (Fin.last m) (occupiedCoordinates q (Fin.last m)+1))/freeSlaterPhase (m+1) := by
  let y := @Fin.cons m (fun _ => ℤ) 0 (fun i => occupiedCoordinates q i.castSucc)
  let x := Function.update (occupiedCoordinates q) (Fin.last m) (occupiedCoordinates q (Fin.last m)+1)
  have hc : occupiedCoordinates q (Fin.last m)=(length : ℤ) := by
    rw [occupiedCoordinates_eq_index,ha]
    rfl
  have hw := freeSlaterWave_cyclic_wrap m (length+1) (by omega) Y hY y
  have ht : @Fin.snoc m (fun _ => ℤ) (fun i => y i.succ) (y 0+((length+1 : ℕ) : ℤ))=x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [x,y,hc]
    · simp [x,y,Fin.castSucc_ne_last]
  rw [ht] at hw
  unfold spinFreeSlaterVector
  rw [occupiedCoordinates_wrap_right length m q ha hb]
  exact congrArg (fun z : ℂ => z/freeSlaterPhase (m+1)) hw.symm

end
end SixVertex
