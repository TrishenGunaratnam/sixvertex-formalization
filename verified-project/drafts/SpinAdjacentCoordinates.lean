import SixVertex.SpinSitePermutation

namespace SixVertex
noncomputable section

theorem occupiedIndex_ne_hole {L particles : ℕ} (q : ParticleConfigurations L particles)
    (b : Fin L) (hb : rowSpinAt L q.val b=0) : ∀ i,occupiedIndex q i≠b := by
  intro i hi
  have h := occupiedIndex_occupied q i
  rw [hi,hb] at h
  norm_num at h

/-- A physical occupied-hole exchange is one ordered-coordinate update
whenever that update is strictly increasing. -/
theorem occupiedIndex_swap_update {L particles : ℕ} (q : ParticleConfigurations L particles)
    (j : Fin particles) (b : Fin L) (hb : rowSpinAt L q.val b=0)
    (hm : StrictMono (Function.update (fun i => occupiedIndex q i) j b)) :
    (fun i => occupiedIndex (swapSpinSites q (occupiedIndex q j) b) i)=
      Function.update (fun i => occupiedIndex q i) j b := by
  have hfun : (fun i => Equiv.swap (occupiedIndex q j) b (occupiedIndex q i))=
      Function.update (fun i => occupiedIndex q i) j b := by
    funext i
    by_cases hi : i=j
    · subst i;simp
    · have ha : occupiedIndex q i≠occupiedIndex q j := fun h => hi ((occupiedIndex q).injective h)
      rw [Equiv.swap_apply_of_ne_of_ne ha (occupiedIndex_ne_hole q b hb i),Function.update_of_ne hi]
  have hs : StrictMono (fun i => Equiv.swap (occupiedIndex q j) b (occupiedIndex q i)) := by
    rw [hfun]
    exact hm
  exact (occupiedIndex_swap_of_strictMono q (occupiedIndex q j) b hs).trans hfun

theorem occupiedIndex_swap_right {L particles : ℕ} (q : ParticleConfigurations L particles)
    (j : Fin particles) (b : Fin L) (hb : rowSpinAt L q.val b=0)
    (hstep : b.val=(occupiedIndex q j).val+1) :
    (fun i => occupiedIndex (swapSpinSites q (occupiedIndex q j) b) i)=
      Function.update (fun i => occupiedIndex q i) j b := by
  exact occupiedIndex_swap_update q j b hb
    (strictMono_update_fin_successor _ (occupiedIndex q).strictMono j b hstep (occupiedIndex_ne_hole q b hb))

theorem occupiedIndex_swap_left {L particles : ℕ} (q : ParticleConfigurations L particles)
    (j : Fin particles) (b : Fin L) (hb : rowSpinAt L q.val b=0)
    (hstep : (occupiedIndex q j).val=b.val+1) :
    (fun i => occupiedIndex (swapSpinSites q (occupiedIndex q j) b) i)=
      Function.update (fun i => occupiedIndex q i) j b := by
  exact occupiedIndex_swap_update q j b hb
    (strictMono_update_fin_predecessor _ (occupiedIndex q).strictMono j b hstep (occupiedIndex_ne_hole q b hb))

/-- The integer coordinate used by the actual Slater state increases by
exactly one at the index of an allowed right hop. -/
theorem occupiedCoordinates_swap_right {L particles : ℕ} (q : ParticleConfigurations L particles)
    (j : Fin particles) (b : Fin L) (hb : rowSpinAt L q.val b=0)
    (hstep : b.val=(occupiedIndex q j).val+1) :
    occupiedCoordinates (swapSpinSites q (occupiedIndex q j) b)=
      Function.update (occupiedCoordinates q) j (occupiedCoordinates q j+1) := by
  funext i
  rw [occupiedCoordinates_eq_index]
  have he := congrFun (occupiedIndex_swap_right q j b hb hstep) i
  rw [he]
  by_cases hi : i=j
  · subst i
    rw [Function.update_self,Function.update_self,occupiedCoordinates_eq_index]
    exact_mod_cast hstep
  · rw [Function.update_of_ne hi,Function.update_of_ne hi,occupiedCoordinates_eq_index]

/-- The corresponding exact coordinate identity for an allowed left hop. -/
theorem occupiedCoordinates_swap_left {L particles : ℕ} (q : ParticleConfigurations L particles)
    (j : Fin particles) (b : Fin L) (hb : rowSpinAt L q.val b=0)
    (hstep : (occupiedIndex q j).val=b.val+1) :
    occupiedCoordinates (swapSpinSites q (occupiedIndex q j) b)=
      Function.update (occupiedCoordinates q) j (occupiedCoordinates q j-1) := by
  funext i
  rw [occupiedCoordinates_eq_index]
  have he := congrFun (occupiedIndex_swap_left q j b hb hstep) i
  rw [he]
  by_cases hi : i=j
  · subst i
    rw [Function.update_self,Function.update_self,occupiedCoordinates_eq_index]
    have hcast : ((occupiedIndex q j).val : ℤ)=(b.val : ℤ)+1 := by exact_mod_cast hstep
    omega
  · rw [Function.update_of_ne hi,Function.update_of_ne hi,occupiedCoordinates_eq_index]

end
end SixVertex
