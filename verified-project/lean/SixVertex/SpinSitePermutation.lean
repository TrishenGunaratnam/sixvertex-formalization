import SixVertex.SpinCoordinates

namespace SixVertex
noncomputable section

/-- The ordered occupied-site embedding before the integer cast. -/
def occupiedIndex {L particles : ℕ} (q : ParticleConfigurations L particles) : Fin particles ↪o Fin L :=
  (occupiedSites L q.val).orderEmbOfFin ((occupiedSites_card L q.val).trans q.property)

theorem occupiedIndex_occupied {L particles : ℕ} (q : ParticleConfigurations L particles)
    (i : Fin particles) : rowSpinAt L q.val (occupiedIndex q i)=1 := by
  have h := (occupiedSites L q.val).orderEmbOfFin_mem
    ((occupiedSites_card L q.val).trans q.property) i
  exact (Finset.mem_filter.mp h).2

theorem occupiedCoordinates_eq_index {L particles : ℕ} (q : ParticleConfigurations L particles)
    (i : Fin particles) : occupiedCoordinates q i=((occupiedIndex q i).val : ℤ) := rfl

/-- Reindexing the site bits is a genuine permutation of physical spins. -/
def permuteSpinSites (L : ℕ) (e : Equiv.Perm (Fin L)) (q : RowSpins L) : RowSpins L :=
  rowSpinsOfSites L (fun i => rowSpinAt L q (e i))

theorem rowSpinAt_permuteSpinSites (L : ℕ) (e : Equiv.Perm (Fin L)) (q : RowSpins L) :
    rowSpinAt L (permuteSpinSites L e q)=fun i => rowSpinAt L q (e i) := by
  exact rowSpinAt_ofSites L _

theorem minusCount_permuteSpinSites (L : ℕ) (e : Equiv.Perm (Fin L)) (q : RowSpins L) :
    minusCount L (permuteSpinSites L e q)=minusCount L q := by
  rw [minusCount_eq_sum_sites,minusCount_eq_sum_sites,rowSpinAt_permuteSpinSites]
  exact Equiv.sum_comp e (fun i => (rowSpinAt L q i).val)

def swapSpinSites {L particles : ℕ} (q : ParticleConfigurations L particles) (a b : Fin L) :
    ParticleConfigurations L particles :=
  ⟨permuteSpinSites L (Equiv.swap a b) q.val,(minusCount_permuteSpinSites L _ q.val).trans q.property⟩

theorem rowSpinAt_swapSpinSites {L particles : ℕ} (q : ParticleConfigurations L particles)
    (a b i : Fin L) : rowSpinAt L (swapSpinSites q a b).val i=
      rowSpinAt L q.val (Equiv.swap a b i) := by
  exact congrFun (rowSpinAt_permuteSpinSites L (Equiv.swap a b) q.val) i

/-- When a site exchange preserves order of occupied positions,it is the
exact ordered-coordinate map of the exchanged physical spin word. -/
theorem occupiedIndex_swap_of_strictMono {L particles : ℕ} (q : ParticleConfigurations L particles)
    (a b : Fin L) (hm : StrictMono (fun i => Equiv.swap a b (occupiedIndex q i))) :
    (fun i => occupiedIndex (swapSpinSites q a b) i)=fun i => Equiv.swap a b (occupiedIndex q i) := by
  symm
  apply Finset.orderEmbOfFin_unique
    ((occupiedSites_card L (swapSpinSites q a b).val).trans (swapSpinSites q a b).property)
  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [rowSpinAt_swapSpinSites,Equiv.swap_apply_self]
    exact occupiedIndex_occupied q i
  · exact hm

/-- Moving an occupied site one step to a missing successor preserves order. -/
theorem strictMono_update_fin_successor {I : Type*} [LinearOrder I] [DecidableEq I]
    {L : ℕ} (f : I → Fin L) (hf : StrictMono f) (j : I) (b : Fin L)
    (hb : b.val=(f j).val+1) (hmiss : ∀ i,f i≠b) : StrictMono (Function.update f j b) := by
  intro i k hik
  by_cases hi : i=j
  · subst i
    have hk : k≠j := ne_of_gt hik
    rw [Function.update_self,Function.update_of_ne hk]
    have hm := hf hik
    have hn : (f k).val≠b.val := by intro h;exact hmiss k (Fin.ext h)
    change b.val<(f k).val
    change (f j).val<(f k).val at hm
    omega
  · by_cases hk : k=j
    · subst k
      rw [Function.update_of_ne hi,Function.update_self]
      have hm := hf hik
      change (f i).val<b.val
      change (f i).val<(f j).val at hm
      omega
    · rw [Function.update_of_ne hi,Function.update_of_ne hk]
      exact hf hik

/-- The same exact order preservation for a missing predecessor. -/
theorem strictMono_update_fin_predecessor {I : Type*} [LinearOrder I] [DecidableEq I]
    {L : ℕ} (f : I → Fin L) (hf : StrictMono f) (j : I) (b : Fin L)
    (hb : (f j).val=b.val+1) (hmiss : ∀ i,f i≠b) : StrictMono (Function.update f j b) := by
  intro i k hik
  by_cases hi : i=j
  · subst i
    have hk : k≠j := ne_of_gt hik
    rw [Function.update_self,Function.update_of_ne hk]
    have hm := hf hik
    change b.val<(f k).val
    change (f j).val<(f k).val at hm
    omega
  · by_cases hk : k=j
    · subst k
      rw [Function.update_of_ne hi,Function.update_self]
      have hm := hf hik
      have hn : (f i).val≠b.val := by intro h;exact hmiss i (Fin.ext h)
      change (f i).val<b.val
      change (f i).val<(f j).val at hm
      omega
    · rw [Function.update_of_ne hi,Function.update_of_ne hk]
      exact hf hik

end
end SixVertex
