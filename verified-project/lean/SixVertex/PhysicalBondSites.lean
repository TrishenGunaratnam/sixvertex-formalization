import SixVertex.FreePhysicalHopping
import SixVertex.SpinCyclicCoordinates

namespace SixVertex
noncomputable section

/-- Site permutation underlying the rotation of a specified actual bond. -/
def physicalBondSitePermutation (n k : ℕ) : Equiv.Perm (Fin (n+2)) :=
  (finRotate (n+2)).symm.trans ((finRotate (n+2))^k)

theorem rowSpinAt_cyclicSpinTranslation_symm (n : ℕ) (q : RowSpins (n+1)) :
    rowSpinAt (n+1) ((cyclicSpinTranslation n).symm q)=
      fun i => rowSpinAt (n+1) q ((finRotate (n+1)).symm i) := by
  funext i
  have h := congrFun (rowSpinAt_cyclicSpinTranslation n ((cyclicSpinTranslation n).symm q))
    ((finRotate (n+1)).symm i)
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem rowSpinAt_physicalBondRotation (n k : ℕ) (q : RowSpins (n+2)) :
    rowSpinAt (n+2) (physicalBondRotation n k q)=
      fun i => rowSpinAt (n+2) q (physicalBondSitePermutation n k i) := by
  change rowSpinAt (n+2) ((cyclicSpinTranslation (n+1)).symm (((cyclicSpinTranslation (n+1))^k) q))=_
  rw [rowSpinAt_cyclicSpinTranslation_symm,rowSpinAt_cyclicSpinTranslation_pow]
  rfl

/-- The physical first-pair exchange is exactly the transposition of sites 0,1. -/
theorem rowSpinAt_headSpinExchange (n : ℕ) (q : RowSpins (n+2)) :
    rowSpinAt (n+2) (headSpinExchange n q)=
      fun i => rowSpinAt (n+2) q (Equiv.swap (0 : Fin (n+2)) 1 i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [headSpinExchange,rowSpinAt]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [headSpinExchange,rowSpinAt]
    · have h0 : (j.succ.succ : Fin (n+2))≠0 := by intro h;have := congrArg Fin.val h;simp at this
      have h1 : (j.succ.succ : Fin (n+2))≠1 := by intro h;have := congrArg Fin.val h;simp at this
      simp [headSpinExchange,rowSpinAt,Equiv.swap_apply_of_ne_of_ne h0 h1]

/-- The actual exchange at any periodic physical bond is the corresponding
transposition of the two underlying sites. -/
theorem rowSpinAt_physicalBondExchange (n k : ℕ) (q : RowSpins (n+2)) :
    rowSpinAt (n+2) (physicalBondExchange n k q)=
      fun i => rowSpinAt (n+2) q (Equiv.swap (physicalBondSitePermutation n k 0)
        (physicalBondSitePermutation n k 1) i) := by
  let e := physicalBondRotation n k
  let s := physicalBondSitePermutation n k
  have hinv (r : RowSpins (n+2)) : rowSpinAt (n+2) (e.symm r)=
      fun i => rowSpinAt (n+2) r (s.symm i) := by
    funext i
    have h := congrFun (rowSpinAt_physicalBondRotation n k (e.symm r)) (s.symm i)
    change rowSpinAt (n+2) (e (e.symm r)) (s.symm i)=rowSpinAt (n+2) (e.symm r) (s (s.symm i)) at h
    simpa only [Equiv.apply_symm_apply] using h.symm
  change rowSpinAt (n+2) (e.symm (headSpinExchange n (e q)))=_
  rw [hinv,rowSpinAt_headSpinExchange,rowSpinAt_physicalBondRotation]
  funext i
  have h := congrArg (fun f : Equiv.Perm (Fin (n+2)) => f i)
    (Equiv.symm_trans_swap_trans (0 : Fin (n+2)) 1 s)
  exact congrArg (rowSpinAt (n+2) q) h

theorem physicalBondExchange_eq_permuteSpinSites (n k : ℕ) (q : RowSpins (n+2)) :
    physicalBondExchange n k q=permuteSpinSites (n+2)
      (Equiv.swap (physicalBondSitePermutation n k 0) (physicalBondSitePermutation n k 1)) q := by
  apply (rowSpinSitesEquiv (n+2)).injective
  exact (rowSpinAt_physicalBondExchange n k q).trans (rowSpinAt_permuteSpinSites _ _ q).symm

/-- The actual bond numbered k connects precisely k-1 and k modulo L. -/
theorem physicalBondSitePermutation_apply (n : ℕ) (k i : Fin (n+2)) :
    physicalBondSitePermutation n k.val i=i-1+k := by
  change (((finRotate (n+2))^k.val) ((finRotate (n+2)).symm i))=_
  rw [Equiv.Perm.coe_pow,← finCycle_eq_finRotate_iterate]
  simp only [finCycle_apply,finRotate_symm_apply]

theorem physicalBondSitePermutation_endpoints (n : ℕ) (k : Fin (n+2)) :
    physicalBondSitePermutation n k.val 0=k-1 ∧ physicalBondSitePermutation n k.val 1=k := by
  rw [physicalBondSitePermutation_apply,physicalBondSitePermutation_apply]
  constructor
  · abel
  · simp

/-- Explicit periodic site-hopping formula for the FULL actual Hamiltonian. -/
theorem homogeneousLinkHamiltonian_freeFermion_site_mulVec (n : ℕ)
    (v : RowSpins (n+2) → ℂ) (q : RowSpins (n+2)) :
    (homogeneousLinkHamiltonian (Real.pi/2) (1/2) (n+1)).mulVec v q=
      ∑ k : Fin (n+2),if rowSpinAt (n+2) q (k-1)≠rowSpinAt (n+2) q k
        then -(1/2 : ℂ)*v (permuteSpinSites (n+2) (Equiv.swap (k-1) k) q) else 0 := by
  rw [homogeneousLinkHamiltonian_freeFermion_mulVec]
  apply Finset.sum_congr rfl
  intro k _
  have h0 := congrFun (rowSpinAt_physicalBondRotation n k.val q) 0
  have h1 := congrFun (rowSpinAt_physicalBondRotation n k.val q) 1
  change (physicalBondRotation n k.val q).1=rowSpinAt (n+2) q (physicalBondSitePermutation n k.val 0) at h0
  change (physicalBondRotation n k.val q).2.1=rowSpinAt (n+2) q (physicalBondSitePermutation n k.val 1) at h1
  rw [h0,h1,physicalBondExchange_eq_permuteSpinSites,
    (physicalBondSitePermutation_endpoints n k).1,(physicalBondSitePermutation_endpoints n k).2]

end
end SixVertex
