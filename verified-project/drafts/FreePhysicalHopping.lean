import SixVertex.FreePhysicalHeadLink
import SixVertex.PhysicalHamiltonianSector

namespace SixVertex
noncomputable section

/-- Exchange the first two physical spins. -/
def headSpinExchange (n : ℕ) : Equiv.Perm (RowSpins (n+2)) where
  toFun q := (q.2.1,q.1,q.2.2)
  invFun q := (q.2.1,q.1,q.2.2)
  left_inv q := by rcases q with ⟨a,b,t⟩;rfl
  right_inv q := by rcases q with ⟨a,b,t⟩;rfl

theorem headSpinExchange_minusCount (n : ℕ) (q : RowSpins (n+2)) :
    minusCount (n+2) (headSpinExchange n q)=minusCount (n+2) q := by
  simp only [headSpinExchange,Equiv.coe_fn_mk,minusCount]
  omega

/-- The actual periodic seam is the inverse rotation of the exact first bond. -/
theorem periodicSeamLink_eq_head_rotated (lam eta : ℝ) (n : ℕ) (q r : RowSpins (n+2)) :
    periodicSeamLink lam eta n q r=
      headPairLink lam eta n ((cyclicSpinTranslation (n+1)).symm q)
        ((cyclicSpinTranslation (n+1)).symm r) := by
  have h := congrArg (fun A : Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ =>
    A ((cyclicSpinTranslation (n+1)).symm q) ((cyclicSpinTranslation (n+1)).symm r))
      (headPairLink_eq_translated_seam lam eta n)
  rw [mul_spinPermutation_apply,spinPermutation_mul_apply] at h
  simpa only [Equiv.symm_symm,Equiv.apply_symm_apply] using h.symm

/-- Exact action of a reindexed physical first bond,with no change of its
matrix entries or the vector being acted on. -/
theorem reindexed_free_head_mulVec (n : ℕ) (e : Equiv.Perm (RowSpins (n+2)))
    (v : RowSpins (n+2) → ℂ) (q : RowSpins (n+2)) :
    (∑ r,headPairLink (Real.pi/2) (1/2) n (e q) (e r)*v r)=
      if (e q).1≠(e q).2.1 then -(1/2 : ℂ)*v (e.symm (headSpinExchange n (e q))) else 0 := by
  have hs : (∑ r,headPairLink (Real.pi/2) (1/2) n (e q) (e r)*v r)=
      (headPairLink (Real.pi/2) (1/2) n).mulVec (fun r => v (e.symm r)) (e q) := by
    simpa only [Matrix.mulVec,dotProduct,Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun r => headPairLink (Real.pi/2) (1/2) n (e q) r*v (e.symm r)))
  rw [hs,headPairLink_freeFermion_mulVec]
  rfl

/-- Rotate a specified physical bond to the first two sites. k=0 is the
periodic seam and k=1 is the first open-chain bond. -/
def physicalBondRotation (n k : ℕ) : Equiv.Perm (RowSpins (n+2)) :=
  ((cyclicSpinTranslation (n+1))^k).trans (cyclicSpinTranslation (n+1)).symm

def physicalBondExchange (n k : ℕ) (q : RowSpins (n+2)) : RowSpins (n+2) :=
  (physicalBondRotation n k).symm (headSpinExchange n (physicalBondRotation n k q))

/-- Each summand of the actual logarithmic Hamiltonian is exactly the
first-bond matrix read at its rotated configurations. -/
theorem physical_hamiltonian_bond_entry (lam eta : ℝ) (n k : ℕ)
    (q r : RowSpins (n+2)) :
    (spinPermutation (cyclicSpinTranslation (n+1)).symm^k*periodicSeamLink lam eta n*
      spinPermutation (cyclicSpinTranslation (n+1))^k) q r=
      headPairLink lam eta n (physicalBondRotation n k q) (physicalBondRotation n k r) := by
  rw [translatedMatrix_apply,periodicSeamLink_eq_head_rotated]
  simp only [physicalBondRotation,Equiv.trans_apply,Equiv.Perm.coe_pow]

/-- The FULL actual free Hamiltonian acts by precisely its allowed
periodic particle-hole exchanges,with coefficient -1/2 per physical bond. -/
theorem homogeneousLinkHamiltonian_freeFermion_mulVec (n : ℕ) (v : RowSpins (n+2) → ℂ)
    (q : RowSpins (n+2)) :
    (homogeneousLinkHamiltonian (Real.pi/2) (1/2) (n+1)).mulVec v q=
      ∑ k : Fin (n+2),if (physicalBondRotation n k.val q).1≠(physicalBondRotation n k.val q).2.1
        then -(1/2 : ℂ)*v (physicalBondExchange n k.val q) else 0 := by
  rw [homogeneousLinkHamiltonian_eq_periodic_links]
  unfold periodicLinkHamiltonian
  change (∑ r : RowSpins (n+2),(∑ k : Fin (n+2),
    spinPermutation (cyclicSpinTranslation (n+1)).symm^k.val*periodicSeamLink (Real.pi/2) (1/2) n*
      spinPermutation (cyclicSpinTranslation (n+1))^k.val) q r*v r)=_
  simp only [Matrix.sum_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [physical_hamiltonian_bond_entry (Real.pi/2) (1/2) n k.val]
  exact reindexed_free_head_mulVec n (physicalBondRotation n k.val) v q

/-- All rotations used to enumerate physical bonds preserve the exact sector. -/
theorem physicalBondRotation_minusCount (n k : ℕ) (q : RowSpins (n+2)) :
    minusCount (n+2) (physicalBondRotation n k q)=minusCount (n+2) q := by
  have hinv (r : RowSpins (n+2)) :
      minusCount (n+2) ((cyclicSpinTranslation (n+1)).symm r)=minusCount (n+2) r := by
    have h := minusCount_cyclicSpinTranslation (n+1) ((cyclicSpinTranslation (n+1)).symm r)
    simpa only [Equiv.apply_symm_apply] using h.symm
  change minusCount (n+2) ((cyclicSpinTranslation (n+1)).symm (((cyclicSpinTranslation (n+1))^k) q))= _
  rw [hinv]
  simpa only [Equiv.Perm.coe_pow] using minusCount_cyclic_iterate (n+1) k q

/-- The actual free bond exchanges remain inside the physical sector. -/
theorem physicalBondExchange_minusCount (n k : ℕ) (q : RowSpins (n+2)) :
    minusCount (n+2) (physicalBondExchange n k q)=minusCount (n+2) q := by
  have hinv (r : RowSpins (n+2)) :
      minusCount (n+2) ((physicalBondRotation n k).symm r)=minusCount (n+2) r := by
    have h := physicalBondRotation_minusCount n k ((physicalBondRotation n k).symm r)
    simpa only [Equiv.apply_symm_apply] using h.symm
  exact (hinv _).trans ((headSpinExchange_minusCount n _).trans (physicalBondRotation_minusCount n k q))

end
end SixVertex
