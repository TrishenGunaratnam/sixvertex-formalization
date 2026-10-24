import SixVertex.RowTranslatedLinks
import SixVertex.PhysicalChainCommutation

namespace SixVertex
noncomputable section
open scoped Matrix

/-- Every actual insertion is a translate of the first insertion. -/
theorem swapInsertionRow_eq_translation_powers (D : Matrix PairSpin PairSpin ℂ)
    (n k : ℕ) (hk : k≤n) :
    swapInsertionRow D n k=
      spinPermutation (cyclicSpinTranslation n).symm^k*swapInsertionRow D n 0*
        spinPermutation (cyclicSpinTranslation n)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [swapInsertionRow_successor D n k (by omega),ih (by omega),pow_succ',pow_succ]
    simp only [mul_assoc]

/-- The physical link on the periodic seam,with the intervening sites
fixed. Conjugating this matrix by translations gives the other bonds. -/
def periodicSeamLink (lam eta : ℝ) (n : ℕ) :
    Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ := fun q r =>
  if (unappendSpin n q.2).1=(unappendSpin n r.2).1 then
    physicalLinkOperator lam eta ((unappendSpin n q.2).2,q.1)
      ((unappendSpin n r.2).2,r.1) else 0

/-- The explicit seam matrix agrees with the boundary term of the
actual logarithmic row derivative. -/
theorem periodicSeamLink_eq_actual_insertion (lam eta : ℝ) (n : ℕ) :
    periodicSeamLink lam eta n=
      (-(eta : ℂ)) • (swapInsertionRow (physicalRPrimeZero lam) (n+1) 0*
        spinPermutation (cyclicSpinTranslation (n+1)).symm) := by
  ext q r
  rcases q with ⟨qh,qt⟩
  rcases r with ⟨rh,rt⟩
  rw [← append_unappend n qt,← append_unappend n rt]
  change periodicSeamLink lam eta n
      (qh,appendSpin n (unappendSpin n qt).1 (unappendSpin n qt).2)
      (rh,appendSpin n (unappendSpin n rt).1 (unappendSpin n rt).2)=
    (-(eta : ℂ))*(firstInsertionRow (physicalRPrimeZero lam) (n+2)*
      spinPermutation (cyclicSpinTranslation (n+1)).symm)
        (qh,appendSpin n (unappendSpin n qt).1 (unappendSpin n qt).2)
        (rh,appendSpin n (unappendSpin n rt).1 (unappendSpin n rt).2)
  simpa only [periodicSeamLink,unappend_append] using
    (physicalBoundaryInsertion_eq_link lam eta n qh (unappendSpin n qt).2
      rh (unappendSpin n rt).2 (unappendSpin n qt).1 (unappendSpin n rt).1).symm

/-- The periodic seam operator is Hermitian,including every boundary
configuration. -/
theorem periodicSeamLink_isHermitian (lam eta : ℝ) (n : ℕ) :
    (periodicSeamLink lam eta n).IsHermitian := by
  unfold Matrix.IsHermitian
  ext q r
  simp only [Matrix.conjTranspose_apply,periodicSeamLink]
  by_cases hm : (unappendSpin n q.2).1=(unappendSpin n r.2).1
  · rw [if_pos hm.symm,if_pos hm]
    exact congrArg (fun A : Matrix PairSpin PairSpin ℂ =>
      A ((unappendSpin n q.2).2,q.1) ((unappendSpin n r.2).2,r.1))
        (physicalLinkOperator_isHermitian lam eta).eq
  · have hms : (unappendSpin n r.2).1≠(unappendSpin n q.2).1 := Ne.symm hm
    rw [if_neg hms,if_neg hm]
    exact star_zero _

/-- The explicit cyclic nearest-neighbor Hamiltonian,formed by moving
the last-first link through every physical bond. -/
def periodicLinkHamiltonian (lam eta : ℝ) (n : ℕ) :
    Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ :=
  ∑ k : Fin (n+2),spinPermutation (cyclicSpinTranslation (n+1)).symm^k.val*
    periodicSeamLink lam eta n*spinPermutation (cyclicSpinTranslation (n+1))^k.val

/-- The actual logarithmic derivative is exactly the full cyclic sum
of physical local links. No local Hamiltonian identity is assumed. -/
theorem homogeneousLinkHamiltonian_eq_periodic_links (lam eta : ℝ) (n : ℕ) :
    homogeneousLinkHamiltonian lam eta (n+1)=periodicLinkHamiltonian lam eta n := by
  rw [homogeneousLinkHamiltonian_eq_insertions]
  unfold periodicLinkHamiltonian
  apply Finset.sum_congr rfl
  intro k _
  change (-(eta : ℂ)) • (swapInsertionRow (physicalRPrimeZero lam) (n+1) k.val*
    spinPermutation (cyclicSpinTranslation (n+1)).symm)= _
  rw [swapInsertionRow_eq_translation_powers _ _ k.val (by omega),periodicSeamLink_eq_actual_insertion]
  let S := spinPermutation (cyclicSpinTranslation (n+1))
  let I := spinPermutation (cyclicSpinTranslation (n+1)).symm
  have hSI : S*I=1 := spinPermutation_mul_inverse _
  have hIS : I*S=1 := by
    simpa only [Equiv.symm_symm] using spinPermutation_mul_inverse (cyclicSpinTranslation (n+1)).symm
  have hc : Commute S I := by
    change S*I=I*S
    rw [hSI,hIS]
  have hp : S^k.val*I=I*S^k.val := (hc.pow_left k.val).eq
  change (-(eta : ℂ)) • ((I^k.val*swapInsertionRow (physicalRPrimeZero lam) (n+1) 0*S^k.val)*I)=
    I^k.val*((-(eta : ℂ)) • (swapInsertionRow (physicalRPrimeZero lam) (n+1) 0*I))*S^k.val
  simp only [mul_smul_comm,smul_mul_assoc,mul_assoc]
  rw [hp]

/-- The actual full logarithmic Hamiltonian is Hermitian. -/
theorem homogeneousLinkHamiltonian_isHermitian (lam eta : ℝ) (n : ℕ) :
    (homogeneousLinkHamiltonian lam eta (n+1)).IsHermitian := by
  rw [homogeneousLinkHamiltonian_eq_periodic_links]
  unfold periodicLinkHamiltonian Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_pow,
    spinPermutation_adjoint (cyclicSpinTranslation (n+1)),
    spinPermutation_adjoint (cyclicSpinTranslation (n+1)).symm,Equiv.symm_symm,(periodicSeamLink_isHermitian lam eta n).eq,mul_assoc]

end
end SixVertex
