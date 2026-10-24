import SixVertex.PhysicalChainHamiltonian

namespace SixVertex
noncomputable section

/-- The local physical link has real entries. -/
theorem physicalLinkOperator_im_zero (lam eta : ℝ) (q r : PairSpin) :
    (physicalLinkOperator lam eta q r).im=0 := by
  rw [physicalLinkOperator_eq_sixMatrix]
  rcases q with ⟨a,b⟩
  rcases r with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [sixMatrix,← Complex.ofReal_cos,← Complex.ofReal_sin]

/-- Every off-diagonal entry of the physical local link is nonpositive. -/
theorem physicalLinkOperator_offdiag_re_nonpos (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0≤eta) (q r : PairSpin) (hne : q≠r) :
    (physicalLinkOperator lam eta q r).re≤0 := by
  rw [physicalLinkOperator_eq_sixMatrix]
  simp only [sixMatrix,if_neg hne]
  split_ifs
  · have hc : (-(eta : ℂ)/Complex.sin (lam : ℂ))=((-eta/Real.sin lam : ℝ) : ℂ) := by
      simp
    rw [hc,Complex.ofReal_re]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta)
      (Real.sin_pos_of_pos_of_lt_pi h0 hpi).le
  · simp

/-- All entries of the actual seam operator are real. -/
theorem periodicSeamLink_im_zero (lam eta : ℝ) (n : ℕ) (q r : RowSpins (n+2)) :
    (periodicSeamLink lam eta n q r).im=0 := by
  unfold periodicSeamLink
  split_ifs
  · exact physicalLinkOperator_im_zero _ _ _ _
  · rfl

/-- The explicit boundary link has no positive off-diagonal entries. -/
theorem periodicSeamLink_offdiag_re_nonpos (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0≤eta) (n : ℕ)
    (q r : RowSpins (n+2)) (hne : q≠r) :
    (periodicSeamLink lam eta n q r).re≤0 := by
  unfold periodicSeamLink
  split_ifs with hm
  · apply physicalLinkOperator_offdiag_re_nonpos lam eta h0 hpi heta
    intro hp
    have hl := congrArg Prod.fst hp
    have hh := congrArg Prod.snd hp
    change (unappendSpin n q.2).2=(unappendSpin n r.2).2 at hl
    change q.1=r.1 at hh
    have ht : q.2=r.2 := by
      rw [← append_unappend n q.2,← append_unappend n r.2]
      rw [hm,hl]
    exact hne (Prod.ext hh ht)
  · simp

/-- Matrix conjugation by a power of translation is exactly simultaneous
rotation of its two physical configurations. -/
theorem translatedMatrix_apply {L : ℕ} (e : Equiv.Perm (RowSpins L))
    (A : Matrix (RowSpins L) (RowSpins L) ℂ) (k : ℕ) (q r : RowSpins L) :
    (spinPermutation e.symm^k*A*spinPermutation e^k) q r=
      A ((e : RowSpins L → RowSpins L)^[k] q) ((e : RowSpins L → RowSpins L)^[k] r) := by
  induction k generalizing q r with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (spinPermutation e.symm),pow_succ (spinPermutation e)]
    calc
      _ = (spinPermutation e.symm*(spinPermutation e.symm^k*A*spinPermutation e^k)*
          spinPermutation e) q r := by congr 1; simp only [mul_assoc]
      _ = (spinPermutation e.symm^k*A*spinPermutation e^k) (e q) (e r) := by
        rw [mul_spinPermutation_apply,spinPermutation_mul_apply]
        rfl
      _ = _ := ih (e q) (e r)

/-- The full Hamiltonian obtained from the actual row derivative is real. -/
theorem homogeneousLinkHamiltonian_im_zero (lam eta : ℝ) (n : ℕ)
    (q r : RowSpins (n+2)) : (homogeneousLinkHamiltonian lam eta (n+1) q r).im=0 := by
  rw [homogeneousLinkHamiltonian_eq_periodic_links]
  simp only [periodicLinkHamiltonian,Matrix.sum_apply,Complex.im_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [translatedMatrix_apply]
  exact periodicSeamLink_im_zero _ _ _ _ _

/-- The actual full Hamiltonian has nonpositive off-diagonal entries,
as required for the sector Perron argument. -/
theorem homogeneousLinkHamiltonian_offdiag_re_nonpos (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0≤eta) (n : ℕ)
    (q r : RowSpins (n+2)) (hne : q≠r) :
    (homogeneousLinkHamiltonian lam eta (n+1) q r).re≤0 := by
  rw [homogeneousLinkHamiltonian_eq_periodic_links]
  simp only [periodicLinkHamiltonian,Matrix.sum_apply,Complex.re_sum]
  apply Finset.sum_nonpos
  intro k _
  rw [translatedMatrix_apply]
  apply periodicSeamLink_offdiag_re_nonpos lam eta h0 hpi heta
  intro h
  exact hne (((cyclicSpinTranslation (n+1)).injective.iterate k.val) h)

end
end SixVertex
