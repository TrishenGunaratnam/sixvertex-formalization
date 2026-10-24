import SixVertex.PhysicalRootMeasures
import SixVertex.RowEndpoints

namespace SixVertex
noncomputable section

/-- The actual complex-spectral derivative of the physical local R
matrix at its swap point. -/
def physicalRPrimeZero (lam : ℝ) : Matrix PairSpin PairSpin ℂ :=
  sixMatrix (-Complex.cos (lam : ℂ)/Complex.sin (lam : ℂ))
    (1/Complex.sin (lam : ℂ)) 0

theorem physicalR_hasDerivAt_zero (lam : ℝ) :
    HasDerivAt (physicalR lam) (physicalRPrimeZero lam) (0 : ℂ) := by
  have ha : HasDerivAt (fun z : ℂ => Complex.sin ((lam : ℂ)-z)/Complex.sin (lam : ℂ))
      (-Complex.cos (lam : ℂ)/Complex.sin (lam : ℂ)) (0 : ℂ) := by
    simpa using (((Complex.hasDerivAt_sin ((lam : ℂ)-0)).comp 0
      ((hasDerivAt_const (0 : ℂ) (lam : ℂ)).sub (hasDerivAt_id (0 : ℂ)))).div_const (Complex.sin (lam : ℂ)))
  have hb : HasDerivAt (fun z : ℂ => Complex.sin z/Complex.sin (lam : ℂ))
      (1/Complex.sin (lam : ℂ)) (0 : ℂ) := by
    simpa using (Complex.hasDerivAt_sin (0 : ℂ)).div_const (Complex.sin (lam : ℂ))
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hij : i=j
  · by_cases hp : i.1=i.2
    · simpa only [physicalR,physicalRPrimeZero,sixMatrix,if_pos hij,if_pos hp] using ha
    · simpa only [physicalR,physicalRPrimeZero,sixMatrix,if_pos hij,if_neg hp] using hb
  · by_cases hs : i.1=j.2 ∧ i.2=j.1
    · simpa only [physicalR,physicalRPrimeZero,sixMatrix,if_neg hij,if_pos hs] using
        (hasDerivAt_const (0 : ℂ) (1 : ℂ))
    · simpa only [physicalR,physicalRPrimeZero,sixMatrix,if_neg hij,if_neg hs] using
        (hasDerivAt_const (0 : ℂ) (0 : ℂ))

/-- The local link operator from the actual R derivative and swap. -/
def physicalLinkOperator (lam eta : ℝ) : Matrix PairSpin PairSpin ℂ :=
  (-(eta : ℂ)) • (swapTile*physicalRPrimeZero lam)

theorem physicalLinkOperator_eq_sixMatrix (lam eta : ℝ) :
    physicalLinkOperator lam eta=
      sixMatrix ((eta : ℂ)*Complex.cos (lam : ℂ)/Complex.sin (lam : ℂ)) 0
        (-(eta : ℂ)/Complex.sin (lam : ℂ)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [physicalLinkOperator,physicalRPrimeZero,swapTile,sixMatrix,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two] <;> ring

theorem physicalLinkOperator_hopping (lam eta : ℝ) :
    physicalLinkOperator lam eta (0,1) (1,0)=((-eta/Real.sin lam : ℝ) : ℂ) := by
  rw [physicalLinkOperator_eq_sixMatrix]
  norm_num [sixMatrix,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_sin]

/-- The hopping coefficient stated in the paper is strictly negative
throughout the physical parameter range,for every positive link scale. -/
theorem physicalLinkOperator_hopping_re_neg (lam eta : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (heta : 0 < eta) :
    (physicalLinkOperator lam eta (0,1) (1,0)).re < 0 := by
  rw [physicalLinkOperator_hopping,Complex.ofReal_re]
  exact div_neg_of_neg_of_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi h0 hpi)


/-- The actual local link operator is Hermitian for real parameters. -/
theorem physicalLinkOperator_isHermitian (lam eta : ℝ) :
    (physicalLinkOperator lam eta).IsHermitian := by
  rw [physicalLinkOperator_eq_sixMatrix]
  unfold Matrix.IsHermitian
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sixMatrix,Matrix.conjTranspose_apply,Complex.star_def,
      ← Complex.ofReal_cos,← Complex.ofReal_sin]

end
end SixVertex
