import SixVertex.PhysicalRowDerivative

namespace SixVertex
noncomputable section

def firstInsertionRow (D : Matrix PairSpin PairSpin ℂ) (L : ℕ) :
    Matrix (RowSpins L) (RowSpins L) ℂ :=
  markedRow (fun j => if j=0 then D else swapTile) L 1

/-- The first actual tile insertion followed by inverse translation
acts on the last and first spins and fixes all intervening spins. -/
theorem firstInsertionRow_shift_apply (D : Matrix PairSpin PairSpin ℂ) (n : ℕ)
    (qh ql rh rl : Fin 2) (qm rm : RowSpins n) :
    (firstInsertionRow D (n+2)*spinPermutation (cyclicSpinTranslation (n+1)).symm)
      (qh,appendSpin n qm ql) (rh,appendSpin n rm rl)=
        if qm=rm then D (ql,qh) (rh,rl) else 0 := by
  simp only [Matrix.mul_apply,spinPermutation,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
  have he : (cyclicSpinTranslation (n+1)).symm (rh,appendSpin n rm rl)=(rl,(rh,rm)) := by
    change ((unappendSpin (n+1) (rh,appendSpin n rm rl)).2,
      (unappendSpin (n+1) (rh,appendSpin n rm rl)).1)=(rl,(rh,rm))
    simp only [unappendSpin,unappend_append]
  rw [he]
  simp only [firstInsertionRow,markedRow,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∑ a : Fin 2,∑ c : Fin 2,D (a,qh) (c,rl)*
    rowBlock (fun _ => swapTile) (n+1) c a (appendSpin n qm ql) (rh,rm))= _
  simp_rw [rowBlock_swaps]
  have happ (a : Fin 2) : appendSpin n qm ql=appendSpin n rm a ↔ qm=rm ∧ ql=a := by
    constructor
    · intro h
      have hh := congrArg (unappendSpin n) h
      simpa only [unappend_append,Prod.mk.injEq] using hh
    · rintro ⟨rfl,rfl⟩
      rfl
  simp_rw [happ]
  by_cases hm : qm=rm <;> simp [hm,mul_ite,ite_and]

/-- The seam term of the actual logarithmic derivative is the local
physical link operator on the last and first spins. -/
theorem physicalBoundaryInsertion_eq_link (lam eta : ℝ) (n : ℕ)
    (qh ql rh rl : Fin 2) (qm rm : RowSpins n) :
    (-(eta : ℂ))*(firstInsertionRow (physicalRPrimeZero lam) (n+2)*
      spinPermutation (cyclicSpinTranslation (n+1)).symm)
        (qh,appendSpin n qm ql) (rh,appendSpin n rm rl)=
      if qm=rm then physicalLinkOperator lam eta (ql,qh) (rl,rh) else 0 := by
  rw [firstInsertionRow_shift_apply]
  by_cases hm : qm=rm
  · simp only [if_pos hm,physicalLinkOperator_eq_sixMatrix]
    fin_cases qh <;> fin_cases ql <;> fin_cases rh <;> fin_cases rl <;>
      simp [physicalRPrimeZero,sixMatrix] <;> ring
  · simp [hm]

end
end SixVertex
