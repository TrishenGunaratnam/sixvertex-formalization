import SixVertex.PhysicalHoppingSign

namespace SixVertex
noncomputable section

/-- The first physical bond,with all later quantum spins fixed. -/
def headPairLink (lam eta : ℝ) (n : ℕ) : Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ :=
  fun q r => if q.2.2=r.2.2 then
    physicalLinkOperator lam eta (q.1,q.2.1) (r.1,r.2.1) else 0

/-- This first-bond operator is an exact translate of the seam term in
the actual logarithmic Hamiltonian. -/
theorem headPairLink_eq_translated_seam (lam eta : ℝ) (n : ℕ) :
    headPairLink lam eta n=
      spinPermutation (cyclicSpinTranslation (n+1)).symm*periodicSeamLink lam eta n*
        spinPermutation (cyclicSpinTranslation (n+1)) := by
  ext ⟨a,b,t⟩ ⟨c,d,s⟩
  have h := translatedMatrix_apply (cyclicSpinTranslation (n+1)) (periodicSeamLink lam eta n)
    1 (a,b,t) (c,d,s)
  simp only [pow_one,Function.iterate_one] at h
  rw [h]
  change (if t=s then physicalLinkOperator lam eta (a,b) (c,d) else 0)=
    periodicSeamLink lam eta n (b,appendSpin n t a) (d,appendSpin n s c)
  simp only [periodicSeamLink,unappend_append]

/-- The exact local physical link at the free point has only the two
particle-hole hopping entries,each equal to -1/2. -/
theorem physicalLinkOperator_freeFermion_apply (q r : PairSpin) :
    physicalLinkOperator (Real.pi/2) (1/2) q r=
      if q.1≠q.2 ∧ r=(q.2,q.1) then -(1/2 : ℂ) else 0 := by
  rw [physicalLinkOperator_eq_sixMatrix]
  rcases q with ⟨a,b⟩
  rcases r with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [sixMatrix,← Complex.ofReal_cos,← Complex.ofReal_sin,
      Complex.ofReal_div,Real.cos_pi_div_two,Real.sin_pi_div_two]

/-- The actual free first bond is a single physical spin exchange. -/
theorem headPairLink_freeFermion_kernel (n : ℕ) (q r : RowSpins (n+2)) :
    headPairLink (Real.pi/2) (1/2) n q r=
      if q.1≠q.2.1 ∧ r=(q.2.1,q.1,q.2.2) then -(1/2 : ℂ) else 0 := by
  rcases q with ⟨a,b,t⟩
  rcases r with ⟨c,d,s⟩
  simp only [headPairLink,physicalLinkOperator_freeFermion_apply]
  by_cases h : t=s
  · subst s
    simp only [ite_true,Prod.mk.injEq,and_true]
  · have hst : s≠t := Ne.symm h
    simp [h,hst]

/-- Exact action of the physical free first bond on every full spin vector. -/
theorem headPairLink_freeFermion_mulVec (n : ℕ) (v : RowSpins (n+2) → ℂ)
    (q : RowSpins (n+2)) :
    (headPairLink (Real.pi/2) (1/2) n).mulVec v q=
      if q.1≠q.2.1 then -(1/2 : ℂ)*v (q.2.1,q.1,q.2.2) else 0 := by
  simp only [Matrix.mulVec,dotProduct,headPairLink_freeFermion_kernel]
  by_cases h : q.1≠q.2.1
  · simp [h,ite_mul]
  · simp [h]

end
end SixVertex
