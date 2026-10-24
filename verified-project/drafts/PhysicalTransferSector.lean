import SixVertex.PhysicalTransferPositive

namespace SixVertex
noncomputable section

/-- The actual homogeneous transfer row has no entries between distinct
particle counts,at every complex spectral coordinate. -/
theorem homogeneousPhysicalRow_charge_zero (lam : ℝ) (L : ℕ) (z : ℂ)
    (q r : RowSpins L) (h : minusCount L q≠minusCount L r) :
    homogeneousPhysicalRow lam L z q r=0 := by
  simp only [homogeneousPhysicalRow,markedRow,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_eq_zero
  intro a _
  change rowBlock (fun _ => sixMatrix
    (Complex.sin ((lam : ℂ)-z)/Complex.sin (lam : ℂ))
    (Complex.sin z/Complex.sin (lam : ℂ)) 1) L a a q r=0
  apply rowBlock_charge_zero
  intro hh
  exact h (Nat.add_left_cancel hh)

/-- The actual full homogeneous transfer family preserves each exact
particle sector. -/
theorem homogeneousPhysicalRow_sector (lam : ℝ) (L : ℕ) (z : ℂ) (k : ℤ)
    (v : RowSpins L → ℂ) (hv : SpinSector L k v) :
    SpinSector L k ((homogeneousPhysicalRow lam L z).mulVec v) := by
  intro q hq
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : (minusCount L r : ℤ)=k
  · have hqr : minusCount L q≠minusCount L r := by omega
    rw [homogeneousPhysicalRow_charge_zero lam L z q r hqr,zero_mul]
  · rw [hv r hr,mul_zero]

end
end SixVertex
