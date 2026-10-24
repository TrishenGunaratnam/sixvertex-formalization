import SixVertex.PhysicalRowDerivative

namespace SixVertex
noncomputable section

/-- Replace exactly one physical tile in the existing ordered row. -/
def insertRowTile (A B : ℕ → Matrix PairSpin PairSpin ℂ) (k : ℕ) :
    ℕ → Matrix PairSpin PairSpin ℂ := fun j => if j=k then B j else A j

/-- The genuine row derivative is the sum of single-site insertions,
with the original auxiliary boundary spins and site order retained. -/
theorem rowBlockDifferential_eq_sum_insertions (A B : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (a b : Fin 2) (q r : RowSpins n) :
    rowBlockDifferential A B n a b q r=
      ∑ k : Fin n,rowBlock (insertRowTile A B k.val) n a b q r := by
  induction n generalizing A B a b with
  | zero => simp [rowBlockDifferential]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [rowBlockDifferential,rowBlock,insertRowTile,Fin.val_zero,Fin.val_succ,
      Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,Nat.zero_ne_add_one,
      ↓reduceIte,Nat.add_right_cancel_iff]
    simp_rw [ih]
    simp only [Finset.sum_add_distrib,Finset.mul_sum]
    change _ = (∑ c : Fin 2,B 0 (a,q.1) (c,r.1)*rowBlock (fun j => A (j+1)) n c b q.2 r.2)+
      ∑ k : Fin n,∑ c : Fin 2,A 0 (a,q.1) (c,r.1)*rowBlock (insertRowTile (fun j => A (j+1)) (fun j => B (j+1)) k.val) n c b q.2 r.2
    rw [Finset.sum_comm]

/-- Auxiliary tracing preserves the actual insertion formula. -/
theorem markedRowDifferential_eq_sum_insertions (A B : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    markedRowDifferential A B n D=
      ∑ k : Fin n,markedRow (insertRowTile A B k.val) n D := by
  ext q r
  simp only [markedRowDifferential,markedRow,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  simp only [rowBlockDifferential_eq_sum_insertions,Finset.mul_sum]
  calc
    _ = ∑ a : Fin 2,∑ k : Fin n,∑ b : Fin 2,D b a*rowBlock (insertRowTile A B k.val) n a b q r := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- Exact insertion expansion of the derivative of the physical row. -/
theorem homogeneousPhysicalRowPrimeZero_eq_insertions (lam : ℝ) (L : ℕ) :
    homogeneousPhysicalRowPrimeZero lam L=
      ∑ k : Fin L,markedRow
        (insertRowTile (fun _ => swapTile) (fun _ => physicalRPrimeZero lam) k.val) L 1 :=
  markedRowDifferential_eq_sum_insertions _ _ _ _

/-- Multiplying the actual insertion sum by the inverse translation
retains the exact logarithmic derivative,including the boundary link. -/
theorem homogeneousLinkHamiltonian_eq_insertions (lam eta : ℝ) (n : ℕ) :
    homogeneousLinkHamiltonian lam eta n=
      ∑ k : Fin (n+1), (-(eta : ℂ)) •
        (markedRow (insertRowTile (fun _ => swapTile) (fun _ => physicalRPrimeZero lam) k.val) (n+1) 1*
          spinPermutation (cyclicSpinTranslation n).symm) := by
  simp only [homogeneousLinkHamiltonian,homogeneousPhysicalRowPrimeZero_eq_insertions,
    Finset.sum_mul,Finset.smul_sum]

end
end SixVertex
