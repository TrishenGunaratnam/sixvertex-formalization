import SixVertex.PhysicalRowInsertions

namespace SixVertex
noncomputable section

/-- A row block depends only on its occupied sites. -/
theorem rowBlock_congr_prefix (A B : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (h : ∀ j,j<n → A j=B j) (a b : Fin 2) :
    rowBlock A n a b=rowBlock B n a b := by
  induction n generalizing A B a b with
  | zero => rfl
  | succ n ih =>
    ext q r
    change (∑ c : Fin 2,A 0 (a,q.1) (c,r.1)*rowBlock (fun j => A (j+1)) n c b q.2 r.2)=
      ∑ c : Fin 2,B 0 (a,q.1) (c,r.1)*rowBlock (fun j => B (j+1)) n c b q.2 r.2
    rw [h 0 (by omega)]
    apply Finset.sum_congr rfl
    intro c _
    rw [ih (fun j => A (j+1)) (fun j => B (j+1)) (fun j hj => h (j+1) (by omega)) c b]

/-- Splitting off the final physical site preserves the exact auxiliary
contraction. This is the cyclic-trace step for translating insertions. -/
theorem rowBlock_append (A : ℕ → Matrix PairSpin PairSpin ℂ) (n : ℕ)
    (a b ql rl : Fin 2) (q r : RowSpins n) :
    rowBlock A (n+1) a b (appendSpin n q ql) (appendSpin n r rl)=
      ∑ c : Fin 2,rowBlock A n a c q r*A n (c,ql) (b,rl) := by
  induction n generalizing A a b with
  | zero =>
    cases q
    cases r
    simp [rowBlock,appendSpin,mul_ite,ite_mul]
  | succ n ih =>
    change (∑ c : Fin 2,A 0 (a,q.1) (c,r.1)*
      rowBlock (fun j => A (j+1)) (n+1) c b (appendSpin n q.2 ql) (appendSpin n r.2 rl))= _
    simp_rw [ih]
    simp only [rowBlock,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    exact (mul_assoc _ _ _).symm

/-- Move the first tile to the final site of a row of length n+1. -/
def rotateRowTiles (A : ℕ → Matrix PairSpin PairSpin ℂ) (n : ℕ) :
    ℕ → Matrix PairSpin PairSpin ℂ := fun j => if j<n then A (j+1) else A 0

/-- Simultaneously rotating the physical sites and the tile list
preserves the actual auxiliary trace. -/
theorem markedRow_cyclic_rotation (A : ℕ → Matrix PairSpin PairSpin ℂ) (n : ℕ)
    (qh rh : Fin 2) (q r : RowSpins n) :
    markedRow (rotateRowTiles A n) (n+1) 1 (appendSpin n q qh) (appendSpin n r rh)=
      markedRow A (n+1) 1 (qh,q) (rh,r) := by
  have hp (a b : Fin 2) : rowBlock (rotateRowTiles A n) n a b=
      rowBlock (fun j => A (j+1)) n a b := by
    apply rowBlock_congr_prefix
    intro j hj
    simp only [rotateRowTiles,if_pos hj]
  simp only [markedRow,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp_rw [rowBlock_append,hp]
  simp only [rotateRowTiles,lt_self_iff_false,ite_false]
  change (∑ a : Fin 2,∑ c : Fin 2,rowBlock (fun j => A (j+1)) n a c q r*
    A 0 (c,qh) (a,rh))=∑ a : Fin 2,∑ c : Fin 2,A 0 (a,qh) (c,rh)*
      rowBlock (fun j => A (j+1)) n c a q r
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

end
end SixVertex
