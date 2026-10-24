import SixVertex.RowCyclicContraction
import SixVertex.PhysicalBoundaryLink

namespace SixVertex
noncomputable section

theorem spinPermutation_mul_apply {L : ℕ} (e : Equiv.Perm (RowSpins L))
    (A : Matrix (RowSpins L) (RowSpins L) ℂ) (q r : RowSpins L) :
    (spinPermutation e*A) q r=A (e.symm q) r := by
  have he (j : RowSpins L) : q=e j ↔ j=e.symm q := by
    constructor
    · intro h
      simpa using (congrArg e.symm h).symm
    · intro h
      rw [h]
      exact (e.apply_symm_apply q).symm
  simp [Matrix.mul_apply,spinPermutation,ite_mul,he]

theorem mul_spinPermutation_apply {L : ℕ} (e : Equiv.Perm (RowSpins L))
    (A : Matrix (RowSpins L) (RowSpins L) ℂ) (q r : RowSpins L) :
    (A*spinPermutation e) q r=A q (e r) := by
  simp [Matrix.mul_apply,spinPermutation,mul_ite]

theorem markedRow_congr_prefix (A B : ℕ → Matrix PairSpin PairSpin ℂ)
    (L : ℕ) (h : ∀ j,j<L → A j=B j) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    markedRow A L D=markedRow B L D := by
  unfold markedRow
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [rowBlock_congr_prefix A B L h a b]

/-- Cyclic rotation of the actual tile list is conjugation by the
actual physical translation matrix. -/
theorem markedRow_rotate_conjugation (A : ℕ → Matrix PairSpin PairSpin ℂ) (n : ℕ) :
    markedRow (rotateRowTiles A n) (n+1) 1=
      spinPermutation (cyclicSpinTranslation n)*markedRow A (n+1) 1*
        spinPermutation (cyclicSpinTranslation n).symm := by
  ext q r
  rw [mul_spinPermutation_apply,spinPermutation_mul_apply]
  let qq := (cyclicSpinTranslation n).symm q
  let rr := (cyclicSpinTranslation n).symm r
  have hq : q=appendSpin n qq.2 qq.1 := (Equiv.apply_symm_apply (cyclicSpinTranslation n) q).symm
  have hr : r=appendSpin n rr.2 rr.1 := (Equiv.apply_symm_apply (cyclicSpinTranslation n) r).symm
  change markedRow (rotateRowTiles A n) (n+1) 1 q r=markedRow A (n+1) 1 qq rr
  rw [hq,hr]
  exact markedRow_cyclic_rotation A n qq.1 rr.1 qq.2 rr.2

/-- A specified insertion in an otherwise homogeneous chain of swaps. -/
def swapInsertionRow (D : Matrix PairSpin PairSpin ℂ) (n k : ℕ) :
    Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ :=
  markedRow (insertRowTile (fun _ => swapTile) (fun _ => D) k) (n+1) 1

/-- Translating a nonboundary insertion moves it one site toward the
boundary. This is an identity for the existing row contraction. -/
theorem swapInsertionRow_translation (D : Matrix PairSpin PairSpin ℂ) (n k : ℕ)
    (hk : k<n) :
    swapInsertionRow D n k=
      spinPermutation (cyclicSpinTranslation n)*swapInsertionRow D n (k+1)*
        spinPermutation (cyclicSpinTranslation n).symm := by
  have hp : markedRow (rotateRowTiles
      (insertRowTile (fun _ => swapTile) (fun _ => D) (k+1)) n) (n+1) 1=
      swapInsertionRow D n k := by
    apply markedRow_congr_prefix
    intro j hj
    simp only [rotateRowTiles,insertRowTile]
    by_cases hjn : j<n
    · simp only [if_pos hjn,Nat.add_right_cancel_iff]
    · have hjn : j=n := by omega
      subst j
      simp only [lt_self_iff_false,ite_false,Nat.zero_ne_add_one,ite_false]
      have hnk : n ≠ k := by omega
      simp only [if_neg hnk]
  rw [← hp]
  exact markedRow_rotate_conjugation _ n

/-- Successive actual insertions are inverse-translation conjugates. -/
theorem swapInsertionRow_successor (D : Matrix PairSpin PairSpin ℂ) (n k : ℕ)
    (hk : k<n) :
    swapInsertionRow D n (k+1)=
      spinPermutation (cyclicSpinTranslation n).symm*swapInsertionRow D n k*
        spinPermutation (cyclicSpinTranslation n) := by
  let S := spinPermutation (cyclicSpinTranslation n)
  let I := spinPermutation (cyclicSpinTranslation n).symm
  have hIS : I*S=1 := by
    simpa only [Equiv.symm_symm] using spinPermutation_mul_inverse (cyclicSpinTranslation n).symm
  have h := swapInsertionRow_translation D n k hk
  change swapInsertionRow D n k=S*swapInsertionRow D n (k+1)*I at h
  change swapInsertionRow D n (k+1)=I*swapInsertionRow D n k*S
  rw [h]
  simp only [mul_assoc]
  rw [← mul_assoc I S,hIS,one_mul,mul_one]

end
end SixVertex
