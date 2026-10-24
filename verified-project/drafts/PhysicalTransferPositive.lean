import SixVertex.GroundStateTransferLine

namespace SixVertex
noncomputable section

/-- The two physical diagonal weights agree at the positive row point. -/
theorem physicalR_at_midpoint (lam : ℝ) :
    physicalR lam ((lam : ℂ)/2)=
      sixMatrix ((Real.sin (lam/2)/Real.sin lam : ℝ) : ℂ)
        ((Real.sin (lam/2)/Real.sin lam : ℝ) : ℂ) 1 := by
  have he : (lam : ℂ)-(lam : ℂ)/2=(lam : ℂ)/2 := by ring
  simp only [physicalR,he,Complex.ofReal_div,Complex.ofReal_sin]
  norm_num

/-- The actual common diagonal weight is strictly positive throughout
the physical parameter range. -/
theorem physical_midpoint_weight_pos (lam : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) :
    0<Real.sin (lam/2)/Real.sin lam := by
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    (Real.sin_pos_of_pos_of_lt_pi h0 hpi)

/-- Existing row contraction preserves real nonnegative local entries. -/
theorem rowBlock_real_nonnegative (tiles : ℕ → Matrix PairSpin PairSpin ℂ)
    (htiles : ∀ j i k,(tiles j i k).im=0 ∧ 0≤(tiles j i k).re)
    (n : ℕ) (a b : Fin 2) (q r : RowSpins n) :
    (rowBlock tiles n a b q r).im=0 ∧ 0≤(rowBlock tiles n a b q r).re := by
  induction n generalizing tiles a b with
  | zero => simp only [rowBlock];split_ifs <;> norm_num
  | succ n ih =>
    change (∑ c : Fin 2,tiles 0 (a,q.1) (c,r.1)*rowBlock (fun j => tiles (j+1)) n c b q.2 r.2).im=0 ∧
      0≤(∑ c : Fin 2,tiles 0 (a,q.1) (c,r.1)*rowBlock (fun j => tiles (j+1)) n c b q.2 r.2).re
    have ht (c : Fin 2) := ih (fun j => tiles (j+1)) (fun j => htiles (j+1)) c b q.2 r.2
    constructor
    · rw [Complex.im_sum]
      apply Finset.sum_eq_zero
      intro c _
      rw [Complex.mul_im,(htiles 0 (a,q.1) (c,r.1)).1,(ht c).1]
      ring
    · rw [Complex.re_sum]
      apply Finset.sum_nonneg
      intro c _
      rw [Complex.mul_re,(htiles 0 (a,q.1) (c,r.1)).1,(ht c).1]
      simp only [mul_zero,sub_zero]
      exact mul_nonneg (htiles 0 (a,q.1) (c,r.1)).2 (ht c).2

/-- The local positive-row matrix has real nonnegative entries. -/
theorem sixMatrix_equal_real_nonnegative (d : ℝ) (hd : 0≤d) (i j : PairSpin) :
    (sixMatrix (d : ℂ) (d : ℂ) 1 i j).im=0 ∧ 0≤(sixMatrix (d : ℂ) (d : ℂ) 1 i j).re := by
  unfold sixMatrix
  split_ifs <;> simp [hd]

/-- Exact local diagonal entry when the parallel and mixed weights agree. -/
theorem sixMatrix_equal_diagonal (d c : ℂ) (a b q : Fin 2) :
    sixMatrix d d c (a,q) (b,q)=if a=b then d else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases q <;> simp [sixMatrix]

/-- Exact diagonal row contraction,with both auxiliary spins retained. -/
theorem rowBlock_equal_diagonal (d c : ℂ) (n : ℕ) (a b : Fin 2) (q : RowSpins n) :
    rowBlock (fun _ => sixMatrix d d c) n a b q q=if a=b then d^n else 0 := by
  induction n generalizing a b with
  | zero => simp [rowBlock]
  | succ n ih =>
    change (∑ k : Fin 2,sixMatrix d d c (a,q.1) (k,q.1)*
      rowBlock (fun _ => sixMatrix d d c) n k b q.2 q.2)= _
    simp_rw [sixMatrix_equal_diagonal,ih]
    simp [ite_mul,mul_ite,pow_succ,mul_comm]

/-- The exact marked-row diagonal is twice the product weight. -/
theorem markedRow_equal_diagonal (d c : ℂ) (n : ℕ) (q : RowSpins n) :
    markedRow (fun _ => sixMatrix d d c) n 1 q q=2*d^n := by
  simp [markedRow,rowBlock_equal_diagonal,Fin.sum_univ_two,Matrix.one_apply,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- The actual positive physical transfer row has real nonnegative
entries at every finite length. -/
theorem homogeneousPhysicalRow_midpoint_real_nonnegative (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (L : ℕ) (q r : RowSpins L) :
    (homogeneousPhysicalRow lam L ((lam : ℂ)/2) q r).im=0 ∧
      0≤(homogeneousPhysicalRow lam L ((lam : ℂ)/2) q r).re := by
  let d : ℝ := Real.sin (lam/2)/Real.sin lam
  have hd : 0≤d := (physical_midpoint_weight_pos lam h0 hpi).le
  have hr (a : Fin 2) := rowBlock_real_nonnegative (fun _ => sixMatrix (d : ℂ) (d : ℂ) 1)
    (fun _ i j => sixMatrix_equal_real_nonnegative d hd i j) L a a q r
  change (markedRow (fun _ => physicalR lam ((lam : ℂ)/2)) L 1 q r).im=0 ∧
    0≤(markedRow (fun _ => physicalR lam ((lam : ℂ)/2)) L 1 q r).re
  simp only [physicalR_at_midpoint]
  simp only [markedRow,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  constructor
  · rw [Complex.im_sum]
    exact Finset.sum_eq_zero (fun a _ => (hr a).1)
  · rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun a _ => (hr a).2)

/-- The actual positive physical transfer row has a strictly positive
exact diagonal,including the finite-length normalization factor. -/
theorem homogeneousPhysicalRow_midpoint_diagonal (lam : ℝ) (L : ℕ) (q : RowSpins L) :
    homogeneousPhysicalRow lam L ((lam : ℂ)/2) q q=
      ((2*(Real.sin (lam/2)/Real.sin lam)^L : ℝ) : ℂ) := by
  change markedRow (fun _ => physicalR lam ((lam : ℂ)/2)) L 1 q q= _
  rw [show (fun _ : ℕ => physicalR lam ((lam : ℂ)/2))=
    (fun _ => sixMatrix ((Real.sin (lam/2)/Real.sin lam : ℝ) : ℂ)
      ((Real.sin (lam/2)/Real.sin lam : ℝ) : ℂ) 1) from funext (fun _ => physicalR_at_midpoint lam)]
  rw [markedRow_equal_diagonal]
  simp

theorem homogeneousPhysicalRow_midpoint_diagonal_re_pos (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (L : ℕ) (q : RowSpins L) :
    0<(homogeneousPhysicalRow lam L ((lam : ℂ)/2) q q).re := by
  rw [homogeneousPhysicalRow_midpoint_diagonal,Complex.ofReal_re]
  exact mul_pos (by norm_num) (pow_pos (physical_midpoint_weight_pos lam h0 hpi) L)

end
end SixVertex
