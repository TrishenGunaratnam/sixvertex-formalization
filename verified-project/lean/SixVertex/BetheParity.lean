import SixVertex.BetheEigenvectors
import SixVertex.RowGauge
import SixVertex.RowCommutation

namespace SixVertex

noncomputable def quantumParity (L : ℕ) : Matrix (RowSpins L) (RowSpins L) ℂ :=
  Matrix.diagonal (fun q => evenSign L q * oddSign L q)

noncomputable def quantumGauge (L : ℕ) : Matrix (RowSpins L) (RowSpins L) ℂ :=
  Matrix.diagonal (evenSign L)

theorem totalSign_succ (n : ℕ) (q : RowSpins (n+1)) :
    evenSign (n+1) q * oddSign (n+1) q = zSpin q.1 * (evenSign n q.2 * oddSign n q.2) := by
  simp only [evenSign, oddSign]
  ring

theorem zSpin_square (a : Fin 2) : zSpin a * zSpin a = 1 := by
  fin_cases a <;> simp [zSpin]

/-- Auxiliary parity is transported through every site of the monodromy. -/
theorem rowBlock_total_parity (A B C : ℕ → ℂ) (n : ℕ) (a b : Fin 2)
    (q r : RowSpins n) :
    (evenSign n q * oddSign n q) * rowBlock (fun j => sixMatrix (A j) (B j) (C j)) n a b q r =
      zSpin a * zSpin b * (evenSign n r * oddSign n r) *
        rowBlock (fun j => sixMatrix (A j) (B j) (C j)) n a b q r := by
  induction n generalizing A B C a b with
  | zero =>
    fin_cases a <;> fin_cases b <;> simp [rowBlock, evenSign, oddSign, zSpin]
  | succ n ih =>
    simp only [totalSign_succ, rowBlock, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hloc := sixMatrix_parity_entry (A 0) (B 0) (C 0) a c q.1 r.1
    have htail := ih (fun j => A (j+1)) (fun j => B (j+1)) (fun j => C (j+1)) c b q.2 r.2
    have hz := zSpin_square c
    linear_combination
      -(evenSign n q.2 * oddSign n q.2 *
        rowBlock (fun j => sixMatrix (A (j+1)) (B (j+1)) (C (j+1))) n c b q.2 r.2) * hloc +
      (zSpin a * zSpin c * zSpin r.1 * sixMatrix (A 0) (B 0) (C 0) (a,q.1) (c,r.1)) * htail +
      (zSpin a * zSpin b * zSpin r.1 * evenSign n r.2 * oddSign n r.2 *
        sixMatrix (A 0) (B 0) (C 0) (a,q.1) (c,r.1) *
        rowBlock (fun j => sixMatrix (A (j+1)) (B (j+1)) (C (j+1))) n c b q.2 r.2) * hz

theorem quantumParity_B (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (x : ℂ) :
    quantumParity L * betheB t b L x = -(betheB t b L x * quantumParity L) := by
  ext q r
  simp only [quantumParity, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply]
  have h := rowBlock_total_parity
    (fun j => Complex.sinh (x-b j-t/2+t)/Complex.sinh t)
    (fun j => Complex.sinh (x-b j-t/2)/Complex.sinh t) (fun _ => 1) L 0 1 q r
  simpa [zSpin, show (1 : Fin 2) ≠ 0 by decide,
    betheB, betheBlock, hyperbolicR, mul_comm, mul_left_comm, mul_assoc] using h

theorem plus_total_sign (L : ℕ) : evenSign L (plusSpins L) * oddSign L (plusSpins L) = 1 := by
  induction L with
  | zero => simp [evenSign, oddSign, plusSpins]
  | succ L ih => simpa only [totalSign_succ, plusSpins, zSpin, ite_true, one_mul] using ih

theorem quantumParity_vacuum (L : ℕ) : quantumParity L * vacuumProjector L = vacuumProjector L := by
  ext q r
  simp only [quantumParity, Matrix.diagonal_mul, vacuumProjector, Matrix.of_apply]
  split_ifs with h
  · rw [h.1, plus_total_sign, mul_one]
  · simp

/-- Every creation flips parity; the off-shell state has parity (-1)^n. -/
theorem betheState_parity (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (L : ℕ) (U : Finset ℂ) :
    quantumParity L * betheState t ht b L U = (-1 : ℂ)^U.card • betheState t ht b L U := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [betheState_empty, quantumParity_vacuum]
  | @insert u U hu ih =>
    rw [← bethe_B_action t ht b L U u hu, ← mul_assoc, quantumParity_B,
      neg_mul, mul_assoc, ih, mul_smul_comm, Finset.card_insert_of_notMem hu, pow_succ]
    simp

theorem quantumGauge_square (L : ℕ) : quantumGauge L * quantumGauge L = 1 := by
  ext q r
  simp only [quantumGauge, Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : q = r
  · subst r
    simp [parity_signs_square]
  · simp [h]

theorem physical_block_gauge (lam : ℝ) (b : ℕ → ℝ) (k : ℕ) (x : ℂ) (a c : Fin 2) :
    rowBlock (fun j => physicalTile lam (b j) x) (2*k) a c =
      quantumGauge (2*k) * betheBlock (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) x a c *
        quantumGauge (2*k) * quantumParity (2*k) := by
  ext q r
  have h := congrArg (fun M => M (a,q) (c,r)) (physical_monodromy_gauge lam b x k)
  simp only [monodromy, parityP, parityQ, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  simp only [quantumGauge, quantumParity, Matrix.diagonal_mul, Matrix.mul_diagonal,
    betheBlock_eq_standard]
  exact h

noncomputable def physicalTwistedRow (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (twist : ℝ) (x : ℂ) :=
  markedRow (fun j => physicalTile lam (b j) x) L
    (Matrix.diagonal (fun a : Fin 2 => if a = 0 then Complex.exp (Complex.I*twist)
      else Complex.exp (-Complex.I*twist)))

theorem physical_twisted_gauge (lam : ℝ) (b : ℕ → ℝ) (k : ℕ) (twist : ℝ) (x : ℂ) :
    physicalTwistedRow lam b (2*k) twist x =
      quantumGauge (2*k) * twistedStandardRow (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) twist x *
        quantumGauge (2*k) * quantumParity (2*k) := by
  rw [physicalTwistedRow, markedRow_diagonal]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rw [physical_block_gauge, physical_block_gauge, twistedStandardRow]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, betheA, betheL]

theorem quantumGauge_parity_sandwich (L : ℕ) :
    quantumGauge L * quantumParity L * quantumGauge L = quantumParity L := by
  ext q r
  simp only [quantumGauge, quantumParity, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply]
  by_cases h : q = r
  · subst r
    simp only [ite_true]
    linear_combination (evenSign L q * oddSign L q) * (parity_signs_square L q).1
  · simp [h]

theorem quantumGauge_mul_ne_zero (L : ℕ) (M : Matrix (RowSpins L) (RowSpins L) ℂ)
    (hM : M ≠ 0) : quantumGauge L * M ≠ 0 := by
  intro h
  have hh := congrArg (fun N => quantumGauge L * N) h
  rw [← mul_assoc, quantumGauge_square, one_mul, mul_zero] at hh
  exact hM hh

/-- The physical twisted row has the parity factor (-1)^card U. -/
theorem physical_eigenvector_of_standard (lam : ℝ) (ht : Complex.sinh (Complex.I*lam) ≠ 0)
    (b : ℕ → ℝ) (k : ℕ) (twist : ℝ) (U : Finset ℂ) (x ρ : ℂ)
    (hstd : twistedStandardRow (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) twist x *
      betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U =
      ρ • betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U) :
    physicalTwistedRow lam b (2*k) twist x *
      (quantumGauge (2*k) * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U) =
    ((-1 : ℂ)^U.card * ρ) •
      (quantumGauge (2*k) * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U) := by
  rw [physical_twisted_gauge]
  calc
    _ = quantumGauge (2*k) * twistedStandardRow (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) twist x *
        (quantumGauge (2*k) * quantumParity (2*k) * quantumGauge (2*k)) *
        betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U := by noncomm_ring
    _ = _ := by
      rw [quantumGauge_parity_sandwich]
      simp only [mul_assoc]
      rw [betheState_parity, mul_smul_comm, mul_smul_comm, hstd, mul_smul_comm, smul_smul]

end SixVertex
