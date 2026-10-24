import SixVertex.RowAlgebra

namespace SixVertex

def zSpin (i : Fin 2) : ℂ := if i = 0 then 1 else -1

theorem sixMatrix_gauge_entry (a b c : ℂ) (i j q r : Fin 2) :
    sixMatrix a (-b) c (i,q) (j,r) = zSpin i * zSpin r * sixMatrix a b c (i,q) (j,r) := by
  fin_cases i <;> fin_cases j <;> fin_cases q <;> fin_cases r <;>
    simp [sixMatrix, zSpin]

theorem sixMatrix_parity_entry (a b c : ℂ) (i j q r : Fin 2) :
    zSpin i * zSpin j * zSpin r * sixMatrix a b c (i,q) (j,r) =
      zSpin q * sixMatrix a b c (i,q) (j,r) := by
  fin_cases i <;> fin_cases j <;> fin_cases q <;> fin_cases r <;>
    simp [sixMatrix, zSpin]

theorem paired_gauge_entry (a b c A B C : ℂ) (i j k q r s t : Fin 2) :
    sixMatrix a (-b) c (i,q) (j,r) * sixMatrix A (-B) C (j,s) (k,t) =
      zSpin q * zSpin t *
        (sixMatrix a b c (i,q) (j,r) * sixMatrix A B C (j,s) (k,t)) := by
  rw [sixMatrix_gauge_entry, sixMatrix_gauge_entry]
  linear_combination
    (zSpin t * sixMatrix A B C (j,s) (k,t)) * sixMatrix_parity_entry a b c i j q r

/- The products of Z eigenvalues at even and odd sites. -/
mutual
  def evenSign : (n : ℕ) → RowSpins n → ℂ
    | 0, _ => 1
    | n+1, q => zSpin q.1 * oddSign n q.2
  def oddSign : (n : ℕ) → RowSpins n → ℂ
    | 0, _ => 1
    | n+1, q => evenSign n q.2
end

/-- Gauge transport through every even chain. No site, spectral parameter or
coefficient is held fixed in the induction. -/
theorem rowBlock_even_gauge (A B C : ℕ → ℂ) (k : ℕ) (a b : Fin 2)
    (q r : RowSpins (2*k)) :
    rowBlock (fun j => sixMatrix (A j) (-(B j)) (C j)) (2*k) a b q r =
      evenSign (2*k) q * oddSign (2*k) r *
        rowBlock (fun j => sixMatrix (A j) (B j) (C j)) (2*k) a b q r := by
  induction k generalizing A B C a b with
  | zero => simp [rowBlock, evenSign, oddSign]
  | succ k ih =>
    simp only [Nat.mul_succ, rowBlock, evenSign, oddSign]
    simp_rw [Finset.mul_sum, ih]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro f hf
    linear_combination
      (evenSign (2*k) q.2.2 * oddSign (2*k) r.2.2 *
        rowBlock (fun j => sixMatrix (A (j+1+1)) (B (j+1+1)) (C (j+1+1)))
          (2*k) f b q.2.2 r.2.2) *
      paired_gauge_entry (A 0) (B 0) (C 0) (A 1) (B 1) (C 1)
        a e f q.1 r.1 q.2.1 r.2.1

theorem parity_signs_square (n : ℕ) (q : RowSpins n) :
    evenSign n q * evenSign n q = 1 ∧ oddSign n q * oddSign n q = 1 := by
  induction n with
  | zero => simp [evenSign, oddSign]
  | succ n ih =>
    have hz : zSpin q.1 * zSpin q.1 = 1 := by
      by_cases h : q.1 = 0 <;> simp [zSpin, h]
    constructor
    · simp only [evenSign]
      calc
        _ = (zSpin q.1 * zSpin q.1) * (oddSign n q.2 * oddSign n q.2) := by ring
        _ = 1 := by rw [hz, (ih q.2).2]; ring
    · exact (ih q.2).1

noncomputable def monodromy (P : ℕ → Matrix PairSpin PairSpin ℂ) (n : ℕ) :
    Matrix (Fin 2 × RowSpins n) (Fin 2 × RowSpins n) ℂ :=
  fun i j => rowBlock P n i.1 j.1 i.2 j.2

/-- P_L extended by the identity on the auxiliary spin. -/
def parityP (n : ℕ) : Matrix (Fin 2 × RowSpins n) (Fin 2 × RowSpins n) ℂ :=
  Matrix.diagonal (fun i => evenSign n i.2)

/-- Q_L extended by the identity on the auxiliary spin. -/
def parityQ (n : ℕ) : Matrix (Fin 2 × RowSpins n) (Fin 2 × RowSpins n) ℂ :=
  Matrix.diagonal (fun i => evenSign n i.2 * oddSign n i.2)

theorem even_monodromy_gauge (A B C : ℕ → ℂ) (k : ℕ) :
    monodromy (fun j => sixMatrix (A j) (-(B j)) (C j)) (2*k) =
      parityP (2*k) * monodromy (fun j => sixMatrix (A j) (B j) (C j)) (2*k) *
        parityP (2*k) * parityQ (2*k) := by
  ext ⟨a,q⟩ ⟨b,r⟩
  simp only [parityP, parityQ, Matrix.mul_diagonal, Matrix.diagonal_mul, monodromy]
  rw [rowBlock_even_gauge]
  linear_combination
    -(evenSign (2*k) q * oddSign (2*k) r *
      rowBlock (fun j => sixMatrix (A j) (B j) (C j)) (2*k) a b q r) *
      (parity_signs_square (2*k) r).1

/-- The complete monodromy-gauge clause of `lem:row-algebra`. -/
theorem physical_monodromy_gauge (lam : ℝ) (b : ℕ → ℝ) (x : ℂ) (k : ℕ) :
    monodromy (fun j => physicalTile lam (b j) x) (2*k) =
      parityP (2*k) * monodromy (fun j => standardL lam (x-b j)) (2*k) *
        parityP (2*k) * parityQ (2*k) := by
  unfold physicalTile
  simp_rw [local_physical_gauge]
  unfold standardL
  simp_rw [sixMatrix_gauge]
  exact even_monodromy_gauge _ _ _ k

end SixVertex
