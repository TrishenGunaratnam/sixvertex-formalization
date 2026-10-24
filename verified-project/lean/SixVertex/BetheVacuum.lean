import SixVertex.BetheRows

namespace SixVertex

/-- The all-plus basis configuration, in the recursive tensor convention. -/
def plusSpins : (n : ℕ) → RowSpins n
  | 0 => ()
  | n+1 => (0, plusSpins n)

/-- Products of upper and lower local diagonal vacuum weights. -/
noncomputable def vacuumA (t : ℂ) (b : ℕ → ℂ) (x : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => (Complex.sinh (x-b 0+t/2) / Complex.sinh t) *
      vacuumA t (fun j => b (j+1)) x n

noncomputable def vacuumL (t : ℂ) (b : ℕ → ℂ) (x : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => (Complex.sinh (x-b 0-t/2) / Complex.sinh t) *
      vacuumL t (fun j => b (j+1)) x n

theorem vacuumA_product (t : ℂ) (b : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    vacuumA t b x n = ∏ j ∈ Finset.range n,
      Complex.sinh (x-b j+t/2) / Complex.sinh t := by
  induction n generalizing b with
  | zero => simp [vacuumA]
  | succ n ih =>
    rw [vacuumA, Finset.prod_range_succ']
    rw [ih]
    exact mul_comm _ _

theorem vacuumL_product (t : ℂ) (b : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    vacuumL t b x n = ∏ j ∈ Finset.range n,
      Complex.sinh (x-b j-t/2) / Complex.sinh t := by
  induction n generalizing b with
  | zero => simp [vacuumL]
  | succ n ih =>
    rw [vacuumL, Finset.prod_range_succ']
    rw [ih]
    exact mul_comm _ _

theorem bethe_upper_vacuum_column (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (x : ℂ) (a : Fin 2) (q : RowSpins n) :
    betheBlock t b n x a 0 q (plusSpins n) =
      if a = 0 ∧ q = plusSpins n then vacuumA t b x n else 0 := by
  induction n generalizing b a with
  | zero =>
    have hq : q = () := Subsingleton.elim _ _
    subst q
    fin_cases a <;> simp [betheBlock, rowBlock, plusSpins, vacuumA]
  | succ n ih =>
    rcases q with ⟨s,q⟩
    change (∑ c : Fin 2, hyperbolicR t (x-b 0-t/2) (a,s) (c,0) *
      betheBlock t (fun j => b (j+1)) n x c 0 q (plusSpins n)) = _
    simp only [Fin.sum_univ_two, ih]
    have he : x-b 0-t/2+t = x-b 0+t/2 := by ring
    fin_cases a <;> fin_cases s <;>
      simp [hyperbolicR, sixMatrix, plusSpins, vacuumA, he]

theorem bethe_lower_vacuum_column (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (x : ℂ) (q : RowSpins n) :
    betheL t b n x q (plusSpins n) =
      if q = plusSpins n then vacuumL t b x n else 0 := by
  induction n generalizing b with
  | zero =>
    have hq : q = () := Subsingleton.elim _ _
    subst q
    simp [betheL, betheBlock, rowBlock, plusSpins, vacuumL]
  | succ n ih =>
    rcases q with ⟨s,q⟩
    change (∑ c : Fin 2, hyperbolicR t (x-b 0-t/2) (1,s) (c,0) *
      betheBlock t (fun j => b (j+1)) n x c 1 q (plusSpins n)) = _
    simp only [Fin.sum_univ_two]
    change _ = if (s,q) = (0,plusSpins n) then vacuumL t b x (n+1) else 0
    simp only [betheL] at ih
    fin_cases s <;> simp [hyperbolicR, sixMatrix, ih, vacuumL]

/-- A rank-one vacuum projector lets the action proofs stay in the
noncommutative matrix algebra. Its plus column is the usual vacuum vector. -/
noncomputable def vacuumProjector (n : ℕ) : Matrix (RowSpins n) (RowSpins n) ℂ :=
  Matrix.of (fun q r => if q = plusSpins n ∧ r = plusSpins n then 1 else 0)

theorem mul_vacuumProjector (n : ℕ) (M : Matrix (RowSpins n) (RowSpins n) ℂ)
    (q r : RowSpins n) :
    (M * vacuumProjector n) q r = if r = plusSpins n then M q (plusSpins n) else 0 := by
  classical
  by_cases hr : r = plusSpins n
  · subst r
    simp [Matrix.mul_apply, vacuumProjector]
  · simp [Matrix.mul_apply, vacuumProjector, hr]

theorem bethe_A_vacuum (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) :
    betheA t b n x * vacuumProjector n = vacuumA t b x n • vacuumProjector n := by
  ext q r
  rw [mul_vacuumProjector]
  simp only [Matrix.smul_apply, smul_eq_mul, vacuumProjector, Matrix.of_apply]
  simp only [betheA, bethe_upper_vacuum_column, true_and]
  split_ifs <;> simp_all

theorem bethe_L_vacuum (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) :
    betheL t b n x * vacuumProjector n = vacuumL t b x n • vacuumProjector n := by
  ext q r
  rw [mul_vacuumProjector]
  simp only [Matrix.smul_apply, smul_eq_mul, vacuumProjector, Matrix.of_apply]
  rw [bethe_lower_vacuum_column]
  split_ifs <;> simp_all

theorem bethe_C_vacuum (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) :
    betheC t b n x * vacuumProjector n = 0 := by
  ext q r
  rw [mul_vacuumProjector]
  simp [betheC, bethe_upper_vacuum_column]

end SixVertex
