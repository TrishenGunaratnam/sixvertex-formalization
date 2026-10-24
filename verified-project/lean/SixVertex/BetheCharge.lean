import SixVertex.BetheParity

namespace SixVertex

/-- Number of minus spins in the ordered quantum basis. -/
def minusCount : (L : ℕ) → RowSpins L → ℕ
  | 0, _ => 0
  | L+1, q => q.1.val + minusCount L q.2

@[simp] theorem minusCount_plus (L : ℕ) : minusCount L (plusSpins L) = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simpa [minusCount, plusSpins] using ih

/-- The ice rule is exact conservation of auxiliary plus quantum charge. -/
theorem sixMatrix_charge_zero (A B C : ℂ) (a d q r : Fin 2)
    (h : a.val+q.val ≠ d.val+r.val) : sixMatrix A B C (a,q) (d,r) = 0 := by
  fin_cases a <;> fin_cases d <;> fin_cases q <;> fin_cases r <;>
    simp_all [sixMatrix]

theorem rowBlock_charge_zero (A B C : ℕ → ℂ) (L : ℕ) (a d : Fin 2)
    (q r : RowSpins L) (h : a.val+minusCount L q ≠ d.val+minusCount L r) :
    rowBlock (fun j => sixMatrix (A j) (B j) (C j)) L a d q r = 0 := by
  induction L generalizing A B C a d with
  | zero =>
    have had : a ≠ d := by intro he; subst d; exact h rfl
    simp [rowBlock, had]
  | succ L ih =>
    simp only [rowBlock]
    apply Finset.sum_eq_zero
    intro c hc
    by_cases hl : a.val+q.1.val = c.val+r.1.val
    · have ht : c.val+minusCount L q.2 ≠ d.val+minusCount L r.2 := by
        simp only [minusCount] at h
        omega
      rw [ih (fun j => A (j+1)) (fun j => B (j+1)) (fun j => C (j+1)) c d q.2 r.2 ht, mul_zero]
    · rw [sixMatrix_charge_zero _ _ _ _ _ _ _ hl, zero_mul]

theorem betheBlock_charge_zero (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (x : ℂ)
    (a d : Fin 2) (q r : RowSpins L)
    (h : a.val+minusCount L q ≠ d.val+minusCount L r) : betheBlock t b L x a d q r = 0 := by
  exact rowBlock_charge_zero
    (fun j => Complex.sinh (x-b j-t/2+t)/Complex.sinh t)
    (fun j => Complex.sinh (x-b j-t/2)/Complex.sinh t) (fun _ => 1) L a d q r h

def SpinSector (L : ℕ) (k : ℤ) (v : RowSpins L → ℂ) : Prop :=
  ∀ q, (minusCount L q : ℤ) ≠ k → v q = 0

/-- Every standard entry has its exact integer charge shift. -/
theorem betheBlock_sector (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (x : ℂ)
    (a d : Fin 2) (k : ℤ) (v : RowSpins L → ℂ) (hv : SpinSector L k v) :
    SpinSector L (k+d.val-a.val) ((betheBlock t b L x a d).mulVec v) := by
  intro q hq
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hk : (minusCount L r : ℤ) = k
  · have hc : a.val+minusCount L q ≠ d.val+minusCount L r := by omega
    rw [betheBlock_charge_zero _ _ _ _ _ _ _ _ hc, zero_mul]
  · rw [hv r hk, mul_zero]

def entryCharge : RowEntry → ℤ
  | .A => 0 | .B => 1 | .C => -1 | .L => 0

theorem entryOperator_sector (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (e : RowEntry)
    (x : ℂ) (k : ℤ) (v : RowSpins L → ℂ) (hv : SpinSector L k v) :
    SpinSector L (k+entryCharge e) ((entryOperator t b L e x).mulVec v) := by
  cases e with
  | A => simpa [entryOperator, entryCharge] using betheBlock_sector t b L x 0 0 k v hv
  | B => simpa [entryOperator, entryCharge] using betheBlock_sector t b L x 0 1 k v hv
  | C => simpa [entryOperator, entryCharge, sub_eq_add_neg] using betheBlock_sector t b L x 1 0 k v hv
  | L => simpa [entryOperator, entryCharge] using betheBlock_sector t b L x 1 1 k v hv

/-- A labelled off-shell creation list belongs to its exact magnon sector,
including repeated complex spectral arguments. -/
theorem betheListState_sector (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (U : List ℂ) :
    SpinSector L (U.length : ℤ) (fun q => betheListState t b L U q (plusSpins L)) := by
  induction U with
  | nil =>
    intro q hq
    have hn : q ≠ plusSpins L := by intro he; subst q; simp at hq
    simp [betheListState, vacuumProjector, hn]
  | cons u U ih =>
    have h := betheBlock_sector t b L u 0 1 (U.length : ℤ)
      (fun q => betheListState t b L U q (plusSpins L)) ih
    convert h using 1
    · simp
    · funext q
      change ((betheB t b L u * (U.map (betheB t b L)).prod) * vacuumProjector L) q (plusSpins L) =
        (betheB t b L u * ((U.map (betheB t b L)).prod * vacuumProjector L)) q (plusSpins L)
      rw [Matrix.mul_assoc]

end SixVertex
