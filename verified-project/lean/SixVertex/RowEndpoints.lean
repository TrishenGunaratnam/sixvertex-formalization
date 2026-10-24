import SixVertex.RowAlgebra

namespace SixVertex

open scoped ComplexConjugate Matrix

def appendSpin : (n : ℕ) → RowSpins n → Fin 2 → RowSpins (n+1)
  | 0, _, a => (a,())
  | n+1, q, a => (q.1, appendSpin n q.2 a)

def unappendSpin : (n : ℕ) → RowSpins (n+1) → RowSpins n × Fin 2
  | 0, q => ((),q.1)
  | n+1, q => ((q.1, (unappendSpin n q.2).1), (unappendSpin n q.2).2)

theorem unappend_append (n : ℕ) (q : RowSpins n) (a : Fin 2) :
    unappendSpin n (appendSpin n q a) = (q,a) := by
  induction n with
  | zero => cases q; rfl
  | succ n ih => simp only [appendSpin, unappendSpin, ih]

theorem append_unappend (n : ℕ) (q : RowSpins (n+1)) :
    appendSpin n (unappendSpin n q).1 (unappendSpin n q).2 = q := by
  induction n with
  | zero => rcases q with ⟨a,q⟩; cases q; rfl
  | succ n ih =>
    simp only [unappendSpin, appendSpin, ih]

/-- Move the first quantum spin to the end; inverse moves the last to the front. -/
def cyclicSpinTranslation (n : ℕ) : Equiv.Perm (RowSpins (n+1)) where
  toFun q := appendSpin n q.2 q.1
  invFun q := ((unappendSpin n q).2, (unappendSpin n q).1)
  left_inv q := by
    change ((unappendSpin n (appendSpin n q.2 q.1)).2,
      (unappendSpin n (appendSpin n q.2 q.1)).1) = q
    rw [unappend_append]
  right_inv q := append_unappend n q

def spinPermutation {n : ℕ} (e : Equiv.Perm (RowSpins n)) :
    Matrix (RowSpins n) (RowSpins n) ℂ := fun q r => if q = e r then 1 else 0

theorem spinPermutation_adjoint {n : ℕ} (e : Equiv.Perm (RowSpins n)) :
    (spinPermutation e)ᴴ = spinPermutation e.symm := by
  ext q r
  simp [Matrix.conjTranspose_apply, spinPermutation,
    Equiv.eq_symm_apply, eq_comm]

theorem spinPermutation_mul_inverse {n : ℕ} (e : Equiv.Perm (RowSpins n)) :
    spinPermutation e * spinPermutation e.symm = 1 := by
  ext q r
  simp [Matrix.mul_apply, spinPermutation, mul_ite, Matrix.one_apply]

/-- The permutation R(0). -/
def swapTile : Matrix PairSpin PairSpin ℂ := fun i j =>
  if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

theorem physicalR_at_zero (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0) :
    physicalR lam 0 = swapTile := by
  ext ⟨a,q⟩ ⟨b,r⟩
  fin_cases a <;> fin_cases q <;> fin_cases b <;> fin_cases r <;>
    simp [physicalR, sixMatrix, swapTile, hs]

/-- Exact contraction of a nonempty chain of swaps, with both seam spins kept. -/
theorem rowBlock_swaps (n : ℕ) (a b : Fin 2)
    (q r : RowSpins (n+1)) :
    rowBlock (fun _ => swapTile) (n+1) a b q r =
      if q = appendSpin n r.2 b ∧ a = r.1 then 1 else 0 := by
  induction n generalizing a b with
  | zero =>
    rcases q with ⟨q,tq⟩
    rcases r with ⟨r,tr⟩
    cases tq
    cases tr
    fin_cases a <;> fin_cases b <;> fin_cases q <;> fin_cases r <;>
      simp [rowBlock, swapTile, appendSpin]
  | succ n ih =>
    rcases q with ⟨q,qt⟩
    rcases r with ⟨r,rt⟩
    change (∑ c : Fin 2, swapTile (a,q) (c,r) *
      rowBlock (fun _ => swapTile) (n+1) c b qt rt) = _
    simp_rw [ih]
    fin_cases a <;> fin_cases q <;> fin_cases r <;>
      simp [swapTile, appendSpin, Fin.sum_univ_two,
        Prod.mk.injEq, eq_comm, and_comm]

theorem markedRow_swaps (n : ℕ) :
    markedRow (fun _ => swapTile) (n+1) 1 =
      spinPermutation (cyclicSpinTranslation n) := by
  ext q r
  rcases r with ⟨r,rt⟩
  fin_cases r <;>
    simp [markedRow, Fin.sum_univ_two, Matrix.one_apply, Matrix.add_apply,
      rowBlock_swaps, spinPermutation, cyclicSpinTranslation] <;> rfl

/-- The positive homogeneous endpoint is exactly cyclic spin translation. -/
theorem physical_endpoint_translation (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0)
    (n : ℕ) :
    markedRow (fun _ => physicalTile lam 0 (Complex.I * lam / 2)) (n+1) 1 =
      spinPermutation (cyclicSpinTranslation n) := by
  have e : ((lam : ℂ)/2 + Complex.I * (Complex.I * lam / 2 - (0 : ℝ))) = 0 := by
    ring_nf
    simp [Complex.I_sq]
  simp only [physicalTile, e, physicalR_at_zero lam hs]
  exact markedRow_swaps n

theorem spinX_identity_mark : spinX * (1 : Matrix (Fin 2) (Fin 2) ℂ).map conj * spinX = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [spinX, flipSpin, Matrix.mul_apply]

/-- The other homogeneous endpoint is the inverse cyclic translation. -/
theorem physical_endpoint_inverse (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0)
    (n : ℕ) :
    markedRow (fun _ => physicalTile lam 0 (-Complex.I * lam / 2)) (n+1) 1 =
      spinPermutation (cyclicSpinTranslation n).symm := by
  have h := physical_markedRow_adjoint lam (fun _ => 0) (Complex.I * lam / 2) (n+1) 1
  have e : conj (Complex.I * (lam : ℂ) / 2) = -Complex.I * lam / 2 := by
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  rw [physical_endpoint_translation lam hs, spinX_identity_mark, e,
    spinPermutation_adjoint] at h
  exact h.symm

/-- The positive-length translation above, extended harmlessly to length zero
as the identity. The named paper theorem is restricted to L≥4. -/
def cyclicTranslation : (L : ℕ) → Equiv.Perm (RowSpins L)
  | 0 => Equiv.refl _
  | n+1 => cyclicSpinTranslation n

end SixVertex
