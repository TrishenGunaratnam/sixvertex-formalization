import SixVertex.ExactScalarProducts

namespace SixVertex
open scoped ComplexConjugate Matrix

/-- Conjugation exchanges the standard parallel and mixed vacuum weights,
with the minus sign forced by the imaginary normalization. -/
theorem standard_parallel_conj (lam b : ℝ) (x : ℂ) :
    conj (Complex.sinh (x-b+Complex.I*lam/2)/(Complex.I*Complex.sin lam)) =
      -(Complex.sinh (conj x-b-Complex.I*lam/2)/(Complex.I*Complex.sin lam)) := by
  simp only [map_div₀, ← Complex.sinh_conj, ← Complex.sin_conj, map_add, map_sub, map_mul,
    map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [show conj x-(b : ℂ)+(-Complex.I)*(lam : ℂ)/2 = conj x-b-Complex.I*lam/2 by ring]
  simp only [neg_mul, div_neg]

theorem standard_mixed_conj (lam b : ℝ) (x : ℂ) :
    conj (Complex.sinh (x-b-Complex.I*lam/2)/(Complex.I*Complex.sin lam)) =
      -(Complex.sinh (conj x-b+Complex.I*lam/2)/(Complex.I*Complex.sin lam)) := by
  simp only [map_div₀, ← Complex.sinh_conj, ← Complex.sin_conj, map_add, map_sub, map_mul,
    map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [show conj x-(b : ℂ)-(-Complex.I)*(lam : ℂ)/2 = conj x-b+Complex.I*lam/2 by ring]
  simp only [neg_mul, div_neg]

theorem standard_local_adjoint (lam b : ℝ) (x : ℂ) (a d q r : Fin 2) :
    conj (standardL lam (x-b) (a,r) (d,q)) =
      (-zSpin a*zSpin d) * standardL lam (conj x-b) (flipSpin a,q) (flipSpin d,r) := by
  fin_cases a <;> fin_cases d <;> fin_cases q <;> fin_cases r <;>
    simp [standardL, sixMatrix, zSpin, flipSpin] <;>
    first
    | simpa only [map_div₀, map_mul, Complex.conj_I, neg_mul] using standard_parallel_conj lam b x
    | simpa only [map_div₀, map_mul, Complex.conj_I, neg_mul] using standard_mixed_conj lam b x

/-- The auxiliary signs telescope through the ordered monodromy. The theorem
is valid for every chain length; even chains give the Hilbert-dual minus sign. -/
theorem rowBlock_signed_adjoint (tiles tiles' : ℕ → Matrix PairSpin PairSpin ℂ)
    (h : ∀ j a d q r, conj (tiles j (a,r) (d,q)) =
      (-zSpin a*zSpin d)*tiles' j (flipSpin a,q) (flipSpin d,r))
    (L : ℕ) (a d : Fin 2) (q r : RowSpins L) :
    conj (rowBlock tiles L a d r q) =
      ((-1 : ℂ)^L*zSpin a*zSpin d) * rowBlock tiles' L (flipSpin a) (flipSpin d) q r := by
  induction L generalizing tiles tiles' a d with
  | zero =>
    fin_cases a <;> fin_cases d <;> simp [rowBlock, zSpin, flipSpin]
  | succ L ih =>
    simp only [rowBlock, Fin.sum_univ_two, map_add, map_mul]
    rw [h 0, h 0,
      ih (fun j => tiles (j+1)) (fun j => tiles' (j+1)) (fun j => h (j+1)),
      ih (fun j => tiles (j+1)) (fun j => tiles' (j+1)) (fun j => h (j+1))]
    simp only [flipSpin_zero, flipSpin_one, zSpin, ite_true, show (1 : Fin 2) ≠ 0 by decide,
      ite_false, pow_succ]
    ring

/-- The actual standard monodromy block adjoint, including the odd-chain sign. -/
theorem betheBlock_hilbert_adjoint (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (x : ℂ)
    (a d : Fin 2) :
    (betheBlock (Complex.I*lam) (fun j => (b j : ℂ)) L x a d)ᴴ =
      ((-1 : ℂ)^L*zSpin a*zSpin d) •
        betheBlock (Complex.I*lam) (fun j => (b j : ℂ)) L (conj x) (flipSpin a) (flipSpin d) := by
  ext q r
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, betheBlock_eq_standard]
  exact rowBlock_signed_adjoint _ _ (fun j => standard_local_adjoint lam (b j) x) L a d q r

/-- Lemma 2.5, the unconditional operator identity B(x)^* = -C(conj x). -/
theorem betheB_hilbert_adjoint (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (x : ℂ) :
    (betheB (Complex.I*lam) (fun j => (b j : ℂ)) L x)ᴴ =
      -betheC (Complex.I*lam) (fun j => (b j : ℂ)) L (conj x) := by
  rw [betheB, betheBlock_hilbert_adjoint]
  simp only [hEven.neg_one_pow, zSpin, ite_true, show (1 : Fin 2) ≠ 0 by decide,
    ite_false, one_mul, mul_neg, mul_one, flipSpin_zero, flipSpin_one, neg_one_smul]

end SixVertex
