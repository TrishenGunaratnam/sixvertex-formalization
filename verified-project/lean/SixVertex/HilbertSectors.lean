import SixVertex.HilbertDual
import SixVertex.BetheCharge

namespace SixVertex
open scoped ComplexConjugate

/-- Distinct exact spin sectors are orthogonal in the actual L2 Hilbert space. -/
theorem spinSector_inner_zero (L : ℕ) (k l : ℤ) (u v : SpinHilbert L)
    (hu : SpinSector L k u) (hv : SpinSector L l v) (hkl : k ≠ l) :
    inner ℂ u v = 0 := by
  change inner ℂ (WithLp.toLp 2 (WithLp.ofLp u)) (WithLp.toLp 2 (WithLp.ofLp v)) = 0
  rw [EuclideanSpace.inner_toLp_toLp]
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hk : (minusCount L q : ℤ) = k
  · have hl : (minusCount L q : ℤ) ≠ l := by simpa [hk] using hkl
    simp [hv q hl]
  · simp [hu q hk]

theorem diagonal_mulVec_sector (L : ℕ) (k : ℤ) (d : RowSpins L → ℂ)
    (v : RowSpins L → ℂ) (hv : SpinSector L k v) :
    SpinSector L k ((Matrix.diagonal d).mulVec v) := by
  intro q hq
  simp only [Matrix.mulVec_diagonal, Pi.mul_apply, hv q hq, mul_zero]

theorem physicalListVector_sector (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (U : List ℂ) :
    SpinSector L (U.length : ℤ) (physicalListVector lam b L U) := by
  have h := diagonal_mulVec_sector L U.length (evenSign L)
    (fun q => betheListState (Complex.I*lam) (fun j => (b j : ℂ)) L U q (plusSpins L))
    (betheListState_sector (Complex.I*lam) (fun j => (b j : ℂ)) L U)
  convert h using 1
  funext q
  simp only [physicalListVector, quantumGauge, Matrix.diagonal_mul,
    Matrix.mulVec_diagonal, betheListState, mul_vacuumProjector, ite_true, creationList]

theorem physicalListVector_inner_zero (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (U V : List ℂ)
    (h : U.length ≠ V.length) :
    inner ℂ (physicalListVector lam b L U) (physicalListVector lam b L V) = 0 := by
  exact spinSector_inner_zero L U.length V.length _ _
    (physicalListVector_sector lam b L U) (physicalListVector_sector lam b L V) (by omega)

noncomputable def hilbertMatrixAction (L : ℕ)
    (M : Matrix (RowSpins L) (RowSpins L) ℂ) (v : SpinHilbert L) : SpinHilbert L :=
  WithLp.toLp 2 (M.mulVec v)

theorem wordOperator_sector (t : ℂ) (b : ℕ → ℂ) (L : ℕ)
    (w : List (RowEntry × ℂ)) (k : ℤ) (v : RowSpins L → ℂ) (hv : SpinSector L k v) :
    SpinSector L (k+(w.map (fun ev => entryCharge ev.1)).sum)
      ((wordOperator t b L w).mulVec v) := by
  induction w generalizing k v with
  | nil => simpa [wordOperator] using hv
  | cons ev w ih =>
    rcases ev with ⟨e,x⟩
    have h := ih (k+entryCharge e) ((entryOperator t b L e x).mulVec v)
      (entryOperator_sector t b L e x k v hv)
    simpa [wordOperator, Matrix.mulVec_mulVec, add_assoc] using h

theorem zSpin_minusCount (a : Fin 2) : zSpin a = (-1 : ℂ)^a.val := by
  fin_cases a <;> simp [zSpin]

theorem totalSign_minusCount (L : ℕ) (q : RowSpins L) :
    evenSign L q * oddSign L q = (-1 : ℂ)^(minusCount L q) := by
  induction L with
  | zero => simp [evenSign, oddSign, minusCount]
  | succ L ih => rw [totalSign_succ, ih, minusCount, pow_add, zSpin_minusCount]

/-- The parity operator is the scalar (-1)^k on the k-minus-spin sector. -/
theorem quantumParity_sector (L k : ℕ) (v : RowSpins L → ℂ)
    (hv : SpinSector L (k : ℤ) v) :
    (quantumParity L).mulVec v = (-1 : ℂ)^k • v := by
  funext q
  by_cases hk : minusCount L q = k
  · simp [quantumParity, Matrix.mulVec_diagonal, totalSign_minusCount, hk]
  · have hz := hv q (by omega)
    simp [quantumParity, Matrix.mulVec_diagonal, hz]

end SixVertex
