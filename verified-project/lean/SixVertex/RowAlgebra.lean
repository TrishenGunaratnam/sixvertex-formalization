import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ext
import Mathlib.Tactic.LinearCombination

/-!
# Section 2: finite row algebra

Source: `sections/02-finite-rows.tex`, `lem:row-algebra`, lines 75–143,
in the pinned OpenAI manuscript. The complete named statement and proof are assembled in
`FiniteRowAlgebra.lean`. This file supplies the explicit matrices and
the adjoint calculation. No mathematical axiom or unfinished proof is used.

The auxiliary spin is the first index. Rows are output indices, columns
are input indices, in the ordered basis (++,+−,−+,−−).
-/

namespace SixVertex

open scoped ComplexConjugate

abbrev PairSpin := Fin 2 × Fin 2

/-- The six-vertex matrix with parallel, mixed and exchange weights a,b,c. -/
def sixMatrix (a b c : ℂ) : Matrix PairSpin PairSpin ℂ := fun i j =>
  if i = j then (if i.1 = i.2 then a else b)
  else if i.1 = j.2 ∧ i.2 = j.1 then c else 0

/-- Pauli Z acting on the auxiliary spin. -/
def auxZ : Matrix PairSpin PairSpin ℂ :=
  Matrix.diagonal (fun i => if i.1 = 0 then 1 else -1)

/-- Pauli Z acting on the quantum spin. -/
def siteZ : Matrix PairSpin PairSpin ℂ :=
  Matrix.diagonal (fun i => if i.2 = 0 then 1 else -1)

/-- Equation (2.2): the physical R matrix, for arbitrary complex u. -/
noncomputable def physicalR (lam : ℝ) (u : ℂ) : Matrix PairSpin PairSpin ℂ :=
  sixMatrix (Complex.sin (lam - u) / Complex.sin lam)
    (Complex.sin u / Complex.sin lam) 1

/-- The standard local L matrix in equation `eq:standard-monodromy`. -/
noncomputable def standardL (lam : ℝ) (x : ℂ) : Matrix PairSpin PairSpin ℂ :=
  sixMatrix (Complex.sinh (x + Complex.I * lam / 2) / (Complex.I * Complex.sin lam))
    (Complex.sinh (x - Complex.I * lam / 2) / (Complex.I * Complex.sin lam)) 1

/-- Exact local sign change, checked entry by entry. -/
theorem sixMatrix_gauge (a b c : ℂ) :
    auxZ * sixMatrix a b c * siteZ = sixMatrix a (-b) c := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [sixMatrix, auxZ, siteZ, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Converting a sine weight into the paper's hyperbolic-sine convention. -/
theorem sin_weight (z s : ℂ) :
    Complex.sin z / s = Complex.sinh (z * Complex.I) / (Complex.I * s) := by
  rw [Complex.sinh_mul_I, mul_comm (Complex.sin z),
    mul_div_mul_left _ _ Complex.I_ne_zero]

/-- The local gauge identity used in the proof of `lem:row-algebra`.
It is valid even before restricting the real parameter to (0,π). -/
theorem local_physical_gauge (lam : ℝ) (x : ℂ) :
    physicalR lam (lam / 2 + Complex.I * x) = auxZ * standardL lam x * siteZ := by
  rw [standardL, sixMatrix_gauge, physicalR]
  congr 1
  · rw [sin_weight]
    congr 2
    ring_nf
    simp [Complex.I_sq, sub_eq_add_neg]
  · rw [sin_weight]
    have h : ((lam : ℂ) / 2 + Complex.I * x) * Complex.I =
        -(x - Complex.I * lam / 2) := by
      ring_nf
      simp [Complex.I_sq, sub_eq_add_neg]
    rw [h, Complex.sinh_neg, neg_div]

/-- Physical local tile at site inhomogeneity b. -/
noncomputable def physicalTile (lam b : ℝ) (x : ℂ) : Matrix PairSpin PairSpin ℂ :=
  physicalR lam (lam / 2 + Complex.I * (x - b))

/-- Reversal of one spin. -/
def flipSpin (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem flipSpin_zero : flipSpin 0 = 1 := rfl
@[simp] theorem flipSpin_one : flipSpin 1 = 0 := rfl
@[simp] theorem flipSpin_flip (i : Fin 2) : flipSpin (flipSpin i) = i := by
  fin_cases i <;> rfl

/-- A complete, finite quantum spin basis. The empty chain has one basis vector. -/
@[reducible] def RowSpins : ℕ → Type
  | 0 => Unit
  | n+1 => Fin 2 × RowSpins n

instance rowSpinsFintype (n : ℕ) : Fintype (RowSpins n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Fin 2 × RowSpins n))

instance rowSpinsDecidableEq (n : ℕ) : DecidableEq (RowSpins n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => exact inferInstanceAs (DecidableEq (Fin 2 × RowSpins n))

/-- An auxiliary block of the ordered monodromy product. This explicitly sums
over the internal auxiliary spins and multiplies sites from left to right. -/
noncomputable def rowBlock (tiles : ℕ → Matrix PairSpin PairSpin ℂ) :
    (n : ℕ) → Fin 2 → Fin 2 → Matrix (RowSpins n) (RowSpins n) ℂ
  | 0, a, b => fun _ _ => if a = b then 1 else 0
  | n+1, a, b => fun q r => ∑ c : Fin 2,
      tiles 0 (a,q.1) (c,r.1) * rowBlock (fun j => tiles (j+1)) n c b q.2 r.2

/-- A row with an arbitrary complex auxiliary mark D, exactly tr_a(D M). -/
noncomputable def markedRow (tiles : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (RowSpins n) (RowSpins n) ℂ :=
  ∑ a : Fin 2, ∑ b : Fin 2, D b a • rowBlock tiles n a b

/-- The physical parallel weight and mixed weight exchange under conjugation. -/
theorem parallel_weight_conj (lam b : ℝ) (x : ℂ) :
    conj (Complex.sin (lam - (lam/2 + Complex.I * (x-b))) / Complex.sin lam) =
      Complex.sin (lam/2 + Complex.I * (conj x-b)) / Complex.sin lam := by
  simp only [map_div₀, ← Complex.sin_conj, map_sub, map_add, map_mul,
    map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  congr 2
  ring

theorem mixed_weight_conj (lam b : ℝ) (x : ℂ) :
    conj (Complex.sin (lam/2 + Complex.I * (x-b)) / Complex.sin lam) =
      Complex.sin (lam - (lam/2 + Complex.I * (conj x-b))) / Complex.sin lam := by
  simp only [map_div₀, ← Complex.sin_conj, map_sub, map_add, map_mul,
    map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  congr 2
  ring

/-- The local quantum-block adjoint rule, including the auxiliary spin flips. -/
theorem local_physical_adjoint (lam b : ℝ) (x : ℂ)
    (a d q r : Fin 2) :
    conj (physicalTile lam b x (a,r) (d,q)) =
      physicalTile lam b (conj x) (flipSpin a,q) (flipSpin d,r) := by
  fin_cases a <;> fin_cases d <;> fin_cases q <;> fin_cases r <;>
    simp [physicalTile, physicalR, sixMatrix, flipSpin] <;>
    first
    | simpa only [map_div₀] using parallel_weight_conj lam b x
    | simpa only [map_div₀] using mixed_weight_conj lam b x

/-- The adjoint rule propagates through every finite ordered chain. -/
theorem rowBlock_adjoint (tiles tiles' : ℕ → Matrix PairSpin PairSpin ℂ)
    (h : ∀ j a d q r, conj (tiles j (a,r) (d,q)) =
      tiles' j (flipSpin a,q) (flipSpin d,r)) (n : ℕ) (a b : Fin 2)
    (q r : RowSpins n) :
    conj (rowBlock tiles n a b r q) =
      rowBlock tiles' n (flipSpin a) (flipSpin b) q r := by
  induction n generalizing tiles tiles' a b with
  | zero =>
    fin_cases a <;> fin_cases b <;> simp [rowBlock]
  | succ n ih =>
    simp only [rowBlock, Fin.sum_univ_two, map_add, map_mul]
    rw [h, h,
      ih (fun j => tiles (j+1)) (fun j => tiles' (j+1)) (fun j => h (j+1)),
      ih (fun j => tiles (j+1)) (fun j => tiles' (j+1)) (fun j => h (j+1))]
    simp only [flipSpin_zero, flipSpin_one]
    ring

open scoped Matrix

/-- The auxiliary spin-exchange matrix X from Section 2. -/
def spinX : Matrix (Fin 2) (Fin 2) ℂ := fun a b => if a = flipSpin b then 1 else 0

theorem spinX_conjugates_mark (D : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    (spinX * D.map conj * spinX) a b = conj (D (flipSpin a) (flipSpin b)) := by
  fin_cases a <;> fin_cases b <;>
    simp [spinX, flipSpin, Matrix.mul_apply, Fin.sum_univ_two]

/-- Full marked-row adjoint identity. Different site blocks commute because
their scalar entries multiply in distinct quantum tensor factors. -/
theorem markedRow_adjoint (tiles tiles' : ℕ → Matrix PairSpin PairSpin ℂ)
    (h : ∀ j a d q r, conj (tiles j (a,r) (d,q)) =
      tiles' j (flipSpin a,q) (flipSpin d,r))
    (n : ℕ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    (markedRow tiles n D)ᴴ = markedRow tiles' n (spinX * D.map conj * spinX) := by
  ext q r
  simp only [markedRow, Matrix.conjTranspose_apply, Complex.star_def, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    spinX_conjugates_mark]
  rw [rowBlock_adjoint tiles tiles' h, rowBlock_adjoint tiles tiles' h,
    rowBlock_adjoint tiles tiles' h, rowBlock_adjoint tiles tiles' h]
  simp only [flipSpin_zero, flipSpin_one]
  ring

/-- The adjoint clause of `lem:row-algebra`, with exactly the paper's
arbitrary complex mark and real inhomogeneities. In fact no parity
restriction on the chain length is needed for this clause. -/
theorem physical_markedRow_adjoint (lam : ℝ) (b : ℕ → ℝ) (x : ℂ)
    (n : ℕ) (D : Matrix (Fin 2) (Fin 2) ℂ) :
    (markedRow (fun j => physicalTile lam (b j) x) n D)ᴴ =
      markedRow (fun j => physicalTile lam (b j) (conj x)) n
        (spinX * D.map conj * spinX) := by
  exact markedRow_adjoint _ _ (fun j => local_physical_adjoint lam (b j) x) n D

end SixVertex
